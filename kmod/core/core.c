/*
 * Copyright (C) 2014 Seth Jennings <sjenning@redhat.com>
 * Copyright (C) 2013-2014 Josh Poimboeuf <jpoimboe@redhat.com>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, see <http://www.gnu.org/licenses/>.
 */

/*
 * kpatch core module
 *
 * Patch modules register with this module to redirect old functions to new
 * functions.
 *
 * For each function patched by the module we must:
 * - Call stop_machine
 * - Ensure that no task has the old function in its call stack
 * - Add the new function address to kpatch_func_hash
 *
 * After that, each call to the old function calls into kpatch_ftrace_handler()
 * which finds the new function in kpatch_func_hash table and updates the
 * return instruction pointer so that ftrace will return to the new function.
 */

#define pr_fmt(fmt) KBUILD_MODNAME ": " fmt

#include <linux/module.h>
#include <linux/slab.h>
#include <linux/spinlock.h>
#include <linux/ftrace.h>
#include <linux/kprobes.h>
#include <linux/hashtable.h>
#include <linux/hardirq.h>
#include <linux/uaccess.h>
#include <linux/kallsyms.h>
#include <linux/smp.h>
#include <linux/delay.h>
#include <asm/stacktrace.h>
#include <asm/cacheflush.h>
#include "kpatch.h"

#if !defined(CONFIG_FUNCTION_TRACER) || \
	!defined(CONFIG_HAVE_FENTRY) || \
	!defined(CONFIG_MODULES) || \
	!defined(CONFIG_SYSFS) || \
	!defined(CONFIG_KALLSYMS_ALL)
#error "CONFIG_FUNCTION_TRACER, CONFIG_HAVE_FENTRY, CONFIG_MODULES, CONFIG_SYSFS, CONFIG_KALLSYMS_ALL kernel config options are required"
#endif

#define KPATCH_HASH_BITS 8
static DEFINE_HASHTABLE(kpatch_func_hash, KPATCH_HASH_BITS);

static DEFINE_SEMAPHORE(kpatch_mutex);

LIST_HEAD(kpmod_list);

static int kpatch_num_patched;

static struct kobject *kpatch_root_kobj;
struct kobject *kpatch_patches_kobj;
EXPORT_SYMBOL_GPL(kpatch_patches_kobj);

struct kpatch_backtrace_args {
	struct kpatch_module *kpmod;
	int ret;
};

struct kpatch_kallsyms_args {
	const char *name;
	unsigned long addr;
};

/* this is a double loop, use goto instead of break */
#define do_for_each_linked_func(kpmod, func) {				\
	struct kpatch_object *_object;					\
	list_for_each_entry(_object, &kpmod->objects, list) {		\
		if (!kpatch_object_linked(_object))			\
			continue;					\
		list_for_each_entry(func, &_object->funcs, list) {

#define while_for_each_linked_func()					\
		}							\
	}								\
}


/*
 * The kpatch core module has a function reference counter which allows for
 * proper synchronization with kpatch_ftrace_handler().
 *
 * The kpatch_refcnt starts with KPATCH_REF_START( == 1). At this point,
 * since all the func_hash entries whose op is KPATCH_OP_PATCH are under
 * updating, kpatch_ftrace_handler() must use previous entries.
 * After checking the stack of all tasks, the kpatch_refcnt is decremented
 * KPATCH_REF_START. If all the target functions are not in use, the refcnt
 * should be back to 0 (== KPATCH_REF_SUCCESS). Then all new entries are
 * valid.
 */
enum {
	KPATCH_REF_INIT = 0,
	KPATCH_REF_START = 1,
	KPATCH_REF_SUCCESS = 0,
	KPATCH_REF_FAILURE = 0x1000,
};
static atomic_t kpatch_refcnt;

static inline void kpatch_refcnt_init(void)
{
	atomic_set(&kpatch_refcnt, KPATCH_REF_INIT);
}

static inline void kpatch_refcnt_start(void)
{
	WARN_ON(atomic_read(&kpatch_refcnt) != KPATCH_REF_INIT);
	atomic_set(&kpatch_refcnt, KPATCH_REF_START);
}

/* Return 0 if kpatch safety-check get succeeded, otherwides still continuing */
static inline int kpatch_refcnt_inc(void)
{
	return atomic_inc_not_zero(&kpatch_refcnt);
}

static inline int kpatch_refcnt_dec(void)
{
	return atomic_dec_if_positive(&kpatch_refcnt);
}

static inline int kpatch_refcnt_finish(bool success)
{
	if (success)
		atomic_dec(&kpatch_refcnt);
	else
		atomic_add(KPATCH_REF_FAILURE, &kpatch_refcnt);
	return atomic_read(&kpatch_refcnt);
}

static inline int kpatch_refcnt_read(void)
{
	return atomic_read(&kpatch_refcnt);
}

static struct kpatch_func *kpatch_get_func(unsigned long ip)
{
	struct kpatch_func *f;

	/* Here, we have to use rcu safe hlist because of NMI concurrency */
	hash_for_each_possible_rcu(kpatch_func_hash, f, node, ip)
		if (f->old_addr == ip)
			return f;
	return NULL;
}

static struct kpatch_func *kpatch_get_prev_func(struct kpatch_func *f,
						unsigned long ip)
{
	hlist_for_each_entry_continue_rcu(f, node)
		if (f->old_addr == ip)
			return f;
	return NULL;
}

static inline bool kpatch_object_linked(struct kpatch_object *object)
{
	return object->mod || !strcmp(object->name, "vmlinux");
}

static inline int kpatch_compare_addresses(unsigned long stack_addr,
					   unsigned long func_addr,
					   unsigned long func_size,
					   const char *func_name)
{
	if (stack_addr >= func_addr && stack_addr < func_addr + func_size) {
		pr_err("activeness safety check failed for %s\n", func_name);
		return -EBUSY;
	}
	return 0;
}

static void kpatch_backtrace_address_verify(void *data, unsigned long address,
					    int reliable)
{
	struct kpatch_backtrace_args *args = data;
	struct kpatch_module *kpmod = args->kpmod;
	struct kpatch_func *func;
	int i;

	if (args->ret)
		return;

	/* check kpmod funcs */
	do_for_each_linked_func(kpmod, func) {
		unsigned long func_addr, func_size;
		const char *func_name;
		struct kpatch_func *active_func;

		if (func->force)
			continue;

		active_func = kpatch_get_func(func->old_addr);
		if (!active_func) {
			/* patching an unpatched func */
			func_addr = func->old_addr;
			func_size = func->old_size;
			func_name = func->name;
		} else {
			/* repatching or unpatching */
			func_addr = active_func->new_addr;
			func_size = active_func->new_size;
			func_name = active_func->name;
		}

		args->ret = kpatch_compare_addresses(address, func_addr,
						     func_size, func_name);
		if (args->ret)
			return;
	} while_for_each_linked_func();

	/* in the replace case, need to check the func hash as well */
	hash_for_each_rcu(kpatch_func_hash, i, func, node) {
		if (func->op == KPATCH_OP_UNPATCH && !func->force) {
			args->ret = kpatch_compare_addresses(address,
							     func->new_addr,
							     func->new_size,
							     func->name);
			if (args->ret)
				return;
		}
	}
}

static int kpatch_backtrace_stack(void *data, char *name)
{
	return 0;
}

static const struct stacktrace_ops kpatch_backtrace_ops = {
	.address	= kpatch_backtrace_address_verify,
	.stack		= kpatch_backtrace_stack,
	.walk_stack	= print_context_stack_bp,
};

static int kpatch_print_trace_stack(void *data, char *name)
{
	pr_cont(" <%s> ", name);
	return 0;
}

static void kpatch_print_trace_address(void *data, unsigned long addr,
				       int reliable)
{
	if (reliable)
		pr_info("[<%p>] %pB\n", (void *)addr, (void *)addr);
}

static const struct stacktrace_ops kpatch_print_trace_ops = {
	.stack		= kpatch_print_trace_stack,
	.address	= kpatch_print_trace_address,
	.walk_stack	= print_context_stack,
};

/* Activitiy monitoring task list */
struct kpatch_montask {
	struct list_head list;
	pid_t pid;
	bool checked;
	bool failed;
};
static LIST_HEAD(kpatch_montasks);
static LIST_HEAD(kpatch_montask_pool);
static DEFINE_SPINLOCK(kpatch_montask_lock);
#define MONTASK_POOL_SIZE	128	/* TODO: this will not fit all */

/* Make an object pool since we can not allocate memory under rcu_read_lock */
static int kpatch_populate_monitoring_task_pool(int size)
{
	struct kpatch_montask *mt;
	int i;

	for (i = 0; i < size; i++) {
		mt = kzalloc(sizeof(*mt), GFP_KERNEL);
		if (!mt)
			return -ENOMEM;
		INIT_LIST_HEAD(&mt->list);
		list_add_tail(&mt->list, &kpatch_montask_pool);
	}
	return 0;
}

/* Cleanup monitoring tasks */
static void kpatch_cleanup_monitoring_task_pool(void)
{
	struct kpatch_montask *mt;

	while (!list_empty(&kpatch_montask_pool)) {
		mt = list_first_entry(&kpatch_montask_pool,
				      struct kpatch_montask, list);
		list_del(&mt->list);
		kfree(mt);
	}
}

static struct kpatch_montask *kpatch_new_monitoring_task_from_pool(void)
{
	struct kpatch_montask *mt;

	if (list_empty(&kpatch_montask_pool))
		return NULL;

	mt = list_first_entry(&kpatch_montask_pool,
				struct kpatch_montask, list);
	list_del_init(&mt->list);

	return mt;
}

static void kpatch_free_monitoring_task_to_pool(struct kpatch_montask *mt)
{
	list_add_tail(&mt->list, &kpatch_montask_pool);
}

static struct kpatch_montask *__kpatch_get_monitoring_task(pid_t pid)
{
	struct kpatch_montask *mt;

	list_for_each_entry(mt, &kpatch_montasks, list)
		if (mt->pid == pid)
			return mt;
	return NULL;
}

static struct kpatch_montask *kpatch_get_monitoring_task(pid_t pid)
{
	struct kpatch_montask *mt;

	spin_lock(&kpatch_montask_lock);
	mt = __kpatch_get_monitoring_task(pid);
	spin_unlock(&kpatch_montask_lock);

	return mt;
}

static int
kpatch_add_monitoring_task(struct task_struct *t, bool checked, bool failed)
{
	struct kpatch_montask *mt;
	int ret = 0;

	spin_lock(&kpatch_montask_lock);
	mt = __kpatch_get_monitoring_task(t->pid);
	if (mt) {
		if (checked && !mt->checked) {
			mt->checked = checked;
			mt->failed = failed;
		}
	} else {
		mt = kpatch_new_monitoring_task_from_pool();
		if (!mt) {
			ret = -ENOMEM;
			goto out;
		}
		mt->pid = t->pid;
		mt->checked = checked;
		mt->failed = failed;
		INIT_LIST_HEAD(&mt->list);
		list_add_tail(&mt->list, &kpatch_montasks);
	}
out:
	spin_unlock(&kpatch_montask_lock);
	return ret;
}

/* Count the number of unchecked tasks and failed tasks */
static int kpatch_unchecked_monitoring_tasks(int *failed)
{
	struct kpatch_montask *mt;
	int count = 0;

	spin_lock(&kpatch_montask_lock);
	list_for_each_entry(mt, &kpatch_montasks, list) {
		if (!mt->checked)
			count++;
		if (mt->failed)
			(*failed)++;
	}
	spin_unlock(&kpatch_montask_lock);

	return count;
}

static void kpatch_dump_monitoring_tasks(void)
{
	struct kpatch_montask *mt;

	spin_lock(&kpatch_montask_lock);
	list_for_each_entry(mt, &kpatch_montasks, list) {
		if (!mt->checked || mt->failed)
			pr_info("PID:%d is %s\n", mt->pid,
				mt->failed ? "in use" : "not checked");
	}
	spin_unlock(&kpatch_montask_lock);
}

static void kpatch_cleanup_monitoring_tasks(void)
{
	struct kpatch_montask *mt;

	spin_lock(&kpatch_montask_lock);
	while (!list_empty(&kpatch_montasks)) {
		mt = list_first_entry(&kpatch_montasks,
				      struct kpatch_montask, list);
		list_del_init(&mt->list);
		kpatch_free_monitoring_task_to_pool(mt);
	}
	spin_unlock(&kpatch_montask_lock);
}

static struct kpatch_module *current_kpatch_module;

static void kpatch_montask_check_current(void)
{
	struct kpatch_montask *mt;
	struct kpatch_backtrace_args args = {
		.kpmod = current_kpatch_module,
		.ret = 0
	};
	int ret;

	if (!current_kpatch_module)
		return;

	mt = kpatch_get_monitoring_task(current->pid);
	/* Skip if already checked */
	if (mt && mt->checked)
		return;

	pr_debug("Check task PID:%d on %d chk:%d\n", current->pid,
		 task_cpu(current), mt ? mt->checked : -1);
	dump_trace(current, NULL, NULL, 0, &kpatch_backtrace_ops, &args);
	ret = kpatch_add_monitoring_task(current, true, !!args.ret);
	if (ret < 0) {
		pr_info("Error: cannot allocate montask\n");
		spin_lock(&kpatch_montask_lock);
		mt = list_first_entry(&kpatch_montasks,
			      struct kpatch_montask, list);
		mt->failed = true;
		mt->checked = true;
		spin_unlock(&kpatch_montask_lock);
	}
}

static int kpatch_montask_handler(struct kprobe *kp, struct pt_regs *regs)
{
	kpatch_montask_check_current();
	return 0;
}

struct kprobe kpatch_ctxsw_probe = {
	.pre_handler = kpatch_montask_handler,
	.symbol_name = "__switch_to",
};

static void unregister_kprobe_init(struct kprobe *kp)
{
	unregister_kprobe(kp);
	if (kp->symbol_name)
		kp->addr = NULL;
	kp->flags = 0;
}

/*
 * Verify activeness safety, i.e. that none of the to-be-patched functions are
 * on the stack of any task.
 *
 * This function is called from stop_machine() context.
 */
static int kpatch_verify_activeness_safety(struct kpatch_module *kpmod)
{
	struct task_struct *g, *t;
	int ret = 0;
	int failed = 0;
	int timeout;

	struct kpatch_backtrace_args args = {
		.kpmod = kpmod,
		.ret = 0
	};

	current_kpatch_module = kpmod;
	smp_rmb();
	/*
	 * Hack the task switching here. At this point, online task stack
	 * checking is started and it could run consequently with off-line
	 * task stack checking. Since the stack-dump just read through the
	 * stack entries, there is no race between them.
	 */
	ret = register_kprobe(&kpatch_ctxsw_probe);
	if (ret < 0) {
		pr_info("Error on registering task switch hook: %d\n", ret);
		return ret;
	}

	/* Check the stacks of all tasks. */
	rcu_read_lock();
	pr_debug("Current PID: %d\n", current->pid);
	do_each_thread(g, t) {
		task_lock(t);
		if (t != current && t->state == TASK_RUNNING &&
		    task_cpu(t) != task_cpu(current)) {
			/* This task is running on other CPUs */
			pr_debug("Deferred check: PID: %d\n", t->pid);
			ret = kpatch_add_monitoring_task(t, false, false);
			task_unlock(t);
			if (ret)
				goto unlock;
			continue;
		}
		dump_trace(t, NULL, NULL, 0, &kpatch_backtrace_ops, &args);
		if (args.ret) {
			ret = args.ret;
			pr_info("PID: %d Comm: %.20s is sleeping on the"\
				" patched function.\n", t->pid, t->comm);
			dump_trace(t, NULL, (unsigned long *)t->thread.sp,
				   0, &kpatch_print_trace_ops, NULL);
			task_unlock(t);
			goto unlock;
		}
		task_unlock(t);
	} while_each_thread(g, t);

unlock:
	rcu_read_unlock();
	if (ret)
		goto out;

	/* Wait for the rest processes on runqueue */
	timeout = 128;
	while (kpatch_unchecked_monitoring_tasks(&failed) && failed == 0) {
		synchronize_sched();
		if (--timeout == 0) {
			pr_info("Safeness check timed out\n");
			kpatch_dump_monitoring_tasks();
			ret = -ETIME;
			goto out;
		}
	}
	if (failed) {
		kpatch_dump_monitoring_tasks();
		ret = -EBUSY;
	}

out:
	/* Cleanup the working area */
	current_kpatch_module = NULL;
	unregister_kprobe_init(&kpatch_ctxsw_probe);
	kpatch_cleanup_monitoring_tasks();

	return ret;
}

/* Called from stop_machine */
static int kpatch_apply_patch(struct kpatch_module *kpmod)
{
	struct kpatch_func *func;
	struct kpatch_hook *hook;
	struct kpatch_object *object;
	int ret;

	/* tentatively add the new funcs to the global func hash, but its
	 * not used until succeeding to verify */
	do_for_each_linked_func(kpmod, func) {
		hash_add_rcu(kpatch_func_hash, &func->node, func->old_addr);
	} while_for_each_linked_func();

	/* memory barrier between func hash add and refcnt change */
	smp_wmb();

	ret = kpatch_verify_activeness_safety(kpmod);
	if (ret)
		goto fail;

	ret = kpatch_refcnt_finish(true);
	if (ret != 0 && kpatch_refcnt_inc())
		goto fail;

	/* run any user-defined load hooks */
	list_for_each_entry(object, &kpmod->objects, list) {
		if (!kpatch_object_linked(object))
			continue;
		list_for_each_entry(hook, &object->hooks_load, list)
			(*hook->hook)();
	}

	return 0;
fail:
	/* Failed, we have to rollback patching process */
	kpatch_refcnt_finish(false);
	do_for_each_linked_func(kpmod, func) {
		hash_del_rcu(&func->node);
	} while_for_each_linked_func();

	return -EBUSY;
}

/* Called from stop_machine */
static int kpatch_remove_patch(struct kpatch_module *kpmod)
{
	struct kpatch_func *func;
	struct kpatch_hook *hook;
	struct kpatch_object *object;
	int ret;

	ret = kpatch_verify_activeness_safety(kpmod);
	if (ret)
		goto fail;

	ret = kpatch_refcnt_finish(true);
	if (ret != 0 && kpatch_refcnt_inc())
		goto fail;

	/* memory barrier between func hash add and refcnt change */
	smp_wmb();

	/* Succeeded, remove all updating funcs from hash table */
	do_for_each_linked_func(kpmod, func) {
		hash_del_rcu(&func->node);
	} while_for_each_linked_func();

	/* run any user-defined unload hooks */
	list_for_each_entry(object, &kpmod->objects, list) {
		if (!kpatch_object_linked(object))
			continue;
		list_for_each_entry(hook, &object->hooks_unload, list)
			(*hook->hook)();
	}

	return 0;
fail:
	kpatch_refcnt_finish(false);
	return -EBUSY;
}

/*
 * This is where the magic happens.  Update regs->ip to tell ftrace to return
 * to the new function.
 *
 * If there are multiple patch modules that have registered to patch the same
 * function, the last one to register wins, as it'll be first in the hash
 * bucket.
 */
static void notrace
kpatch_ftrace_handler(unsigned long ip, unsigned long parent_ip,
		      struct ftrace_ops *fops, struct pt_regs *regs)
{
	struct kpatch_func *func;
	int refcnt;

	preempt_disable_notrace();

	/* Now we don't need to care about NMI because we can check refcnt */
	refcnt = kpatch_refcnt_read();

	/* no memory reordering between refcnt and func hash read */
	smp_rmb();

	func = kpatch_get_func(ip);

	if (refcnt == KPATCH_REF_SUCCESS) {
		/*
		 * Patching succeeded.  If the function was being
		 * unpatched, roll back to the previous version.
		 */
		if (func && func->op == KPATCH_OP_UNPATCH)
			func = kpatch_get_prev_func(func, ip);
	} else {
		/*
		 * Patching failed.  If the function was being patched,
		 * roll back to the previous version.
		 */
		if (func && func->op == KPATCH_OP_PATCH)
			func = kpatch_get_prev_func(func, ip);
	}

	if (func)
		regs->ip = func->new_addr + MCOUNT_INSN_SIZE;

	preempt_enable_notrace();
}

/* Update the reference of target function */
static int kpatch_retprobe_entry(struct kretprobe_instance *rp,
				   struct pt_regs *regs)
{
	kpatch_refcnt_inc();
	return 0;
}

static int kpatch_retprobe_return(struct kretprobe_instance *rp,
				   struct pt_regs *regs)
{
	kpatch_refcnt_dec();
	return 0;
}

struct kpatch_retprobe {
	struct list_head list;
	struct kretprobe rp;
};

static LIST_HEAD(kpatch_retprobes);
static int kpatch_nr_retprobes;

static int kpatch_retprobe_add_func(unsigned long ip)
{
	struct kpatch_retprobe *krp;
	int ret;

	krp = kzalloc(sizeof(*krp), GFP_KERNEL);
	if (!krp)
		return -ENOMEM;

	krp->rp.entry_handler = kpatch_retprobe_entry;
	krp->rp.handler = kpatch_retprobe_return;
	krp->rp.kp.addr = (void *)ip;
	INIT_LIST_HEAD(&krp->list);
	ret = register_kretprobe(&krp->rp);
	if (ret < 0) {
		kfree(krp);
		return ret;
	}

	kpatch_nr_retprobes++;
	list_add(&krp->list, &kpatch_retprobes);

	return 0;
}

static int kpatch_retprobe_remove_func(unsigned long ip)
{
	struct kpatch_retprobe *krp;

	list_for_each_entry(krp, &kpatch_retprobes, list) {
		if ((unsigned long)krp->rp.kp.addr != ip)
			continue;
		list_del(&krp->list);
		unregister_kretprobe(&krp->rp);
		kfree(krp);
		kpatch_nr_retprobes--;
		return 0;
	}
	return -ENOENT;
}

static void kpatch_retprobe_remove_all(void)
{
	struct kpatch_retprobe *krp, *tmp;
	/* TBD: use unregister_kretprobes */
	list_for_each_entry_safe(krp, tmp, &kpatch_retprobes, list)
		kpatch_retprobe_remove_func((unsigned long)krp->rp.kp.addr);
}

static struct ftrace_ops kpatch_ftrace_ops __read_mostly = {
	.func = kpatch_ftrace_handler,
	.flags = FTRACE_OPS_FL_SAVE_REGS,
};

static int kpatch_ftrace_add_func(unsigned long ip)
{
	int ret;

	/* check if any other patch modules have also patched this func */
	if (kpatch_get_func(ip))
		return 0;

	ret = kpatch_retprobe_add_func(ip);
	if (ret) {
		pr_err("can't set kretprobe at address 0x%lx\n", ip);
		return ret;
	}

	ret = ftrace_set_filter_ip(&kpatch_ftrace_ops, ip, 0, 0);
	if (ret) {
		pr_err("can't set ftrace filter at address 0x%lx\n", ip);
		goto out_remove_ret;
	}

	if (!kpatch_num_patched) {
		ret = register_ftrace_function(&kpatch_ftrace_ops);
		if (ret) {
			pr_err("can't register ftrace handler\n");
			goto out_remove_filter;
		}
	}
	kpatch_num_patched++;

	return 0;

out_remove_filter:
	ftrace_set_filter_ip(&kpatch_ftrace_ops, ip, 1, 0);
out_remove_ret:
	kpatch_retprobe_remove_func(ip);

	return ret;
}

static int kpatch_ftrace_remove_func(unsigned long ip)
{
	int ret;

	/* check if any other patch modules have also patched this func */
	if (kpatch_get_func(ip))
		return 0;

	if (kpatch_num_patched == 1) {
		ret = unregister_ftrace_function(&kpatch_ftrace_ops);
		if (ret) {
			pr_err("can't unregister ftrace handler\n");
			return ret;
		}
	}
	kpatch_num_patched--;

	ret = ftrace_set_filter_ip(&kpatch_ftrace_ops, ip, 1, 0);
	if (ret) {
		pr_err("can't remove ftrace filter at address 0x%lx\n", ip);
		return ret;
	}
	kpatch_retprobe_remove_func(ip);

	return 0;
}

static int kpatch_kallsyms_callback(void *data, const char *name,
					 struct module *mod,
					 unsigned long addr)
{
	struct kpatch_kallsyms_args *args = data;

	if (args->addr == addr && !strcmp(args->name, name))
		return 1;

	return 0;
}

static int kpatch_verify_symbol_match(const char *name, unsigned long addr)
{
	int ret;

	struct kpatch_kallsyms_args args = {
		.name = name,
		.addr = addr,
	};

	ret = kallsyms_on_each_symbol(kpatch_kallsyms_callback, &args);
	if (!ret) {
		pr_err("base kernel mismatch for symbol '%s'\n", name);
		pr_err("expected address was 0x%016lx\n", addr);
		return -EINVAL;
	}

	return 0;
}

static unsigned long kpatch_find_module_symbol(struct module *mod,
					       const char *name)
{
	char buf[KSYM_SYMBOL_LEN];

	/* check total string length for overrun */
	if (strlen(mod->name) + strlen(name) + 1 >= KSYM_SYMBOL_LEN) {
		pr_err("buffer overrun finding symbol '%s' in module '%s'\n",
		       name, mod->name);
		return 0;
	}

	/* encode symbol name as "mod->name:name" */
	strcpy(buf, mod->name);
	strcat(buf, ":");
	strcat(buf, name);

	return kallsyms_lookup_name(buf);
}

/*
 * External symbols are located outside the parent object (where the parent
 * object is either vmlinux or the kmod being patched).
 */
static unsigned long kpatch_find_external_symbol(struct kpatch_module *kpmod,
						 const char *name)
{
	const struct kernel_symbol *sym;

	/* first, check if it's an exported symbol */
	preempt_disable();
	sym = find_symbol(name, NULL, NULL, true, true);
	preempt_enable();
	if (sym)
		return sym->value;

	/* otherwise check if it's in another .o within the patch module */
	return kpatch_find_module_symbol(kpmod->mod, name);
}

static int kpatch_write_relocations(struct kpatch_module *kpmod,
				    struct kpatch_object *object)
{
	int ret, size, readonly = 0, numpages;
	struct kpatch_dynrela *dynrela;
	u64 loc, val;
	unsigned long core = (unsigned long)kpmod->mod->module_core;
	unsigned long core_ro_size = kpmod->mod->core_ro_size;
	unsigned long core_size = kpmod->mod->core_size;
	unsigned long src;

	list_for_each_entry(dynrela, &object->dynrelas, list) {
		if (!strcmp(object->name, "vmlinux")) {
			ret = kpatch_verify_symbol_match(dynrela->name,
							 dynrela->src);
			if (ret)
				return ret;
		} else {
			/* module, dynrela->src needs to be discovered */

			if (dynrela->external)
				src = kpatch_find_external_symbol(kpmod,
								  dynrela->name);
			else
				src = kpatch_find_module_symbol(object->mod,
								dynrela->name);

			if (!src) {
				pr_err("unable to find symbol '%s'\n",
				       dynrela->name);
				return -EINVAL;
			}

			dynrela->src = src;
		}

		switch (dynrela->type) {
		case R_X86_64_NONE:
			continue;
		case R_X86_64_PC32:
			loc = dynrela->dest;
			val = (u32)(dynrela->src + dynrela->addend -
				    dynrela->dest);
			size = 4;
			break;
		case R_X86_64_32S:
			loc = dynrela->dest;
			val = (s32)dynrela->src + dynrela->addend;
			size = 4;
			break;
		case R_X86_64_64:
			loc = dynrela->dest;
			val = dynrela->src;
			size = 8;
			break;
		default:
			pr_err("unsupported rela type %ld for source %s (0x%lx <- 0x%lx)\n",
			       dynrela->type, dynrela->name, dynrela->dest,
			       dynrela->src);
			return -EINVAL;
		}

		if (loc >= core && loc < core + core_ro_size)
			readonly = 1;
		else if (loc >= core + core_ro_size && loc < core + core_size)
			readonly = 0;
		else {
			pr_err("bad dynrela location 0x%llx for symbol %s\n",
			       loc, dynrela->name);
			return -EINVAL;
		}

		numpages = (PAGE_SIZE - (loc & ~PAGE_MASK) >= size) ? 1 : 2;

		if (readonly)
			set_memory_rw(loc & PAGE_MASK, numpages);

		ret = probe_kernel_write((void *)loc, &val, size);

		if (readonly)
			set_memory_ro(loc & PAGE_MASK, numpages);

		if (ret) {
			pr_err("write to 0x%llx failed for symbol %s\n",
			       loc, dynrela->name);
			return ret;
		}
	}

	return 0;
}

static int kpatch_unlink_object(struct kpatch_object *object)
{
	struct kpatch_func *func;
	int ret;

	list_for_each_entry(func, &object->funcs, list) {
		if (!func->old_addr)
			continue;
		ret = kpatch_ftrace_remove_func(func->old_addr);
		if (ret) {
			WARN(1, "can't unregister ftrace for address 0x%lx\n",
			     func->old_addr);
			return ret;
		}
	}

	if (object->mod)
		module_put(object->mod);

	return 0;
}

/*
 * Link to a to-be-patched object in preparation for patching it.
 *
 * - Find the object module
 * - Write patch module relocations which reference the object
 * - Calculate the patched functions' addresses
 * - Register them with ftrace
 */
static int kpatch_link_object(struct kpatch_module *kpmod,
			      struct kpatch_object *object)
{
	struct module *mod = NULL;
	struct kpatch_func *func, *func_err = NULL;
	int ret;
	bool vmlinux = !strcmp(object->name, "vmlinux");

	if (!vmlinux) {
		mutex_lock(&module_mutex);
		mod = find_module(object->name);
		if (!mod) {
			/*
			 * The module hasn't been loaded yet.  We can patch it
			 * later in kpatch_module_notify().
			 */
			mutex_unlock(&module_mutex);
			return 0;
		}

		/* should never fail because we have the mutex */
		WARN_ON(!try_module_get(mod));
		mutex_unlock(&module_mutex);
		object->mod = mod;
	}

	ret = kpatch_write_relocations(kpmod, object);
	if (ret)
		goto err_put;

	list_for_each_entry(func, &object->funcs, list) {

		/* calculate actual old location */
		if (vmlinux) {
			ret = kpatch_verify_symbol_match(func->name,
							 func->old_addr);
			if (ret) {
				func_err = func;
				goto err_ftrace;
			}
		} else {
			unsigned long old_addr;
			old_addr = kpatch_find_module_symbol(mod, func->name);
			if (!old_addr) {
				pr_err("unable to find symbol '%s' in module '%s\n",
				       func->name, mod->name);
				func_err = func;
				ret = -EINVAL;
				goto err_ftrace;
			}
			func->old_addr = old_addr;
		}

		/* add to ftrace filter and register handler if needed */
		ret = kpatch_ftrace_add_func(func->old_addr);
		if (ret) {
			func_err = func;
			goto err_ftrace;
		}
	}

	return 0;

err_ftrace:
	list_for_each_entry(func, &object->funcs, list) {
		if (func == func_err)
			break;
		WARN_ON(kpatch_ftrace_remove_func(func->old_addr));
	}
err_put:
	if (!vmlinux)
		module_put(mod);
	return ret;
}

static int kpatch_module_notify(struct notifier_block *nb, unsigned long action,
				void *data)
{
	struct module *mod = data;
	struct kpatch_module *kpmod;
	struct kpatch_object *object;
	struct kpatch_func *func;
	struct kpatch_hook *hook;
	int ret = 0;
	bool found = false;

	if (action != MODULE_STATE_COMING)
		return 0;

	down(&kpatch_mutex);

	list_for_each_entry(kpmod, &kpmod_list, list) {
		list_for_each_entry(object, &kpmod->objects, list) {
			if (kpatch_object_linked(object))
				continue;
			if (!strcmp(object->name, mod->name)) {
				found = true;
				goto done;
			}
		}
	}
done:
	if (!found)
		goto out;

	ret = kpatch_link_object(kpmod, object);
	if (ret)
		goto out;

	BUG_ON(!object->mod);

	pr_notice("patching newly loaded module '%s'\n", object->name);

	/* run any user-defined load hooks */
	list_for_each_entry(hook, &object->hooks_load, list)
		(*hook->hook)();

	/* add to the global func hash */
	list_for_each_entry(func, &object->funcs, list)
		hash_add_rcu(kpatch_func_hash, &func->node, func->old_addr);

out:
	up(&kpatch_mutex);

	/* no way to stop the module load on error */
	WARN(ret, "error (%d) patching newly loaded module '%s'\n", ret,
	     object->name);
	return 0;
}

int kpatch_register(struct kpatch_module *kpmod, bool replace)
{
	int ret, i, force = 0;
	struct kpatch_object *object, *object_err = NULL;
	struct kpatch_func *func;

	if (!kpmod->mod || list_empty(&kpmod->objects))
		return -EINVAL;

	down(&kpatch_mutex);

	if (kpmod->enabled) {
		ret = -EINVAL;
		goto err_up;
	}

	list_add_tail(&kpmod->list, &kpmod_list);

	if (!try_module_get(kpmod->mod)) {
		ret = -ENODEV;
		goto err_list;
	}

	/* Start the reference counting */
	kpatch_refcnt_start();

	/* memory barrier between func hash and refcnt write */
	smp_wmb();

	list_for_each_entry(object, &kpmod->objects, list) {
		/* Mark all funcs are under patching */
		list_for_each_entry(func, &object->funcs, list)
			func->op = KPATCH_OP_PATCH;

		ret = kpatch_link_object(kpmod, object);
		if (ret) {
			object_err = object;
			goto err_unlink;
		}

		if (!kpatch_object_linked(object)) {
			pr_notice("delaying patch of unloaded module '%s'\n",
				  object->name);
			continue;
		}

		if (strcmp(object->name, "vmlinux"))
			pr_notice("patching module '%s'\n", object->name);
	}

	if (replace)
		/* UNPATCH flag must be set after refcnt starting because
		 * refcnt initial value is same as success value */
		hash_for_each_rcu(kpatch_func_hash, i, func, node)
			func->op = KPATCH_OP_UNPATCH;

	/*
	 * Idle the CPUs, verify activeness safety, and atomically make the new
	 * functions visible to the ftrace handler.
	 */
	ret = kpatch_apply_patch(kpmod);

	/* We do not need refcounting anymore */
	kpatch_retprobe_remove_all();

	/*
	 * For the replace case, remove any obsolete funcs from the hash and
	 * the ftrace filter, and disable the owning patch module so that it
	 * can be removed.
	 */
	if (!ret && replace) {
		struct kpatch_module *kpmod2, *safe;

		hash_for_each_rcu(kpatch_func_hash, i, func, node) {
			if (func->op != KPATCH_OP_UNPATCH)
				continue;
			if (func->force)
				force = 1;
			hash_del_rcu(&func->node);
			WARN_ON(kpatch_ftrace_remove_func(func->old_addr));
		}

		list_for_each_entry_safe(kpmod2, safe, &kpmod_list, list) {
			if (kpmod == kpmod2)
				continue;

			kpmod2->enabled = false;
			pr_notice("unloaded patch module '%s'\n",
				  kpmod2->mod->name);

			/*
			 * Don't allow modules with forced functions to be
			 * removed because they might still be in use.
			 */
			if (!force)
				module_put(kpmod2->mod);

			list_del(&kpmod2->list);
		}
	}

	do_for_each_linked_func(kpmod, func) {
		func->op = KPATCH_OP_NONE;
	} while_for_each_linked_func();

	/* memory barrier between func hash and refcnt write */
	smp_wmb();

	/* NMI handlers can return to normal now */
	kpatch_refcnt_init();

	if (ret)
		goto err_ops;

	/* TODO: need TAINT_KPATCH */
	pr_notice_once("tainting kernel with TAINT_USER\n");
	add_taint(TAINT_USER, LOCKDEP_STILL_OK);

	pr_notice("loaded patch module '%s'\n", kpmod->mod->name);

	kpmod->enabled = true;

	up(&kpatch_mutex);
	return 0;

err_ops:
	if (replace)
		hash_for_each_rcu(kpatch_func_hash, i, func, node)
			func->op = KPATCH_OP_NONE;
err_unlink:
	list_for_each_entry(object, &kpmod->objects, list) {
		if (object == object_err)
			break;
		if (!kpatch_object_linked(object))
			continue;
		WARN_ON(kpatch_unlink_object(object));
	}
	module_put(kpmod->mod);

	/* memory barrier between func hash and refcnt write */
	smp_wmb();

	kpatch_refcnt_init();
err_list:
	list_del(&kpmod->list);
err_up:
	up(&kpatch_mutex);
	return ret;
}
EXPORT_SYMBOL(kpatch_register);

int kpatch_unregister(struct kpatch_module *kpmod)
{
	struct kpatch_object *object;
	struct kpatch_func *func;
	int ret, force = 0;

	down(&kpatch_mutex);

	if (!kpmod->enabled) {
	    ret = -EINVAL;
	    goto out;
	}

	/* Start the reference counting */
	kpatch_refcnt_start();

	/* memory barrier between func hash and state write */
	smp_wmb();

	do_for_each_linked_func(kpmod, func) {
		func->op = KPATCH_OP_UNPATCH;
		if (func->force)
			force = 1;
	} while_for_each_linked_func();

	ret = kpatch_remove_patch(kpmod);

	/* NMI handlers can return to normal now */
	kpatch_refcnt_init();

	if (ret) {
		do_for_each_linked_func(kpmod, func) {
			func->op = KPATCH_OP_NONE;
		} while_for_each_linked_func();
		goto out;
	}

	/*
	 * Wait for all existing NMI handlers to complete so that they don't
	 * see any changes to funcs or funcs->op that might occur after this
	 * point.
	 *
	 * Any handlers starting after this point will see the init refcnt.
	 */
	synchronize_rcu();

	list_for_each_entry(object, &kpmod->objects, list) {
		if (!kpatch_object_linked(object))
			continue;
		ret = kpatch_unlink_object(object);
		if (ret)
			goto out;
	}

	pr_notice("unloaded patch module '%s'\n", kpmod->mod->name);

	kpmod->enabled = false;

	/*
	 * Don't allow modules with forced functions to be removed because they
	 * might still be in use.
	 */
	if (!force)
		module_put(kpmod->mod);

	list_del(&kpmod->list);

out:
	up(&kpatch_mutex);
	return ret;
}
EXPORT_SYMBOL(kpatch_unregister);


static struct notifier_block kpatch_module_nb = {
	.notifier_call = kpatch_module_notify,
	.priority = INT_MIN, /* called last */
};

static int kpatch_init(void)
{
	int ret;

	ret = kpatch_populate_monitoring_task_pool(MONTASK_POOL_SIZE);
	if (ret)
		return ret;

	kpatch_root_kobj = kobject_create_and_add("kpatch", kernel_kobj);
	if (!kpatch_root_kobj) {
		ret = -ENOMEM;
		goto err_cleanup;
	}

	kpatch_patches_kobj = kobject_create_and_add("patches",
						     kpatch_root_kobj);
	if (!kpatch_patches_kobj) {
		ret = -ENOMEM;
		goto err_root_kobj;
	}

	ret = register_module_notifier(&kpatch_module_nb);
	if (ret)
		goto err_patches_kobj;

	return 0;

err_patches_kobj:
	kobject_put(kpatch_patches_kobj);
err_root_kobj:
	kobject_put(kpatch_root_kobj);
err_cleanup:
	kpatch_cleanup_monitoring_task_pool();
	return ret;
}

static void kpatch_exit(void)
{
	WARN_ON(kpatch_num_patched != 0);
	WARN_ON(unregister_module_notifier(&kpatch_module_nb));
	kobject_put(kpatch_patches_kobj);
	kobject_put(kpatch_root_kobj);
	kpatch_cleanup_monitoring_task_pool();
}

module_init(kpatch_init);
module_exit(kpatch_exit);
MODULE_LICENSE("GPL");
