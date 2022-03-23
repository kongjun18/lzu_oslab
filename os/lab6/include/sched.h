/**
 * @file sched.h
 * @brief 声明进程相关的数据类型和宏
 *
 * 进程拥有 4G 虚拟地址空间，并被划分成多个段，布局如下：
 * 0xFFFFFFFF----->+--------------+
 *                 |              |
 *                 |              |
 *                 |    Kernel    |
 *                 |              |
 *                 |              |
 * 0xC0000000----->---------------+
 *                 |    Hole      |
 * 0xBFFFFFF0----->---------------+
 *                 |    Stack     |
 *                 |      +       |
 *                 |      |       |
 *                 |      v       |
 *                 |              |
 *                 |              |
 *                 |      ^       |
 *                 |      |       |
 *                 |      +       |
 *                 | Dynamic data |
 *        brk----->+--------------+
 *                 |              |
 *                 | Static data  |
 *                 |              |
 *                 +--------------+
 *                 |              |
 *                 |     Text     |
 *                 |              |
 * 0x00010000----->---------------+
 *                 |   Reserved   |
 * 0x00000000----->+--------------+
 *
 * 段与段之间不一定是相连的，中间可能存在空洞。
 */
#ifndef __SCHED_H__
#define __SCHED_H__
#include <mm.h>
#include <trap.h>
#include <riscv.h>
#include <kdebug.h>
#include <fs/vfs.h>
#include <signal.h>

#define NR_TASKS             512                              /**< 系统最大进程数 */

#define LAST_TASK tasks[NR_TASKS - 1]                         /**< tasks[] 数组最后一项 */
#define FIRST_TASK tasks[0]                                   /**< tasks[] 数组第一项 */

/// @{ @name 进程状态
#define TASK_RUNNING         0                                /**< 正在运行 */
#define TASK_INTERRUPTIBLE   1                                /**< 可中断阻塞 */
#define TASK_UNINTERRUPTIBLE 2                                /**< 不可中断阻塞 */
#define TASK_ZOMBIE          3                                /**< 僵尸状态（进程已终止，但未被父进程回收）*/
#define TASK_STOPPED         4                                /**< 进程停止 */
/// @}

/// @{ 进程内存布局
#define START_CODE 0x10000                                    /**< 代码段起始地址 */
#define START_STACK 0xBFFFFFF0                                /**< 堆起始地址（最高地址处） */
#define START_KERNEL 0xC0000000                               /**< 内核区起始地址 */
/// @}

typedef struct trapframe context;                             /**< 处理器上下文 */

/** 信号处理函数 */
struct sigaction
{
    void (*sa_handler)(uint32_t); /* 对应某信号指定要采取的行动 */
    uint32_t sa_mask;             /* 对信号的屏蔽码，在信号程序执行时将阻塞对这些信号的处理 */
    uint32_t sa_flags;            /* 改变信号处理过程的信号集 */
    void (*sa_restorer)(void);    /* 恢复函数指针，由函数库Libc提供，用于清理用户态堆栈 */
};

/** 进程控制块 PCB(Process Control Block) */
struct task_struct {
    uint32_t signal;                /* 信号位图 */
    struct sigaction sigaction[32]; /* 信号执行属性结构,对应信号将要执行的操作和标志信息 */

    uint32_t uid;  /* 用户ID */
    uint32_t euid; /* 有效用户ID */
    uint32_t suid; /* 保存的设置用户id */
    uint32_t gid;  /* 组id */
    uint32_t egid; /* 有效组id */
    uint32_t sgid; /* 保存的设置组id */

    uint32_t exit_code;           /**< 返回码 */
    uint32_t pid;                 /**< 进程 ID */
    uint32_t pgid;                /**< 进程组 */
    uint64_t start_code;          /**< 代码段起始地址 */
    uint64_t start_rodata;        /**< 只读数据段起始地址 */
    uint64_t start_data;          /**< 数据段起始地址 */
    uint64_t end_data;            /**< 数据段结束地址 */
    uint64_t brk;                 /**< 堆结束地址 */
    uint64_t start_stack;         /**< 栈起始地址 */
    uint64_t start_kernel;        /**< 内核区起始地址 */
    uint32_t state;               /**< 进程调度状态 */
    uint32_t counter;             /**< 时间片大小 */
    uint32_t priority;            /**< 进程优先级 */
    struct vfs_inode *fd[4];
    struct task_struct *p_pptr;   /**< 父进程 */
    struct task_struct *p_cptr;   /**< 子进程 */
    struct task_struct *p_ysptr;  /**< 创建时间最晚的兄弟进程 */
    struct task_struct *p_osptr;  /**< 创建时间最早的兄弟进程 */
    uint32_t utime,stime;         /**< 用户态、内核态耗时 */
    uint32_t cutime,cstime;       /**< 进程及其子进程内核、用户态总耗时 */
    size_t start_time;            /**< 进程创建的时间 */
    uint64_t *pg_dir;             /**< 页目录地址 */
    context context;              /**< 处理器状态 */
    uint64_t sig_epc;             /**< 处理器状态，用于信号触发 */
};

/**
 * @brief 初始化进程 0
 * 手动进入中断处理，调用 sys_init() 初始化进程0
 * @see sys_init()
 * @note 这个宏使用了以下三个 GNU C 拓展：
 *       - [Locally Declared Labels](https://gcc.gnu.org/onlinedocs/gcc/Local-Labels.html)
 *       - [Labels as Values](https://gcc.gnu.org/onlinedocs/gcc/Labels-as-Values.html)
 *       - [Statements and Declarations in Expressions](https://gcc.gnu.org/onlinedocs/gcc/Statement-Exprs.html#Statement-Exprs)
 */
#define init_task0()                                                        \
({                                                                          \
    __label__ ret;                                                          \
    write_csr(scause, CAUSE_USER_ECALL);                                    \
    clear_csr(sstatus, SSTATUS_SPP);                                        \
    set_csr(sstatus, SSTATUS_SPIE);                                         \
    set_csr(sstatus, SSTATUS_UPIE);                                         \
    write_csr(sepc, &&ret - 4 - (SBI_END + LINEAR_OFFSET - START_CODE));    \
    write_csr(sscratch, (char*)&init_task + PAGE_SIZE);                     \
    register uint64_t a7 asm("a7") = 0;                                     \
    __asm__ __volatile__("call __alltraps \n\t" ::"r"(a7):"memory");        \
    ret: ;                                                                  \
})

/**
 * @brief 进程数据结构占用的页
 *
 * 进程 PCB 和内核态堆栈共用一页。
 * PCB 处于一页的低地址，内核态堆栈从页最高地址到低地址增长。
 */
union task_union {
    struct task_struct task;                                  /**< 进程控制块 */
    char stack[PAGE_SIZE];                                    /**< 内核态堆栈 */
};

extern struct task_struct *current;
extern struct task_struct *tasks[NR_TASKS];
extern union task_union init_task;
extern uint64_t stack_size;

void sched_init();
void schedule();
void save_context(context *context);
context* push_context(char *stack, context *context);
void switch_to(size_t task);
void interruptible_sleep_on(struct task_struct **p);
void sleep_on(struct task_struct **p);
void wake_up(struct task_struct **p);
uint32_t sys_pause();
void exit_process(size_t task, uint32_t exit_code);
void do_exit(uint32_t exit_code);

#endif /* end of include guard: __SCHED_H__ */
