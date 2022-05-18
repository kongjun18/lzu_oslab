/**
 * @file syscall.h
 * @brief 声明系统调用号、系统调用表和系统调用创建宏
 */
#ifndef __SYSCALL_H__
#define __SYSCALL_H__
#include <trap.h>
typedef int64_t (*fn_ptr)(struct trapframe *);                 /**< 系统调用指针类型 */
extern fn_ptr syscall_table[];
// extern long test_fork;
/// @{ @name 系统调用号
#define NR_syscalls  18                                     /**< 系统调用数量 */
#define NR_fork      1
#define NR_test_fork 2
#define NR_getpid    3
#define NR_getppid   4
#define NR_char   5
#define NR_block  6
#define NR_open   7
#define NR_close  8
#define NR_stat   9
#define NR_read  10
#define NR_reset 11
#define NR_brk 12
#define NR_sigaction 13
#define NR_kill 14
#define NR_exit 15
#define NR_sigreturn 16
#define NR_setpriority 17
/// @}

int64_t syscall(int64_t number, ...);

#endif /* end of include guard: __SYSCALL_H__ */
