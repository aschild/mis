/* Container portability only: Lean 4.19 asks for its own executable by
 * numeric PID, but this runtime's procfs exposes a different PID namespace.
 * Resolve only that exact self-executable lookup via /proc/self/exe.
 * No permission changes, file substitutions, or Lean proof hooks. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*real_readlink)(const char *, char *, size_t);
    if (!real_readlink) real_readlink = dlsym(RTLD_NEXT, "readlink");
    char own_exe[64];
    snprintf(own_exe, sizeof own_exe, "/proc/%ld/exe", (long)getpid());
    return real_readlink(strcmp(path, own_exe) == 0 ? "/proc/self/exe" : path,
                         buf, size);
}
