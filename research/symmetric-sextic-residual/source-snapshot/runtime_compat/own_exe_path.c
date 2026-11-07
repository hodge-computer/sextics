/* Application compatibility for the executor's PID namespace.
 * Lean 4.33.1 resolves its own executable using /proc/<getpid()>/exe.
 * The mounted procfs uses a different PID namespace, whereas /proc/self/exe
 * correctly identifies the same calling process. Redirect only this exact
 * self-executable lookup. No proof/kernel functions or access rights change.
 */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

ssize_t readlink(const char *path, char *buf, size_t bufsiz) {
  typedef ssize_t (*readlink_fn)(const char *, char *, size_t);
  static readlink_fn original;
  if (!original) original = (readlink_fn)dlsym(RTLD_NEXT, "readlink");
  char own[64];
  snprintf(own, sizeof own, "/proc/%ld/exe", (long)getpid());
  return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, bufsiz);
}
