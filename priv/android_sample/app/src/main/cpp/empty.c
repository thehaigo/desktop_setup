#include <stddef.h>
#include <dlfcn.h>

void erlang_runtime_stub(void) {
    (void)0;
}

/*
 * liberlang.a references dlvsym which is not available in Android's bionic libc.
 * Provide a shim that ignores the version argument and delegates to dlsym.
 */
void *dlvsym(void *handle, const char *symbol, const char *version) {
    (void)version;
    return dlsym(handle, symbol);
}
