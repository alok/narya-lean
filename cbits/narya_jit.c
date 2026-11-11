/*
 * cbits/narya_jit.c — Zero-Subprocess In-Process ARM64 W^X `MAP_JIT` / `mprotect` Runner
 *
 * Executes verified 32-bit little-endian ARMv8-A machine-code words emitted by
 * `Narya.Compiler.ThinEmitter` directly in-process in sub-microseconds (~300 ns on Apple Silicon
 * via reusable thread-local 64 KB `MAP_JIT` slab, vs ~35 ms spawning `clang` + `ld`).
 *
 * Strict W^X compliance:
 * - macOS (`__APPLE__ && __aarch64__`): `MAP_JIT` + `pthread_jit_write_protect_np` + `sys_icache_invalidate`
 * - Linux (`__linux__ && __aarch64__`): `mmap` + `mprotect(PROT_READ | PROT_EXEC)` + `__builtin___clear_cache`
 * - Non-AArch64 fallback: `narya_jit_supported()` returns 0 cleanly.
 */

#include <lean/lean.h>
#include <stdint.h>
#include <stddef.h>
#include <string.h>

typedef uint64_t (*narya_jit_fn_t)(uint64_t, uint64_t);

#if defined(__APPLE__) && defined(__aarch64__)
#include <sys/mman.h>
#include <pthread.h>
#include <libkern/OSCacheControl.h>

static _Thread_local void *tls_jit_slab = NULL;
static _Thread_local size_t tls_jit_cap = 0;

LEAN_EXPORT uint8_t narya_jit_supported(void) {
    return 1;
}

LEAN_EXPORT uint64_t narya_jit_run_u64(b_lean_obj_arg code, uint64_t arg0, uint64_t arg1) {
    size_t sz = lean_sarray_size(code);
    const uint8_t *bytes = lean_sarray_cptr(code);
    if (sz < 4 || (sz & 3) != 0) {
        return 0;
    }

    if (tls_jit_slab == NULL || sz > tls_jit_cap) {
        if (tls_jit_slab != NULL) {
            munmap(tls_jit_slab, tls_jit_cap);
            tls_jit_slab = NULL;
            tls_jit_cap = 0;
        }
        size_t alloc_sz = 65536;
        while (alloc_sz < sz) {
            alloc_sz *= 2;
        }
        void *mem = mmap(NULL, alloc_sz, PROT_READ | PROT_WRITE | PROT_EXEC,
                         MAP_PRIVATE | MAP_ANON | MAP_JIT, -1, 0);
        if (mem == MAP_FAILED) {
            return 0;
        }
        tls_jit_slab = mem;
        tls_jit_cap = alloc_sz;
    }

    pthread_jit_write_protect_np(0);
    memcpy(tls_jit_slab, bytes, sz);
    pthread_jit_write_protect_np(1);
    sys_icache_invalidate(tls_jit_slab, sz);

    narya_jit_fn_t fn = (narya_jit_fn_t)tls_jit_slab;
    return fn(arg0, arg1);
}

#elif defined(__linux__) && defined(__aarch64__)
#include <sys/mman.h>
#include <unistd.h>

static _Thread_local void *tls_jit_slab = NULL;
static _Thread_local size_t tls_jit_cap = 0;

LEAN_EXPORT uint8_t narya_jit_supported(void) {
    return 1;
}

LEAN_EXPORT uint64_t narya_jit_run_u64(b_lean_obj_arg code, uint64_t arg0, uint64_t arg1) {
    size_t sz = lean_sarray_size(code);
    const uint8_t *bytes = lean_sarray_cptr(code);
    if (sz < 4 || (sz & 3) != 0) {
        return 0;
    }

    if (tls_jit_slab == NULL || sz > tls_jit_cap) {
        if (tls_jit_slab != NULL) {
            munmap(tls_jit_slab, tls_jit_cap);
            tls_jit_slab = NULL;
            tls_jit_cap = 0;
        }
        size_t alloc_sz = 65536;
        while (alloc_sz < sz) {
            alloc_sz *= 2;
        }
        void *mem = mmap(NULL, alloc_sz, PROT_READ | PROT_WRITE,
                         MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        if (mem == MAP_FAILED) {
            return 0;
        }
        tls_jit_slab = mem;
        tls_jit_cap = alloc_sz;
    } else {
        if (mprotect(tls_jit_slab, tls_jit_cap, PROT_READ | PROT_WRITE) != 0) {
            return 0;
        }
    }

    memcpy(tls_jit_slab, bytes, sz);
    if (mprotect(tls_jit_slab, tls_jit_cap, PROT_READ | PROT_EXEC) != 0) {
        return 0;
    }
    __builtin___clear_cache((char *)tls_jit_slab, (char *)tls_jit_slab + sz);

    narya_jit_fn_t fn = (narya_jit_fn_t)tls_jit_slab;
    return fn(arg0, arg1);
}

#else

LEAN_EXPORT uint8_t narya_jit_supported(void) {
    return 0;
}

LEAN_EXPORT uint64_t narya_jit_run_u64(b_lean_obj_arg code, uint64_t arg0, uint64_t arg1) {
    (void)code;
    (void)arg0;
    (void)arg1;
    return 0;
}

#endif
