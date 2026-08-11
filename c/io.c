#define _POSIX_C_SOURCE 200809L
// Effectful primitives. Ordinary values (Val::Prim) that enter a program only
// as the `io` argument the CLI passes to `main`. Mirrors src/io.rs. Every user
// function stays pure; try/else rolls back values, not external effects.
#include "snel.h"
#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static const char *PRIMS[] = {"read",   "write", "args",   "env",   "exe",   "spawn",
                              "list",   "stat",  "exists", "mkdir", "rmdir", "unlink",
                              "rename", "link",  "time",   "sleep", NULL};
static int g_argc;
static char **g_argv;
void io_set_args(int argc, char **argv) {
    g_argc = argc;
    g_argv = argv;
}

Val io_tab(void) {
    Tab *t = tab_new();
    for (int i = 0; PRIMS[i]; i++) {
        Bin k = bin_str(PRIMS[i]);
        Val v;
        v.k = V_PRIM;
        v.u.bin = bin_str(PRIMS[i]);
        tab_bind(t, k, v, NULL);
    }
    Val v;
    v.k = V_TAB;
    v.u.tab = t;
    return v;
}

static Val fail(bool *ok, char *err, size_t n, const char *m) {
    snprintf(err, n, "%s", m);
    *ok = false;
    return vnil();
}

bool is_u8_col(const Col *c);
uint8_t *col_bytes(const Col *c, size_t *len);
bool col_from_vals(Val *, size_t, Col **, SnelErr *);

// a [u8] argument's bytes; NULL if not a string
static uint8_t *arg_bytes(Val *args, size_t na, size_t i, size_t *n) {
    if (i >= na || args[i].k != V_VEC || !is_u8_col(args[i].u.vec))
        return NULL;
    return col_bytes(args[i].u.vec, n);
}
// a [u8] argument as a NUL-terminated C string (caller frees)
static char *arg_cstr(Val *args, size_t na, size_t i) {
    size_t n;
    uint8_t *b = arg_bytes(args, na, i, &n);
    if (!b)
        return NULL;
    char *s = malloc(n + 1);
    memcpy(s, b, n);
    s[n] = 0;
    free(b);
    return s;
}
static Val str_val(const uint8_t *b, size_t n) {
    Val v;
    v.k = V_VEC;
    v.u.vec = col_u8s(b, n);
    return v;
}

static Val spawn(Val *args, size_t na, bool *ok, char *err, size_t errlen) {
    char *prog = arg_cstr(args, na, 0);
    if (!prog || na < 4 || args[1].k != V_VEC || args[3].k != V_VEC) {
        free(prog);
        return fail(ok, err, errlen, "spawn: (prog, [argv], stdin, [envs])");
    }
    Col *ac = args[1].u.vec;
    size_t stdin_n;
    uint8_t *stdin_b = arg_bytes(args, na, 2, &stdin_n);
    if (!stdin_b) {
        free(prog);
        return fail(ok, err, errlen, "spawn: stdin must be a string");
    }
    char **argv = calloc(ac->len + 2, sizeof(char *));
    argv[0] = prog;
    for (size_t i = 0; i < ac->len; i++) {
        Val e = col_elem(ac, i);
        Val a[1] = {e};
        argv[i + 1] = arg_cstr(a, 1, 0);
        if (!argv[i + 1]) {
            argv[i + 1] = malloc(1);
            argv[i + 1][0] = 0;
        }
        val_drop(e);
    }
    // env entries, each "KEY=VALUE", set on top of the inherited environment
    Col *ec = args[3].u.vec;
    size_t nenv = ec->len;
    char **envs = calloc(nenv + 1, sizeof(char *));
    for (size_t i = 0; i < nenv; i++) {
        Val e = col_elem(ec, i);
        Val a[1] = {e};
        char *s = arg_cstr(a, 1, 0);
        envs[i] = s ? s : calloc(1, 1);
        val_drop(e);
    }
    int in[2], out[2];
    if (pipe(in) || pipe(out)) {
        free(stdin_b);
        return fail(ok, err, errlen, "spawn: pipe");
    }
    pid_t pid = fork();
    if (pid == 0) {
        for (size_t i = 0; i < nenv; i++) {
            char *eq = strchr(envs[i], '=');
            if (eq) {
                *eq = 0;
                setenv(envs[i], eq + 1, 1);
            }
        }
        dup2(in[0], 0);
        dup2(out[1], 1);
        close(in[1]);
        close(out[0]);
        execvp(prog, argv);
        _exit(127);
    }
    close(in[0]);
    close(out[1]);
    if (write(in[1], stdin_b, stdin_n) < 0) { /* ignore */
    }
    close(in[1]);
    free(stdin_b);
    uint8_t *buf = NULL;
    size_t cap = 0, len = 0;
    uint8_t chunk[4096];
    ssize_t r;
    while ((r = read(out[0], chunk, sizeof chunk)) > 0) {
        if (len + r > cap) {
            cap = (len + r) * 2 + 16;
            buf = realloc(buf, cap);
        }
        memcpy(buf + len, chunk, r);
        len += r;
    }
    close(out[0]);
    waitpid(pid, NULL, 0);
    Val v = str_val(buf, len);
    free(buf);
    return v;
}

Val call_prim(const Bin *name, Val *args, size_t na, bool *ok, char *err, size_t errlen) {
    *ok = true;
    const uint8_t *nm = bin_bytes(name);
    size_t nl = name->len;
    if (nl == 4 && !memcmp(nm, "read", 4)) {
        char *path = arg_cstr(args, na, 0);
        if (!path)
            return fail(ok, err, errlen, "read: arg 0 must be a string ([u8])");
        FILE *f = fopen(path, "rb");
        free(path);
        if (!f)
            return fail(ok, err, errlen, "read: cannot open");
        fseek(f, 0, SEEK_END);
        long sz = ftell(f);
        fseek(f, 0, SEEK_SET);
        uint8_t *buf = malloc(sz > 0 ? sz : 1);
        fread(buf, 1, sz, f);
        fclose(f);
        Val v = str_val(buf, sz);
        free(buf);
        return v;
    }
    if (nl == 5 && !memcmp(nm, "write", 5)) {
        char *path = arg_cstr(args, na, 0);
        size_t dn;
        uint8_t *db = arg_bytes(args, na, 1, &dn);
        if (!path || !db) {
            free(path);
            free(db);
            return fail(ok, err, errlen, "write: (path, bytes) as strings");
        }
        FILE *f = fopen(path, "wb");
        free(path);
        if (!f) {
            free(db);
            return fail(ok, err, errlen, "write: cannot open");
        }
        fwrite(db, 1, dn, f);
        fclose(f);
        free(db);
        return vnil();
    }
    if (nl == 4 && !memcmp(nm, "args", 4)) {
        Val *items = malloc((g_argc ? g_argc : 1) * sizeof(Val));
        size_t n = 0;
        for (int i = 1; i < g_argc; i++)
            items[n++] = str_val((const uint8_t *)g_argv[i], strlen(g_argv[i]));
        Col *c;
        SnelErr e2;
        if (!col_from_vals(items, n, &c, &e2))
            return fail(ok, err, errlen, "args");
        Val v;
        v.k = V_VEC;
        v.u.vec = c;
        return v;
    }
    if (nl == 3 && !memcmp(nm, "env", 3)) {
        extern char **environ;
        Tab *t = tab_new();
        for (char **e = environ; *e; e++) {
            char *eq = strchr(*e, '=');
            if (!eq)
                continue;
            Bin k = bin_new((const uint8_t *)*e, (size_t)(eq - *e));
            tab_bind(t, k, str_val((const uint8_t *)(eq + 1), strlen(eq + 1)), NULL);
        }
        Val v;
        v.k = V_TAB;
        v.u.tab = t;
        return v;
    }
    if (nl == 3 && !memcmp(nm, "exe", 3)) {
        char buf[4096];
        ssize_t k = readlink("/proc/self/exe", buf, sizeof buf - 1);
        if (k < 0)
            return fail(ok, err, errlen, "exe: cannot read /proc/self/exe");
        return str_val((const uint8_t *)buf, (size_t)k);
    }
    if (nl == 5 && !memcmp(nm, "spawn", 5))
        return spawn(args, na, ok, err, errlen);
    if (nl == 4 && !memcmp(nm, "list", 4)) {
        char *path = arg_cstr(args, na, 0);
        if (!path)
            return fail(ok, err, errlen, "list: path must be a string");
        DIR *d = opendir(path);
        free(path);
        if (!d)
            return fail(ok, err, errlen, "list: cannot open directory");
        Val *items = NULL;
        size_t n = 0, cap = 0;
        struct dirent *ent;
        while ((ent = readdir(d))) {
            if (!strcmp(ent->d_name, ".") || !strcmp(ent->d_name, ".."))
                continue; // match Rust read_dir
            if (n == cap) {
                cap = cap ? cap * 2 : 8;
                items = realloc(items, cap * sizeof(Val));
            }
            items[n++] = str_val((const uint8_t *)ent->d_name, strlen(ent->d_name));
        }
        closedir(d);
        Col *c;
        SnelErr e2;
        if (!col_from_vals(items, n, &c, &e2))
            return fail(ok, err, errlen, "list");
        Val v;
        v.k = V_VEC;
        v.u.vec = c;
        return v;
    }
    if (nl == 4 && !memcmp(nm, "stat", 4)) {
        char *path = arg_cstr(args, na, 0);
        if (!path)
            return fail(ok, err, errlen, "stat: path must be a string");
        struct stat st;
        int r = stat(path, &st);
        free(path);
        if (r != 0)
            return fail(ok, err, errlen, "stat: cannot stat");
        Tab *t = tab_new();
        tab_bind(t, bin_str("size"), vi64((int64_t)st.st_size), NULL);
        tab_bind(t, bin_str("mtime"), vi64((int64_t)st.st_mtime), NULL);
        tab_bind(t, bin_str("isdir"), vbit(S_ISDIR(st.st_mode)), NULL);
        Val v;
        v.k = V_TAB;
        v.u.tab = t;
        return v;
    }
    if (nl == 6 && !memcmp(nm, "exists", 6)) {
        char *path = arg_cstr(args, na, 0);
        if (!path)
            return fail(ok, err, errlen, "exists: path must be a string");
        bool e = access(path, F_OK) == 0;
        free(path);
        return vbit(e);
    }
    if (nl == 5 && !memcmp(nm, "mkdir", 5)) {
        char *p = arg_cstr(args, na, 0);
        if (!p)
            return fail(ok, err, errlen, "mkdir: path");
        int r = mkdir(p, 0777);
        free(p);
        if (r)
            return fail(ok, err, errlen, "mkdir failed");
        return vnil();
    }
    if (nl == 5 && !memcmp(nm, "rmdir", 5)) {
        char *p = arg_cstr(args, na, 0);
        if (!p)
            return fail(ok, err, errlen, "rmdir: path");
        int r = rmdir(p);
        free(p);
        if (r)
            return fail(ok, err, errlen, "rmdir failed");
        return vnil();
    }
    if (nl == 6 && !memcmp(nm, "unlink", 6)) {
        char *p = arg_cstr(args, na, 0);
        if (!p)
            return fail(ok, err, errlen, "unlink: path");
        int r = unlink(p);
        free(p);
        if (r)
            return fail(ok, err, errlen, "unlink failed");
        return vnil();
    }
    if (nl == 6 && !memcmp(nm, "rename", 6)) {
        char *a = arg_cstr(args, na, 0), *b = arg_cstr(args, na, 1);
        if (!a || !b) {
            free(a);
            free(b);
            return fail(ok, err, errlen, "rename: (from, to)");
        }
        int r = rename(a, b);
        free(a);
        free(b);
        if (r)
            return fail(ok, err, errlen, "rename failed");
        return vnil();
    }
    if (nl == 4 && !memcmp(nm, "link", 4)) {
        char *a = arg_cstr(args, na, 0), *b = arg_cstr(args, na, 1);
        if (!a || !b) {
            free(a);
            free(b);
            return fail(ok, err, errlen, "link: (from, to)");
        }
        int r = link(a, b);
        free(a);
        free(b);
        if (r)
            return fail(ok, err, errlen, "link failed");
        return vnil();
    }
    if (nl == 4 && !memcmp(nm, "time", 4)) {
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        return vi64((int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000);
    }
    if (nl == 5 && !memcmp(nm, "sleep", 5)) {
        if (na < 1 || args[0].k != V_I64)
            return fail(ok, err, errlen, "sleep needs an i64");
        int64_t ms = args[0].u.i;
        if (ms > 0) {
            struct timespec ts;
            ts.tv_sec = ms / 1000;
            ts.tv_nsec = (ms % 1000) * 1000000;
            nanosleep(&ts, NULL);
        }
        return vnil();
    }
    return fail(ok, err, errlen, "unknown primitive");
}
