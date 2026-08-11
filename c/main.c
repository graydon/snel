// Snel CLI (C99 port). Mirrors src/main.rs: run/fmt/sni/bin/apply/lsp, and
// --remote, which allows `use x = "url"` to fetch (off by default).
#include "snel.h"
#include <libgen.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static char *read_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f)
        return NULL;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *s = malloc(sz + 1);
    fread(s, 1, sz, f);
    s[sz] = 0;
    fclose(f);
    return s;
}

// Fetch a remote unit's source. `file:` needs nothing; `http(s):` shells out to
// the system `curl` (via fork/exec, so no shell quoting is involved) rather
// than linking a TLS stack into the interpreter. Mirrors src/lib.rs fetch_url.
static char *fetch_url(const char *url, char *err, size_t errlen) {
    if (!strncmp(url, "file://", 7)) {
        char *s = read_file(url + 7);
        if (!s)
            snprintf(err, errlen, "%.200s: cannot open", url + 7);
        return s;
    }
    if (strncmp(url, "http://", 7) && strncmp(url, "https://", 8)) {
        snprintf(err, errlen, "unsupported url scheme: %.200s", url);
        return NULL;
    }
    int fd[2];
    if (pipe(fd)) {
        snprintf(err, errlen, "pipe failed");
        return NULL;
    }
    pid_t pid = fork();
    if (pid == 0) {
        dup2(fd[1], 1);
        close(fd[0]);
        close(fd[1]);
        execlp("curl", "curl", "-sL", "--fail", "--max-time", "30", url, (char *)NULL);
        _exit(127);
    }
    close(fd[1]);
    size_t cap = 4096, len = 0;
    char *buf = malloc(cap);
    ssize_t r;
    while ((r = read(fd[0], buf + len, cap - len - 1)) > 0) {
        len += (size_t)r;
        if (len + 1 >= cap) {
            cap *= 2;
            buf = realloc(buf, cap);
        }
    }
    close(fd[0]);
    buf[len] = 0;
    int st = 0;
    waitpid(pid, &st, 0);
    if (!WIFEXITED(st) || WEXITSTATUS(st) != 0) {
        free(buf);
        snprintf(err, errlen, "fetch failed: %.200s (curl exit %d)", url,
                 WIFEXITED(st) ? WEXITSTATUS(st) : -1);
        return NULL;
    }
    return buf;
}

// ---------- unit loader for `use` ----------
// Caches loaded units and detects import cycles (mirrors src/lib.rs FileLoader).
#define LOADER_MAX 64
typedef struct {
    Loader base;
    bool remote; // whether `use x = "url"` may fetch (CLI --remote)
    char dir[4096];
    Bin stack[LOADER_MAX]; // units currently loading -> cycle detection
    size_t depth;
    Bin cnames[LOADER_MAX]; // loaded-unit cache
    Val cvals[LOADER_MAX];
    size_t ncache;
} FileLoader;

static Val loader_load(Loader *self, const Bin *name, bool *ok, char *err, size_t errlen) {
    FileLoader *fl = (FileLoader *)self;
    for (size_t i = 0; i < fl->ncache; i++) // already loaded?
        if (bin_eq(&fl->cnames[i], name)) {
            *ok = true;
            return val_clone(fl->cvals[i]);
        }
    for (size_t i = 0; i < fl->depth; i++) // loading it already? -> cycle
        if (bin_eq(&fl->stack[i], name)) {
            snprintf(err, errlen, "import cycle through `%.*s`", (int)name->len, bin_bytes(name));
            *ok = false;
            return vnil();
        }
    char nm[256];
    size_t l = name->len < 255 ? name->len : 255;
    memcpy(nm, bin_bytes(name), l);
    nm[l] = 0;
    char path[4600];
    snprintf(path, sizeof path, "%s/%s.sn", fl->dir, nm);
    char *src = read_file(path);
    if (!src) {
        snprintf(err, errlen, "cannot open %s", path);
        *ok = false;
        return vnil();
    }
    size_t nds;
    SnelErr pe;
    Node *ds = parse_unit(src, &nds, &pe);
    if (!ds) {
        snprintf(err, errlen, "%s: parse error: %s", path, pe.msg);
        *ok = false;
        return vnil();
    }
    if (fl->depth < LOADER_MAX)
        fl->stack[fl->depth++] = *name; // push (shallow; name outlives the load)
    Val v;
    char eb[512];
    // Errors raised while evaluating the import belong to *its* text; put the
    // importing unit's text back afterwards.
    const char *outer = err_src();
    err_set_src(src);
    bool okp = eval_program(ds, nds, self, &v, eb, sizeof eb);
    err_set_src(outer);
    if (fl->depth > 0)
        fl->depth--; // pop
    if (!okp) {
        snprintf(err, errlen, "%s: %s", path, eb);
        *ok = false;
        return vnil();
    }
    if (fl->ncache < LOADER_MAX) {
        fl->cnames[fl->ncache] = bin_clone(*name);
        fl->cvals[fl->ncache] = val_clone(v);
        fl->ncache++;
    }
    *ok = true;
    return v;
}

// `use x = "url"`: fetch, evaluate, and cache under the same name as a local
// unit, so a URL import behaves exactly like a file one afterwards.
static Val loader_load_url(Loader *self, const Bin *name, const Bin *url, bool *ok, char *err,
                           size_t errlen) {
    FileLoader *fl = (FileLoader *)self;
    for (size_t i = 0; i < fl->ncache; i++)
        if (bin_eq(&fl->cnames[i], name)) {
            *ok = true;
            return val_clone(fl->cvals[i]);
        }
    char u[4096];
    size_t ul = url->len < sizeof u - 1 ? url->len : sizeof u - 1;
    memcpy(u, bin_bytes(url), ul);
    u[ul] = 0;
    *ok = false;
    if (!fl->remote) {
        snprintf(err, errlen, "remote units are disabled (pass --remote to allow `%.200s`)", u);
        return vnil();
    }
    for (size_t i = 0; i < fl->depth; i++)
        if (bin_eq(&fl->stack[i], name)) {
            snprintf(err, errlen, "import cycle through `%.*s`", (int)name->len, bin_bytes(name));
            return vnil();
        }
    char ferr[512] = {0};
    char *src = fetch_url(u, ferr, sizeof ferr);
    if (!src) {
        snprintf(err, errlen, "%s", ferr);
        return vnil();
    }
    size_t nds;
    SnelErr pe;
    Node *ds = parse_unit(src, &nds, &pe);
    if (!ds) {
        snprintf(err, errlen, "%.200s: parse error: %s", u, pe.msg);
        return vnil();
    }
    if (fl->depth < LOADER_MAX)
        fl->stack[fl->depth++] = *name;
    Val v;
    char eb[512];
    bool okp = eval_program(ds, nds, self, &v, eb, sizeof eb);
    if (fl->depth > 0)
        fl->depth--;
    if (!okp) {
        snprintf(err, errlen, "%.200s: %s", u, eb);
        return vnil();
    }
    if (fl->ncache < LOADER_MAX) {
        fl->cnames[fl->ncache] = bin_clone(*name);
        fl->cvals[fl->ncache] = val_clone(v);
        fl->ncache++;
    }
    *ok = true;
    return v;
}

bool g_remote = false; // set from the command line (--remote)

static void loader_init(FileLoader *fl, const char *path) {
    memset(fl, 0, sizeof *fl);
    fl->base.load = loader_load;
    fl->base.load_url = loader_load_url;
    fl->remote = g_remote;
    fl->base.data = NULL;
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s", path);
    char *d = dirname(tmp);
    snprintf(fl->dir, sizeof fl->dir, "%s", d);
}

// ---------- commands ----------
static int cmd_run(const char *path, bool roundtrip) {
    char *src = read_file(path);
    if (!src) {
        fprintf(stderr, "%s: cannot open\n", path);
        return 2;
    }
    err_set_src(src); // error spans are byte offsets; this turns them into lines
    size_t nds;
    SnelErr pe;
    Node *ds = parse_unit(src, &nds, &pe);
    if (!ds) {
        fprintf(stderr, "parse error (line %u): %s\n", err_line(pe.span), pe.msg);
        return 1;
    }
    FileLoader fl;
    loader_init(&fl, path);
    Val v;
    char eb[512];
    // `run` calls the unit's main(io); `bin` round-trips the pure module value
    bool ok = roundtrip ? eval_program(ds, nds, &fl.base, &v, eb, sizeof eb)
                        : run_program(ds, nds, &fl.base, &v, eb, sizeof eb);
    if (!ok) {
        fprintf(stderr, "%s\n", eb);
        return 1;
    }
    if (roundtrip) {
        uint8_t *buf = NULL;
        size_t len = 0, cap = 0;
        encode_val(&v, &buf, &len, &cap);
        size_t pos = 0;
        Val v2;
        SnelErr de;
        if (!decode_val(buf, len, &pos, &v2, &de)) {
            fprintf(stderr, "bin error: %s\n", de.msg);
            return 1;
        }
        char *a = fmt_val(&v), *b = fmt_val(&v2);
        printf("%s\n", b);
        if (strcmp(a, b) != 0) {
            fprintf(stderr, "round-trip MISMATCH\n");
            return 1;
        }
        return 0;
    }
    char *s = fmt_val(&v);
    printf("%s\n", s);
    return 0;
}

static int cmd_fmt(const char *path) {
    char *src = read_file(path);
    if (!src) {
        fprintf(stderr, "%s: cannot open\n", path);
        return 2;
    }
    err_set_src(src); // error spans are byte offsets; this turns them into lines
    size_t nds;
    SnelErr pe;
    Node *ds = parse_unit(src, &nds, &pe);
    if (!ds) {
        fprintf(stderr, "parse error (line %u): %s\n", err_line(pe.span), pe.msg);
        return 1;
    }
    char *out = fmt_program(ds, nds);
    printf("%s", out);
    return 0;
}

static int cmd_sni(const char *path) {
    char *src = read_file(path);
    if (!src) {
        fprintf(stderr, "%s: cannot open\n", path);
        return 2;
    }
    err_set_src(src); // error spans are byte offsets; this turns them into lines
    size_t nds;
    SnelErr pe;
    Node *ds = parse_unit(src, &nds, &pe);
    if (!ds) {
        fprintf(stderr, "parse error (line %u): %s\n", err_line(pe.span), pe.msg);
        return 1;
    }
    FileLoader fl;
    loader_init(&fl, path);
    Val v;
    char eb[512];
    if (!eval_program(ds, nds, &fl.base, &v, eb, sizeof eb)) {
        fprintf(stderr, "%s\n", eb);
        return 1;
    }
    printf("-- %016llx\n", (unsigned long long)fnv1a((const uint8_t *)src, strlen(src)));
    // the module doc, if any, leads the interface (blank line after it)
    Bin mdoc;
    if (module_doc(src, &mdoc)) {
        const uint8_t *d = bin_bytes(&mdoc);
        size_t dl = mdoc.len, a = 0;
        while (a <= dl) {
            size_t b = a;
            while (b < dl && d[b] != '\n')
                b++;
            printf("-- %.*s\n", (int)(b - a), d + a);
            if (b >= dl)
                break;
            a = b + 1;
        }
        printf("\n");
    }
    if (v.k == V_TAB) {
        Tab *t = v.u.tab;
        for (size_t i = 0; i < t->len; i++) {
            if (t->has_doc[i]) {
                const uint8_t *d = bin_bytes(&t->docs[i]);
                size_t dl = t->docs[i].len, a = 0;
                while (a <= dl) {
                    size_t b = a;
                    while (b < dl && d[b] != '\n')
                        b++;
                    printf("-- %.*s\n", (int)(b - a), d + a);
                    if (b >= dl)
                        break;
                    a = b + 1;
                }
            }
            char kbuf[256];
            size_t kl = t->keys[i].len < 255 ? t->keys[i].len : 255;
            memcpy(kbuf, bin_bytes(&t->keys[i]), kl);
            kbuf[kl] = 0;
            Ty ty = val_ty(&t->vals[i]);
            char *ts = fmt_ty(&ty);
            printf("pub %s : %s\n", kbuf, ts);
        }
    }
    return 0;
}

bool is_u8_col(const Col *c);
uint8_t *col_bytes(const Col *c, size_t *len);

// The child side of subprocess eval: decode a closure from stdin, apply it to
// `io`, and write the closure's [u8] response to stdout. Mirrors main.rs's
// `apply` arm. Reads stdin streamingly (it is a pipe, not seekable).
static int cmd_apply(void) {
    uint8_t *buf = NULL;
    size_t len = 0, cap = 0, r;
    uint8_t chunk[4096];
    while ((r = fread(chunk, 1, sizeof chunk, stdin)) > 0) {
        if (len + r > cap) {
            cap = (len + r) * 2 + 16;
            buf = realloc(buf, cap);
        }
        memcpy(buf + len, chunk, r);
        len += r;
    }
    size_t pos = 0;
    Val f;
    SnelErr de;
    if (!decode_val(buf, len, &pos, &f, &de)) {
        fprintf(stderr, "apply: decode: %s\n", de.msg);
        return 1;
    }
    FileLoader fl;
    loader_init(&fl, ".");
    Val v;
    char eb[512];
    if (!run_closure(&f, &fl.base, &v, eb, sizeof eb)) {
        fprintf(stderr, "%s\n", eb);
        return 1;
    }
    // the closure's result is its [u8] response body; ship those bytes as-is
    size_t n;
    uint8_t *b;
    if (v.k == V_VEC && is_u8_col(v.u.vec) && (b = col_bytes(v.u.vec, &n))) {
        fwrite(b, 1, n, stdout);
        free(b);
    } else {
        uint8_t *ob = NULL;
        size_t ol = 0, oc = 0;
        encode_val(&v, &ob, &ol, &oc);
        fwrite(ob, 1, ol, stdout);
        free(ob);
    }
    return 0;
}

int main(int argc, char **argv) {
    // `--remote` allows `use x = "url"` to fetch; off by default. `--no-remote`
    // forces it off. Both are stripped before the usual argument handling.
    bool no_remote = false;
    int w = 1;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--remote"))
            g_remote = true;
        else if (!strcmp(argv[i], "--no-remote"))
            no_remote = true;
        else
            argv[w++] = argv[i];
    }
    argc = w;
    argv[argc] = NULL;
    if (no_remote)
        g_remote = false;
    io_set_args(argc, argv);
    if (argc < 2) {
        fprintf(stderr, "usage: snel run|fmt|sni|bin FILE.sn | snel apply | snel lsp\n"
                        "       --remote allows `use x = \"url\"` to fetch\n");
        return 2;
    }
    const char *cmd = argv[1];
    if (!strcmp(cmd, "apply"))
        return cmd_apply();
    if (!strcmp(cmd, "lsp"))
        return lsp_serve();
    if (argc < 3) {
        fprintf(stderr, "usage: snel %s FILE.sn\n", cmd);
        return 2;
    }
    if (!strcmp(cmd, "run"))
        return cmd_run(argv[2], false);
    if (!strcmp(cmd, "bin"))
        return cmd_run(argv[2], true);
    if (!strcmp(cmd, "fmt"))
        return cmd_fmt(argv[2]);
    if (!strcmp(cmd, "sni"))
        return cmd_sni(argv[2]);
    fprintf(stderr, "unknown command `%s`\n", cmd);
    return 2;
}
