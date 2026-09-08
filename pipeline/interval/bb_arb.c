/* bb_arb.c — Phase 4(c) 第 2 段：Arb 分支定界驱动（单文件 C99）。
 *
 * 输入：emit_rpn.py 生成的 case 文件（格式 v1，见 emit_rpn.py 开头 docstring）：
 *   vars / box（端点 {"num","den"} 精确有理）/ prog（RPN 指令流，含结构化
 *   ite 节点）/ disj（比较型 prog 与 var_lt 备选）。push_const 的 num/den
 *   是任意大整数 —— 按十进制字符串直接喂 fmpz，不经 int64。
 *
 * 求值语义（对齐 docstring）：
 *   ite(c<0, then, else)：cond 球 hi<0 → then；lo>=0 → else；跨 0 → STRADDLE。
 *   ite mode "eq"：cond 恰 [0,0] → then；确定非零 → else；其余 STRADDLE。
 *   div 越零 / sqrt 负底 / log 非正 → INDET（该叶无法闭合，继续二分）。
 *
 * 驱动策略：从根盒起维护叶栈；每叶求值主 prog，未闭合（STRADDLE/INDET/
 *   值跨 0）先做精度阶梯 prec→128→256，仍不闭合 → 检查 disj 备选
 *   （比较型 lo>0；var_lt 型 hi_i<lo_j），任一命中即叶闭合；否则选最宽维
 *   按精确有理中点 (lo+hi)/2 二分（fmpz 任意精度，中点仍精确）。
 *   主 prog hi<=0 且无 disj 备选 → COUNTEREXAMPLE（不该发生，说明翻译错）。
 *
 * 退出码：0 闭合；1 COUNTEREXAMPLE；2 节点超限（打印未闭叶）；3 用法/数据错误。
 *
 * 编译（照抄 README「编译链接本地 GMP/MPFR/FLINT」节，加 -std=c99 -Wall -Wextra）：
 *   TOOLS=$(pwd)/pipeline/tools
 *   gcc -O2 -std=c99 -Wall -Wextra pipeline/interval/bb_arb.c -o pipeline/interval/bb_arb \
 *     -I$TOOLS/flint-3.3.1/include -I$TOOLS/mpfr-4.2.2/include -I$TOOLS/gmp-6.3.0/include \
 *     -L$TOOLS/flint-3.3.1/lib -lflint \
 *     -L$TOOLS/mpfr-4.2.2/lib -lmpfr \
 *     -L$TOOLS/gmp-6.3.0/lib -lgmp -lm \
 *     -Wl,-rpath,$TOOLS/flint-3.3.1/lib \
 *     -Wl,-rpath,$TOOLS/mpfr-4.2.2/lib \
 *     -Wl,-rpath,$TOOLS/gmp-6.3.0/lib
 */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <flint/flint.h>
#include <flint/fmpz.h>
#include <flint/fmpq.h>
#include <flint/mag.h>
#include <flint/arb.h>

#define EXIT_CLOSED 0
#define EXIT_CEX    1
#define EXIT_LIMIT  2
#define EXIT_ERR    3

/* ---------------- 通用工具 ---------------- */

static void die(int code, const char *fmt, ...) __attribute__((noreturn, format(printf, 2, 3)));

static void die(int code, const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    fprintf(stderr, "bb_arb: ");
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
    exit(code);
}

static void *xmalloc(size_t n)
{
    void *p = malloc(n);
    if (!p) die(EXIT_ERR, "内存不足");
    return p;
}

static void *xrealloc(void *p, size_t n)
{
    p = realloc(p, n);
    if (!p) die(EXIT_ERR, "内存不足");
    return p;
}

/* fmpz → 十进制字符串（flint_malloc 分配，用 flint_free 释放） */
static char *fz(const fmpz_t z)
{
    return fmpz_get_str(NULL, 10, z);
}

/* ---------------- 极小 JSON 解析器（递归下降，stdlib only） ----------------
 * 支持对象/数组/字符串/数字/true/false/null。
 * 数字不转 double —— 保留原始词法文本，大整数按十进制字符串进 fmpz。 */

typedef enum { J_NULL, J_BOOL, J_NUM, J_STR, J_ARR, J_OBJ } jtype;

typedef struct jv {
    jtype t;
    char *s;            /* J_STR：解码后文本；J_NUM：原始词法 */
    int b;              /* J_BOOL */
    struct jv **items;  /* J_ARR 元素 / J_OBJ 值 */
    char **keys;        /* J_OBJ 键（与 items 平行） */
    size_t n;
} jv;

typedef struct {
    const char *p;      /* 当前扫描位置 */
    const char *head;   /* 文本起点（报错算偏移用） */
    const char *name;   /* 文件名 */
} jp;

static void jerr(jp *ps, const char *msg) __attribute__((noreturn));
static void jerr(jp *ps, const char *msg)
{
    die(EXIT_ERR, "JSON 语法错误（%s 偏移 %ld）：%s…上下文 %.24s",
        ps->name, (long)(ps->p - ps->head), msg, ps->p);
}

static jv *jnew(jtype t)
{
    jv *v = xmalloc(sizeof(jv));
    memset(v, 0, sizeof(*v));
    v->t = t;
    return v;
}

static void jfree(jv *v)
{
    size_t i;
    if (!v) return;
    free(v->s);
    for (i = 0; i < v->n; i++) {
        jfree(v->items[i]);
        if (v->keys) free(v->keys[i]);
    }
    free(v->items);
    free(v->keys);
    free(v);
}

static void jskip(jp *ps)
{
    while (*ps->p == ' ' || *ps->p == '\t' || *ps->p == '\n' || *ps->p == '\r')
        ps->p++;
}

static int jhex(jp *ps)
{
    char c = *ps->p;
    int d;
    if (c >= '0' && c <= '9') d = c - '0';
    else if (c >= 'a' && c <= 'f') d = c - 'a' + 10;
    else if (c >= 'A' && c <= 'F') d = c - 'A' + 10;
    else jerr(ps, "\\u 后需 4 位十六进制");
    ps->p++;
    return d;
}

/* 把码点编成 UTF-8 追加到 buf */
static void jutfe8(char **buf, size_t *n, size_t *cap, unsigned long cp)
{
    unsigned char t[4];
    size_t k = 0, i;
    if (cp < 0x80) t[k++] = (unsigned char)cp;
    else if (cp < 0x800) {
        t[k++] = (unsigned char)(0xC0 | (cp >> 6));
        t[k++] = (unsigned char)(0x80 | (cp & 0x3F));
    } else if (cp < 0x10000) {
        t[k++] = (unsigned char)(0xE0 | (cp >> 12));
        t[k++] = (unsigned char)(0x80 | ((cp >> 6) & 0x3F));
        t[k++] = (unsigned char)(0x80 | (cp & 0x3F));
    } else {
        t[k++] = (unsigned char)(0xF0 | (cp >> 18));
        t[k++] = (unsigned char)(0x80 | ((cp >> 12) & 0x3F));
        t[k++] = (unsigned char)(0x80 | ((cp >> 6) & 0x3F));
        t[k++] = (unsigned char)(0x80 | (cp & 0x3F));
    }
    for (i = 0; i < k; i++) {
        if (*n + 2 >= *cap) { *cap *= 2; *buf = xrealloc(*buf, *cap); }
        (*buf)[(*n)++] = (char)t[i];
    }
}

/* 解析字符串字面量（ps->p 停在开引号），返回 malloc 的解码文本 */
static char *jstring(jp *ps)
{
    size_t cap = 16, n = 0;
    char *buf = xmalloc(cap);
    ps->p++;                                    /* 跳过开引号 */
    while (*ps->p != '"') {
        if (*ps->p == '\0') jerr(ps, "字符串未闭合");
        if (*ps->p == '\\') {
            ps->p++;
            switch (*ps->p) {
            case '"': case '\\': case '/':
                if (n + 2 >= cap) { cap *= 2; buf = xrealloc(buf, cap); }
                buf[n++] = *ps->p++;
                break;
            case 'b': if (n + 2 >= cap) { cap *= 2; buf = xrealloc(buf, cap); }
                      buf[n++] = '\b'; ps->p++; break;
            case 'f': buf[n++] = '\f'; ps->p++; break;
            case 'n': buf[n++] = '\n'; ps->p++; break;
            case 'r': buf[n++] = '\r'; ps->p++; break;
            case 't': buf[n++] = '\t'; ps->p++; break;
            case 'u': {
                unsigned long cp;
                ps->p++;
                cp  = (unsigned long)jhex(ps) << 12;
                cp |= (unsigned long)jhex(ps) << 8;
                cp |= (unsigned long)jhex(ps) << 4;
                cp |= (unsigned long)jhex(ps);
                if (cp >= 0xD800 && cp <= 0xDBFF &&
                    ps->p[0] == '\\' && ps->p[1] == 'u') {   /* 代理对 */
                    unsigned long lo;
                    ps->p += 2;
                    lo  = (unsigned long)jhex(ps) << 12;
                    lo |= (unsigned long)jhex(ps) << 8;
                    lo |= (unsigned long)jhex(ps) << 4;
                    lo |= (unsigned long)jhex(ps);
                    if (lo < 0xDC00 || lo > 0xDFFF) jerr(ps, "代理对非法");
                    cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                }
                jutfe8(&buf, &n, &cap, cp);
                break;
            }
            default:
                jerr(ps, "非法转义");
            }
        } else {
            if (n + 2 >= cap) { cap *= 2; buf = xrealloc(buf, cap); }
            buf[n++] = *ps->p++;
        }
    }
    ps->p++;                                    /* 跳过闭引号 */
    buf[n] = '\0';
    return buf;
}

/* 数字：JSON 语法，保留原始词法（供 fmpz_set_str 或报错） */
static jv *jnumber(jp *ps)
{
    jv *v = jnew(J_NUM);
    const char *st = ps->p;
    if (*ps->p == '-') ps->p++;
    if (*ps->p < '0' || *ps->p > '9') jerr(ps, "数字语法错");
    while (*ps->p >= '0' && *ps->p <= '9') ps->p++;
    if (*ps->p == '.') {
        ps->p++;
        while (*ps->p >= '0' && *ps->p <= '9') ps->p++;
    }
    if (*ps->p == 'e' || *ps->p == 'E') {
        ps->p++;
        if (*ps->p == '+' || *ps->p == '-') ps->p++;
        while (*ps->p >= '0' && *ps->p <= '9') ps->p++;
    }
    v->s = xmalloc((size_t)(ps->p - st) + 1);
    memcpy(v->s, st, (size_t)(ps->p - st));
    v->s[ps->p - st] = '\0';
    return v;
}

static jv *jvalue(jp *ps)
{
    jskip(ps);
    if (*ps->p == '{') {
        jv *v = jnew(J_OBJ);
        size_t cap = 4;
        ps->p++;
        jskip(ps);
        if (*ps->p == '}') { ps->p++; return v; }
        v->keys = xmalloc(cap * sizeof(char *));
        v->items = xmalloc(cap * sizeof(jv *));
        for (;;) {
            jskip(ps);
            if (*ps->p != '"') jerr(ps, "对象键需为字符串");
            if (v->n >= cap) {
                cap *= 2;
                v->keys = xrealloc(v->keys, cap * sizeof(char *));
                v->items = xrealloc(v->items, cap * sizeof(jv *));
            }
            v->keys[v->n] = jstring(ps);
            jskip(ps);
            if (*ps->p != ':') jerr(ps, "对象缺 ':'");
            ps->p++;
            v->items[v->n] = jvalue(ps);
            v->n++;
            jskip(ps);
            if (*ps->p == ',') { ps->p++; continue; }
            if (*ps->p == '}') { ps->p++; return v; }
            jerr(ps, "对象缺 ',' 或 '}'");
        }
    }
    if (*ps->p == '[') {
        jv *v = jnew(J_ARR);
        size_t cap = 4;
        ps->p++;
        jskip(ps);
        if (*ps->p == ']') { ps->p++; return v; }
        v->items = xmalloc(cap * sizeof(jv *));
        for (;;) {
            if (v->n >= cap) {
                cap *= 2;
                v->items = xrealloc(v->items, cap * sizeof(jv *));
            }
            v->items[v->n++] = jvalue(ps);
            jskip(ps);
            if (*ps->p == ',') { ps->p++; continue; }
            if (*ps->p == ']') { ps->p++; return v; }
            jerr(ps, "数组缺 ',' 或 ']'");
        }
    }
    if (*ps->p == '"') {
        jv *v = jnew(J_STR);
        v->s = jstring(ps);
        return v;
    }
    if (!strncmp(ps->p, "true", 4)) {
        jv *v = jnew(J_BOOL); v->b = 1; ps->p += 4; return v;
    }
    if (!strncmp(ps->p, "false", 5)) {
        jv *v = jnew(J_BOOL); v->b = 0; ps->p += 5; return v;
    }
    if (!strncmp(ps->p, "null", 4)) {
        ps->p += 4; return jnew(J_NULL);
    }
    if (*ps->p == '-' || (*ps->p >= '0' && *ps->p <= '9'))
        return jnumber(ps);
    jerr(ps, "无法识别的值");
}

static jv *jparse(const char *text, const char *name)
{
    jp ps = { text, text, name };
    jv *v = jvalue(&ps);
    jskip(&ps);
    if (*ps.p != '\0') jerr(&ps, "顶层之后有多余内容");
    return v;
}

/* 对象取键（无则 NULL） */
static const jv *jget(const jv *o, const char *key)
{
    size_t i;
    if (!o || o->t != J_OBJ) return NULL;
    for (i = 0; i < o->n; i++)
        if (!strcmp(o->keys[i], key)) return o->items[i];
    return NULL;
}

/* J_NUM → slong（变量下标等小整数） */
static slong jidx(const jv *v, const char *what)
{
    char *end;
    long r;
    if (!v || v->t != J_NUM) die(EXIT_ERR, "%s：需要整数", what);
    r = strtol(v->s, &end, 10);
    if (end == v->s || *end) die(EXIT_ERR, "%s：整数语法错（%s）", what, v->s);
    return (slong)r;
}

/* J_NUM → fmpz（任意精度十进制，拒绝小数/指数） */
static void jfmpz(fmpz_t z, const jv *v, const char *what)
{
    if (!v || v->t != J_NUM) die(EXIT_ERR, "%s：需要数字", what);
    if (strpbrk(v->s, ".eE")) die(EXIT_ERR, "%s：需要精确整数，收到 %s", what, v->s);
    if (fmpz_set_str(z, v->s, 10)) die(EXIT_ERR, "%s：整数解析失败（%s）", what, v->s);
}

/* {"num":n,"den":d} → fmpz 对；den 归一为正 */
static void jrat(fmpz_t n, fmpz_t d, const jv *o, const char *what)
{
    const jv *a, *b;
    if (!o || o->t != J_OBJ) die(EXIT_ERR, "%s：需要 {\"num\":..,\"den\":..}", what);
    a = jget(o, "num");
    b = jget(o, "den");
    jfmpz(n, a, what);
    jfmpz(d, b, what);
    if (fmpz_sgn(d) == 0) die(EXIT_ERR, "%s：den 为 0", what);
    if (fmpz_sgn(d) < 0) {
        fmpz_neg(n, n);
        fmpz_neg(d, d);
    }
}

/* ---------------- RPN 程序 ---------------- */

typedef enum {
    OP_PUSH_VAR, OP_PUSH_CONST,
    OP_ADD, OP_SUB, OP_MUL, OP_NEG, OP_DIV,
    OP_SQRT, OP_ATAN, OP_SIN, OP_COS, OP_ABS, OP_LOG,
    OP_ITE
} opk;

typedef struct prog prog;

typedef struct {
    opk op;
    slong vi;             /* push_var 下标 */
    fmpz_t cn, cd;        /* push_const 精确有理 num/den（大整数） */
    prog *pc, *pt, *pe;   /* ite 的 cond/then/else（嵌套 RPN） */
    int mode_eq;          /* ite mode=="eq" */
} instr;

struct prog {
    instr *is;
    size_t n;
    size_t total;         /* 含嵌套 ite 的指令总数 = 栈深上界 */
};

static const struct { const char *nm; opk k; } OPNAMES[] = {
    { "push_var", OP_PUSH_VAR }, { "push_const", OP_PUSH_CONST },
    { "add", OP_ADD }, { "sub", OP_SUB }, { "mul", OP_MUL }, { "neg", OP_NEG },
    { "div", OP_DIV }, { "sqrt", OP_SQRT }, { "atan", OP_ATAN },
    { "sin", OP_SIN }, { "cos", OP_COS }, { "abs", OP_ABS }, { "log", OP_LOG },
};

static void prog_free(prog *p)
{
    size_t i;
    if (!p) return;
    for (i = 0; i < p->n; i++) {
        fmpz_clear(p->is[i].cn);
        fmpz_clear(p->is[i].cd);
        prog_free(p->is[i].pc);
        prog_free(p->is[i].pt);
        prog_free(p->is[i].pe);
    }
    free(p->is);
    free(p);
}

static prog *compile_prog(const jv *arr, slong nvars, const char *what)
{
    prog *p;
    size_t i;
    int k;

    if (!arr || arr->t != J_ARR || arr->n == 0)
        die(EXIT_ERR, "%s：prog 需为非空数组", what);
    p = xmalloc(sizeof(prog));
    p->n = arr->n;
    p->total = 0;
    p->is = xmalloc(arr->n * sizeof(instr));
    memset(p->is, 0, arr->n * sizeof(instr));

    for (i = 0; i < arr->n; i++) {
        const jv *e = arr->items[i];
        const jv *namev = NULL, *arge = NULL;
        instr *in = &p->is[i];
        fmpz_init(in->cn);
        fmpz_init(in->cd);

        if (e->t == J_OBJ) {                       /* 结构化 ite 节点 */
            const jv *ite = jget(e, "ite");
            const jv *mode;
            if (!ite || ite->t != J_OBJ)
                die(EXIT_ERR, "%s：指令 %lu 需为 ite 节点", what, (unsigned long)i);
            in->op = OP_ITE;
            in->pc = compile_prog(jget(ite, "cond"), nvars, "ite.cond");
            in->pt = compile_prog(jget(ite, "then"), nvars, "ite.then");
            in->pe = compile_prog(jget(ite, "else"), nvars, "ite.else");
            mode = jget(ite, "mode");
            if (mode) {
                if (mode->t != J_STR || strcmp(mode->s, "eq"))
                    die(EXIT_ERR, "%s：ite.mode 仅支持 \"eq\"", what);
                in->mode_eq = 1;
            }
            p->total += 1 + in->pc->total + in->pt->total + in->pe->total;
            continue;
        }
        if (e->t != J_ARR || e->n == 0 || e->n > 2 || e->items[0]->t != J_STR)
            die(EXIT_ERR, "%s：指令 %lu 格式错", what, (unsigned long)i);
        namev = e->items[0];
        if (e->n == 2) arge = e->items[1];
        for (k = 0; k < (int)(sizeof(OPNAMES) / sizeof(OPNAMES[0])); k++)
            if (!strcmp(namev->s, OPNAMES[k].nm)) break;
        if (k == (int)(sizeof(OPNAMES) / sizeof(OPNAMES[0])))
            die(EXIT_ERR, "%s：未知 op \"%s\"", what, namev->s);
        in->op = OPNAMES[k].k;

        switch (in->op) {
        case OP_PUSH_VAR:
            if (!arge) die(EXIT_ERR, "%s：push_var 缺下标", what);
            in->vi = jidx(arge, "push_var 下标");
            if (in->vi < 0 || in->vi >= nvars)
                die(EXIT_ERR, "%s：push_var 下标 %ld 越界（nvars=%ld）",
                    what, (long)in->vi, (long)nvars);
            break;
        case OP_PUSH_CONST: {
            if (!arge) die(EXIT_ERR, "%s：push_const 缺 num/den", what);
            jrat(in->cn, in->cd, arge, "push_const 常量");
            break;
        }
        default:
            if (arge) die(EXIT_ERR, "%s：op \"%s\" 不带参数", what, namev->s);
            break;
        }
        p->total += 1;
    }
    return p;
}

/* 静态检查 RPN 栈纪律：程序从相对深度 0 起执行，从不下溢且恰好净剩 1。
   ite 的 cond/then/else 各自递归检查。坏 prog 早死，免得运行期栈错乱。 */
static void check_prog(const prog *p, const char *what)
{
    size_t i;
    long d = 0;
    for (i = 0; i < p->n; i++) {
        const instr *in = &p->is[i];
        switch (in->op) {
        case OP_PUSH_VAR: case OP_PUSH_CONST: case OP_ITE:
            d++; break;
        case OP_ADD: case OP_SUB: case OP_MUL: case OP_DIV:
            if (d < 2) die(EXIT_ERR, "%s：二元 op 栈下溢", what);
            d--; break;
        default:
            if (d < 1) die(EXIT_ERR, "%s：一元 op 栈下溢", what);
            break;
        }
        if (in->op == OP_ITE) {
            check_prog(in->pc, "ite.cond");
            check_prog(in->pt, "ite.then");
            check_prog(in->pe, "ite.else");
        }
    }
    if (d != 1) die(EXIT_ERR, "%s：prog 净剩 %ld 个栈值（应为 1）", what, d);
}

/* ---------------- Arb 栈式求值器 ---------------- */

typedef enum { EV_OK, EV_STRADDLE, EV_INDET } evres;

/* guard 跨 0 并集兜底阈值：cond 球宽 < 2^-6 才允许 then∪else 兜底。
   动机：guard 边界单元纯符号二分不终止（严格跨 0 残差单元在另一维
   二分时成倍增殖）；先把单元二分到足够薄、再对薄 guard 单元用并集
   （恒 sound 超集）完备化 —— 优先产出分支选择的干净叶，仅薄边界单元
   退化为并集叶。阈值只影响叶的粒度/数量，不影响 soundness。 */
#define UNION_EPS (1.0 / 64.0)

/* 在 vars（每变量一个 Arb 区间）上执行 RPN，结果留在栈顶。
   stk 容量 ≥ p->total + 3（每条指令净入栈至多 1；union 兜底再借 2 个临时位）。
   ufall=0 严格模式：ite guard 未定 → EV_STRADDLE，并把该 cond 球宽下界
     记入 *min_sw（多 guard 取最小；可为 NULL）。
   ufall=1 兜底模式：guard 未定 → 取 then∪else（sound 超集，对齐 emit_rpn
     冒烟求值器的 STRADDLE 语义）。 */
static evres eval_prog(const prog *p, arb_srcptr vars, arb_t *stk,
                       size_t *sp, slong prec, int ufall, double *min_sw)
{
    size_t i;
    for (i = 0; i < p->n; i++) {
        const instr *in = &p->is[i];
        if (in->op == OP_PUSH_VAR) {
            arb_set(stk[*sp], vars + in->vi);
            (*sp)++;
        } else if (in->op == OP_PUSH_CONST) {
            /* 大整数 num/den：fmpz 直接进 fmpq，arb_set_fmpq 产包含精确值的球 */
            fmpq_t q;
            fmpq_init(q);
            fmpz_set(fmpq_numref(q), in->cn);
            fmpz_set(fmpq_denref(q), in->cd);
            arb_set_fmpq(stk[*sp], q, prec);
            fmpq_clear(q);
            (*sp)++;
        } else if (in->op == OP_ITE) {
            evres cs = eval_prog(in->pc, vars, stk, sp, prec, ufall, min_sw);
            if (cs != EV_OK) return cs;
            (*sp)--;
            {
                arb_t c;
                int take_then = -1;
                arb_init(c);
                arb_set(c, stk[*sp]);
                if (in->mode_eq) {
                    /* ite(c=0,..)：恰 [0,0] → then；确定非零 → else */
                    if (arb_is_zero(c)) take_then = 1;
                    else if (arb_is_positive(c) || arb_is_negative(c)) take_then = 0;
                } else {
                    /* ite(c<0,..)：hi<0 → then；lo>=0 → else */
                    if (arb_is_negative(c)) take_then = 1;
                    else if (arb_is_nonnegative(c)) take_then = 0;
                }
                if (take_then >= 0) {
                    arb_clear(c);
                    {
                        evres bs = eval_prog(take_then ? in->pt : in->pe,
                                             vars, stk, sp, prec, ufall, min_sw);
                        if (bs != EV_OK) return bs;
                    }
                } else if (!ufall) {
                    if (min_sw) {   /* 记录跨 0 guard 的球宽（取最小） */
                        arf_t a, b;
                        arf_init(a);
                        arf_init(b);
                        arb_get_lbound_arf(a, c, prec);
                        arb_get_ubound_arf(b, c, prec);
                        arf_sub(a, b, a, prec, ARF_RND_UP);
                        {
                            double w = arf_get_d(a, ARF_RND_UP);
                            if (w > 0 && w < *min_sw) *min_sw = w;
                        }
                        arf_clear(a);
                        arf_clear(b);
                    }
                    arb_clear(c);
                    return EV_STRADDLE;
                } else {
                    /* 兜底：value ⊆ then(box) ∪ else(box)，取并集继续 */
                    arb_t tv, ev;
                    evres ts, es;
                    arb_init(tv);
                    arb_init(ev);
                    arb_clear(c);
                    ts = eval_prog(in->pt, vars, stk, sp, prec, 1, NULL);
                    if (ts != EV_OK) { arb_clear(tv); arb_clear(ev); return ts; }
                    (*sp)--;
                    arb_set(tv, stk[*sp]);
                    es = eval_prog(in->pe, vars, stk, sp, prec, 1, NULL);
                    if (es != EV_OK) { arb_clear(tv); arb_clear(ev); return es; }
                    (*sp)--;
                    arb_set(ev, stk[*sp]);
                    arb_union(stk[*sp], tv, ev, prec);
                    arb_clear(tv);
                    arb_clear(ev);
                    (*sp)++;
                }
            }
        } else if (in->op == OP_ADD || in->op == OP_SUB ||
                   in->op == OP_MUL || in->op == OP_DIV) {
            arb_t a, b;
            if (*sp < 2) die(EXIT_ERR, "运行期 RPN 栈下溢");
            (*sp) -= 2;
            arb_init(a); arb_init(b);
            arb_set(a, stk[*sp]);
            arb_set(b, stk[*sp + 1]);
            if (in->op == OP_ADD) arb_add(a, a, b, prec);
            else if (in->op == OP_SUB) arb_sub(a, a, b, prec);
            else if (in->op == OP_MUL) arb_mul(a, a, b, prec);
            else {
                if (arb_contains_zero(b)) {       /* div 越零 → INDET */
                    arb_clear(a); arb_clear(b);
                    return EV_INDET;
                }
                arb_div(a, a, b, prec);
            }
            arb_set(stk[*sp], a);
            arb_clear(a); arb_clear(b);
            (*sp)++;
        } else {
            arb_t a;
            if (*sp < 1) die(EXIT_ERR, "运行期 RPN 栈下溢");
            (*sp)--;
            arb_init(a);
            arb_set(a, stk[*sp]);
            switch (in->op) {
            case OP_NEG:  arb_neg(a, a); break;
            case OP_ABS:  arb_abs(a, a); break;
            case OP_ATAN: arb_atan(a, a, prec); break;
            case OP_SIN:  arb_sin(a, a, prec); break;
            case OP_COS:  arb_cos(a, a, prec); break;
            case OP_SQRT:
                if (arb_is_negative(a)) {         /* sqrt 负底 → INDET */
                    arb_clear(a);
                    return EV_INDET;
                }
                if (arb_is_nonnegative(a)) {
                    arb_sqrt(a, a, prec);
                } else {
                    /* 跨 0：外扩成 ball(0,M)（M=|x| 上界）再开方，sound 超集 */
                    mag_t m;
                    mag_init(m);
                    arb_get_mag(m, a);
                    arb_zero(a);
                    mag_set(arb_radref(a), m);
                    mag_clear(m);
                    arb_sqrt(a, a, prec);
                }
                break;
            case OP_LOG:
                /* log 非正（含跨 0）→ INDET；lo>0 时球中点必 >0，arb_log 合法 */
                if (!arb_is_positive(a)) {
                    arb_clear(a);
                    return EV_INDET;
                }
                arb_log(a, a, prec);
                break;
            default:
                die(EXIT_ERR, "运行期未知 op");
            }
            arb_set(stk[*sp], a);
            arb_clear(a);
            (*sp)++;
        }
    }
    return EV_OK;
}

/* ---------------- 叶（盒）与队列 ---------------- */

typedef struct {
    slong nv;
    fmpz *ln, *ld, *hn, *hd;   /* 每维 [ln/ld, hn/hd]，den>0 */
} leaf;

static void leaf_init(leaf *L, slong nv)
{
    slong i;
    L->nv = nv;
    L->ln = xmalloc((size_t)nv * sizeof(fmpz));
    L->ld = xmalloc((size_t)nv * sizeof(fmpz));
    L->hn = xmalloc((size_t)nv * sizeof(fmpz));
    L->hd = xmalloc((size_t)nv * sizeof(fmpz));
    for (i = 0; i < nv; i++) {
        fmpz_init(L->ln + i); fmpz_init(L->ld + i);
        fmpz_init(L->hn + i); fmpz_init(L->hd + i);
    }
}

static void leaf_free(leaf *L)
{
    slong i;
    for (i = 0; i < L->nv; i++) {
        fmpz_clear(L->ln + i); fmpz_clear(L->ld + i);
        fmpz_clear(L->hn + i); fmpz_clear(L->hd + i);
    }
    free(L->ln); free(L->ld); free(L->hn); free(L->hd);
}

static void leaf_copy(leaf *dst, const leaf *src)
{
    leaf_init(dst, src->nv);
    {
        slong i;
        for (i = 0; i < src->nv; i++) {
            fmpz_set(dst->ln + i, src->ln + i);
            fmpz_set(dst->ld + i, src->ld + i);
            fmpz_set(dst->hn + i, src->hn + i);
            fmpz_set(dst->hd + i, src->hd + i);
        }
    }
}

/* 叶栈（数组实现，LIFO） */
typedef struct {
    leaf *v;
    size_t n, cap;
} leafq;

static void qpush(leafq *q, const leaf *L)
{
    if (q->n >= q->cap) {
        q->cap = q->cap ? q->cap * 2 : 16;
        q->v = xrealloc(q->v, q->cap * sizeof(leaf));
    }
    leaf_copy(&q->v[q->n++], L);
}

static void qpop(leafq *q, leaf *out)   /* 所有权转移给 out */
{
    *out = q->v[--q->n];
}

/* 宽 wi = (hn·ld − ln·hd)/(ld·hd)；交叉相乘比较（分母均正）。
   返回最宽维下标；所有维宽 0 → -1。 */
static slong widest_dim(const leaf *L)
{
    slong i, best = -1;
    fmpz_t wn, wd, bn, bd, t1, t2;
    fmpz_init(wn); fmpz_init(wd); fmpz_init(bn); fmpz_init(bd);
    fmpz_init(t1); fmpz_init(t2);
    for (i = 0; i < L->nv; i++) {
        fmpz_mul(wn, L->hn + i, L->ld + i);
        fmpz_submul(wn, L->ln + i, L->hd + i);   /* wn = hn*ld - ln*hd */
        if (fmpz_is_zero(wn)) continue;
        fmpz_mul(wd, L->ld + i, L->hd + i);
        /* 与当前最宽比较：wn*bd > bn*wd ⟺ wi > w_best（交叉相乘，分母正） */
        if (best >= 0) {
            fmpz_mul(t1, wn, bd);
            fmpz_mul(t2, bn, wd);
            if (fmpz_cmp(t1, t2) <= 0) continue;
        }
        best = i;
        fmpz_set(bn, wn);
        fmpz_set(bd, wd);
    }
    fmpz_clear(wn); fmpz_clear(wd); fmpz_clear(bn); fmpz_clear(bd);
    fmpz_clear(t1); fmpz_clear(t2);
    return best;
}

/* ---------------- 证书（闭叶收集 + JSON 输出） ---------------- */

typedef struct {
    leaf L;
    char hit[48];        /* "main" | "disj:k" | "var_lt:i,j" */
} cleaf;

typedef struct {
    cleaf *v;
    size_t n, cap;
} cleafq;

static void closed_add(cleafq *c, const leaf *L, const char *hit)
{
    if (c->n >= c->cap) {
        c->cap = c->cap ? c->cap * 2 : 16;
        c->v = xrealloc(c->v, c->cap * sizeof(cleaf));
    }
    leaf_copy(&c->v[c->n].L, L);
    snprintf(c->v[c->n].hit, sizeof(c->v[c->n].hit), "%s", hit);
    c->n++;
}

/* JSON 字符串（转义 " \ 与控制字符） */
static void fjson_str(FILE *f, const char *s)
{
    const unsigned char *p;
    fputc('"', f);
    for (p = (const unsigned char *)s; *p; p++) {
        if (*p == '"' || *p == '\\') fprintf(f, "\\%c", *p);
        else if (*p < 0x20) fprintf(f, "\\u%04x", *p);
        else fputc(*p, f);
    }
    fputc('"', f);
}

static void fjson_rat(FILE *f, const fmpz_t n, const fmpz_t d)
{
    char *ns = fz(n), *ds = fz(d);
    fprintf(f, "{\"num\": %s, \"den\": %s}", ns, ds);
    flint_free(ns);
    flint_free(ds);
}

static void fjson_box(FILE *f, const leaf *L)
{
    slong i;
    fputc('[', f);
    for (i = 0; i < L->nv; i++) {
        if (i) fputs(", ", f);
        fputc('[', f);
        fjson_rat(f, L->ln + i, L->ld + i);
        fputs(", ", f);
        fjson_rat(f, L->hn + i, L->hd + i);
        fputc(']', f);
    }
    fputc(']', f);
}

static void print_box_human(FILE *f, const leaf *L, char **names)
{
    slong i;
    for (i = 0; i < L->nv; i++) {
        char *a = fz(L->ln + i), *b = fz(L->ld + i);
        char *c = fz(L->hn + i), *d = fz(L->hd + i);
        fprintf(f, "%s%s in [%s/%s, %s/%s]", i ? ", " : "",
                names ? names[i] : "?", a, b, c, d);
        flint_free(a); flint_free(b); flint_free(c); flint_free(d);
    }
}

/* 盒一维 [lo,hi]（精确有理）→ 包含它的 Arb 球：
   mid=(lo+hi)/2、rad=(hi-lo)/2 精确有理；arb_set_fmpq 各自产生包含精确值的
   球，半径取 rad 上界 + mid 球半径（全部外向），所得球必 ⊇ [lo,hi]。 */
static void set_var_interval(arb_t dst, const fmpz_t ln, const fmpz_t ld,
                             const fmpz_t hn, const fmpz_t hd, slong prec)
{
    fmpq_t mid, rad;
    arb_t am, ar;
    mag_t R;
    fmpq_init(mid);
    fmpq_init(rad);
    /* mid = (ln*hd + hn*ld) / (2*ld*hd) */
    fmpz_mul(fmpq_numref(mid), ln, hd);
    fmpz_addmul(fmpq_numref(mid), hn, ld);
    fmpz_mul(fmpq_denref(mid), ld, hd);
    fmpz_mul_2exp(fmpq_denref(mid), fmpq_denref(mid), 1);
    /* rad = (hn*ld - ln*hd) / (2*ld*hd)（≥0，装载/二分保证 lo<=hi） */
    fmpz_mul(fmpq_numref(rad), hn, ld);
    fmpz_submul(fmpq_numref(rad), ln, hd);
    fmpz_mul(fmpq_denref(rad), ld, hd);
    fmpz_mul_2exp(fmpq_denref(rad), fmpq_denref(rad), 1);
    arb_init(am);
    arb_init(ar);
    arb_set_fmpq(am, mid, prec);   /* 球包含精确中点 */
    arb_set_fmpq(ar, rad, prec);   /* 球包含精确半径 */
    arb_zero(dst);
    arf_set(arb_midref(dst), arb_midref(am));
    mag_init(R);
    arb_get_mag(R, ar);            /* ≥ |rad| 的上界 */
    mag_add(R, R, arb_radref(am)); /* 并入中点球的半径误差 */
    mag_set(arb_radref(dst), R);
    mag_clear(R);
    arb_clear(am);
    arb_clear(ar);
    fmpq_clear(mid);
    fmpq_clear(rad);
}

/* ---------------- disj 备选 ---------------- */

typedef struct {
    int is_varlt;
    prog *p;             /* 比较型析取项 */
    slong vi, vj;        /* var_lt: y_vi < y_vj */
} disjunct;

typedef struct {
    disjunct *v;
    size_t n;
} disjq;

/* ---------------- 主程序 ---------------- */

static void usage(void)
{
    fprintf(stderr,
            "用法: bb_arb <case.json> [--max-nodes N] [--prec P] [--cert out.json]\n");
    exit(EXIT_ERR);
}

int main(int argc, char **argv)
{
    const char *path = NULL, *certpath = NULL;
    slong prec = 64;
    long max_nodes = 1L << 16;
    int i;

    /* ---- 命令行 ---- */
    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--max-nodes") && i + 1 < argc) {
            max_nodes = strtol(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--prec") && i + 1 < argc) {
            prec = (slong)strtol(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--cert") && i + 1 < argc) {
            certpath = argv[++i];
        } else if (argv[i][0] == '-' && argv[i][1] != '\0') {
            usage();
        } else if (!path) {
            path = argv[i];
        } else {
            usage();
        }
    }
    if (!path) usage();
    if (prec < 2 || prec > 4096) die(EXIT_ERR, "--prec 需在 [2,4096]");
    if (max_nodes < 1) die(EXIT_ERR, "--max-nodes 需 >= 1");

    /* ---- 读文件 + JSON 解析 ---- */
    {
        FILE *f = fopen(path, "rb");
        long sz;
        char *text;
        jv *root, *jid, *jvars, *jbox, *jprog, *jdisj;
        if (!f) die(EXIT_ERR, "无法打开 %s", path);
        fseek(f, 0, SEEK_END);
        sz = ftell(f);
        fseek(f, 0, SEEK_SET);
        text = xmalloc((size_t)sz + 1);
        if (fread(text, 1, (size_t)sz, f) != (size_t)sz)
            die(EXIT_ERR, "读取 %s 失败", path);
        text[sz] = '\0';
        fclose(f);

        root = jparse(text, path);
        free(text);

        jid   = (jv *)jget(root, "id");
        jvars = (jv *)jget(root, "vars");
        jbox  = (jv *)jget(root, "box");
        jprog = (jv *)jget(root, "prog");
        jdisj = (jv *)jget(root, "disj");
        if (!jid || jid->t != J_STR) die(EXIT_ERR, "case 缺 id");
        /* id 字符串要活到证书输出，先复制（root 树随后释放） */
        char *caseid = xmalloc(strlen(jid->s) + 1);
        strcpy(caseid, jid->s);
        if (!jvars || jvars->t != J_ARR || jvars->n == 0) die(EXIT_ERR, "case 缺 vars");
        if (!jbox || jbox->t != J_ARR) die(EXIT_ERR, "case 缺 box");
        if (!jprog) die(EXIT_ERR, "case 缺 prog");

        /* ---- 变量表 ---- */
        slong nvars = (slong)jvars->n;
        char **names = xmalloc((size_t)nvars * sizeof(char *));
        for (i = 0; i < nvars; i++) {
            const jv *nm = jvars->items[i];
            if (nm->t != J_STR) die(EXIT_ERR, "vars[%d] 需为字符串", i);
            names[i] = xmalloc(strlen(nm->s) + 1);
            strcpy(names[i], nm->s);
        }

        /* ---- 根盒 ---- */
        if ((slong)jbox->n != nvars)
            die(EXIT_ERR, "box 维数 %lu != vars 数 %ld",
                (unsigned long)jbox->n, (long)nvars);
        leaf rootbox;
        leaf_init(&rootbox, nvars);
        for (i = 0; i < nvars; i++) {
            const jv *dim = jbox->items[i];
            if (dim->t != J_ARR || dim->n != 2)
                die(EXIT_ERR, "box[%d] 需为 [lo,hi]", i);
            jrat(rootbox.ln + i, rootbox.ld + i, dim->items[0], "box 下端点");
            jrat(rootbox.hn + i, rootbox.hd + i, dim->items[1], "box 上端点");
            /* 端点有序：lo<=hi ⟺ ln*hd <= hn*ld */
            {
                fmpz_t t1, t2;
                fmpz_init(t1); fmpz_init(t2);
                fmpz_mul(t1, rootbox.ln + i, rootbox.hd + i);
                fmpz_mul(t2, rootbox.hn + i, rootbox.ld + i);
                if (fmpz_cmp(t1, t2) > 0)
                    die(EXIT_ERR, "box[%d] 下端点 > 上端点", i);
                fmpz_clear(t1); fmpz_clear(t2);
            }
        }

        /* ---- prog + disj 编译 ---- */
        prog *mainp = compile_prog(jprog, nvars, "prog");
        check_prog(mainp, "prog");

        disjq dis = { NULL, 0 };
        if (jdisj) {
            size_t k;
            if (jdisj->t != J_ARR) die(EXIT_ERR, "disj 需为数组");
            dis.v = xmalloc(jdisj->n * sizeof(disjunct));
            dis.n = jdisj->n;
            for (k = 0; k < jdisj->n; k++) {
                const jv *d = jdisj->items[k];
                const jv *jp2, *vlt;
                if (d->t != J_OBJ) die(EXIT_ERR, "disj[%lu] 格式错", (unsigned long)k);
                jp2 = jget(d, "prog");
                vlt = jget(d, "var_lt");
                dis.v[k].is_varlt = 0;
                dis.v[k].p = NULL;
                dis.v[k].vi = dis.v[k].vj = 0;
                if (jp2) {
                    dis.v[k].p = compile_prog(jp2, nvars, "disj prog");
                    check_prog(dis.v[k].p, "disj prog");
                } else if (vlt) {
                    if (vlt->t != J_ARR || vlt->n != 2)
                        die(EXIT_ERR, "disj[%lu] var_lt 需为 [i,j]", (unsigned long)k);
                    dis.v[k].is_varlt = 1;
                    dis.v[k].vi = jidx(vlt->items[0], "var_lt i");
                    dis.v[k].vj = jidx(vlt->items[1], "var_lt j");
                } else {
                    die(EXIT_ERR, "disj[%lu] 缺 prog/var_lt", (unsigned long)k);
                }
            }
        }
        jfree(root);

        /* ---- 求值栈 / 变量区间 ---- */
        size_t scap = mainp->total + 3;
        for (i = 0; i < (int)dis.n; i++)
            if (!dis.v[i].is_varlt && dis.v[i].p->total + 3 > scap)
                scap = dis.v[i].p->total + 3;
        arb_t *stk = xmalloc(scap * sizeof(arb_t));
        for (i = 0; i < (int)scap; i++) arb_init(stk[i]);
        arb_t *vars = xmalloc((size_t)nvars * sizeof(arb_t));
        for (i = 0; i < nvars; i++) arb_init(vars[i]);

        printf("[bb_arb] case: %s  vars=%ld  prec=%ld  max_nodes=%ld\n",
               caseid, (long)nvars, (long)prec, max_nodes);
        printf("[bb_arb] root box: ");
        print_box_human(stdout, &rootbox, names);
        printf("\n");

        /* ---- 精度阶梯表：prec → 128 → 256 ---- */
        slong lad[3];
        int nlad = 0;
        lad[nlad++] = prec;
        if (prec < 128) lad[nlad++] = 128;
        if (prec < 256) lad[nlad++] = 256;

        leafq q = { NULL, 0, 0 };
        cleafq closed = { NULL, 0, 0 };
        long processed = 0, n_lad128 = 0, n_lad256 = 0, n_ufall = 0;
        qpush(&q, &rootbox);

        while (q.n > 0) {
            leaf L;
            int closed_main = 0, cex = 0, li;
            size_t sp = 0;
            evres st = EV_INDET;
            double min_sw = 1e300;   /* 本叶最细跨 0 guard 的球宽 */

            if (processed >= max_nodes) {
                /* 节点超限：输出未闭合叶列表，exit 2 */
                size_t k;
                fprintf(stderr, "[bb_arb] 节点超限（%ld），未闭合叶 %lu 个：\n",
                        max_nodes, (unsigned long)q.n);
                for (k = 0; k < q.n; k++) {
                    fprintf(stderr, "  leaf %lu: ", (unsigned long)k);
                    print_box_human(stderr, &q.v[k], names);
                    fprintf(stderr, "\n");
                }
                exit(EXIT_LIMIT);
            }
            qpop(&q, &L);
            processed++;

            /* 主 prog 求值 + 精度阶梯 */
            for (li = 0; li < nlad; li++) {
                {
                    /* 盒 → 每变量一个包含 [lo,hi] 的 Arb 球 */
                    slong v;
                    for (v = 0; v < nvars; v++)
                        set_var_interval(vars[v], L.ln + v, L.ld + v,
                                         L.hn + v, L.hd + v, lad[li]);
                }
                sp = 0;
                min_sw = 1e300;
                st = eval_prog(mainp, (arb_srcptr)vars, stk, &sp, lad[li], 0, &min_sw);
                if (st == EV_OK) {
                    if (arb_is_positive(stk[0])) {          /* lo > 0 → 叶闭合 */
                        closed_main = 1;
                        break;
                    }
                    if (dis.n == 0 && arb_is_nonpositive(stk[0])) {
                        cex = 1;                            /* hi <= 0 → 反例 */
                        break;
                    }
                }
                /* STRADDLE / INDET / 值跨 0 → 升精度重试 */
                if (li == 0 && nlad > 1) n_lad128++;
                if (li == 1 && nlad > 2) n_lad256++;
            }

            /* 阶梯走完仍未闭合且是 guard 跨 0：单元已够薄（cond 球宽 <
               UNION_EPS）时用 then∪else 并集兜底再试（sound 超集；guard
               边界单元纯符号二分不终止，见 eval_prog 注） */
            if (!closed_main && !cex && st == EV_STRADDLE && min_sw < UNION_EPS) {
                sp = 0;
                if (eval_prog(mainp, (arb_srcptr)vars, stk, &sp, lad[nlad - 1], 1, NULL)
                    == EV_OK) {
                    if (arb_is_positive(stk[0])) {
                        closed_main = 1;
                        n_ufall++;
                    } else if (dis.n == 0 && arb_is_nonpositive(stk[0])) {
                        cex = 1;
                    }
                }
            }

            if (cex) {
                fprintf(stderr, "[bb_arb] COUNTEREXAMPLE：主 prog hi<=0（翻译错？）于叶：");
                print_box_human(stderr, &L, names);
                fprintf(stderr, "\n[bb_arb] nodes=%ld\n", processed);
                exit(EXIT_CEX);
            }
            if (closed_main) {
                closed_add(&closed, &L, "main");
                leaf_free(&L);
                continue;
            }

            /* disj 备选（主 prog 未闭合时）：任一命中即叶闭合 */
            {
                int hit = 0;
                size_t k;
                char hits[48];
                for (k = 0; k < dis.n && !hit; k++) {
                    if (dis.v[k].is_varlt) {
                        /* hi_i < lo_j（精确有理交叉相乘，den>0） */
                        fmpz_t t1, t2;
                        fmpz_init(t1); fmpz_init(t2);
                        fmpz_mul(t1, L.hn + dis.v[k].vi, L.ld + dis.v[k].vj);
                        fmpz_mul(t2, L.ln + dis.v[k].vj, L.hd + dis.v[k].vi);
                        if (fmpz_cmp(t1, t2) < 0) {
                            snprintf(hits, sizeof(hits), "var_lt:%ld,%ld",
                                     (long)dis.v[k].vi, (long)dis.v[k].vj);
                            hit = 1;
                        }
                        fmpz_clear(t1); fmpz_clear(t2);
                    } else {
                        evres dst = eval_prog(dis.v[k].p, (arb_srcptr)vars, stk,
                                              &sp, prec, 0, NULL);
                        if (dst == EV_STRADDLE)   /* guard 跨 0 → 并集兜底 */
                            dst = eval_prog(dis.v[k].p, (arb_srcptr)vars, stk,
                                            &sp, prec, 1, NULL);
                        if (dst == EV_OK && arb_is_positive(stk[0])) {
                            snprintf(hits, sizeof(hits), "disj:%lu", (unsigned long)k);
                            hit = 1;
                        }
                    }
                }
                if (hit) {
                    closed_add(&closed, &L, hits);
                    leaf_free(&L);
                    continue;
                }
            }

            /* 二分：最宽维、精确有理中点 (lo+hi)/2（fmpz 任意精度） */
            {
                slong d = widest_dim(&L);
                leaf a, b;
                fmpz_t mn, md;
                if (d < 0) {
                    fprintf(stderr, "[bb_arb] 盒已退化仍无法闭合（精度不足或断言不真）：");
                    print_box_human(stderr, &L, names);
                    fprintf(stderr, "\n");
                    exit(EXIT_ERR);
                }
                fmpz_init(mn); fmpz_init(md);
                fmpz_mul(mn, L.ln + d, L.hd + d);
                fmpz_addmul(mn, L.hn + d, L.ld + d);     /* mn = ln*hd + hn*ld */
                fmpz_mul(md, L.ld + d, L.hd + d);
                fmpz_mul_2exp(md, md, 1);                /* md = 2*ld*hd */
                /* 约分：不约分则分母逐层平方（2*ld*hd），深度 30+ 即爆位数；
                   端点皆 dyadic，约分后分母 ≤ 2^(q+深度)，保持小整数 */
                {
                    fmpz_t g;
                    fmpz_init(g);
                    fmpz_gcd(g, mn, md);
                    if (!fmpz_is_zero(g) && fmpz_cmp_ui(g, 1) > 0) {
                        fmpz_divexact(mn, mn, g);
                        fmpz_divexact(md, md, g);
                    }
                    fmpz_clear(g);
                }
                leaf_copy(&a, &L);
                leaf_copy(&b, &L);
                fmpz_set(a.hn + d, mn); fmpz_set(a.hd + d, md);
                fmpz_set(b.ln + d, mn); fmpz_set(b.ld + d, md);
                qpush(&q, &a);
                qpush(&q, &b);
                leaf_free(&a); leaf_free(&b);
                fmpz_clear(mn); fmpz_clear(md);
                leaf_free(&L);
            }
        }

        printf("[bb_arb] CLOSED: leaves=%lu  nodes=%ld  (阶梯128=%ld 256=%ld  union=%ld)\n",
               (unsigned long)closed.n, processed, n_lad128, n_lad256, n_ufall);

        /* ---- 证书输出 ---- */
        if (certpath) {
            FILE *f = fopen(certpath, "w");
            size_t k;
            if (!f) die(EXIT_ERR, "无法写 %s", certpath);
            fprintf(f, "{\n  \"id\": ");
            fjson_str(f, caseid);
            fprintf(f, ",\n  \"root_box\": ");
            fjson_box(f, &rootbox);
            fprintf(f, ",\n  \"leaves\": [");
            for (k = 0; k < closed.n; k++) {
                fprintf(f, "%s\n    {\"box\": ", k ? "," : "");
                fjson_box(f, &closed.v[k].L);
                fprintf(f, ", \"hit\": ");
                fjson_str(f, closed.v[k].hit);
                fputc('}', f);
            }
            fprintf(f, "%s],\n  \"nodes\": %ld,\n  \"prec\": %ld\n}\n",
                    closed.n ? "\n  " : "", processed, (long)prec);
            fclose(f);
            printf("[bb_arb] cert: %s\n", certpath);
        }

        /* ---- 清理 ---- */
        for (i = 0; i < (int)scap; i++) arb_clear(stk[i]);
        free(stk);
        for (i = 0; i < nvars; i++) arb_clear(vars[i]);
        free(vars);
        for (i = 0; i < nvars; i++) free(names[i]);
        free(names);
        free(caseid);
        leaf_free(&rootbox);
        prog_free(mainp);
        for (i = 0; i < (int)dis.n; i++) prog_free(dis.v[i].p);
        free(dis.v);
        while (q.n > 0) { leaf t; qpop(&q, &t); leaf_free(&t); }
        free(q.v);
        for (i = 0; i < (int)closed.n; i++) leaf_free(&closed.v[i].L);
        free(closed.v);
        return EXIT_CLOSED;
    }
}
