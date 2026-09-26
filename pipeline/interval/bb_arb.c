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
 * TM 扩展（--tm，设计文档 taylor-model-design.md §2）：每叶判定前先跑一阶
 * 多元 Taylor 模型前向 AD（tm1_t / eval_prog_tm / tm_decide，见下文 TM1 段），
 * loBound = f0.lo − W > 0 即闭合（hit "tm"）；失败/不可用（ite guard 跨 0、
 * abs 跨 0、div/sqrt/log 盒域违例）退既有裸区间路径，该路径零改动。
 * TM 只在盒宽 ≤ 自适应阈值时启用（阈值只影响性能，不影响 soundness）。
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
#include <math.h>
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

/* ---------------- TM1：一阶多元 Taylor 模型前向 AD（设计文档 §2） ----------------
 *
 * 每 RPN 栈位一个 tm1_t：
 *   f0      f(y) 球（中心 y = 盒中点，精确 fmpq 经 arb_set_fmpq 入球）
 *   df[i]   ∂ᵢf(y) 球（中心点 AD，精度 prec_c）
 *   ddf[ij] |∂²ᵢⱼf| 盒上幅值界（mag，粗精度 prec_h，数量级正确即可）
 *   err     ½·Σᵢⱼ wᵢwⱼ·ddfᵢⱼ（mag；全序对和，不用 Schwarz，对齐 T-D0）
 *   W       振幅界 Σᵢ|dfᵢ|wᵢ + err（缓存；|f(ρ)−f(y)| ≤ W）
 * 二阶盒界传播（积/链法则的区间形式；Bf := |f0|+Wf，Dfᵢ := |dfᵢ|+Σⱼ wⱼ·ddfᵢⱼ）：
 *   mul：     Hᵢⱼ ≤ Hfᵢⱼ·Bg + Bf·Hgᵢⱼ + Dfᵢ·Dgⱼ + Dfⱼ·Dgᵢ
 *   div f/g： Hᵢⱼ ≤ Hfᵢⱼ·M + Bf·Hgᵢⱼ·M² + (DfᵢDgⱼ+DfⱼDgᵢ)·M² + 2·Bf·DgᵢDgⱼ·M³
 *             （M = 1/min|g(box)| 上界；g 盒值域越零 → 不可用）
 *   一元 g∘f：Hᵢⱼ ≤ Mg''·Dfᵢ·Dfⱼ + Mg'·Hfᵢⱼ
 *             sqrt: Mg'=1/(2√c), Mg''=1/(4c^{3/2})（c=f 盒值域下界，c≤0 → 不可用）
 *             log:  Mg'=1/c,    Mg''=1/c²         （c≤0 → 不可用）
 *             atan: Mg'=1,      Mg''=min(1, 2·Bf)（|2t/(1+t²)²| ≤ min(2|t|,9/(8√3))）
 *             sin:  Mg'=1, Mg''=min(1,Bf)；cos: Mg'=min(1,Bf), Mg''=1（|sin t|≤|t|）
 * 中心点一阶规则（球算术）：mul 积法则、div 商法则、sqrt df/(2√f0)、
 *   atan df/(1+f0²)、log df/f0、sin df·cos(f0)、cos −df·sin(f0)。
 * ite：guard 在盒球上裸区间可判定 → 盒上 f 恒等于一支，递归 TM 该支（sound，
 *   与 eval_prog 严格模式同语义）；跨 0 → 本叶 TM 不可用（hull 合并不做，§6）。
 * abs：盒值域定号 → identity/neg（Flyspeck m_taylor_abs_pos_compose 的定号
 *   特款）；跨 0 → 不可用（对齐 TMSafe 排除）。
 * 任一不可用条件触发即整叶放弃 TM（valid 标志保留在结构里，对齐 §2.2；
 * 本实现立即返回 1，调用方退裸区间路径——既有路径零改动）。
 * 判定：y 是中点，线性项逐维端点取 ±wᵢ，故
 *   loBound = f0.lo + Σᵢ(dfᵢ·[−wᵢ,wᵢ]).lo − err = f0.lo − W。
 *   loBound > 0 → 叶闭合（hit "tm"），否则退裸区间 + disj + 二分。 */

/* 注意：arb_t/mag_t 是单元素数组类型，数组字段用裸 struct 指针声明，
   函数实参一律写 base + i（与既有代码的 stk[i] 习惯等价，类型更干净）。 */
typedef struct {
    arb_t  f0;
    arb_struct *df;
    mag_struct *ddf;
    mag_t  err;
    mag_t  W;
    int    valid;   /* 0 = 该子式 TM 不可用（保留字段，见段头注） */
    int    from_ite; /* 谱系诊断：0=纯 TM 1=含 ite-hull(常数) 2=含 ite-hull2(df)
                        3=两者混合（div 越零定性用；不影响任何判定） */
    /* --tm-div2 认证幅值下界（旗标门控维护；默认路径零改动）：
       loa ≤ |f(x)| ∀x∈盒 的认证下界（0 = 未知）。注入点：push_var（盒端
       点）、push_const、sqrt（√(参数 TM 值域下界)——sqrt 规则的成功条件
       本身就是「参数模型值域下界 > 0」，该认证在结果 TM 的线性包络变肥后
       依然成立）、abs（定号时较近端点）。其余算术 op 置 0（保守），
       neg 不变。消费点仅 tm_div2_salvage。不参与 (I1)-(I4)。 */
    mag_t  loa;
    /* --tm-div2 认证值域对（arf 外向舍入；区间算术逐 op 组合）：
       cvalid=1 时 [cLo,cHi] ⊇ 子表达式盒上真值域。与 TM 模型值域
       [f0−W, f0+W] 互补：模型值域在 trans 节点后被线性包络+err 撑肥，
       本轨道在 sqrt/log/atan 处按单调性直接换算端点（紧），在算术 op 处
       标准区间组合。消费点仅 tm_div2_salvage（第二通道）。 */
    arf_t  cLo, cHi;
    int    cvalid;
} tm1_t;

/* div 越零失败指令表条目（同一位置计数合并；srcmask 位 i = from_ite==i 出现过。
   path = 根 prog 到失败指令所在子程序的 ite 走廊：每级 (指令下标<<1)|支号
   （0=then 1=else），打印形如 ip=227@7t.3e——与 case JSON 的 ite 嵌套一一对应） */
typedef struct {
    size_t ip;
    long   cnt;
    int    srcmask;
    int    depth;
    size_t path[24];
} tm_ipent;

typedef struct {
    slong  n;
    slong  prec_c;    /* 中心/一阶精度（rung_c） */
    slong  prec_h;    /* Hessian 粗精度（rung_h） */
    mag_struct *w;    /* n 个半径包 wᵢ 上界 */
    arb_struct *yb;   /* n 个中心球 */
    arb_struct *bvars;/* n 个盒球（ite guard 裸区间判定用） */
    arb_struct *bstk; /* guard 裸区间求值栈（复用主 stk） */
    mag_struct *Df, *Dg;   /* 临时：n 个一阶幅值界 */
    arb_struct *ndf;       /* 临时：n 个新一阶球 */
    int    fail_reason;    /* 诊断：1=guard INDET 2=guard 跨0 3=div越零
                              4=abs跨0 5=sqrt/log底非正 6=未知op */
    size_t fail_ip;        /* 诊断：失败指令下标 */
    int    ite_hull;       /* --ite-hull：guard 跨0 时双支求值 + hull 合成
                              （默认 0 = 既有 bail 语义，memset 覆盖） */
    int    ite_hull2;      /* --ite-hull2：df-hull 收紧版（保留导数结构的合成，
                              见 eval_prog_tm OP_ITE 注；默认 0） */
    /* div 越零定性（--ite-hull2 汇总打印；计数只落在失败路径，无判定影响） */
    long   div_fail_n;
    long   div_fail_src[4];  /* 分母 TM 来源类别直方图（from_ite 0..3） */
    long   div_fail_wb[8];   /* 分母盒值域宽 log2 桶：≤-20 / (-20,-10] /
                                 (-10,-6] / (-6,-2] / (-2,2] / (2,6] / (6,20] / >20 */
    tm_ipent div_ips[64];    /* 失败指令（子式）表，溢出置 div_ips_ovf */
    int    div_ips_n, div_ips_ovf;
    /* --tm-div2：den 倒数界裸区间认证通道（旗标门控计数，默认全零零输出）。
       div2_n = div越零事件数（旗标开启时）；div2_saved = 裸区间轨道给出
       |den| > 0 认证下界、div 规则经 M=1/loa 继续的事件数；
       div2_unsaved = 轨道失效或仍跨 0（真跨 0 或裸区间也肥）事件数；
       div2_lb[] = saved 事件 loa=log₂|den|下界 桶（口径同 div_fail_wb）。 */
    long   div2_n, div2_saved, div2_unsaved;
    long   div2_src1, div2_src2;   /* 通道占比：1=trans 注入 loa 2=值域对定号 */
    long   div2_lb[8];
    size_t ite_path[24];     /* 当前 ite 递归走廊（诊断用，见 tm_ipent 注） */
    int    ite_depth;
    /* --hull-stats：OP_ITE 闭合模式计数（仅旗标开启时累加与打印；
       默认全零且热路径只有旗标判断，既有路径行为与输出零改动）。
       口径：
         事件级 = eval_prog_tm 内每次 OP_ITE 判定；
         盒尝试级 = 主循环/探针对一个盒的一次 eval_prog_tm 调用的归类；
         dmax = 该盒尝试中 straddle 事件的最大嵌套深度（该 ite 之上的
         straddle ite 层数）——Lean 侧 hull 宽度 ×2 翻倍次数的直接对应。 */
    int    hull_stats;       /* --hull-stats 旗标镜像 */
    long   hs_single;        /* 事件：guard 裸区间定号 → 单支求值（不付 hull 宽） */
    long   hs_straddle;      /* 事件：guard 跨0 → 双支求值 + hull 合成 */
    long   hs_strat_d[16];   /* straddle 事件嵌套深度直方图（≥15 入溢出桶） */
    long   hs_strat_ovf;
    long   hs_lf_single;     /* 盒尝试：整棵 TM 无 straddle（全定号单支） */
    long   hs_lf_hull;       /* 盒尝试：≥1 次 straddle-hull */
    long   hs_lf_dmax[16];   /* 盒尝试 dmax 直方图（≥15 入溢出桶） */
    long   hs_cl_single;     /* TM 闭合叶分类（hit=="tm"） */
    long   hs_cl_hull;
    long   hs_cl_dmax[16];   /* 闭合叶 dmax 直方图（证书叶的 ×2^k 宽度代价谱） */
    long   hs_fail_r[8];     /* TM 失败按 reason 直方图（1..6；主循环/探针累加） */
    int    hs_sd;            /* 运行期：当前 straddle 递归层数 */
    long   hs_a_strat;       /* 运行期草稿：本盒尝试 straddle 事件数（每盒复位） */
    int    hs_a_dmax;        /* 运行期草稿：本盒尝试最大 straddle 嵌套深度 */
    /* --gsplit2：straddle 追踪（旗标门控记录，主循环每叶复位）。
       gs_hit = 本盒 TM 求值触发过 hull（某 ite guard 盒上跨 0 走了双支）；
       gs_guard = 首个触发 hull 的 ite guard prog（外层先到先记；借用
       mainp 子树指针，生命周期覆盖全程）。 */
    int    gsplit2;
    int    gs_hit;
    const prog *gs_guard;
    /* --tm-tight：err 走 Schwarz 型收紧（min 保护）+ atan Mg'' 盒上 sup；
       均为 sound 收紧（err 只减不增），见 tm_err_from_ddf 注；默认 0。 */
    int    tm_tight;
    /* --tm-tight2：mul/div 对角完备化实验（实测负结果，留档对照）；默认 0。 */
    int    tm_tight2;
    /* --tm-ddf：诊断 dump（OP_ITE hull 合成事件 + --tm-debug 根盒 ddf 矩阵
       与 err 分解）；仅打印，不影响任何判定；默认 0。 */
    int    tm_ddf;
    /* --tm-div2：div 越零的裸区间认证通道（旗标门控；默认 0 = 既有
       TM_FAIL(3) 语义逐字节不变，见 tm_div2_salvage 注）。 */
    int    tm_div2;
} tmctx;

static void tm1_init(tm1_t *t, slong n)
{
    slong i;
    arb_init(t->f0);
    t->df = xmalloc((size_t)n * sizeof(arb_t));
    t->ddf = xmalloc((size_t)(n * n) * sizeof(mag_t));
    for (i = 0; i < n; i++) arb_init(t->df + i);
    for (i = 0; i < n * n; i++) mag_init(t->ddf + i);
    mag_init(t->err);
    mag_init(t->W);
    t->valid = 1;
    t->from_ite = 0;
    mag_init(t->loa);
    arf_init(t->cLo);
    arf_init(t->cHi);
    t->cvalid = 0;
}

static void tm1_clear(tm1_t *t, slong n)
{
    slong i;
    arb_clear(t->f0);
    for (i = 0; i < n; i++) arb_clear(t->df + i);
    for (i = 0; i < n * n; i++) mag_clear(t->ddf + i);
    mag_clear(t->err);
    mag_clear(t->W);
    mag_clear(t->loa);
    arf_clear(t->cLo);
    arf_clear(t->cHi);
    free(t->df);
    free(t->ddf);
}

/* err = ½·Σᵢⱼ wᵢwⱼ·ddfᵢⱼ（全序对和）。
 *
 * --tm-tight（Schwarz 型收紧；旗标门控，默认路径零改动）：
 *   err_tight = min( err_full, ½·(Σᵢ wᵢ·√ddfᵢᵢ)² )
 * 后一支仅在最终 ddf 矩阵逐格通过几何均值检验时启用。
 *
 * 不等式链（ddfᵢⱼ = 传播所得 |∂²ᵢⱼf| 盒上上界，wᵢ = 盒半宽，δᵢ = xᵢ−yᵢ）：
 *  (0) Taylor 余项（只消费传播不变量 (I4)）：
 *      |R₂(x)| = ½|δᵀH(ξ)δ| ≤ ½Σᵢⱼ|δᵢ||δⱼ|ddfᵢⱼ ≤ ½Σᵢⱼ wᵢwⱼ·ddfᵢⱼ = err_full。
 *  (1) Schwarz/几何均值形：若矩阵逐格满足 ddfᵢⱼ ≤ √(ddfᵢᵢ·ddfⱼⱼ)（对角恒真），
 *      则 err_full ≤ ½Σᵢⱼwᵢwⱼ·√ddfᵢᵢ√ddfⱼⱼ = ½(Σᵢ wᵢ√ddfᵢᵢ)²
 *      （(Σᵢaᵢ)² = Σᵢⱼaᵢaⱼ 展开，aᵢ := wᵢ√ddfᵢᵢ ≥ 0）。∎
 *      soundness 只依赖「最终矩阵」的逐格性质（下方运行时检验认证），
 *      传播公式不动。结构来源（为何该性质常见）：unary 链 H = Mg''·DfDfᵀ +
 *      Mg'·Hf 是秩一项（几何均值精确）+ IH 缩放项（继承）；两几何均值阵
 *      之和仍满足（逐对 Cauchy–Schwarz + (√AᵢAⱼ+√CᵢCⱼ)² ≤ (Aᵢ+Cᵢ)(Aⱼ+Cⱼ)）；
 *      配 --tm-tight 的 mul/div 对角完备化（2·Df·Dg → Df²+Dg²，见各算术分支
 *      注）后该结构对所有 op 归纳成立。
 *  (2) min 保护：两支都是 |R₂| 的有效上界，min 仍有效 ⟹ --tm-tight 的
 *      err ≤ 既有 err 逐格成立，已闭合叶不可能回退。
 * 检验实现：只作「选哪支公式」的判定器，绝不允许假通过——格值双精度化后
 * LHS 逐 op 上取整、RHS 逐 op 下取整（nextafter 余量），溢出/NaN → 判失败
 * → 退 err_full，永远 sound。 */
static void tm_err_from_ddf(tm1_t *t, const tmctx *cx)
{
    slong i, j, n = cx->n;
    mag_t acc, term;
    mag_init(acc);
    mag_init(term);
    mag_zero(acc);
    for (i = 0; i < n; i++)
        for (j = 0; j < n; j++) {
            mag_mul(term, t->ddf + i * n + j, cx->w + j);
            mag_mul(term, term, cx->w + i);
            mag_add(acc, acc, term);
        }
    mag_mul_2exp_si(acc, acc, -1);
    if (cx->tm_tight) {
        mag_t ss;
        double dg[16];
        int gmok = (n >= 1 && n <= 16);
        mag_init(ss);
        mag_zero(ss);
        for (i = 0; i < n && gmok; i++) {
            double di = mag_get_d(t->ddf + i * n + i);
            if (!(di >= 0.0) || (di > 0.0 && di * 2.0 == di)) {
                gmok = 0;   /* NaN/inf → 退 err_full（0 合法：dg[i]=0） */
                break;
            }
            dg[i] = di > 0.0 ? nextafter(di, 0.0) : 0.0;
            mag_sqrt(term, t->ddf + i * n + i);
            mag_mul(term, term, cx->w + i);
            mag_add(ss, ss, term);
        }
        if (gmok)
            for (i = 0; i < n && gmok; i++)
                for (j = 0; j < n; j++) {
                    double du = mag_get_d(t->ddf + i * n + j);
                    if (du == 0.0) continue;   /* 0 ≤ √(ddfᵢᵢ·ddfⱼⱼ) 恒真 */
                    {
                        double li = nextafter(du, HUGE_VAL);
                        double lhs = nextafter(li * li, HUGE_VAL);
                        double rhs = nextafter(nextafter(dg[i] * dg[j], 0.0),
                                               0.0);
                        if (!(lhs <= rhs)) { gmok = 0; break; }
                    }
                }
        if (gmok) {
            mag_mul(ss, ss, ss);
            mag_mul_2exp_si(ss, ss, -1);
            if (mag_cmp(ss, acc) < 0) mag_set(acc, ss);   /* min 保护 */
        }
        mag_clear(ss);
    }
    mag_set(t->err, acc);
    mag_clear(acc);
    mag_clear(term);
}

/* W = Σᵢ |dfᵢ|·wᵢ + err */
static void tm_update_W(tm1_t *t, const tmctx *cx)
{
    slong i;
    mag_t acc, term;
    mag_init(acc);
    mag_init(term);
    mag_set(acc, t->err);
    for (i = 0; i < cx->n; i++) {
        arb_get_mag(term, t->df + i);
        mag_mul(term, term, cx->w + i);
        mag_add(acc, acc, term);
    }
    mag_set(t->W, acc);
    mag_clear(acc);
    mag_clear(term);
}

/* |f| 盒上幅值界 ≤ |f0| + W */
static void tm_Bmag(mag_t out, const tm1_t *t)
{
    arb_get_mag(out, t->f0);
    mag_add(out, out, t->W);
}

/* |∂ᵢf| 盒上幅值界 ≤ |dfᵢ(y)| + Σⱼ wⱼ·ddfᵢⱼ（坐标线段 MVT） */
static void tm_Dmag(mag_t out, const tm1_t *t, const tmctx *cx, slong i)
{
    slong j;
    mag_t term;
    mag_init(term);
    arb_get_mag(out, t->df + i);
    for (j = 0; j < cx->n; j++) {
        mag_mul(term, t->ddf + i * cx->n + j, cx->w + j);
        mag_add(out, out, term);
    }
    mag_clear(term);
}

/* f 盒值域 ⊂ [lo,hi]（arf 外向界：f0 球端点 ∓ W） */
static void tm_range_arf(arf_t lo, arf_t hi, const tm1_t *t, const tmctx *cx)
{
    arf_t wm;
    arf_init(wm);
    arf_set_mag(wm, t->W);          /* mag 的名义值是其上界，arf 精确可表 */
    arb_get_lbound_arf(lo, t->f0, cx->prec_h);
    arb_get_ubound_arf(hi, t->f0, cx->prec_h);
    arf_sub(lo, lo, wm, cx->prec_h, ARF_RND_FLOOR);
    arf_add(hi, hi, wm, cx->prec_h, ARF_RND_CEIL);
    arf_clear(wm);
}

/* sqrt/log 的 Mg'、Mg'' 上界：c = f 盒值域下界（arf，调用方保证 >0）。
   粗球算术外扩取 mag；c 取下界 → 倒数值更大，方向 sound。
   kind 0 = sqrt（1/(2√c), 1/(4c^{3/2})）；kind 1 = log（1/c, 1/c²）。 */
static void tm_uni_M(mag_t Mg1, mag_t Mg2, const arf_t c, int kind, slong prec)
{
    arb_t t, s, u;
    arb_init(t);
    arb_init(s);
    arb_init(u);
    arb_set_arf(t, c);                /* 退化球 = c 的下界 */
    if (kind == 0) {
        arb_sqrt(s, t, prec);         /* ⊇ √c */
        arb_mul_2exp_si(u, s, 1);     /* 2√c */
        arb_inv(u, u, prec);          /* ⊇ 1/(2√c) */
        arb_get_mag(Mg1, u);
        arb_mul(s, s, t, prec);       /* c^{3/2} */
        arb_mul_2exp_si(s, s, 2);     /* 4c^{3/2} */
        arb_inv(s, s, prec);
        arb_get_mag(Mg2, s);
    } else {
        arb_inv(u, t, prec);          /* 1/c */
        arb_get_mag(Mg1, u);
        arb_mul(s, t, t, prec);
        arb_inv(s, s, prec);
        arb_get_mag(Mg2, s);
    }
    arb_clear(t);
    arb_clear(s);
    arb_clear(u);
}

/* --tm-tight：sup_{t∈[lo,hi]} |atan''(t)|，atan''(t) = −2t/(1+t²)²。
   |atan''| 偶，在 |t|=1/√3 处取全局峰 9/(8√3)，沿 |t| 在 [0,1/√3] 增、
   [1/√3,∞) 减。折到 |t| 轴取 a=min(|lo|,|hi|)、b=max(|lo|,|hi|)：
     b ≤ 1/√3（含球界）→ 增段，sup = g(b)；a ≥ 1/√3（含球界）→ 减段，
     sup = g(a)；其余（区间触及临界球）→ 全局峰（sound：sup ≤ 全局 sup）。
   候选点/峰值全部经球算术外向求值（prec_h）⟹ sound 上界；既行
   min(2·Bf,1) 的直接收紧（旧界 = 该 sup 的粗化：全局帽 1 而非 9/(8√3)）。 */
static void tm_atan_M2sup(mag_t out, const arf_t lo, const arf_t hi, slong prec)
{
    arb_t x, n, d, t3;
    arf_t a, b;
    mag_t pk, va;
    int use_left;
    arb_init(x);
    arb_init(n);
    arb_init(d);
    arb_init(t3);
    arf_init(a);
    arf_init(b);
    mag_init(pk);
    mag_init(va);
    /* 峰值 9/(8√3)：s=√3（球），pk = 9/(8s) 的上界 mag */
    arb_set_ui(t3, 3);
    arb_sqrt(t3, t3, prec);
    arb_mul_ui(n, t3, 8, prec);
    arb_set_ui(d, 9);
    arb_div(t3, d, n, prec);           /* 9/(8√3) */
    arb_get_mag(pk, t3);
    /* a = min(|lo|,|hi|), b = max(|lo|,|hi|)（arf 精确） */
    arf_abs(a, lo);
    arf_abs(b, hi);
    if (arf_cmp(a, b) > 0) arf_swap(a, b);
    /* 临界点球 ⊇ 1/√3 = √3/3 */
    arb_set_ui(d, 3);
    arb_div(t3, t3, d, prec);
    {
        arf_t l3, h3;
        arf_init(l3);
        arf_init(h3);
        arb_get_lbound_arf(l3, t3, prec);
        arb_get_ubound_arf(h3, t3, prec);
        if (arf_cmp(b, l3) <= 0) {
            use_left = 0;              /* b 在临界球左 → 增段，sup=g(b) */
            arf_set(a, b);
        } else if (arf_cmp(a, h3) >= 0) {
            use_left = 1;              /* a 在临界球右 → 减段，sup=g(a) */
        } else {
            use_left = -1;             /* 触及临界球 → 全局峰 */
        }
        /* x = 选定候选点（use_left=0 时 a 已置为 b），v = 2|x|/(1+x²)² */
        if (use_left >= 0) {
            arb_set_arf(x, a);
            arb_abs(x, x);
            arb_mul_2exp_si(n, x, 1);          /* 2|x| */
            arb_mul(d, x, x, prec);
            arb_add_ui(d, d, 1, prec);
            arb_mul(d, d, d, prec);
            arb_div(x, n, d, prec);
            arb_get_mag(va, x);
        } else {
            mag_set(va, pk);
        }
        arf_clear(l3);
        arf_clear(h3);
    }
    mag_min(out, va, pk);              /* 墙内永远 ≤ 全局峰（保守并取） */
    arf_clear(a);
    arf_clear(b);
    mag_clear(pk);
    mag_clear(va);
    arb_clear(x);
    arb_clear(n);
    arb_clear(d);
    arb_clear(t3);
}

/* M = 1/min|g(box)| 的上界 mag；g 盒值域越零 → 返回 0（不可用） */
static int tm_inv_range_mag(mag_t M, const tm1_t *g, const tmctx *cx)
{
    arf_t lo, hi;
    arb_t t;
    int ok = 1;
    arf_init(lo);
    arf_init(hi);
    arb_init(t);
    tm_range_arf(lo, hi, g, cx);
    if (arf_sgn(lo) > 0) {
        arb_set_arf(t, lo);           /* |g| ≥ lo > 0 → 1/|g| ≤ 1/lo */
    } else if (arf_sgn(hi) < 0) {
        arf_neg(hi, hi);
        arb_set_arf(t, hi);           /* |g| ≥ |hi| > 0 */
    } else {
        ok = 0;
    }
    if (ok) {
        arb_inv(t, t, cx->prec_h);
        arb_get_mag(M, t);
    }
    arf_clear(lo);
    arf_clear(hi);
    arb_clear(t);
    return ok;
}

/* --tm-div2 认证值域对的区间组合（arf 外向舍入；端点 arf 已是各自
   子表达式真值域的外向界 ⟹ 组合结果仍是外向界）。 */

static void tm_pair_add(arf_t lo, arf_t hi, const arf_t a, const arf_t b,
                        const arf_t c, const arf_t d, slong prec)
{
    arf_add(lo, a, c, prec, ARF_RND_FLOOR);
    arf_add(hi, b, d, prec, ARF_RND_CEIL);
}

static void tm_pair_sub(arf_t lo, arf_t hi, const arf_t a, const arf_t b,
                        const arf_t c, const arf_t d, slong prec)
{
    arf_sub(lo, a, d, prec, ARF_RND_FLOOR);
    arf_sub(hi, b, c, prec, ARF_RND_CEIL);
}

/* 标准区间乘/除：四端点组合，min 取 FLOOR、max 取 CEIL（除法要求
   分母区间不含 0，调用方保证）。 */
static void tm_pair_muldiv(arf_t lo, arf_t hi,
                           const arf_t a, const arf_t b,
                           const arf_t c, const arf_t d,
                           slong prec, int isdiv)
{
    arf_t p[2][4];
    arf_t mn, mx;
    const arf_struct *num[2], *den[2];
    int i, j;
    num[0] = a; num[1] = b;
    den[0] = c; den[1] = d;
    for (i = 0; i < 2; i++)
        for (j = 0; j < 4; j++)
            arf_init(p[i][j]);
    arf_init(mn);
    arf_init(mx);
    for (j = 0; j < 4; j++) {
        const arf_struct *x = num[j & 1];
        const arf_struct *y = den[j >> 1];
        if (isdiv) {
            arf_div(p[0][j], x, y, prec, ARF_RND_FLOOR);
            arf_div(p[1][j], x, y, prec, ARF_RND_CEIL);
        } else {
            arf_mul(p[0][j], x, y, prec, ARF_RND_FLOOR);
            arf_mul(p[1][j], x, y, prec, ARF_RND_CEIL);
        }
    }
    arf_set(mn, p[0][0]);
    arf_set(mx, p[1][0]);
    for (j = 1; j < 4; j++) {
        if (arf_cmp(mn, p[0][j]) > 0) arf_set(mn, p[0][j]);
        if (arf_cmp(mx, p[1][j]) < 0) arf_set(mx, p[1][j]);
    }
    arf_set(lo, mn);
    arf_set(hi, mx);
    for (i = 0; i < 2; i++)
        for (j = 0; j < 4; j++)
            arf_clear(p[i][j]);
    arf_clear(mn);
    arf_clear(mx);
}

/* 单调 trans 换算（kind：0=sqrt 需 a>0，1=log 需 a>0，2=atan 全域单调；
   经 arb 中转做端点外向舍入）。返回 0 = 前置条件不满足。 */
static int tm_pair_trans(arf_t lo, arf_t hi, const arf_t a, const arf_t b,
                         slong prec, int kind)
{
    arb_t t;
    arf_t r;
    int ok = 1;
    if (kind <= 1 && arf_sgn(a) <= 0) return 0;
    arb_init(t);
    arf_init(r);
    arb_set_arf(t, a);
    if (kind == 0) arb_sqrt(t, t, prec);
    else if (kind == 1) arb_log(t, t, prec);
    else arb_atan(t, t, prec);
    arb_get_lbound_arf(r, t, prec);
    arf_set(lo, r);
    arb_set_arf(t, b);
    if (kind == 0) arb_sqrt(t, t, prec);
    else if (kind == 1) arb_log(t, t, prec);
    else arb_atan(t, t, prec);
    arb_get_ubound_arf(r, t, prec);
    arf_set(hi, r);
    arf_clear(r);
    arb_clear(t);
    return ok;
}

/* --tm-div2：div 越零的认证通道（旗标门控；默认路径零改动）。
 *
 * 背景：tm_inv_range_mag 用 TM 模型值域 [f0−W, f0+W] 判 |g| 下界；线性项
 * 沿链传播肥厚时该包络跨 0（549 的 6,565 处 div越零 全部如此，分母宽桶
 * (2,6] 占 87%——「宽盒大振幅」），但真分母在盒上可能定号——模型包络跨 0
 * 只说明*线性包络*够不着 1/g 的界，不说明 g 真的变号。
 *
 * 机制：TM 槽携带认证幅值下界 loa ≤ |g(x)|（tm1_t 注：sqrt/abs 规则在
 * 通过自身成功条件时注入——该条件本身就是对真值域的认证，不随下游线性
 * 包络变肥失效）。取
 *   M := 1/loa   （arb_inv 外向 + arb_get_mag 上取）
 * 则 M ≥ 1/|g(x)| 处处成立，方向 sound；下游 M²/M³ Hessian 传播与中心
 * 商法则与常规路径逐式相同（只换 M 来源），(I1)-(I4) 论证不变。
 * loa = 0（无认证）→ 放弃，维持 TM_FAIL(3) 既有语义。
 *
 * 返回 1 = M 已置、div 规则继续；0 = 不可救（调用方走原失败路径）。 */
static int tm_div2_salvage(mag_t M, const tm1_t *g, tmctx *cx)
{
    arb_t t;
    arf_t la;
    int ok = 0;
    cx->div2_n++;
    arf_init(la);
    arb_init(t);
    /* 通道 1：trans 注入的 |·| 下界（sqrt/abs/push；最紧的单跳认证） */
    if (!mag_is_zero(g->loa)) {
        arf_set_mag(la, g->loa);      /* mag 名义值 = loa 的精确表示 */
        ok = 1;
        cx->div2_src1++;
    }
    /* 通道 2：认证值域对定号（区间组合轨道；sqrt·quad+r 型和链可过） */
    if (!ok && g->cvalid) {
        if (arf_sgn(g->cLo) > 0) {
            arf_set(la, g->cLo);
            ok = 1;
            cx->div2_src2++;
        } else if (arf_sgn(g->cHi) < 0) {
            arf_neg(la, g->cHi);
            ok = 1;
            cx->div2_src2++;
        }
    }
    if (ok) {
        arb_set_arf(t, la);           /* t = loa ≤ |g| */
        arb_inv(t, t, cx->prec_h);
        arb_get_mag(M, t);
        cx->div2_saved++;
        /* loa 桶（log₂|den| 下界）——肥 M 预警（valid 但难闭合） */
        {
            double dv = arf_get_d(la, ARF_RND_DOWN);
            int e = 0, b = 0;
            if (dv > 0) {
                frexp(dv, &e);
                e -= 1;
            }
            if (e <= -20) b = 0;
            else if (e <= -10) b = 1;
            else if (e <= -6) b = 2;
            else if (e <= -2) b = 3;
            else if (e <= 2) b = 4;
            else if (e <= 6) b = 5;
            else if (e <= 20) b = 6;
            else b = 7;
            cx->div2_lb[b]++;
        }
    } else {
        cx->div2_unsaved++;
    }
    arf_clear(la);
    arb_clear(t);
    return ok;
}

/* 谱系合并：0=纯 1=ite-hull 2=ite-hull2 3=混合（非零不同值 → 3） */
static int tm_src_join(int a, int b)
{
    if (a == b) return a;
    if (!a) return b;
    if (!b) return a;
    return 3;
}

/* div 越零定性（诊断计数，仅 --ite-hull2 汇总打印；不改变任何判定）：
   记录分母 TM 的谱系类别、盒值域宽 log2 桶、失败指令（子式）ip 表。
   给 closed-trans/chop 对接的接口语义：
     ip → RPN 指令下标（prog->is[ip]，即分母子表达式的求值入口）；
     srcmask → 分母是否经由 ite-hull 合成（合成宽度是 chop 需压掉的部分）；
     宽桶 → 分母值域盒宽的量级（域切分到宽 < 2^e 时该处转定号）。 */
static void tm_div_fail_diag(tmctx *cx, const tm1_t *g, size_t ip)
{
    arf_t lo, hi;
    int src;
    cx->div_fail_n++;
    src = g->from_ite;
    if (src < 0 || src > 3) src = 0;
    cx->div_fail_src[src]++;
    arf_init(lo);
    arf_init(hi);
    tm_range_arf(lo, hi, g, cx);
    if (arf_cmp(lo, hi) < 0) {
        arf_t wd;
        arf_init(wd);
        arf_sub(wd, hi, lo, 53, ARF_RND_CEIL);
        {
            double dv = arf_get_d(wd, ARF_RND_UP);
            int e = 0, b = 7;
            if (dv > 0) {
                frexp(dv, &e);
                e -= 1;   /* frexp: dv = m·2^e, m∈[0.5,1) → floor(log2) = e−1 */
            }
            if (e <= -20) b = 0;
            else if (e <= -10) b = 1;
            else if (e <= -6) b = 2;
            else if (e <= -2) b = 3;
            else if (e <= 2) b = 4;
            else if (e <= 6) b = 5;
            else if (e <= 20) b = 6;
            cx->div_fail_wb[b]++;
        }
        arf_clear(wd);
    } else {
        cx->div_fail_wb[0]++;   /* 宽 ≤ 0（退化球）归最细桶 */
    }
    arf_clear(lo);
    arf_clear(hi);
    {
        int k, d;
        d = cx->ite_depth > 24 ? 24 : cx->ite_depth;
        for (k = 0; k < cx->div_ips_n; k++)
            if (cx->div_ips[k].ip == ip && cx->div_ips[k].depth == d &&
                memcmp(cx->div_ips[k].path, cx->ite_path,
                       (size_t)d * sizeof(size_t)) == 0) {
                cx->div_ips[k].cnt++;
                cx->div_ips[k].srcmask |= 1 << src;
                return;
            }
        if (cx->div_ips_n < 64) {
            tm_ipent *e = cx->div_ips + cx->div_ips_n;
            e->ip = ip;
            e->cnt = 1;
            e->srcmask = 1 << src;
            e->depth = d;
            memcpy(e->path, cx->ite_path, (size_t)d * sizeof(size_t));
            cx->div_ips_n++;
        } else {
            cx->div_ips_ovf = 1;
        }
    }
}

/* --tm-ddf：单 TM 余项解剖行（旗标门控，只打印不判定）：
   f0 盒值域 / err / W / slopeW=Σᵢ|dfᵢ|wᵢ（W−err = 线性项占比）。 */
static void tm_ddf_row(const char *tag, const tm1_t *t, const tmctx *cx)
{
    arf_t lo, hi;
    mag_t sw;
    slong i;
    arf_init(lo);
    arf_init(hi);
    mag_init(sw);
    tm_range_arf(lo, hi, t, cx);
    for (i = 0; i < cx->n; i++) {
        mag_t m;
        mag_init(m);
        arb_get_mag(m, t->df + i);
        mag_mul(m, m, cx->w + i);
        mag_add(sw, sw, m);
        mag_clear(m);
    }
    printf("[tm-ddf] %s f0=[%.6g,%.6g] err=%.6e W=%.6e slopeW=%.6e\n", tag,
           arf_get_d(lo, ARF_RND_DOWN), arf_get_d(hi, ARF_RND_UP),
           mag_get_d(t->err), mag_get_d(t->W), mag_get_d(sw));
    arf_clear(lo);
    arf_clear(hi);
    mag_clear(sw);
}

/* div 越零定性汇总打印（仅 tm_on && ite_hull2 调用） */
static void tm_div_diag_print(FILE *f, const tmctx *cx)
{
    int k;
    fprintf(f, "[bb_arb] div越零定性: n=%ld  分母谱系: plain=%ld  ite-hull=%ld"
               "  ite-hull2=%ld  混合=%ld\n",
            cx->div_fail_n, cx->div_fail_src[0], cx->div_fail_src[1],
            cx->div_fail_src[2], cx->div_fail_src[3]);
    fprintf(f, "[bb_arb] div 分母盒宽 log2 桶: <=-20:%ld  (-20,-10]:%ld"
               "  (-10,-6]:%ld  (-6,-2]:%ld  (-2,2]:%ld  (2,6]:%ld"
               "  (6,20]:%ld  >20:%ld\n",
            cx->div_fail_wb[0], cx->div_fail_wb[1], cx->div_fail_wb[2],
            cx->div_fail_wb[3], cx->div_fail_wb[4], cx->div_fail_wb[5],
            cx->div_fail_wb[6], cx->div_fail_wb[7]);
    if (cx->div_ips_n > 0) {
        fprintf(f, "[bb_arb] div 失败 ip 表 (ip@ite走廊(次数,谱系位集)):");
        for (k = 0; k < cx->div_ips_n; k++) {
            int d;
            fprintf(f, " %lu@", (unsigned long)cx->div_ips[k].ip);
            for (d = 0; d < cx->div_ips[k].depth; d++)
                fprintf(f, "%s%lu%c", d ? "." : "",
                        (unsigned long)(cx->div_ips[k].path[d] >> 1),
                        (cx->div_ips[k].path[d] & 1) ? 'e' : 't');
            fprintf(f, "(x%ld,s%d)", cx->div_ips[k].cnt, cx->div_ips[k].srcmask);
        }
        if (cx->div_ips_ovf) fprintf(f, " ...(表满截断)");
        fprintf(f, "\n");
    }
    if (cx->tm_div2) {
        fprintf(f, "[bb_arb] div2 裸区间认证: n=%ld  saved=%ld  unsaved=%ld"
                   "  (saved 占比 %.2f%%；通道1 trans-loa=%ld 通道2 值域对=%ld)\n",
                cx->div2_n, cx->div2_saved, cx->div2_unsaved,
                cx->div2_n ? 100.0 * (double)cx->div2_saved / (double)cx->div2_n
                           : 0.0,
                cx->div2_src1, cx->div2_src2);
        fprintf(f, "[bb_arb] div2 loa=log₂|den|下界 桶: <=-20:%ld  (-20,-10]:%ld"
                   "  (-10,-6]:%ld  (-6,-2]:%ld  (-2,2]:%ld  (2,6]:%ld"
                   "  (6,20]:%ld  >20:%ld\n",
                cx->div2_lb[0], cx->div2_lb[1], cx->div2_lb[2],
                cx->div2_lb[3], cx->div2_lb[4], cx->div2_lb[5],
                cx->div2_lb[6], cx->div2_lb[7]);
    }
}

/* --hull-stats 摘要打印（仅旗标开启时调用） */
static void tm_hull_stats_print(FILE *f, const tmctx *cx)
{
    int k;
    long fail_n = 0;
    for (k = 1; k <= 6; k++) fail_n += cx->hs_fail_r[k];
    fprintf(f, "[bb_arb] hull-stats: ite事件 single=%ld  straddle_hull=%ld\n",
            cx->hs_single, cx->hs_straddle);
    fprintf(f, "[bb_arb] hull-stats: straddle 嵌套深度直方图"
               "(上方straddle ite层数:事件数):");
    for (k = 0; k < 16; k++)
        if (cx->hs_strat_d[k]) fprintf(f, " %d:%ld", k, cx->hs_strat_d[k]);
    if (cx->hs_strat_ovf) fprintf(f, " >=16:%ld", cx->hs_strat_ovf);
    fprintf(f, "\n");
    {
        double att = (double)cx->hs_lf_single + (double)cx->hs_lf_hull +
                     (double)fail_n;
        fprintf(f, "[bb_arb] hull-stats: 盒尝试 single=%ld(%.3f%%)"
                   "  straddle_hull=%ld(%.3f%%)  tm_fail=%ld(%.3f%%)"
                   "  attempts=%.0f\n",
                cx->hs_lf_single, att ? 100.0 * (double)cx->hs_lf_single / att : 0.0,
                cx->hs_lf_hull, att ? 100.0 * (double)cx->hs_lf_hull / att : 0.0,
                fail_n, att ? 100.0 * (double)fail_n / att : 0.0, att);
    }
    fprintf(f, "[bb_arb] hull-stats: 尝试最大嵌套深度直方图(层:盒数):");
    for (k = 0; k < 16; k++)
        if (cx->hs_lf_dmax[k]) fprintf(f, " %d:%ld", k, cx->hs_lf_dmax[k]);
    if (cx->hs_lf_hull) fprintf(f, " (仅 straddle_hull 盒计入)");
    fprintf(f, "\n");
    fprintf(f, "[bb_arb] hull-stats: TM闭合叶 single=%ld  straddle_hull=%ld"
               "  (共%ld)\n",
            cx->hs_cl_single, cx->hs_cl_hull,
            cx->hs_cl_single + cx->hs_cl_hull);
    fprintf(f, "[bb_arb] hull-stats: 闭合叶最大嵌套深度直方图(层:叶数):");
    for (k = 0; k < 16; k++)
        if (cx->hs_cl_dmax[k]) fprintf(f, " %d:%ld", k, cx->hs_cl_dmax[k]);
    fprintf(f, "\n");
    fprintf(f, "[bb_arb] hull-stats: tm_fail 原因: guard-INDET=%ld  guard跨0=%ld"
               "  div越零=%ld  abs跨0=%ld  sqrt/log底非正=%ld  未知=%ld\n",
            cx->hs_fail_r[1], cx->hs_fail_r[2], cx->hs_fail_r[3],
            cx->hs_fail_r[4], cx->hs_fail_r[5], cx->hs_fail_r[6]);
}

/* 单遍 RPN 前向 AD：0 = 栈顶 TM 有效；1 = 本叶 TM 不可用（立即放弃）。
   栈纪律与 eval_prog 一致（check_prog 已静态保证）。
   注：本函数在 GCC -O2 下触发 -Wstringop-overflow/overread 误报（对 FLINT
   数组 typedef 参数 arb_t = arb_struct[1] 的对象尺寸分析幻觉；-O1/-O3 均无，
   对象均为完整 tm1_t 槽位）。局部屏蔽，其余文件区域保持默认告警。 */
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wstringop-overflow"
#pragma GCC diagnostic ignored "-Wstringop-overread"
#define TM_FAIL(code) do { if (!cx->fail_reason) { \
        cx->fail_reason = (code); cx->fail_ip = i; } return 1; } while (0)
static int eval_prog_tm(const prog *p, tm1_t *stk, size_t *sp, tmctx *cx)
{
    size_t i;
    slong n = cx->n;
    for (i = 0; i < p->n; i++) {
        const instr *in = &p->is[i];
        if (in->op == OP_PUSH_VAR || in->op == OP_PUSH_CONST) {
            tm1_t *t = stk + (*sp)++;
            slong k;
            if (in->op == OP_PUSH_VAR) {
                arb_set(t->f0, cx->yb + in->vi);
            } else {
                fmpq_t q;
                fmpq_init(q);
                fmpz_set(fmpq_numref(q), in->cn);
                fmpz_set(fmpq_denref(q), in->cd);
                arb_set_fmpq(t->f0, q, cx->prec_c);
                fmpq_clear(q);
            }
            for (k = 0; k < n; k++) {
                if (in->op == OP_PUSH_VAR && k == in->vi) arb_one(t->df + k);
                else arb_zero(t->df + k);
            }
            for (k = 0; k < n * n; k++) mag_zero(t->ddf + k);
            mag_zero(t->err);
            t->from_ite = 0;
            if (cx->tm_div2) {
                /* 认证下界注入：|xᵥ| ≥ 盒端点（bvars 球端点外向）；
                   |c| ≥ 常数球下界。arb_get_mag_lower 向下取 → sound。 */
                arb_t ab;
                arb_init(ab);
                if (in->op == OP_PUSH_VAR) {
                    arf_t lb2, hb2;
                    arf_init(lb2);
                    arf_init(hb2);
                    arb_get_lbound_arf(lb2, cx->bvars + in->vi, cx->prec_h);
                    arb_get_ubound_arf(hb2, cx->bvars + in->vi, cx->prec_h);
                    if (arf_sgn(lb2) > 0) {
                        arb_set_arf(ab, lb2);
                        arb_get_mag_lower(t->loa, ab);
                    } else if (arf_sgn(hb2) < 0) {
                        arb_neg(ab, cx->bvars + in->vi);
                        arb_get_mag_lower(t->loa, ab);
                    }
                    /* 值域对 = 盒球端点（外向） */
                    arf_set(t->cLo, lb2);
                    arf_set(t->cHi, hb2);
                    t->cvalid = 1;
                    arf_clear(lb2);
                    arf_clear(hb2);
                } else {
                    arb_get_mag_lower(t->loa, t->f0);
                    /* 值域对 = 常数球端点 */
                    arb_get_lbound_arf(t->cLo, t->f0, cx->prec_h);
                    arb_get_ubound_arf(t->cHi, t->f0, cx->prec_h);
                    t->cvalid = 1;
                }
                arb_clear(ab);
            }
            tm_update_W(t, cx);
        } else if (in->op == OP_ITE) {
            /* guard 盒上裸区间判定：可定 → 盒上 f 恒等于一支，递归 TM 该支 */
            size_t bsp = 0;
            evres cs = eval_prog(in->pc, (arb_srcptr)cx->bvars, (arb_t *)cx->bstk, &bsp,
                                 cx->prec_c, 0, NULL);
            int take_then = -1;
            if (cs != EV_OK) TM_FAIL(1);
            if (in->mode_eq) {
                if (arb_is_zero(cx->bstk)) take_then = 1;
                else if (arb_is_positive(cx->bstk) ||
                         arb_is_negative(cx->bstk)) take_then = 0;
            } else {
                if (arb_is_negative(cx->bstk)) take_then = 1;
                else if (arb_is_nonnegative(cx->bstk)) take_then = 0;
            }
            if (take_then < 0 && !cx->ite_hull && !cx->ite_hull2) TM_FAIL(2);
            if (take_then < 0) {
                /* --gsplit2：记录"本盒 TM 求值触发过 hull"及首个触发的 ite
                   guard prog（求值顺序外层先到先记；主循环每叶复位；
                   旗标门控，默认路径零改动） */
                if (cx->gsplit2 && !cx->gs_hit) {
                    cx->gs_hit = 1;
                    cx->gs_guard = in->pc;
                }
                /* 走廊压栈：then/else 各记一级（指令下标<<1|支号），div 诊断用 */
                if (cx->ite_depth < 24)
                    cx->ite_path[cx->ite_depth] = (size_t)i << 1;
                cx->ite_depth++;
                if (cx->hull_stats) cx->hs_sd++;
                if (eval_prog_tm(in->pt, stk, sp, cx)) {
                    cx->ite_depth--;
                    if (cx->hull_stats) cx->hs_sd--;
                    return 1;
                }
                if (cx->ite_depth > 0 && cx->ite_depth <= 24)
                    cx->ite_path[cx->ite_depth - 1] |= 1;
                if (eval_prog_tm(in->pe, stk, sp, cx)) {
                    cx->ite_depth--;
                    if (cx->hull_stats) cx->hs_sd--;
                    return 1;
                }
                cx->ite_depth--;
                if (cx->hull_stats) {
                    /* 事件：guard 跨0 → 双支求值 + hull 合成。
                       d0 = 本 ite 之上的 straddle ite 层数（先还原本 ite
                       入口时的自增，再读剩余计数的即为外层层数）。 */
                    cx->hs_sd--;
                    if (cx->hs_sd > cx->hs_a_dmax) cx->hs_a_dmax = cx->hs_sd;
                    if (cx->hs_sd < 15) cx->hs_strat_d[cx->hs_sd]++;
                    else cx->hs_strat_ovf++;
                    cx->hs_straddle++;
                    cx->hs_a_strat++;
                }
                if (cx->ite_hull2) {
                    /* --ite-hull2（df-hull 收紧版）：合成 TM 保留导数结构。
                     *
                     * 前提（与 lane log「分段光滑」同一组假设）：
                     *  P1 逐点分支选择：f(x) = guard(x)<0 ? then(x) : else(x)（精确实数语义）；
                     *  P2 分支在 guard 零点面 C¹ 吻合（549 的 dihatn 判别式结构），
                     *     且各分支在盒上分段 C² ⇒ f 分段 C²、梯度跨面连续；
                     *  P3 两支 TM 各自盒上有效，即满足四不变量（TM1 段头注记号）：
                     *     (I1) f_b(x) ∈ f0_b ⊕ Σᵢ df_b,ᵢ·δᵢ ⊕ B(err_b)，δᵢ=xᵢ−yᵢ∈[−wᵢ,wᵢ] 实数
                     *     (I2) |f_b| ≤ Bf_b   (I3) |∂ᵢf_b| ≤ |df_b,ᵢ|+Σⱼ wⱼ·ddf_b,ᵢⱼ
                     *     (I4) |∂²ᵢⱼf_b| ≤ ddf_b,ᵢⱼ
                     *
                     * 合成：df := 两支 df 逐分量区间 hull（arb_union，外向精确）；
                     *       ddf := 逐格 max；[c±err] ⊇ hull(f0_then ⊕ B(err_t),
                     *       f0_else ⊕ B(err_e))（c=中点，err=外向半宽）。
                     * 注意基值只并 err（余项球），不并 W——线性项改由 df-hull 承载，
                     * 这是相对常数版（f0±W 全并、df 归零）的收紧来源。
                     *
                     * soundness（合成 TM 对 f 满足 (I1)–(I4)）：
                     *  (I1) 固定 x（即固定实数组 δ）：P3(I1) 给
                     *      f_b(x) ∈ f0_b ⊕ Σᵢ df_b,ᵢδᵢ ⊕ B(err_b)。
                     *      df_b,ᵢ ⊆ hᵢ 且区间算术对实数 δᵢ 单调 ⟹ Σᵢ df_b,ᵢδᵢ ⊆ Σᵢ hᵢδᵢ；
                     *      又 f0_b ⊕ B(err_b) ⊆ c ⊕ B(err_s)（构造）⟹ f_b(x) ∈ c ⊕
                     *      Σᵢ hᵢδᵢ ⊕ B(err_s)。两支皆然，P1 取支后即 f(x) 同属。∎
                     *  (I3) 支内点：P3(I3) ≤ |df_b,ᵢ|+Σwⱼddf_b,ᵢⱼ ≤ |hᵢ|+Σwⱼ max(ddf)。
                     *      零点面上：∂ᵢf 沿面连续（P2 C¹），两侧界成立取极限亦成立。∎
                     *  (I4) 支内点 = 支 Hessian ≤ 各自 ddf ≤ max。零点面上 f 二阶
                     *      可导性不需另证——下游规则只用「坐标线段 MVT 的 sup」
                     *      语义（分段 C² + 梯度连续 ⟹ sup = 两片 sup 之 max）。∎
                     *  (I2) 由 (I1) 逐点推出。∎
                     * 下游 add/sub/mul/div/一元规则只消费 (I1)–(I4)，故链式合成
                     * sound。对照：常数版 df=ddf=0 破坏 (I3)/(I4)（Df 被低估为 0，
                     * 上游 mul/div 的 H 传播漏 ∂f·∂g 交叉项），仅逐点闭合安全；
                     * df-hull 版恢复全部四不变量，ite 之上再有复合也 sound。
                     */
                    {
                        tm1_t *tt = stk + (*sp - 2);
                        tm1_t *te = stk + (*sp - 1);
                        arb_t b1, b2, un, tmp;
                        arf_t lo, hi, mid, d1, d2;
                        slong a;
                        if (cx->tm_ddf) {
                            printf("[tm-ddf] hull event: d0=%d\n",
                                   cx->ite_depth);
                            tm_ddf_row("  in-then", tt, cx);
                            tm_ddf_row("  in-else", te, cx);
                        }
                        arb_init(b1); arb_init(b2); arb_init(un); arb_init(tmp);
                        arf_init(lo); arf_init(hi); arf_init(mid);
                        arf_init(d1); arf_init(d2);
                        arb_set(b1, tt->f0); arb_add_error_mag(b1, tt->err);
                        arb_set(b2, te->f0); arb_add_error_mag(b2, te->err);
                        arb_union(un, b1, b2, cx->prec_c);
                        arb_get_lbound_arf(lo, un, cx->prec_c);
                        arb_get_ubound_arf(hi, un, cx->prec_c);
                        arf_add(mid, lo, hi, cx->prec_c, ARF_RND_NEAR);
                        arf_mul_2exp_si(mid, mid, -1);
                        /* 外向半宽：err = max(hi−mid, mid−lo)（各自 CEIL，保证
                           [mid−err, mid+err] ⊇ [lo,hi]） */
                        arf_sub(d1, hi, mid, cx->prec_c, ARF_RND_CEIL);
                        arf_sub(d2, mid, lo, cx->prec_c, ARF_RND_CEIL);
                        if (arf_sgn(d1) < 0) arf_zero(d1);
                        if (arf_cmp(d2, d1) > 0) arf_set(d1, d2);
                        arb_set_arf(tmp, d1);
                        arb_get_mag(tt->err, tmp);
                        arb_set_arf(tt->f0, mid);
                        for (a = 0; a < cx->n; a++) {
                            arb_union(cx->ndf + a, tt->df + a, te->df + a,
                                      cx->prec_c);
                            arb_set(tt->df + a, cx->ndf + a);
                        }
                        for (a = 0; a < cx->n * cx->n; a++)
                            if (mag_cmp(tt->ddf + a, te->ddf + a) < 0)
                                mag_set(tt->ddf + a, te->ddf + a);
                        tt->from_ite = tm_src_join(tt->from_ite, te->from_ite);
                        if (!tt->from_ite) tt->from_ite = 2;
                        if (cx->tm_div2) {
                            /* 认证下界：x 落某支 → |f(x)| ≥ 两支较小者
                               （双双有认证才有效） */
                            if (!mag_is_zero(tt->loa) && !mag_is_zero(te->loa))
                                mag_min(tt->loa, tt->loa, te->loa);
                            else
                                mag_zero(tt->loa);
                            /* 值域对 = 两支并集 */
                            tt->cvalid = tt->cvalid && te->cvalid;
                            if (tt->cvalid) {
                                if (arf_cmp(tt->cLo, te->cLo) > 0)
                                    arf_set(tt->cLo, te->cLo);
                                if (arf_cmp(tt->cHi, te->cHi) < 0)
                                    arf_set(tt->cHi, te->cHi);
                            }
                        }
                        tm_update_W(tt, cx);
                        if (cx->tm_ddf) tm_ddf_row("  out-hull", tt, cx);
                        arb_clear(b1); arb_clear(b2); arb_clear(un);
                        arb_clear(tmp);
                        arf_clear(lo); arf_clear(hi); arf_clear(mid);
                        arf_clear(d1); arf_clear(d2);
                        (*sp)--;
                    }
                } else {
                    /* --ite-hull（549 车道决定性实验）：分段光滑（分支在判别式
                       零点 C¹ 吻合）前提下双支求值 + 保守 hull 合成。
                       soundness：逐点 f(x) ∈ hull(then 界, else 界)；合成 TM
                       退化为常数界（f0=hull 中点, df=0, ddf=0, err=半宽），
                       仅用于闭合判定（内核侧规则归 M2/CertTM）。 */
                    {
                        tm1_t *tt = stk + (*sp - 2);
                        tm1_t *te = stk + (*sp - 1);
                        arb_t b1, b2, un, tmp;
                        arf_t lo, hi, mid, wdt;
                        mag_t m;
                        slong a;
                        arb_init(b1); arb_init(b2); arb_init(un); arb_init(tmp);
                        arf_init(lo); arf_init(hi); arf_init(mid); arf_init(wdt);
                        mag_init(m);
                        arb_set(b1, tt->f0); arb_add_error_mag(b1, tt->W);
                        arb_set(b2, te->f0); arb_add_error_mag(b2, te->W);
                        arb_union(un, b1, b2, cx->prec_c);
                        arb_get_lbound_arf(lo, un, cx->prec_c);
                        arb_get_ubound_arf(hi, un, cx->prec_c);
                        arf_add(mid, lo, hi, cx->prec_c, ARF_RND_NEAR);
                        arf_mul_2exp_si(mid, mid, -1);
                        arf_sub(wdt, hi, lo, cx->prec_c, ARF_RND_CEIL);
                        arf_mul_2exp_si(wdt, wdt, -1);
                        arb_set_arf(tmp, wdt);
                        arb_get_mag(m, tmp);
                        arb_set_arf(tt->f0, mid);
                        for (a = 0; a < cx->n; a++) arb_zero(tt->df + a);
                        for (a = 0; a < cx->n * cx->n; a++) mag_zero(tt->ddf + a);
                        mag_set(tt->err, m);
                        tt->from_ite = tm_src_join(tt->from_ite, te->from_ite);
                        if (!tt->from_ite) tt->from_ite = 1;
                        if (cx->tm_div2) {
                            if (!mag_is_zero(tt->loa) && !mag_is_zero(te->loa))
                                mag_min(tt->loa, tt->loa, te->loa);
                            else
                                mag_zero(tt->loa);
                            tt->cvalid = tt->cvalid && te->cvalid;
                            if (tt->cvalid) {
                                if (arf_cmp(tt->cLo, te->cLo) > 0)
                                    arf_set(tt->cLo, te->cLo);
                                if (arf_cmp(tt->cHi, te->cHi) < 0)
                                    arf_set(tt->cHi, te->cHi);
                            }
                        }
                        tm_update_W(tt, cx);
                        arb_clear(b1); arb_clear(b2); arb_clear(un);
                        arb_clear(tmp);
                        arf_clear(lo); arf_clear(hi); arf_clear(mid);
                        arf_clear(wdt); mag_clear(m);
                        (*sp)--;
                    }
                }
            } else {
                int rt;
                if (cx->ite_depth < 24)
                    cx->ite_path[cx->ite_depth] =
                        ((size_t)i << 1) | (size_t)(take_then ? 0 : 1);
                if (cx->hull_stats) cx->hs_single++;   /* 事件：定号单支 */
                cx->ite_depth++;
                rt = eval_prog_tm(take_then ? in->pt : in->pe, stk, sp, cx);
                cx->ite_depth--;
                if (rt) return 1;   /* 保留内层失败原因 */
            }
        } else if (in->op == OP_ADD || in->op == OP_SUB ||
                   in->op == OP_MUL || in->op == OP_DIV) {
            tm1_t *f, *g;
            slong a, b;
            if (*sp < 2) die(EXIT_ERR, "TM 运行期 RPN 栈下溢");
            (*sp) -= 2;
            f = stk + *sp;
            g = stk + *sp + 1;
            if (in->op == OP_ADD || in->op == OP_SUB) {
                if (in->op == OP_ADD) arb_add(f->f0, f->f0, g->f0, cx->prec_c);
                else arb_sub(f->f0, f->f0, g->f0, cx->prec_c);
                for (a = 0; a < n; a++) {
                    if (in->op == OP_ADD)
                        arb_add(f->df + a, f->df + a, g->df + a, cx->prec_c);
                    else
                        arb_sub(f->df + a, f->df + a, g->df + a, cx->prec_c);
                }
                for (a = 0; a < n * n; a++)
                    mag_add(f->ddf + a, f->ddf + a, g->ddf + a);
                mag_add(f->err, f->err, g->err);
                f->from_ite = tm_src_join(f->from_ite, g->from_ite);
                if (cx->tm_div2) {
                    mag_zero(f->loa);   /* 和/差认证不传播（幅值） */
                    /* 值域对：区间加/减（端点外向，输出可别名输入） */
                    if (f->cvalid && g->cvalid) {
                        if (in->op == OP_ADD)
                            tm_pair_add(f->cLo, f->cHi, f->cLo, f->cHi,
                                        g->cLo, g->cHi, cx->prec_h);
                        else
                            tm_pair_sub(f->cLo, f->cHi, f->cLo, f->cHi,
                                        g->cLo, g->cHi, cx->prec_h);
                    } else {
                        f->cvalid = 0;
                    }
                }
                tm_update_W(f, cx);
            } else if (in->op == OP_MUL) {
                mag_t Bf, Bg, acc, t1;
                mag_init(Bf); mag_init(Bg); mag_init(acc); mag_init(t1);
                tm_Bmag(Bf, f);
                tm_Bmag(Bg, g);
                for (a = 0; a < n; a++) {
                    tm_Dmag(cx->Df + a, f, cx, a);
                    tm_Dmag(cx->Dg + a, g, cx, a);
                }
                /* 二阶盒界（先算，读旧 ddf；同 cell 读后写安全） */
                for (a = 0; a < n; a++)
                    for (b = 0; b < n; b++) {
                        mag_mul(acc, f->ddf + a * n + b, Bg);
                        mag_mul(t1, Bf, g->ddf + a * n + b);
                        mag_add(acc, acc, t1);
                        if (a == b && cx->tm_tight2) {
                            /* 对角完备化（--tm-tight2 实验旗标）：交叉斜率项
                               在 a=b 处 2·Df·Dg → Df²+Dg²（Cauchy–Schwarz
                               配平方向）。使传播矩阵结构性满足几何均值
                               ddfᵢⱼ ≤ √(ddfᵢᵢ·ddfⱼⱼ)（tm_err_from_ddf 注 (1)
                               的归纳步）。实测（549 试点 4 straddle 叶）：
                               负结果——对角变肥沿链放大 Df/Bf，根 err 反升
                               50–80%，故不并入 --tm-tight；留档对照。 */
                            mag_mul(t1, cx->Df + a, cx->Df + a);
                            mag_add(acc, acc, t1);
                            mag_mul(t1, cx->Dg + a, cx->Dg + a);
                            mag_add(acc, acc, t1);
                        } else {
                            mag_mul(t1, cx->Df + a, cx->Dg + b);
                            mag_add(acc, acc, t1);
                            mag_mul(t1, cx->Df + b, cx->Dg + a);
                            mag_add(acc, acc, t1);
                        }
                        mag_set(f->ddf + a * n + b, acc);
                    }
                /* 中心球：f0 = f·g，dfᵢ = dfᵢ·g0 + f0·dgᵢ（积法则） */
                {
                    arb_t nf0, t1a;
                    arb_init(nf0);
                    arb_init(t1a);
                    arb_mul(nf0, f->f0, g->f0, cx->prec_c);
                    for (a = 0; a < n; a++) {
                        arb_mul(t1a, f->df + a, g->f0, cx->prec_c);
                        arb_mul(cx->ndf + a, f->f0, g->df + a, cx->prec_c);
                        arb_add(cx->ndf + a, cx->ndf + a, t1a, cx->prec_c);
                    }
                    arb_set(f->f0, nf0);
                    for (a = 0; a < n; a++) arb_set(f->df + a, cx->ndf + a);
                    arb_clear(nf0);
                    arb_clear(t1a);
                }
                tm_err_from_ddf(f, cx);
                f->from_ite = tm_src_join(f->from_ite, g->from_ite);
                if (cx->tm_div2) {
                    mag_zero(f->loa);   /* 积认证不传播（幅值，保守） */
                    /* 值域对：区间乘 */
                    if (f->cvalid && g->cvalid)
                        tm_pair_muldiv(f->cLo, f->cHi, f->cLo, f->cHi,
                                       g->cLo, g->cHi, cx->prec_h, 0);
                    else
                        f->cvalid = 0;
                }
                tm_update_W(f, cx);
                mag_clear(Bf); mag_clear(Bg); mag_clear(acc); mag_clear(t1);
            } else {  /* OP_DIV：f/g，g 盒值域越零 → 不可用 */
                mag_t M, M2, M3, Bf, acc, t1;
                mag_init(M); mag_init(M2); mag_init(M3);
                mag_init(Bf); mag_init(acc); mag_init(t1);
                tm_Bmag(Bf, f);
                /* --tm-div2：模型值域跨 0 时试裸区间认证通道（M=1/loa，
                   sound 性见 tm_div2_salvage 注）；旗标关 → 与原路径一致 */
                if (!tm_inv_range_mag(M, g, cx) &&
                    !(cx->tm_div2 && tm_div2_salvage(M, g, cx))) {
                    mag_clear(M); mag_clear(M2); mag_clear(M3);
                    mag_clear(Bf); mag_clear(acc); mag_clear(t1);
                    tm_div_fail_diag(cx, g, i);
                    TM_FAIL(3);
                }
                mag_mul(M2, M, M);
                mag_mul(M3, M2, M);
                for (a = 0; a < n; a++) {
                    tm_Dmag(cx->Df + a, f, cx, a);
                    tm_Dmag(cx->Dg + a, g, cx, a);
                }
                /* ∂²ᵢⱼ(f/g) = ∂²ᵢⱼf/g − (∂ᵢf∂ⱼg + ∂ⱼf∂ᵢg)/g²
                   + f·(2∂ᵢg∂ⱼg/g³ − ∂²ᵢⱼg/g²) 的幅值界 */
                for (a = 0; a < n; a++)
                    for (b = 0; b < n; b++) {
                        mag_mul(acc, f->ddf + a * n + b, M);
                        mag_mul(t1, Bf, g->ddf + a * n + b);
                        mag_mul(t1, t1, M2);
                        mag_add(acc, acc, t1);
                        if (a == b && cx->tm_tight2) {
                            /* 对角完备化（--tm-tight2 实验旗标，同 mul 分支
                               注；实测负结果，留档对照）：
                               2·Df·Dg·M² → (Df²+Dg²)·M²；末项 2Bf·DgᵢDgⱼM³
                               为秩一项，几何均值精确，不动。 */
                            mag_mul(t1, cx->Df + a, cx->Df + a);
                            mag_mul(t1, t1, M2);
                            mag_add(acc, acc, t1);
                            mag_mul(t1, cx->Dg + a, cx->Dg + a);
                            mag_mul(t1, t1, M2);
                            mag_add(acc, acc, t1);
                        } else {
                            mag_mul(t1, cx->Df + a, cx->Dg + b);
                            mag_mul(t1, t1, M2);
                            mag_add(acc, acc, t1);
                            mag_mul(t1, cx->Df + b, cx->Dg + a);
                            mag_mul(t1, t1, M2);
                            mag_add(acc, acc, t1);
                        }
                        mag_mul(t1, cx->Dg + a, cx->Dg + b);
                        mag_mul(t1, t1, Bf);
                        mag_mul(t1, t1, M3);
                        mag_mul_2exp_si(t1, t1, 1);
                        mag_add(acc, acc, t1);
                        mag_set(f->ddf + a * n + b, acc);
                    }
                /* 中心球：f0 = f0/g0，dfᵢ = (dfᵢ·g0 − f0·dgᵢ)/g0²（商法则） */
                {
                    arb_t nf0, gsq, t1a;
                    arb_init(nf0);
                    arb_init(gsq);
                    arb_init(t1a);
                    arb_div(nf0, f->f0, g->f0, cx->prec_c);
                    arb_mul(gsq, g->f0, g->f0, cx->prec_c);
                    for (a = 0; a < n; a++) {
                        arb_mul(t1a, f->df + a, g->f0, cx->prec_c);
                        arb_mul(cx->ndf + a, f->f0, g->df + a, cx->prec_c);
                        arb_sub(cx->ndf + a, t1a, cx->ndf + a, cx->prec_c);
                        arb_div(cx->ndf + a, cx->ndf + a, gsq, cx->prec_c);
                    }
                    arb_set(f->f0, nf0);
                    for (a = 0; a < n; a++) arb_set(f->df + a, cx->ndf + a);
                    arb_clear(nf0);
                    arb_clear(gsq);
                    arb_clear(t1a);
                }
                tm_err_from_ddf(f, cx);
                f->from_ite = tm_src_join(f->from_ite, g->from_ite);
                if (cx->tm_div2) {
                    mag_zero(f->loa);   /* 商结果无认证 */
                    /* 值域对：区间商（分母对跨 0 → 轨道失效） */
                    if (f->cvalid && g->cvalid &&
                        !(arf_sgn(g->cLo) <= 0 && arf_sgn(g->cHi) >= 0))
                        tm_pair_muldiv(f->cLo, f->cHi, f->cLo, f->cHi,
                                       g->cLo, g->cHi, cx->prec_h, 1);
                    else
                        f->cvalid = 0;
                }
                tm_update_W(f, cx);
                mag_clear(M); mag_clear(M2); mag_clear(M3);
                mag_clear(Bf); mag_clear(acc); mag_clear(t1);
            }
            (*sp)++;
        } else {
            /* 一元：NEG / ABS / SQRT / ATAN / LOG / SIN / COS */
            tm1_t *f;
            slong a, b;
            if (*sp < 1) die(EXIT_ERR, "TM 运行期 RPN 栈下溢");
            f = stk + (*sp - 1);
            if (in->op == OP_NEG) {
                arb_neg(f->f0, f->f0);
                for (a = 0; a < n; a++) arb_neg(f->df + a, f->df + a);
                if (cx->tm_div2 && f->cvalid) {
                    /* 值域对端点交换取负（loa 不变） */
                    arf_t tmp;
                    arf_init(tmp);
                    arf_set(tmp, f->cLo);
                    arf_neg(f->cLo, f->cHi);
                    arf_neg(f->cHi, tmp);
                    arf_clear(tmp);
                }
                continue;   /* ddf/err/W 不变（loa 对 neg 也不变） */
            }
            if (in->op == OP_ABS) {
                /* 盒值域定号 → ±identity；跨 0 → 不可用（TMSafe 排除） */
                arf_t lo, hi;
                arf_init(lo);
                arf_init(hi);
                tm_range_arf(lo, hi, f, cx);
                if (arf_sgn(lo) > 0) {
                    /* identity：什么都不做；|abs(f)| ≥ lo（认证注入） */
                    if (cx->tm_div2) {
                        arb_t ab;
                        arb_init(ab);
                        arb_set_arf(ab, lo);
                        arb_get_mag_lower(f->loa, ab);
                        arb_clear(ab);
                        /* 值域对：|f| ∈ [0, max(|cLo|,|cHi|)]（sound） */
                        if (f->cvalid) {
                            if (arf_cmpabs(f->cLo, f->cHi) > 0)
                                arf_abs(f->cHi, f->cLo);
                            else
                                arf_abs(f->cHi, f->cHi);
                            arf_zero(f->cLo);
                        }
                    }
                } else if (arf_sgn(hi) < 0) {
                    arb_neg(f->f0, f->f0);
                    for (a = 0; a < n; a++) arb_neg(f->df + a, f->df + a);
                    if (cx->tm_div2) {
                        /* |abs(f)| = |f| ≥ |hi|（认证注入） */
                        arb_t ab;
                        arb_init(ab);
                        arb_neg(ab, f->f0);   /* −f0 球 ⊇ −f(y) > 0 */
                        arb_get_mag_lower(f->loa, ab);
                        arb_clear(ab);
                        /* 值域对：同上 */
                        if (f->cvalid) {
                            if (arf_cmpabs(f->cLo, f->cHi) > 0)
                                arf_abs(f->cHi, f->cLo);
                            else
                                arf_abs(f->cHi, f->cHi);
                            arf_zero(f->cLo);
                        }
                    }
                } else {
                    arf_clear(lo);
                    arf_clear(hi);
                    TM_FAIL(4);
                }
                arf_clear(lo);
                arf_clear(hi);
                continue;
            }
            /* 链法则 g∘f：先定 Mg'、Mg''（盒值域），再中心球，再 ddf/err/W */
            {
                mag_t Mg1, Mg2, acc, t1;
                arf_t lo, hi;
                mag_init(Mg1); mag_init(Mg2); mag_init(acc); mag_init(t1);
                arf_init(lo); arf_init(hi);
                tm_range_arf(lo, hi, f, cx);
                /* Df（内层 |∂ᵢf| 盒上界）必须在中心球更新 df 之前取——
                   链法则余项用的是内层偏导，读新 df 会低估（soundness） */
                for (a = 0; a < n; a++) tm_Dmag(cx->Df + a, f, cx, a);
                switch (in->op) {
                case OP_SQRT:
                    if (arf_sgn(lo) <= 0) goto tm_unary_fail;
                    tm_uni_M(Mg1, Mg2, lo, 0, cx->prec_h);
                    {
                        arb_t s, t2;
                        arb_init(s);
                        arb_init(t2);
                        arb_sqrt(s, f->f0, cx->prec_c);   /* f0 ≥ lo > 0 */
                        for (a = 0; a < n; a++) {
                            arb_mul_2exp_si(t2, s, 1);
                            arb_div(cx->ndf + a, f->df + a, t2, cx->prec_c);
                        }
                        arb_set(f->f0, s);
                        for (a = 0; a < n; a++) arb_set(f->df + a, cx->ndf + a);
                        arb_clear(s);
                        arb_clear(t2);
                    }
                    if (cx->tm_div2) {
                        /* 认证注入：√arg(x) ≥ √lo（lo = 参数模型值域下界
                           > 0，即 sqrt 成功条件本身；mag_lower 向下取）。
                           该认证不随后游线性包络变肥失效——div2 的关键。 */
                        arb_t ab;
                        arb_init(ab);
                        arb_set_arf(ab, lo);
                        arb_sqrt(ab, ab, cx->prec_h);
                        arb_get_mag_lower(f->loa, ab);
                        arb_clear(ab);
                        /* 值域对：单调换算（认证端点 > 0 才有效） */
                        if (f->cvalid && arf_sgn(f->cLo) > 0)
                            tm_pair_trans(f->cLo, f->cHi, f->cLo, f->cHi,
                                          cx->prec_h, 0);
                        else
                            f->cvalid = 0;
                    }
                    break;
                case OP_LOG:
                    if (arf_sgn(lo) <= 0) goto tm_unary_fail;
                    tm_uni_M(Mg1, Mg2, lo, 1, cx->prec_h);
                    for (a = 0; a < n; a++)
                        arb_div(cx->ndf + a, f->df + a, f->f0, cx->prec_c);
                    arb_log(f->f0, f->f0, cx->prec_c);
                    for (a = 0; a < n; a++) arb_set(f->df + a, cx->ndf + a);
                    if (cx->tm_div2) {
                        mag_zero(f->loa);
                        if (f->cvalid && arf_sgn(f->cLo) > 0)
                            tm_pair_trans(f->cLo, f->cHi, f->cLo, f->cHi,
                                          cx->prec_h, 1);
                        else
                            f->cvalid = 0;
                    }
                    break;
                case OP_ATAN:
                    mag_one(Mg1);
                    if (cx->tm_tight) {
                        tm_atan_M2sup(Mg2, lo, hi, cx->prec_h);
                    } else {
                        tm_Bmag(Mg2, f);
                        mag_mul_2exp_si(Mg2, Mg2, 1);     /* 2·Bf */
                        if (mag_cmp(Mg2, Mg1) > 0)
                            mag_set(Mg2, Mg1);            /* min(2Bf,1) */
                    }
                    {
                        arb_t d;
                        arb_init(d);
                        arb_mul(d, f->f0, f->f0, cx->prec_c);
                        arb_add_ui(d, d, 1, cx->prec_c);
                        for (a = 0; a < n; a++)
                            arb_div(cx->ndf + a, f->df + a, d, cx->prec_c);
                        arb_atan(f->f0, f->f0, cx->prec_c);
                        for (a = 0; a < n; a++) arb_set(f->df + a, cx->ndf + a);
                        arb_clear(d);
                    }
                    if (cx->tm_div2) {
                        mag_zero(f->loa);   /* atan 后无 |·| 认证 */
                        if (f->cvalid)
                            tm_pair_trans(f->cLo, f->cHi, f->cLo, f->cHi,
                                          cx->prec_h, 2);
                    }
                    break;
                case OP_SIN:
                    /* Mg' = |cos| ≤ 1；Mg'' = |−sin t| ≤ min(1, Bf) */
                    mag_one(Mg1);
                    tm_Bmag(Mg2, f);
                    if (mag_cmp(Mg2, Mg1) > 0) mag_set(Mg2, Mg1);
                    {
                        arb_t c0;
                        arb_init(c0);
                        arb_cos(c0, f->f0, cx->prec_c);
                        for (a = 0; a < n; a++)
                            arb_mul(cx->ndf + a, f->df + a, c0, cx->prec_c);
                        arb_sin(f->f0, f->f0, cx->prec_c);
                        for (a = 0; a < n; a++) arb_set(f->df + a, cx->ndf + a);
                        arb_clear(c0);
                    }
                    if (cx->tm_div2) {
                        mag_zero(f->loa);
                        /* 值域对：sin ⊆ [-1,1]（无条件 sound） */
                        arf_set_si(f->cLo, -1);
                        arf_set_si(f->cHi, 1);
                        f->cvalid = 1;
                    }
                    break;
                case OP_COS:
                    /* Mg' = |−sin t| ≤ min(1, Bf)；Mg'' = |−cos| ≤ 1 */
                    tm_Bmag(Mg1, f);
                    mag_one(Mg2);
                    if (mag_cmp(Mg1, Mg2) > 0) mag_set(Mg1, Mg2);
                    {
                        arb_t s0;
                        arb_init(s0);
                        arb_sin(s0, f->f0, cx->prec_c);
                        for (a = 0; a < n; a++) {
                            arb_mul(cx->ndf + a, f->df + a, s0, cx->prec_c);
                            arb_neg(cx->ndf + a, cx->ndf + a);
                        }
                        arb_cos(f->f0, f->f0, cx->prec_c);
                        for (a = 0; a < n; a++) arb_set(f->df + a, cx->ndf + a);
                        arb_clear(s0);
                    }
                    if (cx->tm_div2) {
                        mag_zero(f->loa);
                        arf_set_si(f->cLo, -1);
                        arf_set_si(f->cHi, 1);
                        f->cvalid = 1;
                    }
                    break;
                default:
                    goto tm_unary_fail;
                }
                /* Hᵢⱼ ≤ Mg''·Dfᵢ·Dfⱼ + Mg'·Hfᵢⱼ（Df 已在 switch 前用旧 df 算好；
                   此处读旧 ddf、同 cell 读后写安全） */
                for (a = 0; a < n; a++)
                    for (b = 0; b < n; b++) {
                        mag_mul(acc, cx->Df + a, cx->Df + b);
                        mag_mul(acc, acc, Mg2);
                        mag_mul(t1, Mg1, f->ddf + a * n + b);
                        mag_add(acc, acc, t1);
                        mag_set(f->ddf + a * n + b, acc);
                    }
                tm_err_from_ddf(f, cx);
                tm_update_W(f, cx);
                mag_clear(Mg1); mag_clear(Mg2); mag_clear(acc); mag_clear(t1);
                arf_clear(lo); arf_clear(hi);
                continue;
            tm_unary_fail:
                mag_clear(Mg1); mag_clear(Mg2); mag_clear(acc); mag_clear(t1);
                arf_clear(lo); arf_clear(hi);
                TM_FAIL(5);
            }
        }
    }
    return 0;
}

/* loBound = f0.lo − W > 0 → 0（闭合）；否则 1。调用方保证 TM 有效。 */
#pragma GCC diagnostic pop
static int tm_decide(const tm1_t *root)
{
    arf_t lo, wm;
    int r;
    arf_init(lo);
    arf_init(wm);
    arb_get_lbound_arf(lo, root->f0, 64);
    arf_set_mag(wm, root->W);
    arf_sub(lo, lo, wm, 64, ARF_RND_FLOOR);   /* ≤ 真 loBound，外向 */
    r = (arf_sgn(lo) > 0) ? 0 : 1;
    arf_clear(lo);
    arf_clear(wm);
    return r;
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

/* --gsplit：TM 梯度引导切分维（实验；仅 --ite-hull2 组合启用）。
 *
 * 动机：节点 TM 有效但未闭合（hull 太肥）时，最宽维未必是 hull 宽度的
 * 最大贡献者。切分维 i 使 wᵢ 减半 → 线性项 |dfᵢ|·wᵢ 收缩 ∝ wᵢ，二阶项
 * ∝ wᵢ²；故 scoreᵢ = |Dfᵢ|·wᵢ（|Dfᵢ| = tm_Dmag 盒上 |∂ᵢf| 界，零成本取数
 * —— 根 TM 的 df/ddf 已算好）最大的维是 hull 宽度的最大贡献者；
 * guard-贴附细胞上该方向近似 guard 曲面法向。
 *
 * 仅启发式（只影响切分顺序/叶数，不影响 soundness）：log 域比较
 * （mag_get_d_log2_approx）避免极端量级溢出；全零分数 → -1（退最宽维）。
 * 零宽维不可切（交叉相乘精确判零）。 */
static slong gsplit_dim(const leaf *L, const tm1_t *t, const tmctx *cx)
{
    slong i, best = -1;
    double bs = 0;
    fmpz_t wn;
    fmpz_init(wn);
    for (i = 0; i < L->nv; i++) {
        double s;
        mag_t dm;
        fmpz_mul(wn, L->hn + i, L->ld + i);
        fmpz_submul(wn, L->ln + i, L->hd + i);
        if (fmpz_is_zero(wn)) continue;          /* 零宽维不可切 */
        mag_init(dm);
        tm_Dmag(dm, t, cx, i);
        if (mag_is_zero(dm)) { mag_clear(dm); continue; }
        s = mag_get_d_log2_approx(dm) + mag_get_d_log2_approx(cx->w + i);
        mag_clear(dm);
        if (best < 0 || s > bs) { best = i; bs = s; }
    }
    fmpz_clear(wn);
    return best;
}

/* 盒一维 [lo,hi]（精确有理）→ 包含它的 Arb 球（定义见后；gsplit2_dim 前向引用） */
static void set_var_interval(arb_t dst, const fmpz_t ln, const fmpz_t ld,
                             const fmpz_t hn, const fmpz_t hd, slong prec);

/* --gsplit2：guard 引导切分维（实验；仅 --ite-hull2 组合启用）。
 *
 * 动机（区别于 --gsplit 的 |Df|·w hull 收紧目标）：让 straddle 叶变成
 * guard 定号单支叶（Lean 内核 evalTMHullD 只能验证定号单支叶 / straddle
 * 叶需付 hull 宽）。本盒 TM 求值触发过 hull（某 ite guard 盒上跨 0）时，
 * 对首个触发的 guard prog q 做敏感度探测：
 *   对每个维 i，把该维缩到中点半宽（其余维全盒）裸区间求值 q → q_i；
 *   区间算术包含单调 ⟹ q_i ⊆ q_full，width(q_i) ≤ width(q_full)。
 * 选使 q 区间宽度收缩最大（width(q_full)−width(q_i) 最大）的维——该维
 * 近似 guard 曲面法向，切开后子盒最可能 guard 定号（单支化）。
 * q_full 求值失败（INDET）、全零/负收缩 → -1（退最宽维）；零宽维跳过
 * （切不开，选它会层间死循环）。guard prog 小（549 根 guard ~2×10² ops），
 * nvars+1 次额外裸求值成本可忽略。
 * 仅启发式（只影响切分顺序/叶数，不影响 soundness）。 */
static slong gsplit2_dim(const leaf *L, const tmctx *cx,
                         arb_t *vars, arb_t *stk, size_t scap, slong prec)
{
    slong i, v, best = -1;
    size_t sp;
    arf_t wf, wi, shr, bshr;
    fmpz_t t_lh, t_hl, t_den, t_lo, t_hi;

    if (!cx->gs_guard || cx->gs_guard->n == 0) return -1;
    if (cx->gs_guard->total + 3 > scap) return -1;  /* 栈容量兜底（正常必满足） */

    /* q_full：全盒裸区间求值（vars/stk 复用主循环缓冲，此处已无读者） */
    for (v = 0; v < cx->n; v++)
        set_var_interval(vars[v], L->ln + v, L->ld + v, L->hn + v, L->hd + v, prec);
    sp = 0;
    if (eval_prog(cx->gs_guard, (arb_srcptr)vars, stk, &sp, prec, 0, NULL) != EV_OK)
        return -1;
    arf_init(wf);
    arf_init(wi);
    arf_init(shr);
    arf_init(bshr);
    arf_zero(bshr);
    {
        arf_t lo, hi;
        arf_init(lo);
        arf_init(hi);
        arb_get_lbound_arf(lo, stk[0], prec);
        arb_get_ubound_arf(hi, stk[0], prec);
        arf_sub(wf, hi, lo, prec, ARF_RND_CEIL);
        arf_clear(lo);
        arf_clear(hi);
    }
    fmpz_init(t_lh);
    fmpz_init(t_hl);
    fmpz_init(t_den);
    fmpz_init(t_lo);
    fmpz_init(t_hi);
    for (i = 0; i < cx->n; i++) {
        /* 维 i 缩到中点半宽（其余维全盒）：
           mid = (ln·hd + hn·ld)/(2 ld·hd)，rad = (hn·ld − ln·hd)/(2 ld·hd)
           ⟹ lo' = (3 ln·hd + hn·ld)/(4 ld·hd)，
              hi' = (ln·hd + 3 hn·ld)/(4 ld·hd) */
        fmpz_mul(t_lh, L->ln + i, L->hd + i);
        fmpz_mul(t_hl, L->hn + i, L->ld + i);
        if (fmpz_equal(t_lh, t_hl)) continue;       /* 零宽维不可切 */
        fmpz_mul(t_den, L->ld + i, L->hd + i);
        fmpz_mul_2exp(t_den, t_den, 2);
        fmpz_mul_ui(t_lo, t_lh, 3);
        fmpz_add(t_lo, t_lo, t_hl);
        fmpz_mul_ui(t_hi, t_hl, 3);
        fmpz_add(t_hi, t_hi, t_lh);
        set_var_interval(vars[i], t_lo, t_den, t_hi, t_den, prec);
        sp = 0;
        if (eval_prog(cx->gs_guard, (arb_srcptr)vars, stk, &sp, prec, 0, NULL)
            == EV_OK) {
            arf_t lo, hi;
            arf_init(lo);
            arf_init(hi);
            arb_get_lbound_arf(lo, stk[0], prec);
            arb_get_ubound_arf(hi, stk[0], prec);
            arf_sub(wi, hi, lo, prec, ARF_RND_CEIL);
            arf_sub(shr, wf, wi, prec, ARF_RND_NEAR);
            if (arf_cmp(shr, bshr) > 0) {
                arf_set(bshr, shr);
                best = i;
            }
            arf_clear(lo);
            arf_clear(hi);
        }
        /* 还原全盒球（下轮迭代对 vars[i] 先写后读，此处仅保不变式） */
        set_var_interval(vars[i], L->ln + i, L->ld + i, L->hn + i, L->hd + i, prec);
    }
    fmpz_clear(t_lh);
    fmpz_clear(t_hl);
    fmpz_clear(t_den);
    fmpz_clear(t_lo);
    fmpz_clear(t_hi);
    if (best < 0 || arf_sgn(bshr) <= 0) best = -1;
    arf_clear(wf);
    arf_clear(wi);
    arf_clear(shr);
    arf_clear(bshr);
    return best;
}

/* 叶最大维宽（double，仅作 TM 启用阈值的启发式，不参与 soundness） */
static double leaf_wmax(const leaf *L)
{
    slong i;
    double m = 0;
    for (i = 0; i < L->nv; i++) {
        double lo = fmpz_get_d(L->ln + i) / fmpz_get_d(L->ld + i);
        double hi = fmpz_get_d(L->hn + i) / fmpz_get_d(L->hd + i);
        if (hi - lo > m) m = hi - lo;
    }
    return m;
}

/* 每叶 TM 上下文装配：中心球 yb（精确 fmpq 中点入球）、半径包 w（mag 上界）、
   盒球 bvars（ite guard 裸区间判定用，∋ [lo,hi]）。 */
static void tm_setup_leaf(tmctx *cx, const leaf *L)
{
    slong i;
    for (i = 0; i < cx->n; i++) {
        fmpq_t mid, rad;
        fmpq_init(mid);
        fmpq_init(rad);
        /* mid = (ln*hd + hn*ld) / (2*ld*hd)；rad = (hn*ld - ln*hd) / (2*ld*hd) */
        fmpz_mul(fmpq_numref(mid), L->ln + i, L->hd + i);
        fmpz_addmul(fmpq_numref(mid), L->hn + i, L->ld + i);
        fmpz_mul(fmpq_denref(mid), L->ld + i, L->hd + i);
        fmpz_mul_2exp(fmpq_denref(mid), fmpq_denref(mid), 1);
        fmpz_mul(fmpq_numref(rad), L->hn + i, L->ld + i);
        fmpz_submul(fmpq_numref(rad), L->ln + i, L->hd + i);
        fmpz_mul(fmpq_denref(rad), L->ld + i, L->hd + i);
        fmpz_mul_2exp(fmpq_denref(rad), fmpq_denref(rad), 1);
        arb_set_fmpq(cx->yb + i, mid, cx->prec_c);   /* 中心球 ∋ yᵢ */
        {
            arb_t r;
            mag_t R;
            arb_init(r);
            mag_init(R);
            arb_set_fmpq(r, rad, cx->prec_h);
            arb_get_mag(cx->w + i, r);               /* wᵢ 上界 */
            arb_clear(r);
            /* 盒球 = 中点球心 + (rad 上界 + 中点球半径) */
            arb_set_fmpq(r, rad, cx->prec_c);
            arb_get_mag(R, r);
            mag_add(R, R, arb_radref(cx->yb + i));
            arb_zero(cx->bvars + i);
            arf_set(arb_midref(cx->bvars + i), arb_midref(cx->yb + i));
            mag_set(arb_radref(cx->bvars + i), R);
            arb_clear(r);
            mag_clear(R);
        }
        fmpq_clear(mid);
        fmpq_clear(rad);
    }
}

/* ---------------- 证书（闭叶收集 + JSON 输出） ---------------- */

typedef struct {
    leaf L;
    char hit[48];        /* "main" | "disj:k" | "var_lt:i,j" | "tm" */
    /* TM advisory 块（仅 hit=="tm"；内核不信任，stage-A 种子用，§2.3） */
    int   has_tm;
    slong tm_pc, tm_ph;    /* 实测够用的中心/Hessian 精度档 */
    slong tm_eexp;         /* 余项界数量级 hint：floor(log2(err)) */
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
    c->v[c->n].has_tm = 0;
    c->n++;
}

/* TM 闭合叶：附加 advisory 块（center 默认中点，按 §2.3 省略） */
static void closed_add_tm(cleafq *c, const leaf *L, slong pc, slong ph,
                          const mag_t err)
{
    closed_add(c, L, "tm");
    c->v[c->n - 1].has_tm = 1;
    c->v[c->n - 1].tm_pc = pc;
    c->v[c->n - 1].tm_ph = ph;
    c->v[c->n - 1].tm_eexp = mag_is_zero(err)
        ? -1022 : (slong)floor(mag_get_d_log2_approx(err));
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

/* --tm-debug 根盒包围打印（固定 "[tm]" 前缀；ite-hull2 对拍复用同一格式）。
   --tm-ddf 追加：盒半宽 wᵢ + 根 ddf 矩阵逐格（err/W/slope 分解离线算）。 */
static void tm_debug_dump(const tm1_t *r, slong nvars, const tmctx *cx)
{
    arf_t lo, hi, wm, lb, hb;
    slong v;
    arf_init(lo); arf_init(hi); arf_init(wm);
    arf_init(lb); arf_init(hb);
    arb_get_lbound_arf(lo, r->f0, 64);
    arb_get_ubound_arf(hi, r->f0, 64);
    arf_set_mag(wm, r->W);
    arf_sub(lb, lo, wm, 64, ARF_RND_FLOOR);
    arf_add(hb, hi, wm, 64, ARF_RND_CEIL);
    printf("[tm] f0=[%.17g, %.17g]  err=%.6e  W=%.6e\n",
           arf_get_d(lo, ARF_RND_DOWN), arf_get_d(hi, ARF_RND_UP),
           mag_get_d(r->err), mag_get_d(r->W));
    printf("[tm] |df|:");
    for (v = 0; v < nvars; v++) {
        mag_t m;
        mag_init(m);
        arb_get_mag(m, r->df + v);
        printf(" %.6e", mag_get_d(m));
        mag_clear(m);
    }
    printf("\n");
    printf("[tm] loBound=%.17g hiBound=%.17g\n",
           arf_get_d(lb, ARF_RND_DOWN), arf_get_d(hb, ARF_RND_UP));
    printf("[tm] decide=%s\n",
           tm_decide(r) == 0 ? "CLOSED" : "OPEN");
    if (cx != NULL && cx->tm_ddf) {
        slong i, j;
        printf("[tm-ddf] w:");
        for (v = 0; v < nvars; v++)
            printf(" %.6e", mag_get_d(cx->w + v));
        printf("\n");
        printf("[tm-ddf] ddf rows (|d2_ij|):\n");
        for (i = 0; i < nvars; i++) {
            printf("[tm-ddf]   ");
            for (j = 0; j < nvars; j++)
                printf(" %.6e", mag_get_d(r->ddf + i * nvars + j));
            printf("\n");
        }
    }
    arf_clear(lo); arf_clear(hi); arf_clear(wm);
    arf_clear(lb); arf_clear(hb);
}

/* ---------------- 主程序 ---------------- */

static void usage(void)
{
    fprintf(stderr,
            "用法: bb_arb <case.json> [--max-nodes N] [--prec P] [--cert out.json]\n"
            "       [--tm] [--tm-prec P] [--tm-hprec P] [--tm-w0 D] [--tm-debug]\n"
            "  --tm：叶判定启用一阶 Taylor 模型先行（默认关闭，裸区间路径零变动）\n"
            "  --ite-hull：ite guard 跨0 时双支求值 + 常数 hull 合成（实验）\n"
            "  --ite-hull2：同上但 df-hull 收紧合成（保留导数结构，实验）\n"
            "  --gsplit：TM 梯度引导切分（须配 --ite-hull2；TM 有效未闭合节点\n"
            "            切分维改选 |Df|·w 最大维，TM invalid/未尝试维持最宽维，实验）\n"
            "  --gsplit2：guard 引导切分（须配 --ite-hull2；TM 求值触发过 hull 的\n"
            "            节点切分维改选 guard 敏感度最大维——把 straddle 叶劈成\n"
            "            guard 定号单支叶；TM 未触发/未尝试维持最宽维，实验）\n"
            "  --tm-prec：TM 中心/一阶精度（默认 256）；--tm-hprec：Hessian 粗精度（默认 32）\n"
            "  --tm-w0：TM 启用盒宽阈值初值（默认 0.25，窗口自适应）\n"
            "  --tm-debug：只对根盒跑一次 TM 并打印包围，随后退出\n"
            "  --hull-stats：OP_ITE 闭合模式计数 + straddle 嵌套深度直方图\n"
            "            （摘要打印由本旗标门控；隐含 --tm；配 --probe 时逐盒附 mode）\n"
            "  --tm-tight：TM 余项 Schwarz 型收紧（min 保护）+ atan Mg'' 盒上 sup\n"
            "            （sound，err 只减不增；默认关）；--tm-tight2：对角完备\n"
            "            化实验（负结果留档）\n"
            "  --tm-ddf：余项解剖诊断打印（hull 合成事件 + --tm-debug 根盒\n"
            "            ddf 矩阵；只打印不判定，默认关）\n"
            "  --tm-div2：div 越零的裸区间认证通道（TM 槽并行裸区间轨道，\n"
            "            倒数界 M=1/loa 改由 |den| 认证下界；方向 sound，\n"
            "            默认关 = TM_FAIL(3) 语义逐字节不变）\n");
    exit(EXIT_ERR);
}

int main(int argc, char **argv)
{
    const char *path = NULL, *certpath = NULL, *probe_path = NULL;
    slong prec = 64;
    long max_nodes = 1L << 16;
    int tm_on = 0, tm_debug = 0, ite_hull = 0, ite_hull2 = 0, gsplit = 0;
    int tm_tight = 0, tm_tight2 = 0, tm_ddf = 0;
    int tm_div2 = 0;
    int gsplit2 = 0;
    int hull_stats = 0;
    slong tm_prec = 256, tm_hprec = 32;
    double tm_w0 = 0.25;
    int i;

    /* ---- 命令行 ---- */
    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--max-nodes") && i + 1 < argc) {
            max_nodes = strtol(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--prec") && i + 1 < argc) {
            prec = (slong)strtol(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--cert") && i + 1 < argc) {
            certpath = argv[++i];
        } else if (!strcmp(argv[i], "--tm")) {
            tm_on = 1;
        } else if (!strcmp(argv[i], "--tm-prec") && i + 1 < argc) {
            tm_prec = (slong)strtol(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--tm-hprec") && i + 1 < argc) {
            tm_hprec = (slong)strtol(argv[++i], NULL, 10);
        } else if (!strcmp(argv[i], "--tm-w0") && i + 1 < argc) {
            tm_w0 = strtod(argv[++i], NULL);
        } else if (!strcmp(argv[i], "--ite-hull")) {
            /* 549 车道决定性实验：ite 双支求值 + hull 合成（实验旗标，
               默认关闭；需配合 --tm 语义，此处隐含 tm_on） */
            ite_hull = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--ite-hull2")) {
            /* df-hull 收紧版：合成 TM 保留导数结构（soundness 注释见
               eval_prog_tm OP_ITE ite_hull2 分支；隐含 tm_on） */
            ite_hull2 = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--gsplit")) {
            /* 549 工位 TM 梯度引导切分（实验）：TM 有效但未闭合（hull 太肥）
               的节点切分维改选 |Df|·w 最大维；TM invalid / 未尝试节点维持
               最宽维。须与 --ite-hull2 组合（解析后校验）；隐含 tm_on。 */
            gsplit = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--gsplit2")) {
            /* 549 工位 guard 引导切分（实验）：TM 求值触发过 hull（某 ite
               guard 盒上跨 0 走了双支）的节点，二分维改选使 guard prog 裸
               区间宽度收缩最大的维（guard 曲面法向近似）——把 straddle 叶
               劈成 guard 定号单支叶（Lean 内核 evalTMHullD 路径）。
               须与 --ite-hull2 组合（解析后校验）；隐含 tm_on。 */
            gsplit2 = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--tm-debug")) {
            tm_debug = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--hull-stats")) {
            /* OP_ITE 闭合模式计数（549 工位 instrumentation）：single /
               straddle_hull / tm_fail 计数 + straddle 嵌套深度直方图，摘要
               打印与本旗标门控（默认路径零改动）；隐含 --tm，主场景与
               --ite-hull/--ite-hull2 组合。探针模式逐盒附 mode 字段。 */
            hull_stats = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--tm-tight")) {
            /* 549 工位：div/sqrt 分支余项压薄（C 侧先导实验）。两件事，
               均 sound 且 err 只减不增（min 保护）：
               ① tm_err_from_ddf 的 Schwarz/几何均值形（逐格检验认证，
                  不过检验即退全序对和）；
               ② atan Mg'' 用盒上 sup（单调段端点/全局峰 9/(8√3)）替代
                  min(2Bf,1)。
               默认关闭；隐含 --tm。
               注：曾试验 mul/div 对角完备化（2DfDg→Df²+Dg²，使几何均值
               结构性成立），实测使传播对角变肥、根 err 反升 50–80%（试点
               4 叶），已移出为 --tm-tight2 留档，不并入本旗标。 */
            tm_tight = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--tm-tight2")) {
            /* 实验（预期负结果，留档）：mul/div Hessian 对角完备化
               （2·Df·Dg → Df²+Dg²）。sound 性不变（上界方向），但传播
               对角变肥沿链放大，试点实测根 err 反升；仅供对照。 */
            tm_tight2 = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--tm-ddf")) {
            /* 549 工位余项解剖诊断（只打印、不判定，默认路径零输出）：
               OP_ITE hull 合成事件逐支 err/W/f0 dump + --tm-debug 根盒
               ddf 矩阵与 err 分解（全序对和 vs Schwarz 候选 + 几何均值
               检验结果 + 逐格贡献排序）。隐含 --tm。 */
            tm_ddf = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--tm-div2")) {
            /* 549 工位 div 规则收紧（C 侧独立于 Lean closed-trans/chop）：
               TM 槽并行裸区间认证轨道，tm_inv_range_mag 的模型值域跨 0
               时改用 |den| 认证下界（M=1/loa，方向 sound）。默认关闭 =
               div越零 TM_FAIL(3) 语义逐字节不变。隐含 --tm。 */
            tm_div2 = 1;
            tm_on = 1;
        } else if (!strcmp(argv[i], "--probe") && i + 1 < argc) {
            /* L1 探针（549 加速项目 Phase 0）：逐盒 TM 判定 + 带符号 df/σ dump；
               不二分、不产证书；隐含 --tm。默认路径零影响。 */
            probe_path = argv[++i];
            tm_on = 1;
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
    if (tm_prec < 8 || tm_prec > 4096) die(EXIT_ERR, "--tm-prec 需在 [8,4096]");
    if (tm_hprec < 8 || tm_hprec > 256) die(EXIT_ERR, "--tm-hprec 需在 [8,256]");
    if (!(tm_w0 > 0)) die(EXIT_ERR, "--tm-w0 需为正");
    if (gsplit && !ite_hull2)
        die(EXIT_ERR, "--gsplit 需与 --ite-hull2 组合（df-hull 合成保导数结构，"
                      "Df 引导才有意义）");
    if (gsplit && gsplit2)
        die(EXIT_ERR, "--gsplit 与 --gsplit2 互斥（目标不同：hull 收紧 vs "
                      "guard 单支化）");
    if (gsplit2 && !ite_hull2)
        die(EXIT_ERR, "--gsplit2 需与 --ite-hull2 组合（guard 跨0 须走 hull "
                      "路径才会记录触发）");

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
        if (ite_hull || ite_hull2) scap += 8;   /* ite-hull 双支并存槽位余量 */
        for (i = 0; i < (int)dis.n; i++)
            if (!dis.v[i].is_varlt && dis.v[i].p->total + 3 > scap)
                scap = dis.v[i].p->total + 3;
        arb_t *stk = xmalloc(scap * sizeof(arb_t));
        for (i = 0; i < (int)scap; i++) arb_init(stk[i]);
        arb_t *vars = xmalloc((size_t)nvars * sizeof(arb_t));
        for (i = 0; i < nvars; i++) arb_init(vars[i]);

        /* ---- TM 栈与上下文（仅 --tm 时分配；裸区间路径零变动） ---- */
        tm1_t *tstk = NULL;
        tmctx tcx;
        memset(&tcx, 0, sizeof(tcx));
        if (tm_on) {
            size_t k;
            tcx.n = nvars;
            tcx.prec_c = tm_prec;
            tcx.prec_h = tm_hprec;
            tcx.w = xmalloc((size_t)nvars * sizeof(mag_t));
            tcx.yb = xmalloc((size_t)nvars * sizeof(arb_t));
            tcx.bvars = xmalloc((size_t)nvars * sizeof(arb_t));
            tcx.Df = xmalloc((size_t)nvars * sizeof(mag_t));
            tcx.Dg = xmalloc((size_t)nvars * sizeof(mag_t));
            tcx.ndf = xmalloc((size_t)nvars * sizeof(arb_t));
            for (i = 0; i < nvars; i++) {
                mag_init(tcx.w + i);
                arb_init(tcx.yb + i);
                arb_init(tcx.bvars + i);
                mag_init(tcx.Df + i);
                mag_init(tcx.Dg + i);
                arb_init(tcx.ndf + i);
            }
            tcx.ite_hull = ite_hull;
            tcx.ite_hull2 = ite_hull2;
            tcx.gsplit2 = gsplit2;
            tcx.hull_stats = hull_stats;
            tcx.tm_tight = tm_tight;
            tcx.tm_tight2 = tm_tight2;
            tcx.tm_ddf = tm_ddf;
            tcx.tm_div2 = tm_div2;
            tcx.bstk = (arb_struct *)stk;   /* guard 裸区间求值复用主栈（TM 阶段它空闲） */
            tstk = xmalloc(scap * sizeof(tm1_t));
            for (k = 0; k < scap; k++) tm1_init(tstk + k, nvars);
        }

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
        /* TM 统计与自适应阈值（窗口 64 次尝试：全灭减半、过半且 <1 加倍） */
        long tm_att = 0, tm_ok = 0, tm_inv = 0, tm_val = 0;
        long tm_inv_r[8] = { 0 };   /* invalid 原因直方图（诊断） */
        long tm_win = 0, tm_win_ok = 0;
        double tm_thresh = tm_w0;
        /* --gsplit 统计（仅 gsplit 打印；默认路径零输出）：
           n_gs_used = TM 有效未闭合且 |Df|·w 选维生效；
           n_gs_fb   = gsplit 模式下退最宽维（TM invalid / 未尝试 / 全零分）；
           n_gs_dim  = gsplit 实际选中的维直方图 */
        long n_gs_used = 0, n_gs_fb = 0;
        long *n_gs_dim = NULL;
        if (gsplit) {
            size_t k;
            n_gs_dim = xmalloc((size_t)nvars * sizeof(long));
            for (k = 0; k < (size_t)nvars; k++) n_gs_dim[k] = 0;
        }
        /* --gsplit2 统计（仅 gsplit2 打印；默认路径零输出）：
           n_gs2_used = TM 触发过 hull 且 guard 敏感度选维生效；
           n_gs2_fb   = 退最宽维（未触发 hull / TM 未尝试 / 全零负收缩 /
                        guard 求值失败）；n_gs2_dim = 选中维直方图 */
        long n_gs2_used = 0, n_gs2_fb = 0;
        long *n_gs2_dim = NULL;
        if (gsplit2) {
            size_t k;
            n_gs2_dim = xmalloc((size_t)nvars * sizeof(long));
            for (k = 0; k < (size_t)nvars; k++) n_gs2_dim[k] = 0;
        }

        /* ---- --tm-debug：根盒单遍 TM，打印包围后退出 ---- */
        if (tm_debug) {
            size_t tsp = 0;
            tm_setup_leaf(&tcx, &rootbox);
            if (eval_prog_tm(mainp, tstk, &tsp, &tcx) != 0 || tsp != 1) {
                printf("[tm] INVALID（根盒 TM 不可用）reason=%d ip=%lu\n",
                       tcx.fail_reason, (unsigned long)tcx.fail_ip);
            } else {
                tm_debug_dump(tstk, nvars, &tcx);
            }
            if (ite_hull2) {
                /* 对拍：同一根盒用常数 hull 版再跑一遍（--ite-hull2 主跑为
                   df-hull；此处临时切常数版，打印格式同上供界宽对比） */
                size_t tsp2 = 0;
                tcx.ite_hull2 = 0;
                tcx.ite_hull = 1;
                tcx.fail_reason = 0;
                tm_setup_leaf(&tcx, &rootbox);
                printf("[tm] ---- 常数 hull 版对拍 ----\n");
                if (eval_prog_tm(mainp, tstk, &tsp2, &tcx) != 0 || tsp2 != 1) {
                    printf("[tm] INVALID（根盒 TM 不可用）reason=%d ip=%lu\n",
                           tcx.fail_reason, (unsigned long)tcx.fail_ip);
                } else {
                    tm_debug_dump(tstk, nvars, &tcx);
                }
            }
            if (hull_stats) tm_hull_stats_print(stdout, &tcx);
            /* 跳到清理段（closed 为空、无证书输出） */
            goto tm_debug_done;
        }

        /* ---- --probe FILE（L1 探针）：逐盒 TM 判定 + 带符号 df/σ dump。
           σᵢ=Σⱼ wⱼ·ddfᵢⱼ（坐标线段 MVT），盒上 ∂ᵢf ⊆ dfᵢ ± σᵢ；
           mono 定号率 = ∃i 使 dfᵢ±σᵢ 不跨 0。 ---- */
        if (probe_path) {
            FILE *pf = fopen(probe_path, "rb");
            long psz;
            char *ptext;
            jv *proot, *pboxes;
            size_t bi, nb;
            if (!pf) die(EXIT_ERR, "无法打开 %s", probe_path);
            fseek(pf, 0, SEEK_END);
            psz = ftell(pf);
            fseek(pf, 0, SEEK_SET);
            ptext = xmalloc((size_t)psz + 1);
            if (fread(ptext, 1, (size_t)psz, pf) != (size_t)psz)
                die(EXIT_ERR, "读取 %s 失败", probe_path);
            ptext[psz] = '\0';
            fclose(pf);
            proot = jparse(ptext, probe_path);
            pboxes = (jv *)jget(proot, "boxes");
            if (!pboxes || pboxes->t != J_ARR) die(EXIT_ERR, "probe 缺 boxes 数组");
            nb = pboxes->n;
            printf("{\"case\":\"%s\",\"n\":%lu}\n", caseid, (unsigned long)nb);
            for (bi = 0; bi < nb; bi++) {
                leaf L;
                const jv *bx = pboxes->items[bi];
                size_t tsp = 0;
                slong v, j2;
                leaf_init(&L, nvars);
                if (bx->t != J_ARR || (slong)bx->n != nvars)
                    die(EXIT_ERR, "probe box[%lu] 需 %ld 维 [lo,hi]",
                        (unsigned long)bi, (long)nvars);
                for (v = 0; v < nvars; v++) {
                    const jv *dim = bx->items[v];
                    if (dim->t != J_ARR || dim->n != 2)
                        die(EXIT_ERR, "probe box[%lu][%ld] 需 [lo,hi]",
                            (unsigned long)bi, (long)v);
                    jrat(L.ln + v, L.ld + v, dim->items[0], "probe 下端点");
                    jrat(L.hn + v, L.hd + v, dim->items[1], "probe 上端点");
                }
                tcx.fail_reason = 0;
                if (hull_stats) { tcx.hs_a_strat = 0; tcx.hs_a_dmax = 0; }
                tm_setup_leaf(&tcx, &L);
                if (eval_prog_tm(mainp, tstk, &tsp, &tcx) == 0 && tsp == 1) {
                    arf_t alo, ahi;
                    int closed = (tm_decide(tstk) == 0);
                    arf_init(alo);
                    arf_init(ahi);
                    if (hull_stats) {
                        /* 逐盒闭合模式（--hull-stats 门控；默认 probe 输出
                           逐字节不变）：strat = straddle-hull 事件数，
                           dmax = 最大嵌套深度（Lean 侧宽度 ×2 次数） */
                        int dmx = tcx.hs_a_dmax < 15 ? tcx.hs_a_dmax : 15;
                        printf("{\"i\":%lu,\"valid\":1,\"closed\":%d,"
                               "\"strat\":%ld,\"dmax\":%d,\"mode\":\"%s\","
                               "\"f0\":[",
                               (unsigned long)bi, closed,
                               tcx.hs_a_strat, tcx.hs_a_dmax,
                               tcx.hs_a_strat ? "straddle_hull" : "single");
                        /* 盒级归类（与主循环同口径，摘要打印用） */
                        if (tcx.hs_a_strat == 0) {
                            tcx.hs_lf_single++;
                            if (closed) tcx.hs_cl_single++;
                        } else {
                            tcx.hs_lf_hull++;
                            tcx.hs_lf_dmax[dmx]++;
                            if (closed) {
                                tcx.hs_cl_hull++;
                                tcx.hs_cl_dmax[dmx]++;
                            }
                        }
                    } else {
                        printf("{\"i\":%lu,\"valid\":1,\"closed\":%d,\"f0\":[",
                               (unsigned long)bi, closed);
                    }
                    arb_get_lbound_arf(alo, tstk[0].f0, 64);
                    arb_get_ubound_arf(ahi, tstk[0].f0, 64);
                    printf("%.17g,%.17g],\"df\":[",
                           arf_get_d(alo, ARF_RND_FLOOR),
                           arf_get_d(ahi, ARF_RND_CEIL));
                    for (v = 0; v < nvars; v++) {
                        arb_get_lbound_arf(alo, tstk[0].df + v, 64);
                        arb_get_ubound_arf(ahi, tstk[0].df + v, 64);
                        printf("%s[%.17g,%.17g]", v ? "," : "",
                               arf_get_d(alo, ARF_RND_FLOOR),
                               arf_get_d(ahi, ARF_RND_CEIL));
                    }
                    printf("],\"sig\":[");
                    for (v = 0; v < nvars; v++) {
                        mag_t s, t;
                        mag_init(s);
                        mag_init(t);
                        for (j2 = 0; j2 < nvars; j2++) {
                            mag_mul(t, tcx.w + j2, tstk[0].ddf + v * nvars + j2);
                            mag_add(s, s, t);
                        }
                        printf("%s%.6e", v ? "," : "", mag_get_d(s));
                        mag_clear(s);
                        mag_clear(t);
                    }
                    printf("]}\n");
                    arf_clear(alo);
                    arf_clear(ahi);
                } else {
                    printf("{\"i\":%lu,\"valid\":0,\"fail\":%d}\n",
                           (unsigned long)bi, tcx.fail_reason);
                    if (hull_stats && tcx.fail_reason >= 1 &&
                        tcx.fail_reason <= 6)
                        tcx.hs_fail_r[tcx.fail_reason]++;
                }
                fflush(stdout);
                leaf_free(&L);
            }
            if (hull_stats) tm_hull_stats_print(stdout, &tcx);
            goto tm_debug_done;   /* 清理段复用：无证书输出 */
        }

        qpush(&q, &rootbox);

        while (q.n > 0) {
            leaf L;
            int closed_main = 0, cex = 0, li;
            size_t sp = 0;
            evres st = EV_INDET;
            double min_sw = 1e300;   /* 本叶最细跨 0 guard 的球宽 */
            int tm_open_valid = 0;   /* --gsplit：本叶 TM 有效但未闭合（hull 太肥） */

            /* --gsplit2：straddle 追踪复位（每叶；含 TM 未尝试叶，防陈旧值） */
            if (gsplit2) {
                tcx.gs_hit = 0;
                tcx.gs_guard = NULL;
            }

            if (processed >= max_nodes) {
                /* 节点超限：输出未闭合叶列表，exit 2 */
                size_t k;
                fprintf(stderr, "[bb_arb] 节点超限（%ld），未闭合叶 %lu 个：\n",
                        max_nodes, (unsigned long)q.n);
                if (tm_on) {
                    fprintf(stderr, "[bb_arb] TM: att=%ld  valid=%ld  invalid=%ld"
                                    "  closed=%ld  thresh=%g\n",
                            tm_att, tm_val, tm_inv, tm_ok, tm_thresh);
                    fprintf(stderr, "[bb_arb] TM invalid 原因: guard-INDET=%ld"
                                    "  guard跨0=%ld  div越零=%ld  abs跨0=%ld"
                                    "  sqrt/log底非正=%ld  未知=%ld\n",
                            tm_inv_r[1], tm_inv_r[2], tm_inv_r[3],
                            tm_inv_r[4], tm_inv_r[5], tm_inv_r[6]);
                    if (ite_hull2) tm_div_diag_print(stderr, &tcx);
                    if (hull_stats) tm_hull_stats_print(stderr, &tcx);
                    if (gsplit) {
                        fprintf(stderr, "[bb_arb] gsplit（部分跑）: |Df|·w选维=%ld"
                                        "  最宽维回退=%ld\n", n_gs_used, n_gs_fb);
                    }
                    if (gsplit2) {
                        fprintf(stderr, "[bb_arb] gsplit2（部分跑）: guard敏感度选维=%ld"
                                        "  最宽维回退=%ld\n", n_gs2_used, n_gs2_fb);
                    }
                }
                for (k = 0; k < q.n; k++) {
                    fprintf(stderr, "  leaf %lu: ", (unsigned long)k);
                    print_box_human(stderr, &q.v[k], names);
                    fprintf(stderr, "\n");
                }
                exit(EXIT_LIMIT);
            }
            qpop(&q, &L);
            processed++;

            /* TM 先行（§2.3）：盒宽 ≤ 自适应阈值时先跑一阶 Taylor 判定；
               loBound > 0 → 闭合（hit "tm"），否则落回既有裸区间路径 */
            if (tm_on && leaf_wmax(&L) <= tm_thresh) {
                size_t tsp = 0;
                int closed_tm = 0;
                tm_att++;
                tcx.fail_reason = 0;
                if (hull_stats) { tcx.hs_a_strat = 0; tcx.hs_a_dmax = 0; }
                tm_setup_leaf(&tcx, &L);
                if (eval_prog_tm(mainp, tstk, &tsp, &tcx) == 0 && tsp == 1) {
                    tm_val++;
                    closed_tm = (tm_decide(tstk) == 0);
                    /* tstk[0]（df/ddf）与 tcx.w 在二分点前不再被改写，
                       gsplit 选维在二分块零成本取数 */
                    tm_open_valid = !closed_tm;
                    if (hull_stats) {
                        int dmx = tcx.hs_a_dmax < 15 ? tcx.hs_a_dmax : 15;
                        if (tcx.hs_a_strat == 0) {
                            tcx.hs_lf_single++;
                            if (closed_tm) tcx.hs_cl_single++;
                        } else {
                            tcx.hs_lf_hull++;
                            tcx.hs_lf_dmax[dmx]++;
                            if (closed_tm) {
                                tcx.hs_cl_hull++;
                                tcx.hs_cl_dmax[dmx]++;
                            }
                        }
                    }
                } else {
                    tm_inv++;
                    if (tcx.fail_reason >= 1 && tcx.fail_reason <= 6) {
                        tm_inv_r[tcx.fail_reason]++;
                        if (hull_stats) tcx.hs_fail_r[tcx.fail_reason]++;
                    }
                }
                tm_win++;
                tm_win_ok += closed_tm;
                if (tm_win >= 64) {
                    if (tm_win_ok == 0) tm_thresh *= 0.5;
                    else if (tm_win_ok * 2 >= tm_win && tm_thresh < 1.0)
                        tm_thresh *= 2.0;
                    tm_win = tm_win_ok = 0;
                }
                if (closed_tm) {
                    tm_ok++;
                    closed_add_tm(&closed, &L, tcx.prec_c, tcx.prec_h,
                                  tstk[0].err);
                    leaf_free(&L);
                    continue;
                }
            }

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
                        /* sp 复位：主 prog ite STRADDLE 早退留下 sp>0 时，
                           disj 支结果会落在 stk[sp] 而判据读 stk[0]
                           （栈污染伪影，2026-09-20 W6 诊断，最小反例 spbug2） */
                        sp = 0;
                        evres dst = eval_prog(dis.v[k].p, (arb_srcptr)vars, stk,
                                              &sp, prec, 0, NULL);
                        if (dst == EV_STRADDLE) {  /* guard 跨 0 → 并集兜底 */
                            sp = 0;
                            dst = eval_prog(dis.v[k].p, (arb_srcptr)vars, stk,
                                            &sp, prec, 1, NULL);
                        }
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

            /* 二分：默认最宽维、精确有理中点 (lo+hi)/2（fmpz 任意精度）。
                --gsplit：本叶 TM 有效但未闭合（hull 太肥）时改选 |Df|·w 最大维
                （hull 宽度最大贡献者；guard-贴附细胞上近似 guard 曲面法向）；
                TM invalid / 未尝试 / 全零分 → 维持最宽维。
                --gsplit2：本叶 TM 求值触发过 hull（guard 跨 0）时改选使首个
                触发的 guard prog 区间宽度收缩最大的维（guard 曲面法向近似，
                straddle 叶单支化）；未触发 / TM 未尝试 / 全零负收缩 /
                guard 求值失败 → 维持最宽维。 */
            {
                slong d = -1;
                leaf a, b;
                fmpz_t mn, md;
                if (gsplit2) {
                    if (tcx.gs_hit && tcx.gs_guard) {
                        d = gsplit2_dim(&L, &tcx, vars, stk, scap, prec);
                        if (d >= 0) {
                            n_gs2_used++;
                            n_gs2_dim[d]++;
                        } else {
                            n_gs2_fb++;   /* 全零/负收缩等：退最宽维 */
                        }
                    } else {
                        n_gs2_fb++;       /* 本盒 TM 未触发 hull / 未尝试 */
                    }
                } else if (gsplit && tm_open_valid) {
                    d = gsplit_dim(&L, tstk, &tcx);
                    if (d >= 0) {
                        n_gs_used++;
                        n_gs_dim[d]++;
                    } else {
                        n_gs_fb++;   /* 全零分（罕见）：退最宽维 */
                    }
                } else if (gsplit) {
                    n_gs_fb++;       /* TM invalid / 未尝试：维持最宽维 */
                }
                if (d < 0) d = widest_dim(&L);
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
        if (tm_on) {
            printf("[bb_arb] TM: att=%ld  valid=%ld  invalid=%ld  closed=%ld  thresh=%g\n",
                   tm_att, tm_val, tm_inv, tm_ok, tm_thresh);
            printf("[bb_arb] TM invalid 原因: guard-INDET=%ld  guard跨0=%ld"
                   "  div越零=%ld  abs跨0=%ld  sqrt/log底非正=%ld  未知=%ld\n",
                   tm_inv_r[1], tm_inv_r[2], tm_inv_r[3],
                   tm_inv_r[4], tm_inv_r[5], tm_inv_r[6]);
            if (ite_hull2) tm_div_diag_print(stdout, &tcx);
        }
        if (hull_stats) tm_hull_stats_print(stdout, &tcx);
        if (gsplit) {
            slong v;
            printf("[bb_arb] gsplit: |Df|·w选维=%ld  最宽维回退=%ld"
                   "  (回退占比 %.2f%%)\n",
                   n_gs_used, n_gs_fb,
                   n_gs_used + n_gs_fb
                       ? 100.0 * (double)n_gs_fb / (double)(n_gs_used + n_gs_fb)
                       : 0.0);
            printf("[bb_arb] gsplit 选维直方图:");
            for (v = 0; v < nvars; v++) printf(" %ld:%ld", (long)v, n_gs_dim[v]);
            printf("\n");
        }
        if (gsplit2) {
            slong v;
            printf("[bb_arb] gsplit2: guard敏感度选维=%ld  最宽维回退=%ld"
                   "  (回退占比 %.2f%%)\n",
                   n_gs2_used, n_gs2_fb,
                   n_gs2_used + n_gs2_fb
                       ? 100.0 * (double)n_gs2_fb / (double)(n_gs2_used + n_gs2_fb)
                       : 0.0);
            printf("[bb_arb] gsplit2 选维直方图:");
            for (v = 0; v < nvars; v++) printf(" %ld:%ld", (long)v, n_gs2_dim[v]);
            printf("\n");
        }

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
                if (closed.v[k].has_tm)
                    fprintf(f, ", \"tm\": {\"rung_c\": %ld, \"rung_h\": %ld,"
                               " \"err_exp\": %ld}",
                            (long)closed.v[k].tm_pc, (long)closed.v[k].tm_ph,
                            (long)closed.v[k].tm_eexp);
                fputc('}', f);
            }
            fprintf(f, "%s],\n  \"nodes\": %ld,\n  \"prec\": %ld\n}\n",
                    closed.n ? "\n  " : "", processed, (long)prec);
            fclose(f);
            printf("[bb_arb] cert: %s\n", certpath);
        }

        /* ---- 清理 ---- */
tm_debug_done:
        if (tstk) {
            size_t k;
            for (k = 0; k < scap; k++) tm1_clear(tstk + k, nvars);
            free(tstk);
            for (i = 0; i < nvars; i++) {
                mag_clear(tcx.w + i);
                arb_clear(tcx.yb + i);
                arb_clear(tcx.bvars + i);
                mag_clear(tcx.Df + i);
                mag_clear(tcx.Dg + i);
                arb_clear(tcx.ndf + i);
            }
            free(tcx.w); free(tcx.yb); free(tcx.bvars);
            free(tcx.Df); free(tcx.Dg); free(tcx.ndf);
        }
        for (i = 0; i < (int)scap; i++) arb_clear(stk[i]);
        free(stk);
        for (i = 0; i < nvars; i++) arb_clear(vars[i]);
        free(vars);
        for (i = 0; i < nvars; i++) free(names[i]);
        free(names);
        free(caseid);
        free(n_gs_dim);
        free(n_gs2_dim);
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
