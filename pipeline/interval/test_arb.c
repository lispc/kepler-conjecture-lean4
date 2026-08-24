/* Arb/FLINT smoke test：用球算术计算 pi 和 sqrt(2) 的 53-bit 球并打印。
 *
 * 编译（前缀按实际安装路径调整）：
 *   TOOLS=/path/to/pipeline/tools
 *   gcc -O2 test_arb.c -o test_arb \
 *     -I$TOOLS/flint-3.3.1/include -I$TOOLS/mpfr-4.2.2/include -I$TOOLS/gmp-6.3.0/include \
 *     -L$TOOLS/flint-3.3.1/lib -lflint \
 *     -L$TOOLS/mpfr-4.2.2/lib -lmpfr \
 *     -L$TOOLS/gmp-6.3.0/lib -lgmp -lm \
 *     -Wl,-rpath,$TOOLS/flint-3.3.1/lib -Wl,-rpath,$TOOLS/mpfr-4.2.2/lib -Wl,-rpath,$TOOLS/gmp-6.3.0/lib
 */
#include <stdio.h>
#include <math.h>
#include <flint/flint.h>
#include <flint/arb.h>

int main(void)
{
    const slong prec = 53;  /* double 精度 */
    arb_t x;
    arb_init(x);

    /* pi 的 53-bit 球：半径必须足够小，且真值落在球内 */
    arb_const_pi(x, prec);
    printf("pi  @53bit: ");
    arb_printd(x, 20);
    printf("\n");
    if (mag_cmp_2exp_si(arb_radref(x), -50) > 0) {
        fprintf(stderr, "FAIL: pi ball radius too large\n");
        return 1;
    }
    {
        double mid = arf_get_d(arb_midref(x), ARF_RND_NEAR);
        double rad = mag_get_d(arb_radref(x));
        if (fabs(mid - M_PI) > rad + 1e-18) {
            fprintf(stderr, "FAIL: pi not inside ball (mid=%.17g rad=%.3g)\n", mid, rad);
            return 1;
        }
    }

    /* sqrt(2) 的 53-bit 球 */
    arb_set_ui(x, 2);
    arb_sqrt(x, x, prec);
    printf("sqrt2@53bit: ");
    arb_printd(x, 20);
    printf("\n");
    {
        double mid = arf_get_d(arb_midref(x), ARF_RND_NEAR);
        double rad = mag_get_d(arb_radref(x));
        if (fabs(mid - sqrt(2.0)) > rad + 1e-18) {
            fprintf(stderr, "FAIL: sqrt2 not inside ball (mid=%.17g rad=%.3g)\n", mid, rad);
            return 1;
        }
    }

    arb_clear(x);
    printf("OK: arb ball arithmetic verified at 53-bit precision\n");
    return 0;
}
