#include "int_array_def.h"

int array_best_stock_profit(int *prices, int n)
/*@
    Require 0 <= n && n < 1000000 && IntArray::full_shape(prices, n)
    Ensure IntArray::full_shape(prices, n)
*/
{
    int i;
    int min_price;
    int best;
    if (n <= 1) {
        return 0;
    }
    min_price = prices[0];
    best = 0;
    i = 1;
    /*@ Inv
        exists v_i v_min v_best,
        1 <= v_i && v_i <= n@pre &&
        prices == prices@pre && n == n@pre &&
        0 <= n@pre && n@pre < 1000000 &&
        0 <= v_min && v_min <= 1000000 &&
        0 <= v_best && v_best <= 1000000 &&
        store(&i, int, v_i) * store(&min_price, int, v_min) *
        store(&best, int, v_best) *
        IntArray::full_shape(prices@pre, n@pre)
    */
    while (i < n) {
        if (prices[i] - min_price > best) {
            best = prices[i] - min_price;
        }
        if (prices[i] < min_price) {
            min_price = prices[i];
        }
        i = i + 1;
    }
    return best;
}
