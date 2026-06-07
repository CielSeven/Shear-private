#include "int_array_def.h"

int array_best_stock_profit(int *prices, int n)
/*@ With l
    Require 0 <= n && n < 1000000 && IntArray::full(prices, n, l) &&
            (forall (k: Z), (0 <= k && k < n) => 0 <= l[k] && l[k] <= 1000000)
    Ensure IntArray::full(prices, n, l)
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
    /*@ Inv Assert
        exists v_min v_best,
        min_price == v_min && best == v_best &&
        1 <= i && i <= n@pre &&
        prices == prices@pre && n == n@pre &&
        0 <= n@pre && n@pre < 1000000 &&
        0 <= v_min && v_min <= 1000000 &&
        0 <= v_best && v_best <= 1000000 &&
        (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l[k] && l[k] <= 1000000) &&
        IntArray::full(prices@pre, n@pre, l)
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
