#include "int_array_def.h"

int array_trap_rain_water(int *height, int n)
/*@ With l
    Require 0 <= n && n < 10000 && IntArray::full(height, n, l) &&
            (forall (k: Z), (0 <= k && k < n) => 0 <= l[k] && l[k] <= 100)
    Ensure IntArray::full(height, n, l)
*/
{
    int left;
    int right;
    int left_max;
    int right_max;
    int water;
    left = 0;
    right = n - 1;
    left_max = 0;
    right_max = 0;
    water = 0;
    /*@ Inv Assert
        exists v_left_max v_right_max v_water,
        left_max == v_left_max && right_max == v_right_max && water == v_water &&
        0 <= left && left <= right + 1 && right < n@pre &&
        height == height@pre && n == n@pre &&
        0 <= n@pre && n@pre < 10000 &&
        0 <= v_left_max && v_left_max <= 100 &&
        0 <= v_right_max && v_right_max <= 100 &&
        0 <= v_water && v_water <= 1000000 &&
        (forall (k: Z), (0 <= k && k < n@pre) => 0 <= l[k] && l[k] <= 100) &&
        IntArray::full(height@pre, n@pre, l)
    */
    while (left < right) {
        if (height[left] < height[right]) {
            if (height[left] >= left_max) {
                left_max = height[left];
            } else {
                water = water + left_max - height[left];
            }
            left = left + 1;
        } else {
            if (height[right] >= right_max) {
                right_max = height[right];
            } else {
                water = water + right_max - height[right];
            }
            right = right - 1;
        }
    }
    return water;
}
