#include "int_array_def.h"

int array_trap_rain_water(int *height, int n)
/*@ 
    Require IntArray::full_shape(height, n) 
    Ensure IntArray::full_shape(height, n)
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
    /*@ Inv
        exists v_left v_right v_left_max v_right_max v_water,
        0 <= v_left && v_left <= v_right + 1 && v_right < n@pre &&
        height == height@pre && n == n@pre &&
        store(&left, int, v_left) * store(&right, int, v_right) *
        store(&left_max, int, v_left_max) * store(&right_max, int, v_right_max) *
        store(&water, int, v_water) *
        IntArray::full_shape(height@pre, n@pre) 
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
