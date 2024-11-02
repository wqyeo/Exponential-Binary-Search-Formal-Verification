#include <stdio.h>
#include <limits.h>

/*@
// Predicate that checks if an array segment is sorted in non-decreasing order
predicate Sorted{L}(int* a, integer from, integer to) =
\forall integer i, j; from <= i <= j <= to ==> a[i] <= a[j];
*/

/*@
    // NOTE: Ensure initial value within bounds (0~max, low should be equal/smaller than high)
    requires 0 <= low <= high < INT_MAX;

    requires \valid_read(arr + (low .. high));
    requires Sorted(arr, low, high);

    assigns \nothing;
    ensures \result >= -1;

    // NOTE: Where the target exists, result should be in range, and indexed at target element.
    behavior found:
        assumes \exists int i; low <= i <= high && arr[i] == x;
        ensures low <= \result <= high && arr[\result] == x;
    
    // NOTE: Where array doesnt contain target, result is should be -1.
    behavior not_found:
        assumes \forall int i; low <= i <= high ==> arr[i] != x;
        ensures \result == -1;

    complete behaviors;
    disjoint behaviors;
*/
int binarySearch(int arr[], int low, int high, int x)
{   
    /*@
        loop invariant 0 <= low <= high + 1;

        // NOTE: The next low should always be higher than the original,
        // and the next higher should always be lower than the original.
        loop invariant low >= \at(low, Pre) && high <= \at(high, Pre);

        // NOTE: If the search has proceeded by 1 step, the element at the original 'low' must be smaller than target,
        // and the element at the original 'high' must be greater than the target.
        loop invariant low > \at(low, Pre) ==> x > arr[\at(low, Pre)];
        loop invariant high < \at(high, Pre) ==> x < arr[\at(high, Pre)];

        // NOTE: The target should be greater than all elements below the indexed 'low',
        // and target should be smaller than all the elements below the indexed 'high'.
        loop invariant \forall int i; \at(low, Pre) <= i < low ==> arr[i] < x;
        loop invariant \forall int i; high < i < \at(high, Pre) ==> arr[i] > x;

        loop assigns low, high;
        loop variant high - low;
    */
    while (low <= high) {
        int mid = low + (high - low) / 2;
        //@assert mid >= 0 && mid <= high;

        // Check if x is present at mid
        if (arr[mid] == x)
            return mid;

        // If x greater, ignore left half
        if (arr[mid] < x)
            low = mid + 1;

        // If x is smaller, ignore right half
        else
            high = mid - 1;
    }

    return -1;
}

/*@
    // NOTE: Mostly the same as binary search...
    requires 0 < n < INT_MAX;

    requires \valid_read(A + (0 .. n - 1));
    requires Sorted(A, 0, n- 1);

    assigns \nothing;

    ensures \result >= -1 && \result < n;

    behavior found:
        assumes \exists integer i; 0 <= i < n && A[i] == key;
        ensures 0 <= \result < n;
        ensures A[\result] == key;
    
    behavior not_found:
        assumes \forall integer i; 0 <= i < n ==> A[i] != key;
        ensures \result == -1;

    complete behaviors;
    disjoint behaviors;
*/
int exponential_search(int A[], int n, int key)
{
    int lower_bound = 0;
    int upper_bound = 1;
    int ret;

    /*@
        // NOTE: Lowerbound and upperbound should always be in indexing range,
        // and lowerbound should always be lower than upperbound.
        loop invariant 0 <= lower_bound < upper_bound <= n;

        // NOTE: Lowerbound is always increasing after each successful cycle.
        loop invariant lower_bound >= \at(lower_bound, LoopEntry);

        // NOTE: Everything below lowerbound index, the key should be greater than.
        loop invariant \forall int i; \at(lower_bound, LoopEntry) <= i < lower_bound ==> A[i] < key;

        // NOTE: Everything above upperbound index, the key should be smaller than.
        loop invariant \forall int i; upper_bound < i < \at(upper_bound, LoopEntry) ==> A[i] > key;

        loop assigns lower_bound, upper_bound;
        loop variant n - upper_bound;
    */
    while (upper_bound < n && A[upper_bound] < key) {
        lower_bound = upper_bound;
        upper_bound = upper_bound * 2;
        if (upper_bound > n) 
            upper_bound = n;
    }
  
    if (upper_bound >= n)
        upper_bound = n - 1;
    
    ret = binarySearch(A, lower_bound, upper_bound, key);
    
    return ret;
}

int main(void)
{
    int arr[] = { 2, 3, 4, 10, 40 };

    int n = sizeof(arr) / sizeof(arr[0]);
    int x = 10;


    Label_Before_Invoke: ;
    int result = exponential_search(arr, n, x);

    // NOTE: Ensure that the function did not modify the array.
    //@assert \forall int i; 0 <= i < n ==> arr[i] == \at(arr, Label_Before_Invoke)[i];

    if (result == -1)
        printf("Element is not present in array\n");
    else 
        //@assert arr[result] == x;
        printf("Element is present at index %d\n", result);
    return 0;
}