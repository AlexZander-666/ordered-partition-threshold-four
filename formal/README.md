# Five consecutive ordered-partition rows at threshold four

For every old size n and every gap from one through four, the two original rows have strictly interlacing negative roots in the order appropriate to their degrees. This gives every pair of rows in a window of five, including constant rows. Windows of six fail arbitrarily late by a degree difference of two. The finite certificate covers all 1,152 pairs below size 288. The analytic result covers every n at least 288.

The entry module is OrderedPartitions.FourPoleAllSizes. Run python3 -Bu verify.py /absolute/path/to/locked/Lake/packages 3 from a clean extraction. External Lean and Mathlib checkouts are version locked. See modules.txt and audit-names.txt for the exact verification scope.
