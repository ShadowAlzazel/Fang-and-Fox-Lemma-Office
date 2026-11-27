# A127750: proof sketch (Lean file: `proofs/oeis-a127750.lean.txt`)

OEIS A127750: row sums of the inverse of the number triangle A(n,k) = 1/(2n+1) if k <= n <= 2k, 0 otherwise.
Conjecture in the entry: a(n) mod 2 gives the Fredholm-Rueppel sequence A036987. Both entries have offset 0, so there is no index shift.

1. The row sums a of the inverse triangle solve A a = (1, 1, 1, ...). Row n of that system reads
   (1/(2n+1)) * sum_{ceil(n/2) <= k <= n} a(k) = 1, so each window sum is 2n+1.
2. Differencing consecutive windows gives the doubling recursion
   a(0) = 1, a(2m+1) = a(m) + 2, a(2m+2) = 2 (terms 1, 3, 2, 5, 2, 4, 2, 7, ... as in the OEIS data).
   Every truncation of the triangle is lower triangular with nonzero diagonal, so it is invertible and
   its inverse has these row sums; the answer does not depend on the truncation size.
3. Mod 2: a(2m+2) is even and a(2m+1) has the parity of a(m), so by strong induction a(n) is odd iff n = 2^j - 1.
   That is the Formula-section characterization of A036987 ("a(n) = 1 iff n = 2^k - 1").

Checked with upstream `tools/lint.py` and `tools/check.sh` at formal-conjectures 9097e2f: kernel accepted,
axioms propext, Classical.choice, Quot.sound. Numerical cross-check (exact fractions): rows 0..63 give integers
matching the recursion and the parity pattern.
