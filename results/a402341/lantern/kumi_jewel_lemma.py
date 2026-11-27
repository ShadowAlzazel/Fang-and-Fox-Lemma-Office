"""Lantern for A402341 (Kumi): checks the jewel lemma, not a proof.

The jewel: call a monic polynomial f(v) = sum_j f_j v^(deg-j) *strictly Kummer*
if nu_2(f_j) >= s_2(j) + 1 for every j >= 1 (s_2 = binary digit sum).
Lemma (proved in kumi-journey.md): every v_i in the orbit
    v_0 = v,  v_{i+1} = (v_i - 2)^2
is strictly Kummer. This script checks it coefficient by coefficient for i <= I.
Usage: python3 kumi_jewel_lemma.py [I]   (default I = 9, degree 512)
"""
import sys

def v2(x):
    return (x & -x).bit_length() - 1 if x else None   # None = +infinity

def s2(x):
    return bin(x).count("1")

def square(a):
    # a[j] = coefficient of v^(deg - j), so a[0] is the leading one
    c = [0] * (2 * len(a) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(a):
                c[i + j] += x * y
    return c

def strictly_kummer(f):
    if f[0] != 1:
        return False, 0
    for j in range(1, len(f)):
        e = v2(f[j])
        if e is not None and e < s2(j) + 1:
            return False, j
    return True, None

def main():
    I = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    f = [1, 0]                       # v_0 = v  (coefficients from the top)
    for i in range(I + 1):
        ok, where = strictly_kummer(f)
        tight = sum(1 for j in range(1, len(f)) if f[j] and v2(f[j]) == s2(j) + 1)
        print(f"v_{i}: degree {len(f)-1:5d}  strictly Kummer: {ok}"
              f"  (coefficients meeting the bound exactly: {tight})")
        assert ok, (i, where)
        g = f[:]; g[-1] -= 2         # v_i - 2
        f = square(g)                # v_{i+1}
    print("lemma holds for every v_i checked")

if __name__ == "__main__":
    main()
