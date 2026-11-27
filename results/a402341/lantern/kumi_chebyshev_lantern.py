"""Lantern for A402341 (Kumi): checks the folded-circle identity and the
termwise domination it gives. Numerics confirm the proof in kumi-journey.md;
they are not the proof.

For L = 2^K and n = 2t, with M = (L-1)t:
    a_K(2t) := [x^M] (1 + x + ... + x^(L-1))^(2t)
            = sum_J d_J * C(2(M-J), M-J),
where R_K(v)^t = sum_J d_J v^(M-J) and R_K = v_0 v_1 ... v_{K-1},
v_0 = v, v_{i+1} = (v_i - 2)^2.  Claimed: d_0 = 1 and
nu_2(d_J) + s_2(M-J) > s_2(M) for J >= 1, hence nu_2(a_K(2t)) = s_2(M).

Usage: python3 kumi_chebyshev_lantern.py [T]   (default T = 150, so n <= 300)
"""
import sys
from math import comb

def v2(x):
    return (x & -x).bit_length() - 1 if x else 10**9

def s2(x):
    return bin(x).count("1")

def mul(a, b):  # coefficient lists from the top degree down
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                c[i + j] += x * y
    return c

def R(K):
    r, f = [1], [1, 0]
    for _ in range(K):
        r = mul(r, f)
        g = f[:]; g[-1] -= 2
        f = mul(g, g)
    return r

def central_direct(L, n):
    # [x^(floor((L-1)n/2))] (1 + ... + x^(L-1))^n via the OEIS-style sum
    if n == 0:
        return 1
    h = (L - 1) * n // 2
    return sum((-1) ** j * comb(n, j) * comb(n - 1 + h - L * j, n - 1)
               for j in range(h // L + 1))

def main():
    T = int(sys.argv[1]) if len(sys.argv) > 1 else 150
    for K in range(1, 6):
        L = 2 ** K
        RK = R(K)
        P = [1]
        for t in range(0, T + 1):
            if t:
                P = mul(P, RK)
            M = (L - 1) * t
            assert len(P) == M + 1 and P[0] == 1
            a = sum(d * comb(2 * (M - J), M - J) for J, d in enumerate(P))
            assert a == central_direct(L, 2 * t), (K, t)
            for J in range(1, M + 1):
                if P[J]:
                    assert v2(P[J]) >= s2(J) + 1, (K, t, J)
                    assert v2(P[J]) + s2(M - J) > s2(M)
            assert v2(a) == s2(M), (K, t)
        print(f"K={K} (L={L}): identity, jewel bound, termwise domination and "
              f"nu_2 = s_2((L-1)n/2) all hold for even n <= {2*T}")
    # control: lengths that are not powers of two
    for L in (3, 5, 6, 7, 10, 12):
        bad = [2 * t for t in range(1, 41)
               if v2(central_direct(L, 2 * t)) != s2((L - 1) * t)]
        print(f"control L={L}: law fails at {len(bad)} of 40 even n, first {bad[:5]}")

if __name__ == "__main__":
    main()
