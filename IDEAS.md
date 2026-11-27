# Ideas and bridges

Each entry is a picture from our earlier work and the problem it might illuminate. Status tags: **proven**, **open**, **observed**. Nothing here is claimed as new until we have checked the literature; see the honesty checklist in [METHOD.md](METHOD.md).

## 1. The flower on the circle (Li's Criterion)

- *Picture (observed, Fleurdelys `hilbert_polya.py`):* w = 1 − 1/s sends the critical line Re s = ½ to the unit circle |w| = 1. The ζ zeros land on it; the Davenport–Heilbronn zeros fall off.
- *Statement (proven, Li 1997; Bombieri–Lagarias 1999):* RH ⇔ λₙ = Σ_ρ (1 − (1 − 1/ρ)ⁿ) ≥ 0 for all n ≥ 1.
- *The story we want:* λₙ is a power sum over points wρ. On the circle, 1 − wⁿ has non-negative real part, so positivity is "every petal on the circle". Off the circle, |w| > 1 for some ρ makes wⁿ blow up and eventually forces some λₙ negative. Davenport–Heilbronn is the worked counterexample picture.
- *Lean plan:* the Bombieri–Lagarias route through sums over multisets of zeros; hunt Mathlib for the Hadamard product and zero-counting it needs, which may be the real bottleneck.

## 2. Zeros that hear primes (Cramér, Chebyshev bias)

- *Picture (observed, `zero_polar.py`, `prime_subsets.py`):* the explicit formula as a spectrum; primes reproduced by summing over zeros.
- *Bridge:* Cramér's RH gap bound and Littlewood's sign changes are both "how loudly the zeros can speak" statements. One shared explicit-formula lemma file could serve both.

## 3. Roots on and off the unit circle (Lehmer)

- *Picture:* Euler-product and determinant zetas (`zeta_determinants.py`) put roots on circles; Mahler measure measures how far roots sit outside.
- *Bridge:* the same "on the circle versus off it" visual as Li. A shared gallery could tie Tiers 1 and 3 together into one story about the unit circle.

## 4. Kneading and the ruler function (A127752)

- *Observed (Black Swan):* the period-doubling (Feigenbaum) kneading sequence equals ν₂(j) mod 2.
- *Open:* A127752 mod 2 equals that sequence. The inverse of a sparse triangular matrix whose row sums might obey a 2-adic recursion; a doubling recursion would match period doubling exactly.
- *First step:* compute a few thousand terms, guess the recursion, and state it in Lean.

## 5. Doubling chains in Collatz (A153330)

- *Observed (`collatz_structure.py`):* the steps plot shows curves (doubling chains) and dashes (8k+4 and 8k+5 always merge after a fixed number of steps).
- *Bridge:* the merge lemma is provable and gives a structured family of zero differences. Whether it gives "more than half" is open; it may give a positive-density lower bound, which would still be a worthwhile partial result.

## 6. Rotations everywhere (lonely runner, Pisot, Littlewood)

- *Picture (Black Swan, Fleurdelys `star_rotation.py`):* prime progressions, Mandelbrot orbits and runners on a track all turn by a fixed angle.
- *Bridge:* one Lean file of rotation and equidistribution lemmas, reused across Tao 2017, Koksma, and our reading on Littlewood.

## 7. The valley along the line (Newton for ξ)

- *Statement (proven equivalence, Lagarias 1999; Sondow–Dumitrescu 2010):* RH ⇔ Re(ξ′/ξ) > 0 to the right of the line ⇔ |ξ(σ + it)| strictly increases away from σ = ½.
- *Picture (observed, Fleurdelys `davenport_heilbronn.py`, `xi_pull.py`):* every Newton step for ξ points back toward the line; for Davenport–Heilbronn, 50 grid points near its off-line pair move the wrong way.
- *Bridge:* a second picture-first equivalence write-up after Li, and a visual companion to the Li story, with the same "everything flows to the circle or line" theme.

## 8. The positivity trick (how the primes enter)

- *Statement (proven, Mertens; de la Vallée Poussin):* 3 + 4 cos a + cos 2a = 2(1 + cos a)² ≥ 0, applied prime by prime to log|ζ³(σ)ζ⁴(σ+it)ζ(σ+2it)|, shows ζ has no zeros on Re s = 1.
- *Why it's here:* it is the model of a geometric argument that uses the Euler product, which the Davenport–Heilbronn test says any RH-adjacent proof must do. Black Swan already uses the same identity as its boost field.
- *Use:* the honesty filter in METHOD.md step 5, and a template for the "where do the primes enter" step in every write-up.
