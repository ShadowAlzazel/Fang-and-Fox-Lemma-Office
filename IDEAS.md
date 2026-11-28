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

## Source for items 9–14: a 2026 discrete-log preprint

Items 9–14 come from reading S. Liu, B. Zhang and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem" (Zhejiang University, dated 23 November 2026), next to our own pictures.

- *Provenance:* its main theorem is conditional on the Boolean tensor contraction construction in OpenAI's unrefereed preprint "The Exponential Time Hypothesis is false" (October 2026). These preprints are newer than the assistant's training data, so the premise is unverified here.
- *Its own reference list* includes a sceptical note by S. Szeider, "OpenAI's claimed refutation of ETH: exhaustive search below 2^131071".
- *Even granting the premise,* 2^{o(n)} time is not polynomial time, so nothing here bears on P versus NP.
- *What we take* is the toolkit, which is classical and checkable without the premise.

## 9. One doubling story (A402341, A127752, Feigenbaum)

- *Statement (proven, Frobenius and Lucas):* (1 + z)² ≡ 1 + z² (mod 2), so (1 + z)^y ≡ Π_i (1 + z^{2^i})^{y_i} (mod 2), where y_i are the binary digits of y. Equivalently, C(y, k) is odd exactly when the 1-bits of k are among those of y.
- *Statement (proven identity):* the same product is A402341's polynomial, 1 + x + ⋯ + x^{2^K−1} = Π_{j<K} (1 + x^{2^j}).
- *Statement (proven identity):* Kumi's orbit v_{i+1} = (v_i − 2)² is the doubling map in disguise. With v = x + 2 + 1/x, we get v_i = x^{2^i} + 2 + x^{−2^i}, because v_i − 2 = x^{2^i} + x^{−2^i}.
- *Already done:* Black Swan **observed** that the Feigenbaum kneading sequence equals ν₂(j) mod 2 (1,023 symbols). We **proved** in Lean that A127752 mod 2 is that sequence, for all n (item 4).
- *Bridge:* the discrete-log paper uses the same 2-adic bookkeeping as computation:
  - counts live in (Z/2^P)[z]/(z^ℓ);
  - Newton coefficients C(X, j) are read off truncated powers (1 + z)^y;
  - precision loss is tracked by 2-adic valuations.

  Period doubling, Frobenius, Lucas and Kummer carries, and the Chebyshev doubling orbit are one mechanism: doubling writes base-2 digit structure (ν₂, s₂) into a sequence.
- *First step:* one picture-first page that walks from the period-doubling cascade to ν₂ mod 2, then to Lucas, P_K(x) and the jewel lemma. It makes no new claims, only shows the shared mechanism. Check automatic-sequence references (Allouche–Shallit) before calling any link new.

## 10. Lean-sized lemmas inside the discrete-log paper

Each of these is **proven** and elementary, and holds whether or not the paper's headline premise does:

- *Half covers all:* if D ⊆ G, a finite abelian group, and |D| > |G|/2, then D + D = G. For every X, the sets D and X − D must meet. The paper uses this after showing that its sumset covers 7/8 of the group.
- *Energy bound:* let d(g) count representations, W = Σ_g d(g) and C = Σ_g d(g)². Then |supp d| ≥ W²/C, by Cauchy–Schwarz.
- *Coset halving (the paper's Lemma 4.4(b)):* take a nonempty affine solution coset of linear congruences mod M. Adding a congruence that the current point violates at least halves the coset. So at most N·log₂ M counterexamples are ever needed.
- *Fixed-shift soundness (the paper's Prop. 4.1):* if a labeling f of a cyclic group ⟨P⟩ satisfies f(g + P) ≡ f(g) + 1 for every g, and f(P) ≡ 1, then f(O) ≡ 0 and f is the discrete logarithm. In short: a labeling that steps by +1 along the generator is the log.
- *Positivity filter:* Q(X) = Π_{j=−w}^{w} (X − 1 − jM)² ≥ 0, and for |X| < (w + 1)M, Q(X) = 0 exactly when X ≡ 1 (mod M). So a sum of Q over all candidate pairs is 0 exactly when no counterexample exists. That is a "for all" check done by one sum, the same move as item 8.
- *First step:* check Left to Solve for matching targets before writing Lean (honesty checklist). Without a match, these are warm-up stories or Mathlib contributions, not credits. For the positivity step, Mathlib's `Finset.sum_eq_zero_iff_of_nonneg` should apply; confirm the name at the pinned Mathlib.

## 11. The second-moment method (Pisot orbits, Koksma)

- *Picture:* the paper's Stage I bounds the expected value of a potential over a random seed by a variance and a collision energy. It then fixes the seed bit by bit with conditional expectations.
- *Statement (proven, Koksma):* for almost every ξ, the sequence ξαⁿ is equidistributed mod 1 (α > 1). The usual proof bounds the mean square of Weyl sums over the parameter, then applies Borel–Cantelli along a sparse subsequence.
- *Bridge:* both arguments are the same second-moment computation: bound an average of squares, then make a good choice exist.
- *First step:* state the variance lemma on its own in Lean before the metric theorem. It is the reusable piece.

## 12. Terras' bijection: counting Collatz by relabeling (A153330)

- *Statement (proven, Terras 1976):* for T(n) = n/2 (n even) or (3n + 1)/2 (n odd), the parity vector of the first k steps of n depends only on n mod 2^k. The map from residues mod 2^k to parity vectors of length k is a bijection.
- *Bridge:* this is a count-preserving relabeling, exactly what the discrete-log paper demands of its gadgets ("parsimonious" encodings).
  - Density questions about step differences become counts over parity vectors.
  - Those counts can be computed exactly by prefix pinning: fix one bit at a time and keep counts. That is the paper's way of turning counting into search.
- *First step:* tabulate the A153330 quantity by residue class mod 2^k for k ≤ 20. See whether the density claim reduces to a parity-vector count, together with the 8k+4 / 8k+5 merge lemma of item 5.

## 13. "Lean-verified" and conditional (a claim-kit lesson)

- *Observed:* the paper's AI disclosure says all its theorems and lemmas passed Lean verification, yet its main theorem assumes the outside contraction theorem.
- *Lesson:* a kernel check of a conditional theorem certifies only the implication. Our checklist question "did we prove what the site states?" applies. In claim kits, name every hypothesis in the statement and in the pull-request text, as the Li page does with Hadamard summability.

## 14. SAT-side angles (Black Swan Experiment 05)

The SAT-side ideas are being explored in Black Swan, `experiments/05_counting_jewels/` (in progress on the session branch `claude/black-swan-repo-connect-eqsvs3`). Numbers measured so far, all **observed**:

- *Count instead of search.* Give every clause the weight z: Z(z) = Σ_k N_k z^k, where N_k counts assignments that violate k clauses.
  - For `missed_sat_instance_35.cnf` (18 variables), N = 9, 94, 538, 2248, …. Contraction evaluated at 77 points on the unit circle, followed by interpolation, matches brute force exactly.
  - Cauchy's integral of Z around circles of radius 0.5, 1 and 2 returns N₀ = 9. Here the argument principle is legitimate, because Z is a polynomial.
  - Exact counts reproduce all 96 SAT/UNSAT labels of Black Swan's Experiment 03.
  - Fixing bits one at a time by count (self-reduction) finds a witness in 0.03 s.
- *Cost.* Elimination width is about 0.69 n for random 3-SAT at α ≈ 4.26 (34, 69 and 137 at n = 50, 100 and 200). Experiment 03's geometric formulas stay near 10 at n = 32, against 22.5 for random ones.
  - On a 169-variable formula living on the hat patch, the orders give widths: min-fill 25, x-sweep 29, substitution-address order 76, random 103.
  - A random 3-SAT formula of the same size has width 114.
- *Johnson's conditional expectations* (the paper's derandomization method, applied to MAX-SAT). On Experiment 03's 89 satisfiable formulas, the deterministic start violates 1.40 clauses on average, against 11.43 for a random start. It solves 26 of 89 outright with no search, and does similarly across the planted, random and geometric families.
- *Count-preserving transformations.*
  - Black Swan's auxiliary-variable gadget is parsimonious: the extra variable is always forced.
  - Tovey's occurrence splitting preserves the count but raises the elimination width from 13 to 56 (min-degree). A definitional extension keeps width 13 and count 9.
- *Look-alike test,* our Davenport–Heilbronn rule applied to SAT. Planted 3-XOR-SAT with one equation per variable is solved instantly by Gaussian elimination. WalkSAT's median steps grow 180 → 3,948 → 12,384 at n = 20, 40, 60, while planted 3-SAT with the same 4n clauses needs 12 → 91 → 238.
- *Positivity as a detector:* the paper's filter, Black Swan's boost 2(1 + cos a)² and item 8's 3 + 4 cos a + cos 2a are one move. A sum of non-negative terms is zero only if every term is.
