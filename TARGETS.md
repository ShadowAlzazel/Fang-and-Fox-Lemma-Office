# Targets

Picked from [Left to Solve](https://lefttosolve.com) on 2026-11-26. Difficulty is the site's own 1–100 heuristic. Kinds: **warmup** (textbook), **known** (a proven result still missing a Lean proof; earns credit), **open** (unsolved), **unformalized** (no Lean statement yet, so it must be stated before it can be credited).

## Tier 0: test the pipeline

| Problem | Kind | Diff. | Why |
| --- | --- | ---: | --- |
| [Shanks: infinitely many record prime gaps](https://lefttosolve.com/p/MaximalPrimeGap.infinite_maximalPrimeGapIndex) | warmup | 16 | Gaps are unbounded, so records recur. A one-evening check that setup, leases and PRs all work. |
| [Dirichlet divisor bound Δ(x) = O(√x)](https://lefttosolve.com/p/DirichletDivisorProblem.divisor_error_dirichlet) | warmup | 16 | The hyperbola method; a good first story with a picture of lattice points under xy = N. |

## Tier 1: first real wins (known results, credited)

| Problem | Kind | Diff. | Fits | Why |
| --- | --- | ---: | --- | --- |
| [Li's Criterion](https://lefttosolve.com/p/RiemannHypothesis.li_criterion) | known | 42 | Fleurdelys `hilbert_polya.py` | RH ⇔ λₙ ≥ 0 for all n. Under w = 1 − 1/ρ the critical line becomes the unit circle; λₙ = Σ(1 − wⁿ). Our flower-on-a-circle picture *is* the argument (Bombieri–Lagarias). We prove the equivalence, not RH. |
| [Cramér's conditional gap bound](https://lefttosolve.com/p/CramerConjecture.cramer_conjecture.variants.conditional_rh) | known | 31 | `zero_polar.py`, explicit formula | Under RH, p₍ₙ₊₁₎ − pₙ = O(√pₙ log pₙ). The zeros reproducing the primes, quantified. |
| [Littlewood's mod-4 sign changes](https://lefttosolve.com/p/ChebyshevBias.littlewood_mod_four_sign_changes) | known | 43 | `lookalikes.py`, L(s, χ₄) | Chebyshev's bias flips infinitely often. We already plot L(s, χ₄) beside ζ. |
| [Lehmer's Mahler measure: not reciprocal](https://lefttosolve.com/p/LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.not_reciprocal) | known | 31 | `euler_product.py`, `zeta_determinants.py` | Smyth's theorem: the plastic number is the floor. Roots on and off the unit circle again. |
| [Lehmer's Mahler measure: odd coefficients](https://lefttosolve.com/p/LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.odd) | known | 31 | same | Golden ratio as the floor for odd-coefficient polynomials; ties to Black Swan's golden rotations. |
| [Lonely runner, Tao 2017](https://lefttosolve.com/p/LonelyRunnerConjecture.lonely_runner_conjecture.variants.tao_2017) | known | 31 | Black Swan rotations, coprime lattice | Runners on a circle are rotations by fixed angles, the same motion as our star rotations. |
| [Pisot orbits: almost every ξ](https://lefttosolve.com/p/Bugeaud61.problem_10_61.variants.almost_every) | known | 31 | Black Swan quasicrystals | Koksma's metric theorem: ξαⁿ is equidistributed mod 1 for almost every ξ. |
| [Spectral sets: 1D product](https://lefttosolve.com/p/SpectralSetProduct.isSpectral_right_of_product_one_dimensional) / [2D product](https://lefttosolve.com/p/SpectralSetProduct.isSpectral_right_of_product_two_dimensional) | known | 43 | Black Swan tilings | Fuglede's world: tiling and Fourier spectra. |

## Tier 2: research-grade (open), worth a serious look

| Problem | Kind | Diff. | Fits | Why |
| --- | --- | ---: | --- | --- |
| [OEIS A127752 ≡ Feigenbaum kneading sequence mod 2](https://lefttosolve.com/p/oeis-a127752) (also [oeis-a127751](https://lefttosolve.com/p/oeis-a127751)) | DONE (unformalized upstream) | 45 | [page](results/a127752/) | Stated and proved in Lean for all n (`results/a127752/A127752.lean`, `a127752_mod_two`). Window sums 3n+1 give a(2m+1) = a(m) + 3, a(2m+2) = 3, and mod 2 that is the ν₂ bit-flip. Own formalization; formal-conjectures has no statement yet, so not a credit match. |
| [Collatz step differences, conjecture 1](https://lefttosolve.com/p/OeisA153330.conjecture1) (and siblings) | open | 53–54 | `collatz_structure.py` | Doubling chains and the 8k+4 / 8k+5 merges explain why many differences are 0. A density claim, so likely hard, but our structure lemma may carry real weight. |
| [Shanks: record indices](https://lefttosolve.com/p/MaximalPrimeGap.shanks_maximal_prime_gap_conjecture.variants.record_indices) | open | 47 | `near_misses.py` | Natural sequel to the Tier 0 warmup. |
| [Montgomery pair correlation, general interval](https://lefttosolve.com/p/MontgomeryPairCorrelationConjecture.montgomery_pair_correlation_conjecture.variants.general_interval) | open | 48 | `pair_spacing.py` | Our pictures already show it. The dream target; treat as a moonshot. |

## Added by Kumi-San

| Problem | Kind | Diff. | Fits | Why |
| --- | --- | ---: | --- | --- |
| [Zeros around the midpoints of Gram intervals](https://lefttosolve.com/p/mo-366237) | unformalized | 55 | Fleurdelys Gram-law counts, `near_misses.py` | A MathOverflow question about where each zero sits inside the Gram interval it maps to. This is petal counting in its rawest form, and our zero tables up to height 30,000 can test it right away. It needs a precise statement first. |
| [No real zeros of ζ in (0,1)](results/li-criterion/) | DONE | — | Li page | Proved via a sum-versus-integral bound, not the Dirichlet η function. See Part III of the Li page and `NoRealZeros.lean`. This removes the `NoRealZerosInStrip` hypothesis. |
| Hadamard summability Σ m(ρ)/|ρ|² < ∞ for the zeros of ζ | Mathlib gap | — | Li page | The multiplicity-weighted bound, classical and unconditional. Mathlib lacks it. This is the analytic input of both directions on the Li page. |

## Reading, not targets

- [3/2 powers equidistributed mod 1](https://lefttosolve.com/p/Equidistribution.isEquidistributedModuloOne_three_halves_pow) (open, 59)
- [Littlewood conjecture](https://lefttosolve.com/p/LittlewoodConjecture.littlewood_conjecture) (open, 59): golden ratio is badly approximable, so it is the interesting test case.
- [SAT has no p-optimal proof system](https://lefttosolve.com/p/PudlakFiniteDomain.sat_no_p_optimal_proof_system) (open, 59)
- [Collatz](https://lefttosolve.com/p/CollatzConjecture.collatz_conjecture) (open, 58)
- Skip: P vs NP, P = BPP, ERH (100/100), Mandelbrot MLC and density of hyperbolicity.

## Order of attack

1. Shanks warmup (pipeline).
2. Li's Criterion (first story worth reading).
3. Lehmer odd / not-reciprocal, Littlewood mod 4, Cramér (one at a time).
4. ~~A127752: state it in Lean, then prove it.~~ Done, see `results/a127752/`.
5. Sibling [oeis-a127750](https://lefttosolve.com/p/oeis-a127750) (1/(2n+1), Fredholm–Rueppel mod 2): same argument with constant 2; checked numerically, not yet in Lean.
