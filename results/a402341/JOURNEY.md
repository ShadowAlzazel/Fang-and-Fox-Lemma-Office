# A402341, the 2-adic lift beyond parity

Alo, 2026-11-27. Office credit: [ShadowAlzazel](https://github.com/ShadowAlzazel).

This is a Lemma Office journey note, not a Lean formalization and not a Left to Solve submission. Claims are labeled **proven**, **observed**, or **open**. Kumi-San's paper proof of the valuation lives in [`kumi-journey.md`](kumi-journey.md) and is not repeated here; I have not edited that file or her lanterns. The first half of this note is my own path through the four-factor product, Kummer carries, and the recursion. A separate referee pass of her argument is in the last section.

## The sequence, and the even-\(n\) valuation

[OEIS A402341](https://oeis.org/A402341) (Sajid Khan Hussain, Nov 17 2026), offset 0, is the central — equivalently, the largest — coefficient of \((1+x+\cdots+x^{15})^n\). The data begin \(1, 1, 16, 192, 2736, \ldots\). For odd \(n\) the degree \(15n\) is odd, so there are two middle coefficients; they are equal by palindromicity, and the OEIS example \(n=3\) records both as \(192\). Left to Solve lists the problem as [oeis-a402341](https://lefttosolve.com/p/oeis-a402341), still unformalized.

The OEIS entry conjectures that for even \(n\),

\[
\nu_2\bigl(a(n)\bigr) = \mathrm{A000120}(15n/2) = s_2(15n/2),
\]

where \(s_2\) is the sum of binary digits. This has been verified on the entry for even \(n\le 1500\). Equivalently, \(a(n)\big/\binom{15n}{15n/2}\) is a 2-adic unit, since Kummer's theorem (or Legendre's formula) gives \(\nu_2\binom{2m}{m}=s_2(m)\) with \(m=15n/2\).

The parity of \(a(n)\) is already settled on the entry: \(1+x+\cdots+x^{15}\equiv(1+x)^{15}\pmod{2}\), so \(a(n)\equiv\binom{15n}{\lfloor 15n/2\rfloor}\pmod{2}\), and \(a(n)\) is odd if and only if \(n=(16^k-1)/15\). **Kumi-San is writing that mod-2 story; this note does not repeat it.** The remaining content is the valuation *beyond* parity: when \(a(n)\) is already even, how many factors of 2 divide it.

## 1. Four factors and a family of polynomials (**proven** identities)

The geometric series factors completely over the first four powers of two:

\[
1+x+\cdots+x^{15} = \frac{1-x^{16}}{1-x} = \prod_{j=0}^{3}(1+x^{2^j}).
\]

Write generally \(P_K(x)=1+x+\cdots+x^{2^K-1}=\prod_{j=0}^{K-1}(1+x^{2^j})\), so the polynomial in A402341 is \(P_4\). The factors also give the functional equation

\[
P_K(x)=(1+x)\,P_{K-1}(x^2)
\]

(\(K\ge 1\), with \(P_0=1\)). The same valuation law — for even \(n\), the 2-adic valuation of the central coefficient of \(P_K^n\) equals \(s_2\bigl((2^K-1)n/2\bigr)\) — has been **observed** for several \(K\) well past the original scouting range; see the numerics in the referee section. The case \(K=1\) is Kummer's theorem itself: \(P_1=1+x\), the central coefficient is \(\binom{n}{n/2}\), and \(\nu_2\binom{2m}{m}=s_2(m)\). So A402341 is the \(K=4\) case of one pattern, and a proof that works uniformly in \(K\) is the natural target.

## 2. The product expansion, and why Kummer carries are not enough

Expanding the four factors, the central coefficient is a sum of products of ordinary binomials (**proven** identity): for even \(n\),

\[
a(n)=\sum_{k_0+2k_1+4k_2+8k_3=15n/2}\prod_{j=0}^{3}\binom{n}{k_j},
\]

the sum running over integers \(0\le k_j\le n\). For \(n=2m\) the balanced tuple \((m,m,m,m)\) is always present, and its 2-valuation is \(4\,s_2(m)\). The target valuation is \(s_2(15m)\). Since \(15m=m+2m+4m+8m\) and \(s_2(2^j m)=s_2(m)\), the popcount deficit

\[
4\,s_2(m)-s_2(15m)
\]

is exactly the total carry contribution (in the Kummer–Legendre sense) when those four shifted copies of \(m\) are added in base 2. The deficit vanishes if and only if the \(1\)-bits of \(m\) are spaced at least four positions apart, so the four copies never occupy the same bit. In particular it vanishes when \(m\) is a power of two, and then the balanced tuple already has the target valuation.

When the bits of \(m\) cluster, the balanced tuple is *strictly too divisible by 2*. If the conjecture is true, the minimum must then come from other tuples — or from cancellation among them.

The naive reading, that \(\nu_2(a(n))\) equals the minimum of \(\sum_j\nu_2\binom{n}{k_j}\) over those tuples, is **false**. That minimum is only a lower bound in the absence of cancellation, and cancellation does occur. For \(n=6\) (so \(m=3\)): the target is \(s_2(45)=4\), the balanced tuple has valuation \(4\,s_2(3)=8\), and a complete scan of the 4-tuples finds terms with \(\sum_j\nu_2\binom{6}{k_j}=1\), strictly below the actual \(\nu_2(a(6))=4\). Those low-valuation terms cancel 2-adically, and what survives has valuation equal to the target. So the raw Kummer minimum of the summands is not a proof of the conjecture, and is not even a sharp lower bound without a cancellation argument. This is the wrong basis in which to read the valuation.

## 3. Recursion from the functional equation (**proven** identity; a direct induction is awkward)

From \(P_K(x)^n=(1+x)^n P_{K-1}(x^2)^n\), the central coefficient satisfies

\[
\bigl[x^{(2^K-1)n/2}\bigr]P_K^n =\sum_{\substack{0\le i\le n\\ h-i\text{ even}}}\binom{n}{i}\,\bigl[x^{(h-i)/2}\bigr]P_{K-1}^n,
\]

where \(h=(2^K-1)n/2\). The “main” summand, \(i=n/2\) with \(n\) even, is \(\binom{n}{n/2}\) times the central coefficient of \(P_{K-1}^n\). If the valuation law holds at level \(K-1\), that term has valuation

\[
s_2(n/2)+s_2\bigl((2^{K-1}-1)n/2\bigr).
\]

This is at least the target \(s_2\bigl((2^K-1)n/2\bigr)\), because

\[
(2^K-1)\frac{n}{2}=2^{K-1}\cdot\frac{n}{2}+(2^{K-1}-1)\frac{n}{2},
\]

with equality if and only if adding those two summands produces no binary carry. When a carry occurs, the main term is too divisible, and the other indices \(i\) have to be controlled. To induct in this form, one seems to need a valuation law not just for the central coefficient of \(P_{K-1}^n\) but for a range of nearby coefficients. That is an awkward strengthening to take as an inductive hypothesis. The base \(K=1\) is Kummer, as already noted.

## 4. A central-binomial expansion, and a lemma that is true but too weak

The OEIS entry already writes \(a(n)\) as a \(\mathbb{Z}\)-linear combination of central binomials, coming from the change of variables \(u=z+z^{-1}\). Each \(z^{2^j}+z^{-2^j}\) is a monic polynomial in \(u\) of degree \(2^j\) (a Chebyshev polynomial), and

\[
f(u):=\prod_{j=0}^{3}(z^{2^j}+z^{-2^j})=u(u^2-2)(u^4-4u^2+2)(u^8-8u^6+20u^4-16u^2+2)
\]

is monic of degree 15. One has \(P_4(z^2)=z^{15}f(u)\). Expanding \(f(u)^n=\sum_m c(n,m)\,u^m\) and writing each \(u^m\) in the basis of \(z^k+z^{-k}\) produces the exact identity (**proven**)

\[
a(n)=\sum_{m\equiv n\pmod{2}}c(n,m)\binom{m}{\lfloor m/2\rfloor}.
\]

The leading coefficient is \(c(n,15n)=1\), so the top term is exactly \(\binom{15n}{15n/2}\), whose 2-valuation is \(s_2(15n/2)\) — the target. The valuation conjecture is therefore equivalent to this top term not being cancelled 2-adically by the rest of the sum, for even \(n\). A clean way to prove that is to show that every other term has *strictly higher* valuation.

### A lemma (**proven**, but short of the gap)

Each factor \(z^{2^j}+z^{-2^j}\), as a polynomial in \(u\), is monic with even lower-degree coefficients. This is visible for \(j=0,1,2,3\), and it is preserved under multiplication. Hence

\[
f(u)=u^{15}+2g(u)
\]

for some \(g\in\mathbb{Z}[u]\) of degree at most 14. Expanding \((u^{15}+2g)^n\), every coefficient \(c(n,m)\) with \(m<15n\) is divisible by 2:

\[
c(n,15n)=1,\qquad \nu_2\bigl(c(n,m)\bigr)\ge 1\quad\text{for }m<15n.
\]

The same holds for general \(K\): \(f_K(u)=u^{2^K-1}+2g_K(u)\).

Evenness of the lower coefficients is not enough by itself. The popcount \(s_2(m/2)\) can exceed \(s_2(15n/2)\) for some \(m<15n\), so a term with \(\nu_2(c(n,m))=1\) could in principle undercut or cancel the top term. One needs a little more 2-adic mass in \(c(n,m)\), or a bound on how large \(s_2(m/2)\) can be relative to the drop in degree. That extra mass is exactly what Kumi-San's “strictly Kummer” invariant is designed to supply (in the \(v=u^2\) basis, for even \(n\)); I do not repeat her argument in this half of the note.

## Referee notes on Kumi's flower

This section is an independent referee pass of the proof claimed in [`kumi-journey.md`](kumi-journey.md) (commit `569bf7f`). It is kept separate from the story above. I read that file and did not edit it.

### Verdict: sound

The argument is a complete paper proof of the OEIS / Left to Solve conjecture, and of the natural strengthening to every length \(2^K\). I did not find a gap in the identities, in the tail lemma, or in the assembly. I also did not find a numerical counterexample. The proof is not in Lean, and this is not a formalization review.

### What is being claimed, and whether it matches the source

A402341's \(a(n)\) is the central (largest) coefficient of \((1+x+\cdots+x^{15})^n\), offset 0. The Left to Solve problem [oeis-a402341](https://lefttosolve.com/p/oeis-a402341) asks only for the OEIS conjecture: for even \(n\), \(\nu_2(a(n))=s_2(15n/2)\), verified there for \(n\le 1500\). It does not ask for a law at odd \(n\).

Kumi-San writes \(n=2t\) and \(M=15t\), and claims \(\nu_2(a(2t))=s_2(15t)\). That is exactly the OEIS statement. She also proves a strengthening, for every \(K\ge 1\): if \(L=2^K\) and \(M=(L-1)t\), the coefficient of \(x^M\) in \((1+x+\cdots+x^{L-1})^{2t}\) has 2-adic valuation \(s_2(M)\), and more sharply is congruent to \(\binom{2M}{M}\) modulo \(2^{s_2(M)+1}\). The case \(K=4\) is A402341; the case \(K=1\) is Kummer's theorem. None of this overclaims the source at odd \(n\).

The restriction to even \(n\) is necessary. Already the OEIS example \(n=3\) has \(a(3)=192\), so \(\nu_2=6\), while \(s_2(\lfloor 15\cdot 3/2\rfloor)=s_2(22)=3\). Among odd \(n=1,3,\ldots,79\), the naive extension \(\nu_2(a(n))=s_2(\lfloor 15n/2\rfloor)\) fails 39 times and holds accidentally twice more if one goes to \(n=119\) (at \(n=25\) and \(n=89\) only). Her theorem is correctly scoped.

### Is the reduction from the polynomial to the \(v\)-expansion exact?

Yes. The unit-circle language in her write-up is a picture; the identities are algebraic. Set

\[
v_i=\frac{(1+x^{2^i})^2}{x^{2^i}}=x^{2^i}+2+x^{-2^i}.
\]

Then \(v_{i+1}=(v_i-2)^2\) holds as an identity of Laurent polynomials, and \(v_0=v:=x+2+x^{-1}\). Writing \(R_K(v)=v_0\cdots v_{K-1}\) (a monic polynomial in \(v\) of degree \(L-1\)), one has

\[
\frac{P_K(x)^{2t}}{x^M}=R_K(v)^t,
\]

because \(\prod_{i=0}^{K-1}x^{2^i}=x^{L-1}\) and \(M=(L-1)t\). The central coefficient \(a_K(2t)\) is therefore the constant term of \(R_K(v)^t\). Expand \(R_K(v)^t=\sum_{J=0}^{M}d_J v^{M-J}\) with \(d_0=1\). The constant term of \(v^m=(1+x)^{2m}/x^m\) is \(\binom{2m}{m}\), so by linearity

\[
a_K(2t)=\sum_{J=0}^{M}d_J\binom{2(M-J)}{M-J}.
\]

This is an identity in \(\mathbb{Z}\), not an approximation, and it is the even-\(n\) form of the OEIS central-binomial formula (her \(v\) is the square of the entry's \(u=z+z^{-1}\)). I rechecked it by expanding \(R_K^t\) and comparing to the inclusion-exclusion formula for \(a_K(2t)\), with no mismatch, for \(K=1\) and \(t\le 200\); \(K=2\) and \(t\le 200\); \(K=3\) and \(t\le 150\); \(K=4\) and \(t\le 80\); and \(K=5\) and \(t\le 40\).

### The tail lemma, stated precisely

A monic polynomial \(f(v)=\sum_j f_j v^{\deg f-j}\) is called **strictly Kummer** if \(\nu_2(f_j)\ge s_2(j)+1\) for every \(j\ge 1\). (There is no condition at \(j=0\), where monicity says \(f_0=1\).)

**Lemma 1.** A product of strictly Kummer polynomials is strictly Kummer. Valuation lower bounds also survive addition of coefficients (cancellation can only raise a valuation, never lower it).

**Lemma 2.** If \(f\) is strictly Kummer of degree \(n=2^i\), then so is \((f-2)^2\), of degree \(2n\).

**Corollary.** \(v_0=v\) is vacuously strictly Kummer, so every \(v_i\) is, by Lemma 2. Hence \(R_K\) and \(R_K^t\) are, by Lemma 1. In particular \(d_0=1\) and \(\nu_2(d_J)\ge s_2(J)+1\) for \(J\ge 1\).

**Assembly.** For each \(J\ge 1\),

\[
\nu_2\Bigl(d_J\binom{2(M-J)}{M-J}\Bigr)\ge s_2(J)+1+s_2(M-J)\ge s_2(M)+1,
\]

using Kummer's \(\nu_2\binom{2m}{m}=s_2(m)\) and subadditivity \(s_2(J)+s_2(M-J)\ge s_2(M)\). The leading term \(\binom{2M}{M}\) has valuation exactly \(s_2(M)\). It is therefore the unique 2-adic minimizer, there is no cancellation to fight, and

\[
a_K(2t)\equiv\binom{2M}{M}\pmod{2^{s_2(M)+1}},\qquad \nu_2\bigl(a_K(2t)\bigr)=s_2(M).
\]

### Scrutiny

I checked each step by hand.

Lemma 1 is clean. The coefficient of step \(J\ge 1\) in a product is \(\sum_{a+b=J}f_ag_b\). The two axis terms \(a=0\) or \(b=0\) inherit the bound from one factor. For \(a,b\ge 1\) one gets \(\nu_2\ge s_2(a)+s_2(b)+2\ge s_2(a+b)+2\), which is strictly stronger. The parenthetical about sums is not a claim that a sum of monic polynomials remains monic; it is only the fact that \(\nu_2(x+y)\ge\min(\nu_2(x),\nu_2(y))\). That is the right fact, and it is used correctly in Lemma 2 when the pieces of \((f-2)^2=f^2-4f+4\) are added. Cancellation is harmless for a lower bound.

Lemma 2 is the heart, and it holds. Write coefficients in degree \(2n\), so \(-4f\) sits at steps \(j=n+j'\) with \(0\le j'\le n\), and \(+4\) sits at step \(j=2n\). Because \(n\) is a power of two, \(s_2(n+j')=1+s_2(j')\) whenever \(0\le j'<n\). The pieces then meet the bound, and therefore so does their sum:

- at \(j=n\) (\(j'=0\)): \(-4\) has \(\nu_2=2=s_2(n)+1\), and \(f^2\) is already strictly Kummer;
- at \(n<j<2n\): the \(-4f_{j'}\) term has \(\nu_2\ge 2+s_2(j')+1=s_2(j)+2\), which is more than enough;
- at \(j=2n\): \(+4\) has \(\nu_2=2=s_2(2n)+1\), and \(-4f_n\) is even heavier.

The remark that \(f-2\) alone would break the jewel is correct: the constant term of \(f-2\) contributes a bare \(2\) at step \(n\), one factor short of \(s_2(n)+1=2\). Squaring turns that \(2\) into a \(4\). The same arithmetic explains why the argument is tied to lengths \(2^K\): the bit-count identity \(s_2(n+j')=1+s_2(j')\) for all \(j'<n\) holds if and only if \(n\) is a power of two.

The assembly has no missing case. It includes \(J=M\), where \(\binom{0}{0}=1\) and \(s_2(0)=0\), and \(t=0\), where \(a(0)=1\) and \(\nu_2(1)=0=s_2(0)\). Because the leading term is the unique minimizer, the valuation of the sum is exactly the valuation of \(\binom{2M}{M}\), signs and all.

I looked for a counterexample to the jewel itself on the concrete polynomials, not just to the valuation of \(a(n)\). Every \(v_i\) for \(i\le 12\) (degree \(4096\)) is strictly Kummer, with equality only at the two steps \(2^{i-1}\) and \(2^i\) when \(i\ge 1\), matching her lantern. Every \(R_K\) for \(K=1,\ldots,8\) is strictly Kummer. On the \((K,t)\) ranges listed above, every tail coefficient \(d_J\) obeyed \(\nu_2(d_J)\ge s_2(J)+1\), every non-leading term was at least one 2 more divisible than the target, and the sharper congruence held. I found no counterexample.

### Independent numerics, past \(n=300\)

All checks below used an independent implementation (inclusion-exclusion for \(a_K(n)\), and an explicit expansion of the \(v_i\) for the fold and the jewel), not a rerun of her lantern scripts.

- The first 20 OEIS terms of A402341 match the inclusion-exclusion formula (and the definition).
- Valuation, for every even \(n\) in the range, with no failures: \(K=2\) and \(K=3\) with \(n\le 2000\); \(K=4\) with \(n\le 4000\); \(K=5\) with \(n\le 800\); \(K=6\) with \(n\le 400\).
- The sharper congruence \(a_K(2t)\equiv\binom{2M}{M}\pmod{2^{s_2(M)+1}}\), for every even \(n\) in the range, with no failures: \(K=2\) and \(K=3\) with \(n\le 2000\); \(K=4\) with \(n\le 2800\); and at the additional samples \((K,n)=(4,3000),\ (4,3500),\ (4,4000),\ (5,400),\ (5,600),\ (5,800),\ (6,200),\ (6,300),\ (6,400)\).
- The fold identity, the jewel on every \(d_J\), termwise domination, the valuation, and the congruence, as already listed: \(K=1\) (\(t\le 200\)), \(K=2\) (\(t\le 200\)), \(K=3\) (\(t\le 150\)), \(K=4\) (\(t\le 80\)), \(K=5\) (\(t\le 40\)). No failures.

These checks do not replace the proof. They would have caught a gap that shows up at moderate \(n\) or moderate \(K\), and they did not.

### What this does not sign off

The proof is on paper, not in Lean. The further questions she lists — the residue of the 2-adic unit \(a_K(2t)/\binom{2M}{M}\), a valuation law at odd \(n\), and odd primes \(p\) — remain **open** and lie outside the theorem just reviewed. Nothing was submitted to Left to Solve or the OEIS.

## Labels, in one place

- **Proven** (identities and lemmas in my half of the note). The four-factor identity and the functional equation \(P_K(x)=(1+x)P_{K-1}(x^2)\). The 4-tuple expansion. The central-binomial expansion in \(u\), with leading coefficient \(c(n,15n)=1\). Evenness of \(c(n,m)\) for \(m<15n\). Kummer's theorem as the case \(K=1\). The popcount identity relating \(4s_2(m)\) to \(s_2(15m)\) via carries. The mod-2 theorem is already on the OEIS entry (and is Kumi-San's lane, not proved again here).
- **Proven** (Kumi-San's paper proof, referee verdict sound). For every \(K\ge 1\) and every even \(n=2t\), the central coefficient of \(P_K^n\) has 2-adic valuation \(s_2((2^K-1)t)\), and is congruent to \(\binom{2M}{M}\) modulo \(2^{s_2(M)+1}\). This includes the A402341 conjecture. The proof is not in Lean and has not been formalized.
- **Observed.** Independent numerical checks as listed in the referee section, past the OEIS bound and past her lantern bound of even \(n\le 300\). Failure of the naive odd-\(n\) extension, already at the OEIS example \(n=3\). Cancellation among low-valuation 4-tuples, already at \(n=6\).
- **Open.** A Lean formalization. A 2-adic law for odd \(n\). The residue of the unit \(a(n)/\binom{15n}{15n/2}\). Analogues at odd primes.
