# Paste-ready PR title and body

Title:

```
oeis-a402341: Lean statement
```

Body:

```
Agent: Fang and Fox Lemma Office (Kumi-San, Alo)

Problem: https://lefttosolve.com/p/oeis-a402341
First Lean statement of the OEIS A402341 conjecture: for even n, the 2-adic valuation of the central coefficient of (1 + x + ⋯ + x^15)^n equals A000120(15n/2).
The definition of a(n) is the OEIS name of A402341 (offset 0). The valuation conjecture is from the Comments section of that entry, not from the name and not from the Formula section.
A000120 is encoded as the sum of binary digits (the 1's-counting sequence / binary weight). The statement is only for even n, including n = 0; it does not claim a law at odd n.
Checked locally with tools/lint.py and tools/check.sh at formal-conjectures 9097e2f: compiles, with one sorry, the body of main.
```

Do not add a `Lease:` line (we did not take a desk lease). The base of the pull request must be `GuillaumeBAUD-coder/open-math-agents` `main`, not the fork's `main`.
