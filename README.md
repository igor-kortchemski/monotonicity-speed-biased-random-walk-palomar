# The speed of biased random walk on leafless Bienaymé trees is monotone

[![Lean build](https://github.com/igor-kortchemski/monotonicity-speed-biased-random-walk-palomar/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/monotonicity-speed-biased-random-walk-palomar/actions/workflows/lean.yml?query=branch%3Amain)
[![Comparator](https://github.com/igor-kortchemski/monotonicity-speed-biased-random-walk-palomar/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/igor-kortchemski/monotonicity-speed-biased-random-walk-palomar/actions/workflows/comparator.yml?query=branch%3Amain)

Lean 4 and Mathlib formalization of Theorem 1.1 of *The speed of biased random
walk on leafless Bienaymé trees is monotone* by ChatGPT, directed by Igor
Kortchemski ([Hexagon 2611.00820](https://hexagonmath.org/2611.00820v1), November
2026), **assuming the two interval verifications of its Appendix A**.
**`LPPMonotonicity.speed_monotone_of_interval_certificates` proves Theorem 1.1 from the two
closed propositions that the interval verifications of Lemmas A.1 and A.2 check,
using only the axioms `propext`, `Classical.choice` and `Quot.sound`.** The two
propositions are proved outside this repository (see
[below](#the-two-interval-verifications)).

Statement: [`Challenge.lean`](Challenge.lean) ·
model: [`LPPMonotonicity/Model/Defs.lean`](LPPMonotonicity/Model/Defs.lean) ·
interval verifications: section `AppendixA` of [`LPPMonotonicity/Model/Defs.lean`](LPPMonotonicity/Model/Defs.lean)

## Main result

Let $\nu$ be an offspring law with $\mathbb P(\nu = 0) = 0$ and
$1 < m = \mathbb E[\nu] < \infty$, and let $v(\lambda)$ be the speed of the
$\lambda$-biased random walk on the Bienaymé tree with offspring law $\nu$.
Then $v$ is $C^1$ on $[0, m)$, positive and strictly decreasing there, with
$v'(\lambda) < 0$ for $0 < \lambda < m$ and right derivative
$v'_+(0) = -2\,\mathbb E[1/\nu]$.

| Paper | Lean | Role |
| --- | --- | --- |
| Theorem 1.1, assuming the interval verifications of Appendix A | [`LPPMonotonicity.speed_monotone_of_interval_certificates`](LPPMonotonicity/Statements/Conditional.lean) | proved here |
| Interval verification of Lemma A.1 | [`CertACovers`](LPPMonotonicity/Model/Defs.lean) | hypothesis: the retained lower bound of the first split is positive for all normalized data in its domain |
| Interval verification of Lemma A.2 | [`CertBCovers`](LPPMonotonicity/Model/Defs.lean) | hypothesis: every feasible box of Section 5 passes one of the four tests that give $v'(\lambda) < 0$ |

The speed is constructed from the model (the Bienaymé tree law and the law of
the walk), not postulated: for every $\lambda \in [0, m)$ it is the
almost-sure limit of $\lvert X_n\rvert / n$ for almost every tree. Everything
else in the proof is formalized here: the escape probabilities and the speed
formula, the analytic estimates of Sections 2 to 5, the derivation of Lemmas A.1
and A.2 from the two propositions, and the reduction of Theorem 1.1 to the two
lemmas. The proof of Theorem 3.7 uses an exact rational
check of twelve coefficients, done by the Lean kernel.

## The two interval verifications

Lemmas A.1 and A.2 give signs at the actual transient biases in two ranges. The
paper proves them by interval verifications over finite subdivisions of domains of
normalized data. The hypotheses here are the statements that these verifications
check, `CertACovers` and `CertBCovers`: they quantify over all feasible normalized
data, not only over the data of actual offspring laws, and the development derives
Lemmas A.1 and A.2 from them at the actual law.

Both propositions are proved, and Theorem 1.1 with them, in the companion
repository
[monotonicity-speed-biased-random-walk](https://github.com/igor-kortchemski/monotonicity-speed-biased-random-walk),
where the Lean kernel checks both computations in exact arithmetic, in about 620
CPU-hours: 41,919 boxes for Lemma A.1, and 8,185 rectangles with 2,089,525
numerical, 12,634 analytic and 3,532 excluded leaves for Lemma A.2. The paper's
programs, in that repository's `ancillary/` folder, verify them in outward-rounded
floating-point arithmetic. This repository is an
extract of that development (commit `c561a03`), without the certificate
modules and with the development's namespace renamed from
`LPPMonotonicityDraft` to `LPPMonotonicityProof`. The definitions behind
`CertACovers` and `CertBCovers` are the same, apart from that namespace and the
name of one automatically generated proof (of `IsScalarTower ℝ≥0∞ ℝ≥0∞ ℝ≥0∞`);
here they sit next to the model, so that `Challenge.lean` restates them
identically.

## Where to start

- [`Challenge.lean`](Challenge.lean): the statement with every definition it
  uses, importing only Mathlib.
- [`LPPMonotonicity/Model/Defs.lean`](LPPMonotonicity/Model/Defs.lean): the
  tree law `treeLaw`, the walk law `walkLaw`, `offspringMean`, `inverseMean`
  and `height` (section `Model`).
- Section `AppendixA` of [`LPPMonotonicity/Model/Defs.lean`](LPPMonotonicity/Model/Defs.lean):
  the propositions `CertACovers` and `CertBCovers` behind Lemmas A.1 and A.2,
  documented in [`Analytic/Certificates.lean`](LPPMonotonicityProof/Analytic/Certificates.lean).
- [`LPPMonotonicityProof/AssemblyFinal.lean`](LPPMonotonicityProof/AssemblyFinal.lean):
  Theorem 1.1 from the two propositions.

## Verify

Install Lean with [elan](https://leanprover-community.github.io/install/project.html), then:

```bash
git clone https://github.com/igor-kortchemski/monotonicity-speed-biased-random-walk-palomar.git
cd monotonicity-speed-biased-random-walk-palomar
lake exe cache get
lake build
lake env lean scripts/Axioms.lean
```

`lake comparator` (on Linux, with Bubblewrap) checks that `Solution.lean` proves
exactly the statement of `Challenge.lean`, with the permitted axioms, and
replays the proof in Lean's kernel and in NanoDa. The CI runs the build, the
axiom check and Comparator on every push.

## How it was made

The formalization was produced by AI agents coordinated in Claude Code
(Claude Opus 5.5 and Claude Sonnet 5.5), with Kimi K3.1 Pro through Open Math
OS and GPT models (gpt-6.2-sol, gpt-6.2-astra, gpt-6-luna) through Codex. The
statement of Theorem 1.1 was reviewed against the paper before the proof
work. The Lean kernel checks the proofs; no human line-by-line review of the
proofs is claimed.

## License and citation

The Lean code is released under the [Apache-2.0](LICENSE) license, which does
not cover the paper. Some modules are copied from
[random-trees-lean](https://github.com/igor-kortchemski/random-trees-lean)
(Apache-2.0); see [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md). To cite the
mathematics, cite the paper; [`CITATION.cff`](CITATION.cff) also describes
this formalization. Questions and corrections are welcome as GitHub issues.
