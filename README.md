# probabilistic-combinatorics

Modular Lean 4 formalizations of the probabilistic method in combinatorics, built on mathlib.

The first-moment interface starts from a count of witnesses. To use it,
choose a natural-valued count `X`, prove `μ[X] ≤ δ`, and conclude

```text
P(X ≠ 0) ≤ δ,          P(X = 0) ≥ 1 - δ.
```

When `δ n → 0`, a generic theorem gives `P(X_n = 0) → 1`, allowing the sample
spaces and probability measures to vary with `n`. The development uses Mathlib's
expectation, measure, and integral APIs throughout.

## First-moment examples

| Example | Success event | Explicit failure bound |
| --- | --- | --- |
| [Gaussian maxima](ProbabilisticCombinatorics/Examples/GaussianMax.lean) | Every coordinate is at most `(1+ε) sqrt(2 log n)` | `n^(-(2ε+ε²))`, for `n ≥ 1`, `ε > 0` |
| [Balls in bins](ProbabilisticCombinatorics/Examples/BallsBins.lean) | Every bin is occupied after `m` independent uniform throws | `n^(-ε)` when `m ≥ (1+ε)n log n`, for `n ≥ 1`, `ε > 0` |
| [Random graph homogeneous sets](ProbabilisticCombinatorics/Examples/Ramsey/Asymptotics.lean) | `G(n,1/2)` has no clique or independent set of size `ceil(2 log₂ n)` | `4/n`, for `n ≥ 2` |
| [Bipartite expanders](ProbabilisticCombinatorics/Examples/Expanders/FirstMoment.lean) | On either side, `1 ≤ card(S)` and `8 card(S) ≤ n` imply `card(N(S)) > 2 card(S)` | `27/(28n)`, for `n ≥ 1` |

Each example proves convergence of the success probability to one. The Gaussian
example only assumes standard Gaussian marginals. The expander model uses eight
independent uniform perfect matchings between two vertex classes of size `n`;
its underlying simple graph has degree at most eight. Its expansion condition
is vacuous for `n < 8`.

## Second moments and alteration

| Application | Result |
| --- | --- |
| [Clique lower tail](ProbabilisticCombinatorics/Examples/CliqueLower.lean) | A fair random graph contains a clique of size $\lfloor(2-\varepsilon)\log_2 n\rfloor$ with probability tending to one for $0<\varepsilon\le 2$. |
| [Empty bins](ProbabilisticCombinatorics/Examples/EmptyBins.lean) | Below $(1-\varepsilon)n\log n$, the probability of complete occupancy is at most $e n^{-\varepsilon}$ for $n\ge 2$. |
| [Dominating sets](ProbabilisticCombinatorics/Examples/DominatingSet.lean) | A graph with $n$ vertices and minimum degree at least $d$ has a dominating set of size at most $n(1+\log(d+1))/(d+1)$. |

The [second-moment lemmas](ProbabilisticCombinatorics/Method/SecondMoment.lean) bound the
probability of a zero count and expand the variance of an indicator sum into ordered pairs.
Distinct empty bins have nonpositive covariance. For cliques, a pair sharing $r$ vertices
has joint probability equal to the product of its marginal probabilities times $2^{\binom r2}$.
An [intersection estimate](ProbabilisticCombinatorics/Estimates/IntersectionMoment.lean)
controls these contributions using the same sampling-without-replacement bound as the expander proof.

The [alteration lemma](ProbabilisticCombinatorics/Method/Alteration.lean) averages an integrable
upper bound on the cost of a deterministic repair. For domination, sample each vertex with
probability $p$ and add every vertex whose closed neighborhood was missed. This yields
the degree-sequence bound $np+\sum_v(1-p)^{1+\deg(v)}$ before choosing $p$.

## Use and organization

Import the complete development with:

```lean
module

public import ProbabilisticCombinatorics
```

Individual modules are also available for focused imports:

- [Method/FirstMoment](ProbabilisticCombinatorics/Method/FirstMoment): Markov-based
  count bounds, indicator sums, explicit error budgets, varying-space limit
  theorems, and the `first_moment using μ, X` tactic.
- [Probability/UniformPermutation.lean](ProbabilisticCombinatorics/Probability/UniformPermutation.lean):
  the uniform permutation law and exact fixed-set containment probabilities,
  including inverse permutations.
- [RandomGraph/HomogeneousProbability.lean](ProbabilisticCombinatorics/RandomGraph/HomogeneousProbability.lean):
  fixed-set clique and independent-set probabilities in the binomial random graph.
- [Estimates/ChooseRatio.lean](ProbabilisticCombinatorics/Estimates/ChooseRatio.lean):
  the binomial-ratio bound for sampling without replacement.
- [Examples](ProbabilisticCombinatorics/Examples): the four main applications,
  earlier biased-bit and clique examples, and checked tactic usage.

See the [first-moment guide](docs/FirstMoment.md) for the proof structure,
theorem names, mathematical estimates, and a complete file map.

## Build and verification

The repository pins Lean `v4.36.0-rc2` and Mathlib commit
`69552756cd8a2d2d48763cf7279fd814d6a1224d`. With Lean's `elan` installed, run:

```sh
lake exe cache get
lake build
```

The default build includes the library and [Audit.lean](Audit.lean), which checks
the axioms of 62 principal theorems. These proofs use only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or additional axioms.
The project builds with `autoImplicit = false`.

Copyright 2026 Sam McGuire. Released under the [Apache 2.0 license](LICENSE).
