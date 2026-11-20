# First moment: explicit error bounds and high probability

A detailed guide to the repository's quantitative first-moment interface and examples.

Return to the [repository overview](../README.md).

The four main examples are Gaussian maxima, coupon collection, cliques /
independent sets in a fair random graph, and bounded-degree bipartite expanders.

## The quantitative interface

Choose `X : Ω → ℕ`, prove `μ[X] ≤ δ`, and conclude

```text
P(X ≠ 0) ≤ δ,          P(X = 0) ≥ 1 - δ.
```

Keep the explicit error budget. When `δ n → 0`, the second inequality gives
`P(X_n = 0) → 1`. The generic theorem allows the sample spaces, measures, and
counts all to depend on `n`. Probability and integrability assumptions only
need to hold eventually, so boundary cases such as zero bins stay out of the
asymptotic argument.

The notation `μ[X]` is Mathlib's real expectation, and `μ.real E` is real-valued
probability. Counts take values in `ℕ`, so a nonzero count is at least one.
The core applies Mathlib's Markov inequality at threshold one. Indicator sums
use its existing linearity theorem and expectation-of-an-indicator theorem.

## The four examples

The first two examples allow any fixed `ε > 0`.
Natural logarithms are used in the first two rows; graph logarithms have base 2.

| Example | Count | Finite error budget | Specialized budget |
| --- | --- | --- | --- |
| Standard Gaussian marginals | Coordinates exceeding `t` | `n * exp(-t²/2)` for `t ≥ 0` | `n^(-(2ε+ε²))` at `t = (1+ε) sqrt(2 log n)` |
| Independent uniform balls in bins | Empty bins | `n * (1-1/n)^m ≤ n * exp(-m/n)` | `n^(-ε)` if `m ≥ (1+ε)n log n` |
| `G(n,1/2)` | `k`-cliques plus independent `k`-sets | `2 * choose(n,k) * 2^(-choose(k,2))` | `4/n` at `k = ceil(2 log₂ n)` |
| Eight uniform perfect matchings | Bad expansion certificates on either side | `2 * ∑_{s=1}^{floor(n/8)} choose(n,s) choose(n,2s) (2s/n)^(8s)` | `27/(28n)` for `n ≥ 1` |

All four examples prove actual probability limits, as well as explicit finite bounds.
The specialized budgets tend to zero, and the success probabilities tend to one.

### 1. Gaussian maximum

[ProbabilisticCombinatorics/Examples/GaussianMax.lean](../ProbabilisticCombinatorics/Examples/GaussianMax.lean), namespace `ProbabilisticCombinatorics.GaussianMax`.

- `exceedanceCount G t` is the natural count of coordinates strictly above `t`.
- `standardGaussian_tail_le` proves `P(G > t) ≤ exp(-t²/2)` from Mathlib's
  Gaussian moment-generating function and Chernoff inequality.
- `expectation_exceedanceCount_le` sums those tail bounds.
- `all_le_probability_lower_bound` applies the quantitative first-moment theorem.
- `threshold_error_eq` performs the exact real arithmetic for the chosen cutoff.
- `threshold_probability_lower_bound` gives success probability at least
  `1 - n^(-(2ε+ε²))` for `n ≥ 1` and `ε > 0`.
- `threshold_whp` proves convergence to one on a family of probability spaces.

The coordinates are specified by `HasLaw (G i) (gaussianReal 0 1) μ`.
No independence hypothesis is used. The maximum event is written
`∀ i : Fin n, G i ω ≤ t`, avoiding a convention for the maximum of an empty set.
`HasLaw` supplies almost-everywhere measurability; the indicator calculation
uses the corresponding null-measurable versions of Mathlib's integral lemmas.

### 2. Coupon collection

[ProbabilisticCombinatorics/Examples/BallsBins.lean](../ProbabilisticCombinatorics/Examples/BallsBins.lean), namespace `ProbabilisticCombinatorics.Examples.BallsBins`.

`allocationMeasure n m` is the actual product of uniform laws on `Fin n`, on
assignments `Fin m → Fin n`. Thus different balls choose their bins independently.
`emptyCount` counts bins with no preimage, and `emptyCount_eq_zero` identifies
count zero with a surjective allocation.

The file proves, in order:

```text
P(a fixed bin is empty) = (1-1/n)^m
E[emptyCount] = n * (1-1/n)^m
P(some bin is empty) ≤ n * exp(-m/n)
P(every bin is occupied) ≥ 1 - n^(-ε), if m ≥ (1+ε)n log n.
```

`coupon_collection_whp ε hε m hm` permits any `m : ℕ → ℕ` satisfying the cutoff
eventually. `coupon_collection_ceil_whp` supplies the fully concrete sequence
`m n = ⌈(1+ε)n log n⌉₊`.

The individual empty-bin events need not be independent. Linearity adds their
probabilities; independence of the balls is used only in the fixed-bin calculation.

### 3. Random graph homogeneous sets

[ProbabilisticCombinatorics/Examples/Ramsey/Asymptotics.lean](../ProbabilisticCombinatorics/Examples/Ramsey/Asymptotics.lean), namespace `ProbabilisticCombinatorics.Examples.Ramsey`.

The underlying graph law and count are from [ProbabilisticCombinatorics/Examples/Ramsey/Basic.lean](../ProbabilisticCombinatorics/Examples/Ramsey/Basic.lean). The new
file proves the arithmetic estimate

```text
n > 0, k > 0, n² ≤ 2^k
    ⇒ 2 * choose(n,k) * (1/2)^choose(k,2) ≤ 4/n.
```

The factorial in `choose(n,k) ≤ n^k/k!` is sufficient. For `k ≥ 1`, the elementary
bound `k! ≥ 2^(k-1)` gives

```text
2 * choose(n,k) * 2^(-choose(k,2))
    ≤ 2^(1+k/2) / k!
    ≤ 2^(2-k/2)
    ≤ 4/n.
```

The formal arithmetic uses natural powers and squares. It does not need Stirling's
formula. The threshold is implemented as `Nat.clog 2 (n*n)`, and
`logarithmicThreshold_eq` proves that this is exactly `⌈2 * Real.logb 2 n⌉₊`.

For `n ≥ 2`, `logarithmic_failure_probability_le` gives error at most `4/n`, and
`logarithmic_success_probability_ge` gives success at least `1 - 4/n`.
`logarithmic_success_probability_tendsto_one` states the WHP result with the literal
real-logarithm threshold. It rules out cliques and independent sets of that size
and hence every larger size. When `2 log₂ n` is an integer, it also rules out that
exact size, so the result is slightly stronger than forbidding only larger sizes.
No extra epsilon is needed for this example.

### 4. Bounded-degree bipartite expanders

[ProbabilisticCombinatorics/Examples/Expanders/FirstMoment.lean](../ProbabilisticCombinatorics/Examples/Expanders/FirstMoment.lean), namespace `ProbabilisticCombinatorics.Expanders`.

`Matchings n := Fin 8 → Equiv.Perm (Fin n)` presents eight perfect matchings
between two copies of `Fin n`. `matchingMeasure n` is the actual product of
eight uniform permutation laws. The underlying simple graph `graph π` has
vertex set `Fin n ⊕ Fin n`, no edges within a vertex class, and degree at most
eight at every vertex. Counting matching edges with multiplicity gives degree
exactly eight on both sides; distinct-neighbor degrees can be smaller.

The expansion property is explicitly:

```text
For either side and every S, 1 ≤ |S| and 8|S| ≤ n imply |N(S)| > 2|S|.
```

This is two-sided small-set vertex expansion. The implemented statement concerns
sets up to `n/8` on a side; it does not assert a spectral bound or a half-volume
expansion condition. When `n < 8`, the stated expansion condition is vacuous.

A certificate is `(side, S, T)` with `|S| = s`, `|T| = 2s`, and
`N(S) ⊆ T`. The ordinary natural count `badCount n` sums its indicators over
all admissible sizes and certificates. `badCount_eq_zero_iff_expands` proves
that count zero is exactly the desired graph property. The converse direction
extends a deficient neighborhood to a set of size exactly `2s`.

The reusable uniform-permutation calculation proves

```text
P(π(S) ⊆ T) = choose(|T|,|S|) / choose(n,|S|)
             ≤ (|T|/n)^|S|, for n > 0.
```

The exact formula and bound also hold for inverse permutations. This handles
the opposite side without changing the model. Product measure gives the
eighth power for a fixed certificate; linearity of expectation adds the
`2 * choose(n,s) * choose(n,2s)` certificates of each size. Independence is used
only among the eight matching choices, not among certificates.

The numerical estimate uses `choose(n,k) ≤ (3n/k)^k`, followed by the geometric
majorant, valid for `1 ≤ s ≤ n/8`:

```text
choose(n,s) choose(n,2s) (2s/n)^(8s)
    ≤ [1728 (s/n)^5]^s
    ≤ (27/(64n)) (1/8)^(s-1).
```

Summing the geometric series and counting both sides gives `27/(28n)`.
The public results include:

- `expected_badCount_le`: `E[badCount n] ≤ 27/(28n)` for `n > 0`.
- `expansion_failure_probability_le`: failure probability at most `27/(28n)`.
- `expansion_success_probability_ge`: success probability at least `1 - 27/(28n)`.
- `exists_expanding_matchings`: existence for every natural `n`.
- `exists_bipartite_expander`: an actual `SimpleGraph` with the degree,
  bipartition, and two-sided expansion properties.
- `expansion_whp`: the success probability tends to one.

The last probability and limit steps apply the same first-moment interface as
the other examples. The permutation law, graph correspondence, and elementary
numeric estimates are separate reusable modules.

## Tactic usage

Import `ProbabilisticCombinatorics.Method.FirstMoment.Asymptotics` to use the quantitative forms of the existing tactic:

```lean
module

public import ProbabilisticCombinatorics.Method.FirstMoment.Asymptotics

open MeasureTheory
open scoped ProbabilityTheory

example {Ω : Type*} [MeasurableSpace Ω] [Finite Ω]
    [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℕ) (δ : ℝ) (hEX : (μ[X] : ℝ) ≤ δ) :
    1 - δ ≤ μ.real {ω | X ω = 0} := by
  first_moment using μ, X
  exact hEX
```

It also accepts a goal `μ.real {ω | X ω ≠ 0} ≤ δ` and the original existence goal
`∃ ω, X ω = 0`. Integrability is attempted using a local hypothesis or
`Integrable.of_finite`. If those fail, integrability remains a visible goal.
The tactic leaves the expectation estimate to the user; the model-specific
probability and numerical estimates are ordinary named lemmas.

For limits, the main theorem in `ProbabilisticCombinatorics.FirstMoment` is:

```text
tendsto_measure_zero_of_expectation_le μ X δ hprob hInt hEX hδ
```

Here `hprob`, `hInt`, and `hEX` are eventual hypotheses, and `hδ` proves
`Tendsto δ l (𝓝 0)`. Its conclusion is

```lean
Tendsto (fun n ↦ (μ n).real {ω | X n ω = 0}) l (𝓝 1)
```

No custom WHP record or custom expectation definition is introduced.

## Files and reading order

| File | Role |
| --- | --- |
| [ProbabilisticCombinatorics/Method/FirstMoment/Basic.lean](../ProbabilisticCombinatorics/Method/FirstMoment/Basic.lean) | Markov-based core, original existence tactic, indicator-sum helpers. |
| [ProbabilisticCombinatorics/Method/FirstMoment/Asymptotics.lean](../ProbabilisticCombinatorics/Method/FirstMoment/Asymptotics.lean) | Explicit error budgets, varying-space limit theorem, quantitative tactic extension. |
| [ProbabilisticCombinatorics/Examples/FirstMomentUsage.lean](../ProbabilisticCombinatorics/Examples/FirstMomentUsage.lean) | Checked minimal uses of all three tactic goals. |
| [ProbabilisticCombinatorics/Examples/GaussianMax.lean](../ProbabilisticCombinatorics/Examples/GaussianMax.lean) | Gaussian maximum, exact rate, WHP. |
| [ProbabilisticCombinatorics/Examples/BallsBins.lean](../ProbabilisticCombinatorics/Examples/BallsBins.lean) | Actual uniform allocation model, coupon-collector rate, WHP. |
| [ProbabilisticCombinatorics/Examples/Ramsey/Asymptotics.lean](../ProbabilisticCombinatorics/Examples/Ramsey/Asymptotics.lean) | Exact logarithmic threshold, `4/n` estimate, WHP. |
| [ProbabilisticCombinatorics/Examples/Expanders/FirstMoment.lean](../ProbabilisticCombinatorics/Examples/Expanders/FirstMoment.lean) | Actual matching product law, certificate expectation, `27/(28n)` error, existence, WHP. |
| [ProbabilisticCombinatorics/Examples/Expanders/Model.lean](../ProbabilisticCombinatorics/Examples/Expanders/Model.lean) | Neighborhoods, certificates, and count zero iff expansion. |
| [ProbabilisticCombinatorics/Examples/Expanders/Graph.lean](../ProbabilisticCombinatorics/Examples/Expanders/Graph.lean) | Actual bipartite `SimpleGraph`, degree bound, neighborhood correspondence. |
| [ProbabilisticCombinatorics/Probability/UniformPermutation.lean](../ProbabilisticCombinatorics/Probability/UniformPermutation.lean) | Exact fixed-set containment probabilities for a uniform permutation and its inverse. |
| [ProbabilisticCombinatorics/Estimates/ChooseRatio.lean](../ProbabilisticCombinatorics/Estimates/ChooseRatio.lean) | Binomial-ratio bound for sampling without replacement. |
| [ProbabilisticCombinatorics/Examples/Expanders/Estimates.lean](../ProbabilisticCombinatorics/Examples/Expanders/Estimates.lean) | Binomial estimates and the geometric sum giving `27/(28n)`. |
| [ProbabilisticCombinatorics/Examples/Ramsey/Basic.lean](../ProbabilisticCombinatorics/Examples/Ramsey/Basic.lean) | Fair-graph count and exact expectation; earlier finite Ramsey application. |
| [ProbabilisticCombinatorics/RandomGraph/HomogeneousProbability.lean](../ProbabilisticCombinatorics/RandomGraph/HomogeneousProbability.lean) | Fixed-set clique and independent-set probabilities in the actual graph model. |
| [ProbabilisticCombinatorics/Examples/Clique.lean](../ProbabilisticCombinatorics/Examples/Clique.lean) | Earlier arbitrary-bias clique-count bound. |
| [ProbabilisticCombinatorics/Examples/BiasedBits.lean](../ProbabilisticCombinatorics/Examples/BiasedBits.lean) | Earlier biased-bit count and positive-threshold example. |
| [Audit.lean](../Audit.lean) | Axiom checks for the reusable core and all applications. |

## Reproduce

The build pins Lean `v4.36.0-rc2`, Mathlib commit
`69552756cd8a2d2d48763cf7279fd814d6a1224d`, and `autoImplicit = false`.
With Lean's `elan` installed, run:

```sh
lake exe cache get
lake build
```

The modules have been compiled against that environment. The default build
includes the library and the audit, which checks 47 principal probability,
expectation, numerical, and limit theorems. These proofs use only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or additional axioms.

## References

Mathlib's real Gaussian laws and exponential moments:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Distributions/Gaussian/Real.html

Mathlib's finite uniform laws:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/UniformOn.html

For the background on small-set bipartite vertex expansion and random matchings:
Salil Vadhan, *Pseudorandomness*, Chapter 4:
https://people.seas.harvard.edu/~salil/pseudorandomness/expanders.pdf

Mathlib's real-power asymptotics:
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.html

For the original finite Ramsey argument: Noga Alon and Joel H. Spencer,
*The Probabilistic Method*, fourth edition, Chapter 1, Proposition 1.1.1:
https://catalogimages.wiley.com/images/db/pdf/9781119061953.excerpt.pdf

Copyright 2026 Sam McGuire. Apache License 2.0; see [LICENSE](../LICENSE).
