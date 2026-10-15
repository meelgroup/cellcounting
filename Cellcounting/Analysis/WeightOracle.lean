import Cellcounting.Analysis.Contamination

/-!
# Accuracy of the weight oracle

`prop:weight-oracle` (`evaluation.tex:15-37`), accuracy clause, for the
pseudocode oracle `Pseudocode.oracle` (`ĥ_j(x, y) = M_f · ∏_{a<j} R̂_a · T̂`):
at a box-valid small profile `(x, y)` of total `p`, a level `j ≤ H`, and
`0 < ξ_in, θ < 1/4`, the output lies in `[(1 - ξ_in) h_j(x, y), (1 + ξ_in) h_j(x, y)]`
with probability at least `1 - θ`.  `h_j` is `hWeight` of `Contamination.lean`
(`eq:hj`).

The pseudocode's bin intervals, cube point, ratio samples, correction exponent
`β = ⌊jD(v)/H⌋ - jD(z)/H` and walk length `ℓ_in` were compared with
`evaluation.tex:40-125` and `evaluation.tex:327-400` and agree with them.

The paper's proof (`evaluation.tex:40-482`) is the telescoping identity
`eq:oracle-telescope`, Chebyshev over the `j + 1` ideal averages, the
conductance bound for the bin walk (via the Prékopa–Leindler interpolation of
`lem:integral-interpolation`) giving `eq:bin-mixing`, the dyadic offset draws
(`lem:dyadic-integer-draw`), and the error of the bisection for `2^β`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **Weight evaluation, accuracy** (`prop:weight-oracle`): with probability at
least `1 - θ` the oracle is within relative error `ξ_in` of `h_j(x, y)`.
PAPER: sections/evaluation.tex:15-37 -/
theorem weight_oracle_accurate (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
    (htot : ∑ s ∈ Finset.range (nSmall I ε δ), (x s + y s) = pSmall I ε δ)
    (j : ℕ) (hj : j ≤ HParam I ε δ) (ξin θ : ℚ) (hξ : 0 < ξin) (hξ1 : ξin < 1 / 4)
    (hθ : 0 < θ) (hθ1 : θ < 1 / 4) :
    ENNReal.ofReal (1 - (θ : ℝ)) ≤ (oracle I ε δ x y j ξin θ).toOuterMeasure
      {h | (1 - (ξin : ℝ)) * hWeight I ε δ j x y ≤ (h : ℝ) ∧
        (h : ℝ) ≤ (1 + (ξin : ℝ)) * hWeight I ε δ j x y} := by
  sorry

end Cellcounting.Analysis
