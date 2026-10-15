import Cellcounting.Analysis.BinChain

/-!
# Conductance of the bin walk (`lem:bin-conductance`)

`Cellcounting.Analysis.bin_conductance`: for `e ≥ 1`, every set `A` of bins with
`π_a(A) ≤ 1/2` has stationary flow `Σ_{v ∈ A, w ∉ A} π_a(v) P_a(v, w)` at least
`κ π_a(A)`, where `κ = 1/(10⁴ d² B)`.

This is `evaluation.tex:214-279`. The paper argues on the continuous log-concave
density `ϱ_a = 2^{-aD/H}` on `[0, B]^e`:
* the finite-box Prékopa–Leindler inequality (`lem:integral-interpolation`,
  `evaluation.tex:147-203`) gives expansion `μ(M \ S) ≥ (t/2) μ(S)` of the union `S`
  of open unit bins on the smaller side, where `M = (1-t)S + tD₀` and `t = 1/(4dB)`;
* `M \ S` is covered by radius-`1/(4d)` neighbourhoods of cut faces, each of mass at
  most `4 min{V_a(v), V_a(w)}`;
* `eq:bin-density-comparison` compares continuous and discrete side masses.
The ingredients from this project are `penalty_lipschitz` (`eq:scaled-penalty-bounds`)
and the dyadic comparison `V_a/4 ≤ ϱ_a ≤ 2V_a` on a unit bin. Mathlib and Arlib
have no Prékopa–Leindler or Brunn–Minkowski inequality.
-/

namespace Cellcounting.Analysis

open Pseudocode
open Arlib.Probability Arlib.MarkovChains
open Classical

/-- **Bin conductance** (`lem:bin-conductance`): for `e ≥ 1`, every cut of the bin
walk has stationary flow at least `κ = 1/(10⁴ d² B)` times its smaller side mass.
PAPER: sections/evaluation.tex:214-279 -/
theorem bin_conductance (I : Instance) (ε δ : ℚ) (hε : 0 < ε) (hε1 : ε < 1)
    (hfeas : feasible I) (x y : ℕ → ℕ)
    (hbox : ∀ s < nSmall I ε δ, x s ≤ smallB I ε δ s ∧ y s ≤ smallB I ε δ s)
    (a : ℕ) (ha : a ≤ HParam I ε δ) (he : nFree I ε δ ≠ 0)
    (hne : (binSet I ε δ).Nonempty) (A : Finset (binSet I ε δ))
    (hA : Pr (binDist I ε δ a x y hne) A ≤ 1 / 2) :
    1 / (10000 * (dParam I : ℝ) ^ 2 * BParam I ε δ) * Pr (binDist I ε δ a x y hne) A ≤
      cut (binDist I ε δ a x y hne) (binKernel I ε δ a x y) A := by
  sorry

end Cellcounting.Analysis
