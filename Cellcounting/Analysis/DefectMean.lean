import Cellcounting.Analysis.TransportDirichlet
import Cellcounting.Model.Prior

/-!
# Defect means (`lem:defect-mean`, `transport.tex:440-506`)

For good multipliers, every real `g` on `X` and every defect type `il`, some
conditional transversal mean `g'` (the `μ`-mean of `g` on a joint choice in pairs
`i, l` of transversal mass at least `C/4`) satisfies
`(ḡ_il - g')² ≤ (C_d / C) 𝔇(g)` and `(g' - E_μ g)² ≤ 4 Var_μ(g)`, with
`C_d = 8 + 32 p q³` (`CdParam`).  The paper proves the first bound from the one-hole
transport inequality `lem:transport` with singleton slots `{a_i}`, `{b_l'}`, the
lift comparison and `lem:defect-inequalities` (`eq:defect-comparison`); the second
is conditional Cauchy–Schwarz on an event of `μ`-probability at least `1/4`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **Defect means** (`lem:defect-mean`): for good multipliers and each defect type
`il`, a conditional transversal mean `g'` satisfies
`(ḡ_il - g')² ≤ (C_d / C) 𝔇(g)` and `(g' - E_μ g)² ≤ 4 Var_μ(g)`.
PAPER: sections/transport.tex:440-452 -/
theorem defect_mean (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ)
    (i l : ℕ) (hi : i < pSmall I ε δ) (hl : l < pSmall I ε δ) (hil : i ≠ l) :
    ∃ g' : ℝ, (refDefMean I ε δ j i l g - g') ^ 2 ≤
        (CdParam I ε δ : ℝ) / Cpart I ε δ j * refDir I ε δ j w g ∧
      (g' - refMuMean I ε δ j g) ^ 2 ≤ 4 * refMuVar I ε δ j g := by
  sorry

end Cellcounting.Analysis
