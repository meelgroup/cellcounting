import Cellcounting.Analysis.TransportDirichlet
import Cellcounting.Model.Prior

/-!
# Variance on transversals (`prop:transversal-variance`, `transport.tex:318-428`)

For good multipliers and every real `g` on `X`, `C(j) Var_μ(g) ≤ C_p 𝔇(g)`, with
`μ = f_j / C(j)` on transversals and `C_p = p (1 + 8 p q²)` (`CpParam`).  The paper
proves it by a conditioning tree over partial assignments, choosing a sink pair at
each node (`eq:sink-products`, from `lem:defect-inequalities`), and charging each
between-means term to the one-hole transport inequality `lem:transport`
(`eq:slot-transport`) with the lift comparison `eq:lift-comparison`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **Transversal variance** (`prop:transversal-variance`): for good multipliers,
`C Var_μ(g) ≤ C_p 𝔇(g)` for every real `g` on `X`.
PAPER: sections/transport.tex:330-337 -/
theorem transversal_variance (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) :
    Cpart I ε δ j * refMuVar I ε δ j g ≤ (CpParam I ε δ : ℝ) * refDir I ε δ j w g := by
  sorry

end Cellcounting.Analysis
