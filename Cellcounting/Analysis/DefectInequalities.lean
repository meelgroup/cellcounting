import Cellcounting.Analysis.ChoiceSum
import Cellcounting.Model.Prior

/-!
# Pair inequalities for defect masses (`lem:defect-inequalities`, `signatures.tex:303-410`)

For a partial transversal assignment `σ` with unassigned pairs `T` and the second
lift `f̃_j`:

* `defect_two_pair` (`eq:defect-two-pair`): `4 c̃^σ_il c̃^σ_li ≤ z_σ²`;
* `defect_three_pair` (`eq:defect-three-pair`): `c̃^σ_il c̃^σ_lk ≤ z_σ c̃^σ_ik`.

Here `z_σ = trMass f̃ σ T` and `c̃^σ_il = defMass f̃ σ T i l`.  The paper proves both
from the addition property of `f̃_j` (`lem:binary-signatures`, from the addition half
of `cor:hj-signatures`), summing every other unassigned pair at occupancy one; the
three-pair inequality uses the full-matrix (cubic contraction) assertion of
`lem:binary-contraction` and a Schur complement against the `l, l` entry.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **Two-pair defect inequality** (`eq:defect-two-pair`): `4 c̃^σ_il c̃^σ_li ≤ z_σ²`.
PAPER: sections/signatures.tex:328-336 -/
theorem defect_two_pair (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (σ : Finset ℕ) (T : List ℕ) (hv : AsgValid (pSmall I ε δ) σ T)
    (i l : ℕ) (hi : i ∈ T) (hl : l ∈ T) (hil : i ≠ l) :
    4 * defMass (fTilde I ε δ j) σ T i l * defMass (fTilde I ε δ j) σ T l i ≤
      trMass (fTilde I ε δ j) σ T ^ 2 := by
  sorry

/-- **Three-pair defect inequality** (`eq:defect-three-pair`):
`c̃^σ_il c̃^σ_lk ≤ z_σ c̃^σ_ik` for distinct unassigned `i, l, k`.
PAPER: sections/signatures.tex:337-342 -/
theorem defect_three_pair (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (σ : Finset ℕ) (T : List ℕ) (hv : AsgValid (pSmall I ε δ) σ T)
    (i l k : ℕ) (hi : i ∈ T) (hl : l ∈ T) (hk : k ∈ T) (hil : i ≠ l) (hlk : l ≠ k)
    (hik : i ≠ k) :
    defMass (fTilde I ε δ j) σ T i l * defMass (fTilde I ε δ j) σ T l k ≤
      trMass (fTilde I ε δ j) σ T * defMass (fTilde I ε δ j) σ T i k := by
  sorry

end Cellcounting.Analysis
