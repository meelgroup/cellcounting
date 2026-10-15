import Cellcounting.Analysis.ChoiceSum
import Cellcounting.Analysis.TransMassEqCpart
import Cellcounting.Model.Prior

/-!
# Comparison of the two lifts (`eq:lift-comparison`, `signatures.tex:62-78`)

`f_j` and `f̃_j` agree on transversals (`lift_trans_eq`: in every cell `x_s + y_s = b_s`,
so both factorial multipliers are `1/binom(b_s, x_s)`), and on a defect class `A_il`
they are within the factor `q = W²` of each other (`lift_defect_le`): if the empty and
the full pair lie in one cell the ratio is one; otherwise one cell contributes
`(x_s + 1)(y_s + 1)` and another `1/(x_s y_s)` to `f̃/f`, both integer products between
one and `W²` because the small bounds are less than `W`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **The lifts agree on transversals** (`signatures.tex:36-52`).
PAPER: sections/signatures.tex:41-46 -/
theorem lift_trans_eq (I : Instance) (ε δ : ℚ) (j : ℕ) (S : Finset ℕ)
    (hS : kind I ε δ S = .transversal) : fTilde I ε δ j S = fWeight I ε δ j S := by
  rw [kind_eq_transversal_iff] at hS
  have hbal : ∀ s, (profile I ε δ S).1 s + (profile I ε δ S).2 s = smallB I ε δ s := by
    intro s
    rw [smallB_eq_card]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.range (pSmall I ε δ)).filter fun i => pairCell I ε δ i = s)
      (fun i => 2 * i ∈ S)
    rw [Finset.filter_filter, Finset.filter_filter] at hsplit
    rw [← hsplit]
    unfold profile
    simp only
    congr 2
    apply Finset.filter_congr
    intro i hi
    rw [hS i (Finset.mem_range.1 hi), not_not]
  unfold fTilde fWeight
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  have h := hbal s
  rw [show smallB I ε δ s - (profile I ε δ S).1 s = (profile I ε δ S).2 s by omega,
    show smallB I ε δ s - (profile I ε δ S).2 s = (profile I ε δ S).1 s by omega]
  ring

/-- **Lift comparison on defect states** (`eq:lift-comparison`):
`q⁻¹ f ≤ f̃ ≤ q f` on `A_il`, stated as `f ≤ q f̃` and `f̃ ≤ q f`.
PAPER: sections/signatures.tex:62-78 -/
theorem lift_defect_le (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (S : Finset ℕ) (i l : ℕ)
    (hS : kind I ε δ S = .defect i l) :
    fWeight I ε δ j S ≤ (qParam I ε δ : ℝ) * fTilde I ε δ j S ∧
      fTilde I ε δ j S ≤ (qParam I ε δ : ℝ) * fWeight I ε δ j S := by
  sorry

end Cellcounting.Analysis
