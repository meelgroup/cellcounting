import Cellcounting.Analysis.Contamination
import Cellcounting.Analysis.HyperbolicForm

/-!
# The addition signature of `h_j` (`cor:hj-signatures`, addition half)

`integer-signatures.tex:325-400`.  Each small cell `s` contributes two count
coordinates, `(s, false)` for its row view `x_s` and `(s, true)` for its column view
`y_s`.  At every box-valid display `r` (`0 ≤ r_u ≤ b_s`) of total `p - 2`, the
two-addition matrix `(h_j(r + e_u + e_v))_{u, v}`, with zero entries for invalid
additions (`r_u + 1 > b_s`, or `u = v` and `r_u + 2 > b_s`), has at most one positive
eigenvalue (`Hyp`).

Intended route (the paper's, `integer-signatures.tex:394-396`): the same softened
laminar table model as for the removal half (`hWeight_removal_hyp`), with every
coordinate reflected — including the large ones that are summed at balance — so that
two-addition matrices of `h_j` become two-removal matrices of the reflected model;
then `Lemma integer-signature` and the `α ↓ 0` limit.  `h_j` itself is *not*
reflection-symmetric (a small cell loads its row with `x_s` and its column with
`b_s - y_s`), so the addition half does not follow from the removal half by a
substitution in `h_j`; the reflection has to happen inside the model.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: the display `r + e_u + e_v`.
TEXLINE: sections/integer-signatures.tex:325-332 -/
def addDisp {N : ℕ} (r : Fin N × Bool → ℕ) (u v : Fin N × Bool) : Fin N × Bool → ℕ :=
  fun w => r w + (if w = u then 1 else 0) + (if w = v then 1 else 0)

/-- **Addition signature of `h_j`** (`cor:hj-signatures`, second assertion): at every
box-valid display `r` of total `p - 2` on the row/column views of the small cells, the
two-addition matrix of `h_j`, with zero entries for invalid additions, has at most one
positive eigenvalue.  `(s, false)` is the row view `x_s`, `(s, true)` the column view
`y_s`.
PAPER: sections/integer-signatures.tex:325-332 -/
theorem hWeight_addition_hyp (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (r : Fin (nSmall I ε δ) × Bool → ℕ) (hbox : ∀ w, r w ≤ smallB I ε δ w.1)
    (htot : ∑ w, r w + 2 = pSmall I ε δ) :
    Hyp (fun u v : Fin (nSmall I ε δ) × Bool =>
      if r u + 1 ≤ smallB I ε δ u.1 ∧ r v + 1 ≤ smallB I ε δ v.1 ∧
          (u = v → r u + 2 ≤ smallB I ε δ u.1) then
        hWeight I ε δ j (extendN fun s => addDisp r u v (s, false))
          (extendN fun s => addDisp r u v (s, true))
      else 0) := by
  sorry

end Cellcounting.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · handoff rejected twice (`fta-hwadd-1`, `fta-hwadd-2`: no admission receipt); still open
* r1 · stated · child of `fTilde_addition` (via `fTilde_base_addSig`); substitution
  `x ↦ b - y` in `h_j` does not reduce it to `hWeight_removal_hyp` (`baseLoad` is not
  reflection-symmetric)
-/
