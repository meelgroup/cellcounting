import Cellcounting.Analysis.ChoiceSum
import Cellcounting.Model.Prior

/-!
# The omission signature of `f_j` (`lem:binary-signatures`, `signatures.tex:201-262`)

`f_j` has the omission property on the full `p`-subset domain of the paired ground set
`[0, 2p)`, and keeps it after fixing elements included or excluded and summing any
disjoint labeled pairs at occupancy one (`lem:binary-contraction`).  In the form used
by `lem:transport`: fix `F` included, sum the pairs of `L` at occupancy one, exclude
everything else; the resulting weight on subsets of `D` of size `|D| - 2` has a
two-omission matrix `omitMat (fWeight I ε δ j) F D L` with at most one positive
eigenvalue (`Hyp`).

The paper derives it from the integer removal signature of `h_j`
(`cor:hj-signatures`, `integer-signatures.tex:325-400`) by grouping the displayed
elements by small-cell row/column coordinate (group-sum-zero vectors are
nonpositive and uncoupled; on group-constant vectors the factorial multiplicities
cancel), and closes it under pair summation by the cubic-tensor argument of
`lem:binary-contraction` (`signatures.tex:106-199`).
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **Omission signature of `f_j`, after fixing and pair summation**
(`lem:binary-signatures` with `lem:binary-contraction`): for `F`, `D` and the pairs of
`L` disjoint in `[0, 2p)` with `|F| + |D| + |L| = p + 2`, the two-omission matrix of
`U ↦ Σ_c f_j(F ∪ U ∪ c)` at `D` has at most one positive eigenvalue.
PAPER: sections/signatures.tex:201-210 -/
theorem fWeight_omission (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j ≤ HParam I ε δ)
    (F D : Finset ℕ) (L : List ℕ)
    (hF : ∀ e ∈ F, e < 2 * pSmall I ε δ) (hD : ∀ e ∈ D, e < 2 * pSmall I ε δ)
    (hL : ∀ t ∈ L, t < pSmall I ε δ) (hLnd : L.Nodup) (hFD : Disjoint F D)
    (hLF : ∀ t ∈ L, 2 * t ∉ F ∧ 2 * t + 1 ∉ F) (hLD : ∀ t ∈ L, 2 * t ∉ D ∧ 2 * t + 1 ∉ D)
    (hcard : F.card + D.card + L.length = pSmall I ε δ + 2) :
    Hyp (omitMat (fWeight I ε δ j) F D L) := by
  sorry

end Cellcounting.Analysis
