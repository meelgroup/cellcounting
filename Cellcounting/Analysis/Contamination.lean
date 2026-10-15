import Cellcounting.Interface.Pseudocode
import Cellcounting.Model.Prior
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The partition functions `h_j`, `C(j)` and the contamination bound

`eq:hj` and `eq:Cj` (`scales.tex:265-282`) over the pseudocode's tightened data:

* `freeBox` is `∏_{e ∈ F} {0, …, b_e}`, as functions on `Fin (nFree I ε δ)`;
* `hWeight I ε δ j x y = Σ_{z ∈ freeBox} 2^{-j D(x, y, z) / H}`, with `D` the
  pseudocode's `penalty` (whose small-cell convention R1, row `x_s` and column
  `b_s - y_s`, is the paper's own, `scales.tex:101-108`);
* `Cpart I ε δ j = Σ h_j(x, y)` over the balanced profiles `x_s + y_s = b_s`,
  parametrised by `x ∈ ∏_s {0, …, b_s}` with `y_s = b_s - x_s`.

`contamination` is `prop:contamination` (`scales.tex:282-287`, proved in
`integer-signatures.tex:485-549`): `Z ≤ C(H) ≤ (1 + ε/32) Z`.  It is used by
the single-run bounds for both `p ≥ 1` (`annealRun_good`) and `p = 0`.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- INTERNAL: the free box `∏_{e ∈ F} {0, …, b_e}` of `eq:hj`, indexed by the
free-cell positions of `forest`.
TEXLINE: sections/scales.tex:265-270 -/
noncomputable def freeBox (I : Instance) (ε δ : ℚ) : Finset (Fin (nFree I ε δ) → ℕ) :=
  Fintype.piFinset fun k => Finset.range ((freeAt I ε δ k).2.2 + 1)

/-- INTERNAL: a vector on `Fin N`, read as the `ℕ → ℚ` the penalty takes
(zero past `N`, a position the penalty never reads). -/
def extendQ {N : ℕ} (z : Fin N → ℕ) : ℕ → ℚ := fun k => if h : k < N then (z ⟨k, h⟩ : ℚ) else 0

/-- INTERNAL: a vector on `Fin N`, read as an `ℕ → ℕ` (zero past `N`). -/
def extendN {N : ℕ} (x : Fin N → ℕ) : ℕ → ℕ := fun k => if h : k < N then x ⟨k, h⟩ else 0

/-- **`h_j(x, y)`** (`eq:hj`): `Σ_{z ∈ ∏_e {0..b_e}} 2^{-j D(x, y, z)/H}`.
PAPER: sections/scales.tex:265-270 -/
noncomputable def hWeight (I : Instance) (ε δ : ℚ) (j : ℕ) (x y : ℕ → ℕ) : ℝ :=
  ∑ z ∈ freeBox I ε δ,
    (2 : ℝ) ^ (-((j : ℝ) * (penalty I ε δ x y (extendQ z) : ℝ) / (HParam I ε δ : ℝ)))

/-- INTERNAL: the balanced small profiles, parametrised by `x ∈ ∏_s {0..b_s}`
(`y_s = b_s - x_s`).
TEXLINE: sections/scales.tex:279-282 -/
noncomputable def smallBox (I : Instance) (ε δ : ℚ) : Finset (Fin (nSmall I ε δ) → ℕ) :=
  Fintype.piFinset fun s => Finset.range (smallB I ε δ s + 1)

/-- **`C(j)`** (`eq:Cj`): `Σ h_j(x, y)` over balanced profiles `x_s + y_s = b_s`.
PAPER: sections/scales.tex:279-282 -/
noncomputable def Cpart (I : Instance) (ε δ : ℚ) (j : ℕ) : ℝ :=
  ∑ x ∈ smallBox I ε δ,
    hWeight I ε δ j (extendN x) (fun s => smallB I ε δ s - extendN x s)

/-- **Contamination bound** (`prop:contamination`): for the feasible tightened
instance, `Z ≤ C(H) ≤ (1 + ε/32) Z`.
PAPER: sections/scales.tex:282-287 -/
theorem contamination (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) :
    (I.Z : ℝ) ≤ Cpart I ε δ (HParam I ε δ) ∧
      Cpart I ε δ (HParam I ε δ) ≤ (1 + (ε : ℝ) / 32) * (I.Z : ℝ) := by
  sorry

end Cellcounting.Analysis
