import Cellcounting.Analysis.RefPhaseGood
import Cellcounting.Analysis.W0Good
import Cellcounting.Analysis.PmfClose

/-!
# The accuracy of the reference experiment (`prop:annealing`)

The reference experiment `refRun` itself is defined in
`Cellcounting.Analysis.RefExperiment`.

`reference_accuracy` is `prop:annealing` (`algorithm.tex:259-383`), in the form
`annealRun_good` uses: with probability at least `1 - 1/50` the reference run
does not abort and `|log(Z_ref / C(H))| ≤ 4 H η`.  The goodness of the stored
multipliers, also asserted by the paper, is internal to its induction and is
not part of this statement.

The induction: `refInv k` (no abort, `w^(0..k)` good, `∏ R̂` within `4kη` of
`C(k)/C(0)` in log) holds initially by `w0_good` (`W0Good.lean`) and
`C(0) = M_f ∏_s (b_s + 1)` (`Cpart_zero`); each phase preserves it except with
probability `1/[50(H+1)]` by `ref_phase_good` (`RefPhaseGood.lean`); a union
bound over the `H` phases leaves failure probability at most `H/[50(H+1)] ≤ 1/50`.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: a list product read through `getD`. -/
theorem prod_range_getD_eq {α : Type*} (l : List α) (g : α → ℕ) (d : α) :
    ∏ i ∈ Finset.range l.length, g (l.getD i d) = (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.prod_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    rw [ih, List.map_cons, List.prod_cons, mul_comm]

/-- INTERNAL: the free box has `M_f` points.
TEXLINE: sections/algorithm.tex:94-133 -/
theorem card_freeBox (I : Instance) (ε δ : ℚ) : (freeBox I ε δ).card = Mf I ε δ := by
  unfold freeBox
  rw [Fintype.card_piFinset]
  simp only [Finset.card_range]
  rw [Fin.prod_univ_eq_prod_range (fun k => (freeAt I ε δ k).2.2 + 1) (nFree I ε δ)]
  unfold nFree freeAt Mf
  exact prod_range_getD_eq _ (fun e => e.2.2 + 1) (0, 0, 0)

/-- INTERNAL: `C(0) = M_f ∏_s (b_s + 1)`: at parameter zero every term of `h_0` is one.
TEXLINE: sections/algorithm.tex:94-133 -/
theorem Cpart_zero (I : Instance) (ε δ : ℚ) : Cpart I ε δ 0 = (C0 I ε δ : ℝ) := by
  have hh : ∀ x y, hWeight I ε δ 0 x y = (Mf I ε δ : ℝ) := by
    intro x y
    simp [hWeight, card_freeBox]
  simp only [Cpart, hh, Finset.sum_const, nsmul_eq_mul, C0]
  have hsmall : (smallBox I ε δ).card =
      ∏ k ∈ Finset.range (nSmall I ε δ), (smallB I ε δ k + 1) := by
    unfold smallBox
    rw [Fintype.card_piFinset]
    simp only [Finset.card_range]
    exact Fin.prod_univ_eq_prod_range (fun k => smallB I ε δ k + 1) (nSmall I ε δ)
  rw [hsmall]
  push_cast
  ring

/-- INTERNAL: every `C(j)` is positive (both boxes are nonempty, every term positive).
TEXLINE: sections/scales.tex:279-282 -/
theorem Cpart_pos (I : Instance) (ε δ : ℚ) (j : ℕ) : 0 < Cpart I ε δ j := by
  have hS : (smallBox I ε δ).Nonempty := ⟨fun _ => 0, by simp [smallBox]⟩
  have hF : (freeBox I ε δ).Nonempty := ⟨fun _ => 0, by simp [freeBox]⟩
  refine Finset.sum_pos (fun x _ => Finset.sum_pos (fun z _ => by positivity) hF) hS

/-- INTERNAL: union bound across one `bind`: the second stage fails with
probability at most `c` from every state of `A`, so the composite fails with
probability at most `μ(Aᶜ) + c`. -/
theorem outer_bind_le {α β : Type*} (μ : PMF α) (f : α → PMF β) (A : Set α) (B : Set β)
    (c : ℝ≥0∞) (h : ∀ a ∈ A, (f a).toOuterMeasure B ≤ c) :
    (μ.bind f).toOuterMeasure B ≤ μ.toOuterMeasure Aᶜ + c := by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  calc ∑' a, μ a * (f a).toOuterMeasure B ≤ ∑' a, (Aᶜ.indicator μ a + μ a * c) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ A
        · have : a ∉ Aᶜ := fun h' => h' ha
          rw [Set.indicator_of_notMem this, zero_add]
          gcongr; exact h a ha
        · rw [Set.indicator_of_mem (show a ∈ Aᶜ from ha)]
          calc μ a * (f a).toOuterMeasure B ≤ μ a * 1 := by
                gcongr
                rw [outer_eq_pexp]
                exact pexp_le_one _ _ fun b => by by_cases hb : b ∈ B <;> simp [hb]
            _ ≤ μ a + μ a * c := by rw [mul_one]; exact le_self_add
    _ = ∑' a, Aᶜ.indicator μ a + c := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- INTERNAL: the state of the reference experiment after `k` good phases: no
abort, the stored multipliers `w^(0..k)` good, and `∏ R̂` positive within
`4kη` of `C(k)/C(0)` in log.
TEXLINE: sections/algorithm.tex:259-383 -/
def refInv (I : Instance) (ε δ : ℚ) (k : ℕ) (st : RefRunState) : Prop :=
  st.aborted = false ∧ (∀ a ≤ k, a < HParam I ε δ → goodMult I ε δ a (st.ws a)) ∧
    0 < st.prod ∧
    |Real.log st.prod - Real.log (Cpart I ε δ k / Cpart I ε δ 0)| ≤
      4 * (k : ℝ) * (ηParam I ε δ : ℝ)

/-- INTERNAL: a successful phase `j` carries the invariant from `j` to `j + 1`.
TEXLINE: sections/algorithm.tex:345-383 -/
theorem refInv_succ (I : Instance) (ε δ : ℚ) (j : ℕ) (st st' : RefRunState)
    (h : refInv I ε δ j st) (hok : phaseOK I ε δ j st st') : refInv I ε δ (j + 1) st' := by
  obtain ⟨-, hgood, hprod, hlog⟩ := h
  obtain ⟨hab', hws, hnew, R, hR, hprod', hRlog⟩ := hok
  have hC := Cpart_pos I ε δ
  refine ⟨hab', fun a ha haH => ?_, by rw [hprod']; positivity, ?_⟩
  · rcases Nat.lt_or_ge a (j + 1) with hlt | hge
    · rw [hws a (by omega)]; exact hgood a (by omega) haH
    · obtain rfl : a = j + 1 := by omega
      exact hnew haH
  · rw [hprod', Real.log_mul hprod.ne' hR.ne']
    rw [Real.log_div hR.ne' (div_pos (hC _) (hC _)).ne',
      Real.log_div (hC _).ne' (hC _).ne'] at hRlog
    rw [Real.log_div (hC _).ne' (hC _).ne'] at hlog ⊢
    have e : Real.log st.prod + Real.log R - (Real.log (Cpart I ε δ (j + 1)) -
        Real.log (Cpart I ε δ 0)) =
        (Real.log st.prod - (Real.log (Cpart I ε δ j) - Real.log (Cpart I ε δ 0))) +
        (Real.log R - (Real.log (Cpart I ε δ (j + 1)) - Real.log (Cpart I ε δ j))) := by ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ 4 * (j : ℝ) * (ηParam I ε δ : ℝ) + 4 * (ηParam I ε δ : ℝ) := add_le_add hlog hRlog
      _ = _ := by push_cast; ring

/-- INTERNAL: after `k ≤ H` phases the invariant fails with probability at most
`k/[50(H+1)]` (union bound over the phases, `ref_phase_good` for each).
TEXLINE: sections/algorithm.tex:259-383 -/
theorem refInv_loop (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (k : ℕ) (hk : k ≤ HParam I ε δ) :
    (loop (refPhase I ε δ) k
        ⟨fun a => if a = 0 then w0 I ε δ else fun _ _ => 0, 1, false⟩).toOuterMeasure
      {st | ¬ refInv I ε δ k st} ≤ (k : ℝ≥0∞) * (1 / (50 * ((HParam I ε δ : ℝ≥0∞) + 1))) := by
  induction k with
  | zero =>
    have h0 : refInv I ε δ 0
        ⟨fun a => if a = 0 then w0 I ε δ else fun _ _ => 0, 1, false⟩ := by
      refine ⟨rfl, fun a ha _ => ?_, one_pos, ?_⟩
      · obtain rfl : a = 0 := by omega
        simpa using w0_good I ε δ
      · simp
    rw [loop_zero, Nat.cast_zero, zero_mul, nonpos_iff_eq_zero,
      PMF.toOuterMeasure_apply_eq_zero_iff, PMF.support_pure, Set.disjoint_singleton_left]
    exact fun h => h h0
  | succ k ih =>
    rw [loop_succ, Nat.cast_succ, add_mul, one_mul]
    refine (outer_bind_le _ _ {st | refInv I ε δ k st} _ _ fun st hst => ?_).trans
      (add_le_add (by simpa [Set.compl_ofPred] using ih (by omega)) le_rfl)
    refine le_trans (MeasureTheory.measure_mono fun st' hst' => ?_)
      (ref_phase_good hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp k (by omega) st hst.1
        fun a ha => hst.2.1 a ha (by omega))
    exact fun hok => hst' (refInv_succ I ε δ k st st' hst hok)

/-- **Accuracy of the reference experiment** (`prop:annealing`): with probability
at least `1 - 1/50` the reference run does not abort (so `Z_ref > 0`) and
`|log(Z_ref / C(H))| ≤ 4 H η`.
PAPER: sections/algorithm.tex:259-383 -/
theorem reference_accuracy (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) :
    (49 / 50 : ENNReal) ≤ (refRun I ε δ).toOuterMeasure
      {Zr | 0 < Zr ∧ |Real.log (Zr / Cpart I ε δ (HParam I ε δ))| ≤
        4 * (HParam I ε δ : ℝ) * (ηParam I ε δ : ℝ)} := by
  set H := HParam I ε δ
  set μ := loop (refPhase I ε δ) H
    ⟨fun a => if a = 0 then w0 I ε δ else fun _ _ => 0, 1, false⟩
  have hbad := refInv_loop hprior I ε δ hm hn hε hε1 hδ hδ1 hfeas hp H le_rfl
  have hC := Cpart_pos I ε δ
  have hC0 : (0 : ℝ) < (C0 I ε δ : ℝ) := by rw [← Cpart_zero]; exact hC 0
  -- every invariant state maps into the target set
  have hsub : {st | refInv I ε δ H st} ⊆ (fun st : RefRunState =>
      if st.aborted then (0 : ℝ) else (C0 I ε δ : ℝ) * st.prod) ⁻¹'
      {Zr | 0 < Zr ∧ |Real.log (Zr / Cpart I ε δ H)| ≤ 4 * (H : ℝ) * (ηParam I ε δ : ℝ)} := by
    rintro st ⟨hab, -, hprod, hlog⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hab, Bool.false_eq_true, ite_false]
    refine ⟨mul_pos hC0 hprod, ?_⟩
    rw [Real.log_div (mul_pos hC0 hprod).ne' (hC H).ne', Real.log_mul hC0.ne' hprod.ne',
      ← Cpart_zero]
    rw [Real.log_div (hC H).ne' (hC 0).ne'] at hlog
    calc _ = |Real.log st.prod - (Real.log (Cpart I ε δ H) - Real.log (Cpart I ε δ 0))| := by
          congr 1; ring
      _ ≤ _ := hlog
  -- the failure budget is at most `1/50`
  have hbud : (H : ℝ≥0∞) * (1 / (50 * ((H : ℝ≥0∞) + 1))) ≤ 1 / 50 := by
    rw [← mul_div_assoc, mul_one,
      ENNReal.div_le_iff (by positivity) (ENNReal.mul_lt_top (by simp) (by simp)).ne]
    calc (H : ℝ≥0∞) ≤ (H : ℝ≥0∞) + 1 := le_self_add
      _ = 1 / 50 * (50 * ((H : ℝ≥0∞) + 1)) := by
        rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by simp), one_mul]
  have huniv : μ.toOuterMeasure Set.univ = 1 := by
    rw [PMF.toOuterMeasure_apply, Set.indicator_univ, PMF.tsum_coe]
  have hone : 1 ≤ μ.toOuterMeasure {st | refInv I ε δ H st} + 1 / 50 := by
    calc (1 : ℝ≥0∞) = μ.toOuterMeasure ({st | refInv I ε δ H st} ∪ {st | ¬ refInv I ε δ H st}) := by
          rw [← huniv]; congr 1; ext st; simp [em]
      _ ≤ _ := MeasureTheory.measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl (hbad.trans hbud)
  unfold refRun
  rw [PMF.toOuterMeasure_map_apply]
  refine le_trans ?_ (MeasureTheory.measure_mono hsub)
  have h4950 : (49 / 50 : ℝ≥0∞) = 1 - 1 / 50 := by
    refine ENNReal.eq_sub_of_add_eq (by simp) ?_
    rw [ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by simp)
  rw [h4950]
  exact tsub_le_iff_right.2 hone

end Cellcounting.Analysis
