import Cellcounting.Analysis.CostScale

/-!
# One weight-oracle call costs a polynomial number of bit operations

`Cellcounting.Analysis.oracle_cost`: for any context whose sizes are bounded by
`S` (`CtxSize`) and whose penalty is bounded by `S` on the extended box
(`PenaltyOK`), one call `Program.oracle C tape x y j ξin θ cur` on a box-valid
profile, with `j ≤ S` and `ξin⁻¹, θ⁻¹, ratLen ξin, ratLen θ ≤ S`, costs at most
`S ^ k` bit operations on every tape, and returns a rational of length at most
`S ^ k`.  The exponent `k` is fixed.

The penalty bound enters three places: the dyadic Metropolis trials of the bin
walk read `⌊a D(w)/H⌋ - ⌊a D(v)/H⌋` fair bits, the ratio samples compute
`2^{⌊aD/H⌋ - ⌊(a+1)D/H⌋}` exactly, and `pow2Approx` builds `2^h` with
`|h| ≤ (|β| + 1) s'`.  Everything else is loop counts polynomial in `S`,
`ξin⁻¹`, `θ⁻¹` and binary lengths that grow additively: sums of polynomially
many rationals over a common denominator, products of polynomially many.

Proved here so far: `uniformBits_cost`.  The route for `oracle_cost`: bound
`oracleParams` (values `N_in, ℓ_in, s', depth ≤ poly(S)`, `ζ⁻¹ ≤ poly(S)`); bound
`penalty` on bin points and on integer offset points (all intermediate values lie in
`(1/B)ℤ` resp. `ℤ` with magnitude `≤ 2^{poly}`, so lengths stay polynomial through the
leaf elimination; the final `dist/b_t` sum has denominator dividing `B ∏ b_t`); bound
`walkStep`/`sampleBin` with the invariant `v_e ≤ B - 1` (so bin points are in the
extended box and `PenaltyOK` applies); then `ratioAvg`, `pow2Approx` (bisection lengths
grow by `O(1)` per halving, `s'`-th powers by repeated squaring have length
`≤ s'·(depth + O(1))`), `binOffsets` (dyadic draws), `corrAvg`, and the product.
A plain `ratLen (x + y) ≤ 2(ratLen x + ratLen y) + 1` bound doubles per addition and is
too weak for sums of `N_in` terms; use `ratLen_le_of_mul_eq` with a common denominator.
-/

set_option autoImplicit false

namespace Cellcounting.Analysis

open Arlib.Computation
open Cellcounting.Program
open Cellcounting.Model.Operations
open Cellcounting.Interface

/-- INTERNAL: `k` fair bits read as a binary integer: the value is `< 2^k`, the cursor
advances by `k`, and the price is quadratic in `k` (the accumulator has at most `k` bits).
Used by the bin walk's dyadic trials, the dyadic draws, and the acceptance test.
TEXLINE: sections/evaluation.tex:356-371 -/
theorem uniformBits_cost (tape : Coins ℕ) (k cur : ℕ) :
    (uniformBits tape k cur).val.1.get < 2 ^ k ∧ (uniformBits tape k cur).val.2 = cur + k ∧
    Charged.steps rate (uniformBits tape k cur) ≤ 7 + k * (4 * k + 8) := by
  unfold uniformBits
  simp only [Charged.steps_bind, costVb, steps_SNat_lit]
  obtain ⟨⟨h1, h2⟩, h3⟩ := repeatFor_inv (fun _ (st : SNat × ℕ) => (do
      let __x ← coin tape st.2
      let y2 ← SNat.mul st.1 (SNat.lit 2).val
      if __x.1 then do
        let y ← SNat.add y2 (SNat.lit 1).val
        pure (y, __x.2)
      else pure (y2, __x.2) : Prog (SNat × ℕ)))
    (fun r (st : SNat × ℕ) => st.1.get < 2 ^ r ∧ st.2 = cur + r) (4 * k + 8) k
    ((SNat.lit 0).val, cur) (by simp)
    (by
      rintro r ⟨y, c⟩ hr ⟨hy, hc⟩
      simp only [coin, Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_flip,
        steps_SNat_mul, SNat.get_mul, SNat.get_lit] at hy hc ⊢
      have hb2 : bitLen 2 = 3 := by decide
      have hb1 : bitLen 1 = 2 := by decide
      have hyl : bitLen y.get ≤ r + 1 := bitLen_le_of_lt_two_pow hy
      have hmul : bitLen y.get * bitLen 2 ≤ 3 * k := by rw [hb2]; omega
      split
      · simp only [Charged.steps_bind, costVb, costVp, Charged.steps_pure, steps_SNat_add,
          SNat.get_add, SNat.get_mul, SNat.get_lit]
        have h2y : bitLen (y.get * 2) ≤ r + 2 := by
          apply bitLen_le_of_lt_two_pow; rw [pow_succ]; omega
        refine ⟨⟨by rw [pow_succ]; omega, by omega⟩, by rw [hb1]; omega⟩
      · simp only [costVp, Charged.steps_pure, SNat.get_mul, SNat.get_lit]
        refine ⟨⟨by rw [pow_succ]; omega, by omega⟩, by omega⟩)
  refine ⟨h1, h2, ?_⟩
  have hb0 : bitLen 0 = 1 := by decide
  have hb1 : bitLen 1 = 2 := by decide
  have hb2 : bitLen 2 = 3 := by decide
  omega
/-- **Oracle cost.**
PAPER: sections/evaluation.tex:27-28 ("On every execution its bit cost is bounded
by a fixed polynomial in `L, ε⁻¹, ξ_in⁻¹, θ⁻¹` and the encoding lengths of the
parameters", `prop:weight-oracle`); proof at sections/evaluation.tex:386-470. -/
theorem oracle_cost : ∃ k : ℕ, ∀ (S : ℕ) (C : Ctx), 2 ≤ S → CtxSize S C → PenaltyOK S C →
    ∀ (x y : List SNat), ProfileValid C x y → ∀ (j : ℕ), j ≤ S →
    ∀ (ξin θ : SRat), 0 < ξin.get → 0 < θ.get → ξin.get⁻¹ ≤ S → θ.get⁻¹ ≤ S →
    ratLen ξin.get ≤ S → ratLen θ.get ≤ S →
    ∀ (tape : Coins ℕ) (cur : ℕ),
      Charged.steps rate (oracle C tape x y j ξin θ cur) ≤ S ^ k ∧
      ratLen (oracle C tape x y j ξin θ cur).val.1.get ≤ S ^ k := by
  sorry

end Cellcounting.Analysis
