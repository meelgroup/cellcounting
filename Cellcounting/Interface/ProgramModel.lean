import Cellcounting.Model.Program
import Cellcounting.Interface.Pseudocode
import Cellcounting.Interface.Encoding
import Cellcounting.Model.Prior
import Cellcounting.Model.Prelude
import Cellcounting.Model.Operations
import Cellcounting.Model.Run
import Cellcounting.Analysis.TapeWindow
import Cellcounting.Analysis.PhaseWindow
import Cellcounting.Analysis.RepeatRunsTapeFalse
import Cellcounting.Analysis.FlipsReadBound
import Cellcounting.Analysis.BuildCtxView
import Cellcounting.Analysis.ChainSetupView
import Cellcounting.Analysis.UniformBitsTape

/-!
# The program and the model are the same algorithm

`Cellcounting.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`Cellcounting.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`Cellcounting.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`output_eq_fpras` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

A `_tape` lemma states the joint law of one program piece's result and the
next unread tape bits.  That form alone does not compose, because it does not
say which bits a piece reads.  Chaining pieces also uses that each piece reads
only the bits between its start and end cursors.  That is the `Window` of
`Analysis/TapeWindow.lean`, proved for every randomized piece of the program in
`Analysis/PhaseWindow.lean`.  `tapeLaw_bind` composes the two.  For the same
reason, `repeatRuns_tape`, whose run `F` is abstract, is false without a window
hypothesis on `F` (`Analysis/RepeatRunsTapeFalse.lean`).  The repaired statement
is `repeatRuns_tape_of_window`.

`annealRun_tape` is proved from `phase_tape`.  `repeatRuns_tape_of_window` is
proved outright.  `output_eq_fpras` is proved from `output_eq_map_estimate`,
`estimate_feasible_law`, `estimate_infeasible` and `feasible_val`, together with the
input round-trip (`readList_val`, `readMatrix_val`, `decode_input`) and the uniform
bound on fair bits read (`Analysis.flipsRead_bddAbove`, `Analysis/FlipsReadBound.lean`),
which makes `tapeLength` cover every execution.  `binOffsets_tape` is proved from
`dyadicDraw_tape` and `Analysis.dyadicDraw_window`, by induction over the free cells.
`uniformBits_tape` is proved from `Analysis.bitsVal_tape` (`Analysis/UniformBitsTape.lean`):
the program loop reads the bits at `cur, …, cur + k - 1` as `Analysis.bitsVal`.
`dyadicDraw_tape` is proved from `uniformBits_tape` by `Analysis.tapeLaw_map`: the program's
steps before and after its single `uniformBits` call are tape-free, and its exponent
`Nat.size (⌈M/ζ⌉₊ - 1)` is the pseudocode's `Nat.clog 2 ⌈M/ζ⌉₊` (`size_pred_eq_clog`).
`corrAvg_tape` is proved from `sampleBin_tape`, `binOffsets_tape`, `penalty_val` and
`pow2Approx_val`, by induction over the `N_in` rounds; it uses that a program bin sample
has at most `C.nFree` coordinates (`sampleBin_val_length_le`), so that its cube point has
the pseudocode `binPoint` as view (`binPoint_val_view`).
Every other rung is still `sorry`.
-/

set_option autoImplicit false

namespace Cellcounting

/-- Reading k fair coins from a uniform tape gives the uniform k-bit integer, and the unread rest of the tape is still uniform and independent. Every later tape lemma is built from this one. -/
theorem uniformBits_tape (k cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.uniformBits (Arlib.Computation.Coins.ofFinset s) k cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.uniformBits (Arlib.Computation.Coins.ofFinset s) k cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.uniformBits k).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  -- the program reads the bits at `cur, …, cur + k - 1`, most significant first
  have hval : ∀ (s : Finset ℕ) (k : ℕ),
      (Program.uniformBits (Arlib.Computation.Coins.ofFinset s) k cur).val.1.get = Analysis.bitsVal s cur k ∧
      (Program.uniformBits (Arlib.Computation.Coins.ofFinset s) k cur).val.2 = cur + k := by
    intro s k
    let step : Model.Operations.SNat × ℕ → Model.Operations.SNat × ℕ := fun st =>
      (if decide (st.2 ∈ s) = true then (Model.Operations.SNat.add (Model.Operations.SNat.mul st.1 (Model.Operations.SNat.lit 2).val).val (Model.Operations.SNat.lit 1).val).val
        else (Model.Operations.SNat.mul st.1 (Model.Operations.SNat.lit 2).val).val, st.2 + 1)
    have hv : (Program.uniformBits (Arlib.Computation.Coins.ofFinset s) k cur).val =
        (List.range k).foldl (fun b _ => step b) ((Model.Operations.SNat.lit 0).val, cur) := by
      show (Arlib.Computation.Charged.repeatFor _ k _).val = _
      rw [Analysis.val_repeatFor']
      congr 1
      funext b r
      have hc : (Program.coin (Arlib.Computation.Coins.ofFinset s) b.2).val = (decide (b.2 ∈ s), b.2 + 1) := rfl
      rw [Arlib.Computation.Charged.val_bind, hc]
      simp only [step]
      cases decide (b.2 ∈ s) <;> rfl
    rw [hv]
    clear hv
    induction k with
    | zero => exact ⟨rfl, rfl⟩
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨h1, h2⟩ := ih
      generalize List.foldl (fun b _ => step b) ((Model.Operations.SNat.lit 0).val, cur) (List.range k) = st at h1 h2 ⊢
      obtain ⟨y, c⟩ := st
      simp only at h1 h2
      subst h2
      refine ⟨?_, rfl⟩
      simp only [step, Analysis.bitsVal]
      by_cases h : cur + k ∈ s <;> simp [h, h1, mul_comm]
  have e : (fun (s : Finset ℕ) => let r := (Program.uniformBits (Arlib.Computation.Coins.ofFinset s) k cur).val;
      (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) =
      fun s => (Analysis.bitsVal s cur k, Analysis.tapeRest s (cur + k) n) := by
    funext s
    simp only [(hval s k).1, (hval s k).2, Analysis.tapeRest]
  rw [e]
  exact Analysis.bitsVal_tape cur k n T (by have := hT ∅; rw [(hval ∅ k).2] at this; omega)

/-- The bounded fair-bit finite-choice draw used by the program has the pseudocode's dyadic law, and the tape left over stays uniform. -/
theorem dyadicDraw_tape (M : Cellcounting.Model.Operations.SNat) (ζ : Cellcounting.Model.Operations.SRat) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.dyadicDraw (Arlib.Computation.Coins.ofFinset s) M ζ cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.dyadicDraw (Arlib.Computation.Coins.ofFinset s) M ζ cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.dyadicDraw M.get ζ.get).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  -- the exponent the program computes
  let kS := (Program.clog2 (Model.Operations.SRat.natCeil
      (Model.Operations.SRat.div (Model.Operations.SNat.toRat M).val ζ).val).val).val
  have hk : kS.get = Nat.clog 2 ⌈(M.get : ℚ) / ζ.get⌉₊ :=
    Pseudocode.size_pred_eq_clog _
  have hub : Analysis.TapeLaw Prod.snd (fun r : Model.Operations.SNat × ℕ => r.1.get)
      (fun s => (Program.uniformBits (Arlib.Computation.Coins.ofFinset s) kS.get cur).val)
      (Pseudocode.uniformBits kS.get) := fun n T hT => uniformBits_tape kS.get cur n T hT
  let h : Model.Operations.SNat × ℕ → Model.Operations.SNat × ℕ := fun r =>
    ((Model.Operations.SNat.div (Model.Operations.SNat.mul M r.1).val
      (Model.Operations.SNat.pow2 kS).val).val, r.2)
  have hl := Analysis.tapeLaw_map (π' := Prod.snd) (v' := fun r : Model.Operations.SNat × ℕ => r.1.get)
    h (fun y => M.get * y / 2 ^ kS.get) (fun _ => rfl) (fun _ => rfl) hub
  have hval : ∀ s, (Program.dyadicDraw (Arlib.Computation.Coins.ofFinset s) M ζ cur).val =
      h (Program.uniformBits (Arlib.Computation.Coins.ofFinset s) kS.get cur).val := fun _ => rfl
  have := hl n T (fun s => by beta_reduce; rw [← hval s]; exact hT s)
  simp only [← hval, Analysis.tapeRest] at this
  rw [Pseudocode.dyadicDraw, ← hk]
  exact this

/-- The program's deterministic exact-rational computation of the penalty agrees with the pseudocode penalty, given a context that matches the instance. -/
theorem penalty_val (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (x y : List Cellcounting.Model.Operations.SNat) (zf : List Cellcounting.Model.Operations.SRat) : (Cellcounting.Program.penalty C x y zf).val.get = Cellcounting.Pseudocode.penalty I ε δ (fun k => (x.getD k default).get) (fun k => (y.getD k default).get) (fun k => (zf.getD k default).get) := by
  sorry

/-- The program's truncated rational approximation of a power of two is the same value as the pseudocode's. -/
theorem pow2Approx_val (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (ξin θ β : Cellcounting.Model.Operations.SRat) : (Cellcounting.Program.pow2Approx (Cellcounting.Program.oracleParams C ξin θ).val β).val.get = Cellcounting.Pseudocode.pow2Approx I ε δ ξin.get β.get := by
  sorry

/-- One step of the program's walk over free coordinates inside the weight evaluator has the pseudocode walk-step law, and the tape after it is still fresh. -/
theorem walkStep_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (ξin θ aq : Cellcounting.Model.Operations.SRat) (a : ℕ) (ha : aq.get = (a : ℚ)) (x y v : List Cellcounting.Model.Operations.SNat) (hv : v.length = C.nFree) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.walkStep C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) aq x y (v, cur)).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.walkStep C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) aq x y (v, cur)).val; ((fun (k : ℕ) => (r.1.getD k default).get), ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.walkStep I ε δ a (fun k => (x.getD k default).get) (fun k => (y.getD k default).get) (fun k => (v.getD k default).get)).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- The program's bin sampler, a fixed number of walk steps, has the pseudocode law. Proved by induction on the step count using walkStep_tape. -/
theorem sampleBin_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (ξin θ aq : Cellcounting.Model.Operations.SRat) (a : ℕ) (ha : aq.get = (a : ℚ)) (x y : List Cellcounting.Model.Operations.SNat) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.sampleBin C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) aq x y cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.sampleBin C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) aq x y cur).val; ((fun (k : ℕ) => (r.1.getD k default).get), ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.sampleBin I ε δ ξin.get θ.get a (fun k => (x.getD k default).get) (fun k => (y.getD k default).get)).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- The empirical ratio average inside the weight evaluator has the same law in the program as in the pseudocode. -/
theorem ratioAvg_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (ξin θ : Cellcounting.Model.Operations.SRat) (x y : List Cellcounting.Model.Operations.SNat) (a cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.ratioAvg C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) x y a cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.ratioAvg C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) x y a cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.ratioAvg I ε δ ξin.get θ.get a (fun k => (x.getD k default).get) (fun k => (y.getD k default).get)).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- The program's draw of offsets within a bin, together with its weight, has the pseudocode law. -/
theorem binOffsets_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (ξin θ : Cellcounting.Model.Operations.SRat) (v : List Cellcounting.Model.Operations.SNat) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.binOffsets C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) v cur).val.2.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.binOffsets C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) v cur).val; (((fun (k : ℕ) => (r.1.getD k default).get), r.2.1.get), ((s.filter (fun i => r.2.2 ≤ i)).image (fun i => i - r.2.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.binOffsets I ε δ ξin.get θ.get (fun k => (v.getD k default).get)).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  simp only [Prod.mk.injEq] at hC
  obtain ⟨-, -, -, -, -, -, hfree, hnF, -, -, -, -, -, hd, hB, hH, -, -, -⟩ := hC
  -- the offset-draw tolerance
  have hζ : (Program.oracleParams C ξin θ).val.ζ.get = Pseudocode.oZeta I ε δ ξin.get θ.get := by
    show θ.get / (8 * (((C.d.get + 1) * (C.H.get + 1) *
      ⌈1000000 * ((C.H.get + 1 : ℕ) : ℚ) / (θ.get * ((ξin.get / (50 * ((C.H.get + 1 : ℕ) : ℚ))) *
        (ξin.get / (50 * ((C.H.get + 1 : ℕ) : ℚ)))))⌉₊ : ℕ) : ℚ)) = _
    rw [hd, hH]
    simp only [Pseudocode.oZeta, Pseudocode.oQ, Pseudocode.oN, Pseudocode.oSigma, sq]
    push_cast
    ring_nf
  -- the free-cell bound read by the program is the pseudocode's
  have hfreeAt : ∀ k, (Pseudocode.freeAt I ε δ k).2.2 = (C.free.getD k default).2.2.get := by
    intro k
    unfold Pseudocode.freeAt
    rw [← hfree]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases C.free[k]? <;> rfl
  -- one round of the program loop, as a function of the tape
  let P := (Program.oracleParams C ξin θ).val
  let one := (Model.Operations.SNat.lit 1).val
  let step : ℕ → List Model.Operations.SRat × Model.Operations.SNat × ℕ → Finset ℕ →
      List Model.Operations.SRat × Model.Operations.SNat × ℕ := fun k st s =>
    let e := C.free.getD k default
    let ve := v.getD k default
    let b1 := (Model.Operations.SNat.add e.2.2 one).val
    let lo := (Program.ceilDivN (Model.Operations.SNat.mul b1 ve).val C.B).val
    let hi := (Program.ceilDivN (Model.Operations.SNat.mul b1 (Model.Operations.SNat.add ve one).val).val C.B).val
    let len := (Model.Operations.SNat.sub hi lo).val
    let r := (Program.dyadicDraw (Arlib.Computation.Coins.ofFinset s) len P.ζ st.2.2).val
    (st.1 ++ [(Model.Operations.SNat.toRat (Model.Operations.SNat.add lo r.1).val).val],
      (Model.Operations.SNat.mul st.2.1 len).val, r.2)
  let init : List Model.Operations.SRat × Model.Operations.SNat × ℕ := ([], one, cur)
  let g : ℕ → Finset ℕ → List Model.Operations.SRat × Model.Operations.SNat × ℕ := fun k s =>
    (List.range k).foldl (fun st i => step i st s) init
  have hg : ∀ s, (Program.binOffsets C P (Arlib.Computation.Coins.ofFinset s) v cur).val = g C.nFree s := by
    intro s
    show (Arlib.Computation.Charged.repeatFor _ C.nFree init).val = _
    rw [Analysis.val_repeatFor']
    rfl
  let π : List Model.Operations.SRat × Model.Operations.SNat × ℕ → ℕ := fun r => r.2.2
  let view : List Model.Operations.SRat × Model.Operations.SNat × ℕ → (ℕ → ℚ) × ℕ := fun r =>
    (fun k => (r.1.getD k default).get, r.2.1.get)
  let F : ℕ → (ℕ → ℚ) × ℕ → PMF ((ℕ → ℚ) × ℕ) := fun k st =>
    let b1 := (Pseudocode.freeAt I ε δ k).2.2 + 1
    let lo := (b1 * (fun k => (v.getD k default).get) k) ⌈/⌉ Pseudocode.BParam I ε δ
    let hi := (b1 * ((fun k => (v.getD k default).get) k + 1)) ⌈/⌉ Pseudocode.BParam I ε δ
    (Pseudocode.dyadicDraw (hi - lo) (Pseudocode.oZeta I ε δ ξin.get θ.get)).map fun off =>
      (Function.update st.1 k ((lo + off : ℕ) : ℚ), st.2 * (hi - lo))
  -- appending to a list of length `k` updates its view at `k`
  have hpush : ∀ (l : List Model.Operations.SRat) (a : Model.Operations.SRat) (k : ℕ), l.length = k →
      (fun k' => ((l ++ [a]).getD k' default).get) =
        Function.update (fun k' => (l.getD k' default).get) k a.get := by
    intro l a k hl
    funext k'
    rw [Function.update_apply, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rcases lt_trichotomy k' k with h | h | h
    · rw [if_neg (by omega), List.getElem?_append_left (by omega)]
    · subst h
      rw [if_pos rfl, List.getElem?_append_right (by omega), hl, Nat.sub_self]
      rfl
    · have h1 : (l ++ [a])[k']? = none := List.getElem?_eq_none (by simp; omega)
      have h2 : l[k']? = none := List.getElem?_eq_none (by omega)
      rw [if_neg (by omega), h1, h2]
  -- one round: windowed, with the pseudocode round law
  have hstep : ∀ k x, x.1.length = k →
      Analysis.Window x.2.2 π (step k x) ∧ Analysis.TapeLaw π view (step k x) (F k (view x)) := by
    intro k x hx
    let e := C.free.getD k default
    let ve := v.getD k default
    let b1 := (Model.Operations.SNat.add e.2.2 one).val
    let lo := (Program.ceilDivN (Model.Operations.SNat.mul b1 ve).val C.B).val
    let hi := (Program.ceilDivN (Model.Operations.SNat.mul b1 (Model.Operations.SNat.add ve one).val).val C.B).val
    let len := (Model.Operations.SNat.sub hi lo).val
    let post : Model.Operations.SNat × ℕ → List Model.Operations.SRat × Model.Operations.SNat × ℕ := fun r =>
      (x.1 ++ [(Model.Operations.SNat.toRat (Model.Operations.SNat.add lo r.1).val).val],
        (Model.Operations.SNat.mul x.2.1 len).val, r.2)
    have hdd : Analysis.TapeLaw Prod.snd (fun r : Model.Operations.SNat × ℕ => r.1.get)
        (fun s => (Program.dyadicDraw (Arlib.Computation.Coins.ofFinset s) len P.ζ x.2.2).val)
        (Pseudocode.dyadicDraw len.get P.ζ.get) :=
      fun n T hT => dyadicDraw_tape len P.ζ x.2.2 n T hT
    have hlo : lo.get = ((Pseudocode.freeAt I ε δ k).2.2 + 1) * (v.getD k default).get ⌈/⌉
        Pseudocode.BParam I ε δ := by
      show ((e.2.2.get + 1) * ve.get + C.B.get - 1) / C.B.get = _
      rw [hfreeAt, hB]; rfl
    have hhi : hi.get = ((Pseudocode.freeAt I ε δ k).2.2 + 1) * ((v.getD k default).get + 1) ⌈/⌉
        Pseudocode.BParam I ε δ := by
      show ((e.2.2.get + 1) * (ve.get + 1) + C.B.get - 1) / C.B.get = _
      rw [hfreeAt, hB]; rfl
    have hlen : len.get = hi.get - lo.get := rfl
    refine ⟨Analysis.window_map post (fun _ => rfl) (Analysis.dyadicDraw_window len P.ζ x.2.2), ?_⟩
    have hF : F k (view x) = (Pseudocode.dyadicDraw len.get P.ζ.get).map fun off =>
        (Function.update (view x).1 k ((lo.get + off : ℕ) : ℚ), (view x).2 * len.get) := by
      rw [hζ, hlen, hlo, hhi]
    rw [hF]
    exact Analysis.tapeLaw_map post _ (fun _ => rfl) (fun r => by
      simp only [view, post]
      rw [hpush _ _ k hx]
      rfl) hdd
  have key : ∀ k, Analysis.Window cur π (g k) ∧
      Analysis.TapeLaw π view (g k) (Pseudocode.loop F k (view init)) ∧ ∀ s, (g k s).1.length = k := by
    intro k
    induction k with
    | zero =>
      exact ⟨Analysis.window_const init le_rfl, Analysis.tapeLaw_const π view init, fun _ => rfl⟩
    | succ k ih =>
      obtain ⟨hw, hl, hlen⟩ := ih
      have hgf : g (k + 1) = fun s => step k (g k s) s := by
        funext s
        simp only [g, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hloop : Pseudocode.loop F (k + 1) (view init) = (Pseudocode.loop F k (view init)).bind (F k) := by
        unfold Pseudocode.loop
        rw [List.range_succ, List.foldlM_append]
        simp only [List.foldlM_cons, List.foldlM_nil]
        show (List.foldlM (fun b i => F i b) (view init) (List.range k)).bind
          (fun b => (F k b).bind PMF.pure) = _
        simp only [PMF.bind_pure]
      rw [hgf, hloop]
      refine ⟨Analysis.window_bind (g₂ := fun x s => step k x s) (fun x => x.1.length = k) hw hlen
          (fun x hx => (hstep k x hx).1),
        Analysis.tapeLaw_bind (g₂ := fun x s => step k x s) (G₂ := F k) (fun x => x.1.length = k) hw hlen
          (fun x hx => (hstep k x hx).1) hl (fun x hx => (hstep k x hx).2), fun s => ?_⟩
      simp only [step, List.length_append, List.length_singleton, hlen s]
  have hinit : view init = (fun _ => 0, 1) := rfl
  have hpseudo : Pseudocode.binOffsets I ε δ ξin.get θ.get (fun k => (v.getD k default).get) =
      Pseudocode.loop F C.nFree (view init) := by
    rw [hinit, hnF]
    rfl
  rw [hpseudo]
  have := (key C.nFree).2.1 n T (fun s => by rw [← hg]; exact hT s)
  simp only [← hg] at this
  exact this

section corrAvgTape
open Arlib.Computation Cellcounting.Model.Operations

/-- INTERNAL: the bin-walk acceptance step returns a bin vector of the current length when the proposal has that length. TEXLINE: sections/evaluation.tex:40-482 -/
theorem binAccept_val_length (C : Program.Ctx) (tape : Arlib.Computation.Coins ℕ) (aq : Model.Operations.SRat) (x y v w : List Model.Operations.SNat) (cur : ℕ) (hw : w.length = v.length) :
    (Program.binAccept C tape aq x y v w cur).val.1.length = v.length := by
  unfold Program.binAccept
  simp only [Charged.val_bind]
  split
  · simpa using hw
  · simp only [Charged.val_bind]
    split <;> simp [hw]

/-- INTERNAL: one program bin-walk step preserves the length of the bin vector. TEXLINE: sections/evaluation.tex:40-482 -/
theorem walkStep_val_length (C : Program.Ctx) (P : Program.OParams) (tape : Arlib.Computation.Coins ℕ) (aq : Model.Operations.SRat) (x y : List Model.Operations.SNat)
    (st : List Model.Operations.SNat × ℕ) : (Program.walkStep C P tape aq x y st).val.1.length = st.1.length := by
  unfold Program.walkStep
  simp only [Charged.val_bind]
  split
  · simp only [Charged.val_bind]
    split
    · simp only [Charged.val_bind]
      split
      · rfl
      · simp only [Charged.val_bind]; rw [binAccept_val_length]; simp
    · simp only [Charged.val_bind]
      split
      · rfl
      · simp only [Charged.val_bind]; rw [binAccept_val_length]; simp
  · rfl

/-- INTERNAL: the program's bin sample has at most `C.nFree` coordinates, so its view vanishes beyond the free cells. TEXLINE: sections/evaluation.tex:40-482 -/
theorem sampleBin_val_length_le (C : Program.Ctx) (P : Program.OParams) (tape : Arlib.Computation.Coins ℕ) (aq : Model.Operations.SRat) (x y : List Model.Operations.SNat)
    (cur : ℕ) : (Program.sampleBin C P tape aq x y cur).val.1.length ≤ C.nFree := by
  unfold Program.sampleBin
  simp only [Charged.val_bind]
  split
  · simp
  · simp only [Charged.val_bind]
    rw [Analysis.val_repeatFor']
    have : ∀ (l : List ℕ) (b : List SNat × ℕ), (l.foldl (fun b r => (Program.walkStep C P tape aq x y b).val) b).1.length = b.1.length := by
      intro l; induction l with
      | nil => intro b; rfl
      | cons a l ih => intro b; rw [List.foldl_cons, ih, walkStep_val_length]
    rw [this]; simp

/-- INTERNAL: on a bin vector with at most `C.nFree` coordinates, the program's cube point has the pseudocode `binPoint` as its view. TEXLINE: sections/evaluation.tex:40-482 -/
theorem binPoint_val_view (I : Instance) (ε δ : ℚ) (C : Program.Ctx)
    (hfree : C.free.map (fun (e : Program.Entry) => (e.1, e.2.1, e.2.2.get)) = (Pseudocode.forest I ε δ).free)
    (hnF : C.nFree = Pseudocode.nFree I ε δ) (hBq : C.Bq.get = (Pseudocode.BParam I ε δ : ℚ))
    (v : List Model.Operations.SNat) (hv : v.length ≤ C.nFree) :
    (fun k => ((Program.binPoint C v).val.getD k default).get) =
      Pseudocode.binPoint I ε δ (fun k => (v.getD k default).get) := by
  have hfreeAt : ∀ k, (Pseudocode.freeAt I ε δ k).2.2 = (C.free.getD k default).2.2.get := by
    intro k
    unfold Pseudocode.freeAt
    rw [← hfree]
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases C.free[k]? <;> rfl
  let h : ℕ → SRat := fun k =>
    (SRat.div (SNat.toRat (SNat.mul (SNat.add (C.free.getD k default).2.2 (SNat.lit 1).val).val
      (v.getD k default)).val).val C.Bq).val
  have hfold : ∀ m, (List.range m).foldl (fun acc k => acc ++ [h k]) [] = (List.range m).map h := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [List.range_succ, List.foldl_append, ih, List.map_append]; rfl
  have hval : (Program.binPoint C v).val = (List.range C.nFree).map h := by
    unfold Program.binPoint
    simp only [Charged.val_bind, Analysis.val_repeatFor']
    exact hfold _
  rw [hval]
  funext k
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hk : k < C.nFree
  · rw [List.getElem?_range hk]
    simp only [Option.map_some, Option.getD_some, h, Interface.SRat.get_div, Interface.SNat.get_toRat,
      Interface.SNat.get_mul, Interface.SNat.get_add, Interface.SNat.get_lit, Pseudocode.binPoint, hBq, hfreeAt]
  · rw [List.getElem?_eq_none (by simpa using hk)]
    have : v[k]? = none := List.getElem?_eq_none (by omega)
    simp only [Pseudocode.binPoint, List.getD_eq_getElem?_getD, this, Option.getD_none]
    simp

/-- The correction-factor average inside the weight evaluator has the same law in the program as in the pseudocode. -/
theorem corrAvg_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (ξin θ : Cellcounting.Model.Operations.SRat) (x y : List Cellcounting.Model.Operations.SNat) (j cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.corrAvg C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) x y j cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.corrAvg C (Cellcounting.Program.oracleParams C ξin θ).val (Arlib.Computation.Coins.ofFinset s) x y j cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.corrAvg I ε δ ξin.get θ.get j (fun k => (x.getD k default).get) (fun k => (y.getD k default).get)).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  have hC0 := hC
  simp only [Prod.mk.injEq] at hC0
  obtain ⟨-, -, -, -, -, -, hfree, hnF, -, -, -, -, hMf, hd, hB, hH, -, hHq, hBq⟩ := hC0
  let P := (Program.oracleParams C ξin θ).val
  let x' : ℕ → ℕ := fun k => (x.getD k default).get
  let y' : ℕ → ℕ := fun k => (y.getD k default).get
  have hN : P.N = Pseudocode.oN I ε δ ξin.get θ.get := by
    show ⌈1000000 * ((C.H.get + 1 : ℕ) : ℚ) / (θ.get * ((ξin.get / (50 * ((C.H.get + 1 : ℕ) : ℚ))) *
        (ξin.get / (50 * ((C.H.get + 1 : ℕ) : ℚ)))))⌉₊ = _
    rw [hH]
    simp only [Pseudocode.oN, Pseudocode.oSigma, sq]
    push_cast
    rfl
  have hNq : P.Nq.get = (P.N : ℚ) := rfl
  have hBe : P.Be.get = Pseudocode.BParam I ε δ ^ Pseudocode.nFree I ε δ := by
    show ((Charged.repeatFor (fun _ acc => SNat.mul acc C.B) C.nFree (SNat.lit 1).val).val).get = _
    rw [Analysis.val_repeatFor', ← hnF, ← hB]
    induction C.nFree with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Interface.SNat.get_mul, ih,
        pow_succ]
  -- the deterministic tail of one round, after the bin walk and the offsets
  let jq := (SNat.toRat (SNat.lit j).val).val
  let Mq := (SNat.toRat C.Mf).val
  let post : SRat × ℕ → List SNat × ℕ → List SRat × SNat × ℕ → SRat × ℕ := fun st r o =>
    let kv := (Program.binExp C jq x y r.1).val
    let Dz := (Program.penalty C x y o.1).val
    let β := (SRat.sub kv (SRat.div (SRat.mul jq Dz).val C.Hq).val).val
    let approx := (Program.pow2Approx P β).val
    let α := (SRat.div (SNat.toRat (SNat.mul P.Be o.2.1).val).val Mq).val
    ((SRat.add st.1 (SRat.mul α approx).val).val, o.2.2)
  let step : SRat × ℕ → Finset ℕ → SRat × ℕ := fun st s =>
    let r := (Program.sampleBin C P (Coins.ofFinset s) jq x y st.2).val
    post st r (Program.binOffsets C P (Coins.ofFinset s) r.1 r.2).val
  let init : SRat × ℕ := ((SRat.lit 0).val, cur)
  let g : ℕ → Finset ℕ → SRat × ℕ := fun k s => (List.range k).foldl (fun st _ => step st s) init
  have hg : ∀ s, (Program.corrAvg C P (Coins.ofFinset s) x y j cur).val =
      ((SRat.div (g P.N s).1 P.Nq).val, (g P.N s).2) := by
    intro s
    simp only [Program.corrAvg, Charged.val_bind, Analysis.val_repeatFor']
    rfl
  -- the pseudocode round
  let F : ℕ → ℚ → PMF ℚ := fun _ s => do
    let v ← Pseudocode.sampleBin I ε δ ξin.get θ.get j x' y'
    let zl ← Pseudocode.binOffsets I ε δ ξin.get θ.get v
    pure (s + Pseudocode.corrSample I ε δ ξin.get j x' y' v zl.1 zl.2)
  have hjq : jq.get = (j : ℚ) := rfl
  -- the value of the deterministic tail
  have hpost : ∀ (st : SRat × ℕ) (r : List SNat × ℕ) (o : List SRat × SNat × ℕ), r.1.length ≤ C.nFree →
      (post st r o).1.get = st.1.get + Pseudocode.corrSample I ε δ ξin.get j x' y'
        (fun k => (r.1.getD k default).get) (fun k => (o.1.getD k default).get) o.2.1.get := by
    intro st r o hr
    have hkv : (Program.binExp C jq x y r.1).val.get =
        (Pseudocode.binExp I ε δ j x' y' (fun k => (r.1.getD k default).get) : ℚ) := by
      show ((⌊jq.get * (Program.penalty C x y (Program.binPoint C r.1).val).val.get / C.Hq.get⌋ : ℤ) : ℚ) = _
      rw [penalty_val I ε δ C hC, binPoint_val_view I ε δ C hfree hnF hBq r.1 hr, hHq, hjq]
      rfl
    simp only [post, Interface.SRat.get_add, Interface.SRat.get_mul, Interface.SRat.get_div,
      Interface.SNat.get_toRat, Interface.SNat.get_mul]
    rw [pow2Approx_val I ε δ C hC]
    simp only [Interface.SRat.get_sub, Interface.SRat.get_mul, Interface.SRat.get_div]
    rw [hkv, penalty_val I ε δ C hC, hBe, hjq, hHq]
    simp only [Pseudocode.corrSample, Mq, Interface.SNat.get_toRat, hMf]
    rfl
  -- one round: windowed, with the pseudocode round law
  have hstep : ∀ k (st : SRat × ℕ), Analysis.Window st.2 Prod.snd (step st) ∧
      Analysis.TapeLaw Prod.snd (fun r : SRat × ℕ => r.1.get) (step st) (F k st.1.get) := by
    intro k st
    have hw₂ : ∀ r : List SNat × ℕ, r.1.length ≤ C.nFree → Analysis.Window r.2 Prod.snd
        (fun s => post st r (Program.binOffsets C P (Coins.ofFinset s) r.1 r.2).val) :=
      fun r _ => Analysis.window_map (post st r) (fun _ => rfl) (Analysis.binOffsets_window C P r.1 r.2)
    have hw₁ := Analysis.sampleBin_window C P jq x y st.2
    have hP : ∀ s, (Program.sampleBin C P (Coins.ofFinset s) jq x y st.2).val.1.length ≤ C.nFree :=
      fun s => sampleBin_val_length_le C P _ jq x y st.2
    refine ⟨Analysis.window_bind (fun r : List SNat × ℕ => r.1.length ≤ C.nFree) hw₁ hP hw₂, ?_⟩
    have hl₁ : Analysis.TapeLaw Prod.snd (fun r : List SNat × ℕ => fun k => (r.1.getD k default).get)
        (fun s => (Program.sampleBin C P (Coins.ofFinset s) jq x y st.2).val)
        (Pseudocode.sampleBin I ε δ ξin.get θ.get j x' y') :=
      fun n T hT => sampleBin_tape I ε δ C hC ξin θ jq j hjq x y st.2 n T hT
    have hl₂ : ∀ r : List SNat × ℕ, r.1.length ≤ C.nFree → Analysis.TapeLaw Prod.snd
        (fun r : SRat × ℕ => r.1.get)
        (fun s => post st r (Program.binOffsets C P (Coins.ofFinset s) r.1 r.2).val)
        ((Pseudocode.binOffsets I ε δ ξin.get θ.get (fun k => (r.1.getD k default).get)).map
          fun zl => st.1.get + Pseudocode.corrSample I ε δ ξin.get j x' y'
            (fun k => (r.1.getD k default).get) zl.1 zl.2) := by
      intro r hr
      have hbo : Analysis.TapeLaw (fun o : List SRat × SNat × ℕ => o.2.2)
          (fun o : List SRat × SNat × ℕ => ((fun k => (o.1.getD k default).get), o.2.1.get))
          (fun s => (Program.binOffsets C P (Coins.ofFinset s) r.1 r.2).val)
          (Pseudocode.binOffsets I ε δ ξin.get θ.get (fun k => (r.1.getD k default).get)) :=
        fun n T hT => binOffsets_tape I ε δ C hC ξin θ r.1 r.2 n T hT
      exact Analysis.tapeLaw_map (post st r) _ (fun _ => rfl) (fun o => hpost st r o hr) hbo
    have hF : F k st.1.get = (Pseudocode.sampleBin I ε δ ξin.get θ.get j x' y').bind fun v =>
        (Pseudocode.binOffsets I ε δ ξin.get θ.get v).map
          fun zl => st.1.get + Pseudocode.corrSample I ε δ ξin.get j x' y' v zl.1 zl.2 := by
      show (Pseudocode.sampleBin I ε δ ξin.get θ.get j x' y').bind (fun v =>
        (Pseudocode.binOffsets I ε δ ξin.get θ.get v).bind fun zl =>
          PMF.pure (st.1.get + Pseudocode.corrSample I ε δ ξin.get j x' y' v zl.1 zl.2)) = _
      rfl
    rw [hF]
    exact Analysis.tapeLaw_bind (g₂ := fun r s => post st r (Program.binOffsets C P (Coins.ofFinset s) r.1 r.2).val)
      (fun r : List SNat × ℕ => r.1.length ≤ C.nFree) hw₁ hP hw₂ hl₁ hl₂
  -- the loop of rounds
  have key : ∀ k, Analysis.Window cur Prod.snd (g k) ∧
      Analysis.TapeLaw Prod.snd (fun r : SRat × ℕ => r.1.get) (g k) (Pseudocode.loop F k init.1.get) := by
    intro k
    induction k with
    | zero => exact ⟨Analysis.window_const init le_rfl, Analysis.tapeLaw_const Prod.snd _ init⟩
    | succ k ih =>
      obtain ⟨hw, hl⟩ := ih
      have hgf : g (k + 1) = fun s => step (g k s) s := by
        funext s
        simp only [g, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hloop : Pseudocode.loop F (k + 1) init.1.get = (Pseudocode.loop F k init.1.get).bind (F k) := by
        unfold Pseudocode.loop
        rw [List.range_succ, List.foldlM_append]
        simp only [List.foldlM_cons, List.foldlM_nil]
        show (List.foldlM (fun b i => F i b) init.1.get (List.range k)).bind
          (fun b => (F k b).bind PMF.pure) = _
        simp only [PMF.bind_pure]
      rw [hgf, hloop]
      exact ⟨Analysis.window_bind (g₂ := fun st s => step st s) (fun _ => True) hw (fun _ => trivial)
          (fun st _ => (hstep k st).1),
        Analysis.tapeLaw_bind (g₂ := fun st s => step st s) (G₂ := F k) (fun _ => True) hw (fun _ => trivial)
          (fun st _ => (hstep k st).1) hl (fun st _ => (hstep k st).2)⟩
  have hfun : (fun s => (Program.corrAvg C P (Coins.ofFinset s) x y j cur).val) =
      fun s => ((SRat.div (g P.N s).1 P.Nq).val, (g P.N s).2) := funext hg
  have hlaw : Analysis.TapeLaw Prod.snd (fun r : SRat × ℕ => r.1.get)
      (fun s => (Program.corrAvg C P (Coins.ofFinset s) x y j cur).val)
      (Pseudocode.corrAvg I ε δ ξin.get θ.get j x' y') := by
    rw [hfun]
    have h0 : init.1.get = 0 := rfl
    have := Analysis.tapeLaw_map (fun st : SRat × ℕ => ((SRat.div st.1 P.Nq).val, st.2))
      (fun s : ℚ => s / (Pseudocode.oN I ε δ ξin.get θ.get : ℚ)) (π' := Prod.snd)
      (v' := fun r : SRat × ℕ => r.1.get) (fun _ => rfl)
      (fun st => by simp only [Interface.SRat.get_div, hNq, hN]) (key P.N).2
    rw [h0] at this
    have hps : Pseudocode.corrAvg I ε δ ξin.get θ.get j x' y' =
        (Pseudocode.loop F P.N 0).map fun s => s / (Pseudocode.oN I ε δ ξin.get θ.get : ℚ) := by
      rw [hN]; rfl
    rw [hps]
    exact this
  exact hlaw n T hT

end corrAvgTape

/-- The weight evaluator of Prop. weight-oracle, as the program runs it, has exactly the pseudocode oracle's output law. -/
theorem oracle_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (x y : List Cellcounting.Model.Operations.SNat) (j : ℕ) (ξin θ : Cellcounting.Model.Operations.SRat) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.oracle C (Arlib.Computation.Coins.ofFinset s) x y j ξin θ cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.oracle C (Arlib.Computation.Coins.ofFinset s) x y j ξin θ cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.oracle I ε δ (fun k => (x.getD k default).get) (fun k => (y.getD k default).get) j ξin.get θ.get).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- One implemented Metropolis transition (hold coin, proposal, oracle calls, dyadic acceptance test) has the pseudocode step law. The state is read as a Bool list viewed as a Finset. -/
theorem step_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (K : Cellcounting.Program.Chain) (hK : (K.p, K.pS.get, K.nsm, K.pairCell, K.cellFirst, K.smallB.map Cellcounting.Model.Operations.SNat.get, K.ξ.get, K.kAcc, K.kAccS.get) = (Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ)) (a : ℕ) (w : List (List Cellcounting.Model.Operations.SRat)) (S : List Bool) (hS : S.length = 2 * Cellcounting.Pseudocode.pSmall I ε δ) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.step C K (Arlib.Computation.Coins.ofFinset s) a w S cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.step C K (Arlib.Computation.Coins.ofFinset s) a w S cur).val; ((Finset.range (2 * Cellcounting.Pseudocode.pSmall I ε δ)).filter (fun e => r.1.getD e false = true), ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.step I ε δ a (fun (i l : ℕ) => ((w.getD i []).getD l default).get) ((Finset.range (2 * Cellcounting.Pseudocode.pSmall I ε δ)).filter (fun e => S.getD e false = true))).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- The program's initial transversal sampler, a uniform k_s and then a uniform subset for each small cell, has the pseudocode law μ₀. -/
theorem mu0_tape (I : Cellcounting.Instance) (ε δ : ℚ) (K : Cellcounting.Program.Chain) (hK : (K.p, K.pS.get, K.nsm, K.pairCell, K.cellFirst, K.smallB.map Cellcounting.Model.Operations.SNat.get, K.ξ.get, K.kAcc, K.kAccS.get) = (Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ)) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.mu0 K (Arlib.Computation.Coins.ofFinset s) cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.mu0 K (Arlib.Computation.Coins.ofFinset s) cur).val; ((Finset.range (2 * Cellcounting.Pseudocode.pSmall I ε δ)).filter (fun e => r.1.getD e false = true), ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.mu0 I ε δ).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- The capped staged restart, run as trace steps with a transition budget B_ret, has the pseudocode law, including the abort flag. -/
theorem restart_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (K : Cellcounting.Program.Chain) (hK : (K.p, K.pS.get, K.nsm, K.pairCell, K.cellFirst, K.smallB.map Cellcounting.Model.Operations.SNat.get, K.ξ.get, K.kAcc, K.kAccS.get) = (Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ)) (Ph : Cellcounting.Program.Phase) (hPh : (Ph.τ.get, Ph.Bret.get, Ph.BretN, Ph.Nav.get, Ph.NavN, Ph.Hn) = (Cellcounting.Pseudocode.τParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ)) (ws : List (List (List Cellcounting.Model.Operations.SRat))) (j : ℕ) (S0 : List Bool) (hS : S0.length = 2 * Cellcounting.Pseudocode.pSmall I ε δ) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.restart C K (Arlib.Computation.Coins.ofFinset s) Ph ws j S0 cur).val.cur + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.restart C K (Arlib.Computation.Coins.ofFinset s) Ph ws j S0 cur).val; ((⟨(Finset.range (2 * Cellcounting.Pseudocode.pSmall I ε δ)).filter (fun e => r.S.getD e false = true), r.stage, r.hits.get, r.used.get, r.finished, r.aborted⟩ : Cellcounting.Pseudocode.Restart), ((s.filter (fun i => r.cur ≤ i)).image (fun i => i - r.cur)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.restart I ε δ (fun (a i l : ℕ) => (((ws.getD a []).getD i []).getD l default).get) j ((Finset.range (2 * Cellcounting.Pseudocode.pSmall I ε δ)).filter (fun e => S0.getD e false = true))).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- The N_av observation steps of a phase, which accumulate the type counts and G_j, have the pseudocode observation law. -/
theorem observe_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (K : Cellcounting.Program.Chain) (hK : (K.p, K.pS.get, K.nsm, K.pairCell, K.cellFirst, K.smallB.map Cellcounting.Model.Operations.SNat.get, K.ξ.get, K.kAcc, K.kAccS.get) = (Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ)) (Ph : Cellcounting.Program.Phase) (hPh : (Ph.τ.get, Ph.Bret.get, Ph.BretN, Ph.Nav.get, Ph.NavN, Ph.Hn) = (Cellcounting.Pseudocode.τParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ)) (j : ℕ) (w : List (List Cellcounting.Model.Operations.SRat)) (S0 : List Bool) (hS : S0.length = 2 * Cellcounting.Pseudocode.pSmall I ε δ) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.observe C K (Arlib.Computation.Coins.ofFinset s) Ph j w S0 cur).val.cur + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.observe C K (Arlib.Computation.Coins.ofFinset s) Ph j w S0 cur).val; ((⟨(Finset.range (2 * Cellcounting.Pseudocode.pSmall I ε δ)).filter (fun e => r.S.getD e false = true), r.n0.get, fun (i l : ℕ) => ((r.nT.getD i []).getD l default).get, r.sumG.get⟩ : Cellcounting.Pseudocode.Obs), ((s.filter (fun i => r.cur ≤ i)).image (fun i => i - r.cur)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.observe I ε δ j (fun (i l : ℕ) => ((w.getD i []).getD l default).get) ((Finset.range (2 * Cellcounting.Pseudocode.pSmall I ε δ)).filter (fun e => S0.getD e false = true))).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- One annealing phase (initial draw, restart, observations, multiplier update eq:alg-multiplier-update, ratio product) has the pseudocode phase law. -/
theorem phase_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (K : Cellcounting.Program.Chain) (hK : (K.p, K.pS.get, K.nsm, K.pairCell, K.cellFirst, K.smallB.map Cellcounting.Model.Operations.SNat.get, K.ξ.get, K.kAcc, K.kAccS.get) = (Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ)) (Ph : Cellcounting.Program.Phase) (hPh : (Ph.τ.get, Ph.Bret.get, Ph.BretN, Ph.Nav.get, Ph.NavN, Ph.Hn) = (Cellcounting.Pseudocode.τParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ)) (j : ℕ) (ws : List (List (List Cellcounting.Model.Operations.SRat))) (prod : Cellcounting.Model.Operations.SRat) (ab : Bool) (hws : ab = false → ws.length = j + 1 ∧ ∀ t ∈ ws, t.length = Cellcounting.Pseudocode.pSmall I ε δ ∧ ∀ row ∈ t, row.length = Cellcounting.Pseudocode.pSmall I ε δ) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.phase C K (Arlib.Computation.Coins.ofFinset s) Ph j ⟨ws, prod, ab, cur⟩).val.cur + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.phase C K (Arlib.Computation.Coins.ofFinset s) Ph j ⟨ws, prod, ab, cur⟩).val; ((⟨fun (a i l : ℕ) => (((r.ws.getD a []).getD i []).getD l default).get, r.prod.get, r.aborted⟩ : Cellcounting.Pseudocode.RunState), ((s.filter (fun i => r.cur ≤ i)).image (fun i => i - r.cur)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.phase I ε δ j ⟨fun (a i l : ℕ) => (((ws.getD a []).getD i []).getD l default).get, prod.get, ab⟩).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

section AnnealRun

open Arlib.Computation Cellcounting.Program Cellcounting.Model.Operations Cellcounting.Analysis

/-- INTERNAL: a `p × p` table of stored multipliers. -/
def multShape (p : ℕ) (w : List (List SRat)) : Prop := w.length = p ∧ ∀ row ∈ w, row.length = p

/-- INTERNAL: an invariant preserved by every step of a fold. -/
theorem foldl_invariant {α β : Type} (Q : β → Prop) (f : β → α → β) (h : ∀ b a, Q b → Q (f b a)) :
    ∀ (l : List α) (b : β), Q b → Q (l.foldl f b) := by
  intro l; induction l with
  | nil => intro b hb; exact hb
  | cons a l ih => intro b hb; exact ih _ (h b a hb)

/-- INTERNAL: overwriting one entry keeps a `p × p` table. -/
theorem set2_multShape (p : ℕ) (M : List (List SRat)) (u v : ℕ) (a : SRat) (h : multShape p M) :
    multShape p (Program.set2 M u v a).val := by
  have e : (Program.set2 M u v a).val = M.set u ((M.getD u default).set v a) := by
    simp [Program.set2]
  rw [e]
  refine ⟨by rw [List.length_set]; exact h.1, fun row hrow => ?_⟩
  by_cases hu : u < M.length
  · rcases List.mem_or_eq_of_mem_set hrow with hm | rfl
    · exact h.2 row hm
    · rw [List.length_set, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, Option.getD_some]
      exact h.2 _ (List.getElem_mem hu)
  · rw [List.set_eq_of_length_le (by omega)] at hrow
    exact h.2 row hrow

/-- INTERNAL: the multiplier update `eq:alg-multiplier-update` keeps a `p × p` table. -/
theorem updateW_multShape (p : ℕ) (K : Chain) (w : List (List SRat)) (o : Obs) (h : multShape p w) :
    multShape p (updateW K w o).val := by
  show multShape p (Charged.repeatFor _ K.p w).val
  rw [val_repeatFor']
  refine foldl_invariant (multShape p) _ (fun b i hb => ?_) _ _ h
  rw [val_repeatFor']
  refine foldl_invariant (multShape p) _ (fun b' l hb' => ?_) _ _ hb
  simp only [Charged.val_bind]
  split
  · exact hb'
  · exact set2_multShape p _ _ _ _ hb'


/-- INTERNAL: a live run after `k` phases stores `k + 1` tables of shape `p × p` (the
`hws` hypothesis of `phase_tape`). -/
def runMultShape (p k : ℕ) (x : Run) : Prop :=
  x.aborted = false → x.ws.length = k + 1 ∧ ∀ t ∈ x.ws, multShape p t

/-- INTERNAL: a phase that is not the last one stores one more `p × p` table. -/
theorem phase_runMultShape (p : ℕ) (C : Ctx) (K : Chain) (tape : Coins ℕ) (Ph : Phase) (j : ℕ) (st : Run)
    (hj : j + 1 < Ph.Hn) (h : runMultShape p j st) : runMultShape p (j + 1) (phase C K tape Ph j st).val := by
  unfold phase
  split
  · intro hab; simp_all
  · simp only [Charged.val_bind]
    split
    · intro hab; simp_all
    · simp only [Charged.val_bind]
      split
      · simp only [Charged.val_bind, Cellcounting.Interface.val_idxLt, decide_eq_true hj, if_true]
        intro _
        obtain ⟨hl, hs⟩ := h (by simpa using ‹¬st.aborted = true›)
        simp only [Charged.val_pure, Cellcounting.Interface.val_push]
        have hw : multShape p (Model.Operations.get st.ws j).val := by
          rw [Cellcounting.Interface.val_get, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact hs _ (List.getElem_mem _)
        refine ⟨by rw [List.length_append, hl]; rfl, fun t ht => ?_⟩
        rcases List.mem_append.1 ht with ht | ht
        · exact hs t ht
        · rw [List.mem_singleton.1 ht]
          exact updateW_multShape p K _ _ hw
      · intro hab; simp_all


/-- INTERNAL: one more round of the pseudocode loop. -/
theorem pseudoLoop_succ {β : Type} (f : ℕ → β → PMF β) (k : ℕ) (b : β) :
    Pseudocode.loop f (k + 1) b = (Pseudocode.loop f k b).bind (f k) := by
  unfold Pseudocode.loop
  rw [List.range_succ, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil]
  show (List.foldlM (fun b i => f i b) b (List.range k)).bind (fun init => (f k init).bind PMF.pure) = _
  simp only [PMF.bind_pure]

/-- INTERNAL: zero rounds of the pseudocode loop. -/
theorem pseudoLoop_zero {β : Type} (f : ℕ → β → PMF β) (b : β) :
    Pseudocode.loop f 0 b = PMF.pure b := rfl

/-- INTERNAL: one more round of a charged loop, on values. -/
theorem repeatFor_succ_val {β : Type} (F : ℕ → β → Prog β) (k : ℕ) (b : β) :
    (Charged.repeatFor F (k + 1) b).val = (F k (Charged.repeatFor F k b).val).val := by
  rw [val_repeatFor', val_repeatFor', List.range_succ, List.foldl_append]
  rfl

end AnnealRun

/-- The full annealing run for p ≥ 1, H phases folded, has the pseudocode single-run law. Proved by induction on the phase index. -/
theorem annealRun_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (K : Cellcounting.Program.Chain) (hK : (K.p, K.pS.get, K.nsm, K.pairCell, K.cellFirst, K.smallB.map Cellcounting.Model.Operations.SNat.get, K.ξ.get, K.kAcc, K.kAccS.get) = (Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ)) (Ph : Cellcounting.Program.Phase) (hPh : (Ph.τ.get, Ph.Bret.get, Ph.BretN, Ph.Nav.get, Ph.NavN, Ph.Hn) = (Cellcounting.Pseudocode.τParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ)) (w0 : List (List Cellcounting.Model.Operations.SRat)) (hw0s : (w0.length, w0.map List.length) = (Cellcounting.Pseudocode.pSmall I ε δ, List.replicate (Cellcounting.Pseudocode.pSmall I ε δ) (Cellcounting.Pseudocode.pSmall I ε δ))) (hw0 : (fun (i l : ℕ) => ((w0.getD i []).getD l default).get) = Cellcounting.Pseudocode.w0 I ε δ) (C0 : Cellcounting.Model.Operations.SRat) (hC0 : C0.get = Cellcounting.Pseudocode.C0 I ε δ) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.annealRun C K (Arlib.Computation.Coins.ofFinset s) Ph w0 C0 cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.annealRun C K (Arlib.Computation.Coins.ofFinset s) Ph w0 C0 cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.annealRun I ε δ).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  have hp : K.p = Pseudocode.pSmall I ε δ := congrArg (fun t => t.1) hK
  have hHn : Ph.Hn = Pseudocode.HParam I ε δ := congrArg (fun t => t.2.2.2.2.2) hPh
  let view : Program.Run → Pseudocode.RunState := fun r =>
    ⟨fun (a i l : ℕ) => (((r.ws.getD a []).getD i []).getD l default).get, r.prod.get, r.aborted⟩
  let init : Program.Run := ⟨[w0], (Model.Operations.SRat.lit 1).val, false, cur⟩
  let g : ℕ → Finset ℕ → Program.Run := fun k s =>
    (Arlib.Computation.Charged.repeatFor (fun j st => Program.phase C K (Arlib.Computation.Coins.ofFinset s) Ph j st) k init).val
  have hinit : view init =
      ⟨fun a => if a = 0 then Pseudocode.w0 I ε δ else fun _ _ => 0, 1, false⟩ := by
    simp only [view, init, Cellcounting.Interface.SRat.get_lit]
    congr 1
    funext a i l
    rcases a with _ | a
    · exact congrFun (congrFun hw0 i) l
    · simp
  have hshape0 : runMultShape (Pseudocode.pSmall I ε δ) 0 init := by
    intro _
    refine ⟨rfl, fun t ht => ?_⟩
    rw [List.mem_singleton.1 ht]
    have h1 : w0.length = Pseudocode.pSmall I ε δ := congrArg Prod.fst hw0s
    have h2 : w0.map List.length = List.replicate (Pseudocode.pSmall I ε δ) (Pseudocode.pSmall I ε δ) :=
      congrArg Prod.snd hw0s
    refine ⟨h1, fun row hrow => ?_⟩
    have : row.length ∈ w0.map List.length := List.mem_map_of_mem hrow
    rw [h2] at this
    exact List.eq_of_mem_replicate this
  have key : ∀ k, k ≤ Ph.Hn →
      Analysis.Window cur Program.Run.cur (g k) ∧
      Analysis.TapeLaw Program.Run.cur view (g k) (Pseudocode.loop (Pseudocode.phase I ε δ) k (view init)) ∧
      ∀ s, k < Ph.Hn → runMultShape (Pseudocode.pSmall I ε δ) k (g k s) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Analysis.window_const init le_rfl, ?_, fun _ _ => hshape0⟩
      rw [pseudoLoop_zero]
      exact Analysis.tapeLaw_const Program.Run.cur view init
    | succ k ih =>
      intro hk
      obtain ⟨hw, hl, hsh⟩ := ih (by omega)
      have hg : ∀ s, g (k + 1) s = (Program.phase C K (Arlib.Computation.Coins.ofFinset s) Ph k (g k s)).val :=
        fun s => repeatFor_succ_val _ _ _
      have hgf : g (k + 1) = fun s => (Program.phase C K (Arlib.Computation.Coins.ofFinset s) Ph k (g k s)).val :=
        funext hg
      have hP : ∀ s, runMultShape (Pseudocode.pSmall I ε δ) k (g k s) := fun s => hsh s (by omega)
      refine ⟨?_, ?_, ?_⟩
      · rw [hgf]
        exact Analysis.window_bind (g₂ := fun x s => (Program.phase C K (Arlib.Computation.Coins.ofFinset s) Ph k x).val)
          (fun _ => True) hw (fun _ => trivial) (fun x _ => Analysis.phase_window C K Ph k x)
      · rw [hgf, pseudoLoop_succ]
        refine Analysis.tapeLaw_bind (g₂ := fun x s => (Program.phase C K (Arlib.Computation.Coins.ofFinset s) Ph k x).val)
          (G₂ := Pseudocode.phase I ε δ k) (runMultShape (Pseudocode.pSmall I ε δ) k) hw hP
          (fun x _ => Analysis.phase_window C K Ph k x) hl (fun x hx => ?_)
        obtain ⟨ws, prod, ab, c⟩ := x
        intro n T hT
        exact phase_tape I ε δ C hC K hK Ph hPh k ws prod ab
          (fun hab => ⟨(hx hab).1, fun t ht => (hx hab).2 t ht⟩) c n T hT
      · intro s hk'
        rw [hg]
        exact phase_runMultShape _ C K _ Ph k _ (by omega) (hP s)
  obtain ⟨-, hl, -⟩ := key Ph.Hn le_rfl
  let post : Program.Run → Model.Operations.SRat × ℕ := fun st =>
    (if st.aborted then (Model.Operations.SRat.lit 0).val else (Model.Operations.SRat.mul C0 st.prod).val, st.cur)
  have hval : ∀ s, (Program.annealRun C K (Arlib.Computation.Coins.ofFinset s) Ph w0 C0 cur).val = post (g Ph.Hn s) := by
    intro s
    simp only [Program.annealRun, Arlib.Computation.Charged.val_bind, post, g, init]
    split <;> rfl
  have hl' := Analysis.tapeLaw_map (π' := Prod.snd) (v' := fun r : Model.Operations.SRat × ℕ => r.1.get) post
    (fun st => if st.aborted then 0 else Pseudocode.C0 I ε δ * st.prod)
    (fun _ => rfl) (fun a => by
      simp only [post, view]
      split <;> simp [hC0]) hl
  have := hl' n T (fun s => by show (post (g Ph.Hn s)).2 + n ≤ T; rw [← hval]; exact hT s)
  simp only [hval]
  rw [Pseudocode.annealRun, ← hinit, ← hHn]
  exact this

/-- In the p = 0 branch the single run, one oracle call at h_H(∅), has the pseudocode law. -/
theorem zeroRun_tape (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (Hn : ℕ) (hH : Hn = Cellcounting.Pseudocode.HParam I ε δ) (εS : Cellcounting.Model.Operations.SRat) (hε : εS.get = ε) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.zeroRun C Hn εS (Arlib.Computation.Coins.ofFinset s) cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.zeroRun C Hn εS (Arlib.Computation.Coins.ofFinset s) cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.zeroRun I ε δ).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  sorry

/-- R repetitions run on consecutive tape segments are independent copies of the single-run law, which is the independence used by the median step. -/
theorem repeatRuns_tape (F : Arlib.Computation.Coins ℕ → ℕ → Cellcounting.Program.Prog (Cellcounting.Model.Operations.SRat × ℕ)) (G : PMF ℚ) (hF : ∀ cur n T : ℕ, (∀ s : Finset ℕ, (F (Arlib.Computation.Coins.ofFinset s) cur).val.2 + n ≤ T) → (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (F (Arlib.Computation.Coins.ofFinset s) cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = G.bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s')))) (R cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], cur)).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], cur)).val; (r.1.map Cellcounting.Model.Operations.SRat.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.repeatRuns R G).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  -- DISPROVED: Cellcounting.Analysis.repeatRuns_tape_false
  -- REPAIR: (hW : ∀ cur : ℕ, Cellcounting.Analysis.Window cur Prod.snd (fun s : Finset ℕ => (F (Arlib.Computation.Coins.ofFinset s) cur).val))
  sorry

/-- INTERNAL: `repeatRuns_tape` with the window hypothesis `hW` its `REPAIR` line adds:
each run reads only the bits between its start and end cursors. TEXLINE: sections/algorithm.tex:670-690 -/
theorem repeatRuns_tape_of_window (F : Arlib.Computation.Coins ℕ → ℕ → Cellcounting.Program.Prog (Cellcounting.Model.Operations.SRat × ℕ)) (G : PMF ℚ) (hF : ∀ cur n T : ℕ, (∀ s : Finset ℕ, (F (Arlib.Computation.Coins.ofFinset s) cur).val.2 + n ≤ T) → (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (F (Arlib.Computation.Coins.ofFinset s) cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = G.bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s')))) (hW : ∀ cur : ℕ, Cellcounting.Analysis.Window cur Prod.snd (fun s : Finset ℕ => (F (Arlib.Computation.Coins.ofFinset s) cur).val)) (R cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], cur)).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], cur)).val; (r.1.map Cellcounting.Model.Operations.SRat.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.repeatRuns R G).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  let step : List Model.Operations.SRat × ℕ → Finset ℕ → List Model.Operations.SRat × ℕ :=
    fun x s => (x.1 ++ [(F (Arlib.Computation.Coins.ofFinset s) x.2).val.1],
      (F (Arlib.Computation.Coins.ofFinset s) x.2).val.2)
  let g : ℕ → Finset ℕ → List Model.Operations.SRat × ℕ := fun k s =>
    (Arlib.Computation.Charged.repeatFor (fun _ (st : List Model.Operations.SRat × ℕ) =>
      ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2
           let outs ← Model.Operations.push st.1 z
           pure (outs, c')) : Program.Prog (List Model.Operations.SRat × ℕ))) k ([], cur)).val
  let view : List Model.Operations.SRat × ℕ → List ℚ := fun r => r.1.map Model.Operations.SRat.get
  have hstep : ∀ k s, g (k + 1) s = step (g k s) s := by
    intro k s
    exact repeatFor_succ_val _ _ _
  have key : ∀ k, Analysis.Window cur Prod.snd (g k) ∧
      Analysis.TapeLaw Prod.snd view (g k) (Pseudocode.repeatRuns k G) := by
    intro k
    induction k with
    | zero =>
      exact ⟨Analysis.window_const ([], cur) le_rfl, Analysis.tapeLaw_const Prod.snd view ([], cur)⟩
    | succ k ih =>
      have hgf : g (k + 1) = fun s => step (g k s) s := funext (hstep k)
      have hw2 : ∀ x : List Model.Operations.SRat × ℕ, Analysis.Window x.2 Prod.snd (step x) :=
        fun x => Analysis.window_map (fun r : Model.Operations.SRat × ℕ => (x.1 ++ [r.1], r.2)) (fun _ => rfl) (hW x.2)
      refine ⟨?_, ?_⟩
      · rw [hgf]
        exact Analysis.window_bind (g₂ := step) (fun _ => True) ih.1 (fun _ => trivial)
          (fun x _ => hw2 x)
      · rw [hgf]
        show Analysis.TapeLaw Prod.snd view (fun s => step (g k s) s)
          (Pseudocode.loop (fun _ l => G.map fun z => l ++ [z]) (k + 1) [])
        rw [pseudoLoop_succ]
        refine Analysis.tapeLaw_bind (g₂ := step)
          (G₂ := fun l => G.map fun z => l ++ [z]) (fun _ => True) ih.1 (fun _ => trivial)
          (fun x _ => hw2 x) ih.2 (fun x _ => ?_)
        exact Analysis.tapeLaw_map (π := Prod.snd) (v := fun r : Model.Operations.SRat × ℕ => r.1.get)
          (fun r => (x.1 ++ [r.1], r.2)) (fun z => view x ++ [z]) (fun _ => rfl)
          (fun r => by simp [view]) (fun n T hT => hF x.2 n T hT)
  exact (key R).2 n T hT

/-- The program's median selection by exact comparisons returns the pseudocode order statistic. -/
theorem orderStat_val (outs : List Cellcounting.Model.Operations.SRat) (idx : ℕ) : (Cellcounting.Program.orderStat outs idx).val.get = Cellcounting.Pseudocode.orderStat (outs.map Cellcounting.Model.Operations.SRat.get) idx := by
  sorry

/-- The program's preliminary deterministic flow test decides exactly the pseudocode feasibility predicate. -/
theorem feasible_val (m n : ℕ) (r c : List Cellcounting.Model.Operations.SNat) (b : List (List Cellcounting.Model.Operations.SNat)) (hr : r.length = m) (hc : c.length = n) : (Cellcounting.Program.feasible m n r c b).val = decide (Cellcounting.Pseudocode.feasible ⟨m, n, fun i => (r.getD i.val default).get, fun j => (c.getD j.val default).get, fun i j => ((b.getD i.val []).getD j.val default).get⟩) := by
  sorry

/-- On feasible input, the program's tightening step produces the pseudocode's tightened margins and retained cells. -/
theorem tighten_view (I : Cellcounting.Instance) (hfeas : Cellcounting.Pseudocode.feasible I) : let T := (Cellcounting.Program.tighten I.m I.n (Cellcounting.Program.readList (List.ofFn I.r)).val (Cellcounting.Program.readList (List.ofFn I.c)).val (Cellcounting.Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val).val; (T.rows.map Cellcounting.Model.Operations.SNat.get, T.cols.map Cellcounting.Model.Operations.SNat.get, T.cells.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get))) = ((List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.retained I) := by
  sorry

/-- The program computes the scale parameters of eq:parameters exactly as the pseudocode defines them. -/
theorem params_view (I : Cellcounting.Instance) (ε δ : ℚ) : let Pm := (Cellcounting.Program.params I.m I.n (Cellcounting.Program.inputLen I ε δ).val (Cellcounting.Model.Operations.SRat.lit ε).val).val; (Pm.d.get, Pm.K.get, Pm.A.get, Pm.B.get, Pm.W.get, Pm.H.get) = (Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.KParam I ε δ, Cellcounting.Pseudocode.AParam I ε δ, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.WParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ) := by
  sorry

/-- The program's context (small/free split, forest, elimination order, M_f) matches the pseudocode's derived data field by field. This discharges the hC hypothesis of every tape lemma. -/
theorem buildCtx_view (I : Cellcounting.Instance) (ε δ : ℚ) (hfeas : Cellcounting.Pseudocode.feasible I) : let C := (Cellcounting.Program.buildCtx I.m I.n (Cellcounting.Program.tighten I.m I.n (Cellcounting.Program.readList (List.ofFn I.r)).val (Cellcounting.Program.readList (List.ofFn I.c)).val (Cellcounting.Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val).val (Cellcounting.Program.params I.m I.n (Cellcounting.Program.inputLen I ε δ).val (Cellcounting.Model.Operations.SRat.lit ε).val).val).val; (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ)) := by
  exact Analysis.buildCtx_view_of I ε δ _ _ (tighten_view I hfeas) (params_view I ε δ)

/-- The program's chain and phase parameters, initial multipliers w⁽⁰⁾ (closed form of lem:initialization) and C(0) equal the pseudocode's values. -/
theorem chainSetup_view (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (Pm : Cellcounting.Program.Params) (hPm : (Pm.d.get, Pm.K.get, Pm.A.get, Pm.B.get, Pm.W.get, Pm.H.get) = (Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.KParam I ε δ, Cellcounting.Pseudocode.AParam I ε δ, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.WParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ)) (pS : Cellcounting.Model.Operations.SNat) (hp : pS.get = Cellcounting.Pseudocode.pSmall I ε δ) (εS : Cellcounting.Model.Operations.SRat) (hε : εS.get = ε) : let r := (Cellcounting.Program.chainSetup C Pm pS εS).val; ((r.1.p, r.1.pS.get, r.1.nsm, r.1.pairCell, r.1.cellFirst, r.1.smallB.map Cellcounting.Model.Operations.SNat.get, r.1.ξ.get, r.1.kAcc, r.1.kAccS.get), (r.2.1.τ.get, r.2.1.Bret.get, r.2.1.BretN, r.2.1.Nav.get, r.2.1.NavN, r.2.1.Hn), (fun (i l : ℕ) => ((r.2.2.1.getD i []).getD l default).get), (r.2.2.1.length, r.2.2.1.map List.length), r.2.2.2.get) = ((Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ), (Cellcounting.Pseudocode.τParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ), Cellcounting.Pseudocode.w0 I ε δ, (Cellcounting.Pseudocode.pSmall I ε δ, List.replicate (Cellcounting.Pseudocode.pSmall I ε δ) (Cellcounting.Pseudocode.pSmall I ε δ)), Cellcounting.Pseudocode.C0 I ε δ) := by
  exact Analysis.chainSetup_view_of I ε δ C hC Pm hPm pS hp εS hε

/-- Unfolds the output law in Model/Run: it is the pushforward of a uniform finite coin tape through the program's estimate. -/
theorem output_eq_map_estimate (I : Cellcounting.Instance) (ε δ : ℚ) : Cellcounting.output I ε δ = (Cellcounting.tapeHeads (Cellcounting.tapeLength I ε δ)).map (fun (s : Finset ℕ) => Cellcounting.Interface.estimate I ε δ (Arlib.Computation.Coins.ofFinset s)) := by
  sorry

/-- On infeasible input the program returns zero for every coin sequence. This is the theorem's 'zero on every execution' clause. -/
theorem estimate_infeasible (I : Cellcounting.Instance) (ε δ : ℚ) (h : ¬ Cellcounting.Pseudocode.feasible I) (c : Arlib.Computation.Coins ℕ) : Cellcounting.Interface.estimate I ε δ c = 0 := by
  sorry

/-- On feasible input, the law of the program's estimate on any tape long enough to cover every read equals the pseudocode fpras law. It splits on p = 0 versus p ≥ 1. -/
theorem estimate_feasible_law (I : Cellcounting.Instance) (ε δ : ℚ) (hfeas : Cellcounting.Pseudocode.feasible I) (T : ℕ) (hT : ∀ s : Finset ℕ, Cellcounting.Interface.flipsRead I ε δ s ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => Cellcounting.Interface.estimate I ε δ (Arlib.Computation.Coins.ofFinset s)) = Cellcounting.Pseudocode.fpras I ε δ := by
  sorry

/-- INTERNAL: the program's input reader stores each number as its literal. Used to show
that the instance `feasible_val` reconstructs from the encoded input is `I` itself. -/
theorem readList_val (l : List ℕ) :
    (Program.readList l).val = l.map (fun k => (Model.Operations.SNat.lit k).val) := by
  unfold Program.readList
  rw [Analysis.val_foldl']
  have h : ∀ (l : List ℕ) (acc : List Model.Operations.SNat), l.foldl (fun b a => (do
      let x ← Model.Operations.SNat.lit a
      Model.Operations.push b x : Program.Prog (List Model.Operations.SNat)).val) acc =
      acc ++ l.map (fun k => (Model.Operations.SNat.lit k).val) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih => intro acc; rw [List.foldl_cons, ih]; simp
  simpa using h l []

/-- INTERNAL: the matrix reader stores each row as its list of literals. -/
theorem readMatrix_val (rows : List (List ℕ)) :
    (Program.readMatrix rows).val =
      rows.map (fun row => row.map (fun k => (Model.Operations.SNat.lit k).val)) := by
  unfold Program.readMatrix
  rw [Analysis.val_foldl']
  have h : ∀ (l : List (List ℕ)) (acc : List (List Model.Operations.SNat)), l.foldl
      (fun b a => (do
        let xs ← Program.readList a
        Model.Operations.push b xs : Program.Prog (List (List Model.Operations.SNat))).val) acc =
      acc ++ l.map (fun row => row.map (fun k => (Model.Operations.SNat.lit k).val)) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a l ih => intro acc; rw [List.foldl_cons, ih]; simp [← readList_val]
  simpa using h rows []

/-- INTERNAL: reading back entry `i` of an encoded vector gives its `i`-th component. -/
theorem readList_ofFn_getD {k : ℕ} (f : Fin k → ℕ) (i : Fin k) :
    ((Program.readList (List.ofFn f)).val.getD i.val default).get = f i := by
  rw [readList_val, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_ofFn,
    dif_pos i.isLt]
  simp

/-- INTERNAL: the instance `feasible_val` rebuilds from the encoded input of `I` is `I`. -/
theorem decode_input (I : Instance) :
    (⟨I.m, I.n,
      fun i => ((Program.readList (List.ofFn I.r)).val.getD i.val default).get,
      fun j => ((Program.readList (List.ofFn I.c)).val.getD j.val default).get,
      fun i j => (((Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val.getD
        i.val []).getD j.val default).get⟩ : Instance) = I := by
  obtain ⟨m, n, r, c, b⟩ := I
  have hb : ∀ (i : Fin m) (j : Fin n), (((Program.readMatrix (List.ofFn fun i => List.ofFn fun j =>
      b i j)).val.getD i.val []).getD j.val default).get = b i j := by
    intro i j
    rw [readMatrix_val, List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
      List.getElem?_ofFn, dif_pos i.isLt]
    simp only [Option.map_some, Option.getD_some]
    rw [← readList_val]
    exact readList_ofFn_getD (fun j => b i j) j
  simp only [readList_ofFn_getD, hb]

/-- The bridge: the output law of the implemented program, run through Program.feasible on the encoded input and then the pipeline, is exactly the pseudocode fpras law, and the program's feasibility gate decides the pseudocode predicate. The analysis rewrites through the first conjunct. The second conjunct comes from feasible_val once readList/readMatrix are shown to round-trip. -/
theorem output_eq_fpras (I : Cellcounting.Instance) (ε δ : ℚ) : Cellcounting.output I ε δ = Cellcounting.Pseudocode.fpras I ε δ ∧ (Cellcounting.Program.feasible I.m I.n (Cellcounting.Program.readList (List.ofFn I.r)).val (Cellcounting.Program.readList (List.ofFn I.c)).val (Cellcounting.Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val).val = decide (Cellcounting.Pseudocode.feasible I) := by
  refine ⟨?_, ?_⟩
  · rw [output_eq_map_estimate]
    by_cases hfeas : Pseudocode.feasible I
    · refine estimate_feasible_law I ε δ hfeas _ fun s => ?_
      rw [Interface.tapeLength_eq]
      exact le_csSup (Analysis.flipsRead_bddAbove I ε δ) (Set.mem_range_self s)
    · have h0 : (fun s : Finset ℕ => Interface.estimate I ε δ (Arlib.Computation.Coins.ofFinset s)) =
          Function.const _ 0 := funext fun s => estimate_infeasible I ε δ hfeas _
      rw [h0, PMF.map_const, Pseudocode.fpras, if_neg hfeas]
  · have h := feasible_val I.m I.n (Program.readList (List.ofFn I.r)).val
      (Program.readList (List.ofFn I.c)).val
      (Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val
      (by simp [readList_val]) (by simp [readList_val])
    rw [h, decode_input]

end Cellcounting

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r5 · proved · `dyadicDraw_tape` from `uniformBits_tape` via `tapeLaw_map` and `size_pred_eq_clog`; `uniformBits_tape` outright via `Analysis.bitsVal_tape` (new `Analysis/UniformBitsTape.lean`)
* r4 · proved · `corrAvg_tape` from `sampleBin_tape`, `binOffsets_tape`, `penalty_val`, `pow2Approx_val`; bin-vector length invariant `sampleBin_val_length_le` makes `binPoint` views agree
* r3 · proved · `binOffsets_tape` from `dyadicDraw_tape` (per-cell law via `tapeLaw_map`, rounds via `tapeLaw_bind`); `hC` supplies `free`, `nFree`, `d`, `B`, `H`
* r2 · assembled · `output_eq_fpras` from its four sibling rungs; tape-length attainment by `Analysis.flipsRead_bddAbove` (finite range over tapes), input round-trip proved here
* r1 · proved · `annealRun_tape` from `phase_tape`, `phase_window` and the `p × p` shape invariant; `repeatRuns_tape` disproved by `Analysis.repeatRuns_tape_false`, repaired form `repeatRuns_tape_of_window` proved
-/
