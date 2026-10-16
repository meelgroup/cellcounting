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
import Cellcounting.Analysis.CursorFlips
import Cellcounting.Analysis.NetworkVal
import Cellcounting.Analysis.MaxFlowCorrect
import Cellcounting.Analysis.TransportFlowIff
import Cellcounting.Analysis.FeasibleValProof
import Cellcounting.Analysis.CellMinVal
import Cellcounting.Analysis.CellMaxVal
import Cellcounting.Analysis.Mu0InnerVal

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
`estimate_feasible_law` is proved from `repeatRuns_tape_of_window` (through
`median_tape_law`), `zeroRun_tape`, `annealRun_tape`, the run windows of
`Analysis/PhaseWindow.lean`, `buildCtx_view`, `params_view`, `chainSetup_view`,
`feasible_val` and `orderStat_val`.  Its hypothesis bounds the fair bits *paid for*
(`flipsRead`), while the tape lemmas need the final *cursor*; `Analysis/CursorFlips.lean`
proves the cursor never runs ahead of the flips paid for (`Analysis.CurLe`), and
`cost_flip_bind_right`/`_left` place the runs' flips inside those of `Program.fpras`.
`output_eq_map_estimate` is the definition of `output` with its maps composed.
`estimate_infeasible` is the infeasible branch of `Program.fpras`, read through `feasible_val`.
`feasible_val` is `Analysis.feasible_val_proof` (`Analysis/FeasibleValProof.lean`), proved from `Analysis.network_val` (the program builds the network of
`sections/scales.tex:8-11`, `Analysis/NetworkVal.lean`), `Analysis.maxFlow_correct` (the
Edmonds–Karp loop returns the maximum flow value, `Analysis/MaxFlowCorrect.lean`, which rests
on the cited bound `Analysis.edmondsKarp_bound`) and the transport lemmas of
`Analysis/TransportFlowIff.lean` (a flow of value `Σ r` is a feasible table).
`orderStat_val` is proved outright: `Program.insertAsc` builds `insAscList`, whose values
are a sorted permutation, hence the sorted multiset of `Pseudocode.orderStat`.
`params_view` is a formula chase through `Program.params`.
`tighten_view` is proved from `Analysis.cellMin_val` and `Analysis.cellMax_val`
(`Analysis/CellMinVal.lean`, `Analysis/CellMaxVal.lean`: the binary searches return
`cellLow`/`cellHigh`, through the flow test on modified bounds) and a loop invariant over the
row/column double loop of `Program.tighten` (`tightenBody`, `TInv` inside the proof).
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

open Cellcounting.Program Cellcounting.Model Cellcounting.Model.Operations Arlib.Computation Cellcounting.Interface Cellcounting.Analysis in
/-- The program's initial transversal sampler, a uniform k_s and then a uniform subset for each small cell, has the pseudocode law μ₀. -/
theorem mu0_tape (I : Cellcounting.Instance) (ε δ : ℚ) (K : Cellcounting.Program.Chain) (hK : (K.p, K.pS.get, K.nsm, K.pairCell, K.cellFirst, K.smallB.map Cellcounting.Model.Operations.SNat.get, K.ξ.get, K.kAcc, K.kAccS.get) = (Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ)) (cur n T : ℕ) (hT : ∀ s : Finset ℕ, (Cellcounting.Program.mu0 K (Arlib.Computation.Coins.ofFinset s) cur).val.2 + n ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (Cellcounting.Program.mu0 K (Arlib.Computation.Coins.ofFinset s) cur).val; ((Finset.range (2 * Cellcounting.Pseudocode.pSmall I ε δ)).filter (fun e => r.1.getD e false = true), ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = (Cellcounting.Pseudocode.mu0 I ε δ).bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s'))) := by
  have hK0 := hK
  simp only [Prod.mk.injEq] at hK0
  obtain ⟨hp, -, hnsm, -, hcf, hsb, hξ, -, -⟩ := hK0
  have hcellFirst : ∀ s' < Pseudocode.nSmall I ε δ,
      K.cellFirst.getD s' default = Pseudocode.cellFirst I ε δ s' := by
    intro s' hs'
    rw [hcf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (hnsm ▸ hs')]
    rfl
  have hsmallB : ∀ s' < Pseudocode.nSmall I ε δ,
      (K.smallB.getD s' default).get = Pseudocode.smallB I ε δ s' := by
    intro s' hs'
    have e1 : (K.smallB.getD s' default).get =
        (K.smallB.map SNat.get).getD s' (SNat.get default) :=
      (List.getD_map K.smallB default (n := s') SNat.get).symm
    rw [e1, hsb, Interface.SNat.get_default, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (hnsm ▸ hs')]
    rfl
  have hcellFirst_bound : ∀ s' < Pseudocode.nSmall I ε δ,
      Pseudocode.cellFirst I ε δ s' + Pseudocode.smallB I ε δ s' ≤ Pseudocode.pSmall I ε δ := by
    intro s' hs'
    have h1 : Pseudocode.cellFirst I ε δ (s' + 1) = Pseudocode.cellFirst I ε δ s' + Pseudocode.smallB I ε δ s' :=
      Mu0Law.cellFirst_succ I ε δ s'
    have h2 : Pseudocode.cellFirst I ε δ (s' + 1) ≤ Pseudocode.cellFirst I ε δ (Pseudocode.nSmall I ε δ) :=
      Mu0Law.cellFirst_mono I ε δ (by omega)
    rw [Mu0Law.cellFirst_nSmall] at h2
    omega
  set p := Pseudocode.pSmall I ε δ with hpdef
  set nsm := Pseudocode.nSmall I ε δ with hnsmdef
  set ξ := Pseudocode.ξParam I ε δ with hξdef
  let v : List Bool × ℕ → Finset ℕ := fun r => (Finset.range (2 * p)).filter (fun e => r.1.getD e false = true)
  let S0 : List Bool := List.replicate (2 * K.p) false
  have hS0len : S0.length = 2 * p := by simp [S0, hp]
  have hv0 : v (S0, cur) = ∅ := by
    apply Finset.filter_false_of_mem
    intro e _
    simp [S0]
  let F : ℕ → Finset ℕ → PMF (Finset ℕ) := fun s' S => do
    let k ← Pseudocode.dyadicDraw (Pseudocode.smallB I ε δ s' + 1) ξ
    let rank ← Pseudocode.dyadicDraw (Nat.choose (Pseudocode.smallB I ε δ s') k) ξ
    pure (S ∪ Mu0Law.blk (Pseudocode.cellFirst I ε δ s') (Pseudocode.smallB I ε δ s')
      (Pseudocode.unrank (Pseudocode.smallB I ε δ s') k rank))
  have hFmu0 : Pseudocode.mu0 I ε δ = Pseudocode.loop F nsm ∅ := rfl
  let step : ℕ → List Bool × ℕ → Finset ℕ → List Bool × ℕ := fun s' st s =>
    let b := (Operations.get K.smallB s').val
    let first := (Operations.get K.cellFirst s').val
    let b1 := (SNat.add b (SNat.lit 1).val).val
    let dr1 := (dyadicDraw (Coins.ofFinset s) b1 K.ξ st.2).val
    let cnt := (binom b dr1.1).val
    let dr2 := (dyadicDraw (Coins.ofFinset s) cnt K.ξ dr1.2).val
    let st' := (Charged.repeatFor (innerStep b first) b.index.val (st.1, dr1.1, dr2.1)).val
    (st'.1, dr2.2)
  have hg : ∀ s, (Program.mu0 K (Coins.ofFinset s) cur).val =
      (List.range K.nsm).foldl (fun st s' => step s' st s) (S0, cur) := by
    intro s
    unfold Program.mu0
    simp only [Charged.val_bind, Interface.val_replicate, Interface.SNat.get_lit,
      Analysis.val_repeatFor']
    congr 1
    funext st s'
    simp only [step, Charged.val_bind, Charged.val_pure, SNat.val_index, Analysis.val_repeatFor']
    unfold innerStep
    rfl
  
  have hstep : ∀ (s' : ℕ) (st : List Bool × ℕ), s' < nsm → st.1.length = 2 * p →
      Analysis.Window st.2 Prod.snd (fun s => step s' st s) ∧
      Analysis.TapeLaw Prod.snd v (fun s => step s' st s) (F s' (v st)) := by
    intro s' st hs' hstlen
    have hbget : (Operations.get K.smallB s').val.get = Pseudocode.smallB I ε δ s' := by
      rw [Interface.val_get]; exact hsmallB s' hs'
    have hfirsteq : (Operations.get K.cellFirst s').val = Pseudocode.cellFirst I ε δ s' := by
      rw [Interface.val_get]; exact hcellFirst s' hs'
    have hbfp := hcellFirst_bound s' hs'
    constructor
    · show Analysis.Window st.2 Prod.snd (fun s => step s' st s)
      simp only [step]
      set b := (Operations.get K.smallB s').val with hbdef
      set first := (Operations.get K.cellFirst s').val with hfdef
      refine Analysis.window_bind (g₂ := fun (dr1 : SNat × ℕ) (s : Finset ℕ) =>
          let cnt := (binom b dr1.1).val
          let dr2 := (dyadicDraw (Coins.ofFinset s) cnt K.ξ dr1.2).val
          let st' := (Charged.repeatFor (innerStep b first) b.index.val (st.1, dr1.1, dr2.1)).val
          (st'.1, dr2.2))
        (fun _ : SNat × ℕ => True) (dyadicDraw_window _ _ _) (fun _ => trivial) fun dr1 _ => ?_
      exact Analysis.window_bind (g₂ := fun (dr2 : SNat × ℕ) (_ : Finset ℕ) =>
          ((Charged.repeatFor (innerStep b first) b.index.val (st.1, dr1.1, dr2.1)).val.1, dr2.2))
        (fun _ : SNat × ℕ => True) (dyadicDraw_window _ _ _) (fun _ => trivial)
        fun dr2 _ => Analysis.window_const _ le_rfl
    · simp only [step]
      set b := (Operations.get K.smallB s').val with hbdef
      set first := (Operations.get K.cellFirst s').val with hfdef
      have hb1 : (SNat.add b (SNat.lit 1).val).val.get = Pseudocode.smallB I ε δ s' + 1 := by
        simp [Interface.SNat.get_add, Interface.SNat.get_lit, hbget]
      have hP1 : ∀ s, ((dyadicDraw (Coins.ofFinset s) (SNat.add b (SNat.lit 1).val).val K.ξ st.2).val).1.get ≤ b.get := by
        intro s
        have := dyadicDraw_lt (Coins.ofFinset s) (SNat.add b (SNat.lit 1).val).val K.ξ st.2 (by
          simp [Interface.SNat.get_add, Interface.SNat.get_lit])
        simp only [Interface.SNat.get_add, Interface.SNat.get_lit] at this
        omega
      have hd1 : Analysis.TapeLaw Prod.snd (fun r : SNat × ℕ => r.1.get)
          (fun s => (dyadicDraw (Coins.ofFinset s) (SNat.add b (SNat.lit 1).val).val K.ξ st.2).val)
          (Pseudocode.dyadicDraw (Pseudocode.smallB I ε δ s' + 1) ξ) := by
        rw [← hb1, ← hξ]
        exact dyadicDraw_tape (SNat.add b (SNat.lit 1).val).val K.ξ st.2
      have hw1 : Analysis.Window st.2 Prod.snd
          (fun s => (dyadicDraw (Coins.ofFinset s) (SNat.add b (SNat.lit 1).val).val K.ξ st.2).val) :=
        dyadicDraw_window _ _ _
      refine Analysis.tapeLaw_bind (g₂ := fun (dr1 : SNat × ℕ) (s : Finset ℕ) =>
          let cnt := (binom b dr1.1).val
          let dr2 := (dyadicDraw (Coins.ofFinset s) cnt K.ξ dr1.2).val
          let st' := (Charged.repeatFor (innerStep b first) b.index.val (st.1, dr1.1, dr2.1)).val
          (st'.1, dr2.2))
        (fun kr : SNat × ℕ => kr.1.get ≤ b.get) hw1 hP1 ?_ hd1 ?_
      · intro x hx
        exact Analysis.window_bind (g₂ := fun (dr2 : SNat × ℕ) (_ : Finset ℕ) =>
            ((Charged.repeatFor (innerStep b first) b.index.val (st.1, x.1, dr2.1)).val.1, dr2.2))
          (fun _ : SNat × ℕ => True) (dyadicDraw_window _ _ _) (fun _ => trivial)
          fun dr2 _ => Analysis.window_const _ le_rfl
      · intro x hx
        have hcnt : (binom b x.1).val.get = Nat.choose (Pseudocode.smallB I ε δ s') x.1.get := by
          rw [binom_val b x.1 hx, hbget]
        have hP2 : ∀ s, ((dyadicDraw (Coins.ofFinset s) (binom b x.1).val K.ξ x.2).val).1.get <
            (binom b x.1).val.get := by
          intro s
          exact dyadicDraw_lt (Coins.ofFinset s) (binom b x.1).val K.ξ x.2 (by rw [hcnt]; exact Nat.choose_pos (hbget ▸ hx))
        have hd2 : Analysis.TapeLaw Prod.snd (fun r : SNat × ℕ => r.1.get)
            (fun s => (dyadicDraw (Coins.ofFinset s) (binom b x.1).val K.ξ x.2).val)
            (Pseudocode.dyadicDraw (Nat.choose (Pseudocode.smallB I ε δ s') x.1.get) ξ) := by
          rw [← hcnt, ← hξ]
          exact dyadicDraw_tape (binom b x.1).val K.ξ x.2
        refine Analysis.tapeLaw_bind (g₂ := fun (dr2 : SNat × ℕ) (_ : Finset ℕ) =>
            ((Charged.repeatFor (innerStep b first) b.index.val (st.1, x.1, dr2.1)).val.1, dr2.2))
          (fun dr2 : SNat × ℕ => dr2.1.get < (binom b x.1).val.get)
          (dyadicDraw_window _ _ _) hP2 (fun dr2 _ => Analysis.window_const _ le_rfl) hd2 ?_
        intro dr2 hdr2
        have hval : v ((Charged.repeatFor (innerStep b first) b.index.val (st.1, x.1, dr2.1)).val.1, dr2.2) =
            v st ∪ Mu0Law.blk (Pseudocode.cellFirst I ε δ s') (Pseudocode.smallB I ε δ s')
              (Pseudocode.unrank (Pseudocode.smallB I ε δ s') x.1.get dr2.1.get) := by
          rw [← hbget, ← hfirsteq]
          show (Finset.range (2 * p)).filter
              (fun e => (Charged.repeatFor (innerStep b first) b.index.val
                (st.1, x.1, dr2.1)).val.1.getD e false = true) =
            (Finset.range (2 * p)).filter (fun e => st.1.getD e false = true) ∪ _
          rw [SNat.val_index]
          exact mu0Inner_blk b first p x.1 dr2.1 st.1 hx ((binom_val b x.1 hx) ▸ hdr2) hstlen.ge
            (by rw [hfirsteq, hbget]; exact hbfp)
        rw [← hval]
        exact Analysis.tapeLaw_const Prod.snd v _
  have hsteplen : ∀ s' st s, (step s' st s).1.length = st.1.length := by
    intro s' st s
    simp only [step]
    exact mu0Inner_length _ _ _ _ _ _
  have key : ∀ k, k ≤ nsm →
      Analysis.Window cur Prod.snd (fun s => (List.range k).foldl (fun st s' => step s' st s) (S0, cur)) ∧
      Analysis.TapeLaw Prod.snd v (fun s => (List.range k).foldl (fun st s' => step s' st s) (S0, cur))
        (Pseudocode.loop F k ∅) ∧
      ∀ s, ((List.range k).foldl (fun st s' => step s' st s) (S0, cur)).1.length = 2 * p := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Analysis.window_const (S0, cur) le_rfl, ?_, fun _ => hS0len⟩
      rw [← hv0]
      exact Analysis.tapeLaw_const Prod.snd v (S0, cur)
    | succ k ih =>
      intro hkn
      obtain ⟨hw, hl, hlen⟩ := ih (by omega)
      have hks : k < nsm := by omega
      have hgf : (fun s => (List.range (k + 1)).foldl (fun st s' => step s' st s) (S0, cur)) =
          fun s => step k ((List.range k).foldl (fun st s' => step s' st s) (S0, cur)) s := by
        funext s
        simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hloop : Pseudocode.loop F (k + 1) ∅ = (Pseudocode.loop F k ∅).bind (F k) := by
        unfold Pseudocode.loop
        rw [List.range_succ, List.foldlM_append]
        simp only [List.foldlM_cons, List.foldlM_nil]
        show (List.foldlM (fun b i => F i b) ∅ (List.range k)).bind (fun b => (F k b).bind PMF.pure) = _
        simp only [PMF.bind_pure]
      rw [hgf, hloop]
      refine ⟨Analysis.window_bind (fun st : List Bool × ℕ => st.1.length = 2 * p) hw hlen
          (fun st hst => (hstep k st hks hst).1),
        Analysis.tapeLaw_bind (fun st : List Bool × ℕ => st.1.length = 2 * p) hw hlen
          (fun st hst => (hstep k st hks hst).1) hl (fun st hst => (hstep k st hks hst).2), ?_⟩
      intro s
      rw [congrFun hgf s, hsteplen]
      exact hlen s
  obtain ⟨-, hlaw, -⟩ := key nsm le_rfl
  have hfinal : ∀ s, (Program.mu0 K (Coins.ofFinset s) cur).val =
      (List.range nsm).foldl (fun st s' => step s' st s) (S0, cur) := by
    intro s; rw [hg, hnsm]
  have hT2 : ∀ s, ((List.range nsm).foldl (fun st s' => step s' st s) (S0, cur)).2 + n ≤ T := by
    intro s
    rw [← hfinal]
    exact hT s
  have key_result := hlaw n T hT2
  rw [hFmu0]
  rw [show (fun s => let r := (Program.mu0 K (Coins.ofFinset s) cur).val;
      ((Finset.range (2 * p)).filter (fun e => r.1.getD e false = true),
        ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) =
      (fun s => (v ((List.range nsm).foldl (fun st s' => step s' st s) (S0, cur)),
        Analysis.tapeRest s (((List.range nsm).foldl (fun st s' => step s' st s) (S0, cur)).2) n))
      from by funext s; rw [hfinal]; rfl]
  exact key_result

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

section OrderStat
open Arlib.Computation Cellcounting.Model.Operations

/-- INTERNAL: the list `Program.insertAsc` builds: `x` goes before the first entry it is
smaller than. -/
noncomputable def insAscList (x : SRat) : List SRat → List SRat
  | [] => [x]
  | y :: l => if x.get < y.get then x :: y :: l else y :: insAscList x l

/-- INTERNAL: the fold inside `Program.insertAsc`, for any step with its two equations. -/
theorem insAsc_fold (x : SRat) (g : List SRat × Bool → SRat → List SRat × Bool)
    (ht : ∀ acc y, g (acc, true) y = (acc ++ [y], true))
    (hf : ∀ acc y, g (acc, false) y =
      if x.get < y.get then (acc ++ [x, y], true) else (acc ++ [y], false)) (l : List SRat) :
    (if (List.foldl g ([], false) l).2 = true then
        (pure (List.foldl g ([], false) l).1 : Program.Prog (List SRat))
      else Model.Operations.push (List.foldl g ([], false) l).1 x).val = insAscList x l := by
  have htrue : ∀ (l acc : List SRat), List.foldl g (acc, true) l = (acc ++ l, true) := by
    intro l; induction l with
    | nil => intro acc; simp
    | cons y l ih => intro acc; rw [List.foldl_cons, ht, ih]; simp
  have key : ∀ (l acc : List SRat), (if (List.foldl g (acc, false) l).2 = true then
        (pure (List.foldl g (acc, false) l).1 : Program.Prog (List SRat))
      else Model.Operations.push (List.foldl g (acc, false) l).1 x).val = acc ++ insAscList x l := by
    intro l; induction l with
    | nil => intro acc; simp [insAscList]
    | cons y l ih =>
      intro acc
      rw [List.foldl_cons, hf]
      by_cases h : x.get < y.get
      · simp only [h, if_true, htrue, insAscList]; simp
      · simp only [h, if_false, insAscList]; rw [ih]; simp
  simpa using key l []

/-- INTERNAL: the value of `Program.insertAsc`. -/
theorem insertAsc_val (l : List SRat) (x : SRat) : (Program.insertAsc l x).val = insAscList x l := by
  unfold Program.insertAsc
  simp only [Charged.val_bind, Analysis.val_foldl']
  refine insAsc_fold x _ (fun acc y => ?_) (fun acc y => ?_) l
  · simp
  · by_cases h : x.get < y.get <;> simp [h]

/-- INTERNAL: insertion permutes the values. -/
theorem insAscList_perm (x : SRat) (l : List SRat) :
    ((insAscList x l).map SRat.get).Perm (x.get :: l.map SRat.get) := by
  induction l with
  | nil => simp [insAscList]
  | cons y l ih =>
    simp only [insAscList]
    split_ifs
    · simp
    · simp only [List.map_cons]
      exact ((ih.cons y.get).trans (List.Perm.swap _ _ _))

/-- INTERNAL: insertion into a sorted list of values keeps it sorted. -/
theorem insAscList_sorted (x : SRat) (l : List SRat)
    (hl : (l.map SRat.get).Pairwise (· ≤ ·)) :
    ((insAscList x l).map SRat.get).Pairwise (· ≤ ·) := by
  induction l with
  | nil => simp [insAscList]
  | cons y l ih =>
    simp only [List.map_cons, List.pairwise_cons] at hl
    simp only [insAscList]
    split_ifs with h
    · simp only [List.map_cons, List.pairwise_cons]
      refine ⟨fun a ha => ?_, hl.1, hl.2⟩
      rcases List.mem_cons.1 ha with rfl | ha
      · exact h.le
      · exact h.le.trans (hl.1 _ ha)
    · simp only [List.map_cons, List.pairwise_cons]
      refine ⟨fun a ha => ?_, ih hl.2⟩
      rcases List.mem_cons.1 ((insAscList_perm x l).mem_iff.1 ha) with rfl | ha
      · exact not_lt.1 h
      · exact hl.1 a ha

/-- The program's median selection by exact comparisons returns the pseudocode order statistic. -/
theorem orderStat_val (outs : List Cellcounting.Model.Operations.SRat) (idx : ℕ) : (Cellcounting.Program.orderStat outs idx).val.get = Cellcounting.Pseudocode.orderStat (outs.map Cellcounting.Model.Operations.SRat.get) idx := by
  unfold Program.orderStat Pseudocode.orderStat
  simp only [Charged.val_bind, Analysis.val_foldl', Cellcounting.Interface.val_get, insertAsc_val]
  set S := List.foldl (fun acc x => insAscList x acc) [] outs with hS
  have key : ∀ (l acc : List SRat), (acc.map SRat.get).Pairwise (· ≤ ·) →
      ((List.foldl (fun acc x => insAscList x acc) acc l).map SRat.get).Pairwise (· ≤ ·) ∧
      ((List.foldl (fun acc x => insAscList x acc) acc l).map SRat.get).Perm
        (acc.map SRat.get ++ l.map SRat.get) := by
    intro l
    induction l with
    | nil => intro acc h; simp [h]
    | cons y l ih =>
      intro acc h
      obtain ⟨h1, h2⟩ := ih (insAscList y acc) (insAscList_sorted y acc h)
      refine ⟨h1, h2.trans ?_⟩
      simp only [List.map_cons]
      refine ((insAscList_perm y acc).append_right _).trans ?_
      exact List.perm_middle.symm
  obtain ⟨hsort, hperm⟩ := key outs [] (by simp)
  simp only [List.map_nil, List.nil_append] at hperm
  have heq : S.map SRat.get = ((outs.map SRat.get : List ℚ) : Multiset ℚ).sort (· ≤ ·) := by
    refine List.Perm.eq_of_pairwise' hsort (Multiset.pairwise_sort _ _) ?_
    refine hperm.trans ?_
    rw [← Multiset.coe_eq_coe, Multiset.sort_eq]
  rw [← heq, ← Cellcounting.Interface.SRat.get_default, List.getD_map]

end OrderStat

/-- The program's preliminary deterministic flow test decides exactly the pseudocode feasibility predicate. -/
theorem feasible_val (m n : ℕ) (r c : List Cellcounting.Model.Operations.SNat) (b : List (List Cellcounting.Model.Operations.SNat)) (hr : r.length = m) (hc : c.length = n) : (Cellcounting.Program.feasible m n r c b).val = decide (Cellcounting.Pseudocode.feasible ⟨m, n, fun i => (r.getD i.val default).get, fun j => (c.getD j.val default).get, fun i j => ((b.getD i.val []).getD j.val default).get⟩) := by
  exact Analysis.feasible_val_proof m n r c b hr hc

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

section Tighten
open Arlib.Computation Cellcounting.Model.Operations

/-- INTERNAL: reading back entry `(i, j)` of an encoded matrix gives `b i j`. -/
theorem readMatrix_ofFn_getD {m n : ℕ} (b : Fin m → Fin n → ℕ) (i : Fin m) (j : Fin n) :
    (((Program.readMatrix (List.ofFn fun i => List.ofFn fun j => b i j)).val.getD
      i.val []).getD j.val default).get = b i j := by
  rw [readMatrix_val, List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
    List.getElem?_ofFn, dif_pos i.isLt]
  simp only [Option.map_some, Option.getD_some]
  rw [← readList_val]
  exact readList_ofFn_getD (fun j => b i j) j

/-- INTERNAL: `l_ij` read through natural-number indices, `0` outside the table. -/
noncomputable def lowN (I : Instance) (i j : ℕ) : ℕ :=
  if h : i < I.m ∧ j < I.n then Pseudocode.cellLow I ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

/-- INTERNAL: the retained cell `(i, j)`, if any, read through natural-number indices. -/
noncomputable def cellOpt (I : Instance) (i j : ℕ) : Option Pseudocode.Entry :=
  if h : i < I.m ∧ j < I.n then
    (if 0 < Pseudocode.cellRange I ⟨i, h.1⟩ ⟨j, h.2⟩ then
      some (i, j, Pseudocode.cellRange I ⟨i, h.1⟩ ⟨j, h.2⟩) else none)
  else none

/-- INTERNAL: the retained cells, row-major over natural-number indices. -/
theorem retained_eq (I : Instance) : Pseudocode.retained I =
    (List.range I.m).flatMap (fun i => (List.range I.n).filterMap (cellOpt I i)) := by
  unfold Pseudocode.retained
  rw [show List.range I.m = (List.finRange I.m).map Fin.val from
    List.map_coe_finRange_eq_range.symm, List.flatMap_map]
  refine List.flatMap_congr fun i _ => ?_
  rw [show List.range I.n = (List.finRange I.n).map Fin.val from
    List.map_coe_finRange_eq_range.symm, List.filterMap_map]
  refine List.filterMap_congr fun j _ => ?_
  simp [cellOpt, i.isLt, j.isLt]

/-- INTERNAL: entrywise differences, as `Program.subLists` computes them. -/
theorem subLists_val (a b : List SNat) (k : ℕ) :
    (Program.subLists a b k).val =
      (List.range k).map (fun i => (SNat.sub (a.getD i default) (b.getD i default)).val) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold Program.subLists at ih ⊢
    rw [Analysis.nv_repeatFor_succ, ih, List.range_succ, List.map_append]
    simp

/-- INTERNAL: the cell step of `Program.tighten`, verbatim, so that loop lemmas see one
stable term. -/
def tightenBody (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (z : SNat) (i j : ℕ)
    (st : List SNat × List SNat × List Program.Entry) :
    Program.Prog (List SNat × List SNat × List Program.Entry) := do
  let l ← Program.cellMin m n r c b i j
  let u ← Program.cellMax m n r c b i j l
  let w ← SNat.sub u l
  let lr ← Model.Operations.get st.1 i
  let lr' ← SNat.add lr l
  let lowR ← Model.Operations.set st.1 i lr'
  let lc ← Model.Operations.get st.2.1 j
  let lc' ← SNat.add lc l
  let lowC ← Model.Operations.set st.2.1 j lc'
  let keep ← SNat.lt z w
  if keep then do
    let cells ← Model.Operations.push st.2.2 (i, j, w)
    pure (lowR, lowC, cells)
  else pure (lowR, lowC, st.2.2)

/-- INTERNAL: `Program.tighten` in terms of `tightenBody` (definitional). -/
theorem tighten_eq (m n : ℕ) (r c : List SNat) (b : List (List SNat)) :
    Program.tighten m n r c b = (do
      let z ← SNat.lit 0
      let lowR0 ← Model.Operations.replicate m z
      let lowC0 ← Model.Operations.replicate n z
      let st ← Charged.repeatFor (fun i st0 =>
        Charged.repeatFor (tightenBody m n r c b z i) n st0) m (lowR0, lowC0, [])
      let rows ← Program.subLists r st.1 m
      let cols ← Program.subLists c st.2.1 n
      pure ⟨rows, cols, st.2.2⟩) := rfl

/-- INTERNAL: the value of one cell step of the tightening loop. -/
theorem tightenBody_val (m n : ℕ) (r c : List SNat) (b : List (List SNat)) (z : SNat)
    (hz : z.get = 0) (i j : ℕ) (st : List SNat × List SNat × List Program.Entry) :
    (tightenBody m n r c b z i j st).val =
      (st.1.set i (SNat.add (st.1.getD i default) (Program.cellMin m n r c b i j).val).val,
        st.2.1.set j (SNat.add (st.2.1.getD j default) (Program.cellMin m n r c b i j).val).val,
        if 0 < (Program.cellMax m n r c b i j (Program.cellMin m n r c b i j).val).val.get -
            (Program.cellMin m n r c b i j).val.get then
          st.2.2 ++ [(i, j, (SNat.sub (Program.cellMax m n r c b i j
            (Program.cellMin m n r c b i j).val).val (Program.cellMin m n r c b i j).val).val)]
        else st.2.2) := by
  unfold tightenBody
  simp only [Charged.val_bind, Cellcounting.Interface.val_get, Cellcounting.Interface.val_set,
    Cellcounting.Interface.SNat.val_lt, Cellcounting.Interface.SNat.get_sub, hz]
  split_ifs with h <;> simp_all

/-- On feasible input, the program's tightening step produces the pseudocode's tightened margins and retained cells. -/
theorem tighten_view (I : Cellcounting.Instance) (hfeas : Cellcounting.Pseudocode.feasible I) : let T := (Cellcounting.Program.tighten I.m I.n (Cellcounting.Program.readList (List.ofFn I.r)).val (Cellcounting.Program.readList (List.ofFn I.c)).val (Cellcounting.Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val).val; (T.rows.map Cellcounting.Model.Operations.SNat.get, T.cols.map Cellcounting.Model.Operations.SNat.get, T.cells.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get))) = ((List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.retained I)  := by
  intro T
  set r := (Program.readList (List.ofFn I.r)).val with hrdef
  set c := (Program.readList (List.ofFn I.c)).val with hcdef
  set b := (Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val with hbdef
  have hr : r.length = I.m := by simp [hrdef, readList_val]
  have hc : c.length = I.n := by simp [hcdef, readList_val]
  have hb : b.length = I.m := by simp [hbdef, readMatrix_val]
  have hbrow : ∀ row ∈ b, row.length = I.n := by
    intro row h
    rw [hbdef, readMatrix_val] at h
    simp only [List.map_ofFn, List.mem_ofFn, Function.comp_apply] at h
    obtain ⟨i, rfl⟩ := h
    simp
  have hrv : ∀ i : Fin I.m, (r.getD i.val default).get = I.r i := readList_ofFn_getD I.r
  have hcv : ∀ j : Fin I.n, (c.getD j.val default).get = I.c j := readList_ofFn_getD I.c
  have hbv : ∀ (i : Fin I.m) (j : Fin I.n), ((b.getD i.val []).getD j.val default).get = I.b i j :=
    readMatrix_ofFn_getD I.b
  have hmin : ∀ i j, i < I.m → j < I.n →
      (Program.cellMin I.m I.n r c b i j).val.get = lowN I i j := by
    intro i j hi hj
    have := Analysis.cellMin_val I hfeas r c b hr hc hb hbrow hrv hcv hbv ⟨i, hi⟩ ⟨j, hj⟩
    exact this.trans (by rw [lowN, dif_pos ⟨hi, hj⟩])
  have hmax : ∀ i j, (hi : i < I.m) → (hj : j < I.n) →
      (Program.cellMax I.m I.n r c b i j (Program.cellMin I.m I.n r c b i j).val).val.get =
        Pseudocode.cellHigh I ⟨i, hi⟩ ⟨j, hj⟩ := by
    intro i j hi hj
    have := Analysis.cellMax_val I hfeas r c b hr hc hb hbrow hrv hcv hbv ⟨i, hi⟩ ⟨j, hj⟩
      (Program.cellMin I.m I.n r c b i j).val (by rw [hmin i j hi hj, lowN, dif_pos ⟨hi, hj⟩])
    simpa only using this
  -- the loop invariant after full rows `< a` and columns `< bb` of row `a`
  let view : Program.Entry → Pseudocode.Entry := fun e => (e.1, e.2.1, e.2.2.get)
  let TInv : ℕ → ℕ → List SNat × List SNat × List Program.Entry → Prop := fun a bb st =>
    st.1.length = I.m ∧ st.2.1.length = I.n ∧
    (∀ i < I.m, (st.1.getD i default).get = if i < a then ∑ j ∈ Finset.range I.n, lowN I i j
      else if i = a then ∑ j ∈ Finset.range bb, lowN I a j else 0) ∧
    (∀ j < I.n, (st.2.1.getD j default).get =
      ∑ i ∈ Finset.range a, lowN I i j + if j < bb then lowN I a j else 0) ∧
    st.2.2.map view = (List.range a).flatMap (fun i => (List.range I.n).filterMap (cellOpt I i)) ++
      (List.range bb).filterMap (cellOpt I a)
  have hz : (SNat.lit 0).val.get = 0 := rfl
  have hrep : ∀ (k i : ℕ), ((List.replicate k (SNat.lit 0).val).getD i default).get = 0 := by
    intro k i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl
  have hinit : TInv 0 0 (List.replicate I.m (SNat.lit 0).val, List.replicate I.n (SNat.lit 0).val, []) := by
    refine ⟨by simp, by simp, fun i _ => ?_, fun j _ => ?_, by simp⟩
    · rw [hrep]; split_ifs <;> first | omega | simp
    · rw [hrep]; simp
  have hinner : ∀ a, a < I.m → ∀ bb st, bb < I.n → TInv a bb st →
      TInv a (bb + 1) (tightenBody I.m I.n r c b (SNat.lit 0).val a bb st).val := by
    intro a ha bb st hbb ⟨h1, h2, h3, h4, h5⟩
    rw [tightenBody_val _ _ _ _ _ _ hz]
    refine ⟨by simp [h1], by simp [h2], fun i hi => ?_, fun j hj => ?_, ?_⟩
    · simp only
      rw [Analysis.bs_getD_set]
      by_cases hia : i = a
      · subst hia
        rw [if_pos ⟨rfl, by omega⟩, Cellcounting.Interface.SNat.get_add, h3 i hi, hmin i bb hi hbb,
          if_neg (lt_irrefl i), if_pos rfl, if_neg (lt_irrefl i), if_pos rfl, Finset.sum_range_succ]
      · rw [if_neg (fun h => hia h.1.symm), h3 i hi]
        by_cases hlt : i < a
        · simp [hlt]
        · simp [hlt, hia]
    · simp only
      rw [Analysis.bs_getD_set]
      by_cases hjb : j = bb
      · subst hjb
        rw [if_pos ⟨rfl, by omega⟩, Cellcounting.Interface.SNat.get_add, h4 j hj, hmin a j ha hj,
          if_neg (lt_irrefl j), if_pos (Nat.lt_succ_self j)]
        ring
      · rw [if_neg (fun h => hjb h.1.symm), h4 j hj]
        congr 1
        by_cases hlt : j < bb
        · rw [if_pos hlt, if_pos (by omega)]
        · rw [if_neg hlt, if_neg (by omega)]
    · simp only
      rw [List.range_succ, List.filterMap_append, ← List.append_assoc, ← h5]
      have hco : cellOpt I a bb = if 0 < Pseudocode.cellRange I ⟨a, ha⟩ ⟨bb, hbb⟩ then
          some (a, bb, Pseudocode.cellRange I ⟨a, ha⟩ ⟨bb, hbb⟩) else none := by
        rw [cellOpt, dif_pos ⟨ha, hbb⟩]
      have hw : (Program.cellMax I.m I.n r c b a bb (Program.cellMin I.m I.n r c b a bb).val).val.get -
          (Program.cellMin I.m I.n r c b a bb).val.get = Pseudocode.cellRange I ⟨a, ha⟩ ⟨bb, hbb⟩ := by
        rw [hmax a bb ha hbb, hmin a bb ha hbb, lowN, dif_pos ⟨ha, hbb⟩]; rfl
      have hfm : List.filterMap (cellOpt I a) [bb] = (cellOpt I a bb).toList := by
        cases h : cellOpt I a bb <;> simp [h]
      rw [hfm, hco, hw]
      split_ifs with hpos
      · simp only [List.map_append, List.map_cons, List.map_nil, view,
          Cellcounting.Interface.SNat.get_sub, hw, Option.toList_some]
      · simp
  have houter : ∀ a st, a < I.m → TInv a 0 st →
      TInv (a + 1) 0 (Charged.repeatFor (tightenBody I.m I.n r c b (SNat.lit 0).val a) I.n st).val := by
    intro a st ha hst
    obtain ⟨h1, h2, h3, h4, h5⟩ := Analysis.nv_loop_inv (tightenBody I.m I.n r c b (SNat.lit 0).val a)
      (fun bb st => TInv a bb st) I.n st hst (fun bb st hbb h => hinner a ha bb st hbb h)
    refine ⟨h1, h2, fun i hi => ?_, fun j hj => ?_, ?_⟩
    · rw [h3 i hi]
      by_cases hlt : i < a
      · simp [hlt, show i < a + 1 by omega]
      · by_cases hia : i = a
        · subst hia; simp
        · simp [hlt, hia, show ¬ i < a + 1 by omega]
    · rw [h4 j hj, if_pos hj, Finset.sum_range_succ]; simp
    · rw [h5, List.range_succ, List.flatMap_append]; simp
  have hloop := Analysis.nv_loop_inv
    (fun i st0 => Charged.repeatFor (tightenBody I.m I.n r c b (SNat.lit 0).val i) I.n st0)
    (fun a st => TInv a 0 st) I.m _ hinit (fun a st ha h => houter a st ha h)
  obtain ⟨g1, g2, g3, g4, g5⟩ := hloop
  simp only [T, tighten_eq, Charged.val_bind, Cellcounting.Interface.val_replicate,
    Charged.val_pure, subLists_val, List.map_map]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply, Cellcounting.Interface.SNat.get_sub]
    rw [g3 i hi', if_pos hi', Pseudocode.tRow, dif_pos hi', hrv ⟨i, hi'⟩,
      ← Fin.sum_univ_eq_sum_range (fun j => lowN I i j)]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [lowN, dif_pos ⟨hi', j.isLt⟩]
  · refine List.map_congr_left fun j hj => ?_
    have hj' := List.mem_range.1 hj
    simp only [Function.comp_apply, Cellcounting.Interface.SNat.get_sub]
    rw [g4 j hj', if_neg (Nat.not_lt_zero j), add_zero, Pseudocode.tCol, dif_pos hj', hcv ⟨j, hj'⟩,
      ← Fin.sum_univ_eq_sum_range (fun i => lowN I i j)]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [lowN, dif_pos ⟨i.isLt, hj'⟩]
  · show List.map view _ = _
    rw [g5, retained_eq]; simp

end Tighten

/-- The program computes the scale parameters of eq:parameters exactly as the pseudocode defines them. -/
theorem params_view (I : Cellcounting.Instance) (ε δ : ℚ) : let Pm := (Cellcounting.Program.params I.m I.n (Cellcounting.Program.inputLen I ε δ).val (Cellcounting.Model.Operations.SRat.lit ε).val).val; (Pm.d.get, Pm.K.get, Pm.A.get, Pm.B.get, Pm.W.get, Pm.H.get) = (Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.KParam I ε δ, Cellcounting.Pseudocode.AParam I ε δ, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.WParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ)  := by
  intro Pm
  simp only [Pm, Program.params, Program.clog2, Program.inputLen,
    Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Interface.SNat.get_lit, Interface.SNat.get_add, Interface.SNat.get_mul, Interface.SNat.get_sub,
    Interface.SNat.get_size, Interface.SNat.get_toRat, Interface.SRat.get_lit, Interface.SRat.get_div,
    Interface.SRat.get_natCeil, Interface.SNat.get_inputLength, Pseudocode.size_pred_eq_clog,
    Pseudocode.dParam, Pseudocode.KParam, Pseudocode.γParam, Pseudocode.AParam, Pseudocode.BParam,
    Pseudocode.WParam, Pseudocode.HParam, one_div]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))) <;>
    push_cast <;> ring_nf

/-- The program's context (small/free split, forest, elimination order, M_f) matches the pseudocode's derived data field by field. This discharges the hC hypothesis of every tape lemma. -/
theorem buildCtx_view (I : Cellcounting.Instance) (ε δ : ℚ) (hfeas : Cellcounting.Pseudocode.feasible I) : let C := (Cellcounting.Program.buildCtx I.m I.n (Cellcounting.Program.tighten I.m I.n (Cellcounting.Program.readList (List.ofFn I.r)).val (Cellcounting.Program.readList (List.ofFn I.c)).val (Cellcounting.Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val).val (Cellcounting.Program.params I.m I.n (Cellcounting.Program.inputLen I ε δ).val (Cellcounting.Model.Operations.SRat.lit ε).val).val).val; (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ)) := by
  exact Analysis.buildCtx_view_of I ε δ _ _ (tighten_view I hfeas) (params_view I ε δ)

/-- The program's chain and phase parameters, initial multipliers w⁽⁰⁾ (closed form of lem:initialization) and C(0) equal the pseudocode's values. -/
theorem chainSetup_view (I : Cellcounting.Instance) (ε δ : ℚ) (C : Cellcounting.Program.Ctx) (hC : (C.m, C.n, C.rows.map Cellcounting.Model.Operations.SNat.get, C.cols.map Cellcounting.Model.Operations.SNat.get, C.small.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nSmall, C.free.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nFree, C.tree.map (fun (e : Cellcounting.Program.Entry) => (e.1, e.2.1, e.2.2.get)), C.nTree, C.order, C.roots, C.Mf.get, C.d.get, C.B.get, C.H.get, C.Aq.get, C.Hq.get, C.Bq.get) = (I.m, I.n, (List.range I.m).map (Cellcounting.Pseudocode.tRow I), (List.range I.n).map (Cellcounting.Pseudocode.tCol I), Cellcounting.Pseudocode.smallCells I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, (Cellcounting.Pseudocode.forest I ε δ).free, Cellcounting.Pseudocode.nFree I ε δ, (Cellcounting.Pseudocode.forest I ε δ).tree, (Cellcounting.Pseudocode.forest I ε δ).tree.length, Cellcounting.Pseudocode.elimOrder I ε δ, Cellcounting.Pseudocode.roots I ε δ, Cellcounting.Pseudocode.Mf I ε δ, Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ, (Cellcounting.Pseudocode.AParam I ε δ : ℚ), (Cellcounting.Pseudocode.HParam I ε δ : ℚ), (Cellcounting.Pseudocode.BParam I ε δ : ℚ))) (Pm : Cellcounting.Program.Params) (hPm : (Pm.d.get, Pm.K.get, Pm.A.get, Pm.B.get, Pm.W.get, Pm.H.get) = (Cellcounting.Pseudocode.dParam I, Cellcounting.Pseudocode.KParam I ε δ, Cellcounting.Pseudocode.AParam I ε δ, Cellcounting.Pseudocode.BParam I ε δ, Cellcounting.Pseudocode.WParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ)) (pS : Cellcounting.Model.Operations.SNat) (hp : pS.get = Cellcounting.Pseudocode.pSmall I ε δ) (εS : Cellcounting.Model.Operations.SRat) (hε : εS.get = ε) : let r := (Cellcounting.Program.chainSetup C Pm pS εS).val; ((r.1.p, r.1.pS.get, r.1.nsm, r.1.pairCell, r.1.cellFirst, r.1.smallB.map Cellcounting.Model.Operations.SNat.get, r.1.ξ.get, r.1.kAcc, r.1.kAccS.get), (r.2.1.τ.get, r.2.1.Bret.get, r.2.1.BretN, r.2.1.Nav.get, r.2.1.NavN, r.2.1.Hn), (fun (i l : ℕ) => ((r.2.2.1.getD i []).getD l default).get), (r.2.2.1.length, r.2.2.1.map List.length), r.2.2.2.get) = ((Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.pSmall I ε δ, Cellcounting.Pseudocode.nSmall I ε δ, Cellcounting.Pseudocode.pairCells I ε δ, (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.cellFirst I ε δ), (List.range (Cellcounting.Pseudocode.nSmall I ε δ)).map (Cellcounting.Pseudocode.smallB I ε δ), Cellcounting.Pseudocode.ξParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ, Cellcounting.Pseudocode.kAccParam I ε δ), (Cellcounting.Pseudocode.τParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.BretParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.NavParam I ε δ, Cellcounting.Pseudocode.HParam I ε δ), Cellcounting.Pseudocode.w0 I ε δ, (Cellcounting.Pseudocode.pSmall I ε δ, List.replicate (Cellcounting.Pseudocode.pSmall I ε δ) (Cellcounting.Pseudocode.pSmall I ε δ)), Cellcounting.Pseudocode.C0 I ε δ) := by
  exact Analysis.chainSetup_view_of I ε δ C hC Pm hPm pS hp εS hε

/-- Unfolds the output law in Model/Run: it is the pushforward of a uniform finite coin tape through the program's estimate. -/
theorem output_eq_map_estimate (I : Cellcounting.Instance) (ε δ : ℚ) : Cellcounting.output I ε δ = (Cellcounting.tapeHeads (Cellcounting.tapeLength I ε δ)).map (fun (s : Finset ℕ) => Cellcounting.Interface.estimate I ε δ (Arlib.Computation.Coins.ofFinset s)) := by
  unfold output run tape
  rw [PMF.map_comp, PMF.map_comp]
  rfl

/-- On infeasible input the program returns zero for every coin sequence. This is the theorem's 'zero on every execution' clause. -/
theorem estimate_infeasible (I : Cellcounting.Instance) (ε δ : ℚ) (h : ¬ Cellcounting.Pseudocode.feasible I) (c : Arlib.Computation.Coins ℕ) : Cellcounting.Interface.estimate I ε δ c = 0 := by
  have hf := feasible_val I.m I.n (Program.readList (List.ofFn I.r)).val
      (Program.readList (List.ofFn I.c)).val
      (Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val
      (by simp [readList_val]) (by simp [readList_val])
  rw [decode_input, decide_eq_false h] at hf
  simp only [Interface.estimate, Program.fpras, Arlib.Computation.Charged.val_bind, hf,
    Bool.false_eq_true, ↓reduceIte, Interface.SRat.val_output, Interface.SRat.get_lit]

open Arlib.Computation in
/-- INTERNAL: the median of `R` windowed runs read from cursor `0`, on any tape that covers
their final cursor, has the law of the pseudocode median of `R` independent single runs.
Assembled from `repeatRuns_tape_of_window`. TEXLINE: sections/algorithm.tex:670-690 -/
theorem median_tape_law (F : Arlib.Computation.Coins ℕ → ℕ → Cellcounting.Program.Prog (Cellcounting.Model.Operations.SRat × ℕ)) (G : PMF ℚ) (hF : ∀ cur n T : ℕ, (∀ s : Finset ℕ, (F (Arlib.Computation.Coins.ofFinset s) cur).val.2 + n ≤ T) → (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => let r := (F (Arlib.Computation.Coins.ofFinset s) cur).val; (r.1.get, ((s.filter (fun i => r.2 ≤ i)).image (fun i => i - r.2)).filter (fun i => i < n))) = G.bind (fun z => (Cellcounting.tapeHeads n).map (fun s' => (z, s')))) (hW : ∀ cur : ℕ, Cellcounting.Analysis.Window cur Prod.snd (fun s : Finset ℕ => (F (Arlib.Computation.Coins.ofFinset s) cur).val))
    (R mid T : ℕ) (est : Finset ℕ → ℚ)
    (hest : ∀ s, est s = Pseudocode.orderStat (((Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], 0)).val.1).map Model.Operations.SRat.get) mid)
    (hcur : ∀ s, (Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], 0)).val.2 ≤ T) :
    (tapeHeads T).map est = (Pseudocode.repeatRuns R G).map (fun outs => Pseudocode.orderStat outs mid) := by
  have hL : Analysis.TapeLaw Prod.snd (fun r : List Model.Operations.SRat × ℕ => r.1.map Model.Operations.SRat.get)
      (fun s => (Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], 0)).val)
      (Pseudocode.repeatRuns R G) :=
    fun n T hT => repeatRuns_tape_of_window F G hF hW R 0 n T hT
  rw [← hL.map_view T hcur, PMF.map_comp]
  congr 1
  funext s
  exact hest s

open Arlib.Computation in
/-- INTERNAL: the `R` runs of `Program.fpras` end at a cursor at most the fair bits they pay
for, if one run does (`Analysis.CurLe`, `Analysis/CursorFlips.lean`). -/
theorem runs_curLe (F : Arlib.Computation.Coins ℕ → ℕ → Cellcounting.Program.Prog (Cellcounting.Model.Operations.SRat × ℕ))
    (hF : ∀ cur, Analysis.CurLe cur Prod.snd (fun s => F (Arlib.Computation.Coins.ofFinset s) cur)) (R : ℕ) :
    Analysis.CurLe 0 Prod.snd (fun s => Arlib.Computation.Charged.repeatFor (fun _ (st : List Cellcounting.Model.Operations.SRat × ℕ) => ((do let (z, c') ← F (Arlib.Computation.Coins.ofFinset s) st.2; let outs ← Cellcounting.Model.Operations.push st.1 z; pure (outs, c')) : Cellcounting.Program.Prog (List Cellcounting.Model.Operations.SRat × ℕ))) R ([], 0)) := by
  refine Analysis.cl_loop Prod.snd (fun _ st => ?_) R _ le_rfl
  refine Analysis.cl_bind (hF st.2) fun z => ?_
  exact Analysis.cl_det _ fun _ => Analysis.cl_pure _ le_rfl

open Arlib.Computation in
/-- INTERNAL: the flips of a continuation are among the flips of the sequence. -/
theorem cost_flip_bind_right {α β : Type} (p : Program.Prog α) (q : α → Program.Prog β) :
    (q p.val).cost (Model.Operations.Op.rand RandOp.flip) ≤ (p >>= q).cost (Model.Operations.Op.rand RandOp.flip) :=
  Nat.le_add_left _ _

open Arlib.Computation in
/-- INTERNAL: the flips of a first step are among the flips of the sequence. -/
theorem cost_flip_bind_left {α β : Type} (p : Program.Prog α) (q : α → Program.Prog β) :
    p.cost (Model.Operations.Op.rand RandOp.flip) ≤ (p >>= q).cost (Model.Operations.Op.rand RandOp.flip) :=
  Nat.le_add_right _ _

open Arlib.Computation in
/-- INTERNAL: the program's `p`, a charged sum of the small-cell bounds. -/
theorem pS_val (l : List Program.Entry) (acc : Model.Operations.SNat) :
    (Charged.foldl (fun acc (e : Program.Entry) => Model.Operations.SNat.add acc e.2.2) l acc).val.get =
      acc.get + (l.map fun e => e.2.2.get).sum := by
  rw [Analysis.val_foldl']
  induction l generalizing acc with
  | nil => simp
  | cons a l ih => rw [List.foldl_cons, ih]; simp [add_assoc]

open Arlib.Computation in
/-- On feasible input, the law of the program's estimate on any tape long enough to cover every read equals the pseudocode fpras law. It splits on p = 0 versus p ≥ 1. -/
theorem estimate_feasible_law (I : Cellcounting.Instance) (ε δ : ℚ) (hfeas : Cellcounting.Pseudocode.feasible I) (T : ℕ) (hT : ∀ s : Finset ℕ, Cellcounting.Interface.flipsRead I ε δ s ≤ T) : (Cellcounting.tapeHeads T).map (fun (s : Finset ℕ) => Cellcounting.Interface.estimate I ε δ (Arlib.Computation.Coins.ofFinset s)) = Cellcounting.Pseudocode.fpras I ε δ := by
  have hf := feasible_val I.m I.n (Program.readList (List.ofFn I.r)).val
      (Program.readList (List.ofFn I.c)).val
      (Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val
      (by simp [readList_val]) (by simp [readList_val])
  rw [decode_input, decide_eq_true hfeas] at hf
  have hCv := buildCtx_view I ε δ hfeas
  have hPv := params_view I ε δ
  obtain ⟨Pm, hPmd⟩ : ∃ Pm, (Program.params I.m I.n (Program.inputLen I ε δ).val (Model.Operations.SRat.lit ε).val).val = Pm := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ C, (Program.buildCtx I.m I.n (Program.tighten I.m I.n (Program.readList (List.ofFn I.r)).val (Program.readList (List.ofFn I.c)).val (Program.readMatrix (List.ofFn fun i => List.ofFn fun j => I.b i j)).val).val Pm).val = C := ⟨_, rfl⟩
  simp only [hPmd, hCd] at hCv hPv
  obtain ⟨pS, hpSd⟩ : ∃ pS, (Charged.foldl (fun acc (e : Program.Entry) => Model.Operations.SNat.add acc e.2.2) C.small (Model.Operations.SNat.lit 0).val).val = pS := ⟨_, rfl⟩
  have hpS : pS.get = Pseudocode.pSmall I ε δ := by
    have hsm : C.small.map (fun (e : Program.Entry) => (e.1, e.2.1, e.2.2.get)) = Pseudocode.smallCells I ε δ := by
      simp only [Prod.mk.injEq] at hCv
      exact hCv.2.2.2.2.1
    rw [← hpSd, pS_val, Interface.SNat.get_lit, zero_add, Pseudocode.pSmall, ← hsm, List.map_map]
    rfl
  obtain ⟨sN, hsNd⟩ : ∃ sN, (Program.clog2 (Model.Operations.SRat.natCeil (Model.Operations.SRat.div (Model.Operations.SRat.lit 1).val (Model.Operations.SRat.lit δ).val).val).val).val = sN := ⟨_, rfl⟩
  have hsN : sN.get = Pseudocode.sRep δ := by
    rw [← hsNd, Analysis.csv_clog2, Interface.SRat.get_natCeil, Interface.SRat.get_div,
      Interface.SRat.get_lit, Interface.SRat.get_lit, one_div, Pseudocode.sRep]
  have hR : (Model.Operations.SNat.index (Model.Operations.SNat.add (Model.Operations.SNat.mul (Model.Operations.SNat.lit 10).val sN).val (Model.Operations.SNat.lit 1).val).val).val = 10 * Pseudocode.sRep δ + 1 := by
    simp [hsN]
  have hmid : (Model.Operations.SNat.index (Model.Operations.SNat.mul (Model.Operations.SNat.lit 5).val sN).val).val = 5 * Pseudocode.sRep δ := by
    simp [hsN]
  by_cases hp : Pseudocode.pSmall I ε δ = 0
  · have hz : ((Model.Operations.SNat.eq pS (Model.Operations.SNat.lit 0).val).val = true) := by
      simp [hpS, hp]
    rw [Pseudocode.fpras, if_pos hfeas, if_pos hp, ← hR, ← hmid]
    have hC := hCv
    refine median_tape_law (fun tape cur => Program.zeroRun C (Model.Operations.SNat.index Pm.H).val (Model.Operations.SRat.lit ε).val tape cur) _ ?_ (fun cur => Analysis.zeroRun_window _ _ _ cur) _ _ T _ ?_ ?_
    · intro cur n T' hT'
      exact zeroRun_tape I ε δ C hC _ (by simp only [Prod.mk.injEq] at hPv; simp [hPv.2.2.2.2.2]) _ (Interface.SRat.get_lit ε) cur n T' hT'
    · intro s
      simp only [Interface.estimate, Program.fpras, Charged.val_bind]
      rw [if_pos hf]
      simp only [Charged.val_bind]
      rw [hPmd, hCd, hpSd, hsNd, if_pos hz]
      simp only [Charged.val_bind]
      rw [Interface.SRat.val_output, orderStat_val]
    · intro s
      have h1 := runs_curLe _ (fun cur => Analysis.zeroRun_curLe C (Model.Operations.SNat.index Pm.H).val (Model.Operations.SRat.lit ε).val cur) ((Model.Operations.SNat.index (Model.Operations.SNat.add (Model.Operations.SNat.mul (Model.Operations.SNat.lit 10).val sN).val (Model.Operations.SNat.lit 1).val).val).val) s
      refine le_trans h1 (le_trans ?_ (hT s))
      rw [zero_add]
      unfold Interface.flipsRead Program.fpras
      iterate 5 refine le_trans ?_ (cost_flip_bind_right _ _)
      simp only [hf, ↓reduceIte]
      iterate 20 refine le_trans ?_ (cost_flip_bind_right _ _)
      simp only [hPmd, hCd, hpSd, hsNd, hz, ↓reduceIte]
      refine le_trans ?_ (cost_flip_bind_right _ _)
      exact cost_flip_bind_left _ _
  · have hz : ((Model.Operations.SNat.eq pS (Model.Operations.SNat.lit 0).val).val = false) := by
      simp [hpS, hp]
    have hC := hCv
    obtain ⟨cs, hcsd⟩ : ∃ cs, (Program.chainSetup C Pm pS (Model.Operations.SRat.lit ε).val).val = cs := ⟨_, rfl⟩
    have hcs := chainSetup_view I ε δ C hC Pm hPv pS hpS _ (Interface.SRat.get_lit ε)
    obtain ⟨K, Ph, w0, C0⟩ := cs
    simp only [hcsd, Prod.mk.injEq] at hcs
    obtain ⟨hK, hPh, hw0, hw0s, hC0⟩ := hcs
    rw [Pseudocode.fpras, if_pos hfeas, if_neg hp, ← hR, ← hmid]
    refine median_tape_law (fun tape cur => Program.annealRun C K tape Ph w0 C0 cur) _ ?_ (fun cur => Analysis.annealRun_window _ _ _ _ _ cur) _ _ T _ ?_ ?_
    · intro cur n T' hT'
      exact annealRun_tape I ε δ C hC K (by simp only [Prod.mk.injEq]; exact hK) Ph (by simp only [Prod.mk.injEq]; exact hPh) w0 (by simp only [Prod.mk.injEq]; exact hw0s) hw0 C0 hC0 cur n T' hT'
    · intro s
      simp only [Interface.estimate, Program.fpras, Charged.val_bind]
      rw [if_pos hf]
      simp only [Charged.val_bind]
      rw [hPmd, hCd, hpSd, hsNd, if_neg (by rw [hz]; exact Bool.false_ne_true)]
      simp only [Charged.val_bind, hcsd]
      rw [Interface.SRat.val_output, orderStat_val]
    · intro s
      have h1 := runs_curLe (fun tape cur => Program.annealRun C K tape Ph w0 C0 cur) (fun cur => Analysis.annealRun_curLe C K Ph w0 C0 cur) ((Model.Operations.SNat.index (Model.Operations.SNat.add (Model.Operations.SNat.mul (Model.Operations.SNat.lit 10).val sN).val (Model.Operations.SNat.lit 1).val).val).val) s
      refine le_trans h1 (le_trans ?_ (hT s))
      rw [zero_add]
      unfold Interface.flipsRead Program.fpras
      iterate 5 refine le_trans ?_ (cost_flip_bind_right _ _)
      simp only [hf, ↓reduceIte]
      iterate 20 refine le_trans ?_ (cost_flip_bind_right _ _)
      simp only [hPmd, hCd, hpSd, hsNd, hz, Bool.false_eq_true, ↓reduceIte]
      refine le_trans ?_ (cost_flip_bind_right _ _)
      simp only [hcsd]
      exact cost_flip_bind_left _ _

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

* r7 · proved · `tighten_view` from new `Analysis.cellMin_val`/`cellMax_val` (proved); `params_view` outright; `feasible_val` proof moved to `Analysis/FeasibleValProof.lean`
* r7 · proved · `orderStat_val` outright (insertion sort values are the sorted multiset)
* r7 · proved · `feasible_val` from `Analysis.network_val` (proved), `Analysis.maxFlow_correct` and `Analysis.transport_flow_iff` (open children); Edmonds–Karp count isolated as `Analysis.edmondsKarp_bound` (cited, EK1972)
* r6 · proved · `output_eq_map_estimate` (map composition), `estimate_infeasible` (from `feasible_val`)
* r6 · proved · `estimate_feasible_law` directly (not via `output_eq_map_estimate`, which `output_eq_fpras` already combines with it); cursor ≤ flips paid via new `Analysis/CursorFlips.lean`
* r5 · proved · `dyadicDraw_tape` from `uniformBits_tape` via `tapeLaw_map` and `size_pred_eq_clog`; `uniformBits_tape` outright via `Analysis.bitsVal_tape` (new `Analysis/UniformBitsTape.lean`)
* r4 · proved · `corrAvg_tape` from `sampleBin_tape`, `binOffsets_tape`, `penalty_val`, `pow2Approx_val`; bin-vector length invariant `sampleBin_val_length_le` makes `binPoint` views agree
* r3 · proved · `binOffsets_tape` from `dyadicDraw_tape` (per-cell law via `tapeLaw_map`, rounds via `tapeLaw_bind`); `hC` supplies `free`, `nFree`, `d`, `B`, `H`
* r2 · assembled · `output_eq_fpras` from its four sibling rungs; tape-length attainment by `Analysis.flipsRead_bddAbove` (finite range over tapes), input round-trip proved here
* r1 · proved · `annealRun_tape` from `phase_tape`, `phase_window` and the `p × p` shape invariant; `repeatRuns_tape` disproved by `Analysis.repeatRuns_tape_false`, repaired form `repeatRuns_tape_of_window` proved
-/
