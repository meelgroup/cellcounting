import Cellcounting.Analysis.ChoiceSum

/-!
# The one-hole transport inequality (`lem:transport`, `transport.tex:99-316`)

An abstract form of `lem:transport`, for a positive weight `f` on subsets of `ℕ` whose
contracted two-omission matrices have at most one positive eigenvalue.

Fixed inclusions `F`; two singleton slots `{x0}`, `{x1}`; ordinary slots the pairs
`{2t, 2t + 1}`, `t ∈ L`.  A one-hole state is `F ∪ (Y \ {i})` for a complete display
`Y = {x0, x1} ∪ c` (`c` a choice set of `L`) and a hole `i ∈ Y`; its weight is
`W i · f`.  Its hole-`x0` states have `f`-mass `s0` and `f`-weighted mean `m0 / s0`,
similarly for `x1`; `v_t` is the `f`-mass of the sets omitting both singletons, full in
pair `t`, and singly occupied elsewhere.

`slot_transport` is `eq:slot-transport`:
`(ḡ0 - ḡ1)² ≤ (1/(s0 W_{x0}) + 1/(s1 W_{x1}) + 2/(s0 s1) Σ_t v_t / W_t) · D`,
where `D` sums, over complete displays, the clique energy `cliqueEnergy` of the
one-hole states of the display (conductance the minimum of the two endpoint weights).
Distinct displays have disjoint clique edges, so `D` is at most the energy of any
graph containing all those edges with those conductances; that comparison is left
to the application.

The hypothesis `hsig` is the omission signature at every node of the paper's
conditioning tree: for every display `D` drawn from the slots and every set `L'` of
still-unprocessed pairs, with `|D| + |L'| = |L| + 3`, the two-omission matrix
`omitMat f F D L'` has at most one positive eigenvalue (`Hyp`).

Suggested route (the paper's, without explicit currents): process the pairs of `L` in
order; at a node with display `R` and coefficients `h` (`Σ_i m_i h_i = 0`) bound
`Φ = Σ_i h_i Σ_c (f g)(F ∪ R ∪ c \ {i})` by `Φ² ≤ B · D_node`, where
`B = Σ_i m_i h_i² / W_i + Σ_{t unprocessed} (-hᵀ V_t h) / W_t`; split `Φ`, `D_node`
additively over the two children (`X = Σ h_i m_i^a`, new coefficients `∓X/u`), use
`Hyp` of the node matrix with `e_a + e_b` to get `2X²/u ≤ -hᵀ V_t h`, and at a leaf
route to a hub maximizing `W_i m_i` with Cauchy–Schwarz.
-/

namespace Cellcounting.Analysis

/-- INTERNAL: the clique energy of the one-hole states `(F ∪ Disp) \ {i}`, `i ∈ Disp`,
with hole weights `W i · f` and conductance the minimum of the two endpoint weights,
as half the ordered-pair sum.
TEXLINE: sections/transport.tex:152-171 -/
noncomputable def cliqueEnergy (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F Disp : Finset ℕ) : ℝ :=
  (∑ i ∈ Disp, ∑ k ∈ Disp,
    if i = k then 0 else
      min (W i * f ((F ∪ Disp).erase i)) (W k * f ((F ∪ Disp).erase k)) *
        (g ((F ∪ Disp).erase i) - g ((F ∪ Disp).erase k)) ^ 2) / 2

/-- **One-hole transport** (`lem:transport`, `eq:slot-transport`): with singleton slots
`{x0}`, `{x1}` and ordinary slots the pairs of `L`,
`(ḡ0 - ḡ1)² ≤ (1/(s0 W_{x0}) + 1/(s1 W_{x1}) + 2/(s0 s1) Σ_t v_t / W_t) · D_sl(g)`.
PAPER: sections/transport.tex:99-129 -/
theorem slot_transport (f g : Finset ℕ → ℝ) (W : ℕ → ℝ) (F : Finset ℕ) (x0 x1 : ℕ)
    (L : List ℕ) (hf : ∀ S, 0 < f S) (hx : x0 ≠ x1) (hx0F : x0 ∉ F) (hx1F : x1 ∉ F)
    (hL : L.Nodup) (hLF : ∀ t ∈ L, 2 * t ∉ F ∧ 2 * t + 1 ∉ F)
    (hLx : ∀ t ∈ L, 2 * t ≠ x0 ∧ 2 * t ≠ x1 ∧ 2 * t + 1 ≠ x0 ∧ 2 * t + 1 ≠ x1)
    (hW0 : 0 < W x0) (hW1 : 0 < W x1)
    (hWL : ∀ t ∈ L, 0 < W (2 * t) ∧ W (2 * t + 1) = W (2 * t))
    (hsig : ∀ (D : Finset ℕ) (L' : List ℕ), L'.Nodup → (∀ t ∈ L', t ∈ L) →
      (∀ e ∈ D, e = x0 ∨ e = x1 ∨ ∃ t ∈ L, e = 2 * t ∨ e = 2 * t + 1) →
      (∀ t ∈ L', 2 * t ∉ D ∧ 2 * t + 1 ∉ D) →
      D.card + L'.length = L.length + 3 → Hyp (omitMat f F D L')) :
    (chSum L (fun c => f (insert x1 (F ∪ c)) * g (insert x1 (F ∪ c))) /
          chSum L (fun c => f (insert x1 (F ∪ c))) -
        chSum L (fun c => f (insert x0 (F ∪ c)) * g (insert x0 (F ∪ c))) /
          chSum L (fun c => f (insert x0 (F ∪ c)))) ^ 2 ≤
      (1 / (chSum L (fun c => f (insert x1 (F ∪ c))) * W x0) +
          1 / (chSum L (fun c => f (insert x0 (F ∪ c))) * W x1) +
          2 / (chSum L (fun c => f (insert x1 (F ∪ c))) *
              chSum L (fun c => f (insert x0 (F ∪ c)))) *
            ∑ t ∈ L.toFinset,
              chSum (L.erase t) (fun c => f (insert (2 * t) (insert (2 * t + 1) (F ∪ c)))) /
                W (2 * t)) *
        chSum L (fun c => cliqueEnergy f g W F (insert x0 (insert x1 c))) := by
  sorry

end Cellcounting.Analysis
