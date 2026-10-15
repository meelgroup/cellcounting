import Cellcounting.Analysis.TransportDirichlet

/-!
# The energy is the edge energy over `2 p² Λ` (`eq:energy`, `transport.tex:70-96`)

For good multipliers (`λ > 0` on `X`), `𝓔(g) = ⟨g, (I - P) g⟩_π = 𝔇(g) / (2 p² Λ)`.
Every state of `X` has `p` elements in `[0, 2p)`, so a given exchange neighbour
`S'` of `S` is proposed with probability `1/(2p²)` and accepted with probability
`min{1, λ(S')/λ(S)}`; hence `π(S) P(S, S') = min{λ(S), λ(S')}/(2 p² Λ)` for distinct
exchange neighbours and `0` for other distinct pairs.  `P(S, ·)` is supported on
`X` for `S ∈ X`, and the usual reversible identity
`⟨g, (I - P) g⟩_π = ½ Σ π(S) P(S, S') (g(S) - g(S'))²` gives the claim.
-/

namespace Cellcounting.Analysis

open Pseudocode

/-- **The energy identity** (`eq:energy`): `𝓔(g) = 𝔇(g) / (2 p² Λ)` for good multipliers.
PAPER: sections/transport.tex:86-96 -/
theorem refEnergy_eq_refDir (I : Instance) (ε δ : ℚ) (hp : pSmall I ε δ ≠ 0) (j : ℕ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (g : Finset ℕ → ℝ) :
    refEnergy I ε δ j w g =
      refDir I ε δ j w g / (2 * (pSmall I ε δ : ℝ) ^ 2 * refLamTot I ε δ j w) := by
  sorry

end Cellcounting.Analysis
