import Cellcounting.Analysis.RefChainLaw
import Cellcounting.Analysis.PmfClose
import Cellcounting.Model.Prior

/-!
# Time averages from a dominated initial law (`lem:time-average`)

`transport.tex:575-630`.  For good multipliers `w` at parameter `j`, the exact
Metropolis chain `P_{j, w}` (`refStep`) is reversible with stationary law
`π = λ / Λ` on `X` (`refPi`).  For an observable `G` fixed by the projection `Q`
(constant on each defect type `A_il`) and an initial law `ν ≤ U π`, the average of
`N ≥ 1` consecutive observations `G(S_0), …, G(S_{N-1})` has mean squared error
about `E_π G` at most `2 U K_obs Var_π(G) / N`.

`refTraj` is the law of the final state and the running sum `Σ_{t<N} G(S_t)`,
accumulated by `loop` exactly as `refObserve` accumulates its tallies.
-/

namespace Cellcounting.Analysis

open Pseudocode
open scoped ENNReal

/-- INTERNAL: the stationary law `π = λ / Λ` of `P_{j, w}` on `X` (zero off `X`).
TEXLINE: sections/transport.tex:36-47 -/
noncomputable def refPi (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ) (S : Finset ℕ) : ℝ :=
  if S ∈ chainStates I ε δ then refLam I ε δ S j w / refLamTot I ε δ j w else 0

/-- INTERNAL: the stationary mean `E_π G`.
TEXLINE: sections/transport.tex:575-590 -/
noncomputable def refPiMean (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (G : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S * G S

/-- INTERNAL: the stationary variance `Var_π G`.
TEXLINE: sections/transport.tex:575-590 -/
noncomputable def refPiVar (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (G : Finset ℕ → ℝ) : ℝ :=
  ∑ S ∈ chainStates I ε δ, refPi I ε δ j w S * (G S - refPiMean I ε δ j w G) ^ 2

/-- INTERNAL: `N` consecutive observations of `P_{j, w}` from `S0` (the starting
state included): the law of the last state and of `Σ_{t<N} G(S_t)`.
TEXLINE: sections/transport.tex:579-586 -/
noncomputable def refTraj (I : Instance) (ε δ : ℚ) (j : ℕ) (w : ℕ → ℕ → ℚ)
    (G : Finset ℕ → ℝ) (N : ℕ) (S0 : Finset ℕ) : PMF (Finset ℕ × ℝ) :=
  loop (fun _ x => (refStep I ε δ j w x.1).map fun S' => (S', x.2 + G S')) (N - 1)
    (S0, G S0)

/-- **Time averages from a dominated initial law** (`lem:time-average`): for good
multipliers, an observable `G` constant on each defect type (`Q G = G`), and an
initial law `ν ≤ U π`, the average of `N ≥ 1` consecutive observations satisfies
`E_ν[(N⁻¹ Σ_t G(S_t) - E_π G)²] ≤ 2 U K_obs Var_π(G) / N`.
PAPER: sections/transport.tex:575-630 -/
theorem time_average (hprior : Prior) (I : Instance) (ε δ : ℚ) (hm : 0 < I.m)
    (hn : 0 < I.n) (hε : 0 < ε) (hε1 : ε < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfeas : feasible I) (hp : pSmall I ε δ ≠ 0) (j : ℕ) (hj : j < HParam I ε δ)
    (w : ℕ → ℕ → ℚ) (hgood : goodMult I ε δ j w) (G : Finset ℕ → ℝ)
    (hQ : ∀ S S' i l, kind I ε δ S = .defect i l → kind I ε δ S' = .defect i l → G S = G S')
    (U : ℝ) (ν : PMF (Finset ℕ)) (hν : ∀ S, ν S ≤ ENNReal.ofReal (U * refPi I ε δ j w S))
    (N : ℕ) (hN : 1 ≤ N) :
    pexp (ν.bind (refTraj I ε δ j w G N))
        (fun x => ENNReal.ofReal ((x.2 / N - refPiMean I ε δ j w G) ^ 2)) ≤
      ENNReal.ofReal (2 * U * KobsParam I ε δ * refPiVar I ε δ j w G / N) := by
  sorry

end Cellcounting.Analysis
