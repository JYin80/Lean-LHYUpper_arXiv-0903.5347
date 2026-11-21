module

public import LHYUpper.Model.Dirichlet
public import LHYUpper.TrialState.Defs

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Statements of the results of Sections 2 and 3 as propositions

States, as `Prop`-valued definitions, Theorem 2.1 [mainthm] (`MainTheorem`), Theorem 3.1 [lemma2.1],
Theorem 2.2 [lemma2], Lemma 2.2 [lemma1] and Lemma 2.1 [thm1] with the duplication step after it
(§2.1), the variational principle for `e₀^P`, nonnegativity of the Hamiltonian (2.1) [ham] on
finitely supported states, and existence and uniqueness of the zero-energy scattering solution (§2). -/

namespace Stmt

/-- Statement of Theorem 2.1 [mainthm]: the upper limit, first over `L → ∞` with
`N/L³ → ρ` and then over `ρ → 0`, of the ratio for `e₀^P` is at most `16/(15π²)`. -/
def MainTheorem (V w : R3 → ℝ) : Prop :=
  limsup (fun ρ : ℝ => limsup (fun x : ℕ × ℝ => ratio (g0 V w) ρ (e0P x.2 V x.1))
    (thermo ρ)) (𝓝[>] 0) ≤ (cLHY : EReal)

/-- Statement of Theorem 3.1 [lemma2.1]: the trial state (3.18) [deffal] on the torus of side
`L = ρ^{-25/24}`, `ρ = ρ_N`, is normalized and has finite energy for every `k_c` and all
large `N`, and `limsup_{k_c → ∞} limsup_{ρ → 0}` of the ratio is at most `16/(15π²)`. -/
def Theorem3_1 (V w : R3 → ℝ) : Prop :=
  ∃ E : ℝ → ℕ → ℝ,
    (∀ kc : ℝ, ∀ᶠ N in atTop, IsNState N (trialState V w kc N) ∧
      HasEnergy (LN N) V (trialState V w kc N) (E kc N)) ∧
    limsup (fun kc : ℝ => limsup (fun N : ℕ =>
      ratio (g0 V w) (rhoN N) ((E kc N / N : ℝ) : EReal)) atTop) atTop ≤ (cLHY : EReal)

/-- Statement of Theorem 2.2 [lemma2]: a periodic trial state of `N` particles on
`[0, L_N]³` for each `N`, with upper limit of the ratio at most `16/(15π²)`. -/
def Theorem2_2 (V w : R3 → ℝ) : Prop :=
  ∃ Ψ : ℕ → Occ → ℂ, ∃ E : ℕ → ℝ,
    (∀ᶠ N in atTop, IsNState N (Ψ N) ∧ HasEnergy (LN N) V (Ψ N) (E N)) ∧
    limsup (fun N : ℕ => ratio (g0 V w) (rhoN N) ((E N / N : ℝ) : EReal)) atTop
      ≤ (cLHY : EReal)

/-- Statement of Lemma 2.2 [lemma1]: the periodic bound on `[0, L_N]³` gives the Dirichlet
bound on `[0, L̃_N]³` at density `ρ̃_N`. -/
def Lemma2_2 (V w : R3 → ℝ) : Prop :=
  limsup (fun N : ℕ => ratio (g0 V w) (rhoN N) (e0P (LN N) V N)) atTop ≤ (cLHY : EReal) →
    limsup (fun N : ℕ => ratio (g0 V w) (rhotN N) (e0D (LtN N) V N)) atTop ≤ (cLHY : EReal)

/-- Statement of Lemma 2.1 [thm1], for each `N`: a Dirichlet trial state of `N` particles on
`[0, L̃_N]³`, with upper limit of the ratio at density `ρ̃_N` at most `16/(15π²)`. -/
def Lemma2_1 (V w : R3 → ℝ) : Prop :=
  ∃ Ψ : (N : ℕ) → Conf N → ℂ,
    (∀ᶠ N in atTop, IsDirichletTrial (LtN N) N (Ψ N)) ∧
    limsup (fun N : ℕ => ratio (g0 V w) (rhotN N) ((energyD V (Ψ N) / N : ℝ) : EReal))
      atTop ≤ (cLHY : EReal)

/-- Statement of the duplication step after Lemma 2.1 [thm1] (§2.1): the Dirichlet small-box
bound gives Theorem 2.1 [mainthm]. -/
def DuplicationStep (V w : R3 → ℝ) : Prop := Lemma2_1 V w → MainTheorem V w

/-- Variational principle for `e₀^P`: every normalized `N`-particle state with finite energy
bounds `e₀^P` from above. -/
def VariationalPrinciple (V : R3 → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (Ψ : Occ → ℂ) (E : ℝ), IsNState N Ψ → HasEnergy L V Ψ E →
    e0P L V N ≤ ((E / N : ℝ) : EReal)

/-- The Hamiltonian (2.1) [ham] is nonnegative on finitely supported states. -/
def HamiltonianNonneg (V : R3 → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∀ (Ψ : Occ →₀ ℂ) (E : ℝ), HasEnergy L V Ψ E → 0 ≤ E

/-- Existence and uniqueness of the zero-energy scattering solution (§2). -/
def ScatteringSolutionExistsUnique (V : R3 → ℝ) : Prop :=
  ∃ w, IsScatteringSolution V w ∧ ∀ w', IsScatteringSolution V w' → w' = w

end Stmt

end LHYUpper
