import LHYUpper.Model.Basic

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Dirichlet trial functions and the Dirichlet ground state energy

Defines configurations `Conf N`, the admissible Dirichlet trial functions `IsDirichletTrial` on the
box `[0, L]³`, the energy `energyD` of a trial function in position space, and the ground state
energy per particle `e0D` with Dirichlet boundary conditions, the quantity of Lemma 2.1 [thm1] and
Theorem 2.1 [mainthm]. -/

/-- Configurations `(x_1, …, x_N) ∈ (ℝ³)^N`. -/
abbrev Conf (N : ℕ) := Fin N → R3

/-- Admissible Dirichlet trial functions on `[0,L]³`: smooth, compactly supported in the open
box, symmetric, normalized. -/
def IsDirichletTrial (L : ℝ) (N : ℕ) (Ψ : Conf N → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) Ψ ∧ HasCompactSupport Ψ ∧
  tsupport Ψ ⊆ {x | ∀ i a, 0 < (x i) a ∧ (x i) a < L} ∧
  (∀ σ : Equiv.Perm (Fin N), ∀ x, Ψ (x ∘ σ) = Ψ x) ∧ ∫ x, ‖Ψ x‖ ^ 2 = 1

/-- `⟨Ψ, (Σ_i -Δ_i + Σ_{i≠j} V(x_i - x_j)) Ψ⟩` in position space. -/
def energyD (V : R3 → ℝ) {N : ℕ} (Ψ : Conf N → ℂ) : ℝ :=
  ∫ x, ((∑ i, ∑ a : Fin 3, ‖fderiv ℝ Ψ x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2) +
    (∑ i, ∑ j, if i ≠ j then V (x i - x j) else 0) * ‖Ψ x‖ ^ 2)

/-- The ground state energy per particle `e₀^D(ρ, Λ)` on `Λ = [0,L]³` with Dirichlet boundary
condition (§2). -/
def e0D (L : ℝ) (V : R3 → ℝ) (N : ℕ) : EReal :=
  ⨅ (Ψ : Conf N → ℂ) (_ : IsDirichletTrial L N Ψ), ((energyD V Ψ / N : ℝ) : EReal)

end LHYUpper
