module

public import Mathlib

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-!
# The second order (Lee–Huang–Yang) upper bound for the ground state energy of a dilute Bose gas

This file is the statement of the main result of

> H.-T. Yau and J. Yin, *The Second Order Upper Bound for the Ground Energy of a Bose Gas*,
> J. Stat. Phys. 136 (2009), 453–503, arXiv:0903.5347,

with the definitions it uses. It imports Mathlib and nothing else. The proof is in the library
`LHYUpper`; `Solution.lean` connects the statement below to the theorem of the library that
proves it.

## The model

`N` bosons move in the box `Λ = [0, L]³ ⊂ ℝ³` with periodic boundary condition and interact
through a pair potential `V : ℝ³ → ℝ`. With momenta `k ∈ Λ* = (2π/L)ℤ³` and the Fourier transform
`V̂(u) = ∫ e^{-iux} V(x) dx` on `ℝ³`, the Hamiltonian is (2.1) of the paper,

  `H = Σ_k |k|² a†_k a_k + |Λ|⁻¹ Σ_{p,q,u} V̂(u) a†_p a†_q a_{p-u} a_{q+u}`.

There is no factor `1/2` in front of the interaction: each pair is counted twice, as in
`Σ_i (-Δ_i) + Σ_{i≠j} V(x_i - x_j)`. This is the normalization in which the zero-energy scattering
equation is `-Δ(1 - w) + V(1 - w) = 0` and `g₀ = ∫ V(1 - w) = 4πa`, `a` the scattering length.

States are written in the occupation-number basis: `Occ` is the type of finitely supported
`α : ℤ³ → ℕ`, and a state is a function `Ψ : Occ → ℂ`, the coefficient of the normalized
occupation state `|α⟩`. `HasEnergy L V Ψ E` says that the kinetic and the interaction series of
`⟨Ψ, HΨ⟩` converge unconditionally and add up to `E`; `IsNState N Ψ` says that `Ψ` is normalized
and supported on `N`-particle occupations. The ground state energy per particle `e0P L V N` is
the infimum of `E / N` over finitely supported normalized `N`-particle states, in `EReal`.

## The statement

`leeHuangYangUpperBound` is Theorem 2.1 of the paper: if `V` satisfies `PotentialHyp V` and
`1 - w` is the zero-energy scattering solution, then

  `limsup_{ρ → 0⁺} limsup_{L → ∞, N/L³ → ρ} (e₀^P - g₀ ρ) / (g₀^{5/2} ρ^{3/2}) ≤ 16/(15π²)`.

With `g₀ = 4πa` this is the upper bound in the Lee–Huang–Yang formula
`e₀(ρ) = 4πaρ (1 + (128/(15√π)) (ρa³)^{1/2} + ⋯)`, since
`4πaρ · (128/(15√π)) (ρa³)^{1/2} = (16/(15π²)) g₀^{5/2} ρ^{3/2}`.

## Relation to the printed statement

* The paper defines `e₀^P` as `inf spec H / N` on the `N`-particle space. Here `e0P` is the
  infimum over finitely supported normalized states in the occupation-number basis. That this
  infimum is at least `inf spec H / N`, so that the bound below gives the paper's, is a standard
  fact that is not formalized; the equality of the two is not formalized either.
* "Smooth with fast decay" is read as `V` being a Schwartz function, "symmetric" as `V` even, and
  "small enough that the Born series converges" as `sup_x ∫ V(y) / (4π|x - y|) dy < 1`. The
  hypothesis that `V` is not identically zero is added; it makes `g₀ > 0` (proved in the library,
  `LHYUpper.scat_g0_pos`), and the ratio divides by `g₀^{5/2}`.
* The scattering solution enters as the hypothesis `IsScatteringSolution V w`. The library proves
  that under `PotentialHyp V` there is exactly one such `w` (`LHYUpper.scattering_exists_unique`).
* All upper limits are taken in `EReal`. The inner one is along the filter `thermo ρ` on pairs
  `(N, L)`, which is proper for `ρ > 0` (`LHYUpper.thermo_neBot`); the outer one is along `ρ → 0⁺`.
* The library also proves that `E ≥ 0` for every state in the infimum defining `e0P`
  (`LHYUpper.hamiltonianNonneg`), so `e0P ≥ 0` and the bound is not satisfied by `e0P = -∞`, and
  that `PotentialHyp` holds for the Gaussian `V(x) = e^{-|x|²}`
  (`LHYUpper.scat_gaussian_potentialHyp`). These facts are not among the compared statements.

The remarks after Theorem 2.1 in the paper (the same bound with Dirichlet boundary condition in
the thermodynamic limit, and an error bound) are not part of this statement.
-/

/-! ### Definitions -/

/-- Position space ℝ³. -/
abbrev R3 := EuclideanSpace ℝ (Fin 3)

/-- Lattice index `n ∈ ℤ³` of the momentum `(2π/L) n ∈ Λ* = (2π/L)ℤ³` (§2). -/
abbrev Idx := Fin 3 → ℤ

/-- The momentum `(2π/L) n ∈ Λ*` as a point of ℝ³. -/
def mom (L : ℝ) (n : Idx) : R3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => (2 * π / L) * (n i : ℝ))

/-- Fourier transform of §2: `W_p = ∫_{ℝ³} e^{-ipx} W(x) dx`. -/
def ft (W : R3 → ℝ) (p : R3) : ℂ :=
  ∫ x, Complex.exp (-(Complex.I * ((inner ℝ p x : ℝ) : ℂ))) * (W x : ℂ)

/-- Hypotheses of Theorem 2.1 [mainthm] on the potential (§2): smooth and of fast decay, read
as `V` being a Schwartz function; symmetric, read as even; nonnegative; not identically zero,
so that `g₀ > 0`; small enough that the Born series converges, in the sufficient form
`sup_x ∫ V(y) / (4π|x-y|) dy < 1`. -/
structure PotentialHyp (V : R3 → ℝ) : Prop where
  schwartz : ∃ S : SchwartzMap R3 ℝ, (S : R3 → ℝ) = V
  even : ∀ x, V (-x) = V x
  nonneg : ∀ x, 0 ≤ V x
  ne_zero : ∃ x, V x ≠ 0
  born : ∃ c < 1, ∀ x, ∫ y, V y / (4 * π * ‖x - y‖) ≤ c

/-- `1 - w` is the zero-energy scattering solution: `-Δ(1-w) + V(1-w) = 0`, `0 ≤ w < 1`,
`w(x) → 0` as `|x| → ∞` (§2). -/
structure IsScatteringSolution (V w : R3 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 w
  eqn : ∀ x, -(Laplacian.laplacian (fun y => 1 - w y) x) + V x * (1 - w x) = 0
  nonneg : ∀ x, 0 ≤ w x
  lt_one : ∀ x, w x < 1
  tendsto_zero : Tendsto w (cocompact R3) (𝓝 0)

/-- `g = V(1 - w)`, (3.12) [gdef]. -/
def gfun (V w : R3 → ℝ) (x : R3) : ℝ := V x * (1 - w x)

/-- `g₀ = 4πa = ∫ V(1 - w)` (§2). -/
def g0 (V w : R3 → ℝ) : ℝ := ∫ x, gfun V w x

/-- The approximate condensate density `ρ₀ = ρ - (3π²)⁻¹ g₀^{3/2} ρ^{3/2}`, (3.14) [defrho0].
Not used in the statements below; kept so that this file repeats `LHYUpper/Model/Basic.lean`
definition by definition. -/
def rho0 (g ρ : ℝ) : ℝ := ρ - (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) * ρ ^ (3/2 : ℝ)

/-- `ρ_ε = ρ₀ + ε ρ^{3/2}`, (3.14) [defrho0]. Not used in the statements below. -/
def rhoEps (g ρ ε : ℝ) : ℝ := rho0 g ρ + ε * ρ ^ (3/2 : ℝ)

/-- The ratio `(e - g₀ρ) / (g₀^{5/2} ρ^{3/2})` of Theorem 2.1 [mainthm], in `[-∞, ∞]`. -/
def ratio (g : ℝ) (ρ : ℝ) (e : EReal) : EReal :=
  (e - ((g * ρ : ℝ) : EReal)) * (((g ^ (5/2 : ℝ) * ρ ^ (3/2 : ℝ))⁻¹ : ℝ) : EReal)

/-- The constant `16/(15π²)` of Theorem 2.1 [mainthm]. -/
def cLHY : ℝ := 16 / (15 * π ^ 2)

/-- The filter `L → ∞, N/L³ → ρ` on pairs `(N, L)` (§2). -/
def thermo (ρ : ℝ) : Filter (ℕ × ℝ) :=
  comap (fun x : ℕ × ℝ => x.2) atTop ⊓ comap (fun x : ℕ × ℝ => (x.1 : ℝ) / x.2 ^ 3) (𝓝 ρ)

/-- Occupation numbers `α : Λ* → ℕ` with finite support. -/
abbrev Occ := Idx →₀ ℕ

/-- Particle number `Σ_k α(k)`. -/
def Occ.num (α : Occ) : ℕ := α.sum (fun _ m => m)

/-- Action of `a†_p a†_q a_r a_s` on the normalized occupation state `|α⟩`, under
`[a_p, a†_q] = δ_{pq}`: the coefficient and the resulting occupation. -/
def a4 (p q r s : Idx) (α : Occ) : ℝ × Occ :=
  let α1 := α - Finsupp.single s 1
  let α2 := α1 - Finsupp.single r 1
  let α3 := α2 + Finsupp.single q 1
  let α4 := α3 + Finsupp.single p 1
  (Real.sqrt (α s) * Real.sqrt (α1 r) * Real.sqrt (α3 q) * Real.sqrt (α4 p), α4)

/-- Kinetic summand `|Ψ(α)|² Σ_k |k|² α(k)` of `⟨Ψ, H Ψ⟩` for (2.1) [ham]. -/
def kinTerm (L : ℝ) (Ψ : Occ → ℂ) (α : Occ) : ℝ :=
  ‖Ψ α‖ ^ 2 * ∑ n ∈ α.support, ‖mom L n‖ ^ 2 * (α n : ℝ)

/-- Interaction summand of `⟨Ψ, H Ψ⟩` for (2.1) [ham], indexed by `(p, q, u, α)`:
`|Λ|⁻¹ V_u conj(Ψ(β)) ⟨β| a†_p a†_q a_{p-u} a_{q+u} |α⟩ Ψ(α)`. -/
def intTerm (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) : ℂ :=
  let p := i.1; let q := i.2.1; let u := i.2.2.1; let α := i.2.2.2
  let t := a4 p q (p - u) (q + u) α
  (L ^ 3)⁻¹ * ft V (mom L u) * conj (Ψ t.2) * (t.1 : ℂ) * Ψ α

/-- `Ψ` has energy `E = ⟨Ψ, H Ψ⟩` for (2.1) [ham] on the torus of side `L`: the kinetic and
the interaction series converge unconditionally and add up to `E`. -/
def HasEnergy (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (E : ℝ) : Prop :=
  ∃ K : ℝ, ∃ I : ℂ, HasSum (kinTerm L Ψ) K ∧ HasSum (intTerm L V Ψ) I ∧ (E : ℂ) = K + I

/-- `Ψ` is a normalized state of `𝓗_N` in the occupation-number basis. -/
def IsNState (N : ℕ) (Ψ : Occ → ℂ) : Prop :=
  HasSum (fun α => ‖Ψ α‖ ^ 2) 1 ∧ ∀ α, Ψ α ≠ 0 → α.num = N

/-- The ground state energy per particle `e₀^P(ρ, Λ)` for (2.1) [ham] on `Λ = [0,L]³` with
periodic boundary condition (§2), as the infimum of `⟨Ψ, HΨ⟩ / N` over finitely supported
normalized `Ψ ∈ 𝓗_N`. -/
def e0P (L : ℝ) (V : R3 → ℝ) (N : ℕ) : EReal :=
  ⨅ (Ψ : Occ →₀ ℂ) (E : ℝ) (_ : IsNState N Ψ ∧ HasEnergy L V Ψ E), ((E / N : ℝ) : EReal)

/-! ### The main result -/

/-- **Theorem 2.1 of Yau–Yin (the Lee–Huang–Yang upper bound).** If `V` satisfies the hypotheses
`PotentialHyp V` and `1 - w` is the zero-energy scattering solution, then the upper limit as
`ρ → 0⁺` of the upper limit as `L → ∞` with `N/L³ → ρ` of
`(e₀^P - g₀ρ) / (g₀^{5/2} ρ^{3/2})` is at most `16/(15π²)`, where `g₀ = ∫ V(1 - w) = 4πa` and
`e₀^P` is the ground state energy per particle of `N` bosons in `[0, L]³` with periodic boundary
condition. -/
theorem leeHuangYangUpperBound {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    limsup (fun ρ : ℝ => limsup (fun x : ℕ × ℝ => ratio (g0 V w) ρ (e0P x.2 V x.1))
      (thermo ρ)) (𝓝[>] 0) ≤ (cLHY : EReal) := by
  sorry

end LHYUpper
