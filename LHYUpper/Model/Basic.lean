import Mathlib

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # The model and the basic quantities of the main theorem

Sets up §2: position space `R3`, lattice indices `Idx` and momenta `mom`, the Fourier transform
`ft`, the hypotheses `PotentialHyp` of Theorem 2.1 [mainthm] on the potential, and the zero-energy
scattering solution `IsScatteringSolution`. Defines `gfun` (3.12) [gdef], `g0`, the density `rho0`
and `rhoEps` (3.14) [defrho0], the ratio and the constant `cLHY = 16/(15π²)` of Theorem 2.1, and the
thermodynamic filter `thermo`. -/

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

/-- The approximate condensate density `ρ₀ = ρ - (3π²)⁻¹ g₀^{3/2} ρ^{3/2}`, (3.14) [defrho0]. -/
def rho0 (g ρ : ℝ) : ℝ := ρ - (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) * ρ ^ (3/2 : ℝ)

/-- `ρ_ε = ρ₀ + ε ρ^{3/2}`, (3.14) [defrho0]. -/
def rhoEps (g ρ ε : ℝ) : ℝ := rho0 g ρ + ε * ρ ^ (3/2 : ℝ)

/-- The ratio `(e - g₀ρ) / (g₀^{5/2} ρ^{3/2})` of Theorem 2.1 [mainthm], in `[-∞, ∞]`. -/
def ratio (g : ℝ) (ρ : ℝ) (e : EReal) : EReal :=
  (e - ((g * ρ : ℝ) : EReal)) * (((g ^ (5/2 : ℝ) * ρ ^ (3/2 : ℝ))⁻¹ : ℝ) : EReal)

/-- The constant `16/(15π²)` of Theorem 2.1 [mainthm]. -/
def cLHY : ℝ := 16 / (15 * π ^ 2)

/-- The filter `L → ∞, N/L³ → ρ` on pairs `(N, L)` (§2). -/
def thermo (ρ : ℝ) : Filter (ℕ × ℝ) :=
  comap (fun x : ℕ × ℝ => x.2) atTop ⊓ comap (fun x : ℕ × ℝ => (x.1 : ℝ) / x.2 ^ 3) (𝓝 ρ)

end LHYUpper
