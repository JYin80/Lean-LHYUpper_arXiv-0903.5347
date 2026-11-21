module

public import LHYUpper.TrialState.Defs

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! # Definitions for the Riemann-sum lemma and the densities

Definitions for the Riemann-sum estimates of §5–§7: the rate `riemannRate`, shells `IsShell`,
lattice sums `latSum` and `latSum2` with their summability predicates, the singularity and decay
hypotheses (H1)–(H2) `SingDecay` and `MomDecay`, the shell `shellPL`, and the densities `hk` (5.34)
[defhk], `rk`, `occDensity` (5.35) [3.1], `kinDensity` (6.3), `potDensity` (7.8) [u-uPL],
`tailDensity` (5.39) [temp6.35] and the value `lamPL` of `λ_u` on `P_L` (3.15) [lambda]. -/

/-- Rate `E_a(δ)`: `δ` for `a < 2`, `δ(1 + log δ⁻¹)` for `a = 2`, `δ^{3-a}` for `a > 2`. -/
def riemannRate (a δ : ℝ) : ℝ :=
  if a < 2 then δ else if a = 2 then δ * (1 + Real.log δ⁻¹) else δ ^ (3 - a)

/-- `A` lies between the open shell `r₁ + s < |p|, |p| + s < r₂` and the closed shell
`r₁ ≤ |p| ≤ r₂` (`r₂ = ∞` allowed). -/
def IsShell (r₁ : ℝ) (r₂ : ℝ≥0∞) (s : ℝ) (A : Set R3) : Prop :=
  (∀ p : R3, r₁ + s < ‖p‖ → ENNReal.ofReal (‖p‖ + s) < r₂ → p ∈ A) ∧
  (∀ p ∈ A, r₁ ≤ ‖p‖ ∧ ENNReal.ofReal ‖p‖ ≤ r₂)

/-- `Σ_{p ∈ Λ* ∩ A, p ≠ 0} F(p)`. -/
def latSum (L : ℝ) (A : Set R3) (F : R3 → ℝ) : ℝ :=
  ∑' n : Idx, if n ≠ 0 ∧ mom L n ∈ A then F (mom L n) else 0

def latSummable (L : ℝ) (A : Set R3) (F : R3 → ℝ) : Prop :=
  Summable (fun n : Idx => if n ≠ 0 ∧ mom L n ∈ A then F (mom L n) else 0)

/-- `Σ_{p, q ∈ Λ* ∩ A, p, q ≠ 0} G(p, q)`. -/
def latSum2 (L : ℝ) (A : Set R3) (G : R3 → R3 → ℝ) : ℝ :=
  ∑' nm : Idx × Idx,
    if nm.1 ≠ 0 ∧ nm.2 ≠ 0 ∧ mom L nm.1 ∈ A ∧ mom L nm.2 ∈ A then G (mom L nm.1) (mom L nm.2)
    else 0

def latSummable2 (L : ℝ) (A : Set R3) (G : R3 → R3 → ℝ) : Prop :=
  Summable (fun nm : Idx × Idx =>
    if nm.1 ≠ 0 ∧ nm.2 ≠ 0 ∧ mom L nm.1 ∈ A ∧ mom L nm.2 ∈ A then G (mom L nm.1) (mom L nm.2)
    else 0)

/-- Hypotheses (H1)–(H2) of the Riemann-sum lemma. -/
structure SingDecay (a b C : ℝ) (F : R3 → ℝ) : Prop where
  bound : ∀ p : R3, p ≠ 0 → |F p| ≤ C * min (‖p‖ ^ (-a)) (‖p‖ ^ (-b))
  lip : ∀ p q : R3, p ≠ 0 → ‖q - p‖ ≤ ‖p‖ / 2 →
    |F q - F p| ≤ C * ‖q - p‖ * min (‖p‖ ^ (-a - 1)) (‖p‖ ^ (-b))

/-- Local hypothesis on `V_p`, `g_p`: bounded with decay `(1 + |p|)^{-M}`, locally Lipschitz
with the same decay. -/
structure MomDecay (f : R3 → ℝ) (C M : ℝ) : Prop where
  bound : ∀ p : R3, |f p| ≤ C * (1 + ‖p‖) ^ (-M)
  lip : ∀ p q : R3, ‖q - p‖ ≤ 1 → |f q - f p| ≤ C * ‖q - p‖ * (1 + ‖p‖) ^ (-M)

/-- The shell `ε_L ≤ |k| ≤ η_L⁻¹` in the variable `k = ρ^{-1/2} u`. -/
def shellPL (ρ : ℝ) : Set R3 := {k | epsP ρ ≤ ‖k‖ ∧ ‖k‖ ≤ (epsP ρ)⁻¹}

/-- `h(k) = √(1 + 4g₀|k|^{-2})`, (5.34) [defhk]. -/
def hk (g : ℝ) (k : R3) : ℝ := Real.sqrt (1 + 4 * g / ‖k‖ ^ 2)

/-- `r(k) = (1 - h(k)) / (1 + h(k))`, the right side of (5.34) [defhk]. -/
def rk (g : ℝ) (k : R3) : ℝ := (1 - hk g k) / (1 + hk g k)

/-- `(h - 1)² / (4h)`, the integrand of (5.35) [3.1]. -/
def occDensity (g : ℝ) (k : R3) : ℝ := (hk g k - 1) ^ 2 / (4 * hk g k)

/-- `k²[(1 + 2g₀k^{-2}) / (2h) - (1 + 2(g₀k^{-2})²) / 2]`, the integrand of (6.3). -/
def kinDensity (g : ℝ) (k : R3) : ℝ :=
  ‖k‖ ^ 2 * ((1 + 2 * g / ‖k‖ ^ 2) / (2 * hk g k) - (1 + 2 * (g / ‖k‖ ^ 2) ^ 2) / 2)

/-- `g₀k^{-2}(1 - h^{-1})`, the integrand in the proof of (7.8) [u-uPL]. -/
def potDensity (g : ℝ) (k : R3) : ℝ := g / ‖k‖ ^ 2 * (1 - 1 / hk g k)

/-- `|r(k)|^t (h - 1)² / (4h)`; `t = 2n` is `H(2n)` of (5.39) [temp6.35]. -/
def tailDensity (g t : ℝ) (k : R3) : ℝ := |rk g k| ^ t * occDensity g k

/-- `λ_u` on `P_L`, (3.15) [lambda]. -/
def lamPL (g ρ : ℝ) (u : R3) : ℝ :=
  (1 - Real.sqrt (1 + 4 * ρ * g / ‖u‖ ^ 2)) / (1 + Real.sqrt (1 + 4 * ρ * g / ‖u‖ ^ 2)) / ρ

end LHYUpper
