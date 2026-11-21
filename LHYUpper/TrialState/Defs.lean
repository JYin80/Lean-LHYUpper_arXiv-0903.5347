module

public import LHYUpper.Model.Fock

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Definitions for the trial state

Definitions of §3: the sequences `rhoN`, `LN` (Theorem 3.1 [lemma2.1]), `LtN`, `rhotN` (Lemma 2.2
[lemma1]), `epsP` (3.2) [defepseta] and `mc` (3.8) [defmc], the regions `inPL`, `inPI`, `inPH` of
Definition 3.1 [def1], `alphaStar` (3.10) [def*], the strict and soft pair creations of Definition
3.3, the set `M` of Definition 3.4 [M] with `InMuS` and `InMuA` (3.9) [defMsau], `λ_k` as `lam`
(3.15) [lambda], and the square root convention `csqrt` of Definition 3.6, and the weight `f0` of
(3.18) [deffal] with the trial state `trialState`. -/

/-- `ρ_N = N^{-8/17}`, so that `L_N = ρ_N^{-25/24}` gives `ρ_N L_N³ = N` (Theorem 3.1 [lemma2.1]). -/
def rhoN (N : ℕ) : ℝ := (N : ℝ) ^ (-(8/17 : ℝ))

/-- `L_N = ρ_N^{-25/24}` (Theorem 3.1 [lemma2.1]). -/
def LN (N : ℕ) : ℝ := rhoN N ^ (-(25/24 : ℝ))

/-- `L̃ = L(1 + 2ρ^{25/48})` of Lemma 2.2 [lemma1]. -/
def LtN (N : ℕ) : ℝ := LN N * (1 + 2 * rhoN N ^ (25/48 : ℝ))

/-- `ρ̃ = ρL³/L̃³ = N/L̃³` of Lemma 2.2 [lemma1]. -/
def rhotN (N : ℕ) : ℝ := (N : ℝ) / LtN N ^ 3

/-- `ε_L = η_L = ε_H = ρ^η` with `η = 1/200`, (3.2) [defepseta]. -/
def epsP (ρ : ℝ) : ℝ := ρ ^ (1/200 : ℝ)

/-- `m_c = ρ^{-η}`, (3.8) [defmc]. -/
def mc (ρ : ℝ) : ℝ := ρ ^ (-(1/200 : ℝ))

/-- `P_L` of Definition 3.1 [def1]. -/
def inPL (ρ L : ℝ) (n : Idx) : Prop :=
  epsP ρ * ρ ^ (1/2 : ℝ) ≤ ‖mom L n‖ ∧ ‖mom L n‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ)

/-- `P_I` of Definition 3.1 [def1]. -/
def inPI (ρ L : ℝ) (n : Idx) : Prop :=
  (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) < ‖mom L n‖ ∧ ‖mom L n‖ ≤ epsP ρ

/-- `P_H` of Definition 3.1 [def1]. -/
def inPH (ρ L : ℝ) (n : Idx) : Prop := epsP ρ < ‖mom L n‖

/-- `α*(u) = max {α(u), α(-u)}`, (3.10) [def*]. -/
def alphaStar (α : Occ) (u : Idx) : ℕ := max (α u) (α (-u))

/-- Strict pair creation `𝓐^k` (Definition 3.3, item 1). -/
def strictPair (k : Idx) (α : Occ) : Occ :=
  α - Finsupp.single 0 2 + Finsupp.single k 1 + Finsupp.single (-k) 1

/-- Soft pair creation `𝓐^{u,k}` (Definition 3.3, item 2), parametrized by the two created
momenta `p₁ = k + u/2`, `p₂ = -k + u/2` with `p₁ + p₂ = u`. -/
def softPair (u p₁ p₂ : Idx) (α : Occ) : Occ :=
  α - Finsupp.single 0 1 - Finsupp.single u 1 + Finsupp.single p₁ 1 + Finsupp.single p₂ 1

/-- The set `M` of Definition 3.4 [M]: the smallest set containing `α_free` and closed
under rules 2–4. -/
inductive InM (ρ L kc : ℝ) (N : ℕ) : Occ → Prop
  | free : InM ρ L kc N (Finsupp.single 0 N)
  | strictIH {α : Occ} {k : Idx} : InM ρ L kc N α → (inPI ρ L k ∨ inPH ρ L k) → 2 ≤ α 0 →
      InM ρ L kc N (strictPair k α)
  | strictL {α : Occ} {k : Idx} : InM ρ L kc N α → inPL ρ L k →
      ((alphaStar α k : ℕ) : ℝ) < mc ρ → 2 ≤ α 0 → InM ρ L kc N (strictPair k α)
  | soft {α : Occ} {u p₁ p₂ : Idx} : InM ρ L kc N α → inPL ρ L u → α u = α (-u) →
      p₁ + p₂ = u → inPH ρ L p₁ → inPH ρ L p₂ → ‖mom L p₁‖ ≤ kc → ‖mom L p₂‖ ≤ kc →
      1 ≤ α 0 → 1 ≤ α u → InM ρ L kc N (softPair u p₁ p₂ α)

/-- `M_u^s = {α ∈ M | α(u) = α(-u)}`, (3.9) [defMsau]. -/
def InMuS (ρ L kc : ℝ) (N : ℕ) (u : Idx) (α : Occ) : Prop := InM ρ L kc N α ∧ α u = α (-u)

/-- `M_u^a = {α ∈ M | α(u) ≠ α(-u)}`, (3.9) [defMsau]. -/
def InMuA (ρ L kc : ℝ) (N : ℕ) (u : Idx) (α : Occ) : Prop := InM ρ L kc N α ∧ α u ≠ α (-u)

/-- `λ_k` of (3.15) [lambda]; `w_k = g_k / |k|²` by (3.13) [gp]. -/
def lam (V w : R3 → ℝ) (ρ L : ℝ) (n : Idx) : ℝ :=
  if inPL ρ L n then
    (1 - Real.sqrt (1 + 4 * ρ * g0 V w / ‖mom L n‖ ^ 2)) /
      (1 + Real.sqrt (1 + 4 * ρ * g0 V w / ‖mom L n‖ ^ 2)) / ρ
  else -(ft (gfun V w) (mom L n)).re / ‖mom L n‖ ^ 2

/-- Square root with the convention `√x = i√|x|` for `x < 0` (Definition 3.6). -/
def csqrt (x : ℝ) : ℂ := if 0 ≤ x then (Real.sqrt x : ℂ) else (Real.sqrt (-x) : ℂ) * Complex.I

/-- The weight `f(α)` of (3.18) [deffal] without the normalization constant `C_N`. -/
def f0 (V w : R3 → ℝ) (ρ L : ℝ) (α : Occ) : ℂ :=
  (Real.sqrt ((L ^ 3) ^ (α 0) / (Nat.factorial (α 0))) : ℂ) *
  (∏ n ∈ α.support.filter (· ≠ 0), csqrt (lam V w ρ L n) ^ (α n)) *
  ∏ u ∈ (α.support.image Neg.neg).filter
      (fun u => inPL ρ L u ∧ alphaStar α u = α u + 1),
    csqrt (4 * (alphaStar α u : ℝ) * lam V w ρ L u / L ^ 3)

/-- The trial state `Ψ = Σ_{α ∈ M} f(α)|α⟩` of (3.18) [deffal], with `C_N` the
normalization constant, at `ρ = ρ_N`, `L = L_N`. -/
def trialState (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (α : Occ) : ℂ :=
  let ρ := rhoN N; let L := LN N
  let Z : ℝ := ∑' β, if InM ρ L kc N β then ‖f0 V w ρ L β‖ ^ 2 else 0
  if InM ρ L kc N α then ((Real.sqrt Z)⁻¹ : ℂ) * f0 V w ρ L α else 0

end LHYUpper
