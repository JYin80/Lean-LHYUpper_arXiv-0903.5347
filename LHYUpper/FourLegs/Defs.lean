module

public import LHYUpper.Assembly.Section4
public import LHYUpper.Scattering.Solution
public import LHYUpper.TrialState.Legs

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Definitions for the four-legs analysis of Sections 9–11

Defines the four momenta `legs` of `a†_p a†_q a_{p-u} a_{q+u}`, the genericity condition `Gen` of
Lemma 9.1 [fourlegslemma1] ((10.7) [conditionk2]), the set `M(k₁, k₂)` (10.8) as `InMk`, the classes
`Cls` of the four legs (cases 1–3 of Lemma 9.1) with their summands `absPart` and `part`, the inner
sum `mainTuple`, and the summand `hardTerm` of (11.2) [resulthardest]. States Lemma 11.1 [113]
((11.1) [totalresultinMk1k2]) as `Lemma11_1` and Lemma 11.2 [thehardestlemma] as `Lemma11_2`. -/

namespace FourLegs

/-- The four momenta `v₁ = p`, `v₂ = q`, `v₃ = p - u`, `v₄ = q + u` of
`a†_{v₁} a†_{v₂} a_{v₃} a_{v₄}` in the interaction summand at `(p, q, u)`. -/
def legs (p q u : Idx) : Fin 4 → Idx := ![p, q, p - u, q + u]

/-- `v_i ≠ ±v_j` for `i ≠ j` (Lemma 9.1 [fourlegslemma1], (10.7) [conditionk2]). -/
def Gen (v : Fin 4 → Idx) : Prop := ∀ i j, i ≠ j → Legs_pm (v i) (v j)

/-- `β ∈ M(k₁, k₂)`, (10.8): `k₁ + k₂ ∈ P_L` and `β = 𝓐^{k₁+k₂, (k₁-k₂)/2} α` for some
`α ∈ M^s_{k₁+k₂}`. -/
def InMk (ρ L kc : ℝ) (N : ℕ) (k₁ k₂ : Idx) (β : Occ) : Prop :=
  InM ρ L kc N β ∧ inPL ρ L (k₁ + k₂) ∧
    ∃ α, InMuS ρ L kc N (k₁ + k₂) α ∧ softPair (k₁ + k₂) k₁ k₂ α = β

/-- The classes of the four legs: cases 1, 2, 3 of Lemma 9.1 [fourlegslemma1], case 2 with
the roles of `(v₁, v₂)` and `(v₃, v₄)` exchanged, and case 4 split into the special legs of
Lemma 10.1, the main term of Lemma 10.2 [101] and the rest of Lemma 11.1 [113]. -/
inductive Cls
  | one | two | twoAdj | three | fourSpecial | fourMain | fourRest
  deriving DecidableEq

instance : Fintype Cls :=
  ⟨⟨{Cls.one, Cls.two, Cls.twoAdj, Cls.three, Cls.fourSpecial, Cls.fourMain, Cls.fourRest},
    by decide⟩, fun c => by cases c <;> decide⟩

/-- Membership of an index `(p, q, u, α)` of the interaction summands in a class; the
resulting state is `β = a†_p a†_q a_{p-u} a_{q+u} α`. -/
def Cls.mem (ρ L kc : ℝ) (N : ℕ) : Cls → Idx × Idx × Idx × Occ → Prop
  | .one, i => ∀ j, inPL ρ L (legs i.1 i.2.1 i.2.2.1 j)
  | .two, i => inPL ρ L i.1 ∧ inPL ρ L i.2.1 ∧ inPHc ρ L kc (i.1 - i.2.2.1) ∧
      inPHc ρ L kc (i.2.1 + i.2.2.1)
  | .twoAdj, i => inPHc ρ L kc i.1 ∧ inPHc ρ L kc i.2.1 ∧ inPL ρ L (i.1 - i.2.2.1) ∧
      inPL ρ L (i.2.1 + i.2.2.1)
  | .three, i => ((inPL ρ L i.1 ∧ inPHc ρ L kc i.2.1) ∨ (inPHc ρ L kc i.1 ∧ inPL ρ L i.2.1)) ∧
      ((inPL ρ L (i.1 - i.2.2.1) ∧ inPHc ρ L kc (i.2.1 + i.2.2.1)) ∨
        (inPHc ρ L kc (i.1 - i.2.2.1) ∧ inPL ρ L (i.2.1 + i.2.2.1)))
  | .fourSpecial, i => (∀ j, inPHc ρ L kc (legs i.1 i.2.1 i.2.2.1 j)) ∧
      ¬ Gen (legs i.1 i.2.1 i.2.2.1)
  | .fourMain, i => (∀ j, inPHc ρ L kc (legs i.1 i.2.1 i.2.2.1 j)) ∧
      Gen (legs i.1 i.2.1 i.2.2.1) ∧
      InMk ρ L kc N i.1 i.2.1 (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2
  | .fourRest, i => (∀ j, inPHc ρ L kc (legs i.1 i.2.1 i.2.2.1 j)) ∧
      Gen (legs i.1 i.2.1 i.2.2.1) ∧
      ¬ InMk ρ L kc N i.1 i.2.1 (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2

/-- `ρ^{-5/2} |Λ|^{-2} Σ_{class c} |V_{v₁-v₃} conj(Ψ(β)) ⟨β| a†_{v₁} a†_{v₂} a_{v₃} a_{v₄} |α⟩ Ψ(α)|`
over the summands of `H_{A2}`, (4.7), at `ρ = ρ_N`, `L = L_N`. -/
def absPart (V w : R3 → ℝ) (c : Cls) (kc : ℝ) (N : ℕ) : ℝ :=
  (∑' i : Idx × Idx × Idx × Occ, if c.mem (rhoN N) (LN N) kc N i then
      ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i‖ else 0) /
    (LN N ^ 3 * rhoN N ^ (5/2 : ℝ))

/-- `ρ^{-5/2} |Λ|^{-2} Re Σ_{class c} V_{v₁-v₃} conj(Ψ(β)) ⟨β| a†_{v₁} a†_{v₂} a_{v₃} a_{v₄} |α⟩ Ψ(α)`
over the summands of `H_{A2}`, (4.7), at `ρ = ρ_N`, `L = L_N`. -/
def part (V w : R3 → ℝ) (c : Cls) (kc : ℝ) (N : ℕ) : ℝ :=
  (∑' i : Idx × Idx × Idx × Occ, if c.mem (rhoN N) (LN N) kc N i then
      Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i else 0).re /
    (LN N ^ 3 * rhoN N ^ (5/2 : ℝ))

/-- `Σ_{β ∈ M(k₁,k₂)} conj(Ψ(β)) ⟨β| a†_{k₁} a†_{k₂} a_{k₃} a_{k₄} |γ⟩ Ψ(γ)`, the inner sum of
(10.10) [resultinMk1k2] and the left side of (10.11) [temp8.140], at `ρ = ρ_N`, `L = L_N`. -/
def mainTuple (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (k₁ k₂ k₃ k₄ : Idx) : ℂ :=
  ∑' γ : Occ, if InMk (rhoN N) (LN N) kc N k₁ k₂ (a4 k₁ k₂ k₃ k₄ γ).2 then
    conj (trialState V w kc N (a4 k₁ k₂ k₃ k₄ γ).2) * ((a4 k₁ k₂ k₃ k₄ γ).1 : ℂ) *
      trialState V w kc N γ else 0

/-- The summand `|Ψ(β) Ψ(γ)|` of (11.2) [resulthardest]: the legs satisfy (10.7) [conditionk2],
`β ∉ M(k₁, k₂)` and `⟨β| a†_{k₁} a†_{k₂} a_{k₃} a_{k₄} |γ⟩ ≠ 0`, (11.3) [defnastk1234]; the index
is `(k₁, k₂, k₁ - k₃, γ)`. -/
def hardTerm (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (i : Idx × Idx × Idx × Occ) : ℝ :=
  if Cls.mem (rhoN N) (LN N) kc N .fourRest i ∧
      (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).1 ≠ 0 then
    ‖trialState V w kc N (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2‖ *
      ‖trialState V w kc N i.2.2.2‖
  else 0

end FourLegs

namespace Stmt

/-- Lemma 11.1 [113], (11.1) [totalresultinMk1k2], with the rate `ρ^{1/2}`: for every `k_c`,
eventually in `N`, the four-leg terms of `H_{A2}` with legs (10.7) [conditionk2] and
`β ∉ M(k₁, k₂)` are at most `ρ^{1/2}` after `ρ^{-5/2}|Λ|^{-2}`. -/
def Lemma11_1 (V w : R3 → ℝ) : Prop :=
  ∀ kc : ℝ, ∀ᶠ N in atTop, FourLegs.absPart V w .fourRest kc N ≤ rhoN N ^ (1/2 : ℝ)

/-- Lemma 11.2 [thehardestlemma], (11.2) [resulthardest]: for every `k_c`, eventually in `N`,
`Σ_{(10.7)} Σ_{β ∉ M(k₁,k₂), γ} |Ψ(β) Ψ(γ)| ≤ |Λ|`, the sum running over `β, γ` with
(11.3) [defnastk1234]. -/
def Lemma11_2 (V w : R3 → ℝ) : Prop :=
  ∀ kc : ℝ, ∀ᶠ N in atTop, Summable (FourLegs.hardTerm V w kc N) ∧
    ∑' i, FourLegs.hardTerm V w kc N i ≤ LN N ^ 3

end Stmt

end LHYUpper
