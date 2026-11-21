module

public import LHYUpper.Fock.DecompDefs
public import LHYUpper.TrialState.Defs
public import LHYUpper.Statements

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Shapes of the Section 4 estimates and the final summation

Defines the quantities `V0`, `normGradW2`, `normVw`, `normVw2` and `excess` that enter the
identities at the end of §4, the iterated limit superior `limsup2` in `EReal`, and the shapes
`KinBound` and `PartBound` of the kinetic and interaction-part estimates. Lemma 4.1 [lemkinetic] and
Lemmas 4.2–4.6 [lemHS1], [lemHS2], [lemHS3], [lemHAS1], [lemHAS2] ((4.8)–(4.13)) are stated as
propositions here, and `limsup2_sum_add_le` is the order-theoretic step that adds their bounds. -/

/-- `V₀`, the Fourier coefficient of `V` at `0`. -/
def V0 (V : R3 → ℝ) : ℝ := (ft V 0).re

/-- `‖∇w‖₂²`. -/
def normGradW2 (w : R3 → ℝ) : ℝ := ∫ x, ‖gradient w x‖ ^ 2

/-- `‖Vw‖₁`. -/
def normVw (V w : R3 → ℝ) : ℝ := ∫ x, |V x * w x|

/-- `‖Vw²‖₁`. -/
def normVw2 (V w : R3 → ℝ) : ℝ := ∫ x, |V x * w x ^ 2|

namespace Section4

/-- `(|Λ|⁻¹ E - m ρ₀²) ρ^{-5/2}` at `ρ = ρ_N`, `|Λ| = L_N³`, `ρ₀` of (3.14) [defrho0]. -/
def excess (g m E : ℝ) (N : ℕ) : ℝ :=
  (E / LN N ^ 3 - m * rho0 g (rhoN N) ^ 2) / rhoN N ^ (5/2 : ℝ)

/-- `lim sup_{k_c → ∞} lim sup_{N → ∞}` in `EReal`. -/
def limsup2 (F : ℝ → ℕ → ℝ) : EReal :=
  limsup (fun kc : ℝ => limsup (fun N : ℕ => (F kc N : EReal)) atTop) atTop

/-- `g₀^{3/2}/π²`. -/
def G (V w : R3 → ℝ) : ℝ := g0 V w ^ (3/2 : ℝ) / π ^ 2

/-- Shape of Lemma 4.1 [lemkinetic]: kinetic sums of the trial state with main term `m ρ₀²`
and bound `R`. -/
def KinBound (V w : R3 → ℝ) (m R : ℝ) : Prop :=
  ∃ E : ℝ → ℕ → ℝ,
    (∀ kc : ℝ, ∀ᶠ N in atTop, HasSum (kinTerm (LN N) (trialState V w kc N)) (E kc N)) ∧
    limsup2 (fun kc N => excess (g0 V w) m (E kc N) N) ≤ (R : EReal)

/-- Shape of Lemmas 4.2–4.6: sums of part `j` for the trial state with main term `m ρ₀²` and
bound `R`. -/
def PartBound (V w : R3 → ℝ) (j : Decomp.Part) (m R : ℝ) : Prop :=
  ∃ E : ℝ → ℕ → ℝ,
    (∀ kc : ℝ, ∀ᶠ N in atTop,
      HasSum (Decomp.partTerm j (LN N) V (trialState V w kc N)) (E kc N : ℂ)) ∧
    limsup2 (fun kc N => excess (g0 V w) m (E kc N) N) ≤ (R : EReal)

/-- Two-term step: if `lim sup_{k_c} lim sup_N` of `u` and `v` is at most `A` and `B`, that of
`u + v` is at most `A + B`. -/
private theorem limsup2_add_le (u v : ℝ → ℕ → ℝ) (A B : ℝ)
    (hu : limsup2 u ≤ (A : EReal)) (hv : limsup2 v ≤ (B : EReal)) :
    limsup2 (fun kc N => u kc N + v kc N) ≤ ((A + B : ℝ) : EReal) := by
  have key : ∀ ε : ℝ, 0 < ε →
      limsup2 (fun kc N => u kc N + v kc N) ≤ ((A + B + 2 * ε : ℝ) : EReal) := by
    intro ε hε
    have hu' : ∀ᶠ kc : ℝ in atTop, limsup (fun N : ℕ => (u kc N : EReal)) atTop <
        ((A + ε : ℝ) : EReal) :=
      eventually_lt_of_limsup_lt
        (hu.trans_lt (by exact_mod_cast (by linarith : A < A + ε)))
    have hv' : ∀ᶠ kc : ℝ in atTop, limsup (fun N : ℕ => (v kc N : EReal)) atTop <
        ((B + ε : ℝ) : EReal) :=
      eventually_lt_of_limsup_lt
        (hv.trans_lt (by exact_mod_cast (by linarith : B < B + ε)))
    refine limsup_le_of_le (h := ?_)
    filter_upwards [hu', hv'] with kc h1 h2
    have h3 := EReal.limsup_add_le_of_le (f := atTop) (u := fun N : ℕ => (u kc N : EReal))
      (v := fun N : ℕ => (v kc N : EReal)) h1 h2.le
    have h4 : ((A + ε : ℝ) : EReal) + ((B + ε : ℝ) : EReal) = ((A + B + 2 * ε : ℝ) : EReal) := by
      rw [← EReal.coe_add]; congr 1; ring
    rw [h4] at h3
    simpa only [Pi.add_def, EReal.coe_add] using h3
  refine le_of_forall_gt_imp_ge_of_dense (fun a ha => ?_)
  induction a using EReal.rec with
  | bot => exact absurd ha (not_lt_of_ge bot_le)
  | top => exact le_top
  | coe c =>
    have hc : A + B < c := by exact_mod_cast ha
    have := key ((c - (A + B)) / 2) (by linarith)
    refine this.trans ?_
    exact_mod_cast (by linarith : A + B + 2 * ((c - (A + B)) / 2) ≤ c)

/-- Order-theoretic core of the summation at the end of §4. -/
theorem limsup2_sum_add_le {ι : Type*} (s : Finset ι) (X : ι → ℝ → ℕ → ℝ) (R : ι → ℝ)
    (Y : ℕ → ℝ) (y : ℝ) (hX : ∀ j ∈ s, limsup2 (X j) ≤ (R j : EReal))
    (hY : Tendsto Y atTop (𝓝 y)) :
    limsup2 (fun kc N => ∑ j ∈ s, X j kc N + Y N) ≤ ((∑ j ∈ s, R j + y : ℝ) : EReal) := by
  induction s using Finset.induction_on with
  | empty =>
    have hin : ∀ kc : ℝ, limsup (fun N : ℕ =>
        (((∑ j ∈ (∅ : Finset ι), X j kc N + Y N : ℝ)) : EReal)) atTop = (y : EReal) := by
      intro kc
      apply Tendsto.limsup_eq
      apply (continuous_coe_real_ereal.tendsto _).comp
      simpa using hY
    unfold limsup2
    simp_rw [hin]
    rw [limsup_const]
    simp
  | insert a s ha ih =>
    have h1 := limsup2_add_le (X a) (fun kc N => ∑ j ∈ s, X j kc N + Y N) (R a)
      (∑ j ∈ s, R j + y) (hX a (Finset.mem_insert_self a s))
      (ih (fun j hj => hX j (Finset.mem_insert_of_mem hj)))
    have e1 : (fun kc N => ∑ j ∈ insert a s, X j kc N + Y N) =
        fun kc N => X a kc N + (∑ j ∈ s, X j kc N + Y N) := by
      funext kc N; rw [Finset.sum_insert ha]; ring
    have e2 : ∑ j ∈ insert a s, R j + y = R a + (∑ j ∈ s, R j + y) := by
      rw [Finset.sum_insert ha]; ring
    rw [e1, e2]
    exact h1

end Section4

namespace Stmt

/-- Lemma 4.1 [lemkinetic], (4.8). -/
def Lemma4_1 (V w : R3 → ℝ) : Prop :=
  Section4.KinBound V w (normGradW2 w)
    (4 * normGradW2 w * Section4.G V w / 3 - 8 * g0 V w ^ (5/2 : ℝ) / (5 * π ^ 2))

/-- Lemma 4.2 [lemHS1], (4.9). -/
def Lemma4_2 (V w : R3 → ℝ) : Prop :=
  Section4.PartBound V w .S1 (V0 V) (4 * V0 V * Section4.G V w / 3)

/-- Lemma 4.3 [lemHS2], (4.10). -/
def Lemma4_3 (V w : R3 → ℝ) : Prop :=
  Section4.PartBound V w .S2 (-2 * normVw V w) (2 * V0 V * Section4.G V w)

/-- Lemma 4.4 [lemHS3], (4.11), for `H_{S3}` summed over `u ≠ ±v`. -/
def Lemma4_4 (V w : R3 → ℝ) : Prop :=
  Section4.PartBound V w .S3 (normVw2 V w) (-2 * normVw V w * Section4.G V w)

/-- Lemma 4.5 [lemHAS1], (4.12). -/
def Lemma4_5 (V w : R3 → ℝ) : Prop :=
  Section4.PartBound V w .A1 0 (-8 * normVw V w * Section4.G V w / 3)

/-- Lemma 4.6 [lemHAS2], (4.13). -/
def Lemma4_6 (V w : R3 → ℝ) : Prop :=
  Section4.PartBound V w .A2 0 (4 * normVw2 V w * Section4.G V w / 3)

end Stmt

end LHYUpper
