import LHYUpper.Assembly.Section4
import LHYUpper.Riemann.Bridge
import LHYUpper.Scattering.Identities

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Auxiliary facts -/

/-- `mom L 0 = 0`. -/
private lemma MainTerm_mom_zero (L : ℝ) : mom L 0 = 0 := by
  ext i
  simp [mom]

/-- `P_L ∪ P_I ∪ P_H = {ε_L ρ^{1/2} ≤ |u|}` for `0 < ρ ≤ 1` (Definition 3.1 [def1]). -/
private theorem MainTerm_union {ρ L : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (n : Idx) :
    (inPL ρ L n ∨ inPI ρ L n ∨ inPH ρ L n) ↔ epsP ρ * ρ ^ (1/2 : ℝ) ≤ ‖mom L n‖ := by
  have he0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have he1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hs1 : ρ ^ (1/2 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have h1 : epsP ρ * ρ ^ (1/2 : ℝ) ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := by
    gcongr
    exact he1.trans ((one_le_inv₀ he0).2 he1)
  have h2 : epsP ρ * ρ ^ (1/2 : ℝ) ≤ epsP ρ := mul_le_of_le_one_right he0.le hs1
  unfold inPL inPI inPH
  constructor
  · rintro (h | h | h)
    · exact h.1
    · exact h1.trans h.1.le
    · exact h2.trans h.le
  · intro h
    by_cases ha : ‖mom L n‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ)
    · exact Or.inl ⟨h, ha⟩
    · by_cases hb : ‖mom L n‖ ≤ epsP ρ
      · exact Or.inr (Or.inl ⟨not_le.mp ha, hb⟩)
      · exact Or.inr (Or.inr (not_le.mp hb))

/-- The closed and the open exterior ball `{r ≤ |p|}`, `{r < |p|}` are shells with
`r₂ = ∞`, `s = 0`. -/
private theorem MainTerm_shell (r : ℝ) :
    IsShell r ⊤ 0 {p : R3 | r ≤ ‖p‖} ∧ IsShell r ⊤ 0 {p : R3 | r < ‖p‖} :=
  ⟨⟨fun p h1 _ => by simp only [add_zero] at h1; exact h1.le, fun p hp => ⟨hp, le_top⟩⟩,
   ⟨fun p h1 _ => by simpa using h1, fun p hp => ⟨hp.le, le_top⟩⟩⟩

/-- `0 < ρ_N ≤ 1` for `N ≥ 1`. -/
private lemma MainTerm_rhoN {N : ℕ} (hN : 1 ≤ N) : 0 < rhoN N ∧ rhoN N ≤ 1 :=
  ⟨Real.rpow_pos_of_pos (by exact_mod_cast hN) _,
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)⟩

/-- `2π ≤ L_N` for `N ≥ 2^51`: `L_N = N^{25/51}`. -/
private lemma MainTerm_two_pi_le_LN {N : ℕ} (hN : 2 ^ 51 ≤ N) : 2 * π ≤ LN N := by
  have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL : LN N = (N : ℝ) ^ (25 / 51 : ℝ) := by
    rw [LN, rhoN, ← Real.rpow_mul hNpos.le]
    norm_num
  have h2 : ((2 : ℝ) ^ 51) ^ (25 / 51 : ℝ) = 2 ^ 25 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    norm_num
  have h3 : ((2 : ℝ) ^ 51) ^ (25 / 51 : ℝ) ≤ (N : ℝ) ^ (25 / 51 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN) (by norm_num)
  rw [hL]
  have h4 := Real.pi_le_four
  have h5 : (2 : ℝ) * 4 ≤ 2 ^ 25 := by norm_num
  linarith

/-- `E_2(δ) = δ(1 + log δ⁻¹) ≤ δ + 2 δ^{1/2}` for `δ > 0`. -/
private lemma MainTerm_riemannRate_le {δ : ℝ} (hδ : 0 < δ) :
    riemannRate 2 δ ≤ δ + 2 * δ ^ (1/2 : ℝ) := by
  have hs : 0 < δ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hsq : δ ^ (1/2 : ℝ) * δ ^ (1/2 : ℝ) = δ := by
    rw [← Real.rpow_add hδ]
    norm_num
  have hlog : Real.log δ⁻¹ ≤ (δ⁻¹) ^ (1/2 : ℝ) / (1/2) :=
    Real.log_le_rpow_div (inv_nonneg.2 hδ.le) (by norm_num)
  rw [Real.inv_rpow hδ.le] at hlog
  have hrate : riemannRate 2 δ = δ * (1 + Real.log δ⁻¹) := by
    simp [riemannRate]
  rw [hrate]
  have h1 : δ * Real.log δ⁻¹ ≤ δ * ((δ ^ (1/2 : ℝ))⁻¹ / (1/2)) :=
    mul_le_mul_of_nonneg_left hlog hδ.le
  have h2 : δ * ((δ ^ (1/2 : ℝ))⁻¹ / (1/2)) = 2 * δ ^ (1/2 : ℝ) := by
    generalize δ ^ (1/2 : ℝ) = s at hs hsq ⊢
    subst hsq
    field_simp
  nlinarith

/-- The rate bookkeeping of `K (r + E_2(2π/L))` at `L = ρ^{-25/24}`: for `0 < ρ ≤ 1`,
`e ≤ 25/48` and `r ≤ ρ^e`, the sum is at most `(1 + 2π + 2 (2π)^{1/2}) ρ^e`. -/
private lemma MainTerm_rate {ρ e r : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (he : e ≤ 25 / 48)
    (hr : r ≤ ρ ^ e) :
    r + riemannRate 2 (2 * π / ρ ^ (-(25/24 : ℝ)))
      ≤ (1 + 2 * π + 2 * (2 * π) ^ (1/2 : ℝ)) * ρ ^ e := by
  have hpi := Real.pi_pos
  have hh : 2 * π / ρ ^ (-(25/24 : ℝ)) = 2 * π * ρ ^ (25/24 : ℝ) := by
    rw [Real.rpow_neg hρ.le, div_inv_eq_mul]
  rw [hh]
  have hpos : 0 < 2 * π * ρ ^ (25/24 : ℝ) := by positivity
  have h1 := MainTerm_riemannRate_le hpos
  have h2 : ρ ^ (25/24 : ℝ) ≤ ρ ^ e :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (he.trans (by norm_num))
  have h3 : ρ ^ (25/48 : ℝ) ≤ ρ ^ e := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 he
  have h4 : (2 * π * ρ ^ (25/24 : ℝ)) ^ (1/2 : ℝ) = (2 * π) ^ (1/2 : ℝ) * ρ ^ (25/48 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
    norm_num
  have hc : 0 ≤ (2 * π) ^ (1/2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have h5 : 2 * π * ρ ^ (25/24 : ℝ) ≤ 2 * π * ρ ^ e :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h6 : (2 * π) ^ (1/2 : ℝ) * ρ ^ (25/48 : ℝ) ≤ (2 * π) ^ (1/2 : ℝ) * ρ ^ e :=
    mul_le_mul_of_nonneg_left h3 hc
  rw [h4] at h1
  nlinarith

/-- Parseval for the main term of (4.8) [proofthem1-1]: `‖∇w‖₂² = (2π)^{-3} ∫ g_p² |p|^{-2} dp`,
with `g_p = Re ĝ(p)` of (3.13) [gp]. -/
theorem Kinetic_parseval {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    normGradW2 w = ((2 * π) ^ 3)⁻¹ * ∫ p, (ft (gfun V w) p).re ^ 2 / ‖p‖ ^ 2 := by
  have h1 : normGradW2 w = ∫ x, ‖fderiv ℝ w x‖ ^ 2 := by
    unfold normGradW2
    congr 1
    funext x
    simp only [gradient, LinearIsometryEquiv.norm_map]
  rw [h1, scat_grad_w_sq hV hw, inv_pow]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  dsimp only
  conv_lhs => rw [scat_ft_g_real hV hw p]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The lattice sum `|Λ|⁻¹ Σ_{u ∈ Λ*, u ∈ A} |u|² w_u²` over a shell `A` with `r₂ = ∞`, `s = 0`
and the inner radius `r > 0` converges to `‖∇w‖₂²` at the rate `K (r + E_2(2π/L))`: `sum_g2`
with `g_p = Re ĝ(p)` and `M = 4`, then `Kinetic_parseval`; (4.8) [proofthem1-1]. -/
private lemma MainTerm_sum {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L r : ℝ) (A : Set R3) (P : Idx → Prop) [DecidablePred P],
      2 * π ≤ L → 0 < r → MeasurableSet A → IsShell r ⊤ 0 A → (∀ n, P n ↔ mom L n ∈ A) →
      Summable (fun n : Idx => if P n then
          ‖mom L n‖ ^ 2 * wmom V w (mom L n) ^ 2 else 0) ∧
      |(L ^ 3)⁻¹ * (∑' n : Idx, (if P n then
          ‖mom L n‖ ^ 2 * wmom V w (mom L n) ^ 2 else 0)) - normGradW2 w|
        ≤ K * (r + riemannRate 2 (2 * π / L)) := by
  obtain ⟨Cg, hCg⟩ := Bridge_momDecay_g hV hw 4
  obtain ⟨K, hK0, hK⟩ := sum_g2 (le_refl (4 : ℝ)) hCg
  refine ⟨K, hK0, ?_⟩
  intro L r A P _ hL hr hA hS hP
  obtain ⟨hsum, hbd⟩ := hK L r 0 ⊤ A hL hr.le le_rfl ENNReal.zero_lt_top hA hS
  have hfun : (fun n : Idx => if P n then ‖mom L n‖ ^ 2 * wmom V w (mom L n) ^ 2 else 0) =
      fun n : Idx => if n ≠ 0 ∧ mom L n ∈ A then
        (ft (gfun V w) (mom L n)).re ^ 2 / ‖mom L n‖ ^ 2 else 0 := by
    funext n
    by_cases hn : mom L n ∈ A
    · have hn0 : n ≠ 0 := by
        rintro rfl
        have h := (hS.2 _ hn).1
        rw [MainTerm_mom_zero, norm_zero] at h
        linarith
      simp only [(hP n).2 hn, hn0, hn, ne_eq, not_false_eq_true, and_self, ite_true]
      unfold wmom
      by_cases h0 : ‖mom L n‖ = 0
      · simp [h0]
      · field_simp
    · have h1 : ¬ P n := fun h => hn ((hP n).1 h)
      have h2 : ¬ (n ≠ 0 ∧ mom L n ∈ A) := fun h => hn h.2
      simp only [h1, h2, ite_false]
  rw [hfun, Kinetic_parseval hV hw]
  refine ⟨hsum, ?_⟩
  have e2 : ((⊤ : ENNReal)⁻¹).toReal = 0 := by simp
  rw [e2, add_zero, add_zero] at hbd
  exact hbd

/-- The main term of (4.8) [proofthem1-1]: `|Λ|⁻¹ Σ_{u ∈ P_L ∪ P_I ∪ P_H} |u|² w_u²
= ‖∇w‖₂² + O(ρ^{1/2+η})`; the sum runs over `|u| ≥ ε_L ρ^{1/2}`. -/
theorem Kinetic_sum_w2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Summable (fun n : Idx => if inPL (rhoN N) (LN N) n ∨ inPI (rhoN N) (LN N) n ∨
          inPH (rhoN N) (LN N) n then ‖mom (LN N) n‖ ^ 2 * wmom V w (mom (LN N) n) ^ 2 else 0) ∧
      |(LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPL (rhoN N) (LN N) n ∨ inPI (rhoN N) (LN N) n ∨
          inPH (rhoN N) (LN N) n then ‖mom (LN N) n‖ ^ 2 * wmom V w (mom (LN N) n) ^ 2 else 0))
        - normGradW2 w| ≤ C * rhoN N ^ (1/2 + 1/200 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := MainTerm_sum hV hw
  refine ⟨K * (1 + 2 * π + 2 * (2 * π) ^ (1/2 : ℝ)), by positivity, 2 ^ 51, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hN
  obtain ⟨hρ0, hρ1⟩ := MainTerm_rhoN hN1
  have he0 : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ0 _
  have hr : 0 < epsP (rhoN N) * rhoN N ^ (1/2 : ℝ) :=
    mul_pos he0 (Real.rpow_pos_of_pos hρ0 _)
  obtain ⟨hs, hb⟩ := hK (LN N) (epsP (rhoN N) * rhoN N ^ (1/2 : ℝ))
    {p : R3 | epsP (rhoN N) * rhoN N ^ (1/2 : ℝ) ≤ ‖p‖}
    (fun n => inPL (rhoN N) (LN N) n ∨ inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n)
    (MainTerm_two_pi_le_LN hN) hr
    (measurableSet_le measurable_const measurable_norm) (MainTerm_shell _).1
    (fun n => MainTerm_union hρ0 hρ1 n)
  refine ⟨hs, hb.trans ?_⟩
  have hrr : epsP (rhoN N) * rhoN N ^ (1/2 : ℝ) ≤ rhoN N ^ (1/2 + 1/200 : ℝ) := by
    rw [epsP, ← Real.rpow_add hρ0, add_comm]
  have := MainTerm_rate hρ0 hρ1 (e := 1/2 + 1/200) (by norm_num) hrr
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left this hK0

/-- The coefficient of `ρ₀^{5/2}` in (6.4) [boundspsiu2PHtotal] summed against `|u|²`:
`|Λ|⁻¹ Σ_{u ∈ P_H} |u|² w_u² = ‖∇w‖₂² + O(ε_H)`. -/
theorem Kinetic_sum_PH_w2 {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Summable (fun n : Idx => if inPH (rhoN N) (LN N) n then
          ‖mom (LN N) n‖ ^ 2 * wmom V w (mom (LN N) n) ^ 2 else 0) ∧
      |(LN N ^ 3)⁻¹ * (∑' n : Idx, (if inPH (rhoN N) (LN N) n then
          ‖mom (LN N) n‖ ^ 2 * wmom V w (mom (LN N) n) ^ 2 else 0)) - normGradW2 w|
        ≤ C * rhoN N ^ (1/200 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := MainTerm_sum hV hw
  refine ⟨K * (1 + 2 * π + 2 * (2 * π) ^ (1/2 : ℝ)), by positivity, 2 ^ 51, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hN
  obtain ⟨hρ0, hρ1⟩ := MainTerm_rhoN hN1
  have he0 : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ0 _
  obtain ⟨hs, hb⟩ := hK (LN N) (epsP (rhoN N)) {p : R3 | epsP (rhoN N) < ‖p‖}
    (fun n => inPH (rhoN N) (LN N) n) (MainTerm_two_pi_le_LN hN) he0
    (measurableSet_lt measurable_const measurable_norm) (MainTerm_shell _).2
    (fun n => Iff.rfl)
  refine ⟨hs, hb.trans ?_⟩
  have := MainTerm_rate hρ0 hρ1 (e := 1/200) (r := epsP (rhoN N)) (by norm_num) le_rfl
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left this hK0

end LHYUpper
