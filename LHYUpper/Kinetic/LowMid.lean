module

public import LHYUpper.Particles.UpperIH
public import LHYUpper.Particles.UpperL
public import LHYUpper.Riemann.ScaledLimits
public import LHYUpper.Scattering.WMomentum

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Auxiliary facts on the parameters and on series supported in a ball -/

/-- For all large `N`: `N ≥ 1`, `ε_L ≤ δ` and `2π ≤ L ρ^{1/2}` at `ρ = ρ_N`, `L = L_N`. -/
private lemma LowMid_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ epsP (rhoN N) ≤ δ ∧ 2 * π ≤ LN N * rhoN N ^ (1 / 2 : ℝ) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hP : ∀ {a : ℝ}, 0 < a → Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
    intro a ha
    have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at h
    exact h.comp hT
  have h1 : ∀ᶠ N : ℕ in atTop, epsP (rhoN N) ≤ δ :=
    (hP (by norm_num : (0 : ℝ) < 1 / 200)).eventually (ge_mem_nhds hδ)
  have h2 : ∀ᶠ N : ℕ in atTop, 2 * π * rhoN N ^ (13 / 24 : ℝ) ≤ 1 := by
    have h := (hP (by norm_num : (0 : ℝ) < 13 / 24)).const_mul (2 * π)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop 1, h1, h2] with N hN hε hΔ
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  refine ⟨hN, hε, ?_⟩
  have hq : 0 < rhoN N ^ (13 / 24 : ℝ) := Real.rpow_pos_of_pos hρ _
  have e : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) = 1 := by
    rw [LN, mul_assoc, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  by_contra h
  have h' : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) <
      2 * π * rhoN N ^ (13 / 24 : ℝ) := mul_lt_mul_of_pos_right (not_le.1 h) hq
  linarith

/-- A function on `Idx` supported in `{‖p_n‖ ≤ R}` is summable. -/
private lemma LowMid_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
    (hf : ∀ n, f n ≠ 0 → ‖mom L n‖ ≤ R) : Summable f := by
  have hfin : {n : Idx | ‖mom L n‖ ≤ R}.Finite := by
    set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
    refine (Set.finite_Icc (fun _ : Fin 3 => -B) (fun _ => B)).subset ?_
    intro n hn
    have hi : ∀ i : Fin 3, |(n i : ℝ)| ≤ B := by
      intro i
      have h1 : |(mom L n).ofLp i| ≤ R := by
        have := PiLp.norm_apply_le (mom L n) i
        rw [Real.norm_eq_abs] at this
        exact this.trans hn
      have e : (mom L n).ofLp i = 2 * π / L * (n i : ℝ) := rfl
      rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
      have h2 : |(n i : ℝ)| ≤ L * R / (2 * π) := by
        rw [le_div_iff₀ (by positivity)]
        have := h1
        rw [div_mul_eq_mul_div, div_le_iff₀ hL] at this
        nlinarith
      exact h2.trans (Int.le_ceil _)
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := (abs_le.1 (hi i)).1
      exact_mod_cast this
    · have := (abs_le.1 (hi i)).2
      exact_mod_cast this
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  by_contra h
  exact hn (hfin.mem_toFinset.2 (hf n h))

/-- A termwise estimate of a nonnegative majorant bounds the sum of a family that is zero off a
set, whether or not the family is summable. -/
private lemma LowMid_tsum_le {f g : Idx → ℝ} (hg : Summable g) (hg0 : ∀ n, 0 ≤ g n)
    (hfg : ∀ n, f n ≤ g n) : ∑' n, f n ≤ ∑' n, g n := by
  by_cases hf : Summable f
  · exact hf.tsum_le_tsum hfg hg
  · rw [tsum_eq_zero_of_not_summable hf]
    exact tsum_nonneg hg0

/-- Pointwise bound behind (6.2) [boundspsiu2PMtotal]: with `x = (ρ l)² ≤ 1/4`,
`Q ≤ x / (1 − x)` gives `t (Q − (ρ₀ l)²) ≤ D g₁² t⁻¹ + 2 ρ⁴ g₁⁴ (t³)⁻¹`, where `t = |u|²`,
`|l| ≤ g₁ / t` and `ρ² − ρ₀² ≤ D`. -/
private lemma LowMid_PI_pt {g₁ ρ ρ₀ D t Q l : ℝ} (hD0 : 0 ≤ D) (ht : 0 < t)
    (hl : |l| ≤ g₁ / t) (hx : |ρ * l| ≤ 1 / 2)
    (hQ : Q ≤ (ρ * l) ^ 2 / (1 - (ρ * l) ^ 2)) (hD : ρ ^ 2 - ρ₀ ^ 2 ≤ D) :
    t * (Q - (ρ₀ * l) ^ 2) ≤ D * g₁ ^ 2 * t⁻¹ + 2 * ρ ^ 4 * g₁ ^ 4 * (t ^ 3)⁻¹ := by
  set x := (ρ * l) ^ 2 with hxdef
  have hx0 : 0 ≤ x := sq_nonneg _
  have hx1 : x ≤ 1 / 4 := by
    have : x = |ρ * l| ^ 2 := (sq_abs _).symm
    rw [this]
    nlinarith [abs_nonneg (ρ * l)]
  have hsplit : x / (1 - x) = x + x ^ 2 / (1 - x) := by
    have : 1 - x ≠ 0 := by linarith
    field_simp
    ring
  have hx2 : x ^ 2 / (1 - x) ≤ 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg x]
  have hl2 : l ^ 2 ≤ g₁ ^ 2 / t ^ 2 := by
    rw [← sq_abs, ← div_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hl 2
  have hxl : x = ρ ^ 2 * l ^ 2 := by rw [hxdef]; ring
  have hkey : Q - (ρ₀ * l) ^ 2 ≤ (ρ ^ 2 - ρ₀ ^ 2) * l ^ 2 + 2 * x ^ 2 := by
    have h1 : Q - (ρ₀ * l) ^ 2 ≤ x / (1 - x) - (ρ₀ * l) ^ 2 := by linarith
    rw [hsplit] at h1
    have e : x + x ^ 2 / (1 - x) - (ρ₀ * l) ^ 2 = (ρ ^ 2 - ρ₀ ^ 2) * l ^ 2 + x ^ 2 / (1 - x) := by
      rw [hxl]; ring
    linarith
  have e1 : t * (D * l ^ 2) ≤ D * g₁ ^ 2 * t⁻¹ := by
    calc t * (D * l ^ 2) ≤ t * (D * (g₁ ^ 2 / t ^ 2)) := by gcongr
      _ = D * g₁ ^ 2 * t⁻¹ := by field_simp
  have e2 : t * (2 * x ^ 2) ≤ 2 * ρ ^ 4 * g₁ ^ 4 * (t ^ 3)⁻¹ := by
    have hl4 : (l ^ 2) ^ 2 ≤ (g₁ ^ 2 / t ^ 2) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hl2 2
    calc t * (2 * x ^ 2) = 2 * ρ ^ 4 * t * (l ^ 2) ^ 2 := by rw [hxl]; ring
      _ ≤ 2 * ρ ^ 4 * t * (g₁ ^ 2 / t ^ 2) ^ 2 := by gcongr
      _ = 2 * ρ ^ 4 * g₁ ^ 4 * (t ^ 3)⁻¹ := by field_simp
  have h3 : (ρ ^ 2 - ρ₀ ^ 2) * l ^ 2 ≤ D * l ^ 2 := mul_le_mul_of_nonneg_right hD (sq_nonneg _)
  calc t * (Q - (ρ₀ * l) ^ 2) ≤ t * ((ρ ^ 2 - ρ₀ ^ 2) * l ^ 2 + 2 * x ^ 2) :=
        mul_le_mul_of_nonneg_left hkey ht.le
    _ ≤ t * (D * l ^ 2 + 2 * x ^ 2) := by gcongr
    _ = t * (D * l ^ 2) + t * (2 * x ^ 2) := by ring
    _ ≤ _ := add_le_add e1 e2

/-- The Riemann-sum rate `δ (1 + log δ⁻¹)` is at most `3 δ^{1/2}` for `0 < δ ≤ 1`. -/
private lemma LowMid_rate_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    riemannRate 2 δ ≤ 3 * δ ^ (1/2 : ℝ) := by
  have hr : riemannRate 2 δ = δ * (1 + Real.log δ⁻¹) := by simp [riemannRate]
  set s := δ ^ (1/2 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hδ _
  have hsδ : δ = s ^ 2 := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
    norm_num
  have hs1 : s ≤ 1 := Real.rpow_le_one hδ.le hδ1 (by norm_num)
  have hlog : Real.log δ⁻¹ ≤ 2 * s⁻¹ := by
    have h := Real.log_le_rpow_div (inv_nonneg.2 hδ.le) (by norm_num : (0 : ℝ) < 1/2)
    rw [Real.inv_rpow hδ.le, ← hs] at h
    linarith
  rw [hr]
  calc δ * (1 + Real.log δ⁻¹) ≤ δ * (1 + 2 * s⁻¹) := by gcongr
    _ = s ^ 2 + 2 * s := by rw [hsδ]; field_simp
    _ ≤ 3 * s := by nlinarith

/-- (6.2) [boundspsiu2PMtotal] with a rate uniform in `k_c`. -/
theorem Eq6_2 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rhoN N ^ (-(5/2 : ℝ)) * (LN N ^ 3)⁻¹ *
          (∑' n : Idx, (if inPI (rhoN N) (LN N) n then ‖mom (LN N) n‖ ^ 2 *
            (Expect.Q (trialState V w kc N) [n]
              - (rho0 (g0 V w) (rhoN N) * lam V w (rhoN N) (LN N) n) ^ 2) else 0))
        ≤ C * rhoN N ^ (1/200 : ℝ) := by
  obtain ⟨N₁, hN₁⟩ := Lemma5_4_PI V w
  set g₁ : ℝ := ∫ x, |gfun V w x| with hg₁def
  have hg₁ : 0 ≤ g₁ := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨K₁, hK₁, h1⟩ := sum_norm_rpow_le (s := 2) (by norm_num)
  obtain ⟨K₂, hK₂, h2⟩ := sum_norm_rpow_gt (s := 6) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1
    (LowMid_eventually (δ := 1 / (2 * (g₁ + 1))) (by positivity))
  set κ : ℝ := (3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ) with hκdef
  have hκ : 0 ≤ κ := by positivity
  refine ⟨2 * κ * g₁ ^ 2 * K₁ + 2 * g₁ ^ 4 * K₂, by positivity, max N₁ N₂, fun N hN kc => ?_⟩
  have hNa : N ≥ N₁ := le_trans (le_max_left _ _) hN
  have hNb : N ≥ N₂ := le_trans (le_max_right _ _) hN
  obtain ⟨hN1, hε, hL⟩ := hN₂ N hNb
  obtain ⟨-, hρ, hρ1, hLpos⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set ε := epsP ρ with hεdef
  set q := ρ ^ (1 / 2 : ℝ) with hqdef
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hρ _
  have hε1 : ε ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hq0 : 0 < q := Real.rpow_pos_of_pos hρ _
  have hρq : ρ = q ^ 2 := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  set R : ℝ := ε⁻¹ * q with hRdef
  have hR0 : 0 < R := by positivity
  have hqR : q ≤ R := by
    have : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).2 hε1
    nlinarith
  have hLR : 2 * π ≤ L * R := hL.trans (mul_le_mul_of_nonneg_left hqR hLpos.le)
  have hLε : 2 * π ≤ L * ε := by
    have : q ≤ ε := by
      rw [hqdef, hεdef, epsP]
      exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
    exact hL.trans (mul_le_mul_of_nonneg_left this hLpos.le)
  have hρ₀ : rho0 (g0 V w) ρ = ρ - κ * ρ ^ (3/2 : ℝ) := rfl
  have h52 : ρ ^ (5/2 : ℝ) = ρ ^ (3/2 : ℝ) * ρ := by
    rw [← Real.rpow_add_one hρ.ne']
    norm_num
  have hρ32 : 0 < ρ ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hρ52 : 0 < ρ ^ (5/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  set D : ℝ := 2 * κ * ρ ^ (5/2 : ℝ) with hD
  have hD0 : 0 ≤ D := by positivity
  have hDρ : ρ ^ 2 - rho0 (g0 V w) ρ ^ 2 ≤ D := by
    rw [hρ₀, hD, h52]
    nlinarith [sq_nonneg (κ * ρ ^ (3/2 : ℝ))]
  -- the two majorants
  set A : Idx → ℝ := fun n => if n ≠ 0 ∧ ‖mom L n‖ ≤ ε then ‖mom L n‖ ^ (-(2 : ℝ)) else 0
    with hAdef
  set B : Idx → ℝ := fun n => if R < ‖mom L n‖ then ‖mom L n‖ ^ (-(6 : ℝ)) else 0 with hBdef
  have hA0 : ∀ n, 0 ≤ A n := fun n => by
    simp only [hAdef]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hB0 : ∀ n, 0 ≤ B n := fun n => by
    simp only [hBdef]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hAs : Summable A := by
    refine LowMid_summable_ball hLpos A (R := ε) fun n hn => ?_
    by_contra h
    exact hn (by simp [hAdef, h])
  have hBs : Summable B := (h2 L R hR0 hLR).1
  -- termwise bound
  have hpt : ∀ n : Idx, (if inPI ρ L n then ‖mom L n‖ ^ 2 *
      (Expect.Q (trialState V w kc N) [n] - (rho0 (g0 V w) ρ * lam V w ρ L n) ^ 2) else 0) ≤
      D * g₁ ^ 2 * A n + 2 * ρ ^ 4 * g₁ ^ 4 * B n := by
    intro n
    by_cases hu : inPI ρ L n
    · simp only [hu, ↓reduceIte]
      have hlu := Particles_lam_abs_le V w ρ L n (fun h => Regions_PL_PI h hu)
      have hQ := hN₁ N hNa kc n hu
      have hu1 : R < ‖mom L n‖ := hu.1
      have hu2 : ‖mom L n‖ ≤ ε := hu.2
      have hnu0 : 0 < ‖mom L n‖ := lt_trans hR0 hu1
      have hn0 : n ≠ 0 := by
        rintro rfl
        have : mom L 0 = 0 := by ext i; simp [mom]
        rw [this, norm_zero] at hnu0
        exact lt_irrefl _ hnu0
      have hρu : ρ ≤ ε ^ 2 * ‖mom L n‖ ^ 2 := by
        have h1 : q < ε * ‖mom L n‖ := by
          have h2 := mul_lt_mul_of_pos_left hu1 hε0
          rwa [hRdef, ← mul_assoc, mul_inv_cancel₀ hε0.ne', one_mul] at h2
        have h3 : q ^ 2 ≤ (ε * ‖mom L n‖) ^ 2 := pow_le_pow_left₀ hq0.le h1.le 2
        rw [hρq]
        calc q ^ 2 ≤ (ε * ‖mom L n‖) ^ 2 := h3
          _ = ε ^ 2 * ‖mom L n‖ ^ 2 := by ring
      have hrl : |ρ * lam V w ρ L n| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos hρ]
        have h1 : ρ * |lam V w ρ L n| ≤ ρ * (g₁ / ‖mom L n‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hlu hρ.le
        have h2 : ρ * (g₁ / ‖mom L n‖ ^ 2) ≤ ε ^ 2 * g₁ := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          calc ρ * g₁ ≤ ε ^ 2 * ‖mom L n‖ ^ 2 * g₁ := mul_le_mul_of_nonneg_right hρu hg₁
            _ = ε ^ 2 * g₁ * ‖mom L n‖ ^ 2 := by ring
        have h3 : ε ^ 2 * g₁ ≤ ε * g₁ :=
          mul_le_mul_of_nonneg_right (pow_le_of_le_one hε0.le hε1 (by norm_num)) hg₁
        have h4 : ε * g₁ ≤ 1 / 2 := by
          have h5 : ε ≤ 1 / (2 * (g₁ + 1)) := hε
          rw [le_div_iff₀ (by positivity)] at h5
          have h6 : ε * g₁ ≤ ε * (g₁ + 1) := mul_le_mul_of_nonneg_left (by linarith) hε0.le
          linarith
        linarith
      have key := LowMid_PI_pt (g₁ := g₁) (ρ := ρ) (ρ₀ := rho0 (g0 V w) ρ) (D := D)
        (t := ‖mom L n‖ ^ 2) (Q := Expect.Q (trialState V w kc N) [n])
        (l := lam V w ρ L n) hD0 (by positivity) hlu hrl hQ hDρ
      have eA : A n = (‖mom L n‖ ^ 2)⁻¹ := by
        simp only [hAdef, ne_eq, hn0, not_false_eq_true, hu2, and_self, ↓reduceIte]
        rw [Real.rpow_neg (norm_nonneg _)]
        norm_cast
      have eB : B n = ((‖mom L n‖ ^ 2) ^ 3)⁻¹ := by
        simp only [hBdef, hu1, ↓reduceIte]
        rw [Real.rpow_neg (norm_nonneg _), ← pow_mul]
        norm_cast
      rw [eA, eB]
      exact key
    · simp only [hu, ↓reduceIte]
      have := hA0 n
      have := hB0 n
      positivity
  -- summation
  have hgs : Summable (fun n : Idx => D * g₁ ^ 2 * A n + 2 * ρ ^ 4 * g₁ ^ 4 * B n) :=
    (hAs.mul_left _).add (hBs.mul_left _)
  have hsum := LowMid_tsum_le hgs
    (fun n => by have := hA0 n; have := hB0 n; positivity) hpt
  rw [(hAs.mul_left _).tsum_add (hBs.mul_left _), tsum_mul_left, tsum_mul_left] at hsum
  -- the two lattice sums
  have hSA := h1 L ε hε0 hLε
  have hSB := (h2 L R hR0 hLR).2
  have hρm : ρ ^ (-(5/2 : ℝ)) * ρ ^ (5/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hρ]
    norm_num
  have hR3 : R ^ ((3 : ℝ) - 6) = ρ ^ (3/200 - 3/2 : ℝ) := by
    have hRe : R = ρ ^ (-(1/200 : ℝ) + 1/2) := by
      rw [hRdef, hεdef, epsP, hqdef, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
    rw [hRe, ← Real.rpow_mul hρ.le]
    norm_num
  have hρ4 : ρ ^ (-(5/2 : ℝ)) * ρ ^ 4 * ρ ^ (3/200 - 3/2 : ℝ) = ρ ^ (3/200 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  have hε3 : ρ ^ (3/200 : ℝ) ≤ ρ ^ (1/200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hεe : ε = ρ ^ (1/200 : ℝ) := rfl
  have hT1 : ρ ^ (-(5/2 : ℝ)) * (D * g₁ ^ 2 * (K₁ * ε ^ ((3 : ℝ) - 2))) =
      2 * κ * g₁ ^ 2 * K₁ * ρ ^ (1/200 : ℝ) := by
    rw [hD, show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one, ← hεe]
    calc _ = 2 * κ * g₁ ^ 2 * K₁ * (ρ ^ (-(5/2 : ℝ)) * ρ ^ (5/2 : ℝ)) * ε := by ring
      _ = _ := by rw [hρm]; ring
  have hT2 : ρ ^ (-(5/2 : ℝ)) * (2 * ρ ^ 4 * g₁ ^ 4 * (K₂ * R ^ ((3 : ℝ) - 6))) =
      2 * g₁ ^ 4 * K₂ * ρ ^ (3/200 : ℝ) := by
    rw [hR3, ← hρ4]
    ring
  have hρm0 : 0 ≤ ρ ^ (-(5/2 : ℝ)) := Real.rpow_nonneg hρ.le _
  have hL3 : 0 ≤ (L ^ 3)⁻¹ := by positivity
  calc ρ ^ (-(5/2 : ℝ)) * (L ^ 3)⁻¹ * ∑' n : Idx, (if inPI ρ L n then ‖mom L n‖ ^ 2 *
          (Expect.Q (trialState V w kc N) [n] - (rho0 (g0 V w) ρ * lam V w ρ L n) ^ 2) else 0)
      ≤ ρ ^ (-(5/2 : ℝ)) * (L ^ 3)⁻¹ *
          (D * g₁ ^ 2 * (∑' n, A n) + 2 * ρ ^ 4 * g₁ ^ 4 * (∑' n, B n)) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hρm0 hL3)
    _ = ρ ^ (-(5/2 : ℝ)) * (D * g₁ ^ 2 * ((L ^ 3)⁻¹ * ∑' n, A n) +
          2 * ρ ^ 4 * g₁ ^ 4 * ((L ^ 3)⁻¹ * ∑' n, B n)) := by ring
    _ ≤ ρ ^ (-(5/2 : ℝ)) * (D * g₁ ^ 2 * (K₁ * ε ^ ((3 : ℝ) - 2)) +
          2 * ρ ^ 4 * g₁ ^ 4 * (K₂ * R ^ ((3 : ℝ) - 6))) := by
        refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hρm0
        · exact mul_le_mul_of_nonneg_left hSA (by positivity)
        · exact mul_le_mul_of_nonneg_left hSB (by positivity)
    _ = 2 * κ * g₁ ^ 2 * K₁ * ρ ^ (1/200 : ℝ) + 2 * g₁ ^ 4 * K₂ * ρ ^ (3/200 : ℝ) := by
        rw [mul_add, hT1, hT2]
    _ ≤ 2 * κ * g₁ ^ 2 * K₁ * ρ ^ (1/200 : ℝ) + 2 * g₁ ^ 4 * K₂ * ρ ^ (1/200 : ℝ) := by
        gcongr
    _ = (2 * κ * g₁ ^ 2 * K₁ + 2 * g₁ ^ 4 * K₂) * ρ ^ (1/200 : ℝ) := by ring

/-- (6.7): on `P_L`, `Q_Ψ(u) ≤ (ρλ_u)²/(1 − (ρλ_u)²) + C ρ m_c/(ε_H ε_L)`. -/
theorem Eq6_7 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      Expect.Q (trialState V w kc N) [u] ≤
        (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
            (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2)
          + C * rhoN N * mc (rhoN N) / epsP (rhoN N) ^ 2 := by
  obtain ⟨C, hC, N₀, h⟩ := Lemma5_4_PL hg
  have hs : 0 ≤ Real.sqrt (g0 V w) := Real.sqrt_nonneg _
  refine ⟨C * (1 + Real.sqrt (g0 V w)), by positivity, max N₀ 1, fun N hN kc u hu => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : N ≥ N₀ := le_trans (le_max_left _ _) hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have h1 := h N hN0 kc u hu
  obtain ⟨hneg, hlow⟩ := Particles_rho_lam_PL hg hρ hρ1 hu
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hmc : 0 < mc (rhoN N) := Real.rpow_pos_of_pos hρ _
  set y := rhoN N * lam V w (rhoN N) (LN N) u with hy
  set ε := epsP (rhoN N) with hεdef
  set c := ε / (1 + Real.sqrt (g0 V w)) with hc
  have hc0 : 0 < c := by positivity
  have hxy : 1 - y ^ 2 = (1 - y) * (1 + y) := by ring
  have hx1 : c ≤ 1 - y ^ 2 := by
    rw [hxy]
    nlinarith
  have hx0 : 0 < 1 - y ^ 2 := lt_of_lt_of_le hc0 hx1
  have hdiv : y ^ 2 / (1 - y ^ 2) ≤ (1 + Real.sqrt (g0 V w)) / ε := by
    calc y ^ 2 / (1 - y ^ 2) ≤ 1 / (1 - y ^ 2) :=
          div_le_div_of_nonneg_right (by nlinarith) hx0.le
      _ ≤ 1 / c := one_div_le_one_div_of_le hc0 hx1
      _ = (1 + Real.sqrt (g0 V w)) / ε := by rw [hc]; field_simp
  have hE : 0 ≤ C * rhoN N * mc (rhoN N) / ε := by positivity
  have h2 : y ^ 2 / (1 - y ^ 2) * (1 + C * rhoN N * mc (rhoN N) / ε) =
      y ^ 2 / (1 - y ^ 2) + y ^ 2 / (1 - y ^ 2) * (C * rhoN N * mc (rhoN N) / ε) := by ring
  have h3 : y ^ 2 / (1 - y ^ 2) * (C * rhoN N * mc (rhoN N) / ε) ≤
      (1 + Real.sqrt (g0 V w)) / ε * (C * rhoN N * mc (rhoN N) / ε) :=
    mul_le_mul_of_nonneg_right hdiv hE
  have h4 : (1 + Real.sqrt (g0 V w)) / ε * (C * rhoN N * mc (rhoN N) / ε) =
      C * (1 + Real.sqrt (g0 V w)) * rhoN N * mc (rhoN N) / ε ^ 2 := by
    field_simp
  linarith

/-- (6.3) [boundspsiu2PLtotal] with a rate uniform in `k_c`, under `|g_p| ≤ g₀` and
`|g_p − g₀| ≤ C₀|p|` for `g_p = Re ĝ(p)`. -/
theorem Eq6_3 {V w : R3 → ℝ} {C₀ : ℝ} (hg : 0 < g0 V w)
    (hgb : ∀ p, |(ft (gfun V w) p).re| ≤ g0 V w)
    (hgl : ∀ p, |(ft (gfun V w) p).re - g0 V w| ≤ C₀ * ‖p‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rhoN N ^ (-(5/2 : ℝ)) * (LN N ^ 3)⁻¹ *
          (∑' n : Idx, (if inPL (rhoN N) (LN N) n then ‖mom (LN N) n‖ ^ 2 *
            (Expect.Q (trialState V w kc N) [n]
              - (rho0 (g0 V w) (rhoN N) * wmom V w (mom (LN N) n)) ^ 2) else 0))
        ≤ -(8 * g0 V w ^ (5/2 : ℝ) / (5 * π ^ 2)) + C * rhoN N ^ (1/200 : ℝ) := by
  obtain ⟨C₇, hC₇, N₇, h7⟩ := Eq6_7 hg
  obtain ⟨K₁, hK₁, h1⟩ := sum_PL_kin hg
  obtain ⟨K₂, hK₂, h2⟩ := sum_PL_kin_replace (C := C₀) hg
  obtain ⟨K₃, hK₃, h3⟩ := sum_norm_rpow_le (s := -2) (by norm_num)
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 (LowMid_eventually (δ := 1) one_pos)
  refine ⟨K₁ * (1 + 3 * (2 * π) ^ (1/2 : ℝ)) + K₂ + C₇ * K₃, by positivity,
    max N₇ N₂, fun N hN kc => ?_⟩
  have hNa : N ≥ N₇ := le_trans (le_max_left _ _) hN
  have hNb : N ≥ N₂ := le_trans (le_max_right _ _) hN
  obtain ⟨hN1, hε, hL⟩ := hN₂ N hNb
  obtain ⟨-, hρ, hρ1, hLpos⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set ε := epsP ρ with hεdef
  set q := ρ ^ (1 / 2 : ℝ) with hqdef
  set g := g0 V w with hgdef
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hρ _
  have hε1 : ε ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hq0 : 0 < q := Real.rpow_pos_of_pos hρ _
  set R : ℝ := ε⁻¹ * q with hRdef
  have hR0 : 0 < R := by positivity
  have hqR : q ≤ R := by
    have : 1 ≤ ε⁻¹ := (one_le_inv₀ hε0).2 hε1
    nlinarith
  have hLR : 2 * π ≤ L * R := hL.trans (mul_le_mul_of_nonneg_left hqR hLpos.le)
  have hεe : ε = ρ ^ (1/200 : ℝ) := rfl
  -- the three exponent identities
  have hLq : L * q = ρ ^ (-(13/24 : ℝ)) := by
    change ρ ^ (-(25/24 : ℝ)) * ρ ^ (1/2 : ℝ) = _
    rw [← Real.rpow_add hρ]
    norm_num
  have hΔ : 2 * π / (L * q) = 2 * π * ρ ^ (13/24 : ℝ) := by
    rw [hLq, Real.rpow_neg hρ.le, div_inv_eq_mul]
  have hΔ0 : 0 < 2 * π / (L * q) := by positivity
  have hΔ1 : 2 * π / (L * q) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hL
  have hrate : riemannRate 2 (2 * π / (L * q)) ≤ 3 * (2 * π) ^ (1/2 : ℝ) * ρ ^ (1/200 : ℝ) := by
    refine (LowMid_rate_le hΔ0 hΔ1).trans ?_
    rw [hΔ, Real.mul_rpow (by positivity) (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
    have : ρ ^ (13/24 * (1/2) : ℝ) ≤ ρ ^ (1/200 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
    have h0 : 0 ≤ (2 * π) ^ (1/2 : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h0]
  -- the three families
  set F1 : Idx → ℝ := fun n => if inPL ρ L n then ‖mom L n‖ ^ 2 *
      ((ρ * lamPL g ρ (mom L n)) ^ 2 / (1 - (ρ * lamPL g ρ (mom L n)) ^ 2)
        - (ρ * g / ‖mom L n‖ ^ 2) ^ 2) else 0 with hF1
  set F2 : Idx → ℝ := fun n => if inPL ρ L n then ‖mom L n‖ ^ 2 *
      ((ρ * g / ‖mom L n‖ ^ 2) ^ 2 - (rho0 g ρ *
        ((fun p => (ft (gfun V w) p).re) (mom L n) / ‖mom L n‖ ^ 2)) ^ 2) else 0 with hF2
  set A : Idx → ℝ := fun n => if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-(-2 : ℝ)) else 0
    with hAdef
  set f : Idx → ℝ := fun n => if inPL ρ L n then ‖mom L n‖ ^ 2 *
      (Expect.Q (trialState V w kc N) [n] - (rho0 g ρ * wmom V w (mom L n)) ^ 2) else 0
    with hfdef
  set E : ℝ := C₇ * ρ * mc ρ / ε ^ 2 with hEdef
  have hE0 : 0 ≤ E := by
    have : 0 < mc ρ := Real.rpow_pos_of_pos hρ _
    positivity
  have hsupp : ∀ (F : Idx → ℝ), (∀ n, F n ≠ 0 → inPL ρ L n) → Summable F := by
    intro F hF
    exact LowMid_summable_ball hLpos F (R := R) fun n hn => (hF n hn).2
  have hF1s : Summable F1 := hsupp F1 fun n hn => by
    by_contra h
    exact hn (by simp [hF1, h])
  have hF2s : Summable F2 := hsupp F2 fun n hn => by
    by_contra h
    exact hn (by simp [hF2, h])
  have hfs : Summable f := hsupp f fun n hn => by
    by_contra h
    exact hn (by simp [hfdef, h])
  have hAs : Summable A := by
    refine LowMid_summable_ball hLpos A (R := R) fun n hn => ?_
    by_contra h
    exact hn (by simp [hAdef, h])
  -- termwise bound
  have hpt : ∀ n : Idx, f n ≤ F1 n + F2 n + E * A n := by
    intro n
    by_cases hn : inPL ρ L n
    · have hn0 : n ≠ 0 := by
        rintro rfl
        have h0 : mom L 0 = 0 := by ext i; simp [mom]
        have := hn.1
        rw [h0, norm_zero] at this
        have := mul_pos hε0 hq0
        linarith
      have hnR : ‖mom L n‖ ≤ R := hn.2
      have hQ := h7 N hNa kc n hn
      rw [lam_of_inPL hn] at hQ
      have eA : A n = ‖mom L n‖ ^ 2 := by
        simp only [hAdef, ne_eq, hn0, not_false_eq_true, hnR, and_self, ↓reduceIte]
        rw [neg_neg, Real.rpow_two]
      simp only [hfdef, hF1, hF2, hn, ↓reduceIte, eA]
      have hm0 : 0 ≤ ‖mom L n‖ ^ 2 := sq_nonneg _
      have hw : wmom V w (mom L n) = (ft (gfun V w) (mom L n)).re / ‖mom L n‖ ^ 2 := rfl
      rw [hw]
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right hQ ((rho0 g ρ *
        ((ft (gfun V w) (mom L n)).re / ‖mom L n‖ ^ 2)) ^ 2)) hm0
      refine this.trans (le_of_eq ?_)
      ring
    · simp only [hfdef, hF1, hF2, hn, ↓reduceIte]
      have : 0 ≤ E * A n := by
        have : 0 ≤ A n := by
          simp only [hAdef]
          split_ifs
          · exact Real.rpow_nonneg (norm_nonneg _) _
          · exact le_rfl
        positivity
      linarith
  have hsum : ∑' n, f n ≤ (∑' n, F1 n) + (∑' n, F2 n) + E * (∑' n, A n) := by
    have := hfs.tsum_le_tsum hpt ((hF1s.add hF2s).add (hAs.mul_left E))
    rwa [((hF1s.add hF2s).tsum_add (hAs.mul_left E)), hF1s.tsum_add hF2s, tsum_mul_left] at this
  -- the three sums
  have h1' : |(L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) * (∑' n, F1 n) + 8 * g ^ (5/2 : ℝ) / (5 * π ^ 2)| ≤
      K₁ * (ρ ^ (1/200 : ℝ) + riemannRate 2 (2 * π / (L * q))) := h1 ρ L hρ hρ1 hL
  have h2' : |(L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) * (∑' n, F2 n)| ≤ K₂ * ρ ^ (1/2 - 2/200 : ℝ) :=
    h2 (fun p => (ft (gfun V w) p).re) ρ L hgb hgl hρ hρ1 hL
  have h3' : (L ^ 3)⁻¹ * (∑' n, A n) ≤ K₃ * R ^ ((3 : ℝ) - -2) := h3 L R hR0 hLR
  have hX1 := (abs_le.1 h1').2
  have hX2 := (abs_le.1 h2').2
  have hRe : R = ρ ^ (-(1/200 : ℝ) + 1/2) := by
    rw [hRdef, hεe, ← Real.rpow_neg hρ.le, hqdef, ← Real.rpow_add hρ]
  have hR5 : R ^ ((3 : ℝ) - -2) = ρ ^ (5/2 - 5/200 : ℝ) := by
    rw [hRe, ← Real.rpow_mul hρ.le]
    norm_num
  have hρE : ρ * mc ρ / ε ^ 2 = ρ ^ (1 - 3/200 : ℝ) := by
    have e1 : ε ^ 2 = ρ ^ (2/200 : ℝ) := by
      rw [hεe, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      norm_num
    have e2 : mc ρ = ρ ^ (-(1/200 : ℝ)) := rfl
    have e3 : ρ ^ (1 - 3/200 : ℝ) = ρ ^ ((1 : ℝ) + -(1/200) - 2/200) := by norm_num
    rw [e1, e2, e3, Real.rpow_sub hρ, Real.rpow_add hρ, Real.rpow_one]
  have hT3 : E * (ρ ^ (-(5/2 : ℝ)) * (K₃ * R ^ ((3 : ℝ) - -2))) =
      C₇ * K₃ * ρ ^ (1 - 8/200 : ℝ) := by
    have : E = C₇ * ρ ^ (1 - 3/200 : ℝ) := by
      rw [hEdef, mul_assoc, mul_div_assoc, hρE]
    rw [this, hR5]
    have e : ρ ^ (1 - 3/200 : ℝ) * ρ ^ (-(5/2 : ℝ)) * ρ ^ (5/2 - 5/200 : ℝ) =
        ρ ^ (1 - 8/200 : ℝ) := by
      rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
      norm_num
    calc C₇ * ρ ^ (1 - 3/200 : ℝ) * (ρ ^ (-(5/2 : ℝ)) * (K₃ * ρ ^ (5/2 - 5/200 : ℝ)))
        = C₇ * K₃ * (ρ ^ (1 - 3/200 : ℝ) * ρ ^ (-(5/2 : ℝ)) * ρ ^ (5/2 - 5/200 : ℝ)) := by ring
      _ = _ := by rw [e]
  have hρm0 : 0 ≤ ρ ^ (-(5/2 : ℝ)) := Real.rpow_nonneg hρ.le _
  have hL3 : 0 ≤ (L ^ 3)⁻¹ := by positivity
  have hY : ρ ^ (-(5/2 : ℝ)) * (L ^ 3)⁻¹ * ∑' n, f n ≤
      (L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) * (∑' n, F1 n) +
        (L ^ 3)⁻¹ * ρ ^ (-(5/2 : ℝ)) * (∑' n, F2 n) +
        E * (ρ ^ (-(5/2 : ℝ)) * ((L ^ 3)⁻¹ * ∑' n, A n)) := by
    calc ρ ^ (-(5/2 : ℝ)) * (L ^ 3)⁻¹ * ∑' n, f n
        ≤ ρ ^ (-(5/2 : ℝ)) * (L ^ 3)⁻¹ * ((∑' n, F1 n) + (∑' n, F2 n) + E * (∑' n, A n)) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hρm0 hL3)
      _ = _ := by ring
  have hX3 : E * (ρ ^ (-(5/2 : ℝ)) * ((L ^ 3)⁻¹ * ∑' n, A n)) ≤
      E * (ρ ^ (-(5/2 : ℝ)) * (K₃ * R ^ ((3 : ℝ) - -2))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3' hρm0) hE0
  have hρ2 : ρ ^ (1/2 - 2/200 : ℝ) ≤ ρ ^ (1/200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hρ3 : ρ ^ (1 - 8/200 : ℝ) ≤ ρ ^ (1/200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hK1 : K₁ * (ρ ^ (1/200 : ℝ) + riemannRate 2 (2 * π / (L * q))) ≤
      K₁ * (ρ ^ (1/200 : ℝ) + 3 * (2 * π) ^ (1/2 : ℝ) * ρ ^ (1/200 : ℝ)) := by
    gcongr
  have hK2 : K₂ * ρ ^ (1/2 - 2/200 : ℝ) ≤ K₂ * ρ ^ (1/200 : ℝ) := by gcongr
  have hK3 : C₇ * K₃ * ρ ^ (1 - 8/200 : ℝ) ≤ C₇ * K₃ * ρ ^ (1/200 : ℝ) := by gcongr
  change ρ ^ (-(5/2 : ℝ)) * (L ^ 3)⁻¹ * ∑' n, f n ≤ _
  linarith [hY, hX1, hX2, hX3, hT3, hK1, hK2, hK3]

/-- `|g_p| ≤ g₀` for `g_p = Re ĝ(p)`. -/
private theorem P_hgb {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ p, |(ft (gfun V w) p).re| ≤ g0 V w :=
  fun p => (Complex.abs_re_le_norm _).trans (scat_ft_g_norm_le hV hw p)

/-- `|g_p − g₀| ≤ C₀|p|` for `g_p = Re ĝ(p)`. -/
private theorem P_hgl {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C₀ : ℝ, ∀ p, |(ft (gfun V w) p).re - g0 V w| ≤ C₀ * ‖p‖ := by
  obtain ⟨C, hC⟩ := scat_ft_g_lipschitz hV hw
  refine ⟨C, fun p => ?_⟩
  have h := hC p 0
  rw [scat_ft_g_zero, sub_zero] at h
  calc |(ft (gfun V w) p).re - g0 V w| = |(ft (gfun V w) p - (g0 V w : ℂ)).re| := by simp
    _ ≤ ‖ft (gfun V w) p - (g0 V w : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ C * ‖p‖ := h

/-- (6.2) [boundspsiu2PMtotal] with a rate uniform in `k_c`, under the hypotheses of the paper. -/
theorem Eq6_2_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rhoN N ^ (-(5/2 : ℝ)) * (LN N ^ 3)⁻¹ *
          (∑' n : Idx, (if inPI (rhoN N) (LN N) n then ‖mom (LN N) n‖ ^ 2 *
            (Expect.Q (trialState V w kc N) [n]
              - (rho0 (g0 V w) (rhoN N) * lam V w (rhoN N) (LN N) n) ^ 2) else 0))
        ≤ C * rhoN N ^ (1/200 : ℝ) :=
  Eq6_2 (scat_g0_pos hV hw)

/-- (6.3) [boundspsiu2PLtotal] with a rate uniform in `k_c`, under the hypotheses of the paper. -/
theorem Eq6_3_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rhoN N ^ (-(5/2 : ℝ)) * (LN N ^ 3)⁻¹ *
          (∑' n : Idx, (if inPL (rhoN N) (LN N) n then ‖mom (LN N) n‖ ^ 2 *
            (Expect.Q (trialState V w kc N) [n]
              - (rho0 (g0 V w) (rhoN N) * wmom V w (mom (LN N) n)) ^ 2) else 0))
        ≤ -(8 * g0 V w ^ (5/2 : ℝ) / (5 * π ^ 2)) + C * rhoN N ^ (1/200 : ℝ) :=
  Eq6_3 (scat_g0_pos hV hw) (P_hgb hV hw) (P_hgl hV hw).choose_spec

end LHYUpper
