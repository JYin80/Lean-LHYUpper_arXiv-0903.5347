import LHYUpper.Assembly.Section4
import LHYUpper.Fock.Expect
import LHYUpper.Riemann.ScaledLimits
import LHYUpper.Scattering.WMomentum
import LHYUpper.Pair.Sums
import LHYUpper.Pair.S3Bound
import LHYUpper.Particles.Lemma55

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # §7, proof of Lemma 4.4 [lemHS3]: the main terms (7.65)–(7.68) of `H_{S3}`

Sums over `u ≠ ±v` with `ρ = ρ_N`, `|Λ| = L_N³`; rates uniform in `k_c`. -/

/-! ### Scaling facts at `ρ = ρ_N`, `L = L_N` -/

/-- `ρ_N^b = N^{-8b/17}`. -/
private lemma S3_rho_pow_eq (N : ℕ) (b : ℝ) :
    rhoN N ^ b = (N : ℝ) ^ (-(8/17 : ℝ) * b) := by
  rw [rhoN, ← Real.rpow_mul (Nat.cast_nonneg N)]

/-- `ρ_N^{-a} → ∞` for `a > 0`. -/
private lemma S3_tendsto_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ (-a)) atTop atTop := by
  simp_rw [S3_rho_pow_eq]
  have : (0 : ℝ) < -(8/17) * -a := by nlinarith
  exact (tendsto_rpow_atTop this).comp tendsto_natCast_atTop_atTop

/-- `ρ_N^b → 0` for `b > 0`. -/
private lemma S3_tendsto_pos {b : ℝ} (hb : 0 < b) :
    Tendsto (fun N : ℕ => rhoN N ^ b) atTop (𝓝 0) := by
  simp_rw [S3_rho_pow_eq]
  have : (0 : ℝ) < (8/17) * b := by positivity
  have h := (tendsto_rpow_neg_atTop this).comp tendsto_natCast_atTop_atTop
  refine h.congr (fun N => ?_)
  simp only [Function.comp]
  congr 1
  ring

/-- Eventually `A ρ_N^b ≤ 1` for `b > 0`. -/
private lemma S3_ev_small (A : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, A * rhoN N ^ b ≤ 1 := by
  have h := (S3_tendsto_pos hb).const_mul A
  rw [mul_zero] at h
  exact h.eventually (eventually_le_nhds one_pos)

/-- `x^b ≤ x^a` for `0 < x ≤ 1` and `a ≤ b`. -/
private lemma S3_rpow_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {a b : ℝ} (h : a ≤ b) :
    x ^ b ≤ x ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hx hx1 h

/-- `L_N³ = ρ_N^{-25/8}`. -/
private lemma S3_L3 (N : ℕ) : LN N ^ 3 = rhoN N ^ (-(25/8 : ℝ)) := by
  have hρ : 0 ≤ rhoN N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [LN, ← Real.rpow_natCast, ← Real.rpow_mul hρ]
  norm_num

/-- `L_N ρ_N^{1/2} = ρ_N^{-13/24}`. -/
private lemma S3_L_sqrt {N : ℕ} (hN : 1 ≤ N) :
    LN N * rhoN N ^ (1/2 : ℝ) = rhoN N ^ (-(13/24 : ℝ)) := by
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  rw [LN, ← Real.rpow_add hρ]
  norm_num

/-- Eventually `2π ≤ L_N ρ_N^{1/2}`. -/
private lemma S3_ev_L : ∀ᶠ N : ℕ in atTop, 2 * π ≤ LN N * rhoN N ^ (1/2 : ℝ) := by
  filter_upwards [(S3_tendsto_neg (by norm_num : (0 : ℝ) < 13 / 24)).eventually_ge_atTop (2 * π),
    eventually_ge_atTop 1] with N h hN
  rw [S3_L_sqrt hN]
  exact h

/-- `ρ_N / L_N³ ≤ ρ_N^{5/2 + 1/400}`. -/
private lemma S3_rho_div_L3_le {N : ℕ} (hN : 1 ≤ N) :
    rhoN N / LN N ^ 3 ≤ rhoN N ^ (5/2 + 1/400 : ℝ) := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  have h : rhoN N / LN N ^ 3 = rhoN N ^ (33/8 : ℝ) := by
    rw [S3_L3, Real.rpow_neg hρ.le, div_inv_eq_mul, ← Real.rpow_one_add' hρ.le (by norm_num)]
    norm_num
  rw [h]
  exact S3_rpow_le hρ hρ1 (by norm_num)

/-- `ρ^{1/2} ρ² = ρ^{5/2}`. -/
private lemma S3_pow_52 {ρ : ℝ} (hρ : 0 < ρ) : ρ ^ 2 * ρ ^ (1/2 : ℝ) = ρ ^ (5/2 : ℝ) := by
  rw [← Real.rpow_natCast ρ 2, ← Real.rpow_add hρ]
  norm_num

/-- With `c = g^{3/2}/(3π²)` and `cρ^{1/2} ≤ 1`: `0 ≤ ρ₀ ≤ ρ` and
`0 ≤ ρ² − ρ₀² ≤ 2cρ^{5/2}`. -/
private lemma S3_rho0 {g ρ : ℝ} (hg : 0 ≤ g) (hρ : 0 < ρ)
    (hs : (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) * ρ ^ (1/2 : ℝ) ≤ 1) :
    0 ≤ rho0 g ρ ∧ rho0 g ρ ≤ ρ ∧ 0 ≤ ρ ^ 2 - rho0 g ρ ^ 2 ∧
      ρ ^ 2 - rho0 g ρ ^ 2 ≤ 2 * ((3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ)) * ρ ^ (5/2 : ℝ) := by
  have e1 : ρ ^ (3/2 : ℝ) = ρ * ρ ^ (1/2 : ℝ) := by
    rw [show (3/2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have e2 : ρ ^ (5/2 : ℝ) = ρ ^ 2 * ρ ^ (1/2 : ℝ) := by
    rw [show (5/2 : ℝ) = 2 + 1/2 by norm_num, Real.rpow_add hρ, Real.rpow_two]
  have hc : 0 ≤ (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) * ρ ^ (1/2 : ℝ) := by positivity
  set t := (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) * ρ ^ (1/2 : ℝ) with ht
  have hr : rho0 g ρ = ρ * (1 - t) := by
    rw [rho0, e1, ht]
    ring
  rw [hr, e2]
  have hsq : ρ ^ 2 - (ρ * (1 - t)) ^ 2 = ρ ^ 2 * (t * (2 - t)) := by ring
  refine ⟨by nlinarith, by nlinarith,
    by rw [hsq]; exact mul_nonneg (by positivity) (mul_nonneg hc (by linarith)), ?_⟩
  have : ρ ^ 2 - (ρ * (1 - t)) ^ 2 = ρ ^ 2 * (2 * t - t ^ 2) := by ring
  rw [this]
  have h2 : 2 * ((3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ)) * (ρ ^ 2 * ρ ^ (1/2 : ℝ)) = ρ ^ 2 * (2 * t) := by
    rw [ht]
    ring
  rw [h2]
  have : 0 ≤ ρ ^ 2 := by positivity
  nlinarith

/-- If for every `k_c` and every `N ≥ N₀`, `F(k_c, N) ≤ R + D ρ_N^a` with `a > 0`, then
`lim sup_{k_c} lim sup_N F ≤ R` in `EReal`. -/
private lemma S3_limsup2_le (F : ℝ → ℕ → ℝ) (R D a : ℝ) (ha : 0 < a) (N₀ : ℕ)
    (h : ∀ kc : ℝ, ∀ N ≥ N₀, F kc N ≤ R + D * rhoN N ^ a) :
    Section4.limsup2 F ≤ (R : EReal) := by
  have hT : Tendsto (fun N : ℕ => R + D * rhoN N ^ a) atTop (𝓝 R) := by
    have := ((S3_tendsto_pos ha).const_mul D).const_add R
    simpa using this
  have hin : ∀ kc : ℝ, limsup (fun N : ℕ => (F kc N : EReal)) atTop ≤ (R : EReal) := by
    intro kc
    have h2 : Tendsto (fun N : ℕ => ((R + D * rhoN N ^ a : ℝ) : EReal)) atTop
        (𝓝 (R : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hT
    calc limsup (fun N : ℕ => (F kc N : EReal)) atTop
        ≤ limsup (fun N : ℕ => ((R + D * rhoN N ^ a : ℝ) : EReal)) atTop := by
          refine limsup_le_limsup ?_
          filter_upwards [eventually_ge_atTop N₀] with N hN
          exact EReal.coe_le_coe_iff.2 (h kc N hN)
      _ = (R : EReal) := h2.limsup_eq
  unfold Section4.limsup2
  calc limsup (fun kc : ℝ => limsup (fun N : ℕ => (F kc N : EReal)) atTop) atTop
      ≤ limsup (fun _ : ℝ => (R : EReal)) atTop := limsup_le_limsup (Eventually.of_forall hin)
    _ = (R : EReal) := limsup_const _

/-! ### Elementary facts on `V`, `g`, the regions and `λ` -/

/-- `mom L (u − v) = mom L u − mom L v`. -/
private lemma S3_mom_sub (L : ℝ) (u v : Idx) : mom L (u - v) = mom L u - mom L v := by
  ext i
  simp [mom, mul_sub]

/-- `V_{v−u} = V_{u−v}`. -/
private lemma S3_V_swap {V : R3 → ℝ} (hV : PotentialHyp V) (L : ℝ) (u v : Idx) :
    (ft V (mom L (v - u))).re = (ft V (mom L (u - v))).re := by
  rw [← scat_ft_V_neg hV, S3_mom_sub, S3_mom_sub, neg_sub]

/-- `|V_p| ≤ V₀ = ∫ V`. -/
private lemma S3_abs_V_le {V : R3 → ℝ} (hV : PotentialHyp V) (p : R3) :
    |(ft V p).re| ≤ ∫ x, V x :=
  (Complex.abs_re_le_norm _).trans (scat_ft_V_norm_le hV p)

/-- `Q_Ψ(u₁, …, u_s) ≥ 0`. -/
private lemma S3_Q_nonneg (Ψ : Occ → ℂ) (us : List Idx) : 0 ≤ Expect.Q Ψ us :=
  tsum_nonneg fun α => mul_nonneg (List.prod_nonneg (by simp)) (by positivity)

/-- `|Re ĝ(p)| ≤ ∫ |g|`. -/
private lemma S3_abs_re_ft_le (V w : R3 → ℝ) (p : R3) :
    |(ft (gfun V w) p).re| ≤ ∫ x, |gfun V w x| := by
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold ft
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- `|w_p| ≤ ‖g‖₁ |p|⁻²`. -/
private lemma S3_abs_wmom_le (V w : R3 → ℝ) (p : R3) :
    |wmom V w p| ≤ (∫ x, |gfun V w x|) / ‖p‖ ^ 2 := by
  unfold wmom
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖p‖ ^ 2)]
  exact div_le_div_of_nonneg_right (S3_abs_re_ft_le V w p) (by positivity)

/-- `w_{−p} = w_p`. -/
private lemma S3_wmom_neg {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    (p : R3) : wmom V w (-p) = wmom V w p := by
  unfold wmom
  rw [scat_ft_g_neg hV hw p, norm_neg]

/-- `P` excludes `0`. -/
private lemma S3_inP_ne_zero {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inP ρ L n) : n ≠ 0 := by
  rcases h with h | h | h
  · exact Regions_PL_ne_zero hρ h
  · exact Regions_PI_ne_zero hρ h
  · exact Regions_PH_ne_zero hρ h

/-- For `u ∈ P_L` and `v ∈ P_I ∪ P_H`: `u ≠ v` and `u + v ≠ 0`. -/
private lemma S3_L_IH_ne {ρ L : ℝ} (hρ : 0 < ρ) {u v : Idx} (hu : inPL ρ L u)
    (hv : inPI ρ L v ∨ inPH ρ L v) : u ≠ v ∧ u + v ≠ 0 := by
  have key : ∀ n : Idx, inPL ρ L n → ¬ (inPI ρ L n ∨ inPH ρ L n) := fun n hn h => by
    rcases h with h | h
    · exact Regions_PL_PI hn h
    · exact Regions_PL_PH hρ hn h
  refine ⟨fun h => key v (h ▸ hu) hv, fun h => ?_⟩
  have hv' : v = -u := eq_neg_of_add_eq_zero_right h
  rw [hv', Regions_PI_neg, Regions_PH_neg] at hv
  exact key u hu hv

/-- Off `P_L`, `λ_n = −w_n`. -/
private lemma S3_lam_off (V w : R3 → ℝ) {ρ L : ℝ} {n : Idx} (h : ¬ inPL ρ L n) :
    lam V w ρ L n = -wmom V w (mom L n) := by
  simp only [lam, h, ↓reduceIte, wmom, neg_div]

/-- On `P_L`, `|λ_u| ≤ g₀|p_u|^{-2}`, (5.9) [ublambda]. -/
private lemma S3_lam_PL_le {V w : R3 → ℝ} (hg : 0 < g0 V w) {ρ L : ℝ} (hρ : 0 < ρ)
    {n : Idx} (h : inPL ρ L n) (hn : 0 < ‖mom L n‖) :
    |lam V w ρ L n| ≤ g0 V w / ‖mom L n‖ ^ 2 := by
  rw [lam]
  simp only [h, ↓reduceIte]
  have hq : 0 < ‖mom L n‖ ^ 2 := by positivity
  set a : ℝ := 4 * ρ * g0 V w / ‖mom L n‖ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + a)
  have hs1 : 1 ≤ Real.sqrt (1 + a) := Real.one_le_sqrt.2 (by linarith)
  generalize Real.sqrt (1 + a) = s at hs hs1
  have hga : g0 V w / ‖mom L n‖ ^ 2 = a / (4 * ρ) := by
    rw [ha]
    field_simp
  rw [hga, abs_div, abs_div, abs_of_pos hρ, abs_of_pos (by linarith : 0 < 1 + s),
    abs_of_nonpos (by linarith : 1 - s ≤ 0), div_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  have h1 : 0 ≤ (s - 1) * (s - 1) * (s + 3) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h2 : -(1 - s) * 4 ≤ a * (1 + s) := by nlinarith
  nlinarith

/-- On `P_L`, `1 − (ρλ_u)² > 0` and `|λ_u/(1 − (ρλ_u)²)| ≤ g₀|p_u|^{-2}`. -/
private lemma S3_lam_PL_div {V w : R3 → ℝ} (hg : 0 < g0 V w) {ρ L : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {n : Idx} (h : inPL ρ L n) (hn : 0 < ‖mom L n‖) :
    0 < 1 - (ρ * lam V w ρ L n) ^ 2 ∧
      |lam V w ρ L n / (1 - (ρ * lam V w ρ L n) ^ 2)| ≤ g0 V w / ‖mom L n‖ ^ 2 := by
  have hx := Particles_rho_lam_PL hg hρ hρ1 h
  have h1 : 0 < 1 + ρ * lam V w ρ L n :=
    lt_of_lt_of_le (div_pos ((Real.rpow_pos_of_pos hρ _ : 0 < epsP ρ)) (by positivity)) hx.2
  refine ⟨by nlinarith [mul_pos h1 (neg_pos.2 hx.1)], ?_⟩
  rw [lam]
  simp only [h, ↓reduceIte]
  have hq : 0 < ‖mom L n‖ ^ 2 := by positivity
  set a : ℝ := 4 * ρ * g0 V w / ‖mom L n‖ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + a)
  have hs1 : 1 ≤ Real.sqrt (1 + a) := Real.one_le_sqrt.2 (by linarith)
  generalize Real.sqrt (1 + a) = s at hs hs1
  have hga : g0 V w / ‖mom L n‖ ^ 2 = a / (4 * ρ) := by
    rw [ha]
    field_simp
  have hr : ρ * ((1 - s) / (1 + s) / ρ) = (1 - s) / (1 + s) := by
    field_simp
  rw [hr, hga]
  have hs0 : 0 < 1 + s := by linarith
  have hd : 1 - ((1 - s) / (1 + s)) ^ 2 = 4 * s / (1 + s) ^ 2 := by
    field_simp
    ring
  rw [hd]
  have e : (1 - s) / (1 + s) / ρ / (4 * s / (1 + s) ^ 2) = -(a / (4 * s * ρ)) := by
    have : a = s ^ 2 - 1 := by linarith
    rw [this]
    field_simp
    ring
  rw [e, abs_neg, abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_left ha0 (by positivity) (by nlinarith)

/-! ### Finiteness of `P_L` and sums over `Idx × Idx` -/

/-- The lattice points with `‖p_n‖ ≤ R` form a finite set. -/
private lemma S3_finite_ball {L R : ℝ} (hL : 0 < L) : {n : Idx | ‖mom L n‖ ≤ R}.Finite := by
  set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
  refine (Set.finite_Icc (fun _ : Fin 3 => -B) (fun _ => B)).subset ?_
  intro n hn
  have hi : ∀ i : Fin 3, |(n i : ℝ)| ≤ B := by
    intro i
    have h1 : |(mom L n).ofLp i| ≤ R := by
      have := PiLp.norm_apply_le (mom L n) i
      rw [Real.norm_eq_abs] at this
      exact this.trans hn
    rw [Cells_mom_apply, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
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

/-- A family on `Idx` supported in `{‖p_n‖ ≤ R}` is summable. -/
private lemma S3_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
    (hf : ∀ n, f n ≠ 0 → ‖mom L n‖ ≤ R) : Summable f := by
  have hfin := S3_finite_ball (R := R) hL
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  by_contra h
  exact hn (hfin.mem_toFinset.2 (hf n h))

/-- `ε^{-1}ρ^{1/2} = ρ^{1/2 − 1/200}`, the outer radius of `P_L`. -/
private lemma S3_R_eq {ρ : ℝ} (hρ : 0 < ρ) :
    (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) = ρ ^ (1/2 - 1/200 : ℝ) := by
  rw [epsP, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
  norm_num

/-- `P_L ⊆ {‖p_n‖ ≤ ρ^{1/2 − 1/200}}`, so `P_L` is finite for `L > 0`. -/
private lemma S3_PL_finite {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L) : {n : Idx | inPL ρ L n}.Finite :=
  (S3_finite_ball (R := ρ ^ (1/2 - 1/200 : ℝ)) hL).subset fun n hn => by
    rw [← S3_R_eq hρ]
    exact hn.2

/-- A family on `Idx × Idx` supported on rows `u ∈ S`, with summable rows, is summable. -/
private lemma S3_summable_finleft {S : Finset Idx} {f : Idx × Idx → ℝ}
    (h0 : ∀ u v, u ∉ S → f (u, v) = 0) (h : ∀ u, Summable fun v => f (u, v)) : Summable f := by
  have hsum : ∀ u₀ ∈ S, Summable fun uv : Idx × Idx => if uv.1 = u₀ then f uv else 0 := by
    intro u₀ _
    have hinj : Function.Injective fun v : Idx => (u₀, v) := fun a b hab => (Prod.mk.inj hab).2
    refine (hinj.summable_iff (fun x hx => ?_)).1 ?_
    · have : x.1 ≠ u₀ := fun h => hx ⟨x.2, by ext <;> simp [h]⟩
      simp [this]
    · have : ((fun uv : Idx × Idx => if uv.1 = u₀ then f uv else 0) ∘ fun v : Idx => (u₀, v)) =
          fun v => f (u₀, v) := by
        funext v; simp
      rw [this]; exact h u₀
  have := summable_sum hsum
  refine this.congr fun uv => ?_
  by_cases h1 : uv.1 ∈ S
  · simp [h1]
  · simp [h0 _ _ h1]

/-- The sum of such a family is the sum of the row sums over `S`. -/
private lemma S3_tsum_finleft {S : Finset Idx} {f : Idx × Idx → ℝ}
    (h0 : ∀ u v, u ∉ S → f (u, v) = 0) (h : ∀ u, Summable fun v => f (u, v)) :
    ∑' uv, f uv = ∑ u ∈ S, ∑' v, f (u, v) := by
  have hs := S3_summable_finleft h0 h
  rw [hs.tsum_prod' h, tsum_eq_sum (s := S)]
  intro u hu
  simp [h0 u _ hu]

/-! ### The families of (7.65) [temp8.73] and their decomposition -/

/-- `V_{u−v} λ_u λ_v` on `u, v ∈ P`, `u ≠ ±v`: the sum `A` of (7.62). -/
private def S3_FA (P : Idx → Prop) (Vk : Idx → Idx → ℝ) (lm : Idx → ℝ) (x : Idx × Idx) : ℝ :=
  if P x.1 ∧ P x.2 ∧ x.1 ≠ x.2 ∧ x.1 + x.2 ≠ 0 then Vk x.1 x.2 * lm x.1 * lm x.2 else 0

/-- `V_{u−v} w_u w_v` on `u, v ∈ P`. -/
private def S3_FW (P : Idx → Prop) (Vk : Idx → Idx → ℝ) (wm : Idx → ℝ) (x : Idx × Idx) : ℝ :=
  if P x.1 ∧ P x.2 then Vk x.1 x.2 * wm x.1 * wm x.2 else 0

/-- The diagonal `u = ±v` part of `S3_FW`. -/
private def S3_FD (P : Idx → Prop) (Vk : Idx → Idx → ℝ) (wm : Idx → ℝ) (x : Idx × Idx) : ℝ :=
  if P x.1 ∧ P x.2 ∧ ¬ (x.1 ≠ x.2 ∧ x.1 + x.2 ≠ 0) then Vk x.1 x.2 * wm x.1 * wm x.2 else 0

/-- `V_{u−v} d_u w_v` on `u ∈ P_L`, `v ∈ P_I ∪ P_H`. -/
private def S3_FS (PL PI PH : Idx → Prop) (Vk : Idx → Idx → ℝ) (d wm : Idx → ℝ)
    (x : Idx × Idx) : ℝ :=
  if PL x.1 ∧ (PI x.2 ∨ PH x.2) then Vk x.1 x.2 * d x.1 * wm x.2 else 0

/-- `V_{u−v} a_u b_v` on `u, v ∈ P_L`, `u ≠ ±v`. -/
private def S3_F2 (PL : Idx → Prop) (Vk : Idx → Idx → ℝ) (a b : Idx → ℝ) (x : Idx × Idx) : ℝ :=
  if PL x.1 ∧ PL x.2 ∧ x.1 ≠ x.2 ∧ x.1 + x.2 ≠ 0 then Vk x.1 x.2 * a x.1 * b x.2 else 0

/-- Pointwise form of `λ = −w + d`: the identity behind (7.65) [temp8.73]. -/
private lemma S3_pt_decomp {PL PI PH : Idx → Prop} {Vk : Idx → Idx → ℝ} {lm wm : Idx → ℝ}
    (hdj : ∀ n, PL n → ¬ (PI n ∨ PH n))
    (hne : ∀ u v, PL u → (PI v ∨ PH v) → u ≠ v ∧ u + v ≠ 0)
    (hlam : ∀ n, ¬ PL n → lm n = -wm n)
    (hV : ∀ u v, Vk v u = Vk u v) (x : Idx × Idx) :
    S3_FW (fun n => PL n ∨ PI n ∨ PH n) Vk wm x =
      S3_FA (fun n => PL n ∨ PI n ∨ PH n) Vk lm x +
      S3_FD (fun n => PL n ∨ PI n ∨ PH n) Vk wm x +
      S3_FS PL PI PH Vk (fun n => lm n + wm n) wm x +
      S3_F2 PL Vk (fun n => lm n + wm n) wm x +
      (S3_FS PL PI PH Vk (fun n => lm n + wm n) wm x.swap +
        S3_F2 PL Vk (fun n => lm n + wm n) wm x.swap) -
      S3_F2 PL Vk (fun n => lm n + wm n) (fun n => lm n + wm n) x := by
  obtain ⟨u, v⟩ := x
  simp only [S3_FW, S3_FA, S3_FD, S3_FS, S3_F2, Prod.swap_prod_mk]
  have hVv := hV u v
  have hcase : ∀ n, PL n ∨ (PI n ∨ PH n) ∨ ¬ (PL n ∨ PI n ∨ PH n) := fun n => by tauto
  by_cases hoff : u ≠ v ∧ u + v ≠ 0
  · have hoff' : v ≠ u ∧ v + u ≠ 0 := ⟨hoff.1.symm, by rw [add_comm]; exact hoff.2⟩
    rcases hcase u with hu | hu | hu <;> rcases hcase v with hv | hv | hv
    · have h1 := hdj u hu
      have h2 := hdj v hv
      simp [hu, hv, hoff, hoff', h1, h2, hVv]
      ring
    · have h1 := hdj u hu
      have h2 : ¬ PL v := fun h => hdj v h hv
      have h3 := hlam v h2
      simp [hu, hv, hoff, hoff', h1, h2, h3]
      ring
    · have h1 := hdj u hu
      have h2 : ¬ PL v := fun h => hv (Or.inl h)
      have h4 : ¬ (PI v ∨ PH v) := fun h => hv (Or.inr h)
      simp [hu, hoff, hoff', h1, h2, h4]
    · have h1 : ¬ PL u := fun h => hdj u h hu
      have h2 := hdj v hv
      have h3 := hlam u h1
      simp [hu, hv, hoff, hoff', h1, h2, h3, hVv]
      ring
    · have h1 : ¬ PL u := fun h => hdj u h hu
      have h2 : ¬ PL v := fun h => hdj v h hv
      have h3 := hlam u h1
      have h4 := hlam v h2
      simp [hu, hv, hoff, hoff', h1, h2, h3, h4]
    · have h1 : ¬ PL u := fun h => hdj u h hu
      have h2 : ¬ PL v := fun h => hv (Or.inl h)
      have h4 : ¬ (PI v ∨ PH v) := fun h => hv (Or.inr h)
      simp [hu, hoff, hoff', h1, h2, h4]
    · have h1 : ¬ PL u := fun h => hu (Or.inl h)
      have h4 : ¬ (PI u ∨ PH u) := fun h => hu (Or.inr h)
      simp [hv, hoff, hoff', h1, h4]
    · have h1 : ¬ PL u := fun h => hu (Or.inl h)
      have h4 : ¬ (PI u ∨ PH u) := fun h => hu (Or.inr h)
      simp [hv, hoff, hoff', h1, h4]
    · have h1 : ¬ PL u := fun h => hu (Or.inl h)
      have h4 : ¬ (PI u ∨ PH u) := fun h => hu (Or.inr h)
      simp [hv, hoff, hoff', h1, h4]
  · have hFS : ¬ (PL u ∧ (PI v ∨ PH v)) := fun h => hoff (hne u v h.1 h.2)
    have hFS' : ¬ (PL v ∧ (PI u ∨ PH u)) := fun h =>
      hoff ⟨(hne v u h.1 h.2).1.symm, by rw [add_comm]; exact (hne v u h.1 h.2).2⟩
    have hoffv : ¬ (v ≠ u ∧ v + u ≠ 0) := fun h => hoff ⟨h.1.symm, by rw [add_comm]; exact h.2⟩
    simp [hoff, hFS, hFS', hoffv]

/-- The families supported on `P_L × P_L` are summable when `P_L` is finite. -/
private lemma S3_F2_summable {PL : Idx → Prop} (hfin : {n : Idx | PL n}.Finite)
    (Vk : Idx → Idx → ℝ) (a b : Idx → ℝ) : Summable (S3_F2 PL Vk a b) := by
  refine summable_of_ne_finset_zero (s := hfin.toFinset ×ˢ hfin.toFinset) fun x hx => ?_
  unfold S3_F2
  refine ite_eq_right_iff.2 fun h => absurd ?_ hx
  exact Finset.mem_product.2 ⟨hfin.mem_toFinset.2 h.1, hfin.mem_toFinset.2 h.2.1⟩

/-- `Σ A = Σ W − Σ D − 2 Σ S − 2 Σ F₂ + Σ F₃`, the sum form of `λ = −w + d`. -/
private lemma S3_sum_decomp {PL PI PH : Idx → Prop} {Vk : Idx → Idx → ℝ} {lm wm : Idx → ℝ}
    (hdj : ∀ n, PL n → ¬ (PI n ∨ PH n))
    (hne : ∀ u v, PL u → (PI v ∨ PH v) → u ≠ v ∧ u + v ≠ 0)
    (hlam : ∀ n, ¬ PL n → lm n = -wm n)
    (hV : ∀ u v, Vk v u = Vk u v) (hfin : {n : Idx | PL n}.Finite)
    (hA : Summable (S3_FA (fun n => PL n ∨ PI n ∨ PH n) Vk lm))
    (hS : Summable (S3_FS PL PI PH Vk (fun n => lm n + wm n) wm))
    (hD : Summable (S3_FD (fun n => PL n ∨ PI n ∨ PH n) Vk wm)) :
    Summable (S3_FW (fun n => PL n ∨ PI n ∨ PH n) Vk wm) ∧
      (∑' x, S3_FA (fun n => PL n ∨ PI n ∨ PH n) Vk lm x) =
        (∑' x, S3_FW (fun n => PL n ∨ PI n ∨ PH n) Vk wm x) -
          (∑' x, S3_FD (fun n => PL n ∨ PI n ∨ PH n) Vk wm x) -
          2 * (∑' x, S3_FS PL PI PH Vk (fun n => lm n + wm n) wm x) -
          2 * (∑' x, S3_F2 PL Vk (fun n => lm n + wm n) wm x) +
          (∑' x, S3_F2 PL Vk (fun n => lm n + wm n) (fun n => lm n + wm n) x) := by
  set P : Idx → Prop := fun n => PL n ∨ PI n ∨ PH n with hP
  set d : Idx → ℝ := fun n => lm n + wm n with hd
  have h2 := S3_F2_summable hfin Vk d wm
  have h3 := S3_F2_summable hfin Vk d d
  have hSsw : Summable (fun x : Idx × Idx =>
      S3_FS PL PI PH Vk d wm x.swap) :=
    (Equiv.prodComm Idx Idx).summable_iff.2 hS
  have h2sw : Summable (fun x : Idx × Idx => S3_F2 PL Vk d wm x.swap) :=
    (Equiv.prodComm Idx Idx).summable_iff.2 h2
  have hfun : S3_FW P Vk wm = fun x => S3_FA P Vk lm x + S3_FD P Vk wm x +
      S3_FS PL PI PH Vk d wm x + S3_F2 PL Vk d wm x +
      (S3_FS PL PI PH Vk d wm x.swap + S3_F2 PL Vk d wm x.swap) -
      S3_F2 PL Vk d d x := funext fun x => S3_pt_decomp hdj hne hlam hV x
  have hH := ((((hA.hasSum.add hD.hasSum).add hS.hasSum).add h2.hasSum).add
    (hSsw.hasSum.add h2sw.hasSum)).sub h3.hasSum
  rw [← hfun] at hH
  have e1 : ∑' x : Idx × Idx, S3_FS PL PI PH Vk d wm x.swap =
      ∑' x, S3_FS PL PI PH Vk d wm x :=
    (Equiv.prodComm Idx Idx).tsum_eq (S3_FS PL PI PH Vk d wm)
  have e2 : ∑' x : Idx × Idx, S3_F2 PL Vk d wm x.swap = ∑' x, S3_F2 PL Vk d wm x :=
    (Equiv.prodComm Idx Idx).tsum_eq (S3_F2 PL Vk d wm)
  refine ⟨hH.summable, ?_⟩
  have := hH.tsum_eq
  rw [e1, e2] at this
  linarith

/-- `|Σ_{x} V_{u−v} a_u b_v 1_{u,v ∈ P_L, …}| ≤ M (Σ_{P_L} |a|)(Σ_{P_L} |b|)`. -/
private lemma S3_PLPL_bound {PL : Idx → Prop} (hfin : {n : Idx | PL n}.Finite)
    {Vk : Idx → Idx → ℝ} {M : ℝ} (hM : ∀ u v, |Vk u v| ≤ M) (a b : Idx → ℝ) :
    |∑' x, S3_F2 PL Vk a b x| ≤
      M * (∑ u ∈ hfin.toFinset, |a u|) * (∑ v ∈ hfin.toFinset, |b v|) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  have hz : ∀ x ∉ hfin.toFinset ×ˢ hfin.toFinset, S3_F2 PL Vk a b x = 0 := by
    intro x hx
    unfold S3_F2
    refine ite_eq_right_iff.2 fun h => absurd ?_ hx
    exact Finset.mem_product.2 ⟨hfin.mem_toFinset.2 h.1, hfin.mem_toFinset.2 h.2.1⟩
  rw [tsum_eq_sum hz]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_product]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v hv => ?_
  unfold S3_F2
  split_ifs
  · rw [abs_mul, abs_mul]
    have h1 := hM u v
    have h2 := abs_nonneg (a u)
    have h3 := abs_nonneg (b v)
    calc |Vk u v| * |a u| * |b v| ≤ M * |a u| * |b v| := by gcongr
      _ = M * (|a u| * |b v|) := by ring
  · rw [abs_zero]
    positivity

/-- The diagonal `u = ±v`: `|Σ F_D| ≤ 2M Σ_{P} w²`, with summability. -/
private lemma S3_diag_bound {P : Idx → Prop} {Vk : Idx → Idx → ℝ} {M : ℝ}
    (hM : ∀ u v, |Vk u v| ≤ M) {wm : Idx → ℝ} (hneg : ∀ n, wm (-n) = wm n)
    (hsum : Summable fun n => if P n then wm n ^ 2 else 0) :
    Summable (S3_FD P Vk wm) ∧
      |∑' x, S3_FD P Vk wm x| ≤ 2 * M * ∑' n, (if P n then wm n ^ 2 else 0) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
  set h : Idx → ℝ := fun n => if P n then wm n ^ 2 else 0 with hh
  have hh0 : ∀ n, 0 ≤ h n := fun n => by
    simp only [hh]; split_ifs <;> positivity
  set g1 : Idx × Idx → ℝ := fun x => if x.2 = x.1 then M * h x.1 else 0 with hg1
  set g2 : Idx × Idx → ℝ := fun x => if x.2 = -x.1 then M * h x.1 else 0 with hg2
  have hinj1 : Function.Injective fun u : Idx => (u, u) := fun a b hab => (Prod.mk.inj hab).1
  have hinj2 : Function.Injective fun u : Idx => (u, -u) := fun a b hab => (Prod.mk.inj hab).1
  have hs1 : Summable g1 := by
    refine (hinj1.summable_iff (fun x hx => ?_)).1 ?_
    · have : x.2 ≠ x.1 := fun h' => hx ⟨x.1, by ext <;> simp [h']⟩
      simp [hg1, this]
    · simpa [hg1, Function.comp_def] using hsum.mul_left M
  have hs2 : Summable g2 := by
    refine (hinj2.summable_iff (fun x hx => ?_)).1 ?_
    · have : x.2 ≠ -x.1 := fun h' => hx ⟨x.1, by ext <;> simp [h']⟩
      simp [hg2, this]
    · simpa [hg2, Function.comp_def] using hsum.mul_left M
  have ht1 : ∑' x, g1 x = M * ∑' n, h n := by
    rw [← hinj1.tsum_eq (f := g1) (fun x hx => ?_)]
    · simp [hg1, tsum_mul_left]
    · by_contra hcon
      have : x.2 ≠ x.1 := fun h' => hcon ⟨x.1, by ext <;> simp [h']⟩
      exact hx (by simp [hg1, this])
  have ht2 : ∑' x, g2 x = M * ∑' n, h n := by
    rw [← hinj2.tsum_eq (f := g2) (fun x hx => ?_)]
    · simp [hg2, tsum_mul_left]
    · by_contra hcon
      have : x.2 ≠ -x.1 := fun h' => hcon ⟨x.1, by ext <;> simp [h']⟩
      exact hx (by simp [hg2, this])
  have hbd : ∀ x, ‖S3_FD P Vk wm x‖ ≤ g1 x + g2 x := by
    intro x
    obtain ⟨u, v⟩ := x
    have hg1' : 0 ≤ g1 (u, v) := by
      simp only [hg1]; split_ifs <;> [exact mul_nonneg hM0 (hh0 _); exact le_rfl]
    have hg2' : 0 ≤ g2 (u, v) := by
      simp only [hg2]; split_ifs <;> [exact mul_nonneg hM0 (hh0 _); exact le_rfl]
    unfold S3_FD
    split_ifs with hc
    · obtain ⟨hPu, hPv, hn⟩ := hc
      have hor : v = u ∨ v = -u := by
        by_cases h1 : u = v
        · exact Or.inl h1.symm
        · right
          have : u + v = 0 := by
            by_contra h2
            exact hn ⟨h1, h2⟩
          exact eq_neg_of_add_eq_zero_right this
      rcases hor with rfl | rfl
      · have : g1 (v, v) = M * h v := by simp [hg1]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_assoc, ← abs_mul, ← sq,
          abs_of_nonneg (sq_nonneg (wm v))]
        have e : h v = wm v ^ 2 := by simp [hh, hPu]
        calc |Vk v v| * wm v ^ 2 ≤ M * wm v ^ 2 := by gcongr; exact hM v v
          _ = g1 (v, v) := by rw [this, e]
          _ ≤ g1 (v, v) + g2 (v, v) := le_add_of_nonneg_right hg2'
      · have : g2 (u, -u) = M * h u := by simp [hg2]
        rw [Real.norm_eq_abs, abs_mul, abs_mul, hneg, mul_assoc, ← abs_mul, ← sq,
          abs_of_nonneg (sq_nonneg (wm u))]
        have e : h u = wm u ^ 2 := by simp [hh, hPu]
        calc |Vk u (-u)| * wm u ^ 2 ≤ M * wm u ^ 2 := by gcongr; exact hM u (-u)
          _ = g2 (u, -u) := by rw [this, e]
          _ ≤ g1 (u, -u) + g2 (u, -u) := le_add_of_nonneg_left hg1'
    · rw [norm_zero]; exact add_nonneg hg1' hg2'
  have hsD : Summable (S3_FD P Vk wm) :=
    Summable.of_norm_bounded (hs1.add hs2) hbd
  refine ⟨hsD, ?_⟩
  calc |∑' x, S3_FD P Vk wm x| ≤ ∑' x, ‖S3_FD P Vk wm x‖ := by
        simpa using norm_tsum_le_tsum_norm hsD.norm
    _ ≤ ∑' x, (g1 x + g2 x) := hsD.norm.tsum_le_tsum hbd (hs1.add hs2)
    _ = 2 * M * ∑' n, h n := by
        rw [hs1.tsum_add hs2, ht1, ht2]; ring

/-- `|Λ|⁻¹ Σ_{u ∈ P_L} |a_u| ≤ c K ρ^{1/2 − 1/200}` for `|a_u| ≤ c |p_u|^{-2}` on `P_L`
(`R = ρ^{1/2−1/200}`, `s = 2` of the lattice sum). -/
private lemma S3_PL_sum_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ L : ℝ, 0 < ρ → ρ ≤ 1 → 0 < L →
    2 * π ≤ L * ρ ^ (1/2 : ℝ) → ∀ (hfin : {n : Idx | inPL ρ L n}.Finite) (a : Idx → ℝ) (c : ℝ),
      0 ≤ c → (∀ n, inPL ρ L n → |a n| ≤ c / ‖mom L n‖ ^ 2) →
      (L ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset, |a n| ≤ c * K * ρ ^ (1/2 - 1/200 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := sum_norm_rpow_le (s := 2) (by norm_num : (2 : ℝ) < 3)
  refine ⟨K, hK0, fun ρ L hρ hρ1 hL hLρ hfin a c hc ha => ?_⟩
  have hR : 0 < ρ ^ (1/2 - 1/200 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hLR : 2 * π ≤ L * ρ ^ (1/2 - 1/200 : ℝ) := by
    refine hLρ.trans (mul_le_mul_of_nonneg_left (S3_rpow_le hρ hρ1 (by norm_num)) hL.le)
  have h1 := hK L (ρ ^ (1/2 - 1/200 : ℝ)) hR hLR
  have hbd : ∀ n, inPL ρ L n → n ≠ 0 ∧ 0 < ‖mom L n‖ ∧ ‖mom L n‖ ≤ ρ ^ (1/2 - 1/200 : ℝ) := by
    intro n hn
    have hb : ‖mom L n‖ ≤ ρ ^ (1/2 - 1/200 : ℝ) := by
      rw [← S3_R_eq hρ]
      exact hn.2
    have hpos : 0 < ‖mom L n‖ :=
      lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos hρ _)) hn.1
    exact ⟨Regions_PL_ne_zero hρ hn, hpos, hb⟩
  set F : Idx → ℝ := fun n =>
    if n ≠ 0 ∧ ‖mom L n‖ ≤ ρ ^ (1/2 - 1/200 : ℝ) then ‖mom L n‖ ^ (-(2 : ℝ)) else 0 with hF
  have hFs : Summable F := S3_summable_ball hL (R := ρ ^ (1/2 - 1/200 : ℝ)) F fun n hn => by
    by_contra hcon
    exact hn (ite_eq_right_iff.2 fun h => absurd h.2 hcon)
  have hle : ∑ n ∈ hfin.toFinset, |a n| ≤ c * ∑' n, F n := by
    rw [← tsum_mul_left]
    have hz : ∀ n ∉ hfin.toFinset, c * F n ≥ 0 := fun n _ => by
      simp only [hF]; split_ifs <;> positivity
    calc ∑ n ∈ hfin.toFinset, |a n|
        ≤ ∑ n ∈ hfin.toFinset, c * F n := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn' : inPL ρ L n := hfin.mem_toFinset.1 hn
          obtain ⟨h1, h2, h3⟩ := hbd n hn'
          simp only [hF, h1, h3, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
          rw [Real.rpow_neg h2.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
            ← div_eq_mul_inv]
          exact ha n hn'
      _ ≤ ∑' n, c * F n := by
          refine (hFs.mul_left c).sum_le_tsum _ (fun n hn => ?_)
          simp only [hF]; split_ifs <;> positivity
  calc (L ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset, |a n| ≤ (L ^ 3)⁻¹ * (c * ∑' n, F n) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = c * ((L ^ 3)⁻¹ * ∑' n, F n) := by ring
    _ ≤ c * (K * (ρ ^ (1/2 - 1/200 : ℝ)) ^ (3 - 2 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        simpa [hF] using h1
    _ = c * K * ρ ^ (1/2 - 1/200 : ℝ) := by
        rw [show (3 - 2 : ℝ) = 1 by norm_num, Real.rpow_one]; ring

/-! ### Summability facts at `ρ = ρ_N`, `L = L_N` -/

/-- Summability of the `S3_FA` family and of the rows of the mixed sum, and `|Λ|⁻² |Σ A| ≤ K`
(facts (2) and (5) before (7.65) [temp8.73]). -/
private lemma S3_summable_facts {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Summable (S3_FA (inP (rhoN N) (LN N)) (fun u v => (ft V (mom (LN N) (u - v))).re)
        (lam V w (rhoN N) (LN N))) ∧
      |((LN N ^ 3) ^ 2)⁻¹ * ∑' x, S3_FA (inP (rhoN N) (LN N))
        (fun u v => (ft V (mom (LN N) (u - v))).re) (lam V w (rhoN N) (LN N)) x| ≤ K ∧
      ∀ u : Idx, Summable fun v : Idx =>
        if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
          (ft V (mom (LN N) (u - v))).re * wmom V w (mom (LN N) v) else 0 := by
  obtain ⟨K, hK0, N₁, hK⟩ := Pair_sum_lamV hV hw
  refine ⟨K, hK0, max N₁ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨hrow, hs2, hb2⟩ := hK N (le_trans (le_max_left _ _) hN)
  have hdom : ∀ x : Idx × Idx, ‖S3_FA (inP (rhoN N) (LN N))
      (fun u v => (ft V (mom (LN N) (u - v))).re) (lam V w (rhoN N) (LN N)) x‖ ≤
      if x.1 ≠ 0 ∧ x.2 ≠ 0 then
        |lam V w (rhoN N) (LN N) x.1 * (ft V (mom (LN N) (x.1 - x.2))).re *
          lam V w (rhoN N) (LN N) x.2| else 0 := by
    intro x
    unfold S3_FA
    split_ifs with h1 h2 h2
    · rw [Real.norm_eq_abs]
      refine le_of_eq ?_
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
      ring
    · exact absurd ⟨S3_inP_ne_zero hρ h1.1, S3_inP_ne_zero hρ h1.2.1⟩ h2
    · rw [norm_zero]; exact abs_nonneg _
    · rw [norm_zero]
  have hsA := Summable.of_norm_bounded hs2 hdom
  refine ⟨hsA, ?_, fun u => ?_⟩
  · refine le_trans ?_ hb2
    have hc : 0 ≤ ((LN N ^ 3) ^ 2)⁻¹ := by positivity
    rw [abs_mul, abs_of_nonneg hc]
    refine mul_le_mul_of_nonneg_left ?_ hc
    refine (norm_tsum_le_tsum_norm hsA.norm).trans ?_
    exact hsA.norm.tsum_le_tsum hdom hs2
  · have hrow' := (hrow (mom (LN N) u)).1
    refine Summable.of_norm_bounded hrow' fun v => ?_
    by_cases hv : inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v
    · have hvP : inP (rhoN N) (LN N) v := by
        rcases hv with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      have hv0 : v ≠ 0 := S3_inP_ne_zero hρ hvP
      have hPL : ¬ inPL (rhoN N) (LN N) v := by
        intro h
        rcases hv with h' | h'
        · exact Regions_PL_PI h h'
        · exact Regions_PL_PH hρ h h'
      simp only [hv, hv0, ne_eq, not_false_eq_true, ↓reduceIte, Real.norm_eq_abs]
      rw [S3_mom_sub, S3_lam_off V w hPL, abs_mul, abs_mul, abs_neg, mul_comm]
    · simp only [hv, ↓reduceIte, norm_zero]
      split_ifs <;> first | exact abs_nonneg _ | exact le_rfl

/-- The mixed `P_L × (P_I ∪ P_H)` family with a weight `f_u` is summable, with sum
`Σ_{u ∈ P_L} f_u t_u`, `t_u = Σ_{v ∈ P_I ∪ P_H} V_{u−v} w_v`. -/
private lemma S3_mixed_sum {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hfin : {n : Idx | inPL (rhoN N) (LN N) n}.Finite) (f : Idx → ℝ),
      Summable (fun x : Idx × Idx =>
        if inPL (rhoN N) (LN N) x.1 ∧ (inPI (rhoN N) (LN N) x.2 ∨ inPH (rhoN N) (LN N) x.2) then
          (ft V (mom (LN N) (x.1 - x.2))).re * f x.1 * wmom V w (mom (LN N) x.2) else 0) ∧
      ∑' x : Idx × Idx,
        (if inPL (rhoN N) (LN N) x.1 ∧ (inPI (rhoN N) (LN N) x.2 ∨ inPH (rhoN N) (LN N) x.2) then
          (ft V (mom (LN N) (x.1 - x.2))).re * f x.1 * wmom V w (mom (LN N) x.2) else 0) =
        ∑ u ∈ hfin.toFinset, f u * ∑' v : Idx,
          (if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
            (ft V (mom (LN N) (u - v))).re * wmom V w (mom (LN N) v) else 0) := by
  obtain ⟨K, -, N₀, h⟩ := S3_summable_facts hV hw
  refine ⟨N₀, fun N hN hfin f => ?_⟩
  have hrow := (h N hN).2.2
  have h0 : ∀ u v : Idx, u ∉ hfin.toFinset → (fun x : Idx × Idx =>
      if inPL (rhoN N) (LN N) x.1 ∧ (inPI (rhoN N) (LN N) x.2 ∨ inPH (rhoN N) (LN N) x.2) then
        (ft V (mom (LN N) (x.1 - x.2))).re * f x.1 * wmom V w (mom (LN N) x.2) else 0) (u, v) =
        0 := by
    intro u v hu
    refine ite_eq_right_iff.2 fun hc => absurd ?_ hu
    exact hfin.mem_toFinset.2 hc.1
  have hrows : ∀ u : Idx, (∀ v : Idx, (fun x : Idx × Idx =>
      if inPL (rhoN N) (LN N) x.1 ∧ (inPI (rhoN N) (LN N) x.2 ∨ inPH (rhoN N) (LN N) x.2) then
        (ft V (mom (LN N) (x.1 - x.2))).re * f x.1 * wmom V w (mom (LN N) x.2) else 0) (u, v) =
        if inPL (rhoN N) (LN N) u then f u * (if inPI (rhoN N) (LN N) v ∨
          inPH (rhoN N) (LN N) v then (ft V (mom (LN N) (u - v))).re *
            wmom V w (mom (LN N) v) else 0) else 0) := by
    intro u v
    by_cases hu : inPL (rhoN N) (LN N) u
    · by_cases hv : inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v
      · simp only [hu, hv, and_self, ↓reduceIte]
        ring
      · simp [hu, hv]
    · simp [hu]
  have hsr : ∀ u : Idx, Summable fun v : Idx => (fun x : Idx × Idx =>
      if inPL (rhoN N) (LN N) x.1 ∧ (inPI (rhoN N) (LN N) x.2 ∨ inPH (rhoN N) (LN N) x.2) then
        (ft V (mom (LN N) (x.1 - x.2))).re * f x.1 * wmom V w (mom (LN N) x.2) else 0) (u, v) := by
    intro u
    simp_rw [hrows u]
    by_cases hu : inPL (rhoN N) (LN N) u
    · simp only [hu, ↓reduceIte]
      exact (hrow u).mul_left (f u)
    · simp only [hu, ↓reduceIte]
      exact summable_zero
  refine ⟨S3_summable_finleft h0 hsr, ?_⟩
  rw [S3_tsum_finleft h0 hsr]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : inPL (rhoN N) (LN N) u := hfin.mem_toFinset.1 hu
  simp_rw [hrows u]
  simp only [hu', ↓reduceIte]
  rw [tsum_mul_left]

/-- On `P_L`, `d_u = λ_u + w_u`, `w_u` and `Y_u = λ_u/(1 − (ρλ_u)²) + w_u` satisfy
`|Λ|⁻¹ Σ_{P_L} |·| ≤ K ρ^{1/2 − 1/200}`. -/
private lemma S3_PL_sums {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (hfin : {n : Idx | inPL (rhoN N) (LN N) n}.Finite),
      (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset,
        |lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n)| ≤ K * rhoN N ^ (1/2 - 1/200 : ℝ) ∧
      (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset,
        |wmom V w (mom (LN N) n)| ≤ K * rhoN N ^ (1/2 - 1/200 : ℝ) ∧
      (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset,
        |lam V w (rhoN N) (LN N) n / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) +
          wmom V w (mom (LN N) n)| ≤ K * rhoN N ^ (1/2 - 1/200 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨K2, hK2, h2⟩ := S3_PL_sum_le
  have hcg : 0 ≤ ∫ x, |gfun V w x| := integral_nonneg fun x => abs_nonneg _
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (S3_ev_L.and (eventually_ge_atTop 1))
  refine ⟨(g0 V w + ∫ x, |gfun V w x|) * K2, by positivity, N₀, fun N hN hfin => ?_⟩
  obtain ⟨hLρ, hN1⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set cg := ∫ x, |gfun V w x| with hcg_def
  have hpos : ∀ n, inPL (rhoN N) (LN N) n → 0 < ‖mom (LN N) n‖ := fun n hn =>
    lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos hρ _)) hn.1
  have hR0 : 0 ≤ rhoN N ^ (1/2 - 1/200 : ℝ) := Real.rpow_nonneg hρ.le _
  have hlam : ∀ n, inPL (rhoN N) (LN N) n →
      |lam V w (rhoN N) (LN N) n| ≤ g0 V w / ‖mom (LN N) n‖ ^ 2 := fun n hn =>
    S3_lam_PL_le hg hρ hn (hpos n hn)
  have hwm : ∀ n, |wmom V w (mom (LN N) n)| ≤ cg / ‖mom (LN N) n‖ ^ 2 := fun n =>
    S3_abs_wmom_le V w _
  refine ⟨?_, ?_, ?_⟩
  · have := h2 (rhoN N) (LN N) hρ hρ1 hL hLρ hfin
      (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n)) (g0 V w + cg)
      (by positivity) (fun n hn => by
        refine (abs_add_le _ _).trans ?_
        rw [add_div]
        exact add_le_add (hlam n hn) (hwm n))
    exact this.trans (le_of_eq (by ring))
  · have := h2 (rhoN N) (LN N) hρ hρ1 hL hLρ hfin
      (fun n => wmom V w (mom (LN N) n)) cg hcg (fun n _ => hwm n)
    refine this.trans ?_
    have hK : 0 ≤ K2 * rhoN N ^ (1/2 - 1/200 : ℝ) := by positivity
    nlinarith [mul_nonneg hg.le hK]
  · have := h2 (rhoN N) (LN N) hρ hρ1 hL hLρ hfin
      (fun n => lam V w (rhoN N) (LN N) n / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) +
        wmom V w (mom (LN N) n)) (g0 V w + cg)
      (by positivity) (fun n hn => by
        refine (abs_add_le _ _).trans ?_
        rw [add_div]
        exact add_le_add (S3_lam_PL_div hg hρ hρ1 hn (hpos n hn)).2 (hwm n))
    exact this.trans (le_of_eq (by ring))

/-- Eventually `4π ≤ L_N ρ_N^{1/2 + 1/200}`. -/
private lemma S3_ev_L2 : ∀ᶠ N : ℕ in atTop, 4 * π ≤ LN N * rhoN N ^ (1/2 + 1/200 : ℝ) := by
  filter_upwards [(S3_tendsto_neg (by norm_num : (0 : ℝ) < 13 / 24 - 1 / 200)).eventually_ge_atTop
    (4 * π), eventually_ge_atTop 1] with N h hN
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  have : LN N * rhoN N ^ (1/2 + 1/200 : ℝ) = rhoN N ^ (-(13/24 - 1/200 : ℝ)) := by
    rw [Real.rpow_add hρ, ← mul_assoc, S3_L_sqrt hN, ← Real.rpow_add hρ]
    norm_num
  rw [this]
  exact h

/-- `mom L (−n) = −mom L n`. -/
private lemma S3_mom_neg (L : ℝ) (n : Idx) : mom L (-n) = -mom L n := by
  ext i
  simp [mom, mul_neg]

/-- On `P`, `ε ρ^{1/2} ≤ ‖p_n‖`. -/
private lemma S3_inP_lower {ρ L : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {n : Idx} (h : inP ρ L n) :
    epsP ρ * ρ ^ (1/2 : ℝ) ≤ ‖mom L n‖ := by
  have he0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have he1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hs0 : 0 < ρ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hs1 : ρ ^ (1/2 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  rcases h with h | h | h
  · exact h.1
  · have : epsP ρ ≤ (epsP ρ)⁻¹ := he1.trans ((one_le_inv₀ he0).2 he1)
    exact (mul_le_mul_of_nonneg_right this hs0.le).trans h.1.le
  · calc epsP ρ * ρ ^ (1/2 : ℝ) ≤ epsP ρ * 1 := mul_le_mul_of_nonneg_left hs1 he0.le
      _ ≤ ‖mom L n‖ := by rw [mul_one]; exact (show epsP ρ < ‖mom L n‖ from h).le

/-- The diagonal `u = ±v` of the `w w` sum of (7.65) [temp8.73]:
`|Λ|⁻² |Σ_{u = ±v} V_{u−v} w_u w_v| ≤ D ρ^{1/2+1/400}`, with summability. -/
private lemma S3_diag_N {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Summable (S3_FD (inP (rhoN N) (LN N)) (fun u v => (ft V (mom (LN N) (u - v))).re)
        (fun n => wmom V w (mom (LN N) n))) ∧
      ((LN N ^ 3) ^ 2)⁻¹ * |∑' x, S3_FD (inP (rhoN N) (LN N))
        (fun u v => (ft V (mom (LN N) (u - v))).re) (fun n => wmom V w (mom (LN N) n)) x| ≤
        D * rhoN N ^ (1/2 + 1/400 : ℝ) := by
  obtain ⟨K4, hK4, h4⟩ := sum_norm_rpow_gt (s := 4) (by norm_num)
  obtain ⟨N5, h5⟩ := eventually_atTop.1 (S3_ev_L.and ((eventually_ge_atTop 1).and S3_ev_L2))
  set cg := ∫ x, |gfun V w x| with hcg_def
  set M := ∫ x, V x with hM_def
  have hcg : 0 ≤ cg := integral_nonneg fun x => abs_nonneg _
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (S3_abs_V_le hV 0)
  refine ⟨4 * M * cg ^ 2 * K4, by positivity, N5, fun N hN => ?_⟩
  obtain ⟨hLρ, hN1b, hL2⟩ := h5 N hN
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1b
  have hM : ∀ u v : Idx, |(ft V (mom (LN N) (u - v))).re| ≤ M := fun u v => S3_abs_V_le hV _
  have hneg : ∀ n : Idx, wmom V w (mom (LN N) (-n)) = wmom V w (mom (LN N) n) := fun n => by
    rw [S3_mom_neg, S3_wmom_neg hV hw]
  set R4 : ℝ := rhoN N ^ (1/2 + 1/200 : ℝ) / 2 with hR4
  have hR4pos : 0 < R4 := by positivity
  have hLR4 : 2 * π ≤ LN N * R4 := by
    rw [hR4, ← mul_div_assoc, le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith
  obtain ⟨hG4s, hG4⟩ := h4 (LN N) R4 hR4pos hLR4
  have hinP : ∀ n, inP (rhoN N) (LN N) n → R4 < ‖mom (LN N) n‖ := fun n hn => by
    have h1 := S3_inP_lower hρ hρ1 hn
    have h2 : 0 < epsP (rhoN N) * rhoN N ^ (1/2 : ℝ) :=
      mul_pos (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos hρ _)
    have h3 : epsP (rhoN N) * rhoN N ^ (1/2 : ℝ) = rhoN N ^ (1/2 + 1/200 : ℝ) := by
      rw [epsP, mul_comm, ← Real.rpow_add hρ]
    rw [h3] at h1 h2
    rw [hR4]
    linarith
  have hwsq : ∀ n, inP (rhoN N) (LN N) n →
      wmom V w (mom (LN N) n) ^ 2 ≤ cg ^ 2 * ‖mom (LN N) n‖ ^ (-4 : ℝ) := fun n hn => by
    have hpos : 0 < ‖mom (LN N) n‖ := lt_trans hR4pos (hinP n hn)
    have h1 := S3_abs_wmom_le V w (mom (LN N) n)
    have h2 : wmom V w (mom (LN N) n) ^ 2 = |wmom V w (mom (LN N) n)| ^ 2 := (sq_abs _).symm
    rw [h2]
    have h3 : |wmom V w (mom (LN N) n)| ^ 2 ≤ (cg / ‖mom (LN N) n‖ ^ 2) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h3.trans (le_of_eq ?_)
    rw [Real.rpow_neg hpos.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hsumh : Summable fun n : Idx => if inP (rhoN N) (LN N) n then
      wmom V w (mom (LN N) n) ^ 2 else 0 := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (hG4s.mul_left (cg ^ 2))
    · split_ifs <;> positivity
    · by_cases hn : inP (rhoN N) (LN N) n
      · simp only [hn, ↓reduceIte, hinP n hn]
        exact hwsq n hn
      · simp only [hn, ↓reduceIte]
        split_ifs <;> positivity
  obtain ⟨hDs, hDb⟩ := S3_diag_bound (P := inP (rhoN N) (LN N))
    (Vk := fun u v => (ft V (mom (LN N) (u - v))).re) (M := M) hM
    (wm := fun n => wmom V w (mom (LN N) n)) hneg hsumh
  refine ⟨hDs, ?_⟩
  set c : ℝ := ((LN N ^ 3) ^ 2)⁻¹ with hc
  have hL3 : 0 < LN N ^ 3 := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hcc : c = (LN N ^ 3)⁻¹ * (LN N ^ 3)⁻¹ := by rw [hc, sq, mul_inv]
  have hLinv : (LN N ^ 3)⁻¹ = rhoN N ^ (25/8 : ℝ) := by
    rw [S3_L3, Real.rpow_neg hρ.le, inv_inv]
  have h1 : ∑' n : Idx, (if inP (rhoN N) (LN N) n then wmom V w (mom (LN N) n) ^ 2 else 0) ≤
      cg ^ 2 * ∑' n : Idx, (if R4 < ‖mom (LN N) n‖ then ‖mom (LN N) n‖ ^ (-4 : ℝ) else 0) := by
    rw [← tsum_mul_left]
    refine hsumh.tsum_le_tsum (fun n => ?_) (hG4s.mul_left _)
    by_cases hn : inP (rhoN N) (LN N) n
    · simp only [hn, ↓reduceIte, hinP n hn]
      exact hwsq n hn
    · simp only [hn, ↓reduceIte]
      split_ifs <;> positivity
  have h2 : (LN N ^ 3)⁻¹ * ∑' n : Idx,
      (if R4 < ‖mom (LN N) n‖ then ‖mom (LN N) n‖ ^ (-4 : ℝ) else 0) ≤
      K4 * (2 * (rhoN N ^ (1/2 + 1/200 : ℝ))⁻¹) := by
    refine hG4.trans (le_of_eq ?_)
    rw [show (3 - 4 : ℝ) = -1 by norm_num, Real.rpow_neg_one, hR4]
    field_simp
  have h3 : c * |∑' x, S3_FD (inP (rhoN N) (LN N))
      (fun u v => (ft V (mom (LN N) (u - v))).re) (fun n => wmom V w (mom (LN N) n)) x| ≤
      c * (2 * M * (cg ^ 2 * ∑' n : Idx, (if R4 < ‖mom (LN N) n‖ then
        ‖mom (LN N) n‖ ^ (-4 : ℝ) else 0))) :=
    mul_le_mul_of_nonneg_left (hDb.trans (mul_le_mul_of_nonneg_left h1 (by positivity))) hc0
  refine h3.trans ?_
  have h4' : c * (2 * M * (cg ^ 2 * ∑' n : Idx, (if R4 < ‖mom (LN N) n‖ then
      ‖mom (LN N) n‖ ^ (-4 : ℝ) else 0))) =
      2 * M * cg ^ 2 * (LN N ^ 3)⁻¹ * ((LN N ^ 3)⁻¹ * ∑' n : Idx,
        (if R4 < ‖mom (LN N) n‖ then ‖mom (LN N) n‖ ^ (-4 : ℝ) else 0)) := by
    rw [hcc]; ring
  rw [h4']
  have hin : 0 ≤ 2 * M * cg ^ 2 * (LN N ^ 3)⁻¹ := by positivity
  refine (mul_le_mul_of_nonneg_left h2 hin).trans ?_
  have h5' : (LN N ^ 3)⁻¹ * (K4 * (2 * (rhoN N ^ (1/2 + 1/200 : ℝ))⁻¹)) =
      2 * K4 * rhoN N ^ (25/8 - (1/2 + 1/200) : ℝ) := by
    rw [hLinv, Real.rpow_sub hρ, div_eq_mul_inv]
    ring
  have hp := S3_rpow_le hρ hρ1 (show (1/2 + 1/400 : ℝ) ≤ 25/8 - (1/2 + 1/200) by norm_num)
  calc 2 * M * cg ^ 2 * (LN N ^ 3)⁻¹ * (K4 * (2 * (rhoN N ^ (1/2 + 1/200 : ℝ))⁻¹))
      = 2 * M * cg ^ 2 * ((LN N ^ 3)⁻¹ * (K4 * (2 * (rhoN N ^ (1/2 + 1/200 : ℝ))⁻¹))) := by
        ring
    _ = 2 * M * cg ^ 2 * (2 * K4 * rhoN N ^ (25/8 - (1/2 + 1/200) : ℝ)) := by rw [h5']
    _ ≤ 2 * M * cg ^ 2 * (2 * K4 * rhoN N ^ (1/2 + 1/400 : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 4 * M * cg ^ 2 * K4 * rhoN N ^ (1/2 + 1/400 : ℝ) := by ring

/-- The `P_L × P_L` parts `A₂`, `A₃` of (7.65) [temp8.73]:
`|Λ|⁻² |Σ_{u,v ∈ P_L} V_{u−v} a_u b_v| ≤ D ρ^{1/2+1/400}` for `a, b ∈ {d, w}`, `d = λ + w`. -/
private lemma S3_PLPL_N {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ _ : {n : Idx | inPL (rhoN N) (LN N) n}.Finite,
      ((LN N ^ 3) ^ 2)⁻¹ * |∑' x, S3_F2 (inPL (rhoN N) (LN N))
        (fun u v => (ft V (mom (LN N) (u - v))).re)
        (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
        (fun n => wmom V w (mom (LN N) n)) x| ≤ D * rhoN N ^ (1/2 + 1/400 : ℝ) ∧
      ((LN N ^ 3) ^ 2)⁻¹ * |∑' x, S3_F2 (inPL (rhoN N) (LN N))
        (fun u v => (ft V (mom (LN N) (u - v))).re)
        (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
        (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n)) x| ≤
        D * rhoN N ^ (1/2 + 1/400 : ℝ) := by
  obtain ⟨K3, hK3, N3, hP⟩ := S3_PL_sums hV hw
  set M := ∫ x, V x with hM_def
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (S3_abs_V_le hV 0)
  refine ⟨M * K3 ^ 2, by positivity, max N3 1, fun N hN hfin => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨hd3, hw3, -⟩ := hP N (le_trans (le_max_left _ _) hN) hfin
  have hM : ∀ u v : Idx, |(ft V (mom (LN N) (u - v))).re| ≤ M := fun u v => S3_abs_V_le hV _
  set c : ℝ := ((LN N ^ 3) ^ 2)⁻¹ with hc
  have hL3 : 0 < LN N ^ 3 := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hcc : c = (LN N ^ 3)⁻¹ * (LN N ^ 3)⁻¹ := by rw [hc, sq, mul_inv]
  set R : ℝ := rhoN N ^ (1/2 - 1/200 : ℝ) with hR
  have hR0 : 0 ≤ R := Real.rpow_nonneg hρ.le _
  have hRR : R * R ≤ rhoN N ^ (1/2 + 1/400 : ℝ) := by
    rw [hR, ← Real.rpow_add hρ]
    exact S3_rpow_le hρ hρ1 (by norm_num)
  have hsd : 0 ≤ (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset,
      |lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n)| := by positivity
  have hsw : 0 ≤ (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset, |wmom V w (mom (LN N) n)| := by positivity
  have key : ∀ a b : Idx → ℝ, ∀ sa sb : ℝ,
      (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset, |a n| ≤ sa →
      (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset, |b n| ≤ sb →
      c * |∑' x, S3_F2 (inPL (rhoN N) (LN N)) (fun u v => (ft V (mom (LN N) (u - v))).re) a b x|
        ≤ M * (sa * sb) := by
    intro a b sa sb ha hb
    have h1 := S3_PLPL_bound hfin hM a b
    have hna : 0 ≤ (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset, |a n| := by positivity
    have hnb : 0 ≤ (LN N ^ 3)⁻¹ * ∑ n ∈ hfin.toFinset, |b n| := by positivity
    have hsa : 0 ≤ sa := hna.trans ha
    calc c * |∑' x, S3_F2 (inPL (rhoN N) (LN N)) (fun u v => (ft V (mom (LN N) (u - v))).re) a b x|
        ≤ c * (M * (∑ u ∈ hfin.toFinset, |a u|) * (∑ v ∈ hfin.toFinset, |b v|)) :=
          mul_le_mul_of_nonneg_left h1 hc0
      _ = M * (((LN N ^ 3)⁻¹ * ∑ u ∈ hfin.toFinset, |a u|) *
            ((LN N ^ 3)⁻¹ * ∑ v ∈ hfin.toFinset, |b v|)) := by
          rw [hcc]; ring
      _ ≤ M * (sa * sb) := by gcongr
  have hK : M * ((K3 * R) * (K3 * R)) ≤ M * K3 ^ 2 * rhoN N ^ (1/2 + 1/400 : ℝ) := by
    calc M * ((K3 * R) * (K3 * R)) = M * K3 ^ 2 * (R * R) := by ring
      _ ≤ M * K3 ^ 2 * rhoN N ^ (1/2 + 1/400 : ℝ) := by gcongr
  exact ⟨(key _ _ _ _ hd3 hw3).trans hK, (key _ _ _ _ hd3 hd3).trans hK⟩

/-- The decomposition of (7.65) [temp8.73]: `A = ‖Vw²‖₁ − 2S + O(ρ^{1/2+1/400})`, with
`A = |Λ|⁻² Σ_{u,v ∈ P, u ≠ ±v} V_{u−v} λ_u λ_v` and
`S = |Λ|⁻² Σ_{u ∈ P_L, v ∈ P_I ∪ P_H} V_{u−v} (λ_u + w_u) w_v`. -/
private lemma S3_A_bound {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |((LN N ^ 3) ^ 2)⁻¹ * (∑' x, S3_FA (inP (rhoN N) (LN N))
          (fun u v => (ft V (mom (LN N) (u - v))).re) (lam V w (rhoN N) (LN N)) x) -
        (normVw2 V w - 2 * (((LN N ^ 3) ^ 2)⁻¹ * ∑' x,
          S3_FS (inPL (rhoN N) (LN N)) (inPI (rhoN N) (LN N)) (inPH (rhoN N) (LN N))
            (fun u v => (ft V (mom (LN N) (u - v))).re)
            (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
            (fun n => wmom V w (mom (LN N) n)) x))| ≤ C * rhoN N ^ (1/2 + 1/400 : ℝ) := by
  obtain ⟨K1, hK1, N1, hF⟩ := S3_summable_facts hV hw
  obtain ⟨CW, hCW, NW, hW⟩ := Pair_sum_Vww_P hV hw
  obtain ⟨N4, hmix⟩ := S3_mixed_sum hV hw
  obtain ⟨CD, hCD, ND, hD⟩ := S3_diag_N hV hw
  obtain ⟨CP, hCP, NP, hPP⟩ := S3_PLPL_N hV hw
  refine ⟨CW + CD + 3 * CP, by positivity, max (max (max N1 NW) (max N4 ND)) (max NP 1),
    fun N hN => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hN1', hNW'⟩, hN4', hND'⟩, hNP', hN1b⟩ := hN
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1b
  have hfin := S3_PL_finite hρ hL
  obtain ⟨hAs, -, -⟩ := hF N hN1'
  obtain ⟨hFSs, -⟩ := hmix N hN4' hfin (fun n => lam V w (rhoN N) (LN N) n +
    wmom V w (mom (LN N) n))
  obtain ⟨hDs, hDb⟩ := hD N hND'
  obtain ⟨hP2, hP3⟩ := hPP N hNP' hfin
  have hdj : ∀ n, inPL (rhoN N) (LN N) n → ¬ (inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n) :=
    fun n hn h => by
      rcases h with h | h
      · exact Regions_PL_PI hn h
      · exact Regions_PL_PH hρ hn h
  obtain ⟨hWs, hdec⟩ := S3_sum_decomp (PL := inPL (rhoN N) (LN N)) (PI := inPI (rhoN N) (LN N))
    (PH := inPH (rhoN N) (LN N)) (Vk := fun u v => (ft V (mom (LN N) (u - v))).re)
    (lm := lam V w (rhoN N) (LN N)) (wm := fun n => wmom V w (mom (LN N) n)) hdj
    (fun u v hu hv => S3_L_IH_ne hρ hu hv) (fun n hn => S3_lam_off V w hn)
    (fun u v => S3_V_swap hV (LN N) u v) hfin hAs hFSs hDs
  set c : ℝ := ((LN N ^ 3) ^ 2)⁻¹ with hc
  have hL3 : 0 < LN N ^ 3 := by positivity
  have hc0 : 0 ≤ c := by positivity
  have hpow : ∀ e : ℝ, 1/2 + 1/400 ≤ e → rhoN N ^ e ≤ rhoN N ^ (1/2 + 1/400 : ℝ) :=
    fun e he => S3_rpow_le hρ hρ1 he
  have he1 : |c * (∑' x, S3_FW (inP (rhoN N) (LN N))
      (fun u v => (ft V (mom (LN N) (u - v))).re) (fun n => wmom V w (mom (LN N) n)) x) -
        normVw2 V w| ≤ CW * rhoN N ^ (1/2 + 1/400 : ℝ) :=
    (hW N hNW').trans (mul_le_mul_of_nonneg_left (hpow _ (by norm_num)) hCW)
  have hkey : c * (∑' x, S3_FA (inP (rhoN N) (LN N))
          (fun u v => (ft V (mom (LN N) (u - v))).re) (lam V w (rhoN N) (LN N)) x) -
        (normVw2 V w - 2 * (c * ∑' x,
          S3_FS (inPL (rhoN N) (LN N)) (inPI (rhoN N) (LN N)) (inPH (rhoN N) (LN N))
            (fun u v => (ft V (mom (LN N) (u - v))).re)
            (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
            (fun n => wmom V w (mom (LN N) n)) x)) =
      (c * (∑' x, S3_FW (inP (rhoN N) (LN N))
        (fun u v => (ft V (mom (LN N) (u - v))).re) (fun n => wmom V w (mom (LN N) n)) x) -
          normVw2 V w) - c * (∑' x, S3_FD (inP (rhoN N) (LN N))
        (fun u v => (ft V (mom (LN N) (u - v))).re) (fun n => wmom V w (mom (LN N) n)) x) -
      2 * (c * (∑' x, S3_F2 (inPL (rhoN N) (LN N))
        (fun u v => (ft V (mom (LN N) (u - v))).re)
        (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
        (fun n => wmom V w (mom (LN N) n)) x)) +
      c * (∑' x, S3_F2 (inPL (rhoN N) (LN N))
        (fun u v => (ft V (mom (LN N) (u - v))).re)
        (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
        (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n)) x) := by
    have hdec' : (∑' x, S3_FA (inP (rhoN N) (LN N))
          (fun u v => (ft V (mom (LN N) (u - v))).re) (lam V w (rhoN N) (LN N)) x) =
        (∑' x, S3_FW (inP (rhoN N) (LN N))
          (fun u v => (ft V (mom (LN N) (u - v))).re) (fun n => wmom V w (mom (LN N) n)) x) -
        (∑' x, S3_FD (inP (rhoN N) (LN N))
          (fun u v => (ft V (mom (LN N) (u - v))).re) (fun n => wmom V w (mom (LN N) n)) x) -
        2 * (∑' x, S3_FS (inPL (rhoN N) (LN N)) (inPI (rhoN N) (LN N)) (inPH (rhoN N) (LN N))
          (fun u v => (ft V (mom (LN N) (u - v))).re)
          (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
          (fun n => wmom V w (mom (LN N) n)) x) -
        2 * (∑' x, S3_F2 (inPL (rhoN N) (LN N))
          (fun u v => (ft V (mom (LN N) (u - v))).re)
          (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
          (fun n => wmom V w (mom (LN N) n)) x) +
        (∑' x, S3_F2 (inPL (rhoN N) (LN N))
          (fun u v => (ft V (mom (LN N) (u - v))).re)
          (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
          (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n)) x) := hdec
    rw [hdec']
    ring
  rw [hkey]
  have a1 := abs_le.1 he1
  have a2 := abs_le.1 (show |c * ∑' x, S3_FD (inP (rhoN N) (LN N))
      (fun u v => (ft V (mom (LN N) (u - v))).re) (fun n => wmom V w (mom (LN N) n)) x| ≤
        CD * rhoN N ^ (1/2 + 1/400 : ℝ) by
    rw [abs_mul, abs_of_nonneg hc0]; exact hDb)
  have a3 := abs_le.1 (show |c * ∑' x, S3_F2 (inPL (rhoN N) (LN N))
      (fun u v => (ft V (mom (LN N) (u - v))).re)
      (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
      (fun n => wmom V w (mom (LN N) n)) x| ≤ CP * rhoN N ^ (1/2 + 1/400 : ℝ) by
    rw [abs_mul, abs_of_nonneg hc0]; exact hP2)
  have a4 := abs_le.1 (show |c * ∑' x, S3_F2 (inPL (rhoN N) (LN N))
      (fun u v => (ft V (mom (LN N) (u - v))).re)
      (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n))
      (fun n => lam V w (rhoN N) (LN N) n + wmom V w (mom (LN N) n)) x| ≤
        CP * rhoN N ^ (1/2 + 1/400 : ℝ) by
    rw [abs_mul, abs_of_nonneg hc0]; exact hP3)
  refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2]

/-- (7.65) [temp8.73]: `A = ρ₀²(‖Vw²‖₁ + A₁) + O(ρ^{5/2+η/2})`, with
`A₁ = −2|Λ|⁻² Σ_{u ∈ P_L, v ∈ P_I ∪ P_H} V_{u−v}(λ_u + w_u)w_v`; `A₂`, `A₃` and the diagonal
`u = ±v` are in the error. -/
theorem Eq7_65 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      |(Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
                (LN N ^ 3) ^ 2 *
              (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
                if inP (rhoN N) (LN N) uv.1 ∧ inP (rhoN N) (LN N) uv.2 ∧ uv.1 ≠ uv.2 ∧
                    uv.1 + uv.2 ≠ 0 then
                  (ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
                    lam V w (rhoN N) (LN N) uv.2 else 0)) -
          rho0 (g0 V w) (rhoN N) ^ 2 * (normVw2 V w -
            2 * (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
              if inPL (rhoN N) (LN N) uv.1 ∧
                  (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
                (ft V (mom (LN N) (uv.1 - uv.2))).re *
                  (lam V w (rhoN N) (LN N) uv.1 + wmom V w (mom (LN N) uv.1)) *
                  wmom V w (mom (LN N) uv.2) else 0)))|
        ≤ C * rhoN N ^ (5/2 + 1/400 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C6, hC6, N6, h6⟩ := Lemma5_6 hg
  obtain ⟨K1, hK1, N1, hF⟩ := S3_summable_facts hV hw
  obtain ⟨CA, hCA, NA, hA⟩ := S3_A_bound hV hw
  obtain ⟨N7, h7⟩ := eventually_atTop.1
    (S3_ev_small ((3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ)) (b := 1/2) (by norm_num))
  refine ⟨(C6 + 1) * K1 + CA, by positivity, max (max (max N6 N1) (max NA N7)) 1,
    fun N hN kc => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hN6, hN1'⟩, hNA, hN7⟩, hN1b⟩ := hN
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1b
  obtain ⟨hr00, hr0ρ, -, -⟩ := S3_rho0 hg.le hρ (by simpa [mul_assoc] using (h7 N hN7))
  obtain ⟨-, -, hrow⟩ := hF N hN1'
  have hSA := (hF N hN1').2.1
  have hA' := hA N hNA
  have hL3 : 0 < LN N ^ 3 := by positivity
  -- the prefactor
  have hQ0 : 0 ≤ Expect.Q (trialState V w kc N) [0] / (LN N ^ 3) ^ 2 ∧
      Expect.Q (trialState V w kc N) [0] / (LN N ^ 3) ^ 2 ≤ rhoN N ^ (5/2 + 1/400 : ℝ) := by
    refine ⟨div_nonneg (S3_Q_nonneg _ _) (by positivity), ?_⟩
    have hle : Expect.Q (trialState V w kc N) [0] ≤ N :=
      le_hasSum (Particles_hasSum_Q V w kc hN1b) 0 fun j _ => S3_Q_nonneg _ _
    calc Expect.Q (trialState V w kc N) [0] / (LN N ^ 3) ^ 2
        ≤ (N : ℝ) / (LN N ^ 3) ^ 2 := div_le_div_of_nonneg_right hle (by positivity)
      _ = rhoN N / LN N ^ 3 := by rw [← hρL]; field_simp
      _ ≤ rhoN N ^ (5/2 + 1/400 : ℝ) := S3_rho_div_L3_le hN1b
  have hab : |(Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
        (LN N ^ 3) ^ 2 - rho0 (g0 V w) (rhoN N) ^ 2| ≤
      (C6 + 1) * rhoN N ^ (5/2 + 1/400 : ℝ) := by
    have h6' := h6 N hN6 kc
    rw [sub_div]
    have := abs_le.1 h6'
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [this.1, this.2, hQ0.1, hQ0.2]
  have key : ∀ SA S : ℝ, |SA| ≤ K1 → |SA - (normVw2 V w - 2 * S)| ≤
        CA * rhoN N ^ (1/2 + 1/400 : ℝ) →
      |(Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
          (LN N ^ 3) ^ 2 * SA - rho0 (g0 V w) (rhoN N) ^ 2 * (normVw2 V w - 2 * S)| ≤
        ((C6 + 1) * K1 + CA) * rhoN N ^ (5/2 + 1/400 : ℝ) := by
    intro SA S h1 h2
    set a := (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
      (LN N ^ 3) ^ 2 with ha
    set r := rho0 (g0 V w) (rhoN N) ^ 2 with hr
    have e1 : a * SA - r * (normVw2 V w - 2 * S) =
        (a - r) * SA + r * (SA - (normVw2 V w - 2 * S)) := by ring
    have hr0 : 0 ≤ r := sq_nonneg _
    have hrρ : r ≤ rhoN N ^ 2 := by
      rw [hr]
      exact pow_le_pow_left₀ hr00 hr0ρ 2
    have hp : rhoN N ^ 2 * rhoN N ^ (1/2 + 1/400 : ℝ) = rhoN N ^ (5/2 + 1/400 : ℝ) := by
      rw [← Real.rpow_natCast (rhoN N) 2, ← Real.rpow_add hρ]
      norm_num
    have hpp : 0 ≤ rhoN N ^ (1/2 + 1/400 : ℝ) := Real.rpow_nonneg hρ.le _
    have hp2 : 0 ≤ rhoN N ^ (5/2 + 1/400 : ℝ) := Real.rpow_nonneg hρ.le _
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hr0]
    have t1 : |a - r| * |SA| ≤ (C6 + 1) * rhoN N ^ (5/2 + 1/400 : ℝ) * K1 :=
      mul_le_mul hab h1 (abs_nonneg _) (by positivity)
    have t2 : r * |SA - (normVw2 V w - 2 * S)| ≤ CA * rhoN N ^ (5/2 + 1/400 : ℝ) := by
      calc r * |SA - (normVw2 V w - 2 * S)|
          ≤ rhoN N ^ 2 * (CA * rhoN N ^ (1/2 + 1/400 : ℝ)) :=
            mul_le_mul hrρ h2 (abs_nonneg _) (by positivity)
        _ = CA * (rhoN N ^ 2 * rhoN N ^ (1/2 + 1/400 : ℝ)) := by ring
        _ = CA * rhoN N ^ (5/2 + 1/400 : ℝ) := by rw [hp]
    nlinarith [t1, t2]
  exact key _ _ hSA hA'

/-- The algebra behind (7.66)–(7.68): with `f₂ = d − Y`, `T_u = ‖Vw‖₁ + O(R)`,
`|Λ|⁻¹ Σ_{P_L} Y = ρ^{1/2}(G + e₁)` and the sums of `|d|`, `|Y|` at most `K R`,
`2ρ² |Λ|⁻¹ Σ f₂ T − ρ₀² · 2 |Λ|⁻¹ Σ d T + 2‖Vw‖₁ G ρ^{5/2} = O(ρ^{5/2+1/200})`. -/
private lemma S3_B_alg {ι : Type*} (S : Finset ι) (d Y f2 T : ι → ℝ)
    {ρ ρ0 κ m1 Gc U C5 K3 C1 e1 : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hf2 : ∀ u ∈ S, f2 u = d u - Y u)
    (hT : ∀ u ∈ S, |T u - m1| ≤ C5 * ρ ^ (1/2 - 1/200 : ℝ))
    (hU : 0 ≤ U) (hC5 : 0 ≤ C5) (hK3 : 0 ≤ K3) (hκ : 0 ≤ κ)
    (hd : U * ∑ u ∈ S, |d u| ≤ K3 * ρ ^ (1/2 - 1/200 : ℝ))
    (hY : U * ∑ u ∈ S, |Y u| ≤ K3 * ρ ^ (1/2 - 1/200 : ℝ))
    (hA3 : U * ∑ u ∈ S, Y u = ρ ^ (1/2 : ℝ) * (Gc + e1))
    (he1 : |e1| ≤ C1 * ρ ^ (1/200 : ℝ))
    (hr1 : 0 ≤ ρ ^ 2 - ρ0 ^ 2) (hr2 : ρ ^ 2 - ρ0 ^ 2 ≤ 2 * κ * ρ ^ (5/2 : ℝ)) :
    |2 * ρ ^ 2 * (U * ∑ u ∈ S, f2 u * T u) - ρ0 ^ 2 * (2 * (U * ∑ u ∈ S, d u * T u)) +
        2 * m1 * Gc * ρ ^ (5/2 : ℝ)| ≤
      (4 * κ * (|m1| + C5) * K3 + 2 * C5 * K3 + 2 * |m1| * C1) * ρ ^ (5/2 + 1/200 : ℝ) := by
  set R : ℝ := ρ ^ (1/2 - 1/200 : ℝ) with hR
  have hR0 : 0 < R := Real.rpow_pos_of_pos hρ _
  have hR1 : R ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hRe : R ≤ ρ ^ (1/200 : ℝ) := S3_rpow_le hρ hρ1 (by norm_num)
  have hp52 : ρ ^ (5/2 : ℝ) * ρ ^ (1/200 : ℝ) = ρ ^ (5/2 + 1/200 : ℝ) :=
    (Real.rpow_add hρ _ _).symm
  have hp2R : ρ ^ 2 * (R * R) ≤ ρ ^ (5/2 + 1/200 : ℝ) := by
    rw [hR, ← Real.rpow_add hρ, ← Real.rpow_natCast ρ 2, ← Real.rpow_add hρ]
    exact S3_rpow_le hρ hρ1 (by norm_num)
  have hρ52 : 0 ≤ ρ ^ (5/2 : ℝ) := Real.rpow_nonneg hρ.le _
  have hp12 : ρ ^ 2 * ρ ^ (1/2 : ℝ) = ρ ^ (5/2 : ℝ) := S3_pow_52 hρ
  -- the sums
  set Xd := ∑ u ∈ S, d u * T u with hXd
  set Ye := ∑ u ∈ S, Y u * (T u - m1) with hYe
  have hsplit : ∑ u ∈ S, f2 u * T u = Xd - (m1 * (∑ u ∈ S, Y u) + Ye) := by
    have : ∑ u ∈ S, f2 u * T u = ∑ u ∈ S, (d u * T u - (m1 * Y u + Y u * (T u - m1))) :=
      Finset.sum_congr rfl fun u hu => by rw [hf2 u hu]; ring
    rw [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hTb : ∀ u ∈ S, |T u| ≤ |m1| + C5 := fun u hu => by
    have h1 := hT u hu
    have h2 : |T u| ≤ |m1| + |T u - m1| := by
      calc |T u| = |m1 + (T u - m1)| := by ring_nf
        _ ≤ |m1| + |T u - m1| := abs_add_le _ _
    have h3 : C5 * R ≤ C5 * 1 := mul_le_mul_of_nonneg_left hR1 hC5
    linarith
  have hXd : |U * Xd| ≤ (|m1| + C5) * (K3 * R) := by
    have h1 : |Xd| ≤ (|m1| + C5) * ∑ u ∈ S, |d u| := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u hu => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hTb u hu) (abs_nonneg _)
    calc |U * Xd| = U * |Xd| := by rw [abs_mul, abs_of_nonneg hU]
      _ ≤ U * ((|m1| + C5) * ∑ u ∈ S, |d u|) := mul_le_mul_of_nonneg_left h1 hU
      _ = (|m1| + C5) * (U * ∑ u ∈ S, |d u|) := by ring
      _ ≤ (|m1| + C5) * (K3 * R) := mul_le_mul_of_nonneg_left hd (by positivity)
  have hYe : |U * Ye| ≤ C5 * R * (K3 * R) := by
    have h1 : |Ye| ≤ C5 * R * ∑ u ∈ S, |Y u| := by
      rw [Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u hu => ?_)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hT u hu) (abs_nonneg _)
    calc |U * Ye| = U * |Ye| := by rw [abs_mul, abs_of_nonneg hU]
      _ ≤ U * (C5 * R * ∑ u ∈ S, |Y u|) := mul_le_mul_of_nonneg_left h1 hU
      _ = C5 * R * (U * ∑ u ∈ S, |Y u|) := by ring
      _ ≤ C5 * R * (K3 * R) := mul_le_mul_of_nonneg_left hY (by positivity)
  -- the identity
  have hE : 2 * ρ ^ 2 * (U * ∑ u ∈ S, f2 u * T u) - ρ0 ^ 2 * (2 * (U * ∑ u ∈ S, d u * T u)) +
        2 * m1 * Gc * ρ ^ (5/2 : ℝ) =
      2 * (ρ ^ 2 - ρ0 ^ 2) * (U * Xd) - 2 * ρ ^ 2 * (U * Ye) - 2 * m1 * ρ ^ (5/2 : ℝ) * e1 := by
    rw [hsplit]
    have : U * (m1 * ∑ u ∈ S, Y u) = m1 * (U * ∑ u ∈ S, Y u) := by ring
    have e2 : ρ ^ 2 * (m1 * (ρ ^ (1/2 : ℝ) * (Gc + e1))) =
        m1 * ρ ^ (5/2 : ℝ) * (Gc + e1) := by rw [← hp12]; ring
    calc _ = 2 * (ρ ^ 2 - ρ0 ^ 2) * (U * Xd) - 2 * ρ ^ 2 * (m1 * (U * ∑ u ∈ S, Y u)) -
          2 * ρ ^ 2 * (U * Ye) + 2 * m1 * Gc * ρ ^ (5/2 : ℝ) := by ring
      _ = _ := by rw [hA3, mul_assoc 2 (ρ ^ 2), e2]; ring
  rw [hE]
  have b1 : |2 * (ρ ^ 2 - ρ0 ^ 2) * (U * Xd)| ≤
      4 * κ * (|m1| + C5) * K3 * ρ ^ (5/2 + 1/200 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (ρ ^ 2 - ρ0 ^ 2))]
    calc 2 * (ρ ^ 2 - ρ0 ^ 2) * |U * Xd|
        ≤ 2 * (2 * κ * ρ ^ (5/2 : ℝ)) * ((|m1| + C5) * (K3 * R)) :=
          mul_le_mul (by linarith) hXd (abs_nonneg _) (by positivity)
      _ ≤ 2 * (2 * κ * ρ ^ (5/2 : ℝ)) * ((|m1| + C5) * (K3 * ρ ^ (1/200 : ℝ))) := by
          gcongr
      _ = 4 * κ * (|m1| + C5) * K3 * (ρ ^ (5/2 : ℝ) * ρ ^ (1/200 : ℝ)) := by ring
      _ = _ := by rw [hp52]
  have b2 : |2 * ρ ^ 2 * (U * Ye)| ≤ 2 * C5 * K3 * ρ ^ (5/2 + 1/200 : ℝ) := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * ρ ^ 2)]
    calc 2 * ρ ^ 2 * |U * Ye| ≤ 2 * ρ ^ 2 * (C5 * R * (K3 * R)) :=
          mul_le_mul_of_nonneg_left hYe (by positivity)
      _ = 2 * C5 * K3 * (ρ ^ 2 * (R * R)) := by ring
      _ ≤ 2 * C5 * K3 * ρ ^ (5/2 + 1/200 : ℝ) := by gcongr
  have b3 : |2 * m1 * ρ ^ (5/2 : ℝ) * e1| ≤ 2 * |m1| * C1 * ρ ^ (5/2 + 1/200 : ℝ) := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ52, abs_two]
    calc 2 * |m1| * ρ ^ (5/2 : ℝ) * |e1| ≤ 2 * |m1| * ρ ^ (5/2 : ℝ) * (C1 * ρ ^ (1/200 : ℝ)) :=
          mul_le_mul_of_nonneg_left he1 (by positivity)
      _ = 2 * |m1| * C1 * (ρ ^ (5/2 : ℝ) * ρ ^ (1/200 : ℝ)) := by ring
      _ = _ := by rw [hp52]
  have hs1 := abs_le.1 b1
  have hs2 := abs_le.1 b2
  have hs3 := abs_le.1 b3
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith [hs1.1, hs1.2, hs2.1, hs2.2, hs3.1, hs3.2]

/-- (7.66)–(7.68) with (7.67) [temp8.75]: `B + ρ₀²A₁ = −2‖Vw‖₁ g₀^{3/2}π⁻² ρ^{5/2} + O(ρ^{5/2+η})`. -/
theorem Eq7_67 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |2 * rhoN N ^ 2 * (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
                if inPL (rhoN N) (LN N) uv.1 ∧
                    (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
                  (ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
                    lam V w (rhoN N) (LN N) uv.2 *
                    ((rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2 /
                      (1 - (rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2)) else 0)) -
          rho0 (g0 V w) (rhoN N) ^ 2 * (2 * (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
              if inPL (rhoN N) (LN N) uv.1 ∧
                  (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
                (ft V (mom (LN N) (uv.1 - uv.2))).re *
                  (lam V w (rhoN N) (LN N) uv.1 + wmom V w (mom (LN N) uv.1)) *
                  wmom V w (mom (LN N) uv.2) else 0))) +
          2 * normVw V w * Section4.G V w * rhoN N ^ (5/2 : ℝ)|
        ≤ C * rhoN N ^ (5/2 + 1/200 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C1, hC1, N1, h1⟩ := Pair_sum_PL_pot hV hw
  obtain ⟨C5, hC5, N5, h5⟩ := Pair_sum_Vshift_P hV hw
  obtain ⟨K3, hK3, N3, hP⟩ := S3_PL_sums hV hw
  obtain ⟨N4, hmix⟩ := S3_mixed_sum hV hw
  obtain ⟨N7, h7⟩ := eventually_atTop.1
    (S3_ev_small ((3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ)) (b := 1/2) (by norm_num))
  have hκ : 0 ≤ (3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ) := by positivity
  refine ⟨4 * ((3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ)) * (|normVw V w| + C5) * K3 +
      2 * C5 * K3 + 2 * |normVw V w| * C1, by positivity,
    max (max (max N1 N5) (max N3 N4)) (max N7 1), fun N hN => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hN1', hN5'⟩, hN3', hN4'⟩, hN7', hN1b⟩ := hN
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1b
  have hfin := S3_PL_finite hρ hL
  obtain ⟨-, -, hr1, hr2⟩ := S3_rho0 hg.le hρ (by simpa [mul_assoc] using (h7 N hN7'))
  obtain ⟨hd3, -, hY3⟩ := hP N hN3' hfin
  have hL3 : 0 < LN N ^ 3 := by positivity
  set U : ℝ := (LN N ^ 3)⁻¹ with hU
  have hU0 : 0 ≤ U := by positivity
  have hUU : ((LN N ^ 3) ^ 2)⁻¹ = U * U := by rw [hU, sq, mul_inv]
  -- the row sums
  set t : Idx → ℝ := fun u => ∑' v : Idx, (if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
    (ft V (mom (LN N) (u - v))).re * wmom V w (mom (LN N) v) else 0) with ht
  -- the sum `B`
  have hGeq : (fun uv : Idx × Idx => if inPL (rhoN N) (LN N) uv.1 ∧
        (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
      (ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
        lam V w (rhoN N) (LN N) uv.2 *
        ((rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2)) else 0) =
      fun uv : Idx × Idx => if inPL (rhoN N) (LN N) uv.1 ∧
        (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
      (ft V (mom (LN N) (uv.1 - uv.2))).re *
        (-(lam V w (rhoN N) (LN N) uv.1 * ((rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2)))) *
        wmom V w (mom (LN N) uv.2) else 0 := by
    funext uv
    by_cases hc : inPL (rhoN N) (LN N) uv.1 ∧
        (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2)
    · have hn : ¬ inPL (rhoN N) (LN N) uv.2 := by
        intro h
        rcases hc.2 with h' | h'
        · exact Regions_PL_PI h h'
        · exact Regions_PL_PH hρ h h'
      simp only [hc, and_self, ↓reduceIte]
      rw [S3_lam_off V w hn]
      ring
    · simp only [hc, ↓reduceIte]
  obtain ⟨-, hSG⟩ := hmix N hN4' hfin (fun n => -(lam V w (rhoN N) (LN N) n *
    ((rhoN N * lam V w (rhoN N) (LN N) n) ^ 2 / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2))))
  obtain ⟨-, hSS⟩ := hmix N hN4' hfin (fun n => lam V w (rhoN N) (LN N) n +
    wmom V w (mom (LN N) n))
  rw [hGeq, hSG]
  rw [hSS]
  rw [hUU]
  -- the weights
  have hkey := S3_B_alg (hfin.toFinset) (fun n => lam V w (rhoN N) (LN N) n +
    wmom V w (mom (LN N) n))
    (fun n => lam V w (rhoN N) (LN N) n / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) +
      wmom V w (mom (LN N) n))
    (fun n => -(lam V w (rhoN N) (LN N) n *
      ((rhoN N * lam V w (rhoN N) (LN N) n) ^ 2 / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2))))
    (fun n => U * t n) (ρ := rhoN N) (ρ0 := rho0 (g0 V w) (rhoN N))
    (κ := (3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ)) (m1 := normVw V w) (Gc := Section4.G V w) (U := U)
    (C5 := C5) (K3 := K3) (C1 := C1)
    (e1 := (LN N ^ 3)⁻¹ * rhoN N ^ (-(1/2 : ℝ)) * (∑' n : Idx, if inPL (rhoN N) (LN N) n then
        lam V w (rhoN N) (LN N) n / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) +
          wmom V w (mom (LN N) n) else 0) - Section4.G V w)
    hρ hρ1 ?_ ?_ hU0 hC5 hK3 hκ hd3 hY3 ?_ ?_ hr1 hr2
  · -- the main goal
    have hS1 : ∀ f : Idx → ℝ, U * U * ∑ u ∈ hfin.toFinset, f u * t u =
        U * ∑ u ∈ hfin.toFinset, f u * (U * t u) := fun f => by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    rw [hS1, hS1]
    exact hkey
  · -- the weights
    intro u hu
    have hu' : inPL (rhoN N) (LN N) u := hfin.mem_toFinset.1 hu
    have hpos : 0 < ‖mom (LN N) u‖ :=
      lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos hρ _)) hu'.1
    have hx := (S3_lam_PL_div hg hρ hρ1 hu' hpos).1
    have hx' : 1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 ≠ 0 := hx.ne'
    generalize (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 = x at hx'
    generalize lam V w (rhoN N) (LN N) u = l
    field_simp
    ring
  · intro u hu
    exact h5 N hN5' u (hfin.mem_toFinset.1 hu)
  · -- the main sum
    have hz : ∀ n ∉ hfin.toFinset, (if inPL (rhoN N) (LN N) n then
        lam V w (rhoN N) (LN N) n / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) +
          wmom V w (mom (LN N) n) else 0) = 0 := fun n hn => by
      refine ite_eq_right_iff.2 fun h => absurd ?_ hn
      exact hfin.mem_toFinset.2 h
    rw [tsum_eq_sum hz]
    have hs : 0 < rhoN N ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
    have e : rhoN N ^ (1/2 : ℝ) * rhoN N ^ (-(1/2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hρ]; norm_num
    have e2 : ∑ n ∈ hfin.toFinset, (if inPL (rhoN N) (LN N) n then
        lam V w (rhoN N) (LN N) n / (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) +
          wmom V w (mom (LN N) n) else 0) =
        ∑ n ∈ hfin.toFinset, (lam V w (rhoN N) (LN N) n /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) + wmom V w (mom (LN N) n)) :=
      Finset.sum_congr rfl fun n hn => by
        have h' : inPL (rhoN N) (LN N) n := hfin.mem_toFinset.1 hn
        simp only [h', ↓reduceIte]
    rw [e2]
    calc U * ∑ u ∈ hfin.toFinset, (lam V w (rhoN N) (LN N) u /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) + wmom V w (mom (LN N) u))
        = (rhoN N ^ (1/2 : ℝ) * rhoN N ^ (-(1/2 : ℝ))) * (U * ∑ u ∈ hfin.toFinset,
          (lam V w (rhoN N) (LN N) u / (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) +
            wmom V w (mom (LN N) u))) := by rw [e, one_mul]
      _ = _ := by ring
  · exact h1 N hN1'

/-- Lemma 4.4 [lemHS3], (4.11) [proofthem1-4], for `H_{S3}` summed over `u ≠ ±v`. -/
theorem Lemma4_4 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma4_4 V w := by
  obtain ⟨C1, hC1, N1, h1⟩ := Eq7_62 hV hw
  obtain ⟨C2, hC2, N2, h2⟩ := Eq7_65 hV hw
  obtain ⟨C3, hC3, N3, h3⟩ := Eq7_67 hV hw
  let E : ℝ → ℕ → ℝ := fun kc N => if h : N1 ≤ N then (h1 N h kc).choose else 0
  refine ⟨E, fun kc => ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop N1] with N hN
    simp only [E, hN, ↓reduceDIte]
    exact (h1 N hN kc).choose_spec.1
  refine S3_limsup2_le _ (-2 * normVw V w * Section4.G V w) (C1 + C2 + C3) (1/400)
    (by norm_num) (max (max N1 N2) (max N3 1)) (fun kc N hN => ?_)
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN1, hN2⟩, hN3, hN1b⟩ := hN
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1b
  have hEN : E kc N = (h1 N hN1 kc).choose := by simp only [E, hN1, ↓reduceDIte]
  have hI := (h1 N hN1 kc).choose_spec.2
  rw [← hEN] at hI
  have hA := abs_le.1 (h2 N hN2 kc)
  have hB := abs_le.1 (h3 N hN3)
  have hp : 0 < rhoN N ^ (5/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hpq : rhoN N ^ (5/2 + 1/400 : ℝ) = rhoN N ^ (5/2 : ℝ) * rhoN N ^ (1/400 : ℝ) :=
    Real.rpow_add hρ _ _
  have hpq' : rhoN N ^ (5/2 + 1/200 : ℝ) ≤ rhoN N ^ (5/2 : ℝ) * rhoN N ^ (1/400 : ℝ) := by
    rw [← hpq]
    exact S3_rpow_le hρ hρ1 (by norm_num)
  have hC3' : C3 * rhoN N ^ (5/2 + 1/200 : ℝ) ≤
      C3 * (rhoN N ^ (5/2 : ℝ) * rhoN N ^ (1/400 : ℝ)) :=
    mul_le_mul_of_nonneg_left hpq' hC3
  unfold Section4.excess
  rw [div_le_iff₀ hp]
  rw [hpq] at hI hA
  nlinarith [hI, hA.1, hA.2, hB.1, hB.2, hC3']

end LHYUpper
