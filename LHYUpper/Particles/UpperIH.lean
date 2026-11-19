import LHYUpper.Particles.Ratios
import LHYUpper.Riemann.Cells
open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Auxiliary facts: powers of `ε = ρ^η`, thresholds, nonnegative series -/

/-- For `0 < ρ ≤ 1`, `ε = ρ^{1/200}` and `q = ρ^{1/2}`: `0 < ε ≤ 1`, `0 < q ≤ 1`, `ρ = q²` and
`m_c = ε⁻¹`, (3.2) [defepseta], (3.8) [defmc]. -/
private lemma UpperIH_t {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 < epsP ρ ∧ epsP ρ ≤ 1 ∧ 0 < ρ ^ (1 / 2 : ℝ) ∧ ρ ^ (1 / 2 : ℝ) ≤ 1 ∧
      ρ = (ρ ^ (1 / 2 : ℝ)) ^ 2 ∧ mc ρ = (epsP ρ)⁻¹ := by
  refine ⟨Real.rpow_pos_of_pos hρ _, Real.rpow_le_one hρ.le hρ1 (by norm_num),
    Real.rpow_pos_of_pos hρ _, Real.rpow_le_one hρ.le hρ1 (by norm_num), ?_, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  · rw [mc, epsP, Real.rpow_neg hρ.le]

/-- For all large `N`: `N ≥ 1`, `ε ≤ δ`, `2ρ^{1/2} ≤ ε⁴` and `2π ≤ L ρ^{1/2}` at `ρ = ρ_N`,
`L = L_N`. -/
private lemma UpperIH_eventually {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ epsP (rhoN N) ≤ δ ∧
      2 * rhoN N ^ (1 / 2 : ℝ) ≤ epsP (rhoN N) ^ 4 ∧ 2 * π ≤ LN N * rhoN N ^ (1 / 2 : ℝ) := by
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
  have h3 : ∀ᶠ N : ℕ in atTop, rhoN N ^ (12 / 25 : ℝ) ≤ 1 / 2 :=
    (hP (by norm_num : (0 : ℝ) < 12 / 25)).eventually (ge_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop 1, h1, h2, h3] with N hN hε hΔ hq
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  refine ⟨hN, hε, ?_, ?_⟩
  · have e1 : epsP (rhoN N) ^ 4 = rhoN N ^ (1 / 50 : ℝ) := by
      rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      norm_num
    have e2 : rhoN N ^ (1 / 2 : ℝ) = rhoN N ^ (12 / 25 : ℝ) * rhoN N ^ (1 / 50 : ℝ) := by
      rw [← Real.rpow_add hρ]
      norm_num
    rw [e1, e2]
    have hpos : 0 < rhoN N ^ (1 / 50 : ℝ) := Real.rpow_pos_of_pos hρ _
    nlinarith
  have hq : 0 < rhoN N ^ (13 / 24 : ℝ) := Real.rpow_pos_of_pos hρ _
  have e : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) = 1 := by
    rw [LN, mul_assoc, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  by_contra h
  have h' : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) <
      2 * π * rhoN N ^ (13 / 24 : ℝ) := mul_lt_mul_of_pos_right (not_le.1 h) hq
  linarith

/-- `1 ≤ ρ_N² N` for `N ≥ 1`, i.e. `ρ³L³ ≥ 1`. -/
private lemma UpperIH_rho_sq_N {N : ℕ} (hN : 1 ≤ N) : 1 ≤ rhoN N ^ 2 * N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have e : rhoN N ^ 2 * N = (N : ℝ) ^ (1 / 17 : ℝ) := by
    rw [rhoN, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_add_one hN0.ne']
    norm_num
  rw [e]
  exact Real.one_le_rpow hN1 (by norm_num)

/-- `p_{v−u} = p_v − p_u`. -/
private lemma UpperIH_mom_sub (L : ℝ) (v u : Idx) : mom L (v - u) = mom L v - mom L u := by
  ext i
  simp [mom, mul_sub]

/-- A nonnegative sequence with `Σ_m a_m = 1` and `a_{m+1} ≤ c a_m`, `0 ≤ c < 1`, satisfies
`Σ_m m a_m ≤ c/(1 − c)`, the summation in (5.18) [4]. -/
private lemma UpperIH_geom {a : ℕ → ℝ} {c : ℝ} (ha : ∀ m, 0 ≤ a m) (hsum : HasSum a 1)
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hrec : ∀ m, a (m + 1) ≤ c * a m) :
    ∑' m : ℕ, (m : ℝ) * a m ≤ c / (1 - c) := by
  have hpow : ∀ m, a m ≤ c ^ m := by
    intro m
    induction m with
    | zero => simpa using le_hasSum hsum 0 (fun j _ => ha j)
    | succ m ih =>
      calc a (m + 1) ≤ c * a m := hrec m
        _ ≤ c * c ^ m := mul_le_mul_of_nonneg_left ih hc0
        _ = c ^ (m + 1) := by ring
  have hgs : Summable fun m : ℕ => (m : ℝ) * c ^ m := by
    have := summable_pow_mul_geometric_of_norm_lt_one 1 (r := c)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hc0]; exact hc1)
    simpa using this
  have hS : Summable fun m : ℕ => (m : ℝ) * a m :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (Nat.cast_nonneg _) (ha m))
      (fun m => mul_le_mul_of_nonneg_left (hpow m) (Nat.cast_nonneg _)) hgs
  set S := ∑' m : ℕ, (m : ℝ) * a m with hSdef
  have hS1 : Summable fun m : ℕ => ((m + 1 : ℕ) : ℝ) * a (m + 1) :=
    (summable_nat_add_iff 1).2 hS
  have hR : Summable fun m : ℕ => c * ((m : ℝ) * a m + a m) :=
    (hS.add hsum.summable).mul_left c
  have e1 : S = ∑' m : ℕ, ((m + 1 : ℕ) : ℝ) * a (m + 1) := by
    rw [hSdef, hS.tsum_eq_zero_add]
    simp
  have e2 : (∑' m : ℕ, c * ((m : ℝ) * a m + a m)) = c * (S + 1) := by
    rw [tsum_mul_left, hS.tsum_add hsum.summable, hsum.tsum_eq]
  have hle : S ≤ c * (S + 1) := by
    refine (e1.trans_le ?_).trans_eq e2
    refine hS1.tsum_le_tsum (fun m => ?_) hR
    have := hrec m
    have hm : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    calc ((m + 1 : ℕ) : ℝ) * a (m + 1) ≤ ((m + 1 : ℕ) : ℝ) * (c * a m) :=
          mul_le_mul_of_nonneg_left this hm
      _ = c * ((m : ℝ) * a m + a m) := by push_cast; ring
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- `Σ_m Q_Ψ({u, m}) = 1` as a `HasSum`. -/
private lemma UpperIH_hasSum_Qm (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    HasSum (fun m : ℕ => Expect.Qm (trialState V w kc N) [(u, m)]) 1 := by
  have h1 := Expect.tsum_Qm_single N _ (Normalization_isNState V w kc hN) u
  have hsm : Summable fun m : ℕ => Expect.Qm (trialState V w kc N) [(u, m)] := by
    by_contra hc
    rw [tsum_eq_zero_of_not_summable hc] at h1
    norm_num at h1
  rw [← h1]
  exact hsm.hasSum

/-- `Q_Ψ` of an event is nonnegative. -/
private lemma UpperIH_Qm_nonneg (Ψ : Occ → ℂ) (um : List (Idx × ℕ)) : 0 ≤ Expect.Qm Ψ um :=
  tsum_nonneg fun _ => by split_ifs <;> positivity

/-- `ρ ≤ ε⁴` when `2ρ^{1/2} ≤ ε⁴` and `0 < ρ ≤ 1`. -/
private lemma UpperIH_rho_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (h : 2 * ρ ^ (1 / 2 : ℝ) ≤ epsP ρ ^ 4) : ρ ≤ epsP ρ ^ 4 := by
  obtain ⟨-, -, hq0, hq1, hρq, -⟩ := UpperIH_t hρ hρ1
  have h1 : (ρ ^ (1 / 2 : ℝ)) ^ 2 ≤ ρ ^ (1 / 2 : ℝ) := by nlinarith
  linarith

/-- On `P_H`, `C ρ²|λ_u| ε⁻² ≤ 1/2` for all large `N`, uniformly in `u`. -/
private lemma UpperIH_PH_small (V w : R3 → ℝ) {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ ∀ u : Idx, inPH (rhoN N) (LN N) u →
      C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / epsP (rhoN N) ^ 2 ≤ 1 / 2 := by
  set g₁ := ∫ x, |gfun V w x| with hg₁
  have hg0 : 0 ≤ g₁ := integral_nonneg fun _ => abs_nonneg _
  have hδ : 0 < 1 / (2 * (C * g₁ + 1)) := by positivity
  filter_upwards [UpperIH_eventually hδ] with N hN'
  obtain ⟨hN, hε, hq4, -⟩ := hN'
  refine ⟨hN, fun u hu => ?_⟩
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  obtain ⟨ht0, ht1, -, -, -, -⟩ := UpperIH_t hρ hρ1
  have hρ4 := UpperIH_rho_le hρ hρ1 hq4
  have hnu : epsP (rhoN N) < ‖mom (LN N) u‖ := hu
  have hlu := Particles_lam_abs_le V w (rhoN N) (LN N) u (fun h => Regions_PL_PH hρ h hu)
  set t := epsP (rhoN N) with ht
  set ρ := rhoN N with hρdef
  set l := |lam V w ρ (LN N) u| with hl
  have hl0 : 0 ≤ l := abs_nonneg _
  have hnu0 : 0 < ‖mom (LN N) u‖ := ht0.trans hnu
  have ht2 : t ^ 2 ≤ ‖mom (LN N) u‖ ^ 2 := pow_le_pow_left₀ ht0.le hnu.le 2
  have hlt : l * t ^ 2 ≤ g₁ := by
    have h1 : l * ‖mom (LN N) u‖ ^ 2 ≤ g₁ := by
      rw [le_div_iff₀ (by positivity)] at hlu
      exact hlu
    exact (mul_le_mul_of_nonneg_left ht2 hl0).trans h1
  have ht4 : t ^ 4 ≤ t := pow_le_of_le_one ht0.le ht1 (by norm_num)
  have hρt : ρ ≤ t := hρ4.trans ht4
  have hCρ : C * g₁ * ρ ≤ 1 / 2 := by
    have h1 : t ≤ 1 / (2 * (C * g₁ + 1)) := hε
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : C * g₁ * ρ ≤ (C * g₁ + 1) * t :=
      mul_le_mul (by linarith) hρt hρ.le (by positivity)
    linarith
  have hρl : ρ * l ≤ t ^ 2 * g₁ := by
    calc ρ * l ≤ t ^ 4 * l := mul_le_mul_of_nonneg_right hρ4 hl0
      _ = t ^ 2 * (l * t ^ 2) := by ring
      _ ≤ t ^ 2 * g₁ := mul_le_mul_of_nonneg_left hlt (by positivity)
  have hs : 0 ≤ t ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity)]
  calc C * ρ ^ 2 * l = C * ρ * (ρ * l) := by ring
    _ ≤ C * ρ * (t ^ 2 * g₁) := mul_le_mul_of_nonneg_left hρl (by positivity)
    _ = C * g₁ * ρ * t ^ 2 := by ring
    _ ≤ 1 / 2 * t ^ 2 := mul_le_mul_of_nonneg_right hCρ hs

/-- The numerical step behind the soft term of (5.28) [temp6.29]:
`4ρ c D K R³ ≤ 8 K D ρ²` for `ρ = q²`, `R = q/ε`, `q ≤ ε⁴`, `cε ≤ 2`. -/
private lemma UpperIH_alg {t q ρ R K D c : ℝ} (ht0 : 0 < t) (hq0 : 0 ≤ q) (hρ : ρ = q ^ 2)
    (hR : R = q / t) (hq : q ≤ t ^ 4) (hK : 0 ≤ K) (hD : 0 ≤ D) (hc : c * t ≤ 2) :
    4 * ρ * c * D * (K * R ^ 3) ≤ 8 * K * D * ρ ^ 2 := by
  rw [hρ, hR]
  have ht4 : 0 < t ^ 4 := by positivity
  have h2 : 0 ≤ 4 * D * K := by positivity
  have h3 : 0 ≤ q ^ 5 / t ^ 4 := by positivity
  have h1 : q ^ 5 / t ^ 4 ≤ q ^ 4 := by
    rw [div_le_iff₀ ht4]
    calc q ^ 5 = q ^ 4 * q := by ring
      _ ≤ q ^ 4 * t ^ 4 := mul_le_mul_of_nonneg_left hq (by positivity)
  calc 4 * q ^ 2 * c * D * (K * (q / t) ^ 3) = 4 * D * K * (c * t) * (q ^ 5 / t ^ 4) := by
        field_simp
    _ ≤ 4 * D * K * 2 * (q ^ 5 / t ^ 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc h2) h3
    _ ≤ 4 * D * K * 2 * q ^ 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 8 * K * D * (q ^ 2) ^ 2 := by ring

/-- A function on `Idx` supported in `{|p_n| ≤ R}` is summable. -/
private lemma UpperIH_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
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

/-- The exact coefficient of (5.27) [4.1] is at most `C ρ²|λ_u| |u|⁻²` on `P_H`, for all
large `N`, uniformly in `k_c` and `u`: the bound (5.28) [temp6.29] on the coefficient. -/
private lemma UpperIH_coeff (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ ∀ kc : ℝ, ∀ u : Idx,
      inPH (rhoN N) (LN N) u →
      (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 +
        4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 *
          (∑' v : Idx, (if inPL (rhoN N) (LN N) v ∧ inPHc (rhoN N) (LN N) kc (v - u) then
            |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (v - u)| else 0)) ≤
        C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 := by
  obtain ⟨K, hK, hKb⟩ := sum_norm_rpow_le (s := 0) (by norm_num)
  simp only [neg_zero, Real.rpow_zero, sub_zero] at hKb
  set g₁ := ∫ x, |gfun V w x| with hg₁
  have hg0 : 0 ≤ g₁ := integral_nonneg fun _ => abs_nonneg _
  refine ⟨g₁ + 32 * K * g₁, by positivity, ?_⟩
  filter_upwards [UpperIH_eventually (by norm_num : (0 : ℝ) < 1 / 2)] with N hN'
  obtain ⟨hN, -, hq4, hLρ⟩ := hN'
  refine ⟨hN, fun kc u hu => ?_⟩
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN
  obtain ⟨ht0, ht1, hq0, -, hρq, hmc⟩ := UpperIH_t hρ hρ1
  have hnu : epsP (rhoN N) < ‖mom (LN N) u‖ := hu
  have hlu := Particles_lam_abs_le V w (rhoN N) (LN N) u (fun h => Regions_PL_PH hρ h hu)
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set t := epsP ρ with htdef
  set lu := lam V w ρ L u with hludef
  set nu := ‖mom L u‖ with hnudef
  have hnu0 : 0 < nu := ht0.trans hnu
  set q := ρ ^ (1 / 2 : ℝ) with hqdef
  set R := t⁻¹ * q with hRdef
  have hR : R = q / t := by rw [hRdef]; ring
  have hR0 : 0 < R := by rw [hR]; positivity
  have hq : q ≤ t ^ 4 := by linarith
  have hRt : R ≤ t / 2 := by
    have h42 : t ^ 4 ≤ t ^ 2 := pow_le_pow_of_le_one ht0.le ht1 (by norm_num)
    rw [hR, div_le_iff₀ ht0]
    calc q ≤ t ^ 2 / 2 := by linarith
      _ = t / 2 * t := by ring
  have hLR : 2 * π ≤ L * R := by
    have h1 : 1 ≤ t⁻¹ := (one_le_inv₀ ht0).2 ht1
    have h2 : 0 ≤ L * q := by positivity
    calc 2 * π ≤ L * q := hLρ
      _ ≤ t⁻¹ * (L * q) := le_mul_of_one_le_left h2 h1
      _ = L * R := by rw [hRdef]; ring
  set D := |lu| * (4 * g₁ / nu ^ 2) with hDdef
  have hD0 : 0 ≤ D := by positivity
  set T : Idx → ℝ := fun n => if n ≠ 0 ∧ ‖mom L n‖ ≤ R then 1 else 0 with hTdef
  have hT0 : ∀ n, 0 ≤ T n := fun n => by simp only [hTdef]; split_ifs <;> norm_num
  have hTs : Summable T := UpperIH_summable_ball hL T (fun n hn => by
    simp only [hTdef] at hn
    split_ifs at hn with h
    · exact h.2
    · exact absurd rfl hn)
  have hTK : (∑' n, T n) ≤ L ^ 3 * (K * R ^ 3) := by
    have := hKb L R hR0 hLR
    rw [← inv_mul_le_iff₀ (by positivity)]
    simpa [hTdef] using this
  -- each soft term is at most `D` times the indicator of `{0 < |v| ≤ R}`
  have hpt : ∀ v : Idx, (if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
      |lu * lam V w ρ L (v - u)| else 0) ≤ T v * D := by
    intro v
    split_ifs with h
    · have hv0 : v ≠ 0 := Regions_PL_ne_zero hρ h.1
      have hvR : ‖mom L v‖ ≤ R := h.1.2
      have hTv : T v = 1 := by simp only [hTdef]; rw [ite_eq_left ⟨hv0, hvR⟩]
      rw [hTv, one_mul, abs_mul, hDdef]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      have hl2 := Particles_lam_abs_le V w ρ L (v - u) (fun h' => Regions_PL_PH hρ h' h.2.1)
      have hdist : nu / 2 ≤ ‖mom L (v - u)‖ := by
        rw [UpperIH_mom_sub]
        have := norm_sub_norm_le (mom L u) (mom L v)
        rw [norm_sub_rev] at this
        linarith
      have hd2 : (nu / 2) ^ 2 ≤ ‖mom L (v - u)‖ ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdist 2
      refine hl2.trans ?_
      calc g₁ / ‖mom L (v - u)‖ ^ 2 ≤ g₁ / (nu / 2) ^ 2 :=
            div_le_div_of_nonneg_left hg0 (by positivity) hd2
        _ = 4 * g₁ / nu ^ 2 := by field_simp; ring
    · exact mul_nonneg (hT0 v) hD0
  have hSs : Summable fun v : Idx => (if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
      |lu * lam V w ρ L (v - u)| else 0) :=
    Summable.of_nonneg_of_le (fun v => by split_ifs <;> positivity) hpt (hTs.mul_right D)
  have hS : (∑' v : Idx, (if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
      |lu * lam V w ρ L (v - u)| else 0)) ≤ (∑' n, T n) * D := by
    rw [← tsum_mul_right]
    exact hSs.tsum_le_tsum hpt (hTs.mul_right D)
  have hceil : (⌈mc ρ⌉₊ : ℝ) * t ≤ 2 := by
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ mc ρ by rw [hmc]; positivity)
    rw [hmc] at h1
    have h2 : ((⌈t⁻¹⌉₊ : ℕ) : ℝ) * t ≤ (t⁻¹ + 1) * t :=
      mul_le_mul_of_nonneg_right h1.le ht0.le
    rw [add_mul, inv_mul_cancel₀ ht0.ne'] at h2
    rw [hmc]
    linarith
  have hsoft : 4 * ρ * ⌈mc ρ⌉₊ / L ^ 3 *
      (∑' v : Idx, (if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
        |lu * lam V w ρ L (v - u)| else 0)) ≤ 32 * K * g₁ * ρ ^ 2 * |lu| / nu ^ 2 := by
    have hc0 : 0 ≤ 4 * ρ * ⌈mc ρ⌉₊ / L ^ 3 := by positivity
    calc 4 * ρ * ⌈mc ρ⌉₊ / L ^ 3 *
          (∑' v : Idx, (if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
            |lu * lam V w ρ L (v - u)| else 0))
        ≤ 4 * ρ * ⌈mc ρ⌉₊ / L ^ 3 * ((∑' n, T n) * D) := mul_le_mul_of_nonneg_left hS hc0
      _ ≤ 4 * ρ * ⌈mc ρ⌉₊ / L ^ 3 * ((L ^ 3 * (K * R ^ 3)) * D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hTK hD0) hc0
      _ = 4 * ρ * ⌈mc ρ⌉₊ * D * (K * R ^ 3) := by field_simp
      _ ≤ 8 * K * D * ρ ^ 2 := UpperIH_alg ht0 hq0.le hρq hR hq hK hD0 hceil
      _ = 32 * K * g₁ * ρ ^ 2 * |lu| / nu ^ 2 := by rw [hDdef]; ring
  have hx : (ρ * lu) ^ 2 ≤ g₁ * ρ ^ 2 * |lu| / nu ^ 2 := by
    have h1 : (ρ * lu) ^ 2 = ρ ^ 2 * |lu| * |lu| := by rw [mul_pow, ← sq_abs lu]; ring
    rw [h1]
    calc ρ ^ 2 * |lu| * |lu| ≤ ρ ^ 2 * |lu| * (g₁ / nu ^ 2) :=
          mul_le_mul_of_nonneg_left hlu (by positivity)
      _ = g₁ * ρ ^ 2 * |lu| / nu ^ 2 := by ring
  calc (ρ * lu) ^ 2 + 4 * ρ * ⌈mc ρ⌉₊ / L ^ 3 *
        (∑' v : Idx, (if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
          |lu * lam V w ρ L (v - u)| else 0))
      ≤ g₁ * ρ ^ 2 * |lu| / nu ^ 2 + 32 * K * g₁ * ρ ^ 2 * |lu| / nu ^ 2 := add_le_add hx hsoft
    _ = (g₁ + 32 * K * g₁) * ρ ^ 2 * |lu| / nu ^ 2 := by ring

/-! ### Configurations, weights of pair creations, coverings -/

/-- A single occupation number is at most the particle number. -/
private lemma UpperIH_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]; exact Nat.zero_le _

/-- On `M`, `α(n)/|Λ| ≤ ρ`. -/
private lemma UpperIH_occ_div_le {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {α : Occ}
    (hα : InM (rhoN N) (LN N) kc N α) (n : Idx) : (α n : ℝ) / LN N ^ 3 ≤ rhoN N := by
  obtain ⟨hNL, hρ, -, hL⟩ := Particles_rhoN_LN hN
  rw [div_le_iff₀ (by positivity), hNL]
  have h := (UpperIH_occ_le_num α n).trans (MBasic_num hρ hα).le
  exact_mod_cast h

/-- A restriction of a nonnegative summable family is summable. -/
private lemma UpperIH_summable_ite {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (p : Occ → Prop) [DecidablePred p] : Summable fun α => if p α then ψ α else 0 :=
  Summable.of_nonneg_of_le (fun α => by split_ifs <;> simp [hψ α])
    (fun α => by split_ifs <;> simp [hψ α]) hs

/-- Covering bound: if every `α` with `F(α) ≠ 0` is `back j` for some `j` with
`F(α) ≤ G(j)`, then `Σ_α F(α) ≤ Σ_j G(j)`. -/
private lemma UpperIH_cover {ι : Type*} (F : Occ → ℝ) (G : ι → ℝ) (hF : ∀ α, 0 ≤ F α)
    (hG : ∀ j, 0 ≤ G j) (hGs : Summable G) (back : ι → Occ)
    (h : ∀ α, F α ≠ 0 → ∃ j, back j = α ∧ F α ≤ G j) : (∑' α, F α) ≤ ∑' j, G j := by
  let φ : Function.support F → ι := fun x => (h x.1 x.2).choose
  have hφ1 : ∀ x, back (φ x) = x.1 := fun x => (h x.1 x.2).choose_spec.1
  have hφ2 : ∀ x, F x.1 ≤ G (φ x) := fun x => (h x.1 x.2).choose_spec.2
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    rw [← hφ1 x, ← hφ1 y, hxy]
  have hGc : Summable (G ∘ φ) := hGs.comp_injective hinj
  have hFs : Summable (fun x : Function.support F => F x.1) :=
    Summable.of_nonneg_of_le (fun x => hF x.1) hφ2 hGc
  rw [← tsum_subtype_eq_of_support_subset (s := Function.support F) subset_rfl]
  calc (∑' x : Function.support F, F x.1) ≤ ∑' x : Function.support F, G (φ x) :=
        hFs.tsum_le_tsum hφ2 hGc
    _ ≤ ∑' j, G j := tsum_comp_le_tsum_of_inj hGs hG hinj

/-- `Ψ` vanishes off `M`. -/
private lemma UpperIH_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  rw [FIdentities_trialState, ite_eq_right hc, norm_zero]
  norm_num

/-- `|Ψ(α)|² = |z|²|Ψ(β)|²` when `f(α) = z f(β)` on `M`, (3.18) [deffal]. -/
private lemma UpperIH_normsq (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {α β : Occ}
    (hα : InM (rhoN N) (LN N) kc N α) (hβ : InM (rhoN N) (LN N) kc N β) (z : ℂ)
    (h : f0 V w (rhoN N) (LN N) α = z * f0 V w (rhoN N) (LN N) β) :
    ‖trialState V w kc N α‖ ^ 2 = ‖z‖ ^ 2 * ‖trialState V w kc N β‖ ^ 2 := by
  rw [FIdentities_trialState, FIdentities_trialState, ite_eq_left hα, ite_eq_left hβ, h]
  simp only [norm_mul]
  ring

/-- `|√x|² = |x|` for the square root of Definition 3.6. -/
private lemma UpperIH_norm_csqrt_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h, abs_of_nonneg h]
  · have h' : x < 0 := not_le.1 h
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by linarith), abs_of_neg h']

/-- `|Ψ(𝓐^k β)|² = β(0)(β(0) − 1)|Λ|⁻²λ_k²|Ψ(β)|²`, from (5.4) [properf1]. -/
private lemma UpperIH_strict_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} {k : Idx} {β : Occ}
    (hβ : InM (rhoN N) (LN N) kc N β) (hα : InM (rhoN N) (LN N) kc N (strictPair k β))
    (h1 : 1 ≤ β 0)
    (hf : f0 V w (rhoN N) (LN N) (strictPair k β) =
      ((Real.sqrt ((β 0 : ℝ) / LN N ^ 3) * Real.sqrt (((β 0 : ℝ) - 1) / LN N ^ 3) *
        lam V w (rhoN N) (LN N) k : ℝ) : ℂ) * f0 V w (rhoN N) (LN N) β)
    (hL : 0 < LN N) :
    ‖trialState V w kc N (strictPair k β)‖ ^ 2 =
      (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) * lam V w (rhoN N) (LN N) k ^ 2 *
        ‖trialState V w kc N β‖ ^ 2 := by
  have h1' : (1 : ℝ) ≤ β 0 := by exact_mod_cast h1
  rw [UpperIH_normsq V w kc N hα hβ _ hf, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (div_nonneg (by linarith) (by positivity))]

/-- `|Ψ(𝓐^{w;p₁,p₂} β)|² = 4β(0)β(w)|Λ|⁻²|λ_{p₁}λ_{p₂}||Ψ(β)|²`, from (5.7) [properf4]. -/
private lemma UpperIH_soft_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {p p₁ p₂ : Idx}
    {β : Occ} (hp : inPL (rhoN N) (LN N) p) (h₁ : inPH (rhoN N) (LN N) p₁)
    (h₂ : inPH (rhoN N) (LN N) p₂) (hs : p₁ + p₂ = p) (hβ : InMuS (rhoN N) (LN N) kc N p β)
    (hα : InM (rhoN N) (LN N) kc N (softPair p p₁ p₂ β)) :
    ‖trialState V w kc N (softPair p p₁ p₂ β)‖ ^ 2 =
      4 * ((β 0 : ℝ) / LN N ^ 3) * ((β p : ℝ) / LN N ^ 3) *
        |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| *
          ‖trialState V w kc N β‖ ^ 2 := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hf := Lemma5_1_properf4 (V := V) (w := w) hρ hL hp h₁ h₂ hs hβ hα
  rw [UpperIH_normsq V w kc N hα hβ.1 _ hf, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), UpperIH_norm_csqrt_sq,
    UpperIH_norm_csqrt_sq, abs_mul]
  ring

/-- `β(0)(β(0) − 1)|Λ|⁻²λ² ≤ (ρλ)²` on `M`. -/
private lemma UpperIH_strict_le {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {β : Occ}
    (hβ : InM (rhoN N) (LN N) kc N β) (h1 : 1 ≤ β 0) (l : ℝ) :
    (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) * l ^ 2 ≤ (rhoN N * l) ^ 2 := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have h1' : (1 : ℝ) ≤ β 0 := by exact_mod_cast h1
  have ha := UpperIH_occ_div_le hN hβ 0
  have hb : ((β 0 : ℝ) - 1) / LN N ^ 3 ≤ (β 0 : ℝ) / LN N ^ 3 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hb0 : 0 ≤ ((β 0 : ℝ) - 1) / LN N ^ 3 := div_nonneg (by linarith) (by positivity)
  rw [mul_pow]
  have : (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) ≤ rhoN N ^ 2 := by
    rw [sq]
    exact mul_le_mul ha (hb.trans ha) hb0 hρ.le
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- `Q_Ψ({u, m}, {v, n})` as a restricted sum. -/
private lemma UpperIH_Qm_pair (Ψ : Occ → ℂ) (u v : Idx) (m n : ℕ) :
    Expect.Qm Ψ [(u, m), (v, n)] =
      ∑' α : Occ, if α u = m ∧ α v = n then ‖Ψ α‖ ^ 2 else 0 := by
  simp [Expect.Qm, Expect.Ev]

/-- `Q_Ψ({u, m})` as a restricted sum. -/
private lemma UpperIH_Qm_single (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) :
    Expect.Qm Ψ [(u, m)] = ∑' α : Occ, if α u = m then ‖Ψ α‖ ^ 2 else 0 := by
  simp [Expect.Qm, Expect.Ev]

/-- `⌈m_c⌉ ε ≤ 2` for `0 < ρ ≤ 1`, (3.8) [defmc]. -/
private lemma UpperIH_ceil {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (⌈mc ρ⌉₊ : ℝ) * epsP ρ ≤ 2 := by
  obtain ⟨ht0, ht1, -, -, -, hmc⟩ := UpperIH_t hρ hρ1
  have h1 := Nat.ceil_lt_add_one (show 0 ≤ mc ρ by rw [hmc]; positivity)
  rw [hmc] at h1
  have h2 : ((⌈(epsP ρ)⁻¹⌉₊ : ℕ) : ℝ) * epsP ρ ≤ ((epsP ρ)⁻¹ + 1) * epsP ρ :=
    mul_le_mul_of_nonneg_right h1.le ht0.le
  rw [add_mul, inv_mul_cancel₀ ht0.ne'] at h2
  rw [hmc]
  linarith

/-- The two-index recursion for (5.41) [boundpsiuvmn]: for `u, v ∈ P_H` with `u ≠ ±v`,
removing one particle of momentum `u` by Proposition 5.3 [prop2] gives
`Q_Ψ({u, m+1}, {v, n}) ≤ c_u Q_Ψ({u, m}, {v, n}) + 4ρ⌈m_c⌉|Λ|⁻¹|λ_uλ_v| Q_Ψ({u, m}, {v, n−1})`,
with `c_u` the coefficient of (5.27) [4.1]; the second term is the soft creation from
`u + v ∈ P_L` whose second momentum is `v`. -/
private lemma UpperIH_step2 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : inPH (rhoN N) (LN N) u) (hv : inPH (rhoN N) (LN N) v) (huv : u ≠ v)
    (hsum : u + v ≠ 0) (m n : ℕ) :
    Expect.Qm (trialState V w kc N) [(u, m + 1), (v, n)] ≤
      ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 +
        4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 *
          (∑' p : Idx, (if inPL (rhoN N) (LN N) p ∧ inPHc (rhoN N) (LN N) kc (p - u) then
            |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)| else 0))) *
        Expect.Qm (trialState V w kc N) [(u, m), (v, n)] +
      4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 *
        |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| *
        (∑' β : Occ, if β u = m ∧ β v + 1 = n then ‖trialState V w kc N β‖ ^ 2 else 0) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  have hs0 : ∀ α, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  have hv0 : v ≠ 0 := Regions_PH_ne_zero hρ hv
  have hvnu : v ≠ -u := fun h => hsum (by rw [h]; abel)
  set x := (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 with hx
  set κ := 4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set luv := |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| with hluv
  set S : Occ → ℝ := fun β => if β u = m ∧ β v = n then ‖trialState V w kc N β‖ ^ 2 else 0
    with hS
  set S' : Occ → ℝ := fun β => if β u = m ∧ β v + 1 = n then
    ‖trialState V w kc N β‖ ^ 2 else 0 with hS'
  set A : Idx → ℝ := fun p => if inPL (rhoN N) (LN N) p ∧ inPHc (rhoN N) (LN N) kc (p - u) then
    |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)| else 0 with hA
  set B : Idx → ℝ := fun p => if p = v + u then luv else 0 with hB
  have hS0 : ∀ β, 0 ≤ S β := fun β => by simp only [hS]; split_ifs <;> simp [hs0]
  have hS'0 : ∀ β, 0 ≤ S' β := fun β => by simp only [hS']; split_ifs <;> simp [hs0]
  have hA0 : ∀ p, 0 ≤ A p := fun p => by simp only [hA]; split_ifs <;> positivity
  have hB0 : ∀ p, 0 ≤ B p := fun p => by simp only [hB]; split_ifs <;> positivity
  have hSs : Summable S := UpperIH_summable_ite hs hs0 _
  have hS's : Summable S' := UpperIH_summable_ite hs hs0 _
  have hAs : Summable A := UpperIH_summable_ball (R := (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ))
    hL A (fun p hp => by
      simp only [hA] at hp
      split_ifs at hp with h
      · exact h.1.2
      · exact absurd rfl hp)
  have hBs : Summable B := summable_of_ne_finset_zero (s := {v + u}) fun p hp => by
    simp only [hB]
    exact ite_eq_right (by simpa using hp)
  have hBsum : (∑' p, B p) = luv := by
    rw [tsum_eq_single (v + u) fun p hp => by simp only [hB]; exact ite_eq_right hp]
    simp [hB]
  set g₁ : Occ → ℝ := fun β => x * S β with hg₁
  set g₂ : Occ × Idx → ℝ := fun j => κ * (S j.1 * A j.2 + S' j.1 * B j.2) with hg₂
  have hSA : Summable fun j : Occ × Idx => S j.1 * A j.2 := hSs.mul_of_nonneg hAs hS0 hA0
  have hSB : Summable fun j : Occ × Idx => S' j.1 * B j.2 := hS's.mul_of_nonneg hBs hS'0 hB0
  have hg₁s : Summable g₁ := hSs.mul_left x
  have hg₂s : Summable g₂ := (hSA.add hSB).mul_left κ
  have hGs : Summable (Sum.elim g₁ g₂) := Summable.sum (Sum.elim g₁ g₂) hg₁s hg₂s
  have hG0 : ∀ j, 0 ≤ Sum.elim g₁ g₂ j := by
    rintro (β | j)
    · exact mul_nonneg (sq_nonneg _) (hS0 β)
    · exact mul_nonneg hκ0 (add_nonneg (mul_nonneg (hS0 _) (hA0 _)) (mul_nonneg (hS'0 _) (hB0 _)))
  have hGsum : (∑' j, Sum.elim g₁ g₂ j) =
      (x + κ * ∑' p, A p) * (∑' β, S β) + κ * luv * ∑' β, S' β := by
    rw [Summable.tsum_sum (f := Sum.elim g₁ g₂) hg₁s hg₂s]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hg₁, hg₂, tsum_mul_left, tsum_mul_left, (hSA.tsum_add hSB),
      ← hSs.tsum_mul_tsum hAs hSA, ← hS's.tsum_mul_tsum hBs hSB, hBsum]
    ring
  rw [UpperIH_Qm_pair, UpperIH_Qm_pair]
  refine (UpperIH_cover _ (Sum.elim g₁ g₂) (fun α => by split_ifs <;> simp [hs0]) hG0 hGs
    (Sum.elim (strictPair u) (fun j => softPair j.2 u (j.2 - u) j.1)) ?_).trans_eq hGsum
  intro α hα
  have hc : α u = m + 1 ∧ α v = n := by
    by_contra h
    exact hα (ite_eq_right h)
  have hψ : ‖trialState V w kc N α‖ ^ 2 ≠ 0 := by
    intro h
    exact hα (by simp [h])
  have hαM := UpperIH_inM hψ
  rw [ite_eq_left hc]
  rcases Prop5_3 hρ hu hαM (by omega) with ⟨β, hβ, h2, he, hval⟩ |
    ⟨p, β, hp, hβS, hb0, hbp, hcu, hcpu, he, hval⟩
  · refine ⟨Sum.inl β, he, ?_⟩
    have e := MBasic_strictPair_apply u β v
    rw [he] at e
    simp only [hv0, Ne.symm huv, hvnu, ite_false] at e
    have hβv : β v = n := by omega
    have hβu : β u = m := by omega
    simp only [Sum.elim_inl, hg₁, hS]
    rw [ite_eq_left ⟨hβu, hβv⟩]
    subst he
    have hf := Lemma5_1_properf1 (V := V) (w := w) hρ hL (Or.inr hu) hβ hαM
    rw [UpperIH_strict_eq V w kc hβ hαM (by omega) hf hL]
    exact mul_le_mul_of_nonneg_right (UpperIH_strict_le hN hβ (by omega) _) (hs0 _)
  · refine ⟨Sum.inr (β, p), he, ?_⟩
    have hvp : v ≠ p := fun h => Regions_PL_PH hρ hp (h ▸ hv)
    have e := MBasic_softPair_apply p u (p - u) β v
    rw [he] at e
    simp only [hv0, hvp, Ne.symm huv, ite_false] at e
    have hβu : β u = m := by omega
    have hsq : u + (p - u) = p := by abel
    have hbp' : (β p : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := by
      have := (le_max_left (β p) (β (-p))).trans (MStar_PL_ceil hρ hβS.1 hp)
      exact_mod_cast this
    simp only [Sum.elim_inr, hg₂]
    subst he
    rw [UpperIH_soft_eq V w kc hN hp hcu.1 hcpu.1 hsq hβS hαM]
    have hL3 : 0 < LN N ^ 3 := by positivity
    have hb0' : 0 ≤ (β 0 : ℝ) / LN N ^ 3 := by positivity
    have hsoft : 4 * ((β 0 : ℝ) / LN N ^ 3) * ((β p : ℝ) / LN N ^ 3) *
        |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)| *
          ‖trialState V w kc N β‖ ^ 2 ≤
        κ * (‖trialState V w kc N β‖ ^ 2 *
          |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)|) := by
      have hxy : (β 0 : ℝ) / LN N ^ 3 * (β p : ℝ) ≤ rhoN N * ⌈mc (rhoN N)⌉₊ :=
        mul_le_mul (UpperIH_occ_div_le hN hβS.1 0) hbp' (by positivity) hρ.le
      have e1 : 4 * ((β 0 : ℝ) / LN N ^ 3) * ((β p : ℝ) / LN N ^ 3) *
          |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)| *
            ‖trialState V w kc N β‖ ^ 2 =
          ((β 0 : ℝ) / LN N ^ 3 * (β p : ℝ)) * (4 / LN N ^ 3 *
            (‖trialState V w kc N β‖ ^ 2 *
              |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)|)) := by ring
      have e2 : κ * (‖trialState V w kc N β‖ ^ 2 *
          |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)|) =
          (rhoN N * ⌈mc (rhoN N)⌉₊) * (4 / LN N ^ 3 *
            (‖trialState V w kc N β‖ ^ 2 *
              |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)|)) := by
        rw [hκ]; ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right hxy (by positivity)
    refine hsoft.trans (mul_le_mul_of_nonneg_left ?_ hκ0)
    by_cases hvpu : v = p - u
    · rw [ite_eq_left hvpu] at e
      have hβv : β v + 1 = n := by omega
      have hpv : p = v + u := by rw [hvpu]; abel
      have h1 : S' β * B p = ‖trialState V w kc N β‖ ^ 2 *
          |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)| := by
        simp only [hS', hB]
        rw [ite_eq_left ⟨hβu, hβv⟩, ite_eq_left hpv, hluv, ← hvpu]
      rw [h1]
      exact le_add_of_nonneg_left (mul_nonneg (hS0 _) (hA0 _))
    · rw [ite_eq_right hvpu] at e
      have hβv : β v = n := by omega
      have h1 : S β * A p = ‖trialState V w kc N β‖ ^ 2 *
          |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (p - u)| := by
        simp only [hS, hA]
        rw [ite_eq_left ⟨hβu, hβv⟩, ite_eq_left ⟨hp, hcpu⟩]
      rw [h1]
      exact le_add_of_nonneg_right (mul_nonneg (hS'0 _) (hB0 _))

/-- `Q_Ψ(u, v) ≤ Σ_{m,n} m n b_{m,n}` whenever `Q_Ψ({u, m}, {v, n}) ≤ b_{m,n}` and the
right side converges: the fibres of `α ↦ (α(u), α(v))` in Definition 5.1 [1]. -/
private lemma UpperIH_Q2_le (Ψ : Occ → ℂ) (hs : Summable fun α => ‖Ψ α‖ ^ 2) (u v : Idx)
    (b : ℕ → ℕ → ℝ) (hb : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * p.2 * b p.1 p.2)
    (hab : ∀ m n, Expect.Qm Ψ [(u, m), (v, n)] ≤ b m n) :
    Expect.Q Ψ [u, v] ≤ ∑' p : ℕ × ℕ, (p.1 : ℝ) * p.2 * b p.1 p.2 := by
  have hb0 : ∀ m n, 0 ≤ b m n := fun m n => (UpperIH_Qm_nonneg _ _).trans (hab m n)
  have hQ : Expect.Q Ψ [u, v] = ∑' α : Occ, (α u : ℝ) * α v * ‖Ψ α‖ ^ 2 := by
    simp [Expect.Q, mul_assoc]
  set F : Occ → ℝ := fun α => (α u : ℝ) * α v * ‖Ψ α‖ ^ 2 with hF
  by_cases hFs : Summable F
  swap
  · rw [hQ, tsum_eq_zero_of_not_summable hFs]
    exact tsum_nonneg fun p => mul_nonneg (by positivity) (hb0 p.1 p.2)
  let key : Occ → ℕ × ℕ := fun α => (α u, α v)
  let e := Equiv.sigmaFiberEquiv key
  have hfib : ∀ p : ℕ × ℕ, HasSum (fun c : {α : Occ // key α = p} => F (e ⟨p, c⟩))
      ((p.1 : ℝ) * p.2 * Expect.Qm Ψ [(u, p.1), (v, p.2)]) := by
    intro p
    have h1 : HasSum (fun c : {α : Occ // key α = p} => ‖Ψ c.1‖ ^ 2)
        (Expect.Qm Ψ [(u, p.1), (v, p.2)]) := by
      have h2 : HasSum (Set.indicator {α : Occ | key α = p} fun α => ‖Ψ α‖ ^ 2)
          (Expect.Qm Ψ [(u, p.1), (v, p.2)]) := by
        have : Expect.Qm Ψ [(u, p.1), (v, p.2)] =
            ∑' α, Set.indicator {α : Occ | key α = p} (fun α => ‖Ψ α‖ ^ 2) α := by
          rw [UpperIH_Qm_pair]
          congr 1
          funext α
          simp [Set.indicator, key, Prod.ext_iff]
        rw [this]
        exact (hs.indicator _).hasSum
      exact (hasSum_subtype_iff_indicator (f := fun α : Occ => ‖Ψ α‖ ^ 2)
        (s := {α : Occ | key α = p})).mpr h2
    convert h1.mul_left ((p.1 : ℝ) * p.2) using 1
    funext c
    obtain ⟨c, hc⟩ := c
    subst hc
    simp [e, key, hF, mul_assoc]
  have hall : HasSum (fun p : ℕ × ℕ => (p.1 : ℝ) * p.2 * Expect.Qm Ψ [(u, p.1), (v, p.2)])
      (∑' α, F α) :=
    HasSum.sigma (f := fun x => F (e x)) (e.hasSum_iff.mpr hFs.hasSum) hfib
  rw [hQ, ← hall.tsum_eq]
  exact hall.summable.tsum_le_tsum
    (fun p => mul_le_mul_of_nonneg_left (hab p.1 p.2) (by positivity)) hb

/-! ### Upper bounds on `P_I` and `P_H` -/

/-- (5.13) [ubpsiuroughPM] of Lemma 5.4 [lem1]. -/
theorem Lemma5_4_PI (V w : R3 → ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPI (rhoN N) (LN N) u →
      Expect.Q (trialState V w kc N) [u] ≤
        (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) := by
  set g₁ := ∫ x, |gfun V w x| with hg₁
  have hg0 : 0 ≤ g₁ := integral_nonneg fun _ => abs_nonneg _
  have hδ : 0 < 1 / (2 * (g₁ + 1)) := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (UpperIH_eventually hδ)
  refine ⟨N₀, fun N hN kc u hu => ?_⟩
  obtain ⟨hN1, hε, -, -⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  obtain ⟨ht0, ht1, hq0, -, hρq, -⟩ := UpperIH_t hρ hρ1
  have hlu := Particles_lam_abs_le V w (rhoN N) (LN N) u (fun h => Regions_PL_PI h hu)
  have hu1 : (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ) < ‖mom (LN N) u‖ := hu.1
  set t := epsP (rhoN N) with ht
  set nu := ‖mom (LN N) u‖ with hnu
  set l := lam V w (rhoN N) (LN N) u with hl
  set q := rhoN N ^ (1 / 2 : ℝ) with hqdef
  have hnu0 : 0 < nu := lt_of_le_of_lt (by positivity) hu1
  -- `ρ ≤ ε² |u|²` on `P_I`
  have hρu : rhoN N ≤ t ^ 2 * nu ^ 2 := by
    have h1 : q < t * nu := by
      have h2 := mul_lt_mul_of_pos_left hu1 ht0
      rwa [← mul_assoc, mul_inv_cancel₀ ht0.ne', one_mul] at h2
    have h3 : q ^ 2 ≤ (t * nu) ^ 2 := pow_le_pow_left₀ hq0.le h1.le 2
    rw [hρq]
    calc q ^ 2 ≤ (t * nu) ^ 2 := h3
      _ = t ^ 2 * nu ^ 2 := by ring
  have hrl : |rhoN N * l| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hρ]
    have h1 : rhoN N * |l| ≤ rhoN N * (g₁ / nu ^ 2) := mul_le_mul_of_nonneg_left hlu hρ.le
    have h2 : rhoN N * (g₁ / nu ^ 2) ≤ t ^ 2 * g₁ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      calc rhoN N * g₁ ≤ t ^ 2 * nu ^ 2 * g₁ := mul_le_mul_of_nonneg_right hρu hg0
        _ = t ^ 2 * g₁ * nu ^ 2 := by ring
    have h3 : t ^ 2 * g₁ ≤ t * g₁ :=
      mul_le_mul_of_nonneg_right (pow_le_of_le_one ht0.le ht1 (by norm_num)) hg0
    have h4 : t * g₁ ≤ 1 / 2 := by
      have h5 : t ≤ 1 / (2 * (g₁ + 1)) := hε
      rw [le_div_iff₀ (by positivity)] at h5
      have h6 : t * g₁ ≤ t * (g₁ + 1) := mul_le_mul_of_nonneg_left (by linarith) ht0.le
      linarith
    linarith
  have hx1 : (rhoN N * l) ^ 2 < 1 := by
    rw [← sq_abs]
    have := abs_nonneg (rhoN N * l)
    nlinarith
  rw [Particles_Q_eq_tsum V w kc hN1 u]
  exact UpperIH_geom (fun m => UpperIH_Qm_nonneg _ _) (UpperIH_hasSum_Qm V w kc hN1 u)
    (sq_nonneg _) hx1 (fun m => by simpa using Prop5_1 V w kc hN1 hu m 1)

/-- (5.28) [temp6.29]. -/
theorem Eq5_28 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPH (rhoN N) (LN N) u →
      ∀ m : ℕ, Expect.Qm (trialState V w kc N) [(u, m + 1)] ≤
        C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 *
          Expect.Qm (trialState V w kc N) [(u, m)] := by
  obtain ⟨C, hC, hev⟩ := UpperIH_coeff V w
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  refine ⟨C, hC, N₀, fun N hN kc u hu m => ?_⟩
  obtain ⟨hN1, hc⟩ := hN₀ N hN
  exact (Eq5_27 V w kc hN1 hu m).trans
    (mul_le_mul_of_nonneg_right (hc kc u hu) (UpperIH_Qm_nonneg _ _))

/-- (5.40) [temp5.19]. -/
theorem Eq5_40 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPH (rhoN N) (LN N) u →
      ∀ m : ℕ, Expect.Qm (trialState V w kc N) [(u, m)] ≤
        (C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2) ^ m := by
  obtain ⟨C, hC, N₀, h⟩ := Eq5_28 V w
  refine ⟨C, hC, max N₀ 1, fun N hN kc u hu m => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hc0 : 0 ≤ C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 := by
    positivity
  induction m with
  | zero =>
    simpa using le_hasSum (UpperIH_hasSum_Qm V w kc hN1 u) 0
      (fun j _ => UpperIH_Qm_nonneg _ _)
  | succ m ih =>
    calc Expect.Qm (trialState V w kc N) [(u, m + 1)]
        ≤ C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 *
            Expect.Qm (trialState V w kc N) [(u, m)] := h N (le_of_max_le_left hN) kc u hu m
      _ ≤ C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 *
            (C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2) ^ m :=
          mul_le_mul_of_nonneg_left ih hc0
      _ = (C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2) ^ (m + 1) := by
          ring

/-- (5.15) [ubpsiuroughPH] of Lemma 5.4 [lem1]. -/
theorem Lemma5_4_PH (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPH (rhoN N) (LN N) u →
      Expect.Q (trialState V w kc N) [u] ≤
        C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 := by
  obtain ⟨C, hC, N₀, h⟩ := Eq5_28 V w
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (UpperIH_PH_small V w hC)
  refine ⟨2 * C, by positivity, max N₀ N₁, fun N hN kc u hu => ?_⟩
  obtain ⟨hN1, hsm⟩ := hN₁ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  obtain ⟨ht0, -, -, -, -, -⟩ := UpperIH_t hρ hρ1
  have hnu : epsP (rhoN N) < ‖mom (LN N) u‖ := hu
  set c := C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hc2 : c ≤ 1 / 2 :=
    (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ ht0.le hnu.le 2)).trans (hsm u hu)
  rw [Particles_Q_eq_tsum V w kc hN1 u]
  refine (UpperIH_geom (fun m => UpperIH_Qm_nonneg _ _) (UpperIH_hasSum_Qm V w kc hN1 u) hc0
    (by linarith) (fun m => h N (le_of_max_le_left hN) kc u hu m)).trans ?_
  rw [div_le_iff₀ (by linarith)]
  have e : 2 * C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 = 2 * c := by
    rw [hcdef]; ring
  rw [e]
  nlinarith

/-- (5.41) [boundpsiuvmn], for `u ≠ ±v`. -/
theorem Eq5_41 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u v : Idx,
      inPH (rhoN N) (LN N) u → inPH (rhoN N) (LN N) v → u ≠ v → u + v ≠ 0 → ∀ m n : ℕ,
      Expect.Qm (trialState V w kc N) [(u, m), (v, n)] ≤
        (C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / epsP (rhoN N) ^ 2) ^ m *
          (C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) v| / epsP (rhoN N) ^ 2) ^ n := by
  obtain ⟨C₁, hC₁, hev⟩ := UpperIH_coeff V w
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  obtain ⟨C₂, hC₂, N₂, h40⟩ := Eq5_40 V w
  set A := C₁ + C₂ + 3 with hAdef
  have hA0 : 0 ≤ A := by positivity
  refine ⟨2 * A, by positivity, max N₀ N₂, fun N hN kc u v hu hv huv hsum => ?_⟩
  obtain ⟨hN1, hc⟩ := hN₀ N (le_of_max_le_left hN)
  have h40' := h40 N (le_of_max_le_right hN) kc v hv
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨ht0, ht1, -, -, -, -⟩ := UpperIH_t hρ hρ1
  have hceil := UpperIH_ceil hρ hρ1
  have hρN := UpperIH_rho_sq_N hN1
  have hnu : epsP (rhoN N) < ‖mom (LN N) u‖ := hu
  have hnv : epsP (rhoN N) < ‖mom (LN N) v‖ := hv
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set t := epsP ρ with htdef
  set lu := lam V w ρ L u with hlu
  set lv := lam V w ρ L v with hlv
  set bu := A * ρ ^ 2 * |lu| / t ^ 2 with hbu
  set bv := A * ρ ^ 2 * |lv| / t ^ 2 with hbv
  have hbu0 : 0 ≤ bu := by positivity
  have hbv0 : 0 ≤ bv := by positivity
  set κ := 4 * ρ * ⌈mc ρ⌉₊ / L ^ 3 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set cu := (ρ * lu) ^ 2 + κ *
    (∑' p : Idx, (if inPL ρ L p ∧ inPHc ρ L kc (p - u) then |lu * lam V w ρ L (p - u)| else 0))
    with hcu
  have hcu0 : 0 ≤ cu :=
    add_nonneg (sq_nonneg _) (mul_nonneg hκ0 (tsum_nonneg fun p => by split_ifs <;> positivity))
  -- `c_u ≤ b_u`
  have hcub : cu ≤ bu := by
    refine (hc kc u hu).trans ?_
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
        (abs_nonneg _)) (by positivity) (pow_le_pow_left₀ ht0.le hnu.le 2)
  -- `4ρ⌈m_c⌉|Λ|⁻¹|λ_uλ_v| ≤ b_u b_v`
  have hsb : κ * |lu * lv| ≤ bu * bv := by
    have hκb : κ ≤ A ^ 2 * ρ ^ 4 / t ^ 4 := by
      rw [hκ, div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : (⌈mc ρ⌉₊ : ℝ) * t ^ 4 ≤ 2 := by
        have h3 : t ^ 3 ≤ 1 := pow_le_one₀ ht0.le ht1
        calc (⌈mc ρ⌉₊ : ℝ) * t ^ 4 = ((⌈mc ρ⌉₊ : ℝ) * t) * t ^ 3 := by ring
          _ ≤ 2 * 1 := mul_le_mul hceil h3 (by positivity) (by norm_num)
          _ = 2 := by ring
      have h2 : 9 ≤ A ^ 2 := by nlinarith
      have h4 : A ^ 2 * ρ ≤ A ^ 2 * ρ ^ 4 * L ^ 3 := by
        have e : A ^ 2 * ρ ^ 4 * L ^ 3 = A ^ 2 * ρ * (ρ ^ 2 * (ρ * L ^ 3)) := by ring
        rw [e, hNL]
        exact le_mul_of_one_le_right (by positivity) hρN
      calc 4 * ρ * (⌈mc ρ⌉₊ : ℝ) * t ^ 4 = 4 * ρ * ((⌈mc ρ⌉₊ : ℝ) * t ^ 4) := by ring
        _ ≤ 4 * ρ * 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ A ^ 2 * ρ := by nlinarith
        _ ≤ A ^ 2 * ρ ^ 4 * L ^ 3 := h4
    calc κ * |lu * lv| ≤ A ^ 2 * ρ ^ 4 / t ^ 4 * |lu * lv| :=
          mul_le_mul_of_nonneg_right hκb (abs_nonneg _)
      _ = bu * bv := by rw [hbu, hbv, abs_mul]; field_simp
  -- base case `m = 0`, from (5.40) at `v`
  have hbase : ∀ n : ℕ, Expect.Qm (trialState V w kc N) [(u, 0), (v, n)] ≤ bv ^ n := by
    intro n
    have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
      (Normalization_isNState V w kc hN1).1.summable
    have h1 : Expect.Qm (trialState V w kc N) [(u, 0), (v, n)] ≤
        Expect.Qm (trialState V w kc N) [(v, n)] := by
      rw [UpperIH_Qm_pair, UpperIH_Qm_single]
      refine (UpperIH_summable_ite hs (fun _ => by positivity) _).tsum_le_tsum (fun α => ?_)
        (UpperIH_summable_ite hs (fun _ => by positivity) _)
      by_cases h : α u = 0 ∧ α v = n
      · rw [ite_eq_left h, ite_eq_left h.2]
      · rw [ite_eq_right h]; split_ifs <;> positivity
    refine h1.trans ((h40' n).trans (pow_le_pow_left₀ (by positivity) ?_ n))
    exact div_le_div₀ (by positivity)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
        (abs_nonneg _)) (by positivity) (pow_le_pow_left₀ ht0.le hnv.le 2)
  -- induction on `m`, for all `n`
  have key : ∀ m n : ℕ, Expect.Qm (trialState V w kc N) [(u, m), (v, n)] ≤
      (2 * bu) ^ m * bv ^ n := by
    intro m
    induction m with
    | zero => intro n; simpa using hbase n
    | succ m ih =>
      intro n
      have hstep := UpperIH_step2 V w kc hN1 hu hv huv hsum m n
      rw [← hcu] at hstep
      have ha0 := UpperIH_Qm_nonneg (trialState V w kc N) [(u, m), (v, n)]
      have h1 : cu * Expect.Qm (trialState V w kc N) [(u, m), (v, n)] ≤
          bu * ((2 * bu) ^ m * bv ^ n) :=
        mul_le_mul hcub (ih n) ha0 hbu0
      cases n with
      | zero =>
        have h0 : (∑' β : Occ, if β u = m ∧ β v + 1 = 0 then
            ‖trialState V w kc N β‖ ^ 2 else 0) = 0 := by simp
        rw [h0, mul_zero, add_zero] at hstep
        have h2 : 0 ≤ bu * (2 * bu) ^ m := by positivity
        refine hstep.trans (h1.trans ?_)
        calc bu * ((2 * bu) ^ m * bv ^ 0) = bu * (2 * bu) ^ m := by ring
          _ ≤ 2 * (bu * (2 * bu) ^ m) := by linarith
          _ = (2 * bu) ^ (m + 1) * bv ^ 0 := by ring
      | succ k =>
        have hk : (∑' β : Occ, if β u = m ∧ β v + 1 = k + 1 then
            ‖trialState V w kc N β‖ ^ 2 else 0) =
            Expect.Qm (trialState V w kc N) [(u, m), (v, k)] := by
          rw [UpperIH_Qm_pair]
          congr 1
          funext β
          simp
        rw [hk] at hstep
        have h2 : κ * |lu * lv| * Expect.Qm (trialState V w kc N) [(u, m), (v, k)] ≤
            bu * bv * ((2 * bu) ^ m * bv ^ k) :=
          mul_le_mul hsb (ih k) (UpperIH_Qm_nonneg _ _) (by positivity)
        refine hstep.trans ((add_le_add h1 h2).trans_eq ?_)
        ring
  intro m n
  have e1 : 2 * A * ρ ^ 2 * |lu| / t ^ 2 = 2 * bu := by rw [hbu]; ring
  have e2 : 2 * A * ρ ^ 2 * |lv| / t ^ 2 = 2 * bv := by rw [hbv]; ring
  rw [e1, e2]
  refine (key m n).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hbv0 ?_ n)
    (by positivity))
  linarith

/-- (5.42) [boundpsifixeduv], for `u ≠ ±v`. -/
theorem Eq5_42 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u v : Idx,
      inPH (rhoN N) (LN N) u → inPH (rhoN N) (LN N) v → u ≠ v → u + v ≠ 0 →
      Expect.Q (trialState V w kc N) [u, v] ≤
        C * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 4 /
          epsP (rhoN N) ^ 4 := by
  obtain ⟨C, hC, N₀, h41⟩ := Eq5_41 V w
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (UpperIH_PH_small V w hC)
  refine ⟨16 * C ^ 2, by positivity, max N₀ N₁, fun N hN kc u v hu hv huv hsum => ?_⟩
  obtain ⟨hN1, hsm⟩ := hN₁ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  obtain ⟨ht0, -, -, -, -, -⟩ := UpperIH_t hρ hρ1
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN1).1.summable
  set Bu := C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / epsP (rhoN N) ^ 2 with hBu
  set Bv := C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) v| / epsP (rhoN N) ^ 2 with hBv
  have hBu0 : 0 ≤ Bu := by positivity
  have hBv0 : 0 ≤ Bv := by positivity
  have hBu1 : Bu ≤ 1 / 2 := hsm u hu
  have hBv1 : Bv ≤ 1 / 2 := hsm v hv
  have hnu : ‖Bu‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hBu0]; linarith
  have hnv : ‖Bv‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hBv0]; linarith
  have hfu : Summable fun m : ℕ => (m : ℝ) * Bu ^ m := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnu
  have hfv : Summable fun n : ℕ => (n : ℝ) * Bv ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnv
  have hprod := hfu.mul_of_nonneg hfv (fun m => mul_nonneg (Nat.cast_nonneg m) (pow_nonneg hBu0 m))
    (fun n => mul_nonneg (Nat.cast_nonneg n) (pow_nonneg hBv0 n))
  have hb : Summable fun p : ℕ × ℕ => (p.1 : ℝ) * p.2 * (Bu ^ p.1 * Bv ^ p.2) := by
    refine hprod.congr fun p => ?_
    ring
  have hQ := UpperIH_Q2_le (trialState V w kc N) hs u v (fun m n => Bu ^ m * Bv ^ n) hb
    (fun m n => h41 N (le_of_max_le_left hN) kc u v hu hv huv hsum m n)
  have hsum2 : (∑' p : ℕ × ℕ, (p.1 : ℝ) * p.2 * (Bu ^ p.1 * Bv ^ p.2)) =
      (Bu / (1 - Bu) ^ 2) * (Bv / (1 - Bv) ^ 2) := by
    rw [← tsum_coe_mul_geometric_of_norm_lt_one hnu, ← tsum_coe_mul_geometric_of_norm_lt_one hnv,
      hfu.tsum_mul_tsum hfv hprod]
    congr 1
    funext p
    ring
  have hgeo : ∀ B : ℝ, 0 ≤ B → B ≤ 1 / 2 → B / (1 - B) ^ 2 ≤ 4 * B := by
    intro B h0 h1
    rw [div_le_iff₀ (by nlinarith)]
    have h2 : 1 / 4 ≤ (1 - B) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  refine hQ.trans ?_
  rw [hsum2]
  refine (mul_le_mul (hgeo Bu hBu0 hBu1) (hgeo Bv hBv0 hBv1) (by positivity)
    (by positivity)).trans_eq ?_
  rw [hBu, hBv, abs_mul]
  field_simp
  ring

end LHYUpper
