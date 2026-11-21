module

public import LHYUpper.Assembly.Section4
public import LHYUpper.Assembly.Theorem31
public import LHYUpper.OneLeg.Forms
public import LHYUpper.OneLeg.Sums

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! Lemma 8.3, (8.14) [0resultfirstcase]–(8.16) [0resultthirdcase], as an iterated `lim sup` in
`EReal`, and Lemma 4.5 [lemHAS1], (4.12) [proofthem1-5]. -/

/-! ### The scales `ρ_N`, `L_N` and the iterated `lim sup` -/

/-- `ρ_N^a → 0` for `a > 0`. -/
private lemma Lemma45_rho_tendsto_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.comp hT

/-- `ρ_N^a → ∞` for `a < 0`. -/
private lemma Lemma45_rho_tendsto_atTop {a : ℝ} (ha : a < 0) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop atTop := by
  have h : ∀ N : ℕ, rhoN N ^ a = (N : ℝ) ^ (8 / 17 * (-a)) := fun N => by
    rw [rhoN, ← Real.rpow_mul (Nat.cast_nonneg N)]
    ring_nf
  simp_rw [h]
  exact (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop

/-- `2π ≤ L_N` eventually. -/
private lemma Lemma45_ev_L : ∀ᶠ N : ℕ in atTop, 2 * π ≤ LN N := by
  filter_upwards [(Lemma45_rho_tendsto_atTop (a := -(25/24 : ℝ)) (by norm_num)).eventually_ge_atTop
    (2 * π)] with N hN
  exact hN

/-- `ρ_N ≥ 0`. -/
private lemma Lemma45_rho_nonneg (N : ℕ) : 0 ≤ rhoN N := Real.rpow_nonneg (Nat.cast_nonneg N) _

/-- `ρ^{1/2} ≤ ρ^{1/400}` at `ρ = ρ_N`, `N ≥ 1`. -/
private lemma Lemma45_half_le {N : ℕ} (hN : 1 ≤ N) :
    rhoN N ^ (1/2 : ℝ) ≤ rhoN N ^ (1/400 : ℝ) := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)

/-- The coercion `ℝ → EReal` preserves limits. -/
private lemma Lemma45_tendsto_coe {α : Type*} {f : Filter α} {u : α → ℝ} {a : ℝ}
    (h : Tendsto u f (𝓝 a)) : Tendsto (fun x => (u x : EReal)) f (𝓝 (a : EReal)) :=
  (continuous_coe_real_ereal.tendsto a).comp h

/-- A bound `|F(k_c, N) - R| ≤ C(ρ_N^{1/400} + k_c⁻¹)` for `N ≥ N₀` and `k_c ≥ 1` determines
`lim sup_{k_c → ∞} lim sup_{N → ∞} F = R` in `EReal`. -/
private lemma Lemma45_limsup2_eq (F : ℝ → ℕ → ℝ) (R C : ℝ) (N₀ : ℕ)
    (h : ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc → |F kc N - R| ≤ C * (rhoN N ^ (1/400 : ℝ) + kc⁻¹)) :
    Section4.limsup2 F = (R : EReal) := by
  set c : ℝ := |C| with hc
  have hr : Tendsto (fun N : ℕ => rhoN N ^ (1/400 : ℝ)) atTop (𝓝 0) :=
    Lemma45_rho_tendsto_zero (by norm_num)
  have inner : ∀ kc : ℝ, 1 ≤ kc →
      ((R - c * kc⁻¹ : ℝ) : EReal) ≤ limsup (fun N : ℕ => (F kc N : EReal)) atTop ∧
        limsup (fun N : ℕ => (F kc N : EReal)) atTop ≤ ((R + c * kc⁻¹ : ℝ) : EReal) := by
    intro kc hkc
    have hk0 : 0 ≤ kc⁻¹ := inv_nonneg.2 (by linarith)
    have hbd : ∀ N ≥ N₀, |F kc N - R| ≤ c * (rhoN N ^ (1/400 : ℝ) + kc⁻¹) := fun N hN =>
      (h N hN kc hkc).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
        (add_nonneg (Real.rpow_nonneg (Lemma45_rho_nonneg N) _) hk0))
    have hup : Tendsto (fun N : ℕ => R + c * kc⁻¹ + c * rhoN N ^ (1/400 : ℝ)) atTop
        (𝓝 (R + c * kc⁻¹)) := by
      simpa using tendsto_const_nhds.add (hr.const_mul c)
    have hlo : Tendsto (fun N : ℕ => R - c * kc⁻¹ - c * rhoN N ^ (1/400 : ℝ)) atTop
        (𝓝 (R - c * kc⁻¹)) := by
      simpa using tendsto_const_nhds.sub (hr.const_mul c)
    constructor
    · calc ((R - c * kc⁻¹ : ℝ) : EReal)
          = limsup (fun N : ℕ => ((R - c * kc⁻¹ - c * rhoN N ^ (1/400 : ℝ) : ℝ) : EReal)) atTop :=
            (Lemma45_tendsto_coe hlo).limsup_eq.symm
        _ ≤ _ := by
          refine Filter.limsup_le_limsup ?_
          filter_upwards [eventually_ge_atTop N₀] with N hN
          have h1 := (abs_le.1 (hbd N hN)).1
          rw [mul_add] at h1
          exact EReal.coe_le_coe_iff.2 (by linarith)
    · calc limsup (fun N : ℕ => (F kc N : EReal)) atTop
          ≤ limsup (fun N : ℕ =>
              ((R + c * kc⁻¹ + c * rhoN N ^ (1/400 : ℝ) : ℝ) : EReal)) atTop := by
            refine Filter.limsup_le_limsup ?_
            filter_upwards [eventually_ge_atTop N₀] with N hN
            have h1 := (abs_le.1 (hbd N hN)).2
            rw [mul_add] at h1
            exact EReal.coe_le_coe_iff.2 (by linarith)
        _ = _ := (Lemma45_tendsto_coe hup).limsup_eq
  have hk : Tendsto (fun kc : ℝ => kc⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hU : Tendsto (fun kc : ℝ => R + c * kc⁻¹) atTop (𝓝 R) := by
    simpa using tendsto_const_nhds.add (hk.const_mul c)
  have hD : Tendsto (fun kc : ℝ => R - c * kc⁻¹) atTop (𝓝 R) := by
    simpa using tendsto_const_nhds.sub (hk.const_mul c)
  unfold Section4.limsup2
  refine le_antisymm ?_ ?_
  · calc _ ≤ limsup (fun kc : ℝ => ((R + c * kc⁻¹ : ℝ) : EReal)) atTop := by
          refine Filter.limsup_le_limsup ?_
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with kc hkc using (inner kc hkc).2
      _ = _ := (Lemma45_tendsto_coe hU).limsup_eq
  · calc (R : EReal) = limsup (fun kc : ℝ => ((R - c * kc⁻¹ : ℝ) : EReal)) atTop :=
          (Lemma45_tendsto_coe hD).limsup_eq.symm
      _ ≤ _ := by
          refine Filter.limsup_le_limsup ?_
          filter_upwards [eventually_ge_atTop (1 : ℝ)] with kc hkc using (inner kc hkc).1

/-- A bound `|F(k_c, N) - R| ≤ C(ρ_N^{1/400} + k_c⁻¹)` for `N ≥ N₀` and `k_c ≥ 1` gives
`lim sup_{k_c → ∞} lim sup_{N → ∞} F ≤ R`. -/
theorem OneLeg_limsup2_le (F : ℝ → ℕ → ℝ) (R C : ℝ) (N₀ : ℕ)
    (h : ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc → |F kc N - R| ≤ C * (rhoN N ^ (1/400 : ℝ) + kc⁻¹)) :
    Section4.limsup2 F ≤ (R : EReal) :=
  (Lemma45_limsup2_eq F R C N₀ h).le

/-! ### Real parts and norms of the three case sums -/

/-- A sum over the indices satisfying a condition is summable if the summands are absolutely
summable. -/
private lemma Lemma45_summable_ite {ι : Type*} (c : ι → Prop) (f : ι → ℂ)
    (hf : Summable fun i => ‖f i‖) : Summable fun i => if c i then f i else 0 :=
  Summable.of_norm_bounded hf (fun i => by split_ifs <;> simp)

/-- `|Re(a Σ_{c} f)| ≤ a Σ_{c} ‖f‖` for `a ≥ 0` and absolutely summable `f`. -/
private lemma Lemma45_re_ite_le {ι : Type*} (a : ℝ) (ha : 0 ≤ a) (c : ι → Prop) (f : ι → ℂ)
    (hf : Summable fun i => ‖f i‖) :
    |(((a : ℝ) : ℂ) * ∑' i, (if c i then f i else 0)).re| ≤
      a * ∑' i, (if c i then ‖f i‖ else 0) := by
  have hs : Summable fun i => ‖(if c i then f i else 0)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => by split_ifs <;> simp) hf
  calc |(((a : ℝ) : ℂ) * ∑' i, (if c i then f i else 0)).re|
      ≤ ‖((a : ℝ) : ℂ) * ∑' i, (if c i then f i else 0)‖ := Complex.abs_re_le_norm _
    _ = a * ‖∑' i, (if c i then f i else 0)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ a * ∑' i, ‖(if c i then f i else 0)‖ :=
        mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hs) ha
    _ = a * ∑' i, (if c i then ‖f i‖ else 0) := by
        congr 1
        exact tsum_congr fun i => by split_ifs <;> simp

/-- `E/|Λ|` of (4.6) in terms of the normalized complex sum, at `m = 0`. -/
private lemma Lemma45_excess_eq {V w : R3 → ℝ} {N : ℕ} (T : ℂ) :
    Section4.excess (g0 V w) 0 (4 * (LN N ^ 3)⁻¹ * T.re) N =
      4 * (((rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ : ℝ) : ℂ) * T).re := by
  unfold Section4.excess
  rw [Complex.re_ofReal_mul, Real.rpow_neg (Lemma45_rho_nonneg N)]
  ring

/-- Lemma 4.5 [lemHAS1] with a rate: `H_{A1}` of (4.6) has a real sum `E` for the trial state,
and `(E/|Λ|) ρ^{-5/2}` is `-8‖Vw‖₁ g₀^{3/2}/(3π²)` up to `C(ρ^{1/400} + k_c⁻¹)`. -/
theorem OneLeg_rate {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ E : ℝ → ℕ → ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      HasSum (Decomp.partTerm .A1 (LN N) V (trialState V w kc N)) (E kc N : ℂ) ∧
      (1 ≤ kc → |Section4.excess (g0 V w) 0 (E kc N) N -
        (-8 * normVw V w * Section4.G V w / 3)| ≤ C * (rhoN N ^ (1/400 : ℝ) + kc⁻¹)) := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Lemma8_3_first hV hw
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := Lemma8_3_second hV hw
  obtain ⟨C₃, hC₃, N₃, h₃⟩ := Lemma8_3_third hV hw
  obtain ⟨N₄, hN₄⟩ := Filter.eventually_atTop.1 ((eventually_ge_atTop 1).and Lemma45_ev_L)
  refine ⟨fun kc N => 4 * (LN N ^ 3)⁻¹ *
      (∑' i, OneLeg_term (LN N) V (trialState V w kc N) i).re, 4 * (C₁ + C₂ + C₃),
    by positivity, max (max (max N₁ N₂) N₃) N₄, fun N hN kc => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hNa, hNb⟩, hNc⟩, hNd⟩ := hN
  obtain ⟨hN1, hL⟩ := hN₄ N hNd
  have hsum := OneLeg_summable_V hV hL
  have hΨ := Normalization_isNState V w kc hN1
  refine ⟨OneLeg_hasSum_A1 (LN N) V N _ hsum hV.even hΨ, fun hkc => ?_⟩
  have hnorm := OneLeg_summable (LN N) V N _ hsum hΨ
  set Ψ := trialState V w kc N with hΨdef
  have hs1 := Lemma45_summable_ite (fun i : Idx × Idx × Occ =>
    OneLeg_case1 (rhoN N) (LN N) kc i.1 i.2.1) (OneLeg_term (LN N) V Ψ) hnorm
  have hs2 := Lemma45_summable_ite (fun i : Idx × Idx × Occ =>
    OneLeg_case2 (rhoN N) (LN N) kc i.1 i.2.1) (OneLeg_term (LN N) V Ψ) hnorm
  have hs3 := Lemma45_summable_ite (fun i : Idx × Idx × Occ =>
    OneLeg_case3 (rhoN N) (LN N) i.1 i.2.1) (OneLeg_term (LN N) V Ψ) hnorm
  have hT : ∑' i, OneLeg_term (LN N) V Ψ i =
      (∑' i : Idx × Idx × Occ, (if OneLeg_case1 (rhoN N) (LN N) kc i.1 i.2.1 then
          OneLeg_term (LN N) V Ψ i else 0)) +
        (∑' i : Idx × Idx × Occ, (if OneLeg_case2 (rhoN N) (LN N) kc i.1 i.2.1 then
          OneLeg_term (LN N) V Ψ i else 0)) +
        (∑' i : Idx × Idx × Occ, (if OneLeg_case3 (rhoN N) (LN N) i.1 i.2.1 then
          OneLeg_term (LN N) V Ψ i else 0)) := by
    rw [← hs1.tsum_add hs2, ← (hs1.add hs2).tsum_add hs3]
    exact tsum_congr (OneLeg_split V w kc hN1)
  set a : ℝ := rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ with ha
  have ha0 : 0 ≤ a :=
    mul_nonneg (Real.rpow_nonneg (Lemma45_rho_nonneg N) _) (inv_nonneg.2 (sq_nonneg _))
  have hk0 : 0 ≤ kc⁻¹ := inv_nonneg.2 (by linarith)
  have hr0 : 0 ≤ rhoN N ^ (1/400 : ℝ) := Real.rpow_nonneg (Lemma45_rho_nonneg N) _
  have e1 := h₁ N hNa kc hkc
  have e2 := h₂ N hNb kc
  have e3 := h₃ N hNc kc
  set m₁ : ℝ := -2 * normVw V w * (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2)) with hm₁
  set S₁ := ∑' i : Idx × Idx × Occ, (if OneLeg_case1 (rhoN N) (LN N) kc i.1 i.2.1 then
          OneLeg_term (LN N) V Ψ i else 0) with hS₁
  set S₂ := ∑' i : Idx × Idx × Occ, (if OneLeg_case2 (rhoN N) (LN N) kc i.1 i.2.1 then
          OneLeg_term (LN N) V Ψ i else 0) with hS₂
  set S₃ := ∑' i : Idx × Idx × Occ, (if OneLeg_case3 (rhoN N) (LN N) i.1 i.2.1 then
          OneLeg_term (LN N) V Ψ i else 0) with hS₃
  have b1 : |((a : ℂ) * S₁).re - m₁| ≤ C₁ * (rhoN N ^ (1/400 : ℝ) + kc⁻¹) := by
    have : ((a : ℂ) * S₁).re - m₁ = ((a : ℂ) * S₁ - (m₁ : ℂ)).re := by
      simp
    rw [this]
    exact (Complex.abs_re_le_norm _).trans e1
  have b2 : |((a : ℂ) * S₂).re| ≤ C₂ * rhoN N ^ (1/400 : ℝ) := by
    refine (Lemma45_re_ite_le a ha0 (fun i : Idx × Idx × Occ =>
      OneLeg_case2 (rhoN N) (LN N) kc i.1 i.2.1) (OneLeg_term (LN N) V Ψ) hnorm).trans ?_
    exact e2.trans (mul_le_mul_of_nonneg_left (Lemma45_half_le hN1) hC₂)
  have b3 : |((a : ℂ) * S₃).re| ≤ C₃ * rhoN N ^ (1/400 : ℝ) := by
    refine (Lemma45_re_ite_le a ha0 (fun i : Idx × Idx × Occ =>
      OneLeg_case3 (rhoN N) (LN N) i.1 i.2.1) (OneLeg_term (LN N) V Ψ) hnorm).trans ?_
    exact e3.trans (mul_le_mul_of_nonneg_left (Lemma45_half_le hN1) hC₃)
  change |Section4.excess (g0 V w) 0 (4 * (LN N ^ 3)⁻¹ *
      (∑' i, OneLeg_term (LN N) V Ψ i).re) N - (-8 * normVw V w * Section4.G V w / 3)| ≤ _
  rw [Lemma45_excess_eq, hT, mul_add, mul_add, Complex.add_re, Complex.add_re]
  have hG : -8 * normVw V w * Section4.G V w / 3 = 4 * m₁ := by
    simp only [Section4.G, hm₁]
    ring
  rw [hG]
  rw [abs_le] at b1 b2 b3 ⊢
  have p2 : 0 ≤ C₂ * kc⁻¹ := mul_nonneg hC₂ hk0
  have p3 : 0 ≤ C₃ * kc⁻¹ := mul_nonneg hC₃ hk0
  constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]

/-- The normalized sums of the absolute values of the summands over a case, with weight
`ρ^{-5/2} |Λ|⁻²`, are nonnegative. -/
private lemma Lemma45_weight_nonneg {ι : Type*} (N : ℕ) (c : ι → Prop) (f : ι → ℂ) :
    0 ≤ rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ * ∑' i, (if c i then ‖f i‖ else 0) :=
  mul_nonneg (mul_nonneg (Real.rpow_nonneg (Lemma45_rho_nonneg N) _) (inv_nonneg.2 (sq_nonneg _)))
    (tsum_nonneg fun i => by split_ifs <;> simp)

/-- A one-sided bound `0 ≤ F ≤ Cρ^{1/2}` for `N ≥ N₀` and every `k_c` gives
`lim sup_{k_c → ∞} lim sup_{N → ∞} F = 0`. -/
private lemma Lemma45_limsup2_zero (F : ℝ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C) (N₀ : ℕ)
    (h0 : ∀ N kc, 0 ≤ F kc N) (h : ∀ N ≥ N₀, ∀ kc : ℝ, F kc N ≤ C * rhoN N ^ (1/2 : ℝ)) :
    Section4.limsup2 F = 0 := by
  rw [← EReal.coe_zero]
  refine Lemma45_limsup2_eq F 0 C (max N₀ 1) (fun N hN kc hkc => ?_)
  have hk0 : 0 ≤ kc⁻¹ := inv_nonneg.2 (by linarith)
  rw [sub_zero, abs_of_nonneg (h0 N kc)]
  calc F kc N ≤ C * rhoN N ^ (1/2 : ℝ) := h N (le_trans (le_max_left _ _) hN) kc
    _ ≤ C * rhoN N ^ (1/400 : ℝ) :=
        mul_le_mul_of_nonneg_left (Lemma45_half_le (le_trans (le_max_right _ _) hN)) hC
    _ ≤ C * (rhoN N ^ (1/400 : ℝ) + kc⁻¹) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hk0) hC

/-- Lemma 8.3, (8.14) [0resultfirstcase]–(8.16) [0resultthirdcase], as
`lim sup_{k_c → ∞} lim sup_{ρ → 0}` along `ρ = ρ_N`; (8.14) for the real part. -/
theorem Lemma8_3_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Section4.limsup2 (fun kc N => (((rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ : ℝ) : ℂ) *
        (∑' i : Idx × Idx × Occ, (if OneLeg_case1 (rhoN N) (LN N) kc i.1 i.2.1 then
          OneLeg_term (LN N) V (trialState V w kc N) i else 0))).re) =
      ((-2 * normVw V w * (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2)) : ℝ) : EReal) ∧
    Section4.limsup2 (fun kc N => rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ *
        (∑' i : Idx × Idx × Occ, (if OneLeg_case2 (rhoN N) (LN N) kc i.1 i.2.1 then
          ‖OneLeg_term (LN N) V (trialState V w kc N) i‖ else 0))) = 0 ∧
    Section4.limsup2 (fun kc N => rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ *
        (∑' i : Idx × Idx × Occ, (if OneLeg_case3 (rhoN N) (LN N) i.1 i.2.1 then
          ‖OneLeg_term (LN N) V (trialState V w kc N) i‖ else 0))) = 0 := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Lemma8_3_first hV hw
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := Lemma8_3_second hV hw
  obtain ⟨C₃, hC₃, N₃, h₃⟩ := Lemma8_3_third hV hw
  refine ⟨?_, ?_, ?_⟩
  · refine Lemma45_limsup2_eq _ _ C₁ N₁ (fun N hN kc hkc => ?_)
    refine le_trans ?_ (h₁ N hN kc hkc)
    rw [← Complex.ofReal_re (-2 * normVw V w * (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2))),
      ← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  · exact Lemma45_limsup2_zero _ C₂ hC₂ N₂
      (fun N kc => Lemma45_weight_nonneg N _ _) (fun N hN kc => h₂ N hN kc)
  · exact Lemma45_limsup2_zero _ C₃ hC₃ N₃
      (fun N kc => Lemma45_weight_nonneg N _ _) (fun N hN kc => h₃ N hN kc)

/-- Lemma 4.5 [lemHAS1], (4.12) [proofthem1-5]. -/
theorem lemma4_5 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma4_5 V w := by
  obtain ⟨E, C, -, N₀, h⟩ := OneLeg_rate hV hw
  refine ⟨E, fun kc => Filter.eventually_atTop.2 ⟨N₀, fun N hN => (h N hN kc).1⟩, ?_⟩
  exact OneLeg_limsup2_le (fun kc N => Section4.excess (g0 V w) 0 (E kc N) N)
    (-8 * normVw V w * Section4.G V w / 3) C N₀ (fun N hN kc hkc => (h N hN kc).2 hkc)

end LHYUpper
