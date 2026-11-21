module

public import LHYUpper.Assembly.Section4
public import LHYUpper.Fock.Expect
public import LHYUpper.Riemann.ScaledLimits
public import LHYUpper.Scattering.Lambda
public import LHYUpper.TrialState.Normalization
public import LHYUpper.Pair.Identities
public import LHYUpper.Pair.Sums
public import LHYUpper.Pair.S2Exact
public import LHYUpper.Particles.Lower
public import LHYUpper.Particles.Lemma55

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # §7.1–§7.2: `H_{S1}`, `H_{S2}`, Lemma 7.2 [symno20], Lemmas 4.2 [lemHS1] and 4.3 [lemHS2]

Rates at `ρ = ρ_N`, `|Λ| = L_N³`, uniform in `k_c`, and the two endpoints in the form of
`Section4.PartBound`. -/

/-! ### Scaling facts at `ρ = ρ_N`, `L = L_N` -/

/-- `ρ_N^b = N^{-8b/17}`. -/
private lemma S1S2_rho_pow_eq (N : ℕ) (b : ℝ) :
    rhoN N ^ b = (N : ℝ) ^ (-(8/17 : ℝ) * b) := by
  rw [rhoN, ← Real.rpow_mul (Nat.cast_nonneg N)]

/-- `ρ_N^{-a} → ∞` for `a > 0`. -/
private lemma S1S2_tendsto_neg {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ (-a)) atTop atTop := by
  simp_rw [S1S2_rho_pow_eq]
  have : (0 : ℝ) < -(8/17) * -a := by nlinarith
  exact (tendsto_rpow_atTop this).comp tendsto_natCast_atTop_atTop

/-- `ρ_N^b → 0` for `b > 0`. -/
private lemma S1S2_tendsto_pos {b : ℝ} (hb : 0 < b) :
    Tendsto (fun N : ℕ => rhoN N ^ b) atTop (𝓝 0) := by
  simp_rw [S1S2_rho_pow_eq]
  have : (0 : ℝ) < (8/17) * b := by positivity
  have h := (tendsto_rpow_neg_atTop this).comp tendsto_natCast_atTop_atTop
  refine h.congr (fun N => ?_)
  simp only [Function.comp]
  congr 1
  ring

/-- Eventually `A ρ_N^b ≤ 1` for `b > 0`. -/
private lemma S1S2_ev_small (A : ℝ) {b : ℝ} (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, A * rhoN N ^ b ≤ 1 := by
  have h := (S1S2_tendsto_pos hb).const_mul A
  rw [mul_zero] at h
  exact h.eventually (eventually_le_nhds one_pos)

/-- Eventually `A ≤ ρ_N^{-a}` for `a > 0`. -/
private lemma S1S2_ev_large (A : ℝ) {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, A ≤ rhoN N ^ (-a) :=
  (S1S2_tendsto_neg ha).eventually_ge_atTop A

/-- `x^b ≤ x^a` for `0 < x ≤ 1` and `a ≤ b`. -/
private lemma S1S2_rpow_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {a b : ℝ} (h : a ≤ b) :
    x ^ b ≤ x ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hx hx1 h

/-- `L_N³ = ρ_N^{-25/8}`. -/
private lemma S1S2_L3 (N : ℕ) : LN N ^ 3 = rhoN N ^ (-(25/8 : ℝ)) := by
  have hρ : 0 ≤ rhoN N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rw [LN, ← Real.rpow_natCast, ← Real.rpow_mul hρ]
  norm_num

/-- `ρ_N / L_N³ = ρ_N^{33/8}`. -/
private lemma S1S2_rho_div_L3 {N : ℕ} (hN : 1 ≤ N) :
    rhoN N / LN N ^ 3 = rhoN N ^ (33/8 : ℝ) := by
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  rw [S1S2_L3, Real.rpow_neg hρ.le, div_inv_eq_mul, ← Real.rpow_one_add' hρ.le (by norm_num)]
  norm_num

/-- `L_N ρ_N^{1/2} = ρ_N^{-13/24}`. -/
private lemma S1S2_L_sqrt {N : ℕ} (hN : 1 ≤ N) :
    LN N * rhoN N ^ (1/2 : ℝ) = rhoN N ^ (-(13/24 : ℝ)) := by
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  rw [LN, ← Real.rpow_add hρ]
  norm_num

/-- `ρ_N/L_N³ ≤ ρ_N^{5/2 + 1/400}`. -/
private lemma S1S2_rho_div_L3_le {N : ℕ} (hN : 1 ≤ N) :
    rhoN N / LN N ^ 3 ≤ rhoN N ^ (5/2 + 1/400 : ℝ) := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  rw [S1S2_rho_div_L3 hN]
  exact S1S2_rpow_le hρ hρ1 (by norm_num)

/-- `1 ≤ L_N` for `N ≥ 1`. -/
private lemma S1S2_one_le_L {N : ℕ} (hN : 1 ≤ N) : 1 ≤ LN N := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)

/-! ### The condensate density `ρ₀` of (3.14) [defrho0] -/

/-- With `c = g^{3/2}/(3π²)` and `cρ^{1/2} ≤ 1`: `0 ≤ ρ₀ ≤ ρ` and
`0 ≤ ρ² − ρ₀² ≤ 2cρ^{5/2}`. -/
private lemma S1S2_rho0 {g ρ : ℝ} (hg : 0 ≤ g) (hρ : 0 < ρ)
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

/-- `2 · 2 g^{3/2}/(3π²) = (4/3) g^{3/2}/π²`. -/
private lemma S1S2_const (g : ℝ) :
    2 * (2 * ((3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ))) = 4 * (g ^ (3/2 : ℝ) / π ^ 2) / 3 := by
  have : π ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-! ### The double lim sup in `EReal` -/

/-- If for every `k_c` and every `N ≥ N₀`, `F(k_c, N) ≤ R + D ρ_N^a` with `a > 0`, then
`lim sup_{k_c} lim sup_N F ≤ R` in `EReal`. -/
private lemma S1S2_limsup2_le (F : ℝ → ℕ → ℝ) (R D a : ℝ) (ha : 0 < a) (N₀ : ℕ)
    (h : ∀ kc : ℝ, ∀ N ≥ N₀, F kc N ≤ R + D * rhoN N ^ a) :
    Section4.limsup2 F ≤ (R : EReal) := by
  have hT : Tendsto (fun N : ℕ => R + D * rhoN N ^ a) atTop (𝓝 R) := by
    have := ((S1S2_tendsto_pos ha).const_mul D).const_add R
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

/-! ### Elementary facts on `V`, `Q_Ψ` -/

/-- `V₀ = ∫ V`. -/
private lemma S1S2_V0_eq (V : R3 → ℝ) : V0 V = ∫ x, V x := by
  rw [V0, scat_ft_zero, Complex.ofReal_re]

/-- `|V_p| ≤ V₀`. -/
private lemma S1S2_abs_V_le {V : R3 → ℝ} (hV : PotentialHyp V) (p : R3) :
    |(ft V p).re| ≤ V0 V :=
  (Complex.abs_re_le_norm _).trans (S1S2_V0_eq V ▸ scat_ft_V_norm_le hV p)

/-- `V₀ > 0`. -/
private lemma S1S2_V0_pos {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    0 < V0 V := by
  rw [S1S2_V0_eq]
  exact (scat_g0_pos hV hw).trans_le (scat_g0_le hV hw)

/-- `Q_Ψ(u₁, …, u_s) ≥ 0`. -/
private lemma S1S2_Q_nonneg (Ψ : Occ → ℂ) (us : List Idx) : 0 ≤ Expect.Q Ψ us :=
  tsum_nonneg fun α => mul_nonneg (List.prod_nonneg (by simp)) (by positivity)

/-! ### `P_I ∪ P_H`: (7.7) [u-uPMH] -/

/-- `ρ · ρ^{1/200} · ρ^{3/2} ≤ ρ^{5/2+1/400}` for `0 < ρ ≤ 1`. -/
private lemma S1S2_pow_IH {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ * ρ ^ (1/200 : ℝ) * ρ ^ (3/2 : ℝ) ≤ ρ ^ (5/2 + 1/400 : ℝ) := by
  have e : ρ * ρ ^ (1/200 : ℝ) * ρ ^ (3/2 : ℝ) = ρ ^ (1 + 1/200 + 3/2 : ℝ) := by
    rw [Real.rpow_add hρ, Real.rpow_add hρ, Real.rpow_one]
  rw [e]
  exact S1S2_rpow_le hρ hρ1 (by norm_num)

/-- Pointwise bound behind (7.7) [u-uPMH], from (7.12) read with the factor `|Λ|^{-2}`:
for `u ∈ P_I ∪ P_H`, `|V_u(Re⟨…⟩/|Λ| − ρ₀²λ_u)| ≤ V₀ρQ_Ψ(u) + |λ_u V_u|(e + ρ/|Λ|)`
where `e` bounds `|Q_Ψ(0,0)/|Λ|² − ρ₀²|`. -/
private lemma S1S2_IH_pt {V w : R3 → ℝ} (hV : PotentialHyp V) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N)
    {u : Idx} (hu : inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u) {e : ℝ}
    (he : |Expect.Q (trialState V w kc N) [0, 0] / (LN N ^ 3) ^ 2 - rho0 (g0 V w) (rhoN N) ^ 2|
      ≤ e)
    (hrl : |rhoN N * lam V w (rhoN N) (LN N) u| ≤ 1) :
    |(ft V (mom (LN N) u)).re *
        ((Expect.E4 (trialState V w kc N) u (-u) 0 0).re / LN N ^ 3 -
          rho0 (g0 V w) (rhoN N) ^ 2 * lam V w (rhoN N) (LN N) u)| ≤
      V0 V * rhoN N * Expect.Q (trialState V w kc N) [u] +
        |lam V w (rhoN N) (LN N) u * (ft V (0 - mom (LN N) u)).re| *
          (e + rhoN N / LN N ^ 3) := by
  obtain ⟨hρL, hρ, -, hL⟩ := Particles_rhoN_LN hN
  set Ψ := trialState V w kc N
  set ρ := rhoN N
  set L3 := LN N ^ 3 with hL3
  set l := lam V w ρ (LN N) u
  set Q := Expect.Q Ψ [u]
  set Q00 := Expect.Q Ψ [0, 0]
  set Q0 := Expect.Q Ψ [0]
  set r0 := rho0 (g0 V w) ρ
  set X := Expect.E4 Ψ u (-u) 0 0
  have hL3p : 0 < L3 := pow_pos hL 3
  have h12 := Eq7_12 V w kc hN hu
  have hre : |X.re / L3 - l / L3 ^ 2 * (Q00 - Q0)| ≤ |l| * ρ ^ 2 * Q := by
    have := (Complex.abs_re_le_norm _).trans h12
    rwa [Complex.sub_re, Complex.div_ofReal_re, Complex.ofReal_re] at this
  have hQ0 : 0 ≤ Q0 := S1S2_Q_nonneg _ _
  have hQ0N : Q0 ≤ N := Expect.Q_single_le N Ψ (Normalization_isNState V w kc hN) 0
  have hQ : 0 ≤ Q := S1S2_Q_nonneg _ _
  have hQ0L : Q0 / L3 ^ 2 ≤ ρ / L3 := by
    rw [div_le_div_iff₀ (by positivity) hL3p]
    have h := hQ0N
    rw [← hρL] at h
    nlinarith
  have hD : |l / L3 ^ 2 * (Q00 - Q0) - r0 ^ 2 * l| ≤ |l| * (e + ρ / L3) := by
    have : l / L3 ^ 2 * (Q00 - Q0) - r0 ^ 2 * l = l * ((Q00 / L3 ^ 2 - r0 ^ 2) - Q0 / L3 ^ 2) := by
      ring
    rw [this, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity : 0 ≤ Q0 / L3 ^ 2)]
    exact add_le_add he hQ0L
  have hdiff : |X.re / L3 - r0 ^ 2 * l| ≤ |l| * ρ ^ 2 * Q + |l| * (e + ρ / L3) := by
    have : X.re / L3 - r0 ^ 2 * l =
        (X.re / L3 - l / L3 ^ 2 * (Q00 - Q0)) + (l / L3 ^ 2 * (Q00 - Q0) - r0 ^ 2 * l) := by ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add hre hD)
  have hVle := S1S2_abs_V_le hV (mom (LN N) u)
  have hV0 : 0 ≤ V0 V := (abs_nonneg _).trans hVle
  have hneg : (ft V (0 - mom (LN N) u)).re = (ft V (mom (LN N) u)).re := by
    rw [zero_sub, scat_ft_V_neg ‹PotentialHyp V›]
  rw [hneg, abs_mul, abs_mul]
  have hρl : |l| * ρ ≤ 1 := by
    rw [abs_mul, abs_of_pos hρ] at hrl
    linarith
  have h1 : |(ft V (mom (LN N) u)).re| * (|l| * ρ ^ 2 * Q) ≤ V0 V * ρ * Q := by
    have : |(ft V (mom (LN N) u)).re| * (|l| * ρ ^ 2 * Q) =
        |(ft V (mom (LN N) u)).re| * (|l| * ρ) * (ρ * Q) := by ring
    rw [this]
    have h0 : 0 ≤ ρ * Q := by positivity
    calc |(ft V (mom (LN N) u)).re| * (|l| * ρ) * (ρ * Q) ≤ V0 V * 1 * (ρ * Q) := by
          gcongr
      _ = V0 V * ρ * Q := by ring
  calc |(ft V (mom (LN N) u)).re| * |X.re / L3 - r0 ^ 2 * l|
      ≤ |(ft V (mom (LN N) u)).re| * (|l| * ρ ^ 2 * Q + |l| * (e + ρ / L3)) :=
        mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
    _ = |(ft V (mom (LN N) u)).re| * (|l| * ρ ^ 2 * Q) +
          |l| * |(ft V (mom (LN N) u)).re| * (e + ρ / L3) := by ring
    _ ≤ V0 V * ρ * Q + |l| * |(ft V (mom (LN N) u)).re| * (e + ρ / L3) := by linarith

/-- (7.7) [u-uPMH] with the summability of its series. -/
private lemma S1S2_IH_core {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      Summable (fun n : Idx => if inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n then
          (ft V (mom (LN N) n)).re *
            ((Expect.E4 (trialState V w kc N) n (-n) 0 0).re / LN N ^ 3 -
              rho0 (g0 V w) (rhoN N) ^ 2 * lam V w (rhoN N) (LN N) n) else 0) ∧
      |(LN N ^ 3)⁻¹ * (∑' n : Idx, if inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n then
          (ft V (mom (LN N) n)).re *
            ((Expect.E4 (trialState V w kc N) n (-n) 0 0).re / LN N ^ 3 -
              rho0 (g0 V w) (rhoN N) ^ 2 * lam V w (rhoN N) (LN N) n) else 0)|
        ≤ C * rhoN N ^ (5/2 + 1/400 : ℝ) := by
  have hg := scat_g0_pos hV hw
  have hV0 := (S1S2_V0_pos hV hw).le
  obtain ⟨Nr, hr⟩ := Pair_rho_lam_le V w
  obtain ⟨K, hK, NK, hKb⟩ := Pair_sum_lamV hV hw
  obtain ⟨CT, hCT, NT, hT⟩ := Thm5_1 hg
  obtain ⟨C6, hC6, N6, h6⟩ := Lemma5_6 hg
  refine ⟨V0 V * CT + K * (C6 + 1), by positivity, max (max Nr NK) (max (max NT N6) 1),
    fun N hN kc => ?_⟩
  have hNr : Nr ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNK : NK ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNT : NT ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hN
  have hN6 : N6 ≤ N := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨hq, -⟩ := hKb N hNK
  have hT1 := (hT N hNT kc).1
  have h6N := h6 N hN6 kc
  set Ψ := trialState V w kc N
  set ρ := rhoN N
  set L3 := LN N ^ 3 with hL3
  have hL3p : 0 < L3 := pow_pos hL 3
  set e := C6 * ρ ^ (5/2 + 1/400 : ℝ) + ρ / L3 with he
  have he0 : 0 ≤ e := by positivity
  set F : Idx → ℝ := fun n => if inPI ρ (LN N) n ∨ inPH ρ (LN N) n then
      (ft V (mom (LN N) n)).re * ((Expect.E4 Ψ n (-n) 0 0).re / L3 -
        rho0 (g0 V w) ρ ^ 2 * lam V w ρ (LN N) n) else 0 with hF
  set A : Idx → ℝ := fun n => if inPI ρ (LN N) n ∨ inPH ρ (LN N) n then
      Expect.Q Ψ [n] else 0 with hA
  set B : Idx → ℝ := fun n => if n ≠ 0 then
      |lam V w ρ (LN N) n * (ft V (0 - mom (LN N) n)).re| else 0 with hB
  have hQs := (Particles_hasSum_Q V w kc hN1).summable
  have hAs : Summable A := Summable.of_nonneg_of_le
    (fun n => by simp only [hA]; split_ifs; exacts [S1S2_Q_nonneg _ _, le_rfl])
    (fun n => by simp only [hA]; split_ifs; exacts [le_rfl, S1S2_Q_nonneg _ _]) hQs
  have hBs : Summable B := (hq 0).1
  have hpt : ∀ n, |F n| ≤ V0 V * ρ * A n + e * B n := by
    intro n
    simp only [hF, hA, hB]
    by_cases hn : inPI ρ (LN N) n ∨ inPH ρ (LN N) n
    · have hn0 : n ≠ 0 := by
        rcases hn with h | h
        · exact Regions_PI_ne_zero hρ h
        · exact Regions_PH_ne_zero hρ h
      rw [ite_eq_left hn, ite_eq_left hn, ite_eq_left hn0]
      have hrl := hr N hNr n (Or.inr hn)
      have := S1S2_IH_pt hV kc hN1 hn (e := C6 * ρ ^ (5/2 + 1/400 : ℝ)) h6N hrl
      calc _ ≤ _ := this
        _ = _ := by rw [he]; ring
    · rw [ite_eq_right hn, ite_eq_right hn, abs_zero, mul_zero, zero_add]
      split_ifs <;> positivity
  have hGs : Summable fun n => V0 V * ρ * A n + e * B n :=
    (hAs.mul_left _).add (hBs.mul_left _)
  have hFs : Summable F := Summable.of_norm_bounded hGs (fun n => by
    rw [Real.norm_eq_abs]
    exact hpt n)
  refine ⟨hFs, ?_⟩
  have hsum : |∑' n, F n| ≤ V0 V * ρ * (∑' n, A n) + e * (∑' n, B n) := by
    calc |∑' n, F n| = ‖∑' n, F n‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' n, ‖F n‖ := norm_tsum_le_tsum_norm hFs.norm
      _ ≤ ∑' n, (V0 V * ρ * A n + e * B n) :=
        Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hpt n) hFs.norm hGs
      _ = V0 V * ρ * (∑' n, A n) + e * (∑' n, B n) := by
        rw [Summable.tsum_add (hAs.mul_left _) (hBs.mul_left _), tsum_mul_left, tsum_mul_left]
  have hA1 : L3⁻¹ * (∑' n, A n) ≤ CT * ρ ^ (1/200 : ℝ) * ρ ^ (3/2 : ℝ) := by
    have e1 : L3⁻¹ * (∑' n, A n) =
        ρ ^ (3/2 : ℝ) * (ρ ^ (-(3/2 : ℝ)) * L3⁻¹ * (∑' n, A n)) := by
      rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hρ]
      norm_num
    rw [e1, mul_comm (CT * _)]
    exact mul_le_mul_of_nonneg_left hT1 (by positivity)
  have hB1 : L3⁻¹ * (∑' n, B n) ≤ K := (hq 0).2
  have hp1 := S1S2_pow_IH hρ hρ1
  have hp2 := S1S2_rho_div_L3_le hN1
  have hpos : 0 ≤ ρ ^ (5/2 + 1/400 : ℝ) := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.2 hL3p)]
  calc L3⁻¹ * |∑' n, F n| ≤ L3⁻¹ * (V0 V * ρ * (∑' n, A n) + e * (∑' n, B n)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = V0 V * ρ * (L3⁻¹ * (∑' n, A n)) + e * (L3⁻¹ * (∑' n, B n)) := by ring
    _ ≤ V0 V * ρ * (CT * ρ ^ (1/200 : ℝ) * ρ ^ (3/2 : ℝ)) + e * K := by
        gcongr
    _ = V0 V * CT * (ρ * ρ ^ (1/200 : ℝ) * ρ ^ (3/2 : ℝ)) +
          K * (C6 * ρ ^ (5/2 + 1/400 : ℝ) + ρ / L3) := by rw [he]; ring
    _ ≤ V0 V * CT * ρ ^ (5/2 + 1/400 : ℝ) +
          K * (C6 * ρ ^ (5/2 + 1/400 : ℝ) + ρ ^ (5/2 + 1/400 : ℝ)) := by
        gcongr
    _ = (V0 V * CT + K * (C6 + 1)) * ρ ^ (5/2 + 1/400 : ℝ) := by ring

/-! ### `P_L`: (7.8) [u-uPL] -/

/-- A function on `Λ*` supported in `{|u| ≤ R}` is summable. -/
private lemma S1S2_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
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

/-- `Q_Ψ({u, m}) ≥ 0`. -/
private lemma S1S2_Qm_nonneg (Ψ : Occ → ℂ) (um : List (Idx × ℕ)) : 0 ≤ Expect.Qm Ψ um :=
  tsum_nonneg fun _ => by split_ifs <;> positivity

/-- `m ↦ Q_Ψ({u, m})` is summable. -/
private lemma S1S2_Qm_summable (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    Summable fun m : ℕ => Expect.Qm (trialState V w kc N) [(u, m)] := by
  have h1 := Expect.tsum_Qm_single N _ (Normalization_isNState V w kc hN) u
  by_contra hc
  rw [tsum_eq_zero_of_not_summable hc] at h1
  norm_num at h1

/-- `m Q_Ψ({u, m}) ≤ N Q_Ψ({u, m})`: the event `α(u) = m` is empty for `m > N`. -/
private lemma S1S2_mQm_le (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) (m : ℕ) :
    (m : ℝ) * Expect.Qm (trialState V w kc N) [(u, m)] ≤
      N * Expect.Qm (trialState V w kc N) [(u, m)] := by
  have h0 := S1S2_Qm_nonneg (trialState V w kc N) [(u, m)]
  by_cases hm : m ≤ N
  · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hm) h0
  · have hz : Expect.Qm (trialState V w kc N) [(u, m)] = 0 := by
      unfold Expect.Qm
      refine (tsum_congr (g := fun _ : Occ => (0 : ℝ)) fun α => ?_).trans tsum_zero
      split_ifs with hα
      · have hu : α u = m := by simpa [Expect.Ev] using hα
        by_cases hz : trialState V w kc N α = 0
        · rw [hz, norm_zero]
          ring
        · exfalso
          have h1 : α u ≤ α.num := by
            by_cases hs : u ∈ α.support
            · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hs
            · rw [Finsupp.notMem_support_iff.mp hs]
              exact Nat.zero_le _
          rw [(Normalization_isNState V w kc hN).2 α hz] at h1
          omega
      · rfl
    rw [hz, mul_zero, mul_zero]

/-- The tail of (7.18) in the range `m_c ≤ m + 2` is at most its `m`-weighted form (the left
side of (5.57) [ubpsiuPLmc]) when `m_c ≥ 3`. -/
private lemma S1S2_tail_le (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx)
    (hmc : 3 ≤ mc (rhoN N)) :
    (∑' m : ℕ, if mc (rhoN N) ≤ (m : ℝ) + 2 then
        Expect.Qm (trialState V w kc N) [(u, m)] else 0) ≤
      ∑' m : ℕ, (if mc (rhoN N) ≤ (m : ℝ) + 2 then
        (m : ℝ) * Expect.Qm (trialState V w kc N) [(u, m)] else 0) := by
  have hs := S1S2_Qm_summable V w kc hN u
  have h1 : Summable fun m : ℕ => if mc (rhoN N) ≤ (m : ℝ) + 2 then
      Expect.Qm (trialState V w kc N) [(u, m)] else 0 :=
    Summable.of_nonneg_of_le (fun m => by split_ifs <;> simp [S1S2_Qm_nonneg])
      (fun m => by split_ifs <;> simp [S1S2_Qm_nonneg]) hs
  have h2 : Summable fun m : ℕ => if mc (rhoN N) ≤ (m : ℝ) + 2 then
      (m : ℝ) * Expect.Qm (trialState V w kc N) [(u, m)] else 0 :=
    Summable.of_nonneg_of_le
      (fun m => by split_ifs <;> simp [S1S2_Qm_nonneg, mul_nonneg])
      (fun m => by
        split_ifs
        · exact S1S2_mQm_le V w kc hN u m
        · exact mul_nonneg (Nat.cast_nonneg _) (S1S2_Qm_nonneg _ _))
      (hs.mul_left (N : ℝ))
  refine Summable.tsum_le_tsum (fun m => ?_) h1 h2
  split_ifs with h
  · have hm : (1 : ℝ) ≤ m := by linarith
    have := S1S2_Qm_nonneg (trialState V w kc N) [(u, m)]
    nlinarith
  · exact le_rfl

/-- The algebra of (7.16) [temp8.24]–(7.22) [temp8.29]: from the bound (7.18) with `λ < 0`,
the lower bound (5.58) [lbpsiuPL0] of the weighted sum, the tail bound
`T ≤ ρ^{η/2} x/(1 − x)` of (5.57) [ubpsiuPLmc] and the bound on `Q_Ψ(0,0)/|Λ|² − ρ₀²`. -/
private lemma S1S2_PL_alg {L3 ρ N l X A D T Q00 Q0 r0 y C b t e6 : ℝ}
    (hL3 : 0 < L3) (hρ : 0 < ρ) (hN : ρ * L3 = N) (hl : l < 0) (hρl : |ρ * l| ≤ 1)
    (hX : X ≤ l / L3 * (A + D - N ^ 2 * T))
    (hA : N ^ 2 * y * (1 - C * b - t) ≤ A) (hT : T ≤ y * b)
    (hD : D = Q00 - Q0) (h6 : |Q00 / L3 ^ 2 - r0 ^ 2| ≤ e6) (hQ0N : Q0 ≤ N)
    (hr0 : 0 ≤ r0) (hr0ρ : r0 ≤ ρ) (hy : 0 ≤ y) (hC : 0 ≤ C) (hb : 0 ≤ b) (ht : 0 ≤ t) :
    X / L3 ≤ r0 ^ 2 * (l + l * y) + ρ * y * ((C + 1) * b + t) + |l| * (e6 + ρ / L3) := by
  have hL32 : 0 < L3 ^ 2 := by positivity
  have hk : l / L3 ^ 2 < 0 := div_neg_of_neg_of_pos hl hL32
  have hNL : N ^ 2 / L3 ^ 2 = ρ ^ 2 := by
    rw [← hN]
    field_simp
  have s0 : X / L3 ≤ l / L3 ^ 2 * (A + D - N ^ 2 * T) := by
    refine (div_le_div_of_nonneg_right hX hL3.le).trans (le_of_eq ?_)
    field_simp
  have s1 : l / L3 ^ 2 * A ≤ l * ρ ^ 2 * y * (1 - C * b - t) := by
    have := mul_le_mul_of_nonpos_left hA hk.le
    refine this.trans (le_of_eq ?_)
    rw [← hNL]
    ring
  have s2 : l / L3 ^ 2 * (-(N ^ 2 * T)) ≤ -l * ρ ^ 2 * (y * b) := by
    have e : l / L3 ^ 2 * (-(N ^ 2 * T)) = -l * (N ^ 2 / L3 ^ 2) * T := by ring
    rw [e, hNL]
    exact mul_le_mul_of_nonneg_left hT (by nlinarith)
  have hQ0L : Q0 / L3 ^ 2 ≤ ρ / L3 := by
    rw [div_le_div_iff₀ hL32 hL3]
    rw [← hN] at hQ0N
    nlinarith
  have s3 : l / L3 ^ 2 * D ≤ l * r0 ^ 2 + -l * e6 + -l * (ρ / L3) := by
    have e : l / L3 ^ 2 * D = l * r0 ^ 2 + l * (Q00 / L3 ^ 2 - r0 ^ 2) + -l * (Q0 / L3 ^ 2) := by
      rw [hD]
      ring
    rw [e]
    have h1 : l * (Q00 / L3 ^ 2 - r0 ^ 2) ≤ -l * e6 := by
      have := le_abs_self (l * (Q00 / L3 ^ 2 - r0 ^ 2))
      rw [abs_mul, abs_of_neg hl] at this
      exact this.trans (mul_le_mul_of_nonneg_left h6 (by linarith))
    have h2 : -l * (Q0 / L3 ^ 2) ≤ -l * (ρ / L3) := mul_le_mul_of_nonneg_left hQ0L (by linarith)
    linarith
  have s4 : l * ρ ^ 2 * y ≤ l * r0 ^ 2 * y := by
    have h1 : r0 ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr0 hr0ρ 2
    have h2 : l * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hl.le hy
    nlinarith
  have s5 : -l * ρ ^ 2 ≤ ρ := by
    rw [abs_mul, abs_of_pos hρ, abs_of_neg hl] at hρl
    nlinarith
  have hY : 0 ≤ y * ((C + 1) * b + t) := by positivity
  have s5' : -l * ρ ^ 2 * (y * ((C + 1) * b + t)) ≤ ρ * (y * ((C + 1) * b + t)) :=
    mul_le_mul_of_nonneg_right s5 hY
  calc X / L3 ≤ l / L3 ^ 2 * (A + D - N ^ 2 * T) := s0
    _ = l / L3 ^ 2 * A + l / L3 ^ 2 * D + l / L3 ^ 2 * (-(N ^ 2 * T)) := by ring
    _ ≤ l * ρ ^ 2 * y * (1 - C * b - t) + (l * r0 ^ 2 + -l * e6 + -l * (ρ / L3)) +
          -l * ρ ^ 2 * (y * b) := add_le_add (add_le_add s1 s3) s2
    _ = l * ρ ^ 2 * y + l * r0 ^ 2 + -l * ρ ^ 2 * (y * ((C + 1) * b + t)) +
          -l * (e6 + ρ / L3) := by ring
    _ ≤ l * r0 ^ 2 * y + l * r0 ^ 2 + ρ * (y * ((C + 1) * b + t)) + -l * (e6 + ρ / L3) :=
        add_le_add (add_le_add (add_le_add s4 le_rfl) s5') le_rfl
    _ = r0 ^ 2 * (l + l * y) + ρ * y * ((C + 1) * b + t) + |l| * (e6 + ρ / L3) := by
        rw [abs_of_neg hl]
        ring

/-- On `P_L` (Definition 3.1 [def1]), with `|Re ĝ_p| ≤ C_g`: `λ_u < 0`, `|ρλ_u| ≤ 1`,
`0 < 1 − x_u`, `x_u/(1 − x_u) ≥ 0`, `|λ_u| ≤ ρ⁻¹` and
`|λ_u/(1 − x_u) + w_u| ≤ (1 + √g₀ + C_g) ρ^{-1} ε^{-2}`, `x_u = (ρλ_u)²`, `ε = ρ^{1/200}`. -/
private lemma S1S2_PL_facts {V w : R3 → ℝ} (hg : 0 < g0 V w) {ρ L Cg : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hgd : ∀ p, |(ft (gfun V w) p).re| ≤ Cg) {n : Idx} (hn : inPL ρ L n) :
    lam V w ρ L n < 0 ∧ |ρ * lam V w ρ L n| ≤ 1 ∧ 0 < 1 - (ρ * lam V w ρ L n) ^ 2 ∧
      0 ≤ (ρ * lam V w ρ L n) ^ 2 / (1 - (ρ * lam V w ρ L n) ^ 2) ∧
      |lam V w ρ L n| ≤ ρ⁻¹ ∧
      |lam V w ρ L n / (1 - (ρ * lam V w ρ L n) ^ 2) + wmom V w (mom L n)| ≤
        (1 + Real.sqrt (g0 V w) + Cg) * (ρ ^ (-1 : ℝ) * ρ ^ (-(2/200) : ℝ)) := by
  obtain ⟨h1, h2⟩ := Particles_rho_lam_PL hg hρ hρ1 hn
  set l := lam V w ρ L n
  have hε0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hs0 : 0 ≤ Real.sqrt (g0 V w) := Real.sqrt_nonneg _
  have he1 : 0 < epsP ρ / (1 + Real.sqrt (g0 V w)) := by positivity
  have hl : l < 0 := by
    by_contra h
    push Not at h
    have := mul_nonneg hρ.le h
    linarith
  have hr1 : -1 < ρ * l := by linarith
  have habs : |ρ * l| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
  have hx : epsP ρ / (1 + Real.sqrt (g0 V w)) ≤ 1 - (ρ * l) ^ 2 := by nlinarith
  have hx0 : 0 < 1 - (ρ * l) ^ 2 := he1.trans_le hx
  have hlr : |l| ≤ ρ⁻¹ := by
    have e : |l| = |ρ * l| / ρ := by
      rw [abs_mul, abs_of_pos hρ]
      field_simp
    rw [e, inv_eq_one_div]
    exact div_le_div_of_nonneg_right habs hρ.le
  refine ⟨hl, habs, hx0, div_nonneg (sq_nonneg _) hx0.le, hlr, ?_⟩
  have hCg : 0 ≤ Cg := (abs_nonneg _).trans (hgd 0)
  set E := epsP ρ with hE
  have hpn : E * ρ ^ (1/2 : ℝ) ≤ ‖mom L n‖ := hn.1
  have hsq : (ρ ^ (1/2 : ℝ)) ^ 2 = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have hε2 : E ^ 2 = ρ ^ (2/200 : ℝ) := by
    rw [hE, epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have hpos : 0 < E ^ 2 * ρ := by positivity
  have hp2 : E ^ 2 * ρ ≤ ‖mom L n‖ ^ 2 := by
    calc E ^ 2 * ρ = (E * ρ ^ (1/2 : ℝ)) ^ 2 := by rw [mul_pow, hsq]
      _ ≤ ‖mom L n‖ ^ 2 := pow_le_pow_left₀ (by positivity) hpn 2
  have hw : |wmom V w (mom L n)| ≤ Cg / (E ^ 2 * ρ) := by
    unfold wmom
    rw [abs_div, abs_of_nonneg (sq_nonneg ‖mom L n‖)]
    calc |(ft (gfun V w) (mom L n)).re| / ‖mom L n‖ ^ 2 ≤ Cg / ‖mom L n‖ ^ 2 :=
          div_le_div_of_nonneg_right (hgd _) (sq_nonneg _)
      _ ≤ Cg / (E ^ 2 * ρ) := div_le_div_of_nonneg_left hCg hpos hp2
  have hl1 : |l / (1 - (ρ * l) ^ 2)| ≤ ρ⁻¹ * (1 + Real.sqrt (g0 V w)) / E := by
    rw [abs_div, abs_of_pos hx0]
    calc |l| / (1 - (ρ * l) ^ 2) ≤ ρ⁻¹ / (1 - (ρ * l) ^ 2) :=
          div_le_div_of_nonneg_right hlr hx0.le
      _ ≤ ρ⁻¹ / (E / (1 + Real.sqrt (g0 V w))) :=
          div_le_div_of_nonneg_left (by positivity) he1 hx
      _ = ρ⁻¹ * (1 + Real.sqrt (g0 V w)) / E := by field_simp
  have hEE : E⁻¹ ≤ (E ^ 2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
  have h3 : ρ⁻¹ * (1 + Real.sqrt (g0 V w)) / E ≤ (1 + Real.sqrt (g0 V w)) * (ρ⁻¹ * (E ^ 2)⁻¹) := by
    rw [div_eq_mul_inv, mul_comm ρ⁻¹, mul_assoc]
    gcongr
  have h4 : Cg / (E ^ 2 * ρ) = Cg * (ρ⁻¹ * (E ^ 2)⁻¹) := by
    field_simp
  calc |l / (1 - (ρ * l) ^ 2) + wmom V w (mom L n)|
      ≤ |l / (1 - (ρ * l) ^ 2)| + |wmom V w (mom L n)| := abs_add_le _ _
    _ ≤ (1 + Real.sqrt (g0 V w)) * (ρ⁻¹ * (E ^ 2)⁻¹) + Cg * (ρ⁻¹ * (E ^ 2)⁻¹) := by
        rw [← h4]
        exact add_le_add (hl1.trans h3) hw
    _ = (1 + Real.sqrt (g0 V w) + Cg) * (ρ ^ (-1 : ℝ) * ρ ^ (-(2/200) : ℝ)) := by
        rw [Real.rpow_neg_one, Real.rpow_neg hρ.le, ← hε2]
        ring

/-- `ε^{-1}ρ^{1/2} = ρ^{1/2 − 1/200}`, the outer radius of `P_L`. -/
private lemma S1S2_R_eq {ρ : ℝ} (hρ : 0 < ρ) :
    (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) = ρ ^ (1/2 - 1/200 : ℝ) := by
  rw [epsP, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
  norm_num

/-- Exponent count of the `V_u → V₀` error on `P_L`: `R · ρ² · ρ^{-1}ε^{-2} · R³ ≤ ρ^{5/2+1/400}`
with `R = ρ^{1/2−1/200}`. -/
private lemma S1S2_pow_Q1 {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ (1/2 - 1/200 : ℝ) * ρ ^ 2 * (ρ ^ (-1 : ℝ) * ρ ^ (-(2/200) : ℝ)) *
        ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ) ≤ ρ ^ (5/2 + 1/400 : ℝ) := by
  rw [← Real.rpow_natCast ρ 2]
  simp only [← Real.rpow_add hρ]
  exact S1S2_rpow_le hρ hρ1 (by norm_num)

/-- Exponent count of the `Q_Ψ(0,0)` error on `P_L`: `ρ⁻¹ ρ^{5/2+1/400} R³ ≤ ρ^{5/2+1/400}`. -/
private lemma S1S2_pow_Q2 {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ⁻¹ * ρ ^ (5/2 + 1/400 : ℝ) * ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ) ≤
      ρ ^ (5/2 + 1/400 : ℝ) := by
  rw [← Real.rpow_neg_one]
  simp only [← Real.rpow_add hρ]
  exact S1S2_rpow_le hρ hρ1 (by norm_num)

/-- Exponent count of the `Q_Ψ(0)` error on `P_L`: `ρ⁻¹ ρ^{33/8} R³ ≤ ρ^{5/2+1/400}`. -/
private lemma S1S2_pow_Q3 {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ⁻¹ * ρ ^ (33/8 : ℝ) * ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ) ≤ ρ ^ (5/2 + 1/400 : ℝ) := by
  rw [← Real.rpow_neg_one]
  simp only [← Real.rpow_add hρ]
  exact S1S2_rpow_le hρ hρ1 (by norm_num)

/-- `(1 + 2√m_c)^{-2} ≤ ρ^{1/400}`, `m_c = ρ^{-1/200}`. -/
private lemma S1S2_tau1 {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (1 + 2 * Real.sqrt (mc ρ)) ^ (-2 : ℝ) ≤ ρ ^ (1/400 : ℝ) := by
  have hm : 0 < mc ρ := Real.rpow_pos_of_pos hρ _
  have hs := Real.sq_sqrt hm.le
  have hs0 := Real.sqrt_nonneg (mc ρ)
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  have h1 : 4 * mc ρ ≤ (1 + 2 * Real.sqrt (mc ρ)) ^ 2 := by nlinarith
  have h2 : ((1 + 2 * Real.sqrt (mc ρ)) ^ 2)⁻¹ ≤ (4 * mc ρ)⁻¹ := inv_anti₀ (by positivity) h1
  have h3 : (mc ρ)⁻¹ = ρ ^ (1/200 : ℝ) := by
    rw [mc, Real.rpow_neg hρ.le, inv_inv]
  have h4 : ρ ^ (1/200 : ℝ) ≤ ρ ^ (1/400 : ℝ) := S1S2_rpow_le hρ hρ1 (by norm_num)
  have h5 : (4 * mc ρ)⁻¹ = (mc ρ)⁻¹ / 4 := by rw [mul_inv]; ring
  have h6 : 0 ≤ ρ ^ (1/200 : ℝ) := by positivity
  rw [h5, h3] at h2
  linarith

/-- `2π/(L_N ρ_N^{1/2}) ≤ 2π ρ_N^{1/400}`. -/
private lemma S1S2_tau2 {N : ℕ} (hN : 1 ≤ N) :
    2 * π / (LN N * rhoN N ^ (1/2 : ℝ)) ≤ 2 * π * rhoN N ^ (1/400 : ℝ) := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  rw [S1S2_L_sqrt hN, Real.rpow_neg hρ.le, div_inv_eq_mul]
  exact mul_le_mul_of_nonneg_left (S1S2_rpow_le hρ hρ1 (by norm_num)) (by positivity)

/-- `ρ^{1/2} ρ² = ρ^{5/2}`. -/
private lemma S1S2_pow_52a {ρ : ℝ} (hρ : 0 < ρ) : ρ ^ 2 * ρ ^ (1/2 : ℝ) = ρ ^ (5/2 : ℝ) := by
  rw [← Real.rpow_natCast ρ 2, ← Real.rpow_add hρ]
  norm_num

/-- `ρ ρ^{3/2} = ρ^{5/2}`. -/
private lemma S1S2_pow_52b {ρ : ℝ} (hρ : 0 < ρ) : ρ * ρ ^ (3/2 : ℝ) = ρ ^ (5/2 : ℝ) := by
  conv_lhs => arg 1; rw [← Real.rpow_one ρ]
  rw [← Real.rpow_add hρ]
  norm_num

/-! ### Outside `P` -/

/-- For `u ≠ 0` outside `P = P_L ∪ P_I ∪ P_H`, `⟨a†_u a†_{−u} a_0 a_0⟩_Ψ = 0`: the state
`𝓐^u α` has `u` occupied, so it is not in `M` (Definition 3.4 [M]). -/
private lemma S1S2_E4_zero (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {u : Idx} (hu : u ≠ 0)
    (hP : ¬ inP (rhoN N) (LN N) u) :
    Expect.E4 (trialState V w kc N) u (-u) 0 0 = 0 := by
  unfold Expect.E4
  refine (tsum_congr (g := fun _ : Occ => (0 : ℂ)) fun α => ?_).trans tsum_zero
  have hsnd : (a4 u (-u) 0 0 α).2 = strictPair u α := by
    unfold a4 strictPair
    simp only
    ext n
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  have hne : strictPair u α u ≠ 0 := by
    simp [strictPair, Finsupp.single_apply, Ne.symm hu]
  have hM : ¬ InM (rhoN N) (LN N) kc N (strictPair u α) := fun h => by
    rcases MBasic_support h u hne with h0 | h1
    · exact hu h0
    · exact hP h1
  have hz : trialState V w kc N (strictPair u α) = 0 := by
    unfold trialState
    simp [hM]
  rw [hsnd, hz, map_zero, zero_mul, zero_mul]

/-! ## Statements -/

/-- Lemma 4.2 [lemHS1], (4.9) [proofthem1-2]. -/
theorem Lemma4_2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma4_2 V w := by
  have hg := scat_g0_pos hV hw
  have hV0 := (S1S2_V0_pos hV hw).le
  obtain ⟨C6, hC6, N6, h6⟩ := Lemma5_6 hg
  obtain ⟨N1, h1⟩ := eventually_atTop.1
    ((eventually_ge_atTop 1).and (S1S2_ev_small ((3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ))
      (b := 1/2) (by norm_num)))
  let E : ℝ → ℕ → ℝ := fun kc N => if h : 1 ≤ N then
    (Eq7_2 hV (S1S2_one_le_L h) (Normalization_isNState V w kc h)).choose else 0
  refine ⟨E, fun kc => ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [E, hN, ↓reduceDIte]
    exact (Eq7_2 hV (S1S2_one_le_L hN) (Normalization_isNState V w kc hN)).choose_spec.1
  refine S1S2_limsup2_le _ _ (V0 V * C6) (1/400) (by norm_num) (max N1 N6) (fun kc N hN => ?_)
  obtain ⟨hN1, hs⟩ := h1 N (le_of_max_le_left hN)
  have h6N := h6 N (le_of_max_le_right hN) kc
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨-, -, -, hd⟩ := S1S2_rho0 hg.le hρ (by simpa [mul_assoc] using hs)
  have hE := (Eq7_2 hV (S1S2_one_le_L hN1) (Normalization_isNState V w kc hN1)).choose_spec.2
  have hEN : E kc N = (Eq7_2 hV (S1S2_one_le_L hN1)
      (Normalization_isNState V w kc hN1)).choose := by simp only [E, hN1, ↓reduceDIte]
  rw [← hEN] at hE
  set ρ := rhoN N
  set L3 := LN N ^ 3 with hL3
  have hL3p : 0 < L3 := pow_pos hL 3
  have hp : 0 < ρ ^ (5/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  set Q00 := Expect.Q (trialState V w kc N) [0, 0]
  set r0 := rho0 (g0 V w) ρ
  have hNc : (N : ℝ) = ρ * L3 := hρL.symm
  have hEL : E kc N / L3 ≤ V0 V * (2 * ρ ^ 2 - ρ / L3 - Q00 / L3 ^ 2) := by
    have : E kc N / L3 ≤ L3⁻¹ * V0 V * (2 * (N : ℝ) ^ 2 - N - Q00) / L3 :=
      div_le_div_of_nonneg_right hE hL3p.le
    refine this.trans (le_of_eq ?_)
    rw [hNc]
    field_simp
  have hab := abs_le.1 h6N
  have h52 : ρ ^ (5/2 + 1/400 : ℝ) = ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ) := Real.rpow_add hρ _ _
  have hρL3 : 0 ≤ ρ / L3 := by positivity
  unfold Section4.excess
  rw [div_le_iff₀ hp]
  have key : E kc N / L3 - V0 V * r0 ^ 2 ≤
      V0 V * (2 * (ρ ^ 2 - r0 ^ 2) + (r0 ^ 2 - Q00 / L3 ^ 2)) := by
    nlinarith
  have hb : 2 * (ρ ^ 2 - r0 ^ 2) + (r0 ^ 2 - Q00 / L3 ^ 2) ≤
      4 * (g0 V w ^ (3/2 : ℝ) / π ^ 2) / 3 * ρ ^ (5/2 : ℝ) +
        C6 * (ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ)) := by
    rw [← S1S2_const, ← h52]
    nlinarith
  calc E kc N / L3 - V0 V * r0 ^ 2
      ≤ V0 V * (2 * (ρ ^ 2 - r0 ^ 2) + (r0 ^ 2 - Q00 / L3 ^ 2)) := key
    _ ≤ V0 V * (4 * (g0 V w ^ (3/2 : ℝ) / π ^ 2) / 3 * ρ ^ (5/2 : ℝ) +
          C6 * (ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ))) := mul_le_mul_of_nonneg_left hb hV0
    _ = (4 * V0 V * Section4.G V w / 3 + V0 V * C6 * ρ ^ (1/400 : ℝ)) * ρ ^ (5/2 : ℝ) := by
        unfold Section4.G
        ring

/-- (7.7) [u-uPMH] of Lemma 7.2 [symno20] with a rate uniform in `k_c`:
`||Λ|⁻¹ Σ_{u ∈ P_I ∪ P_H} (V_u|Λ|⁻¹⟨a†_u a†_{−u} a_0 a_0⟩_Ψ − ρ₀² V_u λ_u)| ≤ Cρ^{5/2+η/2}`. -/
theorem Eq7_7 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      |(LN N ^ 3)⁻¹ * (∑' n : Idx, if inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n then
          (ft V (mom (LN N) n)).re *
            ((Expect.E4 (trialState V w kc N) n (-n) 0 0).re / LN N ^ 3 -
              rho0 (g0 V w) (rhoN N) ^ 2 * lam V w (rhoN N) (LN N) n) else 0)|
        ≤ C * rhoN N ^ (5/2 + 1/400 : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := S1S2_IH_core hV hw
  exact ⟨C, hC, N₀, fun N hN kc => (h N hN kc).2⟩

/-- (7.8) [u-uPL] of Lemma 7.2 [symno20] with a rate uniform in `k_c`:
`|Λ|⁻¹ Σ_{u ∈ P_L} (V_u|Λ|⁻¹⟨a†_u a†_{−u} a_0 a_0⟩_Ψ + ρ₀² V_u w_u) ≤ (V₀g₀^{3/2}/π² + Cρ^{η/2})ρ^{5/2}`. -/
theorem Eq7_8 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      (LN N ^ 3)⁻¹ * (∑' n : Idx, if inPL (rhoN N) (LN N) n then
          (ft V (mom (LN N) n)).re *
            ((Expect.E4 (trialState V w kc N) n (-n) 0 0).re / LN N ^ 3 +
              rho0 (g0 V w) (rhoN N) ^ 2 * wmom V w (mom (LN N) n)) else 0)
        ≤ (V0 V * Section4.G V w + C * rhoN N ^ (1/400 : ℝ)) * rhoN N ^ (5/2 : ℝ) := by
  have hg := scat_g0_pos hV hw
  have hV0p := S1S2_V0_pos hV hw
  have hV0 := hV0p.le
  obtain ⟨C58, hC58, N58, h58⟩ := Eq5_58 hg
  obtain ⟨N57, h57⟩ := Eq5_57 hg
  obtain ⟨C6, hC6, N6, h6⟩ := Lemma5_6 hg
  obtain ⟨Cp, hCp, Np, hpot⟩ := Pair_sum_PL_pot hV hw
  obtain ⟨K1, hK1, hocc⟩ := sum_PL_occ hg
  obtain ⟨Kt, hKt, htail⟩ := sum_PL_tail hg
  obtain ⟨K0, hK0, hcnt⟩ := sum_norm_rpow_le (s := 0) (by norm_num)
  obtain ⟨CV, hVd, hgd⟩ := Bridge_momDecay hV hw 0
  have hVb : ∀ p, |(ft V p).re| ≤ CV := fun p => by simpa using hVd.bound p
  have hgb : ∀ p, |(ft (gfun V w) p).re| ≤ CV := fun p => by simpa using hgd.bound p
  have hVlip : ∀ q : R3, ‖q‖ ≤ 1 → |(ft V q).re - V0 V| ≤ CV * ‖q‖ := fun q hq => by
    have := hVd.lip 0 q (by simpa using hq)
    simpa [V0] using this
  have hCV : 0 ≤ CV := (abs_nonneg _).trans (hVb 0)
  set c := g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set Cq := 1 + Real.sqrt (g0 V w) + CV with hCq
  have hCq0 : 0 ≤ Cq := by positivity
  obtain ⟨Ne, hev⟩ := eventually_atTop.1
    (((eventually_ge_atTop 1).and (S1S2_ev_large 3 (a := 1/200) (by norm_num))).and
      (((S1S2_ev_small ((3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ)) (b := 1/2) (by norm_num)).and
        (S1S2_ev_small (CV / V0 V) (b := 1/2 - 1/200) (by norm_num))).and
        (S1S2_ev_large (2 * π) (a := 13/24) (by norm_num))))
  refine ⟨V0 V * Cp + V0 V * (C58 + 1) * (c + 2 * K1) + V0 V * Kt * (1 + 2 * π) +
      K0 * (CV * Cq + V0 V * C6 + V0 V), by positivity,
    max (max (max N58 N57) (max N6 Np)) Ne, fun N hN kc => ?_⟩
  have hN58 : N58 ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))) hN
  have hN57 : N57 ≤ N := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))) hN
  have hN6 : N6 ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_left _ _))) hN
  have hNp : Np ≤ N := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_left _ _))) hN
  obtain ⟨⟨hN1, hmc⟩, ⟨hs, hCVR⟩, hL13⟩ := hev N (le_trans (le_max_right _ _) hN)
  obtain ⟨hρL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hLs : 2 * π ≤ LN N * rhoN N ^ (1/2 : ℝ) := by
    rw [S1S2_L_sqrt hN1]
    exact hL13
  have hτ2 := S1S2_tau2 hN1
  have hρL3 := S1S2_rho_div_L3 hN1
  have h6N := h6 N hN6 kc
  have hpotN := (abs_le.1 (hpot N hNp)).2
  have hoccN := (abs_le.1 (hocc (rhoN N) (LN N) hρ hρ1 hLs)).2
  have htailN := htail (2 * Real.sqrt (mc (rhoN N))) (rhoN N) (LN N) (by positivity) hρ hLs
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set L3 := L ^ 3 with hL3
  have hL3p : 0 < L3 := pow_pos hL 3
  obtain ⟨hr00, hr0ρ, -, -⟩ := S1S2_rho0 hg.le hρ (by simpa [mul_assoc] using hs)
  set r0 := rho0 (g0 V w) ρ with hr0
  set Ψ := trialState V w kc N with hΨ
  set R := ρ ^ (1/2 - 1/200 : ℝ) with hR
  have hR0 : 0 < R := Real.rpow_pos_of_pos hρ _
  have hR1 : R ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hsR : ρ ^ (1/2 : ℝ) ≤ R := S1S2_rpow_le hρ hρ1 (by norm_num)
  have hLR : 2 * π ≤ L * R := hLs.trans (mul_le_mul_of_nonneg_left hsR hL.le)
  have hCVR' : CV * R ≤ V0 V := by
    rw [div_mul_eq_mul_div, div_le_one hV0p] at hCVR
    exact hCVR
  have hPLR : ∀ n, inPL ρ L n → ‖mom L n‖ ≤ R := fun n hn => by
    have := hn.2
    rwa [S1S2_R_eq hρ] at this
  set b := ρ ^ (1/400 : ℝ) with hb
  have hb0 : 0 ≤ b := by positivity
  set e6 := C6 * ρ ^ (5/2 + 1/400 : ℝ) with he6
  set E6 := e6 + ρ / L3 with hE6
  have hE60 : 0 ≤ E6 := by positivity
  set Mp := Cq * (ρ ^ (-1 : ℝ) * ρ ^ (-(2/200) : ℝ)) with hMp
  have hMp0 : 0 ≤ Mp := by positivity
  set M := CV * R * ρ ^ 2 * Mp + V0 V * ρ⁻¹ * E6 with hM
  have hM0 : 0 ≤ M := by positivity
  set F : Idx → ℝ := fun n => if inPL ρ L n then
      (ft V (mom L n)).re * ((Expect.E4 Ψ n (-n) 0 0).re / L3 + r0 ^ 2 * wmom V w (mom L n))
      else 0 with hF
  set H1 : Idx → ℝ := fun n => if inPL ρ L n then
      lam V w ρ L n / (1 - (ρ * lam V w ρ L n) ^ 2) + wmom V w (mom L n) else 0 with hH1
  set H2 : Idx → ℝ := fun n => if inPL ρ L n then
      (ρ * lam V w ρ L n) ^ 2 / (1 - (ρ * lam V w ρ L n) ^ 2) else 0 with hH2
  set H3 : Idx → ℝ := fun n => if inPL ρ L n then
      |ρ * lam V w ρ L n| ^ (2 * Real.sqrt (mc ρ)) *
        ((ρ * lam V w ρ L n) ^ 2 / (1 - (ρ * lam V w ρ L n) ^ 2)) else 0 with hH3
  set H4 : Idx → ℝ := fun n => if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-(0 : ℝ)) else 0
    with hH4
  have hball : ∀ g : Idx → ℝ, (∀ n, ¬ inPL ρ L n → g n = 0) → Summable g := fun g hg0 =>
    S1S2_summable_ball hL g (fun n hn => by
      by_contra h
      exact hn (hg0 n (fun hp => h (hPLR n hp))))
  have hFs : Summable F := hball F (fun n hn => by simp only [hF, ite_eq_right hn])
  have hH1s : Summable H1 := hball H1 (fun n hn => by simp only [hH1, ite_eq_right hn])
  have hH2s : Summable H2 := hball H2 (fun n hn => by simp only [hH2, ite_eq_right hn])
  have hH3s : Summable H3 := hball H3 (fun n hn => by simp only [hH3, ite_eq_right hn])
  have hH4s : Summable H4 := S1S2_summable_ball hL H4 (fun n hn => by
    by_contra h
    exact hn (by simp only [hH4]; rw [ite_eq_right (fun h' => h h'.2)]))
  have hpt : ∀ n, F n ≤ V0 V * r0 ^ 2 * H1 n + V0 V * ρ * ((C58 + 1) * b) * H2 n +
      V0 V * ρ * H3 n + M * H4 n := by
    intro n
    by_cases hn : inPL ρ L n
    · have hn0 : n ≠ 0 := Regions_PL_ne_zero hρ hn
      have hnR := hPLR n hn
      simp only [hF, hH1, hH2, hH3, hH4, ite_eq_left hn, ite_eq_left (And.intro hn0 hnR), neg_zero,
        Real.rpow_zero, mul_one]
      obtain ⟨hl, hρl, hx0, hy, hlr, hpb⟩ := S1S2_PL_facts hg hρ hρ1 hgb hn
      have hX := Eq7_17 hg kc hN1 hn
      have hA := h58 N hN58 kc n hn
      have hT := (S1S2_tail_le V w kc hN1 n hmc).trans (h57 N hN57 kc n hn)
      have hQ0N := Expect.Q_single_le N Ψ (Normalization_isNState V w kc hN1) 0
      have ht0 : 0 ≤ |ρ * lam V w ρ L n| ^ (2 * Real.sqrt (mc ρ)) := by positivity
      have halg := S1S2_PL_alg hL3p hρ hρL hl hρl hX hA hT rfl h6N hQ0N hr00 hr0ρ hy hC58
        hb0 ht0
      set l := lam V w ρ L n with hl'
      set y := (ρ * l) ^ 2 / (1 - (ρ * l) ^ 2) with hy'
      set t := |ρ * l| ^ (2 * Real.sqrt (mc ρ)) with ht'
      set X := (Expect.E4 Ψ n (-n) 0 0).re with hX'
      set wn := wmom V w (mom L n) with hwn
      set Vn := (ft V (mom L n)).re with hVn
      have hly : l + l * y = l / (1 - (ρ * l) ^ 2) := by
        have hne : 1 - (ρ * l) ^ 2 ≠ 0 := hx0.ne'
        have key : ∀ x : ℝ, 1 - x ≠ 0 → l + l * (x / (1 - x)) = l / (1 - x) := fun x hx => by
          field_simp
          ring
        exact key _ hne
      rw [hly] at halg
      set p := l / (1 - (ρ * l) ^ 2) + wn with hp
      have hf : X / L3 + r0 ^ 2 * wn ≤ r0 ^ 2 * p + ρ * y * ((C58 + 1) * b + t) + |l| * E6 := by
        rw [hp, hE6]
        linarith
      have hVd' : |Vn - V0 V| ≤ CV * R :=
        (hVlip _ (hnR.trans hR1)).trans (mul_le_mul_of_nonneg_left hnR hCV)
      have hVn0 : 0 ≤ Vn := by
        have := (abs_le.1 hVd').1
        linarith
      have hVnV : Vn ≤ V0 V := (le_abs_self _).trans (S1S2_abs_V_le hV _)
      have hY : 0 ≤ ρ * y * ((C58 + 1) * b + t) := by positivity
      have hr2 : r0 ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr00 hr0ρ 2
      have k1 : (Vn - V0 V) * (r0 ^ 2 * p) ≤ CV * R * ρ ^ 2 * Mp := by
        calc (Vn - V0 V) * (r0 ^ 2 * p) ≤ |Vn - V0 V| * (r0 ^ 2 * |p|) := by
              have := le_abs_self ((Vn - V0 V) * (r0 ^ 2 * p))
              rwa [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r0 ^ 2)] at this
          _ ≤ CV * R * (ρ ^ 2 * Mp) := by
              gcongr
          _ = CV * R * ρ ^ 2 * Mp := by ring
      have k2 : Vn * (ρ * y * ((C58 + 1) * b + t)) ≤ V0 V * (ρ * y * ((C58 + 1) * b + t)) :=
        mul_le_mul_of_nonneg_right hVnV hY
      have k3 : Vn * (|l| * E6) ≤ V0 V * ρ⁻¹ * E6 := by
        calc Vn * (|l| * E6) ≤ V0 V * (ρ⁻¹ * E6) := by gcongr
          _ = V0 V * ρ⁻¹ * E6 := by ring
      calc Vn * (X / L3 + r0 ^ 2 * wn)
          ≤ Vn * (r0 ^ 2 * p + ρ * y * ((C58 + 1) * b + t) + |l| * E6) :=
            mul_le_mul_of_nonneg_left hf hVn0
        _ = V0 V * r0 ^ 2 * p + (Vn - V0 V) * (r0 ^ 2 * p) +
              Vn * (ρ * y * ((C58 + 1) * b + t)) + Vn * (|l| * E6) := by ring
        _ ≤ V0 V * r0 ^ 2 * p + CV * R * ρ ^ 2 * Mp + V0 V * (ρ * y * ((C58 + 1) * b + t)) +
              V0 V * ρ⁻¹ * E6 := by linarith
        _ = V0 V * r0 ^ 2 * p + V0 V * ρ * ((C58 + 1) * b) * y + V0 V * ρ * (t * y) + M := by
              rw [hM]
              ring
    · simp only [hF, hH1, hH2, hH3, ite_eq_right hn, mul_zero, zero_add]
      have : 0 ≤ H4 n := by
        simp only [hH4]
        split_ifs <;> positivity
      positivity
  have hBs : Summable fun n => V0 V * r0 ^ 2 * H1 n + V0 V * ρ * ((C58 + 1) * b) * H2 n +
      V0 V * ρ * H3 n + M * H4 n :=
    (((hH1s.mul_left _).add (hH2s.mul_left _)).add (hH3s.mul_left _)).add (hH4s.mul_left _)
  have hsum : ∑' n, F n ≤ V0 V * r0 ^ 2 * (∑' n, H1 n) +
      V0 V * ρ * ((C58 + 1) * b) * (∑' n, H2 n) + V0 V * ρ * (∑' n, H3 n) +
      M * (∑' n, H4 n) := by
    refine (Summable.tsum_le_tsum hpt hFs hBs).trans (le_of_eq ?_)
    rw [Summable.tsum_add (((hH1s.mul_left _).add (hH2s.mul_left _)).add (hH3s.mul_left _))
      (hH4s.mul_left _), Summable.tsum_add ((hH1s.mul_left _).add (hH2s.mul_left _))
      (hH3s.mul_left _), Summable.tsum_add (hH1s.mul_left _) (hH2s.mul_left _),
      tsum_mul_left, tsum_mul_left, tsum_mul_left, tsum_mul_left]
  have hsplit : ∀ (a : ℝ) (S : ℝ), L3⁻¹ * S = ρ ^ a * (L3⁻¹ * ρ ^ (-a) * S) := by
    intro a S
    rw [mul_comm L3⁻¹ (ρ ^ (-a)), ← mul_assoc, ← mul_assoc, ← Real.rpow_add hρ]
    norm_num
  have hG0 : 0 ≤ Section4.G V w := by unfold Section4.G; positivity
  have hS1 : L3⁻¹ * (∑' n, H1 n) ≤ ρ ^ (1/2 : ℝ) * (Section4.G V w + Cp * ρ ^ (1/200 : ℝ)) := by
    rw [hsplit (1/2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hε1 : ρ ^ (1/200 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hq1 : 2 * π / (L * ρ ^ (1/2 : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 hLs
  have eH2 : (∑' n : Idx, if inPL ρ L n then
      (ρ * lamPL (g0 V w) ρ (mom L n)) ^ 2 / (1 - (ρ * lamPL (g0 V w) ρ (mom L n)) ^ 2)
      else 0) = ∑' n, H2 n := tsum_congr fun n => by
    simp only [hH2]
    split_ifs with h
    · rw [lam_of_inPL h]
    · rfl
  have eH3 : (∑' n : Idx, if inPL ρ L n then
      |ρ * lamPL (g0 V w) ρ (mom L n)| ^ (2 * Real.sqrt (mc ρ)) *
        ((ρ * lamPL (g0 V w) ρ (mom L n)) ^ 2 / (1 - (ρ * lamPL (g0 V w) ρ (mom L n)) ^ 2))
      else 0) = ∑' n, H3 n := tsum_congr fun n => by
    simp only [hH3]
    split_ifs with h
    · rw [lam_of_inPL h]
    · rfl
  rw [eH2] at hoccN
  rw [eH3] at htailN
  have hS2 : L3⁻¹ * (∑' n, H2 n) ≤ ρ ^ (3/2 : ℝ) * (c + 2 * K1) := by
    rw [hsplit (3/2 : ℝ)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : K1 * (ρ ^ (1/200 : ℝ) + 2 * π / (L * ρ ^ (1/2 : ℝ))) ≤ K1 * (1 + 1) :=
      mul_le_mul_of_nonneg_left (add_le_add hε1 hq1) hK1
    linarith
  have hS3 : L3⁻¹ * (∑' n, H3 n) ≤ ρ ^ (3/2 : ℝ) * (Kt * (b + 2 * π * b)) := by
    rw [hsplit (3/2 : ℝ)]
    refine mul_le_mul_of_nonneg_left (htailN.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left (add_le_add (S1S2_tau1 hρ hρ1) hτ2) hKt
  have hS4 : L3⁻¹ * (∑' n, H4 n) ≤ K0 * R ^ (3 - 0 : ℝ) := hcnt L R hR0 hLR
  have hr2 : r0 ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr00 hr0ρ 2
  have hB1 : 0 ≤ ρ ^ (1/2 : ℝ) * (Section4.G V w + Cp * ρ ^ (1/200 : ℝ)) := by positivity
  have t1 : V0 V * r0 ^ 2 * (L3⁻¹ * (∑' n, H1 n)) ≤
      V0 V * ρ ^ 2 * (ρ ^ (1/2 : ℝ) * (Section4.G V w + Cp * ρ ^ (1/200 : ℝ))) :=
    (mul_le_mul_of_nonneg_left hS1 (by positivity)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr2 hV0) hB1)
  have t2 : V0 V * ρ * ((C58 + 1) * b) * (L3⁻¹ * (∑' n, H2 n)) ≤
      V0 V * ρ * ((C58 + 1) * b) * (ρ ^ (3/2 : ℝ) * (c + 2 * K1)) :=
    mul_le_mul_of_nonneg_left hS2 (by positivity)
  have t3 : V0 V * ρ * (L3⁻¹ * (∑' n, H3 n)) ≤
      V0 V * ρ * (ρ ^ (3/2 : ℝ) * (Kt * (b + 2 * π * b))) :=
    mul_le_mul_of_nonneg_left hS3 (by positivity)
  have t4 : M * (L3⁻¹ * (∑' n, H4 n)) ≤ M * (K0 * R ^ (3 - 0 : ℝ)) :=
    mul_le_mul_of_nonneg_left hS4 hM0
  have h52 : ρ ^ (5/2 + 1/400 : ℝ) = ρ ^ (5/2 : ℝ) * b := Real.rpow_add hρ _ _
  have hεb : ρ ^ (1/200 : ℝ) ≤ b := S1S2_rpow_le hρ hρ1 (by norm_num)
  have u1 : V0 V * ρ ^ 2 * (ρ ^ (1/2 : ℝ) * (Section4.G V w + Cp * ρ ^ (1/200 : ℝ))) ≤
      V0 V * Section4.G V w * ρ ^ (5/2 : ℝ) + V0 V * Cp * (ρ ^ (5/2 : ℝ) * b) := by
    have e : V0 V * ρ ^ 2 * (ρ ^ (1/2 : ℝ) * (Section4.G V w + Cp * ρ ^ (1/200 : ℝ))) =
        V0 V * Section4.G V w * (ρ ^ 2 * ρ ^ (1/2 : ℝ)) +
          V0 V * Cp * ((ρ ^ 2 * ρ ^ (1/2 : ℝ)) * ρ ^ (1/200 : ℝ)) := by ring
    rw [e, S1S2_pow_52a hρ]
    gcongr
  have u2 : V0 V * ρ * ((C58 + 1) * b) * (ρ ^ (3/2 : ℝ) * (c + 2 * K1)) =
      V0 V * (C58 + 1) * (c + 2 * K1) * (ρ ^ (5/2 : ℝ) * b) := by
    rw [← S1S2_pow_52b hρ]
    ring
  have u3 : V0 V * ρ * (ρ ^ (3/2 : ℝ) * (Kt * (b + 2 * π * b))) =
      V0 V * Kt * (1 + 2 * π) * (ρ ^ (5/2 : ℝ) * b) := by
    rw [← S1S2_pow_52b hρ]
    ring
  have u4 : M * (K0 * R ^ (3 - 0 : ℝ)) ≤
      K0 * (CV * Cq + V0 V * C6 + V0 V) * (ρ ^ (5/2 : ℝ) * b) := by
    have hR3 : R ^ (3 - 0 : ℝ) = ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ) := by
      rw [hR, ← Real.rpow_mul hρ.le]
    have e : M * (K0 * R ^ (3 - 0 : ℝ)) = K0 * (CV * Cq *
        (R * ρ ^ 2 * (ρ ^ (-1 : ℝ) * ρ ^ (-(2/200) : ℝ)) * ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ)) +
        V0 V * C6 * (ρ⁻¹ * ρ ^ (5/2 + 1/400 : ℝ) * ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ)) +
        V0 V * (ρ⁻¹ * (ρ / L3) * ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ))) := by
      rw [hR3, hM, hMp, hE6, he6]
      ring
    rw [e, hρL3, ← h52]
    have q1 := S1S2_pow_Q1 hρ hρ1
    have q2 := S1S2_pow_Q2 hρ hρ1
    have q3 := S1S2_pow_Q3 hρ hρ1
    rw [← hR] at q1
    have hp : 0 ≤ ρ ^ (5/2 + 1/400 : ℝ) := by positivity
    calc K0 * (CV * Cq *
          (R * ρ ^ 2 * (ρ ^ (-1 : ℝ) * ρ ^ (-(2/200) : ℝ)) * ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ)) +
          V0 V * C6 * (ρ⁻¹ * ρ ^ (5/2 + 1/400 : ℝ) * ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ)) +
          V0 V * (ρ⁻¹ * ρ ^ (33/8 : ℝ) * ρ ^ ((1/2 - 1/200) * (3 - 0) : ℝ)))
        ≤ K0 * (CV * Cq * ρ ^ (5/2 + 1/400 : ℝ) + V0 V * C6 * ρ ^ (5/2 + 1/400 : ℝ) +
            V0 V * ρ ^ (5/2 + 1/400 : ℝ)) := by
          gcongr
      _ = K0 * (CV * Cq + V0 V * C6 + V0 V) * ρ ^ (5/2 + 1/400 : ℝ) := by ring
  calc L3⁻¹ * (∑' n, F n)
      ≤ L3⁻¹ * (V0 V * r0 ^ 2 * (∑' n, H1 n) +
          V0 V * ρ * ((C58 + 1) * b) * (∑' n, H2 n) + V0 V * ρ * (∑' n, H3 n) +
          M * (∑' n, H4 n)) := mul_le_mul_of_nonneg_left hsum (inv_nonneg.2 hL3p.le)
    _ = V0 V * r0 ^ 2 * (L3⁻¹ * (∑' n, H1 n)) +
          V0 V * ρ * ((C58 + 1) * b) * (L3⁻¹ * (∑' n, H2 n)) +
          V0 V * ρ * (L3⁻¹ * (∑' n, H3 n)) + M * (L3⁻¹ * (∑' n, H4 n)) := by ring
    _ ≤ (V0 V * Section4.G V w * ρ ^ (5/2 : ℝ) + V0 V * Cp * (ρ ^ (5/2 : ℝ) * b)) +
          V0 V * (C58 + 1) * (c + 2 * K1) * (ρ ^ (5/2 : ℝ) * b) +
          V0 V * Kt * (1 + 2 * π) * (ρ ^ (5/2 : ℝ) * b) +
          K0 * (CV * Cq + V0 V * C6 + V0 V) * (ρ ^ (5/2 : ℝ) * b) := by
        rw [← u2, ← u3]
        linarith
    _ = (V0 V * Section4.G V w + (V0 V * Cp + V0 V * (C58 + 1) * (c + 2 * K1) +
          V0 V * Kt * (1 + 2 * π) + K0 * (CV * Cq + V0 V * C6 + V0 V)) * b) *
          ρ ^ (5/2 : ℝ) := by ring

/-- (7.7) [u-uPMH] and (7.8) [u-uPL] of Lemma 7.2 [symno20] combined over `u ≠ 0`, with
`λ_u = −w_u` on `P_I ∪ P_H`: `|Λ|⁻¹ Σ_{u ≠ 0} V_u|Λ|⁻¹⟨a†_u a†_{−u} a_0 a_0⟩_Ψ + ρ₀²|Λ|⁻¹ Σ_{u ∈ P} V_u w_u`
is at most `(V₀g₀^{3/2}/π² + Cρ^{η/2})ρ^{5/2}`. -/
theorem Pair_S2_total {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      (LN N ^ 3)⁻¹ * (∑' n : Idx, if n ≠ 0 then
          (ft V (mom (LN N) n)).re * (Expect.E4 (trialState V w kc N) n (-n) 0 0).re / LN N ^ 3
          else 0) +
        rho0 (g0 V w) (rhoN N) ^ 2 * ((LN N ^ 3)⁻¹ * (∑' n : Idx, if inP (rhoN N) (LN N) n then
          (ft V (mom (LN N) n)).re * wmom V w (mom (LN N) n) else 0))
        ≤ (V0 V * Section4.G V w + C * rhoN N ^ (1/400 : ℝ)) * rhoN N ^ (5/2 : ℝ) := by
  obtain ⟨C7, hC7, N7, h7⟩ := S1S2_IH_core hV hw
  obtain ⟨C8, hC8, N8, h8⟩ := Eq7_8 hV hw
  obtain ⟨K, hK, NK, hKb⟩ := Pair_sum_lamV hV hw
  refine ⟨C7 + C8, by positivity, max (max N7 N8) (max NK 1), fun N hN kc => ?_⟩
  have hN7 : N7 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN8 : N8 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNK : NK ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hcs, hcb⟩ := h7 N hN7 kc
  have hdb := h8 N hN8 kc
  obtain ⟨hq, -⟩ := hKb N hNK
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set L3 := L ^ 3 with hL3
  have hL3p : 0 < L3 := pow_pos hL 3
  set Ψ := trialState V w kc N with hΨ
  set r0 := rho0 (g0 V w) ρ with hr0
  set a : Idx → ℝ := fun n => if n ≠ 0 then
      (ft V (mom L n)).re * (Expect.E4 Ψ n (-n) 0 0).re / L3 else 0 with ha
  set bP : Idx → ℝ := fun n => if inP ρ L n then
      (ft V (mom L n)).re * wmom V w (mom L n) else 0 with hbP
  set c : Idx → ℝ := fun n => if inPI ρ L n ∨ inPH ρ L n then
      (ft V (mom L n)).re * ((Expect.E4 Ψ n (-n) 0 0).re / L3 - r0 ^ 2 * lam V w ρ L n)
      else 0 with hc
  set d : Idx → ℝ := fun n => if inPL ρ L n then
      (ft V (mom L n)).re * ((Expect.E4 Ψ n (-n) 0 0).re / L3 + r0 ^ 2 * wmom V w (mom L n))
      else 0 with hd
  have hPLR : ∀ n, inPL ρ L n → ‖mom L n‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := fun n hn => hn.2
  have hball : ∀ g : Idx → ℝ, (∀ n, ¬ inPL ρ L n → g n = 0) → Summable g := fun g hg0 =>
    S1S2_summable_ball hL g (fun n hn => by
      by_contra h
      exact hn (hg0 n (fun hp => h (hPLR n hp))))
  have hds : Summable d := hball d (fun n hn => by simp only [hd, ite_eq_right hn])
  set dV : Idx → ℝ := fun n => if inPL ρ L n then
      |(ft V (mom L n)).re * wmom V w (mom L n)| else 0 with hdV
  have hdVs : Summable dV := hball dV (fun n hn => by simp only [hdV, ite_eq_right hn])
  have hbPs : Summable bP := by
    refine Summable.of_norm_bounded (hdVs.add (hq 0).1) (fun n => ?_)
    rw [Real.norm_eq_abs]
    simp only [hbP, hdV]
    by_cases hn : inP ρ L n
    · rw [ite_eq_left hn]
      by_cases hL' : inPL ρ L n
      · rw [ite_eq_left hL']
        have : 0 ≤ (if n ≠ 0 then |lam V w ρ L n * (ft V (0 - mom L n)).re| else 0) := by
          split_ifs <;> positivity
        linarith
      · have hn0 : n ≠ 0 := by
          rcases hn with h | h | h
          · exact absurd h hL'
          · exact Regions_PI_ne_zero hρ h
          · exact Regions_PH_ne_zero hρ h
        rw [ite_eq_right hL', ite_eq_left hn0, zero_add, scat_lam_of_not_PL ρ L n hL', zero_sub,
          scat_ft_V_neg hV, abs_mul, abs_mul, abs_neg, mul_comm]
    · rw [ite_eq_right hn, abs_zero]
      have h1 : 0 ≤ (if inPL ρ L n then |(ft V (mom L n)).re * wmom V w (mom L n)| else 0) := by
        split_ifs <;> positivity
      have h2 : 0 ≤ (if n ≠ 0 then |lam V w ρ L n * (ft V (0 - mom L n)).re| else 0) := by
        split_ifs <;> positivity
      linarith
  have hpt : ∀ n, a n + r0 ^ 2 * bP n = c n + d n := by
    intro n
    simp only [ha, hbP, hc, hd]
    by_cases hn0 : n = 0
    · have h1 : ¬ inPL ρ L n := fun h => Regions_PL_ne_zero hρ h hn0
      have h2 : ¬ (inPI ρ L n ∨ inPH ρ L n) := fun h => by
        rcases h with h | h
        · exact Regions_PI_ne_zero hρ h hn0
        · exact Regions_PH_ne_zero hρ h hn0
      have h3 : ¬ inP ρ L n := fun h => by
        rcases h with h | h | h
        · exact h1 h
        · exact h2 (Or.inl h)
        · exact h2 (Or.inr h)
      rw [ite_eq_right (not_not.2 hn0), ite_eq_right h3, ite_eq_right h2, ite_eq_right h1]
      ring
    · rw [ite_eq_left hn0]
      by_cases hL' : inPL ρ L n
      · have h2 : ¬ (inPI ρ L n ∨ inPH ρ L n) := fun h => by
          rcases h with h | h
          · exact Regions_PL_PI hL' h
          · exact Regions_PL_PH hρ hL' h
        have h3 : inP ρ L n := Or.inl hL'
        rw [ite_eq_left h3, ite_eq_right h2, ite_eq_left hL']
        ring
      · by_cases hIH : inPI ρ L n ∨ inPH ρ L n
        · have h3 : inP ρ L n := Or.inr hIH
          rw [ite_eq_left h3, ite_eq_left hIH, ite_eq_right hL', scat_lam_of_not_PL ρ L n hL']
          ring
        · have h3 : ¬ inP ρ L n := fun h => by
            rcases h with h | h | h
            · exact hL' h
            · exact hIH (Or.inl h)
            · exact hIH (Or.inr h)
          rw [ite_eq_right h3, ite_eq_right hIH, ite_eq_right hL', S1S2_E4_zero V w kc N hn0 h3]
          simp
  have has : Summable a := by
    have : a = fun n => c n + d n - r0 ^ 2 * bP n := by
      funext n
      rw [← hpt n]
      ring
    rw [this]
    exact (hcs.add hds).sub (hbPs.mul_left _)
  have hsum : (∑' n, a n) + r0 ^ 2 * (∑' n, bP n) = (∑' n, c n) + (∑' n, d n) := by
    rw [← tsum_mul_left, ← Summable.tsum_add has (hbPs.mul_left _),
      ← Summable.tsum_add hcs hds]
    exact tsum_congr hpt
  have hcb' := (abs_le.1 hcb).2
  have h52 : ρ ^ (5/2 + 1/400 : ℝ) = ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ) := Real.rpow_add hρ _ _
  calc L3⁻¹ * (∑' n, a n) + r0 ^ 2 * (L3⁻¹ * (∑' n, bP n))
      = L3⁻¹ * (∑' n, c n) + L3⁻¹ * (∑' n, d n) := by
        rw [← mul_assoc, mul_comm (r0 ^ 2) L3⁻¹, mul_assoc, ← mul_add, hsum, mul_add]
    _ ≤ C7 * ρ ^ (5/2 + 1/400 : ℝ) +
          (V0 V * Section4.G V w + C8 * ρ ^ (1/400 : ℝ)) * ρ ^ (5/2 : ℝ) := add_le_add hcb' hdb
    _ = (V0 V * Section4.G V w + (C7 + C8) * ρ ^ (1/400 : ℝ)) * ρ ^ (5/2 : ℝ) := by
        rw [h52]
        ring

/-- Lemma 4.3 [lemHS2], (4.10) [proofthem1-3]. -/
theorem Lemma4_3 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma4_3 V w := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C9, hC9, N9, h9⟩ := Pair_S2_total hV hw
  obtain ⟨Cw, hCw, Nw, hvw⟩ := Pair_sum_Vw_P hV hw
  obtain ⟨N1, h1⟩ := eventually_atTop.1
    ((eventually_ge_atTop 1).and (S1S2_ev_small ((3 * π ^ 2)⁻¹ * g0 V w ^ (3/2 : ℝ))
      (b := 1/2) (by norm_num)))
  let E : ℝ → ℕ → ℝ := fun kc N => (LN N ^ 3)⁻¹ * ∑' n : Idx, if n ≠ 0 then
    (ft V (mom (LN N) n)).re * (2 * (Expect.E4 (trialState V w kc N) n (-n) 0 0).re) else 0
  refine ⟨E, fun kc => ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hL1 := S1S2_one_le_L hN
    have hVs := ((scat_lattice_V hV).choose_spec (LN N) hL1).1
    have h := Lemma7_1_S2 (LN N) V N _ hVs (Normalization_isNState V w kc hN)
    convert h using 1
    simp only [E]
    rw [Complex.ofReal_mul, Complex.ofReal_tsum]
    congr 1
    refine tsum_congr fun n => ?_
    split_ifs
    · rw [Complex.add_conj]
      conv_rhs => rw [scat_ft_V_real hV (mom (LN N) n)]
      push_cast
      ring
    · simp
  refine S1S2_limsup2_le _ _ (2 * C9 + 2 * Cw) (1/400) (by norm_num) (max (max N9 Nw) N1)
    (fun kc N hN => ?_)
  have hN9 : N9 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNw : Nw ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hN1, hs⟩ := h1 N (le_trans (le_max_right _ _) hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have h9N := h9 N hN9 kc
  have hvwN := (abs_le.1 (hvw N hNw)).1
  obtain ⟨hr00, hr0ρ, -, -⟩ := S1S2_rho0 hg.le hρ (by simpa [mul_assoc] using hs)
  set ρ := rhoN N with hρdef
  set L3 := LN N ^ 3 with hL3
  have hL3p : 0 < L3 := pow_pos hL 3
  set r0 := rho0 (g0 V w) ρ with hr0
  set S := ∑' n : Idx, if n ≠ 0 then
      (ft V (mom (LN N) n)).re * (Expect.E4 (trialState V w kc N) n (-n) 0 0).re / L3 else 0
    with hS
  set SP := (L3)⁻¹ * (∑' n : Idx, if inP ρ (LN N) n then
      (ft V (mom (LN N) n)).re * wmom V w (mom (LN N) n) else 0) with hSP
  have hE : E kc N / L3 = 2 * (L3⁻¹ * S) := by
    simp only [E]
    have e : (∑' n : Idx, if n ≠ 0 then
        (ft V (mom (LN N) n)).re * (2 * (Expect.E4 (trialState V w kc N) n (-n) 0 0).re) else 0) =
        (2 * L3) * S := by
      rw [hS, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      split_ifs
      · field_simp
      · simp
    rw [e]
    field_simp
    rfl
  have hp : 0 < ρ ^ (5/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hr2 : r0 ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr00 hr0ρ 2
  have hpw : ρ ^ 2 * ρ ^ (1/2 + 1/200 : ℝ) ≤ ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ) := by
    rw [← Real.rpow_natCast ρ 2, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    exact S1S2_rpow_le hρ hρ1 (by norm_num)
  have hdiff : r0 ^ 2 * (normVw V w - SP) ≤ Cw * (ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ)) := by
    have h0 : normVw V w - SP ≤ Cw * ρ ^ (1/2 + 1/200 : ℝ) := by linarith
    have h0' : 0 ≤ Cw * ρ ^ (1/2 + 1/200 : ℝ) := by positivity
    calc r0 ^ 2 * (normVw V w - SP) ≤ r0 ^ 2 * (Cw * ρ ^ (1/2 + 1/200 : ℝ)) :=
          mul_le_mul_of_nonneg_left h0 (by positivity)
      _ ≤ ρ ^ 2 * (Cw * ρ ^ (1/2 + 1/200 : ℝ)) := mul_le_mul_of_nonneg_right hr2 h0'
      _ = Cw * (ρ ^ 2 * ρ ^ (1/2 + 1/200 : ℝ)) := by ring
      _ ≤ Cw * (ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ)) := mul_le_mul_of_nonneg_left hpw hCw
  unfold Section4.excess
  rw [div_le_iff₀ hp, hE]
  have key : 2 * (L3⁻¹ * S) - -2 * normVw V w * r0 ^ 2 =
      2 * (L3⁻¹ * S + r0 ^ 2 * SP) + 2 * (r0 ^ 2 * (normVw V w - SP)) := by ring
  rw [key]
  calc 2 * (L3⁻¹ * S + r0 ^ 2 * SP) + 2 * (r0 ^ 2 * (normVw V w - SP))
      ≤ 2 * ((V0 V * Section4.G V w + C9 * ρ ^ (1/400 : ℝ)) * ρ ^ (5/2 : ℝ)) +
          2 * (Cw * (ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ))) := by
        have := h9N
        linarith
    _ = (2 * V0 V * Section4.G V w + (2 * C9 + 2 * Cw) * ρ ^ (1/400 : ℝ)) * ρ ^ (5/2 : ℝ) := by
        ring

end LHYUpper
