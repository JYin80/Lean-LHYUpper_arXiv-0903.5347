module

public import LHYUpper.Scattering.Solution
public import LHYUpper.Position.Lemma22
public import LHYUpper.Position.DirichletFacts
public import LHYUpper.Assembly.Final

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Lemma 2.1 [thm1]

The density `ρ̃_N = N / L̃_N³` of Lemma 2.2 [lemma1] is strictly decreasing for `N ≥ 2`, and the
side `L̃_N` of the Dirichlet box satisfies `L̃_N ρ̃_N^{25/24} → 1`. Near-minimizers of `e₀^D` on
`[0, L̃_N]³` at density `ρ̃_N`, together with Lemma 2.2 [lemma1] and the periodic bound for
`e₀^P`, give the trial states of Lemma 2.1 [thm1] for every large `N`. For a given small `ρ`, the
integer `N(ρ)` with `ρ̃_{N+1} < ρ ≤ ρ̃_N` and the side `L(ρ) = (N(ρ)/ρ)^{1/3} ≥ L̃_{N(ρ)}` give
the form stated in the paper, with `N = ρ L³`; the ratio of (2.4) changes by `O(1/N)` relative
amounts and by an additive error `O(N^{-13/17})` under the change of density `ρ̃_N → ρ`. -/

/-- `N^{-25/102}`, the quantity `ρ_N^{25/48}` of Lemma 2.2 [lemma1]. -/
private def Lemma21_s (N : ℕ) : ℝ := (N : ℝ) ^ (-(25 / 102 : ℝ))

/-- `N^{-25/102} > 0` for `N ≥ 1`. -/
private lemma Lemma21_s_pos {N : ℕ} (hN : 1 ≤ N) : 0 < Lemma21_s N :=
  Real.rpow_pos_of_pos (by exact_mod_cast hN) _

/-- `ρ_N = s_N^{48/25}` for `N ≥ 1`. -/
private lemma Lemma21_rhoN_eq {N : ℕ} (hN : 1 ≤ N) : rhoN N = Lemma21_s N ^ (48 / 25 : ℝ) := by
  unfold rhoN Lemma21_s
  rw [← Real.rpow_mul (by positivity)]
  norm_num

/-- `ρ_N^{25/48} = s_N` for `N ≥ 1`, the exponent in `L̃_N` of Lemma 2.2 [lemma1]. -/
private lemma Lemma21_t_eq {N : ℕ} (hN : 1 ≤ N) : rhoN N ^ (25 / 48 : ℝ) = Lemma21_s N := by
  rw [Lemma21_rhoN_eq hN, ← Real.rpow_mul (Lemma21_s_pos hN).le]
  norm_num

/-- `ρ̃_N = s_N^{48/25} / (1 + 2 s_N)³` for `N ≥ 1`. -/
private lemma Lemma21_rhotN_eq {N : ℕ} (hN : 1 ≤ N) :
    rhotN N = Lemma21_s N ^ (48 / 25 : ℝ) / (1 + 2 * Lemma21_s N) ^ 3 := by
  have hx : (0 : ℝ) < N := by exact_mod_cast hN
  have hs := Lemma21_s_pos hN
  have hr : 0 < rhoN N := Real.rpow_pos_of_pos hx _
  have hNr : (N : ℝ) = rhoN N ^ (-(17 / 8 : ℝ)) := by
    unfold rhoN
    rw [← Real.rpow_mul hx.le]
    norm_num
  have h3 : (rhoN N ^ (-(25 / 24 : ℝ))) ^ 3 = rhoN N ^ (-(25 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    norm_num
  unfold rhotN LtN LN
  rw [mul_pow, h3, Lemma21_t_eq hN, hNr, ← Lemma21_rhoN_eq hN, div_mul_eq_div_div,
    ← Real.rpow_sub hr]
  norm_num


/-- The function `s ↦ s^{48/25} / (1 + 2s)³` with `ρ̃_N = φ(N^{-25/102})`. -/
private def Lemma21_phi (s : ℝ) : ℝ := s ^ (48 / 25 : ℝ) / (1 + 2 * s) ^ 3

/-- The derivative of `φ(s) = s^{48/25} / (1 + 2s)³` at `s > 0`. -/
private lemma Lemma21_phi_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt Lemma21_phi
      (((48 / 25 : ℝ) * s ^ ((48 / 25 : ℝ) - 1) * (1 + 2 * s) ^ 3 -
        s ^ (48 / 25 : ℝ) * (3 * (1 + 2 * s) ^ 2 * 2)) / ((1 + 2 * s) ^ 3) ^ 2) s := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ (48 / 25 : ℝ))
      ((48 / 25 : ℝ) * s ^ ((48 / 25 : ℝ) - 1)) s :=
    Real.hasDerivAt_rpow_const (Or.inl hs.ne')
  have h2 : HasDerivAt (fun s : ℝ => (1 + 2 * s) ^ 3) (3 * (1 + 2 * s) ^ 2 * 2) s := by
    have := ((hasDerivAt_id s).const_mul (2 : ℝ)).const_add 1
    simpa using this.fun_pow 3
  exact h1.div h2 (by positivity)

/-- `φ` has positive derivative on `(0, 8/9)`. -/
private lemma Lemma21_phi_deriv_pos {s : ℝ} (hs : 0 < s) (hs' : s < 8 / 9) :
    0 < deriv Lemma21_phi s := by
  rw [(Lemma21_phi_hasDerivAt hs).deriv]
  have e : s ^ (48 / 25 : ℝ) = s * s ^ ((48 / 25 : ℝ) - 1) := by
    rw [← Real.rpow_one_add' hs.le (by norm_num)]
    norm_num
  have hp : 0 < s ^ ((48 / 25 : ℝ) - 1) := Real.rpow_pos_of_pos hs _
  have hc : 0 < 1 + 2 * s := by positivity
  rw [e]
  refine div_pos ?_ (by positivity)
  have : (48 / 25 : ℝ) * s ^ ((48 / 25 : ℝ) - 1) * (1 + 2 * s) ^ 3 -
      s * s ^ ((48 / 25 : ℝ) - 1) * (3 * (1 + 2 * s) ^ 2 * 2) =
      s ^ ((48 / 25 : ℝ) - 1) * (1 + 2 * s) ^ 2 * ((48 - 54 * s) / 25) := by ring
  rw [this]
  refine mul_pos (by positivity) (by linarith)

/-- `φ` is strictly increasing on `(0, 8/9]`. -/
private lemma Lemma21_phi_strictMonoOn : StrictMonoOn Lemma21_phi (Set.Ioc 0 (8 / 9)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioc _ _) ?_ ?_
  · intro s hs
    exact (Lemma21_phi_hasDerivAt hs.1).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioc] at hs
    exact Lemma21_phi_deriv_pos hs.1 hs.2

/-- `2^{-25/102} < 8/9`. -/
private lemma Lemma21_s_two_lt : Lemma21_s 2 < 8 / 9 := by
  unfold Lemma21_s
  have hx : (9 / 8 : ℝ) < (2 : ℝ) ^ (25 / 102 : ℝ) := by
    by_contra hcon
    push Not at hcon
    have h1 : ((2 : ℝ) ^ (25 / 102 : ℝ)) ^ 102 = 2 ^ 25 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h2 : ((2 : ℝ) ^ (25 / 102 : ℝ)) ^ 102 ≤ (9 / 8 : ℝ) ^ 102 :=
      pow_le_pow_left₀ (by positivity) hcon 102
    rw [h1] at h2
    norm_num at h2
  rw [Nat.cast_ofNat, Real.rpow_neg (by norm_num)]
  rw [inv_lt_comm₀ (by positivity) (by norm_num)]
  simpa using hx

/-- `s_N` is nonincreasing in `N ≥ 1`. -/
private lemma Lemma21_s_anti {M N : ℕ} (hM : 1 ≤ M) (h : M ≤ N) : Lemma21_s N ≤ Lemma21_s M := by
  unfold Lemma21_s
  exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hM) (by exact_mod_cast h) (by norm_num)

/-- `s_N` is strictly decreasing in `N ≥ 1`. -/
private lemma Lemma21_s_strictAnti {M N : ℕ} (hM : 1 ≤ M) (h : M < N) :
    Lemma21_s N < Lemma21_s M := by
  unfold Lemma21_s
  exact Real.rpow_lt_rpow_of_neg (by exact_mod_cast (by omega : 0 < M)) (by exact_mod_cast h)
    (by norm_num)

/-- The density `ρ̃_N` of Lemma 2.2 [lemma1] is strictly decreasing in `N ≥ 2`. -/
theorem rhotN_strictAntiOn : StrictAntiOn (fun N : ℕ => rhotN N) (Set.Ici 2) := by
  intro a ha b hb hab
  have ha2 : 2 ≤ a := ha
  have hb2 : 2 ≤ b := hb
  have e : ∀ N : ℕ, 2 ≤ N → rhotN N = Lemma21_phi (Lemma21_s N) := fun N hN =>
    Lemma21_rhotN_eq (by omega)
  simp only [e a ha2, e b hb2]
  have hsa : Lemma21_s a ≤ Lemma21_s 2 := Lemma21_s_anti (by norm_num) ha2
  have hsb : Lemma21_s b ≤ Lemma21_s 2 := Lemma21_s_anti (by norm_num) hb2
  have h2 := Lemma21_s_two_lt
  exact Lemma21_phi_strictMonoOn ⟨Lemma21_s_pos (by omega), by linarith⟩
    ⟨Lemma21_s_pos (by omega), by linarith⟩ (Lemma21_s_strictAnti (by omega) hab)


/-- `s_N → 0`. -/
private lemma Lemma21_tendsto_s : Tendsto (fun N : ℕ => Lemma21_s N) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 25 / 102)).comp tendsto_natCast_atTop_atTop

/-- `L̃_N = (1 + 2 s_N) / s_N²` for `N ≥ 1`. -/
private lemma Lemma21_LtN_eq {N : ℕ} (hN : 1 ≤ N) :
    LtN N = (1 + 2 * Lemma21_s N) / Lemma21_s N ^ 2 := by
  have hs := Lemma21_s_pos hN
  unfold LtN LN
  rw [Lemma21_t_eq hN, Lemma21_rhoN_eq hN, ← Real.rpow_mul hs.le]
  norm_num [Real.rpow_neg hs.le, div_eq_mul_inv, mul_comm]

/-- `L̃_N ρ̃_N^{25/24} = (1 + 2 s_N) / ((1 + 2 s_N)³)^{25/24}` for `N ≥ 1`. -/
private lemma Lemma21_LtN_mul_eq {N : ℕ} (hN : 1 ≤ N) :
    LtN N * rhotN N ^ (25 / 24 : ℝ) =
      (1 + 2 * Lemma21_s N) / ((1 + 2 * Lemma21_s N) ^ 3) ^ (25 / 24 : ℝ) := by
  have hs := Lemma21_s_pos hN
  have hc : 0 < 1 + 2 * Lemma21_s N := by positivity
  rw [Lemma21_LtN_eq hN, Lemma21_rhotN_eq hN, Real.div_rpow (Real.rpow_nonneg hs.le _)
    (by positivity), ← Real.rpow_mul hs.le]
  have h2 : (48 / 25 : ℝ) * (25 / 24) = ((2 : ℕ) : ℝ) := by norm_num
  rw [h2, Real.rpow_natCast]
  have : 0 < ((1 + 2 * Lemma21_s N) ^ 3) ^ (25 / 24 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  field_simp

/-- `L̃_N ρ̃_N^{25/24} → 1`: the box of Lemma 2.1 [thm1] has side `L̃ ∼ ρ̃^{-25/24}`. -/
theorem tendsto_LtN_mul_rhotN :
    Tendsto (fun N : ℕ => LtN N * rhotN N ^ (25 / 24 : ℝ)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun N : ℕ => 1 + 2 * Lemma21_s N) atTop (𝓝 (1 + 2 * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul Lemma21_tendsto_s)
  have h2 : Tendsto (fun N : ℕ => ((1 + 2 * Lemma21_s N) ^ 3) ^ (25 / 24 : ℝ)) atTop
      (𝓝 (((1 + 2 * 0) ^ 3) ^ (25 / 24 : ℝ))) :=
    (h1.pow 3).rpow_const (Or.inr (by norm_num))
  have h3 := h1.div h2 (by norm_num)
  norm_num at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (Lemma21_LtN_mul_eq hN).symm


/-- `s_N ≤ 1` for `N ≥ 1`. -/
private lemma Lemma21_s_le_one {N : ℕ} (hN : 1 ≤ N) : Lemma21_s N ≤ 1 := by
  unfold Lemma21_s
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)

/-- `ρ̃_N = ρ_N / (1 + 2 s_N)³` for `N ≥ 1`. -/
private lemma Lemma21_rhotN_eq' {N : ℕ} (hN : 1 ≤ N) :
    rhotN N = rhoN N / (1 + 2 * Lemma21_s N) ^ 3 := by
  rw [Lemma21_rhotN_eq hN, Lemma21_rhoN_eq hN]

/-- `ρ̃_N > 0` for `N ≥ 1`. -/
private lemma Lemma21_rhotN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < rhotN N := by
  have hs := Lemma21_s_pos hN
  rw [Lemma21_rhotN_eq hN]
  positivity

/-- `L̃_N > 0` for `N ≥ 1`. -/
private lemma Lemma21_LtN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < LtN N := by
  have hs := Lemma21_s_pos hN
  rw [Lemma21_LtN_eq hN]
  positivity

/-- `L̃_N³ ρ̃_N = N`. -/
private lemma Lemma21_LtN_pow {N : ℕ} (hN : 1 ≤ N) : LtN N ^ 3 * rhotN N = N := by
  have hL := Lemma21_LtN_pos hN
  unfold rhotN
  field_simp

/-- `ρ̃_N → 0`. -/
private lemma Lemma21_tendsto_rhotN : Tendsto (fun N : ℕ => rhotN N) atTop (𝓝 0) := by
  have hφ : ContinuousAt Lemma21_phi 0 := by
    unfold Lemma21_phi
    exact ((Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num))).div
      (by fun_prop) (by norm_num))
  have h := hφ.tendsto.comp Lemma21_tendsto_s
  have h0 : Lemma21_phi 0 = 0 := by
    unfold Lemma21_phi
    rw [Real.zero_rpow (by norm_num)]
    simp
  rw [h0] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (Lemma21_rhotN_eq hN).symm

/-- `ρ̃_N ≤ (1 + 8/(17N)) ρ̃_{N+1}`. -/
private lemma Lemma21_rhotN_le_succ {N : ℕ} (hN : 1 ≤ N) :
    rhotN N ≤ (1 + 8 / (17 * (N : ℝ))) * rhotN (N + 1) := by
  have hx : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : 1 ≤ N + 1 := by omega
  have hc : (0 : ℝ) < 1 + 2 * Lemma21_s N := by have := Lemma21_s_pos hN; positivity
  have hc1 : (0 : ℝ) < 1 + 2 * Lemma21_s (N + 1) := by have := Lemma21_s_pos hN1; positivity
  have hss : Lemma21_s (N + 1) ≤ Lemma21_s N := Lemma21_s_anti hN (by omega)
  have hcc : 1 + 2 * Lemma21_s (N + 1) ≤ 1 + 2 * Lemma21_s N := by linarith
  have hr : rhoN N = (((N : ℝ) + 1) / N) ^ (8 / 17 : ℝ) * rhoN (N + 1) := by
    unfold rhoN
    push_cast
    have e1 : (N : ℝ) ^ (-(8 / 17 : ℝ)) = ((N : ℝ) ^ (8 / 17 : ℝ))⁻¹ := Real.rpow_neg hx.le _
    have e2 : ((N : ℝ) + 1) ^ (-(8 / 17 : ℝ)) = (((N : ℝ) + 1) ^ (8 / 17 : ℝ))⁻¹ :=
      Real.rpow_neg (by positivity) _
    rw [Real.div_rpow (by positivity) hx.le, e1, e2]
    have : (0 : ℝ) < ((N : ℝ) + 1) ^ (8 / 17 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    have h2 : (0 : ℝ) < (N : ℝ) ^ (8 / 17 : ℝ) := Real.rpow_pos_of_pos hx _
    field_simp
  have hb : (((N : ℝ) + 1) / N) ^ (8 / 17 : ℝ) ≤ 1 + 8 / (17 * (N : ℝ)) := by
    have h1 : (((N : ℝ) + 1) / N) = 1 + 1 / (N : ℝ) := by field_simp
    have := rpow_one_add_le_one_add_mul_self (s := 1 / (N : ℝ)) (by
      have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
      linarith) (p := 8 / 17) (by norm_num) (by norm_num)
    rw [h1]
    refine this.trans (le_of_eq ?_)
    field_simp
  rw [Lemma21_rhotN_eq' hN, Lemma21_rhotN_eq' hN1, hr]
  have hρ1 : 0 < rhoN (N + 1) := Real.rpow_pos_of_pos (by positivity) _
  calc (((N : ℝ) + 1) / N) ^ (8 / 17 : ℝ) * rhoN (N + 1) / (1 + 2 * Lemma21_s N) ^ 3
      ≤ (((N : ℝ) + 1) / N) ^ (8 / 17 : ℝ) * rhoN (N + 1) / (1 + 2 * Lemma21_s (N + 1)) ^ 3 := by
        gcongr
    _ = (((N : ℝ) + 1) / N) ^ (8 / 17 : ℝ) * (rhoN (N + 1) / (1 + 2 * Lemma21_s (N + 1)) ^ 3) := by
        ring
    _ ≤ (1 + 8 / (17 * (N : ℝ))) * (rhoN (N + 1) / (1 + 2 * Lemma21_s (N + 1)) ^ 3) := by
        gcongr


/-- `(√ρ)⁻¹ ≤ 6 (N+1)^{4/17}` when `ρ > ρ̃_{N+1}`. -/
private lemma Lemma21_sqrt_lb {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (h : rhotN (N + 1) < ρ) :
    (ρ ^ (1 / 2 : ℝ))⁻¹ ≤ 6 * ((N : ℝ) + 1) ^ (4 / 17 : ℝ) := by
  have hN1 : 1 ≤ N + 1 := by omega
  have hs := Lemma21_s_pos hN1
  have hs1 := Lemma21_s_le_one hN1
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have h1 : Lemma21_s (N + 1) ^ (48 / 25 : ℝ) / 27 ≤ rhotN (N + 1) := by
    rw [Lemma21_rhotN_eq hN1]
    have : (1 + 2 * Lemma21_s (N + 1)) ^ 3 ≤ 27 := by
      have h3 : 1 + 2 * Lemma21_s (N + 1) ≤ 3 := by linarith
      calc (1 + 2 * Lemma21_s (N + 1)) ^ 3 ≤ 3 ^ 3 := by gcongr
        _ = 27 := by norm_num
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hs.le _) (by positivity) this
  have h2 : (Lemma21_s (N + 1) ^ (24 / 25 : ℝ) / 6) ^ 2 ≤ ρ := by
    have e : (Lemma21_s (N + 1) ^ (24 / 25 : ℝ)) ^ 2 = Lemma21_s (N + 1) ^ (48 / 25 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
      norm_num
    have hp : 0 ≤ Lemma21_s (N + 1) ^ (48 / 25 : ℝ) := Real.rpow_nonneg hs.le _
    rw [div_pow, e]
    have : Lemma21_s (N + 1) ^ (48 / 25 : ℝ) / 6 ^ 2 ≤ Lemma21_s (N + 1) ^ (48 / 25 : ℝ) / 27 :=
      div_le_div_of_nonneg_left hp (by norm_num) (by norm_num)
    linarith
  have h3 : Lemma21_s (N + 1) ^ (24 / 25 : ℝ) / 6 ≤ ρ ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq (by have := Real.rpow_nonneg hs.le (24 / 25 : ℝ); positivity)] at this
  have h4 : Lemma21_s (N + 1) ^ (24 / 25 : ℝ) = ((N : ℝ) + 1) ^ (-(4 / 17 : ℝ)) := by
    unfold Lemma21_s
    push_cast
    rw [← Real.rpow_mul hpos.le]
    norm_num
  have h5 : 0 < Lemma21_s (N + 1) ^ (24 / 25 : ℝ) := Real.rpow_pos_of_pos hs _
  calc (ρ ^ (1 / 2 : ℝ))⁻¹ ≤ (Lemma21_s (N + 1) ^ (24 / 25 : ℝ) / 6)⁻¹ :=
        inv_anti₀ (by positivity) h3
    _ = 6 * ((N : ℝ) + 1) ^ (4 / 17 : ℝ) := by
        rw [h4, Real.rpow_neg hpos.le]
        field_simp

/-- `N⁻¹ (N + 1)^{4/17} → 0`. -/
private lemma Lemma21_tendsto_W :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ((N : ℝ) + 1) ^ (4 / 17 : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => 2 * (N : ℝ) ^ (-(13 / 17 : ℝ))) atTop (𝓝 (2 * 0)) :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 13 / 17)).comp
      tendsto_natCast_atTop_atTop).const_mul 2
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · exact Eventually.of_forall fun N => by positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hx : (0 : ℝ) < N := by exact_mod_cast hN
    have hx1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have h1 : ((N : ℝ) + 1) ^ (4 / 17 : ℝ) ≤ 2 * (N : ℝ) ^ (4 / 17 : ℝ) := by
      calc ((N : ℝ) + 1) ^ (4 / 17 : ℝ) ≤ (2 * N) ^ (4 / 17 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ = 2 ^ (4 / 17 : ℝ) * (N : ℝ) ^ (4 / 17 : ℝ) := Real.mul_rpow (by norm_num) hx.le
        _ ≤ 2 * (N : ℝ) ^ (4 / 17 : ℝ) := by
            gcongr
            calc (2 : ℝ) ^ (4 / 17 : ℝ) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
    calc (N : ℝ)⁻¹ * ((N : ℝ) + 1) ^ (4 / 17 : ℝ) ≤ (N : ℝ)⁻¹ * (2 * (N : ℝ) ^ (4 / 17 : ℝ)) := by
          gcongr
      _ = 2 * (N : ℝ) ^ (-(13 / 17 : ℝ)) := by
          have : (N : ℝ) ^ (-(13 / 17 : ℝ)) = (N : ℝ)⁻¹ * (N : ℝ) ^ (4 / 17 : ℝ) := by
            rw [← Real.rpow_neg_one, ← Real.rpow_add hx]
            norm_num
          rw [this]
          ring

/-- The bound at `N` for the ratio at density `ρ` shifted from `ρ̃_N`, tending to `K`. -/
private lemma Lemma21_tendsto_B (g K : ℝ) :
    Tendsto (fun N : ℕ => K * (1 + 8 / 17 * (N : ℝ)⁻¹) ^ (3 / 2 : ℝ) +
      (g ^ (3 / 2 : ℝ))⁻¹ * (48 / 17 * ((N : ℝ)⁻¹ * ((N : ℝ) + 1) ^ (4 / 17 : ℝ)))) atTop
      (𝓝 K) := by
  have h1 : Tendsto (fun N : ℕ => 1 + 8 / 17 * (N : ℝ)⁻¹) atTop (𝓝 (1 + 8 / 17 * 0)) :=
    tendsto_const_nhds.add
      ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _)
  have h2 := (h1.rpow_const (p := (3 / 2 : ℝ)) (Or.inr (by norm_num))).const_mul K
  have h3 := (Lemma21_tendsto_W.const_mul (48 / 17 : ℝ)).const_mul ((g ^ (3 / 2 : ℝ))⁻¹)
  have := h2.add h3
  norm_num at this
  exact this

/-- The ratio of (2.4) at a real energy per particle is a real number. -/
private lemma Lemma21_ratio_coe (g ρ E : ℝ) :
    ratio g ρ (E : EReal) =
      (((E - g * ρ) * (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹ : ℝ) : EReal) := by
  unfold ratio
  rw [← EReal.coe_sub, ← EReal.coe_mul]


/-- `g ρ / (g^{5/2} ρ^{3/2}) = (g^{3/2})⁻¹ (ρ^{1/2})⁻¹`. -/
private lemma Lemma21_gap_eq {g ρ : ℝ} (hg : 0 < g) (hρ : 0 < ρ) :
    g * ρ * (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹ = (g ^ (3 / 2 : ℝ))⁻¹ * (ρ ^ (1 / 2 : ℝ))⁻¹ := by
  have e1 : g ^ (5 / 2 : ℝ) = g * g ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hg.le (by norm_num)]
    norm_num
  have e2 : ρ ^ (3 / 2 : ℝ) = ρ * ρ ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_one_add' hρ.le (by norm_num)]
    norm_num
  have h1 : 0 < g ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hg _
  have h2 : 0 < ρ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  rw [e1, e2]
  field_simp

/-- Shifting the density from `ρ'` down to `ρ ≥ ρ' / (1 + δ)` in the ratio of (2.4). -/
private lemma Lemma21_shift {g ρ ρ' E K δ : ℝ} (hg : 0 < g) (hρ : 0 < ρ) (hρρ' : ρ ≤ ρ')
    (hδ : ρ' ≤ (1 + δ) * ρ) (hδ0 : 0 ≤ δ) (hK : 0 ≤ K)
    (hE : (E - g * ρ') * (g ^ (5 / 2 : ℝ) * ρ' ^ (3 / 2 : ℝ))⁻¹ ≤ K) :
    (E - g * ρ) * (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹ ≤
      K * (1 + δ) ^ (3 / 2 : ℝ) + (g ^ (3 / 2 : ℝ))⁻¹ * δ * (ρ ^ (1 / 2 : ℝ))⁻¹ := by
  have hρ' : 0 < ρ' := lt_of_lt_of_le hρ hρρ'
  have hD' : 0 < g ^ (5 / 2 : ℝ) * ρ' ^ (3 / 2 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hg _) (Real.rpow_pos_of_pos hρ' _)
  have hD : 0 < g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ) :=
    mul_pos (Real.rpow_pos_of_pos hg _) (Real.rpow_pos_of_pos hρ _)
  have h1 : E - g * ρ' ≤ K * (g ^ (5 / 2 : ℝ) * ρ' ^ (3 / 2 : ℝ)) := by
    have := mul_le_mul_of_nonneg_right hE hD'.le
    rwa [mul_assoc, inv_mul_cancel₀ hD'.ne', mul_one] at this
  have h2 : ρ' ^ (3 / 2 : ℝ) ≤ (1 + δ) ^ (3 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ) := by
    rw [← Real.mul_rpow (by linarith) hρ.le]
    exact Real.rpow_le_rpow hρ'.le hδ (by norm_num)
  have h3 : E - g * ρ ≤ K * ((1 + δ) ^ (3 / 2 : ℝ) * (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))) +
      g * ρ * δ := by
    have : K * (g ^ (5 / 2 : ℝ) * ρ' ^ (3 / 2 : ℝ)) ≤
        K * ((1 + δ) ^ (3 / 2 : ℝ) * (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ hK
      calc g ^ (5 / 2 : ℝ) * ρ' ^ (3 / 2 : ℝ) ≤ g ^ (5 / 2 : ℝ) * ((1 + δ) ^ (3 / 2 : ℝ) *
            ρ ^ (3 / 2 : ℝ)) := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hg.le _)
        _ = _ := by ring
    have h4 : g * (ρ' - ρ) ≤ g * ρ * δ := by
      have : ρ' - ρ ≤ ρ * δ := by linarith
      nlinarith
    linarith
  calc (E - g * ρ) * (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹
      ≤ (K * ((1 + δ) ^ (3 / 2 : ℝ) * (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))) + g * ρ * δ) *
        (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹ := mul_le_mul_of_nonneg_right h3 (inv_nonneg.2 hD.le)
    _ = K * (1 + δ) ^ (3 / 2 : ℝ) + (g * ρ * (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹) * δ := by
        field_simp
    _ = _ := by rw [Lemma21_gap_eq hg hρ]; ring

/-- `ρ̃^2 (g^{5/2} ρ̃^{3/2})⁻¹ = (g^{5/2})⁻¹ ρ̃^{1/2}`. -/
private lemma Lemma21_corr_eq {g u : ℝ} (hg : 0 < g) (hu : 0 < u) :
    u ^ 2 * (g ^ (5 / 2 : ℝ) * u ^ (3 / 2 : ℝ))⁻¹ = (g ^ (5 / 2 : ℝ))⁻¹ * u ^ (1 / 2 : ℝ) := by
  have e2 : u ^ 2 = u ^ (3 / 2 : ℝ) * u ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hu]
    norm_num
  have h1 : 0 < g ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hg _
  have h2 : 0 < u ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hu _
  rw [e2]
  field_simp

/-- The near-minimizer correction `ρ̃_N² (g^{5/2} ρ̃_N^{3/2})⁻¹` tends to `0`. -/
private lemma Lemma21_tendsto_corr {g : ℝ} (hg : 0 < g) :
    Tendsto (fun N : ℕ => rhotN N ^ 2 * (g ^ (5 / 2 : ℝ) * rhotN N ^ (3 / 2 : ℝ))⁻¹) atTop
      (𝓝 0) := by
  have h : ContinuousAt (fun u : ℝ => (g ^ (5 / 2 : ℝ))⁻¹ * u ^ (1 / 2 : ℝ)) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 _ (Or.inr (by norm_num)))
  have h2 := h.tendsto.comp Lemma21_tendsto_rhotN
  rw [Real.zero_rpow (by norm_num), mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (Lemma21_corr_eq hg (Lemma21_rhotN_pos hN)).symm

/-- A trial function on `[0, L]³` is a trial function on every larger box. -/
private lemma Lemma21_trial_mono {L L' : ℝ} (h : L ≤ L') {N : ℕ} {Ψ : Conf N → ℂ}
    (hΨ : IsDirichletTrial L N Ψ) : IsDirichletTrial L' N Ψ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hΨ
  exact ⟨h1, h2, fun x hx i a => ⟨(h3 hx i a).1, (h3 hx i a).2.trans_le h⟩, h4, h5⟩

/-- `e₀^D` is a real number on a box of positive side, for `V ≥ 0`. -/
private lemma Lemma21_e0D_real {V : R3 → ℝ} (hV : ∀ x, 0 ≤ V x) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    ∃ r : ℝ, e0D L V N = (r : EReal) :=
  ⟨(e0D L V N).toReal, (EReal.coe_toReal (e0D_lt_top hL V N).ne
    (ne_bot_of_le_ne_bot (by simp) (e0D_nonneg hV L N))).symm⟩

/-- Selection of `N(ρ)`: `ρ̃_{N+1} < ρ ≤ ρ̃_N` with `N ≥ M`, for `0 < ρ < ρ̃_M`. -/
private lemma Lemma21_select {M : ℕ} {ρ : ℝ} (hρ : 0 < ρ) (hρM : ρ < rhotN M) :
    ∃ N : ℕ, M ≤ N ∧ rhotN (N + 1) < ρ ∧ ρ ≤ rhotN N := by
  have hex : ∃ k : ℕ, rhotN (k + M + 1) < ρ := by
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (Lemma21_tendsto_rhotN.eventually (gt_mem_nhds hρ))
    exact ⟨n₀, hn₀ _ (by omega)⟩
  refine ⟨Nat.find hex + M, by omega, Nat.find_spec hex, ?_⟩
  by_cases hk : Nat.find hex = 0
  · rw [hk, zero_add]
    exact hρM.le
  · obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk
    have := Nat.find_min hex (m := k') (by omega)
    push Not at this
    rw [hk']
    convert this using 2
    omega


/-- Lemma 2.1 [thm1], for each `N`: a Dirichlet trial state on `[0, L̃_N]³` at density `ρ̃_N`. -/
theorem Lemma2_1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma2_1 V w := by
  have hg := scat_g0_pos hV hw
  set g := g0 V w with hgdef
  have key : ∀ N : ℕ, ∃ Φ : Conf N → ℂ, 1 ≤ N → (IsDirichletTrial (LtN N) N Φ ∧
      ((energyD V Φ / N : ℝ) : EReal) < e0D (LtN N) V N + ((rhotN N ^ 2 : ℝ) : EReal)) := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨Φ, h1, h2⟩ := exists_lt_e0D hV.nonneg (Lemma21_LtN_pos hN) N
        (δ := rhotN N ^ 2) (by have := Lemma21_rhotN_pos hN; positivity)
      exact ⟨Φ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Φ hΦ using key
  refine ⟨Φ, ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (hΦ N hN).1
  · have hlim := Lemma2_2 hV hw (e0P_limsup_le hV hw)
    refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
    have hε : 0 < z - cLHY := by
      have := EReal.coe_lt_coe_iff.1 hz
      linarith
    have e1 : ∀ᶠ N : ℕ in atTop,
        ratio g (rhotN N) (e0D (LtN N) V N) < ((cLHY + (z - cLHY) / 2 : ℝ) : EReal) :=
      eventually_lt_of_limsup_lt
        (lt_of_le_of_lt hlim (EReal.coe_lt_coe_iff.2 (by linarith)))
    have e2 : ∀ᶠ N : ℕ in atTop,
        rhotN N ^ 2 * (g ^ (5 / 2 : ℝ) * rhotN N ^ (3 / 2 : ℝ))⁻¹ < (z - cLHY) / 2 :=
      (Lemma21_tendsto_corr hg).eventually_lt_const (by linarith)
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [e1, e2, eventually_ge_atTop 1] with N h1 h2 hN
    obtain ⟨r, hr⟩ := Lemma21_e0D_real hV.nonneg (Lemma21_LtN_pos hN) N
    have hρ := Lemma21_rhotN_pos hN
    have hDpos : 0 < (g ^ (5 / 2 : ℝ) * rhotN N ^ (3 / 2 : ℝ))⁻¹ :=
      inv_pos.2 (mul_pos (Real.rpow_pos_of_pos hg _) (Real.rpow_pos_of_pos hρ _))
    have h3 := (hΦ N hN).2
    rw [hr, ← EReal.coe_add, EReal.coe_lt_coe_iff] at h3
    rw [hr, Lemma21_ratio_coe, EReal.coe_lt_coe_iff] at h1
    rw [Lemma21_ratio_coe, EReal.coe_le_coe_iff]
    have h4 : (energyD V (Φ N) / N - g * rhotN N) * (g ^ (5 / 2 : ℝ) * rhotN N ^ (3 / 2 : ℝ))⁻¹ ≤
        (r + rhotN N ^ 2 - g * rhotN N) * (g ^ (5 / 2 : ℝ) * rhotN N ^ (3 / 2 : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hDpos.le
    have h5 : (r + rhotN N ^ 2 - g * rhotN N) * (g ^ (5 / 2 : ℝ) * rhotN N ^ (3 / 2 : ℝ))⁻¹ =
        (r - g * rhotN N) * (g ^ (5 / 2 : ℝ) * rhotN N ^ (3 / 2 : ℝ))⁻¹ +
          rhotN N ^ 2 * (g ^ (5 / 2 : ℝ) * rhotN N ^ (3 / 2 : ℝ))⁻¹ := by ring
    linarith


/-- The exponent bookkeeping of the box limit: `P v^{-1/3} (vT)^{25/24} = P T^{25/24} v^{17/24}`. -/
private lemma Lemma21_box_alg {P T v : ℝ} (hT : 0 < T) (hv : 0 < v) :
    P * v ^ (-(1 / 3 : ℝ)) * (v * T) ^ (25 / 24 : ℝ) =
      P * T ^ (25 / 24 : ℝ) * v ^ (17 / 24 : ℝ) := by
  rw [Real.mul_rpow hv.le hT.le]
  have : v ^ (-(1 / 3 : ℝ)) * v ^ (25 / 24 : ℝ) = v ^ (17 / 24 : ℝ) := by
    rw [← Real.rpow_add hv]
    norm_num
  calc P * v ^ (-(1 / 3 : ℝ)) * (v ^ (25 / 24 : ℝ) * T ^ (25 / 24 : ℝ))
      = P * T ^ (25 / 24 : ℝ) * (v ^ (-(1 / 3 : ℝ)) * v ^ (25 / 24 : ℝ)) := by ring
    _ = _ := by rw [this]

/-- The box `L(ρ) = (N/ρ)^{1/3}` equals `L̃_N (ρ̃_N/ρ)^{1/3}`. -/
private lemma Lemma21_box_eq {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (hρ : 0 < ρ) :
    ((N : ℝ) / ρ) ^ (1 / 3 : ℝ) = LtN N * (ρ / rhotN N) ^ (-(1 / 3 : ℝ)) := by
  have hT := Lemma21_rhotN_pos hN
  have hP := Lemma21_LtN_pos hN
  have hv : 0 < ρ / rhotN N := div_pos hρ hT
  have hPT := Lemma21_LtN_pow hN
  have h1 : (N : ℝ) / ρ = LtN N ^ 3 * (ρ / rhotN N)⁻¹ := by
    rw [← hPT]
    field_simp
  rw [h1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hP.le, Real.rpow_neg hv.le, Real.inv_rpow hv.le]
  norm_num

/-- `L(ρ) ρ^{25/24} = L̃_N ρ̃_N^{25/24} (ρ/ρ̃_N)^{17/24}` for `L(ρ) = (N/ρ)^{1/3}`. -/
private lemma Lemma21_box_prod {N : ℕ} (hN : 1 ≤ N) {ρ : ℝ} (hρ : 0 < ρ) :
    ((N : ℝ) / ρ) ^ (1 / 3 : ℝ) * ρ ^ (25 / 24 : ℝ) =
      LtN N * rhotN N ^ (25 / 24 : ℝ) * (ρ / rhotN N) ^ (17 / 24 : ℝ) := by
  have hT := Lemma21_rhotN_pos hN
  have hv : 0 < ρ / rhotN N := div_pos hρ hT
  rw [Lemma21_box_eq hN hρ]
  have e : ρ ^ (25 / 24 : ℝ) = (ρ / rhotN N * rhotN N) ^ (25 / 24 : ℝ) := by
    rw [div_mul_cancel₀ _ hT.ne']
  rw [e]
  exact Lemma21_box_alg hT hv

/-- Lemma 2.1 [thm1] in the paper's form: for `ρ` small enough there are a box side
`L(ρ)` with `L(ρ) ρ^{25/24} → 1` and a Dirichlet trial state of `N(ρ) = ρ L(ρ)³` particles on
`[0, L(ρ)]³` whose ratio has upper limit at most `16/(15π²)` as `ρ → 0`. -/
theorem Lemma2_1_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ Nρ : ℝ → ℕ, ∃ Lρ : ℝ → ℝ, ∃ Ψ : (ρ : ℝ) → Conf (Nρ ρ) → ℂ,
      (∀ ρ ∈ Set.Ioo 0 ρ₀, 0 < Lρ ρ ∧ (Nρ ρ : ℝ) = ρ * Lρ ρ ^ 3 ∧
        IsDirichletTrial (Lρ ρ) (Nρ ρ) (Ψ ρ)) ∧
      Tendsto (fun ρ => Lρ ρ * ρ ^ (25 / 24 : ℝ)) (𝓝[>] 0) (𝓝 1) ∧
      limsup (fun ρ => ratio (g0 V w) ρ ((energyD V (Ψ ρ) / Nρ ρ : ℝ) : EReal)) (𝓝[>] 0)
        ≤ (cLHY : EReal) := by
  have hg := scat_g0_pos hV hw
  set g := g0 V w with hgdef
  obtain ⟨Φ, hΦtrial, hΦlim⟩ := Lemma2_1 hV hw
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hΦtrial
  obtain ⟨M, hM2, hM0⟩ : ∃ M : ℕ, 2 ≤ M ∧ N₀ ≤ M := ⟨max N₀ 2, le_max_right _ _, le_max_left _ _⟩
  have hρ₀ : 0 < rhotN M := Lemma21_rhotN_pos (by omega)
  have hsel : ∀ ρ : ℝ, ∃ N : ℕ, (0 < ρ ∧ ρ < rhotN M) →
      M ≤ N ∧ rhotN (N + 1) < ρ ∧ ρ ≤ rhotN N := by
    intro ρ
    by_cases h : 0 < ρ ∧ ρ < rhotN M
    · obtain ⟨N, h1, h2, h3⟩ := Lemma21_select h.1 h.2
      exact ⟨N, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose Nρ hNρ using hsel
  have hmem : ∀ ρ ∈ Set.Ioo 0 (rhotN M),
      M ≤ Nρ ρ ∧ rhotN (Nρ ρ + 1) < ρ ∧ ρ ≤ rhotN (Nρ ρ) := fun ρ hρ => hNρ ρ hρ
  have hNlim : Tendsto Nρ (𝓝[>] (0 : ℝ)) atTop := by
    refine tendsto_atTop.2 fun K => ?_
    have hK : 0 < min (rhotN M) (rhotN (max K 2)) :=
      lt_min hρ₀ (Lemma21_rhotN_pos (by omega))
    filter_upwards [Ioo_mem_nhdsGT hK] with ρ hρ
    obtain ⟨h1, h2, h3⟩ := hmem ρ ⟨hρ.1, lt_of_lt_of_le hρ.2 (min_le_left _ _)⟩
    have h4 : ρ < rhotN (max K 2) := lt_of_lt_of_le hρ.2 (min_le_right _ _)
    by_contra hcon
    push Not at hcon
    have h5 := rhotN_strictAntiOn.antitoneOn (Set.mem_Ici.2 (by omega : 2 ≤ Nρ ρ + 1))
      (Set.mem_Ici.2 (by omega : 2 ≤ max K 2)) (by omega : Nρ ρ + 1 ≤ max K 2)
    linarith
  have hmemIoo : Set.Ioo 0 (rhotN M) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hρ₀
  refine ⟨rhotN M, hρ₀, Nρ, fun ρ => ((Nρ ρ : ℝ) / ρ) ^ (1 / 3 : ℝ), fun ρ => Φ (Nρ ρ), ?_, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨h1, h2, h3⟩ := hmem ρ hρ
    have hN1 : 1 ≤ Nρ ρ := by omega
    have hn : 0 < (Nρ ρ : ℝ) := by exact_mod_cast hN1
    have hnρ : 0 < (Nρ ρ : ℝ) / ρ := div_pos hn hρ.1
    have hL3 : (((Nρ ρ : ℝ) / ρ) ^ (1 / 3 : ℝ)) ^ 3 = (Nρ ρ : ℝ) / ρ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnρ.le]
      norm_num
    refine ⟨Real.rpow_pos_of_pos hnρ _, ?_, ?_⟩
    · change (Nρ ρ : ℝ) = ρ * (((Nρ ρ : ℝ) / ρ) ^ (1 / 3 : ℝ)) ^ 3
      have hρne : ρ ≠ 0 := hρ.1.ne'
      rw [hL3]
      field_simp
    · refine Lemma21_trial_mono ?_ (hN₀ _ (by omega))
      have hP := Lemma21_LtN_pos hN1
      have hT := Lemma21_rhotN_pos hN1
      have hPT : LtN (Nρ ρ) ^ 3 = (Nρ ρ : ℝ) / rhotN (Nρ ρ) := by
        rw [eq_div_iff hT.ne']
        exact Lemma21_LtN_pow hN1
      refine le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0)
        (Real.rpow_nonneg hnρ.le _) ?_
      rw [hL3, hPT]
      exact div_le_div_of_nonneg_left hn.le hρ.1 h3
  · have hv : Tendsto (fun ρ : ℝ => ρ / rhotN (Nρ ρ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hlow : Tendsto (fun ρ : ℝ => (1 + 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹)⁻¹) (𝓝[>] (0 : ℝ))
          (𝓝 1) := by
        have h1 : Tendsto (fun N : ℕ => (1 + 8 / 17 * (N : ℝ)⁻¹)⁻¹) atTop
            (𝓝 ((1 + 8 / 17 * 0)⁻¹)) :=
          (tendsto_const_nhds.add
            ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul _)).inv₀
            (by norm_num)
        have := h1.comp hNlim
        norm_num at this
        exact this
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [hmemIoo] with ρ hρ
        obtain ⟨h1, h2, h3⟩ := hmem ρ hρ
        have hN1 : 1 ≤ Nρ ρ := by omega
        have hT := Lemma21_rhotN_pos hN1
        have hn : (0 : ℝ) < (Nρ ρ : ℝ) := by exact_mod_cast hN1
        have h4 := Lemma21_rhotN_le_succ hN1
        have hpos : (0 : ℝ) < 1 + 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹ := by positivity
        have e : 8 / (17 * ((Nρ ρ : ℕ) : ℝ)) = 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹ := by ring
        rw [e] at h4
        rw [le_div_iff₀ hT, inv_mul_le_iff₀ hpos]
        calc rhotN (Nρ ρ) ≤ (1 + 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) * rhotN (Nρ ρ + 1) := h4
          _ ≤ (1 + 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) * ρ := by gcongr
      · filter_upwards [hmemIoo] with ρ hρ
        obtain ⟨h1, h2, h3⟩ := hmem ρ hρ
        exact (div_le_one (Lemma21_rhotN_pos (by omega))).2 h3
    have hprod : Tendsto (fun ρ : ℝ => LtN (Nρ ρ) * rhotN (Nρ ρ) ^ (25 / 24 : ℝ) *
        (ρ / rhotN (Nρ ρ)) ^ (17 / 24 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h1 := tendsto_LtN_mul_rhotN.comp hNlim
      have h2 := hv.rpow_const (p := (17 / 24 : ℝ)) (Or.inl one_ne_zero)
      rw [Real.one_rpow] at h2
      simpa using h1.mul h2
    refine hprod.congr' ?_
    filter_upwards [hmemIoo] with ρ hρ
    obtain ⟨h1, h2, h3⟩ := hmem ρ hρ
    exact (Lemma21_box_prod (by omega) hρ.1).symm
  · refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
    have hε : 0 < z - cLHY := by
      have := EReal.coe_lt_coe_iff.1 hz
      linarith
    have e1 : ∀ᶠ N : ℕ in atTop, ratio g (rhotN N) ((energyD V (Φ N) / N : ℝ) : EReal) <
        ((cLHY + (z - cLHY) / 2 : ℝ) : EReal) :=
      eventually_lt_of_limsup_lt
        (lt_of_le_of_lt hΦlim (EReal.coe_lt_coe_iff.2 (by linarith)))
    have e2 : ∀ᶠ N : ℕ in atTop, (cLHY + (z - cLHY) / 2) * (1 + 8 / 17 * (N : ℝ)⁻¹) ^ (3 / 2 : ℝ) +
        (g ^ (3 / 2 : ℝ))⁻¹ * (48 / 17 * ((N : ℝ)⁻¹ * ((N : ℝ) + 1) ^ (4 / 17 : ℝ))) < z :=
      (Lemma21_tendsto_B g (cLHY + (z - cLHY) / 2)).eventually_lt_const (by linarith)
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 (e1.and (e2.and (eventually_ge_atTop 1)))
    have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), N₁ ≤ Nρ ρ ∧ ρ ∈ Set.Ioo 0 (rhotN M) :=
      (hNlim.eventually_ge_atTop N₁).and hmemIoo
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [hev] with ρ hρ'
    obtain ⟨hN, hρ⟩ := hρ'
    obtain ⟨h1, h2, h3⟩ := hmem ρ hρ
    obtain ⟨he1, he2, hN1⟩ := hN₁ (Nρ ρ) hN
    have hn : (0 : ℝ) < (Nρ ρ : ℝ) := by exact_mod_cast hN1
    have hT := Lemma21_rhotN_pos hN1
    rw [Lemma21_ratio_coe, EReal.coe_lt_coe_iff] at he1
    change ratio g ρ ((energyD V (Φ (Nρ ρ)) / (Nρ ρ : ℕ) : ℝ) : EReal) ≤ (z : EReal)
    rw [Lemma21_ratio_coe, EReal.coe_le_coe_iff]
    have hδ0 : (0 : ℝ) ≤ 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹ := by positivity
    have hδ : rhotN (Nρ ρ) ≤ (1 + 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) * ρ := by
      have h4 := Lemma21_rhotN_le_succ hN1
      have e : 8 / (17 * ((Nρ ρ : ℕ) : ℝ)) = 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹ := by ring
      rw [e] at h4
      calc rhotN (Nρ ρ) ≤ (1 + 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) * rhotN (Nρ ρ + 1) := h4
        _ ≤ (1 + 8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) * ρ := by gcongr
    have hK : 0 ≤ cLHY + (z - cLHY) / 2 := by
      have : 0 < cLHY := by unfold cLHY; positivity
      linarith
    have hs := Lemma21_shift hg hρ.1 h3 hδ hδ0 hK he1.le
    have hsq := Lemma21_sqrt_lb hN1 h2
    have hc : 0 ≤ (g ^ (3 / 2 : ℝ))⁻¹ * (8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) := by positivity
    have h5 : (g ^ (3 / 2 : ℝ))⁻¹ * (8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) * (ρ ^ (1 / 2 : ℝ))⁻¹ ≤
        (g ^ (3 / 2 : ℝ))⁻¹ * (8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) *
          (6 * (((Nρ ρ : ℕ) : ℝ) + 1) ^ (4 / 17 : ℝ)) := mul_le_mul_of_nonneg_left hsq hc
    have h6 : (g ^ (3 / 2 : ℝ))⁻¹ * (8 / 17 * ((Nρ ρ : ℕ) : ℝ)⁻¹) *
          (6 * (((Nρ ρ : ℕ) : ℝ) + 1) ^ (4 / 17 : ℝ)) =
        (g ^ (3 / 2 : ℝ))⁻¹ *
          (48 / 17 * (((Nρ ρ : ℕ) : ℝ)⁻¹ * (((Nρ ρ : ℕ) : ℝ) + 1) ^ (4 / 17 : ℝ))) := by
      ring
    linarith

end LHYUpper
