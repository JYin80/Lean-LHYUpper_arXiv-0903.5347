import LHYUpper.Scattering.Solution

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- The smooth ramp `s(τ)`: `0` for `τ ≤ 1/4`, `1` for `τ ≥ 3/4`. -/
def ramp (τ : ℝ) : ℝ := Real.smoothTransition (2 * τ - 1 / 2)

/-- The constant `C_s = ∫_0^1 s'(τ)² dτ` of the ramp. -/
def rampConst : ℝ := ∫ τ in (0 : ℝ)..1, deriv ramp τ ^ 2

/-- The phase `φ(x) = (π/2) s((ℓ - x)/(2ℓ))`. -/
def phase (ℓ x : ℝ) : ℝ := π / 2 * ramp ((ℓ - x) / (2 * ℓ))

/-- The smooth profile `q(x) = cos φ(x) · sin φ(x - L)` replacing `q` of (12.1): `0` outside
`[-ℓ, L + ℓ]`, `1` on `[ℓ, L - ℓ]`, `q(x)² + q(x + L)² = 1` on the ramp. -/
def prof (ℓ L x : ℝ) : ℝ := Real.cos (phase ℓ x) * Real.sin (phase ℓ (x - L))

/-- The cut-off `h(y) = q(y¹) q(y²) q(y³)` of (12.1). -/
def cutoff (ℓ L : ℝ) (y : R3) : ℝ := ∏ a, prof ℓ L (y a)

/-- The periodized squared slope `w(x) = Σ_m q'(x + mL)²`, the weight of (12.3) [3.51]. -/
def profW (ℓ L x : ℝ) : ℝ := ∑' m : ℤ, deriv (prof ℓ L) (x + m * L) ^ 2

/-! ### The ramp and the phase -/

private lemma Profile_ramp_of_le {τ : ℝ} (h : τ ≤ 1 / 4) : ramp τ = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

private lemma Profile_ramp_of_ge {τ : ℝ} (h : 3 / 4 ≤ τ) : ramp τ = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

private lemma Profile_ramp_contDiff : ContDiff ℝ (⊤ : ℕ∞) ramp :=
  Real.smoothTransition.contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const))

private lemma Profile_phase_contDiff (ℓ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (phase ℓ) :=
  contDiff_const.mul (Profile_ramp_contDiff.comp
    ((contDiff_const.sub contDiff_id).div_const _))

private lemma Profile_phase_of_le {ℓ x : ℝ} (hℓ : 0 < ℓ) (h : x ≤ -(ℓ / 2)) :
    phase ℓ x = π / 2 := by
  unfold phase
  rw [Profile_ramp_of_ge, mul_one]
  rw [le_div_iff₀ (by positivity)]
  linarith

private lemma Profile_phase_of_ge {ℓ x : ℝ} (hℓ : 0 < ℓ) (h : ℓ / 2 ≤ x) : phase ℓ x = 0 := by
  unfold phase
  rw [Profile_ramp_of_le, mul_zero]
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- If `ψ` is constant on `(-∞, a]` and `deriv ψ` is continuous, then `deriv ψ = 0` there. -/
private lemma Profile_deriv_zero_Iic {ψ : ℝ → ℝ} (hψ : Continuous (deriv ψ)) {a c : ℝ}
    (h : ∀ y ≤ a, ψ y = c) : ∀ y ≤ a, deriv ψ y = 0 := by
  have hS : IsClosed {y | deriv ψ y = 0} := isClosed_eq hψ continuous_const
  have hsub : Set.Iio a ⊆ {y | deriv ψ y = 0} := by
    intro y hy
    have : ψ =ᶠ[𝓝 y] fun _ => c :=
      Filter.eventuallyEq_of_mem (Iio_mem_nhds hy) (fun z hz => h z (le_of_lt hz))
    simp [this.deriv_eq]
  have := closure_minimal hsub hS
  rw [closure_Iio] at this
  exact fun y hy => this hy

/-- If `ψ` is constant on `[a, ∞)` and `deriv ψ` is continuous, then `deriv ψ = 0` there. -/
private lemma Profile_deriv_zero_Ici {ψ : ℝ → ℝ} (hψ : Continuous (deriv ψ)) {a c : ℝ}
    (h : ∀ y, a ≤ y → ψ y = c) : ∀ y, a ≤ y → deriv ψ y = 0 := by
  have hS : IsClosed {y | deriv ψ y = 0} := isClosed_eq hψ continuous_const
  have hsub : Set.Ioi a ⊆ {y | deriv ψ y = 0} := by
    intro y hy
    have : ψ =ᶠ[𝓝 y] fun _ => c :=
      Filter.eventuallyEq_of_mem (Ioi_mem_nhds hy) (fun z hz => h z (le_of_lt hz))
    simp [this.deriv_eq]
  have := closure_minimal hsub hS
  rw [closure_Ioi] at this
  exact fun y hy => this hy

private lemma Profile_continuous_deriv_ramp : Continuous (deriv ramp) :=
  Profile_ramp_contDiff.continuous_deriv (by simp)

private lemma Profile_continuous_deriv_phase (ℓ : ℝ) : Continuous (deriv (phase ℓ)) :=
  (Profile_phase_contDiff ℓ).continuous_deriv (by simp)

private lemma Profile_deriv_ramp_zero {τ : ℝ} (h : τ ≤ 1 / 4 ∨ 3 / 4 ≤ τ) : deriv ramp τ = 0 := by
  rcases h with h | h
  · exact Profile_deriv_zero_Iic Profile_continuous_deriv_ramp
      (fun y hy => Profile_ramp_of_le hy) τ h
  · exact Profile_deriv_zero_Ici Profile_continuous_deriv_ramp
      (fun y hy => Profile_ramp_of_ge hy) τ h

private lemma Profile_deriv_phase_zero {ℓ z : ℝ} (hℓ : 0 < ℓ)
    (h : z ≤ -(ℓ / 2) ∨ ℓ / 2 ≤ z) : deriv (phase ℓ) z = 0 := by
  rcases h with h | h
  · exact Profile_deriv_zero_Iic (Profile_continuous_deriv_phase ℓ)
      (fun y hy => Profile_phase_of_le hℓ hy) z h
  · exact Profile_deriv_zero_Ici (Profile_continuous_deriv_phase ℓ)
      (fun y hy => Profile_phase_of_ge hℓ hy) z h

/-! ### Values of the profile -/

private lemma Profile_prof_of_le {ℓ L y : ℝ} (hℓ : 0 < ℓ) (h : y ≤ L - ℓ / 2) :
    prof ℓ L y = Real.cos (phase ℓ y) := by
  unfold prof
  rw [Profile_phase_of_le hℓ (by linarith : y - L ≤ -(ℓ / 2)), Real.sin_pi_div_two, mul_one]

private lemma Profile_prof_of_ge {ℓ L y : ℝ} (hℓ : 0 < ℓ) (h : ℓ / 2 ≤ y) :
    prof ℓ L y = Real.sin (phase ℓ (y - L)) := by
  unfold prof
  rw [Profile_phase_of_ge hℓ h, Real.cos_zero, one_mul]

private lemma Profile_prof_of_le_neg {ℓ L y : ℝ} (hℓ : 0 < ℓ) (h : y ≤ -(ℓ / 2)) :
    prof ℓ L y = 0 := by
  unfold prof
  rw [Profile_phase_of_le hℓ h, Real.cos_pi_div_two, zero_mul]

private lemma Profile_prof_of_ge_add {ℓ L y : ℝ} (hℓ : 0 < ℓ) (h : L + ℓ / 2 ≤ y) :
    prof ℓ L y = 0 := by
  unfold prof
  rw [Profile_phase_of_ge hℓ (by linarith : ℓ / 2 ≤ y - L), Real.sin_zero, mul_zero]

/-- The profile is smooth. -/
theorem prof_contDiff (ℓ L : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (prof ℓ L) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => Real.cos (phase ℓ x) * Real.sin (phase ℓ (x - L)))
  exact (Real.contDiff_cos.comp (Profile_phase_contDiff ℓ)).mul
    (Real.contDiff_sin.comp ((Profile_phase_contDiff ℓ).comp (contDiff_id.sub contDiff_const)))

/-- The profile vanishes outside `[-ℓ/2, L + ℓ/2]`. -/
theorem tsupport_prof {ℓ : ℝ} (hℓ : 0 < ℓ) (L : ℝ) :
    tsupport (prof ℓ L) ⊆ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) := by
  refine closure_minimal ?_ isClosed_Icc
  intro y hy
  rw [Function.mem_support] at hy
  constructor
  · by_contra h
    exact hy (Profile_prof_of_le_neg hℓ (by linarith [not_le.mp h]))
  · by_contra h
    exact hy (Profile_prof_of_ge_add hℓ (by linarith [not_le.mp h]))

/-! ### Periodic sums -/

/-- A family `m ↦ g (x + m L)` with the same sum for all `x ∈ [0, L)` has it for all `x`. -/
private lemma Profile_hasSum_reduce {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} {a : ℝ}
    (H : ∀ x, 0 ≤ x → x < L → HasSum (fun m : ℤ => g (x + m * L)) a) (x : ℝ) :
    HasSum (fun m : ℤ => g (x + m * L)) a := by
  set k : ℤ := ⌊x / L⌋ with hk
  have h1 : (k : ℝ) ≤ x / L := Int.floor_le _
  have h2 : x / L < k + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hL] at h1
  rw [div_lt_iff₀ hL] at h2
  have h := H (x - k * L) (by linarith) (by linarith)
  have e : (fun m : ℤ => g (x + m * L)) =
      (fun m : ℤ => g (x - k * L + m * L)) ∘ (Equiv.addRight k) := by
    funext m
    simp only [Function.comp, Equiv.coe_addRight]
    congr 1
    push_cast
    ring
  rw [e]
  exact (Equiv.hasSum_iff _).mpr h

/-- Outside the three translates `m ∈ {-1, 0, 1}`, `x + m L` is outside the support. -/
private lemma Profile_far {ℓ L x : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ < L) (hx0 : 0 ≤ x) (hxL : x ≤ L)
    {m : ℤ} (hm : m ∉ ({-1, 0, 1} : Finset ℤ)) :
    x + m * L < -(ℓ / 2) ∨ L + ℓ / 2 < x + m * L := by
  have hL : 0 < L := by linarith
  have : m ≤ -2 ∨ 2 ≤ m := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    omega
  rcases this with h | h
  · left
    have : (m : ℝ) ≤ -2 := by exact_mod_cast h
    nlinarith
  · right
    have : (2 : ℝ) ≤ m := by exact_mod_cast h
    nlinarith

/-- On `(-ℓ/2, L + ℓ/2)` the three translates of `q²` by `-L, 0, L` sum to `1`. -/
private lemma Profile_three {ℓ L y : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ < L) (hy1 : -(ℓ / 2) < y)
    (hy2 : y < L + ℓ / 2) :
    prof ℓ L (y - L) ^ 2 + prof ℓ L y ^ 2 + prof ℓ L (y + L) ^ 2 = 1 := by
  rcases lt_or_ge y (ℓ / 2) with h | h
  · rw [Profile_prof_of_le_neg hℓ (by linarith : y - L ≤ -(ℓ / 2)),
      Profile_prof_of_le hℓ (by linarith : y ≤ L - ℓ / 2),
      Profile_prof_of_ge hℓ (by linarith : ℓ / 2 ≤ y + L), add_sub_cancel_right]
    nlinarith [Real.cos_sq_add_sin_sq (phase ℓ y)]
  · rcases le_or_gt y (L - ℓ / 2) with h' | h'
    · rw [Profile_prof_of_le_neg hℓ (by linarith : y - L ≤ -(ℓ / 2)),
        Profile_prof_of_le hℓ h', Profile_phase_of_ge hℓ h,
        Profile_prof_of_ge_add hℓ (by linarith : L + ℓ / 2 ≤ y + L), Real.cos_zero]
      norm_num
    · rw [Profile_prof_of_ge_add hℓ (by linarith : L + ℓ / 2 ≤ y + L),
        Profile_prof_of_ge hℓ h,
        Profile_prof_of_le hℓ (by linarith : y - L ≤ L - ℓ / 2)]
      nlinarith [Real.cos_sq_add_sin_sq (phase ℓ (y - L))]

/-- `Σ_m q(x + mL)² = 1`, the identity behind (12.2) [proh1]. -/
theorem prof_sq_hasSum {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (x : ℝ) :
    HasSum (fun m : ℤ => prof ℓ L (x + m * L) ^ 2) 1 := by
  have hL : 0 < L := by linarith
  refine Profile_hasSum_reduce hL (g := fun y => prof ℓ L y ^ 2) ?_ x
  intro x hx0 hxL
  have hfin : HasSum (fun m : ℤ => prof ℓ L (x + m * L) ^ 2)
      (∑ m ∈ ({-1, 0, 1} : Finset ℤ), prof ℓ L (x + m * L) ^ 2) :=
    hasSum_sum_of_ne_finset_zero (by
      intro m hm
      rcases Profile_far hℓ (by linarith) hx0 hxL.le hm with h | h
      · rw [Profile_prof_of_le_neg hℓ h.le]
        norm_num
      · rw [Profile_prof_of_ge_add hℓ h.le]
        norm_num)
  convert hfin using 1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have h3 := Profile_three (L := L) hℓ (by linarith) (y := x) (by linarith) (by linarith)
  simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, neg_mul, one_mul, zero_mul, add_zero]
  rw [← sub_eq_add_neg]
  linarith

/-! ### The derivative of the profile -/

private lemma Profile_deriv_prof_zero {ℓ L y : ℝ} (hℓ : 0 < ℓ)
    (h : y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2)) : deriv (prof ℓ L) y = 0 := by
  by_contra h0
  exact h (tsupport_prof hℓ L (support_deriv_subset (f := prof ℓ L) h0))

private lemma Profile_hasDerivAt_sq (ℓ L y : ℝ) :
    HasDerivAt (fun z => prof ℓ L z ^ 2) (2 * prof ℓ L y * deriv (prof ℓ L) y) y := by
  have hd := (((prof_contDiff ℓ L).differentiable (by simp)) y).hasDerivAt
  convert hd.pow 2 using 1
  simp

private lemma Profile_deriv_sq_sum {ℓ L x : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ < L)
    (hx1 : -(ℓ / 2) < x) (hx2 : x < L + ℓ / 2) :
    deriv (fun y => prof ℓ L y ^ 2) (x - L) + deriv (fun y => prof ℓ L y ^ 2) x +
      deriv (fun y => prof ℓ L y ^ 2) (x + L) = 0 := by
  set f : ℝ → ℝ := fun y => prof ℓ L y ^ 2 with hf
  have hd : ∀ y, HasDerivAt f (deriv f y) y := fun y =>
    (Profile_hasDerivAt_sq ℓ L y).differentiableAt.hasDerivAt
  have h1 : HasDerivAt (fun y => f (y - L)) (deriv f (x - L)) x := (hd (x - L)).comp_sub_const x L
  have h3 : HasDerivAt (fun y => f (y + L)) (deriv f (x + L)) x := (hd (x + L)).comp_add_const x L
  have hS := (h1.add (hd x)).add h3
  have hev : (fun y => f (y - L) + f y + f (y + L)) =ᶠ[𝓝 x] fun _ => (1 : ℝ) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds hx1 hx2)
      (fun y hy => Profile_three hℓ hℓL hy.1 hy.2)
  have hc := (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq hev
  exact hS.unique hc

/-- `Σ_m (q²)'(x + mL) = 0`: the cross term of (12.3) [3.51] vanishes. -/
theorem deriv_prof_sq_hasSum {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (x : ℝ) :
    HasSum (fun m : ℤ => deriv (fun y => prof ℓ L y ^ 2) (x + m * L)) 0 := by
  have hL : 0 < L := by linarith
  refine Profile_hasSum_reduce hL (g := fun y => deriv (fun z => prof ℓ L z ^ 2) y) ?_ x
  intro x hx0 hxL
  have hfin : HasSum (fun m : ℤ => deriv (fun z => prof ℓ L z ^ 2) (x + m * L))
      (∑ m ∈ ({-1, 0, 1} : Finset ℤ), deriv (fun z => prof ℓ L z ^ 2) (x + m * L)) :=
    hasSum_sum_of_ne_finset_zero (by
      intro m hm
      have hout : x + m * L ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) := by
        rcases Profile_far hℓ (by linarith) hx0 hxL.le hm with h | h
        · intro hh
          linarith [hh.1]
        · intro hh
          linarith [hh.2]
      rw [(Profile_hasDerivAt_sq ℓ L (x + m * L)).deriv, Profile_deriv_prof_zero hℓ hout]
      ring)
  convert hfin using 1
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have h := Profile_deriv_sq_sum hℓ (by linarith : ℓ < L) (x := x) (by linarith) (by linarith)
  simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, neg_mul, one_mul, zero_mul, add_zero]
  rw [← sub_eq_add_neg]
  linarith

/-! ### The weight `w` -/

private lemma Profile_hasDerivAt_phase {ℓ : ℝ} (x : ℝ) :
    HasDerivAt (phase ℓ) (π / 2 * (deriv ramp ((ℓ - x) / (2 * ℓ)) * (-1 / (2 * ℓ)))) x := by
  have hτ : HasDerivAt (fun x : ℝ => (ℓ - x) / (2 * ℓ)) (-1 / (2 * ℓ)) x :=
    ((hasDerivAt_id x).const_sub ℓ).div_const (2 * ℓ)
  have hr : HasDerivAt ramp (deriv ramp ((ℓ - x) / (2 * ℓ))) ((ℓ - x) / (2 * ℓ)) :=
    ((Profile_ramp_contDiff.differentiable (by simp)) _).hasDerivAt
  exact (hr.comp x hτ).const_mul (π / 2)

private lemma Profile_deriv_prof (ℓ L y : ℝ) :
    deriv (prof ℓ L) y =
      -Real.sin (phase ℓ y) * deriv (phase ℓ) y * Real.sin (phase ℓ (y - L)) +
        Real.cos (phase ℓ y) * (Real.cos (phase ℓ (y - L)) * deriv (phase ℓ) (y - L)) := by
  have hφ : ∀ z, HasDerivAt (phase ℓ) (deriv (phase ℓ) z) z := fun z =>
    ((Profile_phase_contDiff ℓ).differentiable (by simp) z).hasDerivAt
  have h1 := (hφ y).cos
  have h2 := ((hφ (y - L)).comp_sub_const y L).sin
  exact (h1.mul h2).deriv

private lemma Profile_dphase_ne {ℓ z : ℝ} (hℓ : 0 < ℓ) (h : deriv (phase ℓ) z ≠ 0) :
    -(ℓ / 2) < z ∧ z < ℓ / 2 := by
  by_contra hc
  apply h
  apply Profile_deriv_phase_zero hℓ
  rw [not_and_or, not_lt, not_lt] at hc
  exact hc

/-- `q'² = sin²φ · φ'² + cos²φ(· - L) · φ'(· - L)²`: the two ramps do not overlap. -/
private lemma Profile_deriv_prof_sq {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ < L) (y : ℝ) :
    deriv (prof ℓ L) y ^ 2 =
      Real.sin (phase ℓ y) ^ 2 * deriv (phase ℓ) y ^ 2 +
        Real.cos (phase ℓ (y - L)) ^ 2 * deriv (phase ℓ) (y - L) ^ 2 := by
  rw [Profile_deriv_prof]
  by_cases h1 : deriv (phase ℓ) y = 0
  · by_cases h2 : deriv (phase ℓ) (y - L) = 0
    · rw [h1, h2]
      ring
    · have h := Profile_dphase_ne hℓ h2
      have hc : Real.cos (phase ℓ y) = 1 := by
        rw [Profile_phase_of_ge hℓ (by linarith)]
        exact Real.cos_zero
      rw [h1, hc]
      ring
  · have h := Profile_dphase_ne hℓ h1
    have h2 : deriv (phase ℓ) (y - L) = 0 :=
      Profile_deriv_phase_zero hℓ (Or.inl (by linarith))
    have hs : Real.sin (phase ℓ (y - L)) = 1 := by
      rw [Profile_phase_of_le hℓ (by linarith)]
      exact Real.sin_pi_div_two
    rw [h2, hs]
    ring

private lemma Profile_profW_eq {ℓ L x : ℝ} (hℓ : 0 < ℓ) (hℓL : ℓ < L) (hx0 : 0 ≤ x)
    (hxL : x ≤ L) :
    profW ℓ L x = deriv (prof ℓ L) (x - L) ^ 2 + deriv (prof ℓ L) x ^ 2 +
      deriv (prof ℓ L) (x + L) ^ 2 := by
  unfold profW
  have hsum : ∑' m : ℤ, deriv (prof ℓ L) (x + m * L) ^ 2 =
      ∑ m ∈ ({-1, 0, 1} : Finset ℤ), deriv (prof ℓ L) (x + m * L) ^ 2 :=
    tsum_eq_sum (by
      intro m hm
      have hout : x + m * L ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) := by
        rcases Profile_far hℓ hℓL hx0 hxL hm with h | h
        · intro hh
          linarith [hh.1]
        · intro hh
          linarith [hh.2]
      rw [Profile_deriv_prof_zero hℓ hout]
      norm_num)
  rw [hsum, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [Int.cast_neg, Int.cast_one, Int.cast_zero, neg_mul, one_mul, zero_mul, add_zero]
  rw [← sub_eq_add_neg]
  ring

private lemma Profile_integral_support {f : ℝ → ℝ} {a b c d : ℝ}
    (hf : ∀ y, y ∉ Set.Ioo a b → f y = 0) (hca : c ≤ a) (hbd : b ≤ d) :
    ∫ x in c..d, f x = ∫ x in a..b, f x := by
  have hs : Function.support f ⊆ Set.Ioo a b := fun y hy => by
    by_contra h
    exact hy (hf y h)
  rw [intervalIntegral.integral_eq_integral_of_support_subset
      (hs.trans (fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩)),
    intervalIntegral.integral_eq_integral_of_support_subset (hs.trans Set.Ioo_subset_Ioc_self)]

/-- `∫_0^L w = C_s π² / (8ℓ)`, the size of the error in (12.3) [3.51]. -/
theorem integral_profW {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) :
    ∫ x in (0 : ℝ)..L, profW ℓ L x = rampConst * π ^ 2 / (8 * ℓ) := by
  have hℓL' : ℓ < L := by linarith
  have hL : 0 < L := by linarith
  have hφc : Continuous (phase ℓ) := (Profile_phase_contDiff ℓ).continuous
  have hφ'c : Continuous (deriv (phase ℓ)) := Profile_continuous_deriv_phase ℓ
  set g : ℝ → ℝ := fun y => deriv (prof ℓ L) y ^ 2 with hg
  have hgc : Continuous g := ((prof_contDiff ℓ L).continuous_deriv (by simp)).pow 2
  have hint : ∀ a b, IntervalIntegrable g volume a b := fun a b => hgc.intervalIntegrable a b
  -- the weight is a three-term sum on `[0, L]`
  have h1 : ∫ x in (0 : ℝ)..L, profW ℓ L x = ∫ x in (0 : ℝ)..L, (g (x - L) + g x + g (x + L)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hL.le] at hx
    exact Profile_profW_eq hℓ hℓL' hx.1 hx.2
  have i1 : IntervalIntegrable (fun x => g (x - L)) volume 0 L :=
    (hgc.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun x => g (x + L)) volume 0 L :=
    (hgc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
  have h2 : ∫ x in (0 : ℝ)..L, (g (x - L) + g x + g (x + L)) = ∫ x in (0 - L)..(L + L), g x := by
    rw [intervalIntegral.integral_add (i1.add (hint _ _)) i3,
      intervalIntegral.integral_add i1 (hint _ _),
      intervalIntegral.integral_comp_sub_right g L, intervalIntegral.integral_comp_add_right g L,
      sub_self, zero_add,
      intervalIntegral.integral_add_adjacent_intervals (hint (0 - L) 0) (hint 0 L),
      intervalIntegral.integral_add_adjacent_intervals (hint (0 - L) L) (hint L (L + L))]
  -- splitting `q'²` into the two ramps
  set h₁ : ℝ → ℝ := fun y => Real.sin (phase ℓ y) ^ 2 * deriv (phase ℓ) y ^ 2 with hh₁
  set h₃ : ℝ → ℝ := fun y => Real.cos (phase ℓ y) ^ 2 * deriv (phase ℓ) y ^ 2 with hh₃
  have hc₁ : Continuous h₁ := ((Real.continuous_sin.comp hφc).pow 2).mul (hφ'c.pow 2)
  have hc₃ : Continuous h₃ := ((Real.continuous_cos.comp hφc).pow 2).mul (hφ'c.pow 2)
  have hgeq : ∀ y, g y = h₁ y + h₃ (y - L) := fun y => Profile_deriv_prof_sq hℓ hℓL' y
  have hz₁ : ∀ y, y ∉ Set.Ioo (-(ℓ / 2)) (ℓ / 2) → h₁ y = 0 := by
    intro y hy
    have : deriv (phase ℓ) y = 0 := by
      apply Profile_deriv_phase_zero hℓ
      by_contra hc
      rw [not_or, not_le, not_le] at hc
      exact hy hc
    simp [hh₁, this]
  have hz₃ : ∀ y, y ∉ Set.Ioo (-(ℓ / 2)) (ℓ / 2) → h₃ y = 0 := by
    intro y hy
    have : deriv (phase ℓ) y = 0 := by
      apply Profile_deriv_phase_zero hℓ
      by_contra hc
      rw [not_or, not_le, not_le] at hc
      exact hy hc
    simp [hh₃, this]
  have h3 : ∫ x in (0 - L)..(L + L), g x =
      ∫ x in (-(ℓ / 2))..(ℓ / 2), deriv (phase ℓ) x ^ 2 := by
    have e1 : ∫ x in (0 - L)..(L + L), g x =
        (∫ x in (0 - L)..(L + L), h₁ x) + ∫ x in (0 - L)..(L + L), h₃ (x - L) := by
      have j3 : IntervalIntegrable (fun x => h₃ (x - L)) volume (0 - L) (L + L) :=
        (hc₃.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
      rw [← intervalIntegral.integral_add (hc₁.intervalIntegrable _ _) j3]
      exact intervalIntegral.integral_congr (fun y _ => hgeq y)
    rw [e1, intervalIntegral.integral_comp_sub_right h₃ L,
      Profile_integral_support (a := -(ℓ / 2)) (b := ℓ / 2) (c := 0 - L) (d := L + L) hz₁
        (by linarith) (by linarith),
      Profile_integral_support (a := -(ℓ / 2)) (b := ℓ / 2) (c := 0 - L - L) (d := L + L - L) hz₃
        (by linarith) (by linarith),
      ← intervalIntegral.integral_add (hc₁.intervalIntegrable _ _) (hc₃.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun y _ => ?_)
    simp only [hh₁, hh₃]
    rw [← add_mul, Real.sin_sq_add_cos_sq, one_mul]
  -- the substitution `τ = (ℓ - x)/(2ℓ)`
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  have hφ2 : ∀ y, deriv (phase ℓ) y ^ 2 =
      π ^ 2 / (16 * ℓ ^ 2) * (deriv ramp (1 / 2 - y / (2 * ℓ)) ^ 2) := by
    intro y
    rw [(Profile_hasDerivAt_phase y).deriv]
    have : (ℓ - y) / (2 * ℓ) = 1 / 2 - y / (2 * ℓ) := by
      field_simp
    rw [this]
    field_simp
    ring
  have hk : ∀ τ, τ ∉ Set.Ioo (1 / 4 : ℝ) (3 / 4) → deriv ramp τ ^ 2 = 0 := by
    intro τ hτ
    have : deriv ramp τ = 0 := by
      apply Profile_deriv_ramp_zero
      by_contra hc
      rw [not_or, not_le, not_le] at hc
      exact hτ hc
    rw [this]
    norm_num
  have h4 : ∫ x in (-(ℓ / 2))..(ℓ / 2), deriv (phase ℓ) x ^ 2 =
      π ^ 2 / (16 * ℓ ^ 2) * (2 * ℓ * rampConst) := by
    have e2 : ∫ x in (-(ℓ / 2))..(ℓ / 2), deriv (phase ℓ) x ^ 2 =
        ∫ x in (-(ℓ / 2))..(ℓ / 2),
          π ^ 2 / (16 * ℓ ^ 2) * (deriv ramp (1 / 2 - x / (2 * ℓ)) ^ 2) :=
      intervalIntegral.integral_congr (fun y _ => hφ2 y)
    rw [e2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_div (fun τ => deriv ramp τ ^ 2) (by positivity) (1 / 2)]
    have e3 : (1 : ℝ) / 2 - ℓ / 2 / (2 * ℓ) = 1 / 4 := by
      field_simp
      norm_num
    have e4 : (1 : ℝ) / 2 - -(ℓ / 2) / (2 * ℓ) = 3 / 4 := by
      field_simp
      norm_num
    rw [e3, e4, ← Profile_integral_support (f := fun τ => deriv ramp τ ^ 2) (a := 1 / 4)
      (b := 3 / 4) (c := 0) (d := 1) hk (by norm_num) (by norm_num), smul_eq_mul]
    rfl
  rw [h1, h2, h3, h4]
  field_simp
  ring

end LHYUpper
