module

public import LHYUpper.Riemann.Cells

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! Riemann sums on shells: the lattice sum `|Λ|⁻¹ Σ_{p ∈ Λ* ∩ A, p ≠ 0} F(p)` differs from
`(2π)⁻³ ∫_A F` by `K C E_a(2π/L)` for `F` in the class (H1)–(H2) of `SingDecay`. This is the
quantitative form of the limit `L^{-3} Σ_{p ∈ Λ*} F(p) → (2π)^{-3} ∫ F` recalled before
(5.35) [3.1].

The proof compares, on each cell `Q_n` of side `δ = 2π/L`, the term `δ³ [p_n ∈ A] F(p_n)` with
`∫_{Q_n ∩ A} F`. With `s = |q|`, the difference density is bounded pointwise by
`C s⁻² χ(s)`, where `χ` collects three contributions: cells near the origin (`|p_n| < 4δ`),
cells inside the open shell (the local Lipschitz bound (H2)), and cells meeting a boundary
sphere (which lie in the `2δ`-neighbourhood of that sphere). -/

/-! ### Elementary bounds -/

private lemma Shell_sq_mul_rpow {u : ℝ} (hu : 0 < u) (c : ℝ) : u ^ 2 * u ^ (-c) = u ^ (2 - c) := by
  rw [sub_eq_add_neg, Real.rpow_add hu, Real.rpow_two]

private lemma Shell_div_two_rpow {s : ℝ} (hs : 0 < s) (c : ℝ) :
    (s / 2) ^ (-c) = 2 ^ c * s ^ (-c) := by
  rw [Real.div_rpow hs.le zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul, mul_comm]

private lemma Shell_sqrt3_half_le_one : √3 / 2 ≤ 1 := by
  have : √3 ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  linarith

/-- For `0 < δ ≤ 1`: `δ`, `δ^{3-a}` and `δ max(1, δ^{2-a})` are at most `E_a(δ)`. -/
private lemma Shell_rate_facts {a δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ ≤ riemannRate a δ ∧ δ ^ (3 - a) ≤ riemannRate a δ ∧
      δ * max 1 (δ ^ (2 - a)) ≤ riemannRate a δ := by
  have e : δ ^ (3 - a) = δ * δ ^ (2 - a) := by
    rw [show 3 - a = 1 + (2 - a) by ring, Real.rpow_add hδ, Real.rpow_one]
  have hlog : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hδ, hδ1⟩)
  have h1 : δ ≤ riemannRate a δ ∧ δ ^ (3 - a) ≤ riemannRate a δ := by
    rcases lt_trichotomy a 2 with h | h | h
    · have hr : riemannRate a δ = δ := by simp [riemannRate, h]
      rw [hr]
      refine ⟨le_rfl, ?_⟩
      have := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show (1 : ℝ) ≤ 3 - a by linarith)
      rwa [Real.rpow_one] at this
    · subst h
      have hr : riemannRate 2 δ = δ * (1 + Real.log δ⁻¹) := by simp [riemannRate]
      rw [hr, show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one]
      constructor <;> nlinarith
    · have hr : riemannRate a δ = δ ^ (3 - a) := by
        simp [riemannRate, not_lt.2 h.le, h.ne']
      rw [hr]
      refine ⟨?_, le_rfl⟩
      have := Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show 3 - a ≤ (1 : ℝ) by linarith)
      rwa [Real.rpow_one] at this
  refine ⟨h1.1, h1.2, ?_⟩
  rw [mul_max_of_nonneg _ _ hδ.le, mul_one, ← e]
  exact max_le h1.1 h1.2

/-- `δ ∫_δ^1 s^{1-a} ds ≤ (|2-a|⁻¹ + 1) E_a(δ)`. -/
private lemma Shell_J_le {a δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    δ * ∫ s in Set.Ioc δ 1, s ^ (1 - a) ≤ (|2 - a|⁻¹ + 1) * riemannRate a δ := by
  have h0 : (0 : ℝ) ∉ Set.uIcc δ 1 := by
    rw [Set.uIcc_of_le hδ1]; exact fun h => by linarith [h.1]
  rw [← intervalIntegral.integral_of_le hδ1]
  have hX : 0 ≤ δ ^ (2 - a) := Real.rpow_nonneg hδ.le _
  rcases lt_trichotomy a 2 with h | h | h
  · rw [integral_rpow (Or.inr ⟨by intro h'; linarith, h0⟩), show 1 - a + 1 = 2 - a by ring,
      Real.one_rpow, abs_of_pos (by linarith : (0 : ℝ) < 2 - a)]
    have hr : riemannRate a δ = δ := by simp [riemannRate, h]
    rw [hr]
    have h2a : 0 < 2 - a := by linarith
    have : (1 - δ ^ (2 - a)) / (2 - a) ≤ (2 - a)⁻¹ := by
      rw [div_le_iff₀ h2a, inv_mul_cancel₀ h2a.ne']; linarith
    nlinarith
  · subst h
    have hr : riemannRate 2 δ = δ * (1 + Real.log δ⁻¹) := by simp [riemannRate]
    rw [hr, show (1 : ℝ) - 2 = -1 by norm_num]
    simp only [Real.rpow_neg_one]
    rw [integral_inv_of_pos hδ one_pos, one_div, sub_self, abs_zero, inv_zero, zero_add, one_mul]
    nlinarith
  · rw [integral_rpow (Or.inr ⟨by intro h'; linarith, h0⟩), show 1 - a + 1 = 2 - a by ring,
      Real.one_rpow, abs_of_neg (by linarith : 2 - a < 0)]
    have hr : riemannRate a δ = δ ^ (3 - a) := by
      simp [riemannRate, not_lt.2 h.le, h.ne']
    have e : δ ^ (3 - a) = δ * δ ^ (2 - a) := by
      rw [show 3 - a = 1 + (2 - a) by ring, Real.rpow_add hδ, Real.rpow_one]
    rw [hr, e]
    have ha2 : 0 < a - 2 := by linarith
    have : (1 - δ ^ (2 - a)) / (2 - a) ≤ (-(2 - a))⁻¹ * δ ^ (2 - a) + δ ^ (2 - a) := by
      rw [neg_sub, div_le_iff_of_neg (by linarith : 2 - a < 0)]
      have : (a - 2)⁻¹ * δ ^ (2 - a) * (2 - a) = -δ ^ (2 - a) := by
        field_simp; ring
      nlinarith
    calc δ * ((1 - δ ^ (2 - a)) / (2 - a))
        ≤ δ * ((-(2 - a))⁻¹ * δ ^ (2 - a) + δ ^ (2 - a)) := mul_le_mul_of_nonneg_left this hδ.le
      _ = ((-(2 - a))⁻¹ + 1) * (δ * δ ^ (2 - a)) := by ring

/-- Interior majorant: for `δ < s ≤ 2r`,
`s² min(r^{-a-1}, r^{-b}) ≤ (2^{a+1} + 2^b) (1_{(δ,1]}(s) s^{1-a} + 1_{(1,∞)}(s) s^{2-b})`. -/
private lemma Shell_interior_le {a b δ s r : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ)
    (hs : δ < s) (hr : s / 2 ≤ r) :
    s ^ 2 * min (r ^ (-a - 1)) (r ^ (-b)) ≤ (2 ^ (a + 1) + 2 ^ b) *
      ((Set.Ioc δ 1).indicator (fun s => s ^ (1 - a)) s +
        (Set.Ioi 1).indicator (fun s => s ^ (2 - b)) s) := by
  have hs0 : 0 < s := hδ.trans hs
  have hs2 : 0 < s / 2 := by positivity
  have h2a : (0 : ℝ) ≤ 2 ^ (a + 1) := Real.rpow_nonneg zero_le_two _
  have h2b : (0 : ℝ) ≤ 2 ^ b := Real.rpow_nonneg zero_le_two _
  have hmin : min (r ^ (-a - 1)) (r ^ (-b)) ≤ min ((s / 2) ^ (-a - 1)) ((s / 2) ^ (-b)) :=
    min_le_min (Real.rpow_le_rpow_of_nonpos hs2 hr (by linarith))
      (Real.rpow_le_rpow_of_nonpos hs2 hr (by linarith))
  have hsq : 0 ≤ s ^ 2 := sq_nonneg s
  rw [show -a - 1 = -(a + 1) by ring] at hmin ⊢
  rcases le_or_gt s 1 with h1 | h1
  · rw [Set.indicator_of_mem (show s ∈ Set.Ioc δ 1 from ⟨hs, h1⟩),
      Set.indicator_of_notMem (show s ∉ Set.Ioi 1 from fun h => by simp at h; linarith), add_zero]
    have hp : 0 ≤ s ^ (1 - a) := Real.rpow_nonneg hs0.le _
    calc s ^ 2 * min (r ^ (-(a + 1))) (r ^ (-b))
        ≤ s ^ 2 * (s / 2) ^ (-(a + 1)) :=
          mul_le_mul_of_nonneg_left (hmin.trans (min_le_left _ _)) hsq
      _ = 2 ^ (a + 1) * s ^ (1 - a) := by
          rw [Shell_div_two_rpow hs0, mul_left_comm, Shell_sq_mul_rpow hs0,
            show 2 - (a + 1) = 1 - a by ring]
      _ ≤ (2 ^ (a + 1) + 2 ^ b) * s ^ (1 - a) := by nlinarith
  · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc δ 1 from fun h => by linarith [h.2]),
      Set.indicator_of_mem (show s ∈ Set.Ioi 1 from h1), zero_add]
    have hp : 0 ≤ s ^ (2 - b) := Real.rpow_nonneg hs0.le _
    calc s ^ 2 * min (r ^ (-(a + 1))) (r ^ (-b))
        ≤ s ^ 2 * (s / 2) ^ (-b) :=
          mul_le_mul_of_nonneg_left (hmin.trans (min_le_right _ _)) hsq
      _ = 2 ^ b * s ^ (2 - b) := by
          rw [Shell_div_two_rpow hs0, mul_left_comm, Shell_sq_mul_rpow hs0]
      _ ≤ (2 ^ (a + 1) + 2 ^ b) * s ^ (2 - b) := by nlinarith

/-- Boundary majorant: for `2δ ≤ s ≤ 2r`, `0 < δ ≤ 1`,
`s² min(r^{-a}, r^{-b}) ≤ 4 max(1, δ^{2-a})`. -/
private lemma Shell_boundary_le {a b δ s r : ℝ} (ha : 0 ≤ a) (hb3 : 2 ≤ b)
    (hδ : 0 < δ) (hs : 2 * δ ≤ s) (hr : s / 2 ≤ r) :
    s ^ 2 * min (r ^ (-a)) (r ^ (-b)) ≤ 4 * max 1 (δ ^ (2 - a)) := by
  set u := s / 2 with hu
  have hu0 : 0 < u := by rw [hu]; linarith
  have hδu : δ ≤ u := by rw [hu]; linarith
  have hmin : min (r ^ (-a)) (r ^ (-b)) ≤ min (u ^ (-a)) (u ^ (-b)) :=
    min_le_min (Real.rpow_le_rpow_of_nonpos hu0 hr (by linarith))
      (Real.rpow_le_rpow_of_nonpos hu0 hr (by linarith))
  have hs2 : s ^ 2 = 4 * u ^ 2 := by rw [hu]; ring
  have hsq : 0 ≤ s ^ 2 := sq_nonneg s
  have key : u ^ 2 * min (u ^ (-a)) (u ^ (-b)) ≤ max 1 (δ ^ (2 - a)) := by
    have hu2 : 0 ≤ u ^ 2 := sq_nonneg u
    rcases le_or_gt u 1 with h1 | h1
    · calc u ^ 2 * min (u ^ (-a)) (u ^ (-b)) ≤ u ^ 2 * u ^ (-a) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hu2
        _ = u ^ (2 - a) := Shell_sq_mul_rpow hu0 a
        _ ≤ max 1 (δ ^ (2 - a)) := by
            rcases le_or_gt a 2 with h2 | h2
            · exact (Real.rpow_le_one hu0.le h1 (by linarith)).trans (le_max_left _ _)
            · exact (Real.rpow_le_rpow_of_nonpos hδ hδu (by linarith)).trans (le_max_right _ _)
    · calc u ^ 2 * min (u ^ (-a)) (u ^ (-b)) ≤ u ^ 2 * u ^ (-b) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) hu2
        _ = u ^ (2 - b) := Shell_sq_mul_rpow hu0 b
        _ ≤ max 1 (δ ^ (2 - a)) :=
            (Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith)).trans (le_max_left _ _)
  calc s ^ 2 * min (r ^ (-a)) (r ^ (-b)) ≤ s ^ 2 * min (u ^ (-a)) (u ^ (-b)) :=
        mul_le_mul_of_nonneg_left hmin hsq
    _ = 4 * (u ^ 2 * min (u ^ (-a)) (u ^ (-b))) := by rw [hs2]; ring
    _ ≤ 4 * max 1 (δ ^ (2 - a)) := by linarith

/-! ### The radial profile `χ` -/

/-- The radial profile `χ(s)`, with `r₂` real (the outer radius, or `0` if there is none):
`(5^a + 1) 1_{(0,5δ]}(s) s^{2-a}` (cells near the origin),
`(2^{a+1} + 2^b) δ (1_{(δ,1]}(s) s^{1-a} + 1_{(1,∞)}(s) s^{2-b})` (interior cells) and
`8 max(1, δ^{2-a}) (1_{|s-r₁| ≤ 2δ} + 1_{|s-r₂| ≤ 2δ})` (boundary cells). -/
private def Shell_chi (a b δ r₁ r₂ s : ℝ) : ℝ :=
  (5 ^ a + 1) * (Set.Ioc 0 (5 * δ)).indicator (fun s => s ^ (2 - a)) s +
    (2 ^ (a + 1) + 2 ^ b) * δ * ((Set.Ioc δ 1).indicator (fun s => s ^ (1 - a)) s +
      (Set.Ioi 1).indicator (fun s => s ^ (2 - b)) s) +
    8 * max 1 (δ ^ (2 - a)) *
      ((Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s +
        (Set.Icc (r₂ - 2 * δ) (r₂ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s)

private lemma Shell_chi_pieces_nonneg (a b δ r₁ r₂ s : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ (5 ^ a + 1) * (Set.Ioc 0 (5 * δ)).indicator (fun s => s ^ (2 - a)) s ∧
    0 ≤ (2 ^ (a + 1) + 2 ^ b) * δ * ((Set.Ioc δ 1).indicator (fun s => s ^ (1 - a)) s +
      (Set.Ioi 1).indicator (fun s => s ^ (2 - b)) s) ∧
    0 ≤ 8 * max 1 (δ ^ (2 - a)) *
      ((Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s +
        (Set.Icc (r₂ - 2 * δ) (r₂ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s) := by
  have h5 : (0 : ℝ) ≤ 5 ^ a := Real.rpow_nonneg (by norm_num) _
  have h2a : (0 : ℝ) ≤ 2 ^ (a + 1) := Real.rpow_nonneg zero_le_two _
  have h2b : (0 : ℝ) ≤ 2 ^ b := Real.rpow_nonneg zero_le_two _
  have i1 : 0 ≤ (Set.Ioc 0 (5 * δ)).indicator (fun s => s ^ (2 - a)) s :=
    Set.indicator_nonneg (fun x (hx : x ∈ Set.Ioc 0 (5 * δ)) => Real.rpow_nonneg hx.1.le _) _
  have i2 : 0 ≤ (Set.Ioc δ 1).indicator (fun s => s ^ (1 - a)) s :=
    Set.indicator_nonneg (fun x (hx : x ∈ Set.Ioc δ 1) => Real.rpow_nonneg (hδ.trans hx.1.le) _) _
  have i3 : 0 ≤ (Set.Ioi 1).indicator (fun s => s ^ (2 - b)) s :=
    Set.indicator_nonneg
      (fun x (hx : x ∈ Set.Ioi 1) => Real.rpow_nonneg (zero_le_one.trans (le_of_lt hx)) _) _
  have i4 : 0 ≤ (Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have i5 : 0 ≤ (Set.Icc (r₂ - 2 * δ) (r₂ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hm : (0 : ℝ) ≤ max 1 (δ ^ (2 - a)) := zero_le_one.trans (le_max_left _ _)
  refine ⟨by positivity, by positivity, by positivity⟩

private lemma Shell_chi_nonneg (a b δ r₁ r₂ s : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ Shell_chi a b δ r₁ r₂ s := by
  obtain ⟨h1, h2, h3⟩ := Shell_chi_pieces_nonneg a b δ r₁ r₂ s hδ
  unfold Shell_chi
  linarith

/-- The constant `K'(a, b)` with `∫ χ ≤ K'(a, b) E_a(δ)`. -/
private def Shell_K (a b : ℝ) : ℝ :=
  (5 ^ a + 1) * 5 ^ (3 - a) / (3 - a) + (2 ^ (a + 1) + 2 ^ b) * (|2 - a|⁻¹ + 1) +
    (2 ^ (a + 1) + 2 ^ b) / (b - 3) + 64

/-- `χ` is integrable on `ℝ` with `∫ χ ≤ K'(a, b) E_a(δ)`, uniformly in `r₁`, `r₂`. -/
private lemma Shell_chi_integral {a b δ : ℝ} (ha3 : a < 3) (hb : 3 < b) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (r₁ r₂ : ℝ) :
    Integrable (Shell_chi a b δ r₁ r₂) ∧
      ∫ s, Shell_chi a b δ r₁ r₂ s ≤ Shell_K a b * riemannRate a δ := by
  have h3a : 0 < 3 - a := by linarith
  have hb3 : 0 < b - 3 := by linarith
  have h5δ : 0 ≤ 5 * δ := by positivity
  have h0 : (0 : ℝ) ∉ Set.uIcc δ 1 := by
    rw [Set.uIcc_of_le hδ1]; exact fun h => by linarith [h.1]
  -- the five pieces
  have int1 : Integrable ((Set.Ioc 0 (5 * δ)).indicator (fun s : ℝ => s ^ (2 - a))) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le h5δ).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))).integrable_indicator
      measurableSet_Ioc
  have int2 : Integrable ((Set.Ioc δ 1).indicator (fun s : ℝ => s ^ (1 - a))) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ1).1
      (intervalIntegral.intervalIntegrable_rpow (Or.inr h0))).integrable_indicator
      measurableSet_Ioc
  have int3 : Integrable ((Set.Ioi 1).indicator (fun s : ℝ => s ^ (2 - b))) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).integrable_indicator measurableSet_Ioi
  have int4 : ∀ r : ℝ,
      Integrable ((Set.Icc (r - 2 * δ) (r + 2 * δ)).indicator (fun _ : ℝ => (1 : ℝ))) :=
    fun r => (integrableOn_const (by simp)).integrable_indicator measurableSet_Icc
  have val1 : ∫ s, (Set.Ioc 0 (5 * δ)).indicator (fun s : ℝ => s ^ (2 - a)) s =
      (5 * δ) ^ (3 - a) / (3 - a) := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le h5δ,
      integral_rpow (Or.inl (by linarith)), show 2 - a + 1 = 3 - a by ring,
      Real.zero_rpow h3a.ne', sub_zero]
  have val2 : ∫ s, (Set.Ioc δ 1).indicator (fun s : ℝ => s ^ (1 - a)) s =
      ∫ s in Set.Ioc δ 1, s ^ (1 - a) := integral_indicator measurableSet_Ioc
  have val3 : ∫ s, (Set.Ioi 1).indicator (fun s : ℝ => s ^ (2 - b)) s = 1 / (b - 3) := by
    rw [integral_indicator measurableSet_Ioi, integral_Ioi_rpow_of_lt (by linarith) one_pos,
      Real.one_rpow, show 2 - b + 1 = -(b - 3) by ring, div_neg, neg_div, neg_neg]
  have val4 : ∀ r : ℝ,
      ∫ s, (Set.Icc (r - 2 * δ) (r + 2 * δ)).indicator (fun _ : ℝ => (1 : ℝ)) s = 4 * δ := by
    intro r
    rw [integral_indicator_const _ measurableSet_Icc, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
    ring
  set c₁ : ℝ := 5 ^ a + 1
  set c₂ : ℝ := (2 ^ (a + 1) + 2 ^ b) * δ
  set c₃ : ℝ := 8 * max 1 (δ ^ (2 - a))
  have hχ : Shell_chi a b δ r₁ r₂ = fun s =>
      c₁ * (Set.Ioc 0 (5 * δ)).indicator (fun s : ℝ => s ^ (2 - a)) s +
        c₂ * ((Set.Ioc δ 1).indicator (fun s : ℝ => s ^ (1 - a)) s +
          (Set.Ioi 1).indicator (fun s : ℝ => s ^ (2 - b)) s) +
        c₃ * ((Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ)).indicator (fun _ : ℝ => (1 : ℝ)) s +
          (Set.Icc (r₂ - 2 * δ) (r₂ + 2 * δ)).indicator (fun _ : ℝ => (1 : ℝ)) s) := rfl
  have i23 := int2.add int3
  have i45 := (int4 r₁).add (int4 r₂)
  refine ⟨hχ ▸ ((int1.const_mul c₁).add (i23.const_mul c₂)).add (i45.const_mul c₃), ?_⟩
  set X1 := (Set.Ioc 0 (5 * δ)).indicator (fun s : ℝ => s ^ (2 - a))
  set X2 := (Set.Ioc δ 1).indicator (fun s : ℝ => s ^ (1 - a))
  set X3 := (Set.Ioi 1).indicator (fun s : ℝ => s ^ (2 - b))
  set X4 := (Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ)).indicator (fun _ : ℝ => (1 : ℝ))
  set X5 := (Set.Icc (r₂ - 2 * δ) (r₂ + 2 * δ)).indicator (fun _ : ℝ => (1 : ℝ))
  have hI : ∫ s, Shell_chi a b δ r₁ r₂ s =
      c₁ * (∫ s, X1 s) + c₂ * ((∫ s, X2 s) + ∫ s, X3 s) + c₃ * ((∫ s, X4 s) + ∫ s, X5 s) := by
    rw [hχ, integral_add (f := fun s => c₁ * X1 s + c₂ * (X2 s + X3 s))
      (g := fun s => c₃ * (X4 s + X5 s)) ((int1.const_mul c₁).add (i23.const_mul c₂))
      (i45.const_mul c₃),
      integral_add (f := fun s => c₁ * X1 s) (g := fun s => c₂ * (X2 s + X3 s))
        (int1.const_mul c₁) (i23.const_mul c₂),
      integral_const_mul, integral_const_mul, integral_const_mul,
      integral_add int2 int3, integral_add (int4 r₁) (int4 r₂)]
  rw [hI, val1, val2, val3, val4, val4]
  obtain ⟨e1, e2, e3⟩ := Shell_rate_facts (a := a) hδ hδ1
  have hJ := Shell_J_le (a := a) hδ hδ1
  have hc₁ : 0 ≤ c₁ := by positivity
  have hcI : (0 : ℝ) ≤ 2 ^ (a + 1) + 2 ^ b := by positivity
  have t1 : c₁ * ((5 * δ) ^ (3 - a) / (3 - a)) ≤
      (5 ^ a + 1) * 5 ^ (3 - a) / (3 - a) * riemannRate a δ := by
    rw [Real.mul_rpow (by norm_num) hδ.le]
    have h55 : 0 ≤ c₁ * 5 ^ (3 - a) / (3 - a) := by positivity
    calc c₁ * (5 ^ (3 - a) * δ ^ (3 - a) / (3 - a))
        = c₁ * 5 ^ (3 - a) / (3 - a) * δ ^ (3 - a) := by ring
      _ ≤ c₁ * 5 ^ (3 - a) / (3 - a) * riemannRate a δ := mul_le_mul_of_nonneg_left e2 h55
  have t2 : c₂ * ((∫ s in Set.Ioc δ 1, s ^ (1 - a)) + 1 / (b - 3)) ≤
      ((2 ^ (a + 1) + 2 ^ b) * (|2 - a|⁻¹ + 1) + (2 ^ (a + 1) + 2 ^ b) / (b - 3)) *
        riemannRate a δ := by
    have hd : δ * (1 / (b - 3)) ≤ 1 / (b - 3) * riemannRate a δ := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left e1 (by positivity)
    calc c₂ * ((∫ s in Set.Ioc δ 1, s ^ (1 - a)) + 1 / (b - 3))
        = (2 ^ (a + 1) + 2 ^ b) * (δ * ∫ s in Set.Ioc δ 1, s ^ (1 - a)) +
            (2 ^ (a + 1) + 2 ^ b) * (δ * (1 / (b - 3))) := by ring
      _ ≤ (2 ^ (a + 1) + 2 ^ b) * ((|2 - a|⁻¹ + 1) * riemannRate a δ) +
            (2 ^ (a + 1) + 2 ^ b) * (1 / (b - 3) * riemannRate a δ) := by
          gcongr
      _ = _ := by ring
  have t3 : c₃ * (4 * δ + 4 * δ) ≤ 64 * riemannRate a δ := by
    calc c₃ * (4 * δ + 4 * δ) = 64 * (δ * max 1 (δ ^ (2 - a))) := by ring
      _ ≤ 64 * riemannRate a δ := by linarith
  unfold Shell_K
  nlinarith

/-! ### The pointwise bound on a cell -/

private lemma Shell_mom_zero (L : ℝ) : mom L 0 = 0 := by
  ext i; rw [Cells_mom_apply]; simp

/-- For `q ≠ 0` in the cell `Q_n`: `|q|² |[n ≠ 0, p_n ∈ A] F(p_n) − 1_A(q) F(q)| ≤ C χ(|q|)`,
with `δ = 2π/L` and the outer radius `r₂` read as a real number. -/
private lemma Shell_pointwise {a b C L r₁ : ℝ} {r₂ : ℝ≥0∞} {F : R3 → ℝ} {A : Set R3}
    (ha : 0 ≤ a) (hb : 3 < b) (hC : 0 ≤ C) (hF : SingDecay a b C F)
    (hL : 2 * π ≤ L) (hAs : IsShell r₁ r₂ 0 A) (n : Idx) {q : R3}
    (hq : q ∈ Cells_cell L n) (hq0 : q ≠ 0) :
    ‖q‖ ^ 2 * |(if n ≠ 0 ∧ mom L n ∈ A then F (mom L n) else 0) - A.indicator F q| ≤
      C * Shell_chi a b (2 * π / L) r₁ r₂.toReal ‖q‖ := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  set δ := 2 * π / L with hδdef
  have hδ : 0 < δ := by positivity
  set p := mom L n with hp
  set s := ‖q‖ with hs
  have hs0 : 0 < s := norm_pos_iff.2 hq0
  have hcell : ∀ z ∈ Cells_cell L n, ‖z - p‖ ≤ δ := fun z hz =>
    (Cells_norm_sub_mom_le hL0 hz).trans (by nlinarith [Shell_sqrt3_half_le_one])
  have hpcell : p ∈ Cells_cell L n := Cells_mom_mem hL0 n
  have hdist : ∀ z ∈ Cells_cell L n, |s - ‖z‖| ≤ 2 * δ := fun z hz => by
    calc |s - ‖z‖| ≤ ‖q - z‖ := abs_norm_sub_norm_le q z
      _ ≤ ‖q - p‖ + ‖p - z‖ := norm_sub_le_norm_sub_add_norm_sub q p z
      _ ≤ δ + δ := by rw [norm_sub_rev p z]; exact add_le_add (hcell q hq) (hcell z hz)
      _ = 2 * δ := by ring
  have hqp : |s - ‖p‖| ≤ δ := (abs_norm_sub_norm_le q p).trans (hcell q hq)
  obtain ⟨P1, P2, P3⟩ := Shell_chi_pieces_nonneg a b δ r₁ r₂.toReal s hδ.le
  set T := (if n ≠ 0 ∧ p ∈ A then F p else 0) with hT
  set Gq := A.indicator F q with hGq
  have hmin0 : ∀ x : ℝ, 0 ≤ x → ∀ c d : ℝ, 0 ≤ C * min (x ^ c) (x ^ d) := fun x hx c d =>
    mul_nonneg hC (le_min (Real.rpow_nonneg hx _) (Real.rpow_nonneg hx _))
  have hGq_le : |Gq| ≤ C * min (s ^ (-a)) (s ^ (-b)) := by
    rw [hGq, Set.indicator_apply]
    split_ifs
    · exact hF.bound q hq0
    · rw [abs_zero]; exact hmin0 s hs0.le _ _
  have htri : s ^ 2 * |T - Gq| ≤ s ^ 2 * (|T| + |Gq|) := by
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg s)
    have := abs_add_le T (-Gq)
    rwa [abs_neg, ← sub_eq_add_neg] at this
  have hχ0 : 0 ≤ C * Shell_chi a b δ r₁ r₂.toReal s :=
    mul_nonneg hC (Shell_chi_nonneg a b δ r₁ r₂.toReal s hδ.le)
  by_cases hnear : ‖p‖ < 4 * δ
  · -- cells near the origin
    have hs5 : s ≤ 5 * δ := by have := (abs_le.1 hqp).2; linarith
    have hδs : δ ^ (-a) ≤ 5 ^ a * s ^ (-a) := by
      have h := Real.rpow_le_rpow_of_nonpos hs0 hs5 (show -a ≤ 0 by linarith)
      rw [Real.mul_rpow (by norm_num) hδ.le, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 5)] at h
      have h5 : 0 < (5 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) _
      calc δ ^ (-a) = 5 ^ a * ((5 ^ a)⁻¹ * δ ^ (-a)) := by field_simp
        _ ≤ 5 ^ a * s ^ (-a) := mul_le_mul_of_nonneg_left h h5.le
    have hT_le : |T| ≤ C * (5 ^ a * s ^ (-a)) := by
      rw [hT]
      split_ifs with h
      · have hpδ : δ ≤ ‖p‖ := Cells_le_norm_mom hL0 h.1
        have hp0 : p ≠ 0 := fun h0 => by rw [h0, norm_zero] at hpδ; linarith
        calc |F p| ≤ C * min (‖p‖ ^ (-a)) (‖p‖ ^ (-b)) := hF.bound p hp0
          _ ≤ C * ‖p‖ ^ (-a) := mul_le_mul_of_nonneg_left (min_le_left _ _) hC
          _ ≤ C * δ ^ (-a) :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hδ hpδ (by linarith)) hC
          _ ≤ C * (5 ^ a * s ^ (-a)) := mul_le_mul_of_nonneg_left hδs hC
      · rw [abs_zero]
        exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg hs0.le _))
    have hG' : |Gq| ≤ C * s ^ (-a) := hGq_le.trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hC)
    have hχ1 : (5 ^ a + 1) * s ^ (2 - a) ≤ Shell_chi a b δ r₁ r₂.toReal s := by
      have e : (5 ^ a + 1) * (Set.Ioc 0 (5 * δ)).indicator (fun s => s ^ (2 - a)) s =
          (5 ^ a + 1) * s ^ (2 - a) := by
        rw [Set.indicator_of_mem (show s ∈ Set.Ioc 0 (5 * δ) from ⟨hs0, hs5⟩)]
      unfold Shell_chi
      linarith
    calc s ^ 2 * |T - Gq| ≤ s ^ 2 * (|T| + |Gq|) := htri
      _ ≤ s ^ 2 * (C * (5 ^ a * s ^ (-a)) + C * s ^ (-a)) :=
          mul_le_mul_of_nonneg_left (add_le_add hT_le hG') (sq_nonneg s)
      _ = C * ((5 ^ a + 1) * (s ^ 2 * s ^ (-a))) := by ring
      _ = C * ((5 ^ a + 1) * s ^ (2 - a)) := by rw [Shell_sq_mul_rpow hs0]
      _ ≤ C * Shell_chi a b δ r₁ r₂.toReal s := mul_le_mul_of_nonneg_left hχ1 hC
  push Not at hnear
  have hn : n ≠ 0 := by
    rintro rfl
    rw [hp, Shell_mom_zero, norm_zero] at hnear
    linarith
  have hp0 : p ≠ 0 := fun h0 => by rw [h0, norm_zero] at hnear; linarith
  have hs3 : 3 * δ ≤ s := by have := (abs_le.1 hqp).1; linarith
  have hsp : s / 2 ≤ ‖p‖ := by have := (abs_le.1 hqp).2; linarith
  by_cases hI : ∀ z ∈ Cells_cell L n, r₁ < ‖z‖ ∧ ENNReal.ofReal ‖z‖ < r₂
  · -- cells inside the open shell
    have hA' : ∀ z ∈ Cells_cell L n, z ∈ A := fun z hz =>
      hAs.1 z (by rw [add_zero]; exact (hI z hz).1) (by rw [add_zero]; exact (hI z hz).2)
    have eT : T = F p := by rw [hT]; exact ite_eq_left_iff.2 fun h => absurd ⟨hn, hA' p hpcell⟩ h
    have eG : Gq = F q := by rw [hGq, Set.indicator_of_mem (hA' q hq)]
    rw [eT, eG, abs_sub_comm]
    have hqp' : ‖q - p‖ ≤ ‖p‖ / 2 := by have := hcell q hq; linarith
    have hlip := hF.lip p q hp0 hqp'
    have hint := Shell_interior_le (a := a) (b := b) ha (by linarith) hδ (by linarith) hsp
    have hφ0 : 0 ≤ min (‖p‖ ^ (-a - 1)) (‖p‖ ^ (-b)) :=
      le_min (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
    have hχ2 : (2 ^ (a + 1) + 2 ^ b) * δ * ((Set.Ioc δ 1).indicator (fun s => s ^ (1 - a)) s +
        (Set.Ioi 1).indicator (fun s => s ^ (2 - b)) s) ≤ Shell_chi a b δ r₁ r₂.toReal s := by
      unfold Shell_chi
      linarith
    calc s ^ 2 * |F q - F p|
        ≤ s ^ 2 * (C * ‖q - p‖ * min (‖p‖ ^ (-a - 1)) (‖p‖ ^ (-b))) :=
          mul_le_mul_of_nonneg_left hlip (sq_nonneg s)
      _ ≤ s ^ 2 * (C * δ * min (‖p‖ ^ (-a - 1)) (‖p‖ ^ (-b))) := by
          gcongr
          exact hcell q hq
      _ = C * δ * (s ^ 2 * min (‖p‖ ^ (-a - 1)) (‖p‖ ^ (-b))) := by ring
      _ ≤ C * δ * ((2 ^ (a + 1) + 2 ^ b) * ((Set.Ioc δ 1).indicator (fun s => s ^ (1 - a)) s +
            (Set.Ioi 1).indicator (fun s => s ^ (2 - b)) s)) :=
          mul_le_mul_of_nonneg_left hint (mul_nonneg hC hδ.le)
      _ = C * ((2 ^ (a + 1) + 2 ^ b) * δ * ((Set.Ioc δ 1).indicator (fun s => s ^ (1 - a)) s +
            (Set.Ioi 1).indicator (fun s => s ^ (2 - b)) s)) := by ring
      _ ≤ C * Shell_chi a b δ r₁ r₂.toReal s := mul_le_mul_of_nonneg_left hχ2 hC
  -- cells meeting a boundary sphere
  push Not at hI
  obtain ⟨y, hy, hy'⟩ := hI
  by_cases hx : p ∈ A ∨ q ∈ A
  · obtain ⟨x, hxc, hxA⟩ : ∃ x ∈ Cells_cell L n, x ∈ A := by
      rcases hx with hx | hx
      exacts [⟨p, hpcell, hx⟩, ⟨q, hq, hx⟩]
    obtain ⟨hx1, hx2⟩ := hAs.2 x hxA
    have hdx := abs_le.1 (hdist x hxc)
    have hdy := abs_le.1 (hdist y hy)
    have hin : s ∈ Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ) ∨
        s ∈ Set.Icc (r₂.toReal - 2 * δ) (r₂.toReal + 2 * δ) := by
      by_cases hy1 : r₁ < ‖y‖
      · have hy2 := hy' hy1
        have htop : r₂ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy2
        have h1 : r₂.toReal ≤ ‖y‖ := ENNReal.toReal_le_of_le_ofReal (norm_nonneg _) hy2
        have h2 : ‖x‖ ≤ r₂.toReal := (ENNReal.ofReal_le_iff_le_toReal htop).1 hx2
        exact Or.inr ⟨by linarith, by linarith⟩
      · push Not at hy1
        exact Or.inl ⟨by linarith, by linarith⟩
    have hind : 1 ≤ (Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s +
        (Set.Icc (r₂.toReal - 2 * δ) (r₂.toReal + 2 * δ)).indicator (fun _ => (1 : ℝ)) s := by
      have i4 : 0 ≤ (Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have i5 : 0 ≤ (Set.Icc (r₂.toReal - 2 * δ) (r₂.toReal + 2 * δ)).indicator
          (fun _ => (1 : ℝ)) s := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      rcases hin with h | h
      · rw [Set.indicator_of_mem h]; linarith
      · rw [Set.indicator_of_mem h]; linarith
    have hT_le : |T| ≤ C * min (‖p‖ ^ (-a)) (‖p‖ ^ (-b)) := by
      rw [hT]
      split_ifs
      · exact hF.bound p hp0
      · rw [abs_zero]; exact hmin0 _ (norm_nonneg _) _ _
    have b1 := Shell_boundary_le (a := a) (b := b) ha (by linarith) hδ (by linarith) hsp
    have b2 := Shell_boundary_le (a := a) (b := b) (s := s) (r := s) ha (by linarith) hδ
      (by linarith) (by linarith)
    have hm : (0 : ℝ) ≤ max 1 (δ ^ (2 - a)) := zero_le_one.trans (le_max_left _ _)
    have hχ3 : 8 * max 1 (δ ^ (2 - a)) ≤ Shell_chi a b δ r₁ r₂.toReal s := by
      have : 8 * max 1 (δ ^ (2 - a)) ≤ 8 * max 1 (δ ^ (2 - a)) *
          ((Set.Icc (r₁ - 2 * δ) (r₁ + 2 * δ)).indicator (fun _ => (1 : ℝ)) s +
            (Set.Icc (r₂.toReal - 2 * δ) (r₂.toReal + 2 * δ)).indicator (fun _ => (1 : ℝ)) s) :=
        le_mul_of_one_le_right (by positivity) hind
      unfold Shell_chi
      linarith
    calc s ^ 2 * |T - Gq| ≤ s ^ 2 * (|T| + |Gq|) := htri
      _ ≤ s ^ 2 * (C * min (‖p‖ ^ (-a)) (‖p‖ ^ (-b)) + C * min (s ^ (-a)) (s ^ (-b))) :=
          mul_le_mul_of_nonneg_left (add_le_add hT_le hGq_le) (sq_nonneg s)
      _ = C * (s ^ 2 * min (‖p‖ ^ (-a)) (‖p‖ ^ (-b)) + s ^ 2 * min (s ^ (-a)) (s ^ (-b))) := by
          ring
      _ ≤ C * (4 * max 1 (δ ^ (2 - a)) + 4 * max 1 (δ ^ (2 - a))) :=
          mul_le_mul_of_nonneg_left (add_le_add b1 b2) hC
      _ = C * (8 * max 1 (δ ^ (2 - a))) := by ring
      _ ≤ C * Shell_chi a b δ r₁ r₂.toReal s := mul_le_mul_of_nonneg_left hχ3 hC
  · push Not at hx
    have eT : T = 0 := by rw [hT]; exact ite_eq_right_iff.2 fun h => absurd h.2 hx.1
    have eG : Gq = 0 := by rw [hGq, Set.indicator_of_notMem hx.2]
    rw [eT, eG, sub_zero, abs_zero, mul_zero]
    exact hχ0

/-! ### The Riemann-sum lemma -/

/-- Riemann-sum lemma on `Λ* = (2π/L)ℤ³`: for `F` in the class (H1)–(H2) and a shell `A`,
`| |Λ|⁻¹ Σ_{p ∈ Λ* ∩ A, p ≠ 0} F(p) − (2π)⁻³ ∫_A F | ≤ K C E_a(2π/L)`, with `K` independent of
`C`, `F`, `L ≥ 2π` and the shell radii. -/
theorem riemann_shell {a b : ℝ} (ha : 0 ≤ a) (ha3 : a < 3) (hb : 3 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (F : R3 → ℝ) (L r₁ : ℝ) (r₂ : ℝ≥0∞) (A : Set R3),
      0 ≤ C → SingDecay a b C F → 2 * π ≤ L → MeasurableSet A → IsShell r₁ r₂ 0 A →
      IntegrableOn F A ∧ latSummable L A F ∧
      |(L ^ 3)⁻¹ * latSum L A F - ((2 * π) ^ 3)⁻¹ * ∫ p in A, F p|
        ≤ K * C * riemannRate a (2 * π / L) := by
  obtain ⟨K₁, -, hK₁⟩ := integral_sub_setIntegral_shell ha ha3 hb
  obtain ⟨K₂, -, hK₂⟩ := latSum_abs_le ha ha3 hb
  have hK0 : 0 ≤ Shell_K a b := by
    have h3a : 0 < 3 - a := by linarith
    have hb3 : 0 < b - 3 := by linarith
    unfold Shell_K
    positivity
  refine ⟨((2 * π) ^ 3)⁻¹ * (4 * π * Shell_K a b), by positivity, ?_⟩
  intro C F L r₁ r₂ A hC hF hL hA hAs
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hpt := fun n q (hq : q ∈ Cells_cell L n) (hq0 : q ≠ 0) =>
    Shell_pointwise ha hb hC hF hL hAs n hq hq0
  set δ := 2 * π / L with hδdef
  have hδ : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hL0]; exact hL
  -- integrability and summability
  have hFint : Integrable F := (hK₁ C F 0 ⊤ Set.univ hC hF le_rfl (by simp) MeasurableSet.univ
    ⟨fun _ _ _ => trivial, fun _ _ => ⟨norm_nonneg _, le_top⟩⟩).1
  obtain ⟨hsumAbs, -⟩ := hK₂ C F L hC hL hF.bound
  set t : Idx → ℝ := fun n => if n ≠ 0 ∧ mom L n ∈ A then F (mom L n) else 0 with ht
  have htsum : Summable t := by
    refine Summable.of_norm_bounded hsumAbs fun n => ?_
    simp only [ht, Set.mem_univ, and_true, Real.norm_eq_abs]
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact absurd h1.1 h2
    · rw [abs_zero]; exact abs_nonneg _
    · rw [abs_zero]
  refine ⟨hFint.integrableOn, htsum, ?_⟩
  -- the profile and the majorant `Ψ(q) = C |q|⁻² χ(|q|)`
  obtain ⟨hχint, hχle⟩ := Shell_chi_integral (r₁ := r₁) (r₂ := r₂.toReal) ha3 hb hδ hδ1
  set χ := Shell_chi a b δ r₁ r₂.toReal with hχ
  have hχ0 : ∀ s, 0 ≤ χ s := fun s => Shell_chi_nonneg a b δ r₁ r₂.toReal s hδ.le
  set f : ℝ → ℝ := fun s => C * ((s ^ 2)⁻¹ * χ s) with hf
  have hfχ : Set.EqOn (fun s => C * χ s) (fun s => s ^ 2 * f s) (Set.Ioi 0) := by
    intro s hs
    have hs0 : s ≠ 0 := (Set.mem_Ioi.1 hs).ne'
    simp only [hf]
    field_simp
  have hΨint : Integrable (fun q : R3 => f ‖q‖) := by
    have h : IntegrableOn (fun s => s ^ 2 * f s) (Set.Ioi 0) :=
      ((hχint.const_mul C).integrableOn).congr_fun hfχ measurableSet_Ioi
    rw [integrable_fun_norm_addHaar volume]
    simpa [finrank_euclideanSpace_fin] using h
  have hΨval : ∫ q : R3, f ‖q‖ ≤ 4 * π * Shell_K a b * C * riemannRate a δ := by
    rw [integral_radial, ← setIntegral_congr_fun measurableSet_Ioi hfχ, integral_const_mul]
    have h1 : ∫ s in Set.Ioi 0, χ s ≤ ∫ s, χ s :=
      setIntegral_le_integral hχint (Eventually.of_forall hχ0)
    have h2 : C * ∫ s in Set.Ioi 0, χ s ≤ C * (Shell_K a b * riemannRate a δ) :=
      mul_le_mul_of_nonneg_left (h1.trans hχle) hC
    have hpi : 0 < 4 * π := by positivity
    calc 4 * π * (C * ∫ s in Set.Ioi 0, χ s) ≤ 4 * π * (C * (Shell_K a b * riemannRate a δ)) :=
          mul_le_mul_of_nonneg_left h2 hpi.le
      _ = 4 * π * Shell_K a b * C * riemannRate a δ := by ring
  -- decomposition over the cells
  set G : R3 → ℝ := A.indicator F with hG
  have hGint : Integrable G := hFint.indicator hA
  have hGsum : HasSum (fun n => ∫ q in Cells_cell L n, G q) (∫ q in A, F q) := by
    have h := hasSum_integral_iUnion (Cells_measurableSet L) (Cells_pairwise_disjoint hL0)
      (by rw [Cells_iUnion hL0]; exact hGint.integrableOn)
    rwa [Cells_iUnion hL0, Measure.restrict_univ, hG, integral_indicator hA] at h
  have hΨsum : HasSum (fun n => ∫ q in Cells_cell L n, f ‖q‖) (∫ q : R3, f ‖q‖) := by
    have h := hasSum_integral_iUnion (Cells_measurableSet L) (Cells_pairwise_disjoint hL0)
      (by rw [Cells_iUnion hL0]; exact hΨint.integrableOn)
    rwa [Cells_iUnion hL0, Measure.restrict_univ] at h
  have hd : HasSum (fun n => δ ^ 3 * t n - ∫ q in Cells_cell L n, G q)
      (δ ^ 3 * latSum L A F - ∫ q in A, F q) :=
    (htsum.hasSum.mul_left (δ ^ 3)).sub hGsum
  have hkey : ∀ n, |δ ^ 3 * t n - ∫ q in Cells_cell L n, G q| ≤
      ∫ q in Cells_cell L n, f ‖q‖ := by
    intro n
    have hvol : volume.real (Cells_cell L n) = δ ^ 3 := by
      rw [Measure.real, Cells_volume hL0, ENNReal.toReal_ofReal (by positivity)]
    have e : δ ^ 3 * t n - ∫ q in Cells_cell L n, G q =
        ∫ q in Cells_cell L n, (t n - G q) := by
      rw [integral_sub (integrableOn_const (by rw [Cells_volume hL0]; simp)) hGint.integrableOn,
        setIntegral_const, smul_eq_mul, hvol]
    rw [e, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hΨint.integrableOn ?_
    rw [ae_restrict_iff' (Cells_measurableSet L n)]
    filter_upwards [Measure.ae_ne volume (0 : R3)] with q hq0 hq
    have hs0 : 0 < ‖q‖ := norm_pos_iff.2 hq0
    have h := hpt n q hq hq0
    rw [Real.norm_eq_abs, hf]
    simp only
    rw [show C * ((‖q‖ ^ 2)⁻¹ * χ ‖q‖) = C * χ ‖q‖ / ‖q‖ ^ 2 by ring,
      le_div_iff₀ (by positivity), mul_comm]
    exact h
  have habs : |δ ^ 3 * latSum L A F - ∫ q in A, F q| ≤ ∫ q : R3, f ‖q‖ := by
    rw [abs_le]
    constructor
    · have := hasSum_le (fun n => (abs_le.1 (hkey n)).1) hΨsum.neg hd
      linarith
    · exact hasSum_le (fun n => (abs_le.1 (hkey n)).2) hd hΨsum
  have eL : (L ^ 3)⁻¹ = ((2 * π) ^ 3)⁻¹ * δ ^ 3 := by
    rw [hδdef, div_pow]
    field_simp
  have e2 : (L ^ 3)⁻¹ * latSum L A F - ((2 * π) ^ 3)⁻¹ * ∫ p in A, F p =
      ((2 * π) ^ 3)⁻¹ * (δ ^ 3 * latSum L A F - ∫ q in A, F q) := by
    rw [eL]; ring
  rw [e2, abs_mul, abs_of_pos (by positivity)]
  calc ((2 * π) ^ 3)⁻¹ * |δ ^ 3 * latSum L A F - ∫ q in A, F q|
      ≤ ((2 * π) ^ 3)⁻¹ * (4 * π * Shell_K a b * C * riemannRate a δ) :=
        mul_le_mul_of_nonneg_left (habs.trans hΨval) (by positivity)
    _ = ((2 * π) ^ 3)⁻¹ * (4 * π * Shell_K a b) * C * riemannRate a δ := by ring

end LHYUpper
