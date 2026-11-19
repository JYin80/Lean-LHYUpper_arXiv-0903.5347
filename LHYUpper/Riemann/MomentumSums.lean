import LHYUpper.Riemann.Shell

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! Lattice sums of `V_p`, `g_p` and `w_p = g_p/|p|²` over (fuzzy) shells of `Λ* = (2π/L)ℤ³`:
the explicit-rate forms of the limits `|Λ|⁻¹ Σ_u V_u w_u → ‖Vw‖₁` (Lemma 4.3 [lemHS2],
(7.7) [u-uPMH], (7.8) [u-uPL], Lemma 4.5 [lemHAS1]), `|Λ|⁻¹ Σ_u |g_u|²/|u|² → ‖∇w‖₂²` ((4.8)
[proofthem1-1] via (6.2)–(6.4)), `|Λ|⁻² Σ_{u,v} V_{u-v} w_u w_v → ‖Vw²‖₁` ((7.65) [temp8.73],
(10.10) [resultinMk1k2]), and the bounds of facts (2), (5) before (7.65) [temp8.73]. The main
terms are written as momentum integrals `(2π)⁻³ ∫ …`; `V_p`, `g_p` are any functions with the
decay `MomDecay`, `M ≥ 4`.

Every integrand is of the form `φ(p) g_p/|p|²` with `φ` bounded and Lipschitz, hence in the class
`SingDecay 2 4` of the Riemann-sum lemma `riemann_shell`. A fuzzy shell `A` (edge width `s`) lies
between the exact shell `A₀ = {r₁ + s < |p|, |p| + s < r₂}` and `A₀ ∪ B₁ ∪ B₂`, with the ball
`B₁ = {|p| ≤ r₁ + s}` and the exterior `B₂ = {|p| ≥ r₂ - s}`; the sums over `B₁`, `B₂` and the
integrals outside `A₀` are `O(r₁ + s + r₂⁻¹ + E₂(2π/L))`. -/

/-! ### Elementary bounds -/

private lemma MomentumSums_rpow_neg_nat {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    x ^ (-(n : ℝ)) = (x ^ n)⁻¹ := by
  rw [Real.rpow_neg hx, Real.rpow_natCast]

/-- `(1 + x)^{-M} ≤ (1 + x)^{-4} ≤ 1` for `x ≥ 0`, `M ≥ 4`. -/
private lemma MomentumSums_weight_le {x M : ℝ} (hx : 0 ≤ x) (hM : 4 ≤ M) :
    (1 + x) ^ (-M) ≤ ((1 + x) ^ 4)⁻¹ ∧ ((1 + x) ^ 4)⁻¹ ≤ 1 := by
  have h1 : (1 : ℝ) ≤ 1 + x := by linarith
  refine ⟨?_, inv_le_one_of_one_le₀ (one_le_pow₀ h1)⟩
  have h := Real.rpow_le_rpow_of_exponent_le h1 (show -M ≤ -((4 : ℕ) : ℝ) by push_cast; linarith)
  rwa [MomentumSums_rpow_neg_nat (by linarith)] at h

/-- Consequences of `MomDecay f C M`, `M ≥ 4`. -/
private lemma MomentumSums_decay {f : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M) (hf : MomDecay f C M) :
    0 ≤ C ∧ (∀ p, |f p| ≤ C * ((1 + ‖p‖) ^ 4)⁻¹) ∧
      (∀ p q, ‖q - p‖ ≤ 1 → |f q - f p| ≤ C * ‖q - p‖ * ((1 + ‖p‖) ^ 4)⁻¹) ∧
      (∀ p, |f p| ≤ C) ∧ (∀ p q, ‖q - p‖ ≤ 1 → |f q - f p| ≤ C * ‖q - p‖) := by
  have hC : 0 ≤ C := by
    have h := hf.bound 0
    rw [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  have hb : ∀ p : R3, |f p| ≤ C * ((1 + ‖p‖) ^ 4)⁻¹ := fun p =>
    (hf.bound p).trans (mul_le_mul_of_nonneg_left
      (MomentumSums_weight_le (norm_nonneg p) hM).1 hC)
  have hl : ∀ p q : R3, ‖q - p‖ ≤ 1 → |f q - f p| ≤ C * ‖q - p‖ * ((1 + ‖p‖) ^ 4)⁻¹ :=
    fun p q h => (hf.lip p q h).trans (mul_le_mul_of_nonneg_left
      (MomentumSums_weight_le (norm_nonneg p) hM).1 (by positivity))
  refine ⟨hC, hb, hl, fun p => ?_, fun p q h => ?_⟩
  · have := (MomentumSums_weight_le (norm_nonneg p) hM).2
    exact (hb p).trans (by nlinarith)
  · have := (MomentumSums_weight_le (norm_nonneg p) hM).2
    have h0 : 0 ≤ C * ‖q - p‖ := by positivity
    exact (hl p q h).trans (by nlinarith)

/-- `(x²(1 + x)²)⁻¹ ≤ min(x^{-2}, x^{-4})` and `(x³(1 + x))⁻¹ ≤ min(x^{-3}, x^{-4})`. -/
private lemma MomentumSums_min_ge {x : ℝ} (hx : 0 < x) :
    (x ^ 2 * (1 + x) ^ 2)⁻¹ ≤ min (x ^ (-(2 : ℝ))) (x ^ (-(4 : ℝ))) ∧
      (x ^ 3 * (1 + x))⁻¹ ≤ min (x ^ (-(2 : ℝ) - 1)) (x ^ (-(4 : ℝ))) := by
  have e2 : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
    simp [Real.rpow_neg hx.le]
  have e3 : x ^ (-(2 : ℝ) - 1) = (x ^ 3)⁻¹ := by
    rw [show -(2 : ℝ) - 1 = -((3 : ℕ) : ℝ) by norm_num, MomentumSums_rpow_neg_nat hx.le]
  have e4 : x ^ (-(4 : ℝ)) = (x ^ 4)⁻¹ := by
    simp [Real.rpow_neg hx.le]
  rw [e2, e3, e4]
  have h1 : 0 < 1 + x := by linarith
  refine ⟨le_min ?_ ?_, le_min ?_ ?_⟩
  · exact inv_anti₀ (by positivity)
      (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith)))
  · exact inv_anti₀ (by positivity) (by nlinarith [pow_pos hx 2, pow_pos hx 3])
  · exact inv_anti₀ (by positivity) (le_mul_of_one_le_right (by positivity) (by linarith))
  · exact inv_anti₀ (by positivity) (by nlinarith [pow_pos hx 3])

/-- For `|q - p| ≤ |p|/2`, `x = |p| > 0`, `y = |q|`: `y⁻² ≤ 4x⁻²`, `(1 + y)⁻⁴ ≤ 16(1 + x)⁻⁴` and
`|y⁻² - x⁻²| ≤ 10 |q - p| x⁻³`. -/
private lemma MomentumSums_near {p q : R3} (hp : 0 < ‖p‖) (hq : ‖q - p‖ ≤ ‖p‖ / 2) :
    (‖q‖ ^ 2)⁻¹ ≤ 4 * (‖p‖ ^ 2)⁻¹ ∧ ((1 + ‖q‖) ^ 4)⁻¹ ≤ 16 * ((1 + ‖p‖) ^ 4)⁻¹ ∧
      |(‖q‖ ^ 2)⁻¹ - (‖p‖ ^ 2)⁻¹| ≤ 10 * ‖q - p‖ * (‖p‖ ^ 3)⁻¹ := by
  set x := ‖p‖
  set y := ‖q‖
  set t := ‖q - p‖
  have hyx : |y - x| ≤ t := abs_norm_sub_norm_le q p
  have ht0 : 0 ≤ t := norm_nonneg _
  have hy : x / 2 ≤ y := by have := (abs_le.1 hyx).1; linarith
  have hy' : y ≤ 3 * x / 2 := by have := (abs_le.1 hyx).2; linarith
  have hy0 : 0 < y := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [show 4 * (x ^ 2)⁻¹ = ((x / 2) ^ 2)⁻¹ by field_simp; norm_num]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hy 2)
  · rw [show 16 * ((1 + x) ^ 4)⁻¹ = (((1 + x) / 2) ^ 4)⁻¹ by field_simp; norm_num]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  · have e : (y ^ 2)⁻¹ - (x ^ 2)⁻¹ = (x - y) * (x + y) / (x ^ 2 * y ^ 2) := by
      field_simp; ring
    rw [e, abs_div, abs_mul, abs_of_pos (by positivity : 0 < x ^ 2 * y ^ 2),
      abs_of_pos (by positivity : 0 < x + y), abs_sub_comm, div_le_iff₀ (by positivity)]
    have h1 : |y - x| * (x + y) ≤ t * (5 * x / 2) :=
      mul_le_mul hyx (by linarith) (by positivity) ht0
    have h2 : x ^ 4 / 4 ≤ x ^ 2 * y ^ 2 := by
      have : (x / 2) ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
      nlinarith [pow_pos hp 2]
    have h3 : 10 * t * (x ^ 3)⁻¹ * (x ^ 4 / 4) = t * (5 * x / 2) := by
      field_simp; ring
    calc |y - x| * (x + y) ≤ t * (5 * x / 2) := h1
      _ = 10 * t * (x ^ 3)⁻¹ * (x ^ 4 / 4) := h3.symm
      _ ≤ 10 * t * (x ^ 3)⁻¹ * (x ^ 2 * y ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)

/-- If `g` has `MomDecay g C M` (`M ≥ 4`) and `φ` is bounded by `D` and `D`-Lipschitz at distance
`≤ 1`, then `p ↦ φ(p) g(p)/|p|²` is in the class `SingDecay 2 4` with constant `200 C D`. -/
private lemma MomentumSums_singDecay {g φ : R3 → ℝ} {C M D : ℝ} (hM : 4 ≤ M)
    (hg : MomDecay g C M) (hD : 0 ≤ D) (hφ : ∀ p, |φ p| ≤ D)
    (hφl : ∀ p q, ‖q - p‖ ≤ 1 → |φ q - φ p| ≤ D * ‖q - p‖) :
    SingDecay 2 4 (200 * C * D) (fun p => φ p * (g p / ‖p‖ ^ 2)) := by
  obtain ⟨hC, hgb, hgl, -, -⟩ := MomentumSums_decay hM hg
  -- `|φ(p) g(p)/|p|²| ≤ D C (1 + |p|)⁻⁴ |p|⁻²`
  have hval : ∀ p : R3, |φ p * (g p / ‖p‖ ^ 2)| ≤ D * (C * ((1 + ‖p‖) ^ 4)⁻¹) * (‖p‖ ^ 2)⁻¹ := by
    intro p
    rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖p‖ ^ 2), div_eq_mul_inv,
      ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hφ p) (hgb p) (abs_nonneg _) hD)
      (by positivity)
  constructor
  · intro p hp
    have hx : 0 < ‖p‖ := norm_pos_iff.2 hp
    refine (hval p).trans ?_
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (MomentumSums_min_ge hx).1 (by positivity))
    set x := ‖p‖
    have h1 : ((1 + x) ^ 4)⁻¹ ≤ ((1 + x) ^ 2)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) (by norm_num))
    calc D * (C * ((1 + x) ^ 4)⁻¹) * (x ^ 2)⁻¹ ≤ D * (C * ((1 + x) ^ 2)⁻¹) * (x ^ 2)⁻¹ := by
          gcongr
      _ ≤ 200 * C * D * (x ^ 2 * (1 + x) ^ 2)⁻¹ := by
          rw [mul_inv]
          have : 0 ≤ D * C * ((1 + x) ^ 2)⁻¹ * (x ^ 2)⁻¹ := by positivity
          nlinarith
  · intro p q hp hq
    have hx : 0 < ‖p‖ := norm_pos_iff.2 hp
    obtain ⟨n1, n2, n3⟩ := MomentumSums_near hx hq
    set x := ‖p‖ with hxdef
    set y := ‖q‖
    set t := ‖q - p‖ with htdef
    set P := ((1 + x) ^ 4)⁻¹ with hP
    set W := (x ^ 3 * (1 + x))⁻¹ with hW
    have hP0 : 0 ≤ P := by positivity
    have hW0 : 0 ≤ W := by positivity
    have ht0 : 0 ≤ t := norm_nonneg _
    -- `P x⁻² ≤ W`, `P x⁻³ ≤ W`
    have hPW2 : P * (x ^ 2)⁻¹ ≤ W := by
      rw [hP, hW, ← mul_inv]
      refine inv_anti₀ (by positivity) ?_
      have h : x ≤ (1 + x) ^ 3 := by nlinarith [pow_pos hx 2, pow_pos hx 3]
      calc x ^ 3 * (1 + x) = x ^ 2 * (1 + x) * x := by ring
        _ ≤ x ^ 2 * (1 + x) * (1 + x) ^ 3 := mul_le_mul_of_nonneg_left h (by positivity)
        _ = (1 + x) ^ 4 * x ^ 2 := by ring
    have hPW3 : P * (x ^ 3)⁻¹ ≤ W := by
      rw [hP, hW, ← mul_inv]
      refine inv_anti₀ (by positivity) ?_
      calc x ^ 3 * (1 + x) ≤ x ^ 3 * (1 + x) ^ 4 :=
            mul_le_mul_of_nonneg_left (le_self_pow₀ (by linarith) (by norm_num)) (by positivity)
        _ = (1 + x) ^ 4 * x ^ 3 := by ring
    have hgq : |g q| ≤ 16 * C * P := by
      have := hgb q
      calc |g q| ≤ C * ((1 + y) ^ 4)⁻¹ := this
        _ ≤ C * (16 * P) := mul_le_mul_of_nonneg_left n2 hC
        _ = 16 * C * P := by ring
    have hgp : |g p| ≤ C * P := hgb p
    have hy2 : 0 ≤ (y ^ 2)⁻¹ := by positivity
    have hx2 : 0 ≤ (x ^ 2)⁻¹ := by positivity
    have hFq : |φ q * (g q / y ^ 2)| ≤ 64 * D * C * (P * (x ^ 2)⁻¹) := by
      rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ y ^ 2), div_eq_mul_inv]
      calc |φ q| * (|g q| * (y ^ 2)⁻¹) ≤ D * (16 * C * P * (4 * (x ^ 2)⁻¹)) :=
            mul_le_mul (hφ q) (mul_le_mul hgq n1 hy2 (by positivity)) (by positivity) hD
        _ = 64 * D * C * (P * (x ^ 2)⁻¹) := by ring
    have hFp : |φ p * (g p / x ^ 2)| ≤ D * C * (P * (x ^ 2)⁻¹) := by
      have := hval p
      calc |φ p * (g p / x ^ 2)| ≤ D * (C * P) * (x ^ 2)⁻¹ := this
        _ = D * C * (P * (x ^ 2)⁻¹) := by ring
    have hgoal : |φ q * (g q / y ^ 2) - φ p * (g p / x ^ 2)| ≤ 200 * C * D * t * W := by
      rcases le_or_gt t 1 with ht1 | ht1
      · have e : φ q * (g q / y ^ 2) - φ p * (g p / x ^ 2) =
            (φ q - φ p) * (g q * (y ^ 2)⁻¹) +
              φ p * ((g q - g p) * (y ^ 2)⁻¹ + g p * ((y ^ 2)⁻¹ - (x ^ 2)⁻¹)) := by ring
        have a1 : |(φ q - φ p) * (g q * (y ^ 2)⁻¹)| ≤ D * t * (16 * C * P * (4 * (x ^ 2)⁻¹)) := by
          rw [abs_mul, abs_mul, abs_of_nonneg hy2]
          exact mul_le_mul (hφl p q ht1) (mul_le_mul hgq n1 hy2 (by positivity))
            (by positivity) (by positivity)
        have a2 : |(g q - g p) * (y ^ 2)⁻¹| ≤ C * t * P * (4 * (x ^ 2)⁻¹) := by
          rw [abs_mul, abs_of_nonneg hy2]
          exact mul_le_mul (hgl p q ht1) n1 hy2 (by positivity)
        have a3 : |g p * ((y ^ 2)⁻¹ - (x ^ 2)⁻¹)| ≤ C * P * (10 * t * (x ^ 3)⁻¹) := by
          rw [abs_mul]
          exact mul_le_mul hgp n3 (abs_nonneg _) (by positivity)
        have a4 : |φ p * ((g q - g p) * (y ^ 2)⁻¹ + g p * ((y ^ 2)⁻¹ - (x ^ 2)⁻¹))| ≤
            D * (C * t * P * (4 * (x ^ 2)⁻¹) + C * P * (10 * t * (x ^ 3)⁻¹)) := by
          rw [abs_mul]
          exact mul_le_mul (hφ p) ((abs_add_le _ _).trans (add_le_add a2 a3)) (abs_nonneg _) hD
        rw [e]
        refine (abs_add_le _ _).trans ((add_le_add a1 a4).trans ?_)
        have hCDt : 0 ≤ C * D * t := by positivity
        have k1 := mul_le_mul_of_nonneg_left hPW2 hCDt
        have k2 := mul_le_mul_of_nonneg_left hPW3 hCDt
        nlinarith
      · have hsum := (abs_sub _ _).trans (add_le_add hFq hFp)
        refine hsum.trans ?_
        have hCD : 0 ≤ C * D := by positivity
        have k1 := mul_le_mul_of_nonneg_left hPW2 hCD
        have k0 : 0 ≤ C * D * (P * (x ^ 2)⁻¹) := by positivity
        nlinarith
    refine hgoal.trans ?_
    have := (MomentumSums_min_ge hx).2
    rw [← hW] at this
    have h0 : 0 ≤ 200 * C * D * t := by positivity
    exact mul_le_mul_of_nonneg_left this h0

/-- `E₂(δ) ≥ 0` for `δ = 2π/L`, `L ≥ 2π`. -/
private lemma MomentumSums_rate_nonneg {L : ℝ} (hL : 2 * π ≤ L) :
    0 ≤ riemannRate 2 (2 * π / L) := by
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hδ : 0 < 2 * π / L := by positivity
  have hδ1 : 2 * π / L ≤ 1 := by rw [div_le_one hL0]; exact hL
  have hlog : 0 ≤ Real.log (2 * π / L)⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hδ, hδ1⟩)
  simp only [riemannRate, show ¬ (2 : ℝ) < 2 by norm_num, ite_false, ite_true]
  positivity

/-- `E₂(1) = 1`. -/
private lemma MomentumSums_rate_one : riemannRate 2 (2 * π / (2 * π)) = 1 := by
  rw [div_self (by positivity)]
  simp [riemannRate]

/-- For `A ⊆ B`, the summand of `latSum L A F` is dominated by the summand of `latSum L B |F|`. -/
private lemma MomentumSums_term_le {A B : Set R3} (hAB : A ⊆ B) (L : ℝ) (F : R3 → ℝ) (n : Idx) :
    |if n ≠ 0 ∧ mom L n ∈ A then F (mom L n) else 0| ≤
      if n ≠ 0 ∧ mom L n ∈ B then |F (mom L n)| else 0 := by
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, hAB h1.2⟩ h2
  · rw [abs_zero]; exact abs_nonneg _
  · rw [abs_zero]

/-- If `A₀ ⊆ A ⊆ A₀ ∪ B₁ ∪ B₂`, the summands of `latSum L A F` and `latSum L A₀ F` differ by at
most the summands of `latSum L B₁ |F|` and `latSum L B₂ |F|`. -/
private lemma MomentumSums_term_split {A A₀ B₁ B₂ : Set R3} (hA₀A : A₀ ⊆ A)
    (hcov : ∀ p ∈ A, p ∉ A₀ → p ∈ B₁ ∨ p ∈ B₂) (L : ℝ) (F : R3 → ℝ) (n : Idx) :
    |(if n ≠ 0 ∧ mom L n ∈ A then F (mom L n) else 0) -
        (if n ≠ 0 ∧ mom L n ∈ A₀ then F (mom L n) else 0)| ≤
      (if n ≠ 0 ∧ mom L n ∈ B₁ then |F (mom L n)| else 0) +
        (if n ≠ 0 ∧ mom L n ∈ B₂ then |F (mom L n)| else 0) := by
  by_cases hn : n = 0
  · simp [hn]
  set p := mom L n
  have h1 : 0 ≤ (if n ≠ 0 ∧ p ∈ B₁ then |F p| else 0) := by split_ifs <;> simp
  have h2 : 0 ≤ (if n ≠ 0 ∧ p ∈ B₂ then |F p| else 0) := by split_ifs <;> simp
  by_cases h0 : p ∈ A₀
  · rw [ite_eq_left (show n ≠ 0 ∧ p ∈ A from ⟨hn, hA₀A h0⟩),
      ite_eq_left (show n ≠ 0 ∧ p ∈ A₀ from ⟨hn, h0⟩),
      sub_self, abs_zero]
    linarith
  rw [ite_eq_right (show ¬(n ≠ 0 ∧ p ∈ A₀) from fun h => h0 h.2), sub_zero]
  by_cases hA : p ∈ A
  · rw [ite_eq_left (show n ≠ 0 ∧ p ∈ A from ⟨hn, hA⟩)]
    rcases hcov p hA h0 with hb | hb
    · rw [ite_eq_left (show n ≠ 0 ∧ p ∈ B₁ from ⟨hn, hb⟩)] at h1 ⊢; linarith
    · rw [ite_eq_left (show n ≠ 0 ∧ p ∈ B₂ from ⟨hn, hb⟩)] at h2 ⊢; linarith
  · rw [ite_eq_right (show ¬(n ≠ 0 ∧ p ∈ A) from fun h => hA h.2), abs_zero]
    linarith

/-- `|Σ f - Σ g| ≤ Σ h` from `|f n - g n| ≤ h n`. -/
private lemma MomentumSums_abs_tsum_sub_le {f g h : Idx → ℝ} (hf : Summable f) (hg : Summable g)
    (hh : Summable h) (hle : ∀ n, |f n - g n| ≤ h n) : |(∑' n, f n) - ∑' n, g n| ≤ ∑' n, h n := by
  rw [← hf.tsum_sub hg]
  refine abs_le.2 ⟨?_, (hf.sub hg).tsum_le_tsum (fun n => (abs_le.1 (hle n)).2) hh⟩
  rw [← tsum_neg]
  exact hh.neg.tsum_le_tsum (fun n => by linarith [(abs_le.1 (hle n)).1]) (hf.sub hg)

/-- The fuzzy-shell Riemann-sum bound for the class `SingDecay 2 4`:
`| |Λ|⁻¹ Σ_{p ∈ Λ* ∩ A, p ≠ 0} F(p) − (2π)⁻³ ∫ F | ≤ K C (r₁ + s + r₂⁻¹ + E₂(2π/L))`. -/
private lemma MomentumSums_fuzzy :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (F : R3 → ℝ) (L r₁ s : ℝ) (r₂ : ℝ≥0∞) (A : Set R3),
      0 ≤ C → SingDecay 2 4 C F → 2 * π ≤ L → 0 ≤ r₁ → 0 ≤ s → 0 < r₂ → IsShell r₁ r₂ s A →
      Integrable F ∧ latSummable L A F ∧
      |(L ^ 3)⁻¹ * latSum L A F - ((2 * π) ^ 3)⁻¹ * ∫ p, F p|
        ≤ K * C * (r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L)) := by
  obtain ⟨K₁, hK₁0, hK₁⟩ := riemann_shell (a := 2) (b := 4) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨K₂, hK₂0, hK₂⟩ := latSum_abs_le (a := 2) (b := 4) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨K₃, hK₃0, hK₃⟩ := integral_sub_setIntegral_shell (a := 2) (b := 4) (by norm_num)
    (by norm_num) (by norm_num)
  set c : ℝ := ((2 * π) ^ 3)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  refine ⟨4 * (K₁ + 2 * K₂) + 3 * K₁ + 4 * c * K₃, by positivity, ?_⟩
  intro C F L r₁ s r₂ A hC hF hL hr₁ hs hr₂ hAs
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hE := MomentumSums_rate_nonneg hL
  set E := riemannRate 2 (2 * π / L) with hEdef
  set ρ₂ := (r₂⁻¹).toReal with hρ₂
  have hρ₂0 : 0 ≤ ρ₂ := ENNReal.toReal_nonneg
  have hFa : SingDecay 2 4 C (fun p => |F p|) :=
    ⟨fun p hp => by rw [abs_abs]; exact hF.bound p hp,
      fun p q hp hq => (abs_abs_sub_abs_le_abs_sub _ _).trans (hF.lip p q hp hq)⟩
  have hshell_univ : IsShell 0 ⊤ 0 (Set.univ : Set R3) :=
    ⟨fun _ _ _ => trivial, fun _ _ => ⟨norm_nonneg _, le_top⟩⟩
  have hFint : Integrable F :=
    (hK₃ C F 0 ⊤ Set.univ hC hF le_rfl (by simp) MeasurableSet.univ hshell_univ).1
  obtain ⟨hsumU, hsumU_le⟩ := hK₂ C F L hC hL hF.bound
  have hsumA : latSummable L A F :=
    Summable.of_norm_bounded hsumU fun n => by
      rw [Real.norm_eq_abs]; exact MomentumSums_term_le (Set.subset_univ A) L F n
  refine ⟨hFint, hsumA, ?_⟩
  have hK : 0 ≤ 4 * (K₁ + 2 * K₂) + 3 * K₁ + 4 * c * K₃ := by positivity
  have hR0 : 0 ≤ r₁ + s + ρ₂ + E := by positivity
  by_cases hgood : r₁ + s + ρ₂ < 1 / 4
  swap
  · -- trivial bound
    push Not at hgood
    have hlatA : |latSum L A F| ≤ latSum L Set.univ (fun p => |F p|) := by
      have h := MomentumSums_abs_tsum_sub_le hsumA (summable_zero) hsumU
        (fun n => by rw [sub_zero]; exact MomentumSums_term_le (Set.subset_univ A) L F n)
      simpa [latSum] using h
    -- `(2π)⁻³ ∫ |F| ≤ (K₁ + K₂) C`, from the Riemann-sum lemma at `L = 2π`
    have hint : c * ∫ p, |F p| ≤ (K₁ + K₂) * C := by
      obtain ⟨-, -, h⟩ := hK₁ C (fun p => |F p|) (2 * π) 0 ⊤ Set.univ hC hFa le_rfl
        MeasurableSet.univ hshell_univ
      obtain ⟨-, h'⟩ := hK₂ C F (2 * π) hC le_rfl hF.bound
      rw [MomentumSums_rate_one, Measure.restrict_univ] at h
      have := (abs_le.1 h).1
      nlinarith
    have hI : |∫ p, F p| ≤ ∫ p, |F p| := abs_integral_le_integral_abs
    have hL3 : 0 < (L ^ 3)⁻¹ := by positivity
    calc |(L ^ 3)⁻¹ * latSum L A F - c * ∫ p, F p|
        ≤ (L ^ 3)⁻¹ * |latSum L A F| + c * |∫ p, F p| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos hL3, abs_of_pos hc0]
      _ ≤ K₂ * C + (K₁ + K₂) * C := by
          have := mul_le_mul_of_nonneg_left hlatA hL3.le
          have := mul_le_mul_of_nonneg_left hI hc0.le
          linarith
      _ ≤ 4 * (K₁ + 2 * K₂) * C * (r₁ + s + ρ₂ + E) := by
          have h1 : 1 / 4 ≤ r₁ + s + ρ₂ + E := by linarith
          have h2 : 0 ≤ (K₁ + 2 * K₂) * C := by positivity
          nlinarith
      _ ≤ (4 * (K₁ + 2 * K₂) + 3 * K₁ + 4 * c * K₃) * C * (r₁ + s + ρ₂ + E) := by
          have : 0 ≤ (3 * K₁ + 4 * c * K₃) * C * (r₁ + s + ρ₂ + E) := by positivity
          nlinarith
  -- good case: an exterior radius `r₂'` with `|p| < r₂' ⇒ |p| + s < r₂` and `r₂'⁻¹ ≤ 2 r₂⁻¹`
  obtain ⟨r₂', hr₂'0, hr₂'s, hr₂'ρ⟩ : ∃ r₂' : ℝ≥0∞, 0 < r₂' ∧
      (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x < r₂' → ENNReal.ofReal (x + s) < r₂) ∧
      (r₂'⁻¹).toReal ≤ 2 * ρ₂ := by
    by_cases htop : r₂ = ⊤
    · refine ⟨⊤, by simp, fun x _ _ => htop ▸ ENNReal.ofReal_lt_top, by simpa using hρ₂0⟩
    · set R := r₂.toReal with hR
      have hr₂R : r₂ = ENNReal.ofReal R := (ENNReal.ofReal_toReal htop).symm
      have hR0 : 0 < R := ENNReal.toReal_pos hr₂.ne' htop
      have hρR : ρ₂ = R⁻¹ := by rw [hρ₂, ENNReal.toReal_inv]
      have hR4 : 4 < R := by
        have : R⁻¹ < 1 / 4 := by rw [← hρR]; linarith
        rw [inv_lt_comm₀ hR0 (by norm_num)] at this
        norm_num at this; exact this
      have hs4 : s < 1 / 4 := by linarith
      refine ⟨ENNReal.ofReal (R - s), ENNReal.ofReal_pos.2 (by linarith), fun x hx h => ?_, ?_⟩
      · rw [hr₂R, ENNReal.ofReal_lt_ofReal_iff' ] at *
        obtain ⟨h1, -⟩ := h
        exact ⟨by linarith, hR0⟩
      · rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith), hρR]
        rw [inv_le_comm₀ (by linarith) (by positivity)]
        rw [mul_inv, inv_inv]
        nlinarith
  -- the exact shell `A₀`, the ball `B₁` and the exterior `B₂`
  set A₀ : Set R3 := {p | r₁ + s < ‖p‖ ∧ ENNReal.ofReal ‖p‖ < r₂'} with hA₀
  set B₁ : Set R3 := {p | ‖p‖ ≤ r₁ + s} with hB₁
  set B₂ : Set R3 := {p | r₂' ≤ ENNReal.ofReal ‖p‖} with hB₂
  have hA₀m : MeasurableSet A₀ :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_norm) measurable_const)
  have hB₁m : MeasurableSet B₁ := measurableSet_le measurable_norm measurable_const
  have hB₂m : MeasurableSet B₂ :=
    measurableSet_le measurable_const (ENNReal.measurable_ofReal.comp measurable_norm)
  have hA₀s : IsShell (r₁ + s) r₂' 0 A₀ :=
    ⟨fun p h1 h2 => ⟨by simpa using h1, by simpa using h2⟩, fun p hp => ⟨hp.1.le, hp.2.le⟩⟩
  have hB₁s : IsShell 0 (ENNReal.ofReal (r₁ + s)) 0 B₁ :=
    ⟨fun p _ h2 => by
      simp only [add_zero] at h2
      exact ((ENNReal.ofReal_lt_ofReal_iff'.1 h2).1).le,
     fun p hp => ⟨norm_nonneg p, ENNReal.ofReal_le_ofReal hp⟩⟩
  have hA₀A : A₀ ⊆ A := fun p hp => hAs.1 p hp.1 (hr₂'s _ (norm_nonneg p) hp.2)
  have hcov : ∀ p ∈ A, p ∉ A₀ → p ∈ B₁ ∨ p ∈ B₂ := by
    intro p _ hp0
    by_cases h : ‖p‖ ≤ r₁ + s
    · exact Or.inl h
    · right
      exact not_lt.1 fun h' => hp0 ⟨not_le.1 h, h'⟩
  -- the exact shell
  obtain ⟨-, hsum₀, h₀⟩ := hK₁ C F L (r₁ + s) r₂' A₀ hC hF hL hA₀m hA₀s
  obtain ⟨-, h₀'⟩ := hK₃ C F (r₁ + s) r₂' A₀ hC hF (by positivity) hr₂'0 hA₀m hA₀s
  -- the ball
  obtain ⟨-, hsum₁, h₁⟩ := hK₁ C (fun p => |F p|) L 0 _ B₁ hC hFa hL hB₁m hB₁s
  have hB₁c : B₁ᶜ = {p : R3 | r₁ + s < ‖p‖} := by ext p; simp [hB₁]
  obtain ⟨-, h₁'⟩ := hK₃ C (fun p => |F p|) (r₁ + s) ⊤ B₁ᶜ hC hFa (by positivity) (by simp)
    hB₁m.compl (by rw [hB₁c]; exact ⟨fun p h _ => by simpa using h, fun p hp => ⟨hp.le, le_top⟩⟩)
  have hI₁ := integral_add_compl hB₁m hFint.abs
  -- the exterior
  have hB₂rs : latSummable L B₂ (fun p => |F p|) ∧
      |(L ^ 3)⁻¹ * latSum L B₂ (fun p => |F p|) - c * (∫ p in B₂, |F p|)| ≤ K₁ * C * E := by
    by_cases htop : r₂' = ⊤
    · have hB₂e : B₂ = ∅ := by ext p; simp [hB₂, htop]
      obtain ⟨-, h1, h2⟩ := hK₁ C (fun p => |F p|) L 0 0 B₂ hC hFa hL hB₂m
        ⟨fun p _ h => absurd h (by simp),
          fun p hp => by rw [hB₂e] at hp; exact absurd hp (Set.notMem_empty p)⟩
      exact ⟨h1, h2⟩
    · obtain ⟨-, h1, h2⟩ := hK₁ C (fun p => |F p|) L r₂'.toReal ⊤ B₂ hC hFa hL hB₂m
        ⟨fun p h _ => by
          change r₂' ≤ ENNReal.ofReal ‖p‖
          rw [← ENNReal.ofReal_toReal htop]
          exact ENNReal.ofReal_le_ofReal (by simp only [add_zero] at h; exact h.le),
         fun p hp => ⟨ENNReal.toReal_le_of_le_ofReal (norm_nonneg p) hp, le_top⟩⟩
      exact ⟨h1, h2⟩
  obtain ⟨hsum₂, h₂⟩ := hB₂rs
  have hB₂c : B₂ᶜ = {p : R3 | ENNReal.ofReal ‖p‖ < r₂'} := by ext p; simp [hB₂]
  obtain ⟨-, h₂'⟩ := hK₃ C (fun p => |F p|) 0 r₂' B₂ᶜ hC hFa le_rfl hr₂'0 hB₂m.compl
    (by rw [hB₂c]; exact ⟨fun p _ h => by simpa using h, fun p hp => ⟨norm_nonneg p, hp.le⟩⟩)
  have hI₂ := integral_add_compl hB₂m hFint.abs
  -- the sum over `A ∖ A₀`
  have hdiff : |latSum L A F - latSum L A₀ F| ≤
      latSum L B₁ (fun p => |F p|) + latSum L B₂ (fun p => |F p|) := by
    rw [latSum, latSum, latSum, latSum, ← hsum₁.tsum_add hsum₂]
    exact MomentumSums_abs_tsum_sub_le hsumA hsum₀ (hsum₁.add hsum₂)
      (MomentumSums_term_split hA₀A hcov L F)
  -- assembly
  set ρ₂' := (r₂'⁻¹).toReal
  have hρ₂'0 : 0 ≤ ρ₂' := ENNReal.toReal_nonneg
  norm_num at h₀' h₁' h₂'
  have hL3 : 0 < (L ^ 3)⁻¹ := by positivity
  have ha : |(L ^ 3)⁻¹ * latSum L A F - (L ^ 3)⁻¹ * latSum L A₀ F| ≤
      (L ^ 3)⁻¹ * latSum L B₁ (fun p => |F p|) + (L ^ 3)⁻¹ * latSum L B₂ (fun p => |F p|) := by
    rw [← mul_sub, ← mul_add, abs_mul, abs_of_pos hL3]
    exact mul_le_mul_of_nonneg_left hdiff hL3.le
  have hb : |c * (∫ p, F p) - c * ∫ p in A₀, F p| ≤ c * (K₃ * C * (r₁ + s + ρ₂')) := by
    rw [← mul_sub, abs_mul, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left h₀' hc0.le
  have hc1 : c * ∫ p in B₁, |F p| ≤ c * (K₃ * C * (r₁ + s)) := by
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    have := (abs_le.1 h₁').2
    linarith
  have hc2 : c * ∫ p in B₂, |F p| ≤ c * (K₃ * C * ρ₂') := by
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    have := (abs_le.1 h₂').2
    linarith
  have he : c * (K₃ * C * ρ₂') ≤ c * (K₃ * C * (2 * ρ₂)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr₂'ρ (by positivity)) hc0.le
  have hX : |(L ^ 3)⁻¹ * latSum L A F - c * ∫ p, F p| ≤
      3 * (K₁ * C * E) + 2 * (c * (K₃ * C * (r₁ + s))) + 4 * (c * (K₃ * C * ρ₂)) := by
    have e1 := abs_le.1 h₀
    have e2 := abs_le.1 h₁
    have e3 := abs_le.1 h₂
    have e4 := abs_le.1 ha
    have e5 := abs_le.1 hb
    have hcK : c * (K₃ * C * (r₁ + s + ρ₂')) =
        c * (K₃ * C * (r₁ + s)) + c * (K₃ * C * ρ₂') := by ring
    rw [abs_le]
    constructor <;> linarith
  refine hX.trans ?_
  have hpos : 0 ≤ 4 * (K₁ + 2 * K₂) * C * (r₁ + s + ρ₂ + E) + 3 * K₁ * C * (r₁ + s + ρ₂) +
      2 * c * K₃ * C * (r₁ + s) + 4 * c * K₃ * C * E := by positivity
  linarith

/-- Functions of the class `SingDecay 2 4` are integrable on `ℝ³`. -/
private lemma MomentumSums_integrable {C : ℝ} {F : R3 → ℝ} (hC : 0 ≤ C) (hF : SingDecay 2 4 C F) :
    Integrable F := by
  obtain ⟨K, -, hK⟩ := integral_sub_setIntegral_shell (a := 2) (b := 4) (by norm_num)
    (by norm_num) (by norm_num)
  exact (hK C F 0 ⊤ Set.univ hC hF le_rfl (by simp) MeasurableSet.univ
    ⟨fun _ _ _ => trivial, fun _ _ => ⟨norm_nonneg _, le_top⟩⟩).1

/-- `p ↦ V_{u-p} g_p/|p|²` is in the class `SingDecay 2 4` with constant `200 C²`, for every `u`. -/
private lemma MomentumSums_shift_singDecay {Vp gp : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M)
    (hV : MomDecay Vp C M) (hg : MomDecay gp C M) (u : R3) :
    SingDecay 2 4 (200 * C * C) (fun p => Vp (u - p) * (gp p / ‖p‖ ^ 2)) := by
  obtain ⟨hC, -, -, hVb, hVl⟩ := MomentumSums_decay hM hV
  refine MomentumSums_singDecay (φ := fun p => Vp (u - p)) hM hg hC (fun p => hVb _) ?_
  intro p q h
  have e : (u - q) - (u - p) = -(q - p) := by abel
  have := hVl (u - p) (u - q) (by rw [e, norm_neg]; exact h)
  rwa [e, norm_neg] at this

/-- `w_p = g_p/|p|²` is in the class `SingDecay 2 4` with constant `200 C`. -/
private lemma MomentumSums_w_singDecay {gp : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M)
    (hg : MomDecay gp C M) : SingDecay 2 4 (200 * C) (fun p => gp p / ‖p‖ ^ 2) := by
  have h := MomentumSums_singDecay (φ := fun _ => (1 : ℝ)) hM hg zero_le_one (fun _ => by simp)
    (fun p q _ => by simp)
  simpa using h

/-! ### Single sums -/

/-- `|Λ|^{-1} Σ V_u w_u → (2π)^{-3} ∫ V_p w_p`: Lemma 4.3 [lemHS2], (7.7)–(7.8), Lemma 4.5. -/
theorem sum_Vw {Vp gp : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M) (hV : MomDecay Vp C M)
    (hg : MomDecay gp C M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L r₁ s : ℝ) (r₂ : ℝ≥0∞) (A : Set R3),
      2 * π ≤ L → 0 ≤ r₁ → 0 ≤ s → 0 < r₂ → MeasurableSet A → IsShell r₁ r₂ s A →
      latSummable L A (fun p => Vp p * (gp p / ‖p‖ ^ 2)) ∧
      |(L ^ 3)⁻¹ * latSum L A (fun p => Vp p * (gp p / ‖p‖ ^ 2))
        - ((2 * π) ^ 3)⁻¹ * ∫ p, Vp p * (gp p / ‖p‖ ^ 2)|
        ≤ K * (r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L)) := by
  obtain ⟨K, hK0, hK⟩ := MomentumSums_fuzzy
  obtain ⟨hC, -, -, hVb, hVl⟩ := MomentumSums_decay hM hV
  have hF := MomentumSums_singDecay hM hg hC hVb hVl
  refine ⟨K * (200 * C * C), by positivity, ?_⟩
  intro L r₁ s r₂ A hL hr₁ hs hr₂ _ hAs
  obtain ⟨-, h1, h2⟩ := hK _ _ L r₁ s r₂ A (by positivity) hF hL hr₁ hs hr₂ hAs
  exact ⟨h1, h2⟩

/-- `|Λ|^{-1} Σ_v V_{u-v} w_v`, uniformly in `u`. -/
theorem sum_Vshift_w {Vp gp : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M) (hV : MomDecay Vp C M)
    (hg : MomDecay gp C M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : R3) (L r₁ s : ℝ) (r₂ : ℝ≥0∞) (A : Set R3),
      2 * π ≤ L → 0 ≤ r₁ → 0 ≤ s → 0 < r₂ → MeasurableSet A → IsShell r₁ r₂ s A →
      latSummable L A (fun p => Vp (u - p) * (gp p / ‖p‖ ^ 2)) ∧
      |(L ^ 3)⁻¹ * latSum L A (fun p => Vp (u - p) * (gp p / ‖p‖ ^ 2))
        - ((2 * π) ^ 3)⁻¹ * ∫ p, Vp (u - p) * (gp p / ‖p‖ ^ 2)|
        ≤ K * (r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L)) := by
  obtain ⟨K, hK0, hK⟩ := MomentumSums_fuzzy
  obtain ⟨hC, -⟩ := MomentumSums_decay hM hV
  refine ⟨K * (200 * C * C), by positivity, ?_⟩
  intro u L r₁ s r₂ A hL hr₁ hs hr₂ _ hAs
  obtain ⟨-, h1, h2⟩ := hK _ _ L r₁ s r₂ A (by positivity)
    (MomentumSums_shift_singDecay hM hV hg u) hL hr₁ hs hr₂ hAs
  exact ⟨h1, h2⟩

/-- The form used in (7.67) [temp8.75]: `V_{u-v}` replaced by `V_v` at cost `O(|u|)`. -/
theorem sum_Vshift_w_near {Vp gp : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M) (hV : MomDecay Vp C M)
    (hg : MomDecay gp C M) (hVe : ∀ p, Vp (-p) = Vp p) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : R3) (L r₁ s : ℝ) (r₂ : ℝ≥0∞) (A : Set R3),
      2 * π ≤ L → 0 ≤ r₁ → 0 ≤ s → 0 < r₂ → MeasurableSet A → IsShell r₁ r₂ s A →
      |(L ^ 3)⁻¹ * latSum L A (fun p => Vp (u - p) * (gp p / ‖p‖ ^ 2))
        - ((2 * π) ^ 3)⁻¹ * ∫ p, Vp p * (gp p / ‖p‖ ^ 2)|
        ≤ K * (‖u‖ + r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L)) := by
  obtain ⟨K₄, hK₄0, hK₄⟩ := sum_Vshift_w hM hV hg
  obtain ⟨hC, -, -, hVb, hVl⟩ := MomentumSums_decay hM hV
  have hwint := MomentumSums_integrable (by positivity) (MomentumSums_w_singDecay hM hg)
  set Iw := ∫ p, |gp p / ‖p‖ ^ 2| with hIw
  have hIw0 : 0 ≤ Iw := integral_nonneg fun _ => abs_nonneg _
  set c : ℝ := ((2 * π) ^ 3)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  refine ⟨K₄ + c * (2 * C * Iw), by positivity, ?_⟩
  intro u L r₁ s r₂ A hL hr₁ hs hr₂ hA hAs
  have h1 := (hK₄ u L r₁ s r₂ A hL hr₁ hs hr₂ hA hAs).2
  -- `|V_{u-p} - V_p| ≤ 2 C |u|`
  have hpt : ∀ p : R3, |Vp (u - p) - Vp p| ≤ 2 * C * ‖u‖ := by
    intro p
    rcases le_or_gt ‖u‖ 1 with hu | hu
    · have e := hVe (p - u)
      rw [neg_sub] at e
      have h := hVl p (p - u) (by rw [sub_sub_cancel_left, norm_neg]; exact hu)
      rw [sub_sub_cancel_left, norm_neg] at h
      rw [e]
      nlinarith [norm_nonneg u]
    · calc |Vp (u - p) - Vp p| ≤ |Vp (u - p)| + |Vp p| := abs_sub _ _
        _ ≤ C + C := add_le_add (hVb _) (hVb _)
        _ ≤ 2 * C * ‖u‖ := by nlinarith
  have hI1 := MomentumSums_integrable (by positivity) (MomentumSums_shift_singDecay hM hV hg u)
  have hI2 := MomentumSums_integrable (by positivity) (MomentumSums_singDecay hM hg hC hVb hVl)
  have hdiff : |(∫ p, Vp (u - p) * (gp p / ‖p‖ ^ 2)) - ∫ p, Vp p * (gp p / ‖p‖ ^ 2)| ≤
      2 * C * ‖u‖ * Iw := by
    rw [← integral_sub hI1 hI2, ← Real.norm_eq_abs, hIw, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hwint.abs.const_mul _) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right (hpt p) (abs_nonneg _)
  set R := r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L) with hR
  have hR0 : 0 ≤ R := by
    have := MomentumSums_rate_nonneg hL
    have : 0 ≤ (r₂⁻¹).toReal := ENNReal.toReal_nonneg
    rw [hR]; positivity
  have e : ‖u‖ + r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L) = ‖u‖ + R := by
    rw [hR]; ring
  rw [e]
  have h3 : |c * (∫ p, Vp (u - p) * (gp p / ‖p‖ ^ 2)) - c * ∫ p, Vp p * (gp p / ‖p‖ ^ 2)| ≤
      c * (2 * C * ‖u‖ * Iw) := by
    rw [← mul_sub, abs_mul, abs_of_pos hc0]
    exact mul_le_mul_of_nonneg_left hdiff hc0.le
  have h4 := abs_sub_le ((L ^ 3)⁻¹ * latSum L A (fun p => Vp (u - p) * (gp p / ‖p‖ ^ 2)))
    (c * ∫ p, Vp (u - p) * (gp p / ‖p‖ ^ 2)) (c * ∫ p, Vp p * (gp p / ‖p‖ ^ 2))
  refine h4.trans ?_
  have hu0 := norm_nonneg u
  have : 0 ≤ K₄ * ‖u‖ + c * (2 * C * Iw) * R := by positivity
  nlinarith

/-- `|Λ|^{-1} Σ u² w_u² = |Λ|^{-1} Σ |g_u|² |u|^{-2} → (2π)^{-3} ∫ |g_p|² |p|^{-2}`:
(4.8) [proofthem1-1] via (6.2)–(6.4). -/
theorem sum_g2 {gp : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M) (hg : MomDecay gp C M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L r₁ s : ℝ) (r₂ : ℝ≥0∞) (A : Set R3),
      2 * π ≤ L → 0 ≤ r₁ → 0 ≤ s → 0 < r₂ → MeasurableSet A → IsShell r₁ r₂ s A →
      latSummable L A (fun p => gp p ^ 2 / ‖p‖ ^ 2) ∧
      |(L ^ 3)⁻¹ * latSum L A (fun p => gp p ^ 2 / ‖p‖ ^ 2)
        - ((2 * π) ^ 3)⁻¹ * ∫ p, gp p ^ 2 / ‖p‖ ^ 2|
        ≤ K * (r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L)) := by
  obtain ⟨K, hK0, hK⟩ := MomentumSums_fuzzy
  obtain ⟨hC, -, -, hgb, hgl⟩ := MomentumSums_decay hM hg
  have hF := MomentumSums_singDecay hM hg hC hgb hgl
  have e : (fun p : R3 => gp p ^ 2 / ‖p‖ ^ 2) = fun p => gp p * (gp p / ‖p‖ ^ 2) := by
    funext p; ring
  refine ⟨K * (200 * C * C), by positivity, ?_⟩
  intro L r₁ s r₂ A hL hr₁ hs hr₂ _ hAs
  obtain ⟨-, h1, h2⟩ := hK _ _ L r₁ s r₂ A (by positivity) hF hL hr₁ hs hr₂ hAs
  rw [e]
  exact ⟨h1, h2⟩

/-! ### Double sums -/

/-- `|Λ|^{-2} Σ V_{u-v} w_u w_v → (2π)^{-6} ∫∫ V_{p-q} w_p w_q`: (7.65) [temp8.73],
(10.10) [resultinMk1k2]. -/
theorem sum_Vww {Vp gp : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M) (hV : MomDecay Vp C M)
    (hg : MomDecay gp C M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L r₁ s : ℝ) (r₂ : ℝ≥0∞) (A : Set R3),
      2 * π ≤ L → 0 ≤ r₁ → 0 ≤ s → 0 < r₂ → MeasurableSet A → IsShell r₁ r₂ s A →
      latSummable2 L A (fun p q => Vp (p - q) * (gp p / ‖p‖ ^ 2) * (gp q / ‖q‖ ^ 2)) ∧
      |((L ^ 3) ^ 2)⁻¹ * latSum2 L A (fun p q => Vp (p - q) * (gp p / ‖p‖ ^ 2) * (gp q / ‖q‖ ^ 2))
        - (((2 * π) ^ 3) ^ 2)⁻¹ *
            ∫ p, ∫ q, Vp (p - q) * (gp p / ‖p‖ ^ 2) * (gp q / ‖q‖ ^ 2)|
        ≤ K * (r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L)) := by
  obtain ⟨Kf, hKf0, hKf⟩ := MomentumSums_fuzzy
  obtain ⟨K₂, hK₂0, hK₂⟩ := latSum_abs_le (a := 2) (b := 4) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨K₃, hK₃0, hK₃⟩ := sum_Vshift_w hM hV hg
  obtain ⟨hC, -, -, hVb, hVl⟩ := MomentumSums_decay hM hV
  set c : ℝ := ((2 * π) ^ 3)⁻¹ with hc
  have hc0 : 0 < c := by positivity
  have hwD := MomentumSums_w_singDecay hM hg
  have hwint := MomentumSums_integrable (by positivity) hwD
  set Iw := ∫ q, |gp q / ‖q‖ ^ 2| with hIw
  have hIw0 : 0 ≤ Iw := integral_nonneg fun _ => abs_nonneg _
  have hF3 : ∀ u, Integrable (fun q => Vp (u - q) * (gp q / ‖q‖ ^ 2)) := fun u =>
    MomentumSums_integrable (by positivity) (MomentumSums_shift_singDecay hM hV hg u)
  -- `Ψ(p) = (2π)⁻³ ∫ V_{p-q} w_q dq` is bounded and Lipschitz with constant `D = (2π)⁻³ C ‖w‖₁`
  set Ψ : R3 → ℝ := fun p => c * ∫ q, Vp (p - q) * (gp q / ‖q‖ ^ 2) with hΨ
  set D := c * C * Iw with hD
  have hD0 : 0 ≤ D := by positivity
  have hΨb : ∀ p, |Ψ p| ≤ D := by
    intro p
    simp only [hΨ, hD]
    rw [abs_mul, abs_of_pos hc0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    rw [← Real.norm_eq_abs, hIw, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hwint.abs.const_mul _) (Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hVb _) (abs_nonneg _)
  have hΨl : ∀ p q, ‖q - p‖ ≤ 1 → |Ψ q - Ψ p| ≤ D * ‖q - p‖ := by
    intro p q h
    simp only [hΨ, hD]
    rw [← mul_sub, ← integral_sub (hF3 q) (hF3 p), abs_mul, abs_of_pos hc0,
      show c * C * Iw * ‖q - p‖ = c * (∫ k, C * ‖q - p‖ * |gp k / ‖k‖ ^ 2|) by
        rw [integral_const_mul, hIw]; ring]
    refine mul_le_mul_of_nonneg_left ?_ hc0.le
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le (hwint.abs.const_mul _) (Eventually.of_forall fun k => ?_)
    rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have e : (q - k) - (p - k) = q - p := by abel
    have := hVl (p - k) (q - k) (by rw [e]; exact h)
    rwa [e] at this
  have hH := MomentumSums_singDecay hM hg hD0 hΨb hΨl
  refine ⟨K₃ * K₂ * (200 * C) + Kf * (200 * C * D), by positivity, ?_⟩
  intro L r₁ s r₂ A hL hr₁ hs hr₂ hA hAs
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hL3 : 0 < (L ^ 3)⁻¹ := by positivity
  obtain ⟨-, hHsum, hHbd⟩ := hKf _ _ L r₁ s r₂ A (by positivity) hH hL hr₁ hs hr₂ hAs
  obtain ⟨hwsumU, hwsumU_le⟩ := hK₂ (200 * C) _ L (by positivity) hL hwD.bound
  set R := r₁ + s + (r₂⁻¹).toReal + riemannRate 2 (2 * π / L) with hR
  have hR0 : 0 ≤ R := by
    have := MomentumSums_rate_nonneg hL
    have : 0 ≤ (r₂⁻¹).toReal := ENNReal.toReal_nonneg
    rw [hR]; positivity
  -- `a_n = |[n ≠ 0, p_n ∈ A] w(p_n)|`
  set a : Idx → ℝ := fun n =>
    |if n ≠ 0 ∧ mom L n ∈ A then gp (mom L n) / ‖mom L n‖ ^ 2 else 0| with ha
  have ha0 : 0 ≤ a := fun n => abs_nonneg _
  have hale := fun n => MomentumSums_term_le (Set.subset_univ A) L (fun p => gp p / ‖p‖ ^ 2) n
  have hasum : Summable a := Summable.of_nonneg_of_le ha0 hale hwsumU
  have hasum_le : (L ^ 3)⁻¹ * ∑' n, a n ≤ K₂ * (200 * C) :=
    (mul_le_mul_of_nonneg_left (hasum.tsum_le_tsum hale hwsumU) hL3.le).trans hwsumU_le
  -- the summand of the double sum
  set t : Idx × Idx → ℝ := fun nm =>
    if nm.1 ≠ 0 ∧ nm.2 ≠ 0 ∧ mom L nm.1 ∈ A ∧ mom L nm.2 ∈ A then
      Vp (mom L nm.1 - mom L nm.2) * (gp (mom L nm.1) / ‖mom L nm.1‖ ^ 2) *
        (gp (mom L nm.2) / ‖mom L nm.2‖ ^ 2) else 0 with ht
  have htle : ∀ nm, |t nm| ≤ C * (a nm.1 * a nm.2) := by
    intro nm
    simp only [ht, ha]
    by_cases h : nm.1 ≠ 0 ∧ nm.2 ≠ 0 ∧ mom L nm.1 ∈ A ∧ mom L nm.2 ∈ A
    · rw [ite_eq_left h, ite_eq_left (show nm.1 ≠ 0 ∧ mom L nm.1 ∈ A from ⟨h.1, h.2.2.1⟩),
        ite_eq_left (show nm.2 ≠ 0 ∧ mom L nm.2 ∈ A from ⟨h.2.1, h.2.2.2⟩), abs_mul, abs_mul,
        mul_assoc]
      exact mul_le_mul_of_nonneg_right (hVb _) (by positivity)
    · rw [ite_eq_right h, abs_zero]
      positivity
  have hprod : Summable (fun nm : Idx × Idx => a nm.1 * a nm.2) :=
    hasum.mul_of_nonneg hasum ha0 ha0
  have htsum : Summable t := Summable.of_norm_bounded (hprod.mul_left C)
    (fun nm => by rw [Real.norm_eq_abs]; exact htle nm)
  refine ⟨htsum, ?_⟩
  -- Fubini for the double sum: `latSum2 = Σ_n [n ≠ 0, p_n ∈ A] w(p_n) S(p_n)`
  set S : R3 → ℝ := fun u => latSum L A (fun q => Vp (u - q) * (gp q / ‖q‖ ^ 2)) with hS
  set T : Idx → ℝ := fun n =>
    if n ≠ 0 ∧ mom L n ∈ A then gp (mom L n) / ‖mom L n‖ ^ 2 * S (mom L n) else 0 with hT
  have hrow : ∀ n, ∑' m, t (n, m) = T n := by
    intro n
    by_cases h : n ≠ 0 ∧ mom L n ∈ A
    · have e : (fun m => t (n, m)) = fun m => gp (mom L n) / ‖mom L n‖ ^ 2 *
          (if m ≠ 0 ∧ mom L m ∈ A then
            Vp (mom L n - mom L m) * (gp (mom L m) / ‖mom L m‖ ^ 2) else 0) := by
        funext m
        simp only [ht]
        by_cases hm : m ≠ 0 ∧ mom L m ∈ A
        · rw [ite_eq_left (show n ≠ 0 ∧ m ≠ 0 ∧ mom L n ∈ A ∧ mom L m ∈ A from
            ⟨h.1, hm.1, h.2, hm.2⟩), ite_eq_left hm]
          ring
        · rw [ite_eq_right (show ¬(n ≠ 0 ∧ m ≠ 0 ∧ mom L n ∈ A ∧ mom L m ∈ A) from
            fun h' => hm ⟨h'.2.1, h'.2.2.2⟩), ite_eq_right hm, mul_zero]
      rw [e, tsum_mul_left, hT]
      simp only
      rw [ite_eq_left h]
      rfl
    · have e : (fun m => t (n, m)) = fun _ => 0 := by
        funext m
        simp only [ht]
        rw [ite_eq_right (show ¬(n ≠ 0 ∧ m ≠ 0 ∧ mom L n ∈ A ∧ mom L m ∈ A) from
          fun h' => h ⟨h'.1, h'.2.2.1⟩)]
      rw [e, tsum_zero, hT]
      simp only
      rw [ite_eq_right h]
  have hlat2 : latSum2 L A (fun p q => Vp (p - q) * (gp p / ‖p‖ ^ 2) * (gp q / ‖q‖ ^ 2)) =
      ∑' n, T n := by
    rw [latSum2, ← funext hrow]
    exact htsum.tsum_prod
  -- comparison with the summand of `latSum L A (Ψ w)`
  set H : Idx → ℝ := fun n =>
    if n ≠ 0 ∧ mom L n ∈ A then Ψ (mom L n) * (gp (mom L n) / ‖mom L n‖ ^ 2) else 0 with hHdef
  set ε := K₃ * R with hε
  have hε0 : 0 ≤ ε := by positivity
  have hUH : ∀ n, |(L ^ 3)⁻¹ * T n - H n| ≤ ε * a n := by
    intro n
    simp only [hT, hHdef, ha]
    by_cases h : n ≠ 0 ∧ mom L n ∈ A
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h]
      have hb := (hK₃ (mom L n) L r₁ s r₂ A hL hr₁ hs hr₂ hA hAs).2
      have e : (L ^ 3)⁻¹ * (gp (mom L n) / ‖mom L n‖ ^ 2 * S (mom L n)) -
          Ψ (mom L n) * (gp (mom L n) / ‖mom L n‖ ^ 2) =
          gp (mom L n) / ‖mom L n‖ ^ 2 * ((L ^ 3)⁻¹ * S (mom L n) - Ψ (mom L n)) := by ring
      rw [e, abs_mul, mul_comm ε]
      exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
      simp
  have hUsum : Summable (fun n => (L ^ 3)⁻¹ * T n) := by
    refine Summable.of_norm_bounded (hHsum.abs.add (hasum.mul_left ε)) fun n => ?_
    rw [Real.norm_eq_abs]
    have := hUH n
    have h2 := abs_sub_abs_le_abs_sub ((L ^ 3)⁻¹ * T n) (H n)
    linarith
  have hfirst : |(L ^ 3)⁻¹ * (∑' n, (L ^ 3)⁻¹ * T n) - (L ^ 3)⁻¹ * (∑' n, H n)| ≤
      ε * (K₂ * (200 * C)) := by
    have h := MomentumSums_abs_tsum_sub_le hUsum hHsum (hasum.mul_left ε) hUH
    rw [show ∑' n, ε * a n = ε * ∑' n, a n from tsum_mul_left] at h
    rw [← mul_sub, abs_mul, abs_of_pos hL3]
    calc (L ^ 3)⁻¹ * |(∑' n, (L ^ 3)⁻¹ * T n) - ∑' n, H n| ≤ (L ^ 3)⁻¹ * (ε * ∑' n, a n) :=
          mul_le_mul_of_nonneg_left h hL3.le
      _ = ε * ((L ^ 3)⁻¹ * ∑' n, a n) := by ring
      _ ≤ ε * (K₂ * (200 * C)) := mul_le_mul_of_nonneg_left hasum_le hε0
  -- the main term: `(2π)⁻³ ∫ Ψ w = (2π)⁻⁶ ∫∫ V_{p-q} w_p w_q`
  have hmain : c * ∫ p, Ψ p * (gp p / ‖p‖ ^ 2) = (((2 * π) ^ 3) ^ 2)⁻¹ *
      ∫ p, ∫ q, Vp (p - q) * (gp p / ‖p‖ ^ 2) * (gp q / ‖q‖ ^ 2) := by
    have e : ∀ p : R3, Ψ p * (gp p / ‖p‖ ^ 2) =
        c * ∫ q, Vp (p - q) * (gp p / ‖p‖ ^ 2) * (gp q / ‖q‖ ^ 2) := by
      intro p
      simp only [hΨ]
      rw [show (fun q => Vp (p - q) * (gp p / ‖p‖ ^ 2) * (gp q / ‖q‖ ^ 2)) =
        fun q => gp p / ‖p‖ ^ 2 * (Vp (p - q) * (gp q / ‖q‖ ^ 2)) by funext q; ring,
        integral_const_mul]
      ring
    simp_rw [e]
    rw [integral_const_mul, hc]
    ring
  -- assembly
  have hsplit : ((L ^ 3) ^ 2)⁻¹ * ∑' n, T n = (L ^ 3)⁻¹ * ∑' n, (L ^ 3)⁻¹ * T n := by
    rw [tsum_mul_left]; ring
  rw [hlat2, hsplit, ← hmain]
  have hsecond : |(L ^ 3)⁻¹ * (∑' n, H n) - c * ∫ p, Ψ p * (gp p / ‖p‖ ^ 2)| ≤
      Kf * (200 * C * D) * R := hHbd
  calc |(L ^ 3)⁻¹ * (∑' n, (L ^ 3)⁻¹ * T n) - c * ∫ p, Ψ p * (gp p / ‖p‖ ^ 2)|
      ≤ |(L ^ 3)⁻¹ * (∑' n, (L ^ 3)⁻¹ * T n) - (L ^ 3)⁻¹ * (∑' n, H n)| +
          |(L ^ 3)⁻¹ * (∑' n, H n) - c * ∫ p, Ψ p * (gp p / ‖p‖ ^ 2)| := abs_sub_le _ _ _
    _ ≤ ε * (K₂ * (200 * C)) + Kf * (200 * C * D) * R := add_le_add hfirst hsecond
    _ = (K₃ * K₂ * (200 * C) + Kf * (200 * C * D)) * R := by rw [hε]; ring

/-- `latSum` and `latSummable` over `ℝ³` are the sums over `n ≠ 0`. -/
private lemma MomentumSums_univ (L : ℝ) (G : R3 → ℝ) :
    latSum L Set.univ G = ∑' n : Idx, (if n ≠ 0 then G (mom L n) else 0) ∧
      (latSummable L Set.univ G ↔ Summable fun n : Idx => if n ≠ 0 then G (mom L n) else 0) := by
  exact ⟨by simp only [latSum, Set.mem_univ, and_true],
    by simp only [latSummable, Set.mem_univ, and_true]⟩

/-- Facts (2) and (5) before (7.65) [temp8.73]. -/
theorem sum_lam_V_le {Vp : R3 → ℝ} {C M : ℝ} (hM : 4 ≤ M) (hV : MomDecay Vp C M) (c : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L : ℝ) (lamb : Idx → ℝ), 2 * π ≤ L →
      (∀ n : Idx, n ≠ 0 → |lamb n| ≤ c * ‖mom L n‖ ^ (-2 : ℝ) * (1 + ‖mom L n‖) ^ (-M)) →
      (∀ u : R3,
        Summable (fun n : Idx => if n ≠ 0 then |lamb n * Vp (u - mom L n)| else 0) ∧
        (L ^ 3)⁻¹ * ∑' n : Idx, (if n ≠ 0 then |lamb n * Vp (u - mom L n)| else 0) ≤ K) ∧
      Summable (fun nm : Idx × Idx =>
        if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then |lamb nm.1 * Vp (mom L nm.1 - mom L nm.2) * lamb nm.2|
        else 0) ∧
      ((L ^ 3) ^ 2)⁻¹ * ∑' nm : Idx × Idx,
        (if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then |lamb nm.1 * Vp (mom L nm.1 - mom L nm.2) * lamb nm.2|
         else 0) ≤ K := by
  obtain ⟨K₂, hK₂0, hK₂⟩ := latSum_abs_le (a := 2) (b := 4) (by norm_num) (by norm_num)
    (by norm_num)
  obtain ⟨hC, -, -, hVb, -⟩ := MomentumSums_decay hM hV
  -- the majorant `F(p) = c |p|^{-2} (1 + |p|)^{-M}` of `λ`
  set Fl : R3 → ℝ := fun p => c * ‖p‖ ^ (-2 : ℝ) * (1 + ‖p‖) ^ (-M) with hFl
  have hFlb : ∀ p : R3, p ≠ 0 → |Fl p| ≤ |c| * min (‖p‖ ^ (-(2 : ℝ))) (‖p‖ ^ (-(4 : ℝ))) := by
    intro p hp
    have hx : 0 < ‖p‖ := norm_pos_iff.2 hp
    obtain ⟨hw1, -⟩ := MomentumSums_weight_le (norm_nonneg p) hM
    have e2 : ‖p‖ ^ (-(2 : ℝ)) = (‖p‖ ^ 2)⁻¹ := by simp [Real.rpow_neg hx.le]
    simp only [hFl]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg p) _),
      abs_of_nonneg (Real.rpow_nonneg (by positivity) _), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    refine le_trans ?_ (MomentumSums_min_ge hx).1
    rw [e2, mul_inv]
    refine mul_le_mul_of_nonneg_left (hw1.trans ?_) (by positivity)
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith [norm_nonneg p]) (by norm_num))
  refine ⟨C * (K₂ * |c|) + C * (K₂ * |c|) ^ 2, by positivity, ?_⟩
  intro L lamb hL hlam
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hL3 : 0 < (L ^ 3)⁻¹ := by positivity
  obtain ⟨hsum, hle⟩ := hK₂ |c| Fl L (abs_nonneg c) hL hFlb
  obtain ⟨e1, e2⟩ := MomentumSums_univ L (fun p => |Fl p|)
  set f : Idx → ℝ := fun n => if n ≠ 0 then |Fl (mom L n)| else 0 with hf
  have hfsum : Summable f := e2.1 hsum
  have hf0 : 0 ≤ f := fun n => by simp only [hf]; split_ifs <;> simp
  have hfle : (L ^ 3)⁻¹ * ∑' n, f n ≤ K₂ * |c| := by rw [← e1]; exact hle
  have hfle0 : 0 ≤ (L ^ 3)⁻¹ * ∑' n, f n := mul_nonneg hL3.le (tsum_nonneg hf0)
  -- `[n ≠ 0] |λ_n| ≤ f(n)`
  have hlf : ∀ n : Idx, n ≠ 0 → |lamb n| ≤ f n := by
    intro n hn
    simp only [hf, ne_eq, hn, not_false_eq_true, ite_true]
    exact (hlam n hn).trans (le_abs_self _)
  refine ⟨fun u => ?_, ?_⟩
  · have hb : ∀ n, (if n ≠ 0 then |lamb n * Vp (u - mom L n)| else 0) ≤ C * f n := by
      intro n
      by_cases hn : n ≠ 0
      · rw [ite_eq_left hn, abs_mul, mul_comm C]
        exact mul_le_mul (hlf n hn) (hVb _) (abs_nonneg _) (hf0 n)
      · rw [ite_eq_right hn]
        exact mul_nonneg hC (hf0 n)
    have hs : Summable (fun n : Idx => if n ≠ 0 then |lamb n * Vp (u - mom L n)| else 0) :=
      Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hb (hfsum.mul_left C)
    refine ⟨hs, ?_⟩
    calc (L ^ 3)⁻¹ * ∑' n : Idx, (if n ≠ 0 then |lamb n * Vp (u - mom L n)| else 0)
        ≤ (L ^ 3)⁻¹ * ∑' n, C * f n :=
          mul_le_mul_of_nonneg_left (hs.tsum_le_tsum hb (hfsum.mul_left C)) hL3.le
      _ = C * ((L ^ 3)⁻¹ * ∑' n, f n) := by rw [tsum_mul_left]; ring
      _ ≤ C * (K₂ * |c|) := mul_le_mul_of_nonneg_left hfle hC
      _ ≤ C * (K₂ * |c|) + C * (K₂ * |c|) ^ 2 := by
          have : 0 ≤ C * (K₂ * |c|) ^ 2 := by positivity
          linarith
  · have hb : ∀ nm : Idx × Idx,
        (if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then |lamb nm.1 * Vp (mom L nm.1 - mom L nm.2) * lamb nm.2|
          else 0) ≤ C * (f nm.1 * f nm.2) := by
      intro nm
      by_cases h : nm.1 ≠ 0 ∧ nm.2 ≠ 0
      · rw [ite_eq_left h, abs_mul, abs_mul]
        have h1 := hlf _ h.1
        have h2 := hlf _ h.2
        have h3 := hVb (mom L nm.1 - mom L nm.2)
        calc |lamb nm.1| * |Vp (mom L nm.1 - mom L nm.2)| * |lamb nm.2|
            ≤ f nm.1 * C * f nm.2 :=
              mul_le_mul (mul_le_mul h1 h3 (abs_nonneg _) (hf0 _)) h2 (abs_nonneg _)
                (mul_nonneg (hf0 _) hC)
          _ = C * (f nm.1 * f nm.2) := by ring
      · rw [ite_eq_right h]
        exact mul_nonneg hC (mul_nonneg (hf0 _) (hf0 _))
    have hprod : Summable (fun nm : Idx × Idx => f nm.1 * f nm.2) :=
      hfsum.mul_of_nonneg hfsum hf0 hf0
    have hs : Summable (fun nm : Idx × Idx =>
        if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then |lamb nm.1 * Vp (mom L nm.1 - mom L nm.2) * lamb nm.2|
        else 0) :=
      Summable.of_nonneg_of_le (fun nm => by split_ifs <;> positivity) hb (hprod.mul_left C)
    refine ⟨hs, ?_⟩
    have hnorm : Summable (fun n => ‖f n‖) := by
      simpa [Real.norm_eq_abs] using hfsum.abs
    have hmul := tsum_mul_tsum_of_summable_norm hnorm hnorm
    calc ((L ^ 3) ^ 2)⁻¹ * ∑' nm : Idx × Idx,
          (if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then |lamb nm.1 * Vp (mom L nm.1 - mom L nm.2) * lamb nm.2|
           else 0)
        ≤ ((L ^ 3) ^ 2)⁻¹ * ∑' nm : Idx × Idx, C * (f nm.1 * f nm.2) :=
          mul_le_mul_of_nonneg_left (hs.tsum_le_tsum hb (hprod.mul_left C)) (by positivity)
      _ = C * ((L ^ 3)⁻¹ * ∑' n, f n) ^ 2 := by rw [tsum_mul_left, ← hmul]; ring
      _ ≤ C * (K₂ * |c|) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hfle0 hfle 2) hC
      _ ≤ C * (K₂ * |c|) + C * (K₂ * |c|) ^ 2 := by
          have : 0 ≤ C * (K₂ * |c|) := by positivity
          linarith

end LHYUpper
