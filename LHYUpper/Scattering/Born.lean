module

public import LHYUpper.Scattering.Newton
public import LHYUpper.Scattering.Gaussian

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-- The Born equation `w = G ∗ (V (1 - w))` of the zero-energy scattering problem (§2), for
bounded continuous `w`. -/
def IsBornSolution (V w : R3 → ℝ) : Prop :=
  Continuous w ∧ (∃ M, ∀ x, |w x| ≤ M) ∧ ∀ x, w x = newton (fun y => V y * (1 - w y)) x

/-- A bounded continuous solution of the Born equation, when one exists (it is unique under
the hypotheses of Theorem 2.1 [mainthm]). -/
def bornSol (V : R3 → ℝ) : R3 → ℝ :=
  if h : ∃ w, IsBornSolution V w then Classical.choose h else 0

section
variable {V : R3 → ℝ}

open scoped BoundedContinuousFunction

/-! ### Estimates for the Born operator -/

/-- A potential satisfying `PotentialHyp` is continuous and bounded by `C (1 + |y|)^{-5}`. -/
private lemma born_potential_bound (hV : PotentialHyp V) :
    Continuous V ∧ ∃ C, ∀ y, |V y| ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
  obtain ⟨S, rfl⟩ := hV.schwartz
  refine ⟨S.continuous, 2 ^ 5 * (Finset.Iic ((5, 0) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S, fun y => ?_⟩
  have h : (1 + ‖y‖) ^ 5 * |S y| ≤ 2 ^ 5 * (Finset.Iic ((5, 0) : ℕ × ℕ)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S := by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((5, 0) : ℕ × ℕ))
      (k := 5) (n := 0) le_rfl le_rfl S y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  rw [Real.rpow_neg (by positivity), show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num,
    Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

/-- If `|f| ≤ M` then `|V f| ≤ C (1 + |y|)^{-5}` for some `C`. -/
private lemma born_mul_bound (hV : PotentialHyp V) {f : R3 → ℝ} {M : ℝ} (hM : ∀ y, |f y| ≤ M) :
    ∃ C, ∀ y, |V y * f y| ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
  obtain ⟨-, C, hC⟩ := born_potential_bound hV
  refine ⟨C * M, fun y => ?_⟩
  rw [abs_mul]
  calc |V y| * |f y| ≤ (C * (1 + ‖y‖) ^ (-(5 : ℝ))) * M :=
        mul_le_mul (hC y) (hM y) (abs_nonneg _) ((abs_nonneg _).trans (hC y))
    _ = _ := by ring

/-- The constant of the smallness condition: `0 ≤ c < 1` and `G ∗ V ≤ c`. -/
private lemma born_const (hV : PotentialHyp V) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ x, newton V x ≤ c := by
  obtain ⟨c, hc1, hc⟩ := hV.born
  refine ⟨c, le_trans (integral_nonneg fun y => div_nonneg (hV.nonneg y) (by positivity))
    (hc 0), hc1, hc⟩

private lemma born_V_integrable (hV : PotentialHyp V) (x : R3) :
    Integrable (fun y => V y / (4 * π * ‖x - y‖)) := by
  obtain ⟨hVc, C, hC⟩ := born_potential_bound hV
  exact newton_integrable (by norm_num) hVc hC x

private lemma born_integrable (hV : PotentialHyp V) {f : R3 → ℝ} {M : ℝ} (hf : Continuous f)
    (hM : ∀ y, |f y| ≤ M) (x : R3) :
    Integrable (fun y => V y * f y / (4 * π * ‖x - y‖)) := by
  obtain ⟨hVc, -⟩ := born_potential_bound hV
  obtain ⟨C, hC⟩ := born_mul_bound hV hM
  exact newton_integrable (by norm_num) (hVc.mul hf) hC x

private lemma born_continuous (hV : PotentialHyp V) {f : R3 → ℝ} {M : ℝ} (hf : Continuous f)
    (hM : ∀ y, |f y| ≤ M) : Continuous (newton fun y => V y * f y) := by
  obtain ⟨hVc, -⟩ := born_potential_bound hV
  obtain ⟨C, hC⟩ := born_mul_bound hV hM
  exact newton_continuous (by norm_num) (hVc.mul hf) hC

/-- `|G ∗ (V f)| ≤ c M` when `|f| ≤ M` and `G ∗ V ≤ c`. -/
private lemma born_abs_le (hV : PotentialHyp V) {c : ℝ} (hc : ∀ x, newton V x ≤ c)
    {f : R3 → ℝ} {M : ℝ} (hM : ∀ y, |f y| ≤ M) (x : R3) :
    |newton (fun y => V y * f y) x| ≤ c * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [newton, ← Real.norm_eq_abs]
  calc ‖∫ y, V y * f y / (4 * π * ‖x - y‖)‖ ≤ ∫ y, M * (V y / (4 * π * ‖x - y‖)) := by
        refine norm_integral_le_of_norm_le ((born_V_integrable hV x).const_mul M)
          (Eventually.of_forall fun y => ?_)
        have hVy := hV.nonneg y
        rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hVy,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * π * ‖x - y‖)]
        calc V y * |f y| / (4 * π * ‖x - y‖) ≤ V y * M / (4 * π * ‖x - y‖) := by
              gcongr; exact hM y
          _ = M * (V y / (4 * π * ‖x - y‖)) := by ring
    _ = M * newton V x := by rw [integral_const_mul]; rfl
    _ ≤ M * c := mul_le_mul_of_nonneg_left (hc x) hM0
    _ = c * M := mul_comm _ _

/-- Linearity of `f ↦ G ∗ (V f)` on bounded continuous functions. -/
private lemma born_newton_sub (hV : PotentialHyp V) {f g : R3 → ℝ} {Mf Mg : ℝ}
    (hf : Continuous f) (hg : Continuous g) (hMf : ∀ y, |f y| ≤ Mf) (hMg : ∀ y, |g y| ≤ Mg)
    (x : R3) :
    newton (fun y => V y * f y) x - newton (fun y => V y * g y) x =
      newton (fun y => V y * (f y - g y)) x := by
  rw [newton, newton, newton, ← integral_sub (born_integrable hV hf hMf x)
    (born_integrable hV hg hMg x)]
  congr 1
  ext y
  ring

/-- `|G ∗ (V f) - G ∗ (V g)| ≤ c M` when `|f - g| ≤ M` and `G ∗ V ≤ c`. -/
private lemma born_diff_le (hV : PotentialHyp V) {c : ℝ} (hc : ∀ x, newton V x ≤ c)
    {f g : R3 → ℝ} {Mf Mg M : ℝ} (hf : Continuous f) (hg : Continuous g)
    (hMf : ∀ y, |f y| ≤ Mf) (hMg : ∀ y, |g y| ≤ Mg) (hM : ∀ y, |f y - g y| ≤ M) (x : R3) :
    |newton (fun y => V y * f y) x - newton (fun y => V y * g y) x| ≤ c * M := by
  rw [born_newton_sub hV hf hg hMf hMg x]
  exact born_abs_le hV hc hM x

private lemma born_one_sub_le (b : R3 →ᵇ ℝ) (y : R3) : |1 - b y| ≤ 1 + ‖b‖ := by
  have h := b.norm_coe_le_norm y
  rw [Real.norm_eq_abs] at h
  calc |1 - b y| ≤ |(1 : ℝ)| + |b y| := abs_sub _ _
    _ ≤ 1 + ‖b‖ := by rw [abs_one]; linarith

/-- The Born operator `b ↦ G ∗ (V (1 - b))` on bounded continuous functions. -/
private lemma born_op (hV : PotentialHyp V) :
    ∃ Φ : (R3 →ᵇ ℝ) → (R3 →ᵇ ℝ), ∀ b x, Φ b x = newton (fun y => V y * (1 - b y)) x := by
  obtain ⟨c, hc0, hc1, hc⟩ := born_const hV
  have : ∀ b : R3 →ᵇ ℝ, ∃ f : R3 →ᵇ ℝ, ∀ x, f x = newton (fun y => V y * (1 - b y)) x := by
    intro b
    have hbc : Continuous fun y => 1 - b y := continuous_const.sub b.continuous
    refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup
      (newton fun y => V y * (1 - b y)) (born_continuous hV hbc (born_one_sub_le b))
      (c * (1 + ‖b‖)) fun x => ?_, fun x => rfl⟩
    rw [Real.norm_eq_abs]
    exact born_abs_le hV hc (born_one_sub_le b) x
  choose Φ hΦ using this
  exact ⟨Φ, hΦ⟩

/-- The set `0 ≤ b ≤ c` is invariant under the Born operator. -/
private lemma born_invariant (hV : PotentialHyp V) {c : ℝ} (hc : ∀ x, newton V x ≤ c)
    (hc1 : c ≤ 1) {b : R3 → ℝ} (hb : ∀ x, 0 ≤ b x ∧ b x ≤ c) (x : R3) :
    0 ≤ newton (fun y => V y * (1 - b y)) x ∧ newton (fun y => V y * (1 - b y)) x ≤ c := by
  have hb1 : ∀ y, b y ≤ 1 := fun y => (hb y).2.trans hc1
  refine ⟨integral_nonneg fun y => div_nonneg (mul_nonneg (hV.nonneg y) (by linarith [hb1 y]))
    (by positivity), ?_⟩
  refine le_trans ?_ (hc x)
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => ?_) (born_V_integrable hV x)
    (Eventually.of_forall fun y => ?_)
  · exact div_nonneg (mul_nonneg (hV.nonneg y) (by linarith [hb1 y])) (by positivity)
  · have h1 := hV.nonneg y
    have h2 := (hb y).1
    change V y * (1 - b y) / (4 * π * ‖x - y‖) ≤ V y / (4 * π * ‖x - y‖)
    gcongr
    nlinarith

private lemma born_exists_aux (hV : PotentialHyp V) :
    ∃ c : ℝ, c < 1 ∧ ∃ w, IsBornSolution V w ∧ (∀ x, 0 ≤ w x) ∧ ∀ x, w x ≤ c := by
  obtain ⟨c, hc0, hc1, hc⟩ := born_const hV
  obtain ⟨Φ, hΦ⟩ := born_op hV
  have hcon : ContractingWith c.toNNReal Φ := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun b b' => ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal c hc0]
      exact_mod_cast hc1
    · rw [Real.coe_toNNReal c hc0]
      refine (BoundedContinuousFunction.dist_le (mul_nonneg hc0 dist_nonneg)).2 fun x => ?_
      rw [Real.dist_eq, hΦ, hΦ]
      refine born_diff_le hV hc (f := fun y => 1 - b y) (g := fun y => 1 - b' y)
        (Mf := 1 + ‖b‖) (Mg := 1 + ‖b'‖) (continuous_const.sub b.continuous)
        (continuous_const.sub b'.continuous)
        (born_one_sub_le b) (born_one_sub_le b') (fun y => ?_) x
      have := BoundedContinuousFunction.dist_coe_le_dist (f := b) (g := b') y
      rw [Real.dist_eq] at this
      change |(1 - b y) - (1 - b' y)| ≤ dist b b'
      rw [show (1 - b y) - (1 - b' y) = -(b y - b' y) by ring, abs_neg]
      exact this
  have hfix : Φ (ContractingWith.fixedPoint Φ hcon) = ContractingWith.fixedPoint Φ hcon :=
    hcon.fixedPoint_isFixedPt
  set w := ContractingWith.fixedPoint Φ hcon with hw
  have hiter : ∀ n : ℕ, ∀ x, 0 ≤ (Φ^[n] 0) x ∧ (Φ^[n] 0) x ≤ c := by
    intro n
    induction n with
    | zero => intro x; simpa using hc0
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply', hΦ]
      exact born_invariant hV hc hc1.le ih x
  have hlim := hcon.tendsto_iterate_fixedPoint (0 : R3 →ᵇ ℝ)
  have hev : ∀ x, Tendsto (fun n : ℕ => (Φ^[n] 0) x) atTop (𝓝 (w x)) := fun x =>
    ((continuous_apply x).comp BoundedContinuousFunction.continuous_coe).continuousAt.tendsto.comp
      hlim
  refine ⟨c, hc1, w, ⟨w.continuous, ⟨‖w‖, fun x => ?_⟩, fun x => ?_⟩,
    fun x => ge_of_tendsto' (hev x) fun n => (hiter n x).1,
    fun x => le_of_tendsto' (hev x) fun n => (hiter n x).2⟩
  · have := w.norm_coe_le_norm x
    rwa [Real.norm_eq_abs] at this
  · rw [← hΦ, hfix]

/-- Under the smallness condition of Theorem 2.1 [mainthm], `h ↦ G ∗ (V (1 - h))` is a
contraction on bounded continuous functions, so the Born equation has a solution. -/
theorem born_exists (hV : PotentialHyp V) : ∃ w, IsBornSolution V w := by
  obtain ⟨_, _, w, hw, _⟩ := born_exists_aux hV
  exact ⟨w, hw⟩

/-- The bounded continuous solution of the Born equation is unique. -/
theorem born_unique (hV : PotentialHyp V) {w w' : R3 → ℝ} (hw : IsBornSolution V w)
    (hw' : IsBornSolution V w') : w = w' := by
  obtain ⟨c, hc0, hc1, hc⟩ := born_const hV
  obtain ⟨hwc, ⟨M₁, hM₁⟩, hwe⟩ := hw
  obtain ⟨hwc', ⟨M₂, hM₂⟩, hwe'⟩ := hw'
  have hb1 : ∀ y, |1 - w y| ≤ 1 + M₁ := fun y =>
    (abs_sub _ _).trans (by rw [abs_one]; linarith [hM₁ y])
  have hb2 : ∀ y, |1 - w' y| ≤ 1 + M₂ := fun y =>
    (abs_sub _ _).trans (by rw [abs_one]; linarith [hM₂ y])
  have key : ∀ n : ℕ, ∀ x, |w x - w' x| ≤ c ^ n * (M₁ + M₂) := by
    intro n
    induction n with
    | zero =>
      intro x
      simpa using (abs_sub _ _).trans (add_le_add (hM₁ x) (hM₂ x))
    | succ n ih =>
      intro x
      rw [hwe x, hwe' x, pow_succ, mul_comm (c ^ n) c, mul_assoc]
      exact born_diff_le hV hc (f := fun y => 1 - w y) (g := fun y => 1 - w' y)
        (continuous_const.sub hwc) (continuous_const.sub hwc') hb1 hb2
        (fun y => by
          rw [show (1 - w y) - (1 - w' y) = -(w y - w' y) by ring, abs_neg]
          exact ih y) x
  funext x
  have hlim : Tendsto (fun n : ℕ => c ^ n * (M₁ + M₂)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const (M₁ + M₂)
  have h0 : |w x - w' x| ≤ 0 := ge_of_tendsto' hlim fun n => key n x
  linarith [abs_nonpos_iff.1 h0]

theorem bornSol_isBornSolution (hV : PotentialHyp V) : IsBornSolution V (bornSol V) := by
  have h : ∃ w, IsBornSolution V w := born_exists hV
  have h' : bornSol V = Classical.choose h := by
    simp only [bornSol, h, ↓reduceDIte]
  rw [h']
  exact Classical.choose_spec h

theorem bornSol_nonneg (hV : PotentialHyp V) : ∀ x, 0 ≤ bornSol V x := by
  obtain ⟨_, _, w, hw, h0, _⟩ := born_exists_aux hV
  rw [born_unique hV (bornSol_isBornSolution hV) hw]
  exact h0

/-- `w < 1` uniformly: `w ≤ c` with `c < 1` the constant of the smallness condition. -/
theorem bornSol_lt_one (hV : PotentialHyp V) : ∃ c < 1, ∀ x, bornSol V x ≤ c := by
  obtain ⟨c, hc1, w, hw, _, hc⟩ := born_exists_aux hV
  rw [born_unique hV (bornSol_isBornSolution hV) hw]
  exact ⟨c, hc1, hc⟩

theorem bornSol_tendsto (hV : PotentialHyp V) : Tendsto (bornSol V) (cocompact R3) (𝓝 0) := by
  obtain ⟨hwc, ⟨M, hM⟩, hwe⟩ := bornSol_isBornSolution hV
  obtain ⟨hVc, -⟩ := born_potential_bound hV
  have hbd : ∀ y, |1 - bornSol V y| ≤ 1 + M := fun y =>
    (abs_sub _ _).trans (by rw [abs_one]; linarith [hM y])
  obtain ⟨C, hC⟩ := born_mul_bound hV hbd
  obtain ⟨C', hC'⟩ := newton_decay (by norm_num : (4 : ℝ) < 5)
    (hVc.mul (continuous_const.sub hwc)) hC
  refine squeeze_zero_norm (a := fun x => C' / (1 + ‖x‖)) (fun x => ?_) ?_
  · rw [Real.norm_eq_abs, hwe x]
    exact hC' x
  · exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ 1 tendsto_norm_cocompact_atTop)

/-- `G ∗ (h ∘ (-·))` evaluated at `x` is `G ∗ h` evaluated at `-x`. -/
private lemma born_newton_neg (h : R3 → ℝ) (x : R3) :
    newton (fun y => h (-y)) x = newton h (-x) := by
  rw [newton, newton, ← integral_neg_eq_self (fun y => h y / (4 * π * ‖-x - y‖)) volume]
  congr 1
  ext y
  rw [show -x - -y = -(x - y) by abel, norm_neg]

theorem bornSol_even (hV : PotentialHyp V) : ∀ x, bornSol V (-x) = bornSol V x := by
  obtain ⟨hwc, ⟨M, hM⟩, hwe⟩ := bornSol_isBornSolution hV
  have hw' : IsBornSolution V (fun x => bornSol V (-x)) := by
    refine ⟨hwc.comp continuous_neg, ⟨M, fun x => hM (-x)⟩, fun x => ?_⟩
    change bornSol V (-x) = newton (fun y => V y * (1 - bornSol V (-y))) x
    rw [hwe (-x), ← born_newton_neg]
    congr 1
    ext y
    rw [hV.even]
  intro x
  exact congr_fun (born_unique hV hw' (bornSol_isBornSolution hV)) x

end

end LHYUpper
