module

public import LHYUpper.TrialState.FIdentities

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

section Normalization

/-! ### Lattice sum `Σ_{n ∈ ℤ³ ∖ 0} |n|^{-4} < ∞` -/

/-- One-dimensional factor `(1 + k²)^{-2/3}` of the lattice majorant. -/
private def Normalization_h (k : ℤ) : ℝ := ((1 + (k : ℝ) ^ 2) ^ (2/3 : ℝ))⁻¹

private lemma Normalization_h_nonneg (k : ℤ) : 0 ≤ Normalization_h k := by
  unfold Normalization_h
  positivity

private lemma Normalization_h_summable : Summable Normalization_h := by
  refine Summable.of_norm_bounded_eventually
    (Real.summable_abs_int_rpow (b := 4/3) (by norm_num)) ?_
  have : ∀ᶠ k : ℤ in cofinite, k ≠ 0 := eventually_cofinite_ne 0
  filter_upwards [this] with k hk
  rw [Real.norm_of_nonneg (Normalization_h_nonneg k), Normalization_h]
  have hk' : (0 : ℝ) < |(k : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast hk
  rw [Real.rpow_neg hk'.le]
  apply inv_anti₀ (by positivity)
  have h1 : |(k : ℝ)| ^ (4/3 : ℝ) = ((k : ℝ) ^ 2) ^ (2/3 : ℝ) := by
    rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
    norm_num
  rw [h1]
  exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)

/-- The lattice majorant `∏_i (1 + n_i²)^{-2/3}`. -/
private def Normalization_H (n : Idx) : ℝ :=
  Normalization_h (n 0) * Normalization_h (n 1) * Normalization_h (n 2)

private lemma Normalization_H_nonneg (n : Idx) : 0 ≤ Normalization_H n := by
  unfold Normalization_H
  exact mul_nonneg (mul_nonneg (Normalization_h_nonneg _) (Normalization_h_nonneg _))
    (Normalization_h_nonneg _)

private lemma Normalization_H_summable : Summable Normalization_H := by
  let e : ℤ × ℤ × ℤ ≃ Idx :=
    { toFun := fun p => ![p.1, p.2.1, p.2.2]
      invFun := fun n => (n 0, n 1, n 2)
      left_inv := fun p => rfl
      right_inv := fun n => by
        funext i
        fin_cases i <;> rfl }
  rw [← e.summable_iff]
  have h2 := Summable.mul_of_nonneg Normalization_h_summable Normalization_h_summable
    (fun k => Normalization_h_nonneg k) (fun k => Normalization_h_nonneg k)
  have h3 := Summable.mul_of_nonneg Normalization_h_summable h2
    (fun k => Normalization_h_nonneg k) (fun p => mul_nonneg (Normalization_h_nonneg _)
      (Normalization_h_nonneg _))
  refine h3.congr fun p => ?_
  simp only [Function.comp, Normalization_H, mul_assoc]
  rfl

/-- `|n|²` for `n ∈ ℤ³`. -/
private def Normalization_S (n : Idx) : ℝ := ∑ i, ((n i : ℤ) : ℝ) ^ 2

private lemma Normalization_S_ge_one {n : Idx} (hn : n ≠ 0) : 1 ≤ Normalization_S n := by
  have : ∃ i, n i ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  obtain ⟨i, hi⟩ := this
  have h1 : (1 : ℝ) ≤ ((n i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (n i) ^ 2 := by
      have := sq_pos_of_ne_zero hi
      omega
    exact_mod_cast this
  calc (1 : ℝ) ≤ ((n i : ℤ) : ℝ) ^ 2 := h1
    _ ≤ Normalization_S n :=
      Finset.single_le_sum (f := fun j => ((n j : ℤ) : ℝ) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)

private lemma Normalization_S_inv_le {n : Idx} (hn : n ≠ 0) :
    (Normalization_S n ^ 2)⁻¹ ≤ 4 * Normalization_H n := by
  have hS := Normalization_S_ge_one hn
  set S := Normalization_S n with hSdef
  have hS3 : S = (n 0 : ℝ) ^ 2 + (n 1 : ℝ) ^ 2 + (n 2 : ℝ) ^ 2 := by
    simp [hSdef, Normalization_S, Fin.sum_univ_three]
  have hP : (1 + (n 0 : ℝ) ^ 2) * (1 + (n 1 : ℝ) ^ 2) * (1 + (n 2 : ℝ) ^ 2) ≤ (1 + S) ^ 3 := by
    have a0 : 1 + (n 0 : ℝ) ^ 2 ≤ 1 + S := by nlinarith [sq_nonneg (n 1 : ℝ), sq_nonneg (n 2 : ℝ)]
    have a1 : 1 + (n 1 : ℝ) ^ 2 ≤ 1 + S := by nlinarith [sq_nonneg (n 0 : ℝ), sq_nonneg (n 2 : ℝ)]
    have a2 : 1 + (n 2 : ℝ) ^ 2 ≤ 1 + S := by nlinarith [sq_nonneg (n 0 : ℝ), sq_nonneg (n 1 : ℝ)]
    calc (1 + (n 0 : ℝ) ^ 2) * (1 + (n 1 : ℝ) ^ 2) * (1 + (n 2 : ℝ) ^ 2)
        ≤ (1 + S) * (1 + S) * (1 + S) := by
          gcongr
      _ = (1 + S) ^ 3 := by ring
  have hH : Normalization_H n =
      (((1 + (n 0 : ℝ) ^ 2) * (1 + (n 1 : ℝ) ^ 2) * (1 + (n 2 : ℝ) ^ 2)) ^ (2/3 : ℝ))⁻¹ := by
    simp only [Normalization_H, Normalization_h]
    rw [Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      mul_inv, mul_inv]
  have h13 : ((1 + S) ^ 3) ^ (2/3 : ℝ) = (1 + S) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hle : ((1 + (n 0 : ℝ) ^ 2) * (1 + (n 1 : ℝ) ^ 2) * (1 + (n 2 : ℝ) ^ 2)) ^ (2/3 : ℝ) ≤
      (1 + S) ^ 2 := by
    rw [← h13]
    exact Real.rpow_le_rpow (by positivity) hP (by norm_num)
  rw [hH]
  have h4 : (S ^ 2)⁻¹ ≤ 4 * ((1 + S) ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
      div_le_iff₀ (by positivity)]
    nlinarith
  calc (S ^ 2)⁻¹ ≤ 4 * ((1 + S) ^ 2)⁻¹ := h4
    _ ≤ _ := by
      gcongr

/-! ### Momenta outside a box, and the bound on `λ_k` there -/

private lemma Normalization_mom_apply (L : ℝ) (n : Idx) (i : Fin 3) :
    (mom L n).ofLp i = 2 * π / L * (n i : ℝ) := rfl

private lemma Normalization_norm_mom_sq (L : ℝ) (n : Idx) :
    ‖mom L n‖ ^ 2 = (2 * π / L) ^ 2 * Normalization_S n := by
  rw [EuclideanSpace.norm_sq_eq, Normalization_S, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Normalization_mom_apply, Real.norm_eq_abs, sq_abs, mul_pow]

/-- The box `[-b, b]³ ⊂ ℤ³`. -/
private def Normalization_box (b : ℤ) : Finset Idx :=
  Fintype.piFinset fun _ => Finset.Icc (-b) b

private lemma Normalization_box_neg {b : ℤ} {n : Idx} :
    -n ∈ Normalization_box b ↔ n ∈ Normalization_box b := by
  simp only [Normalization_box, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply]
  constructor
  · intro h i
    have := h i
    omega
  · intro h i
    have := h i
    omega

private lemma Normalization_zero_mem_box {b : ℤ} (hb : 0 ≤ b) :
    (0 : Idx) ∈ Normalization_box b := by
  simp only [Normalization_box, Fintype.mem_piFinset, Finset.mem_Icc, Pi.zero_apply]
  intro i
  omega

private lemma Normalization_far {L R : ℝ} (hL : 0 < L) {b : ℤ} (hb : R * L / (2 * π) ≤ b)
    {n : Idx} (hn : n ∉ Normalization_box b) : R < ‖mom L n‖ := by
  simp only [Normalization_box, Fintype.mem_piFinset, Finset.mem_Icc, not_forall] at hn
  obtain ⟨i, hi⟩ := hn
  have h1 : (b : ℝ) < |(n i : ℝ)| := by
    have : b < |n i| := by
      rw [lt_abs]
      omega
    exact_mod_cast this
  have h2 : |(mom L n).ofLp i| ≤ ‖mom L n‖ := by
    have := PiLp.norm_apply_le (mom L n) i
    rwa [Real.norm_eq_abs] at this
  have hc : (0 : ℝ) < 2 * π / L := by positivity
  rw [Normalization_mom_apply, abs_mul, abs_of_pos hc] at h2
  have h3 : R ≤ 2 * π / L * b := by
    rw [div_le_iff₀ (by positivity)] at hb
    rw [div_mul_eq_mul_div, le_div_iff₀ hL]
    linarith
  have h4 : 2 * π / L * b < 2 * π / L * |(n i : ℝ)| := mul_lt_mul_of_pos_left h1 hc
  linarith

/-- `|W_p| ≤ ∫ |W|` for every real `W` (§2). -/
private lemma Normalization_ft_le (W : R3 → ℝ) (p : R3) : ‖ft W p‖ ≤ ∫ x, |W x| := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have : -(Complex.I * ((inner ℝ p x : ℝ) : ℂ)) = ((-(inner ℝ p x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [this, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Off `P_L`, `λ_k² ≤ (∫|g|)² / |k|⁴` by (3.15) [lambda]. -/
private lemma Normalization_lam_sq_le (V w : R3 → ℝ) {ρ L : ℝ} {n : Idx} (hn : ¬ inPL ρ L n) :
    lam V w ρ L n ^ 2 ≤ (∫ x, |gfun V w x|) ^ 2 / (‖mom L n‖ ^ 2) ^ 2 := by
  simp only [lam, hn, ↓reduceIte]
  rw [div_pow, neg_sq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have h1 := (Complex.abs_re_le_norm (ft (gfun V w) (mom L n))).trans
    (Normalization_ft_le (gfun V w) (mom L n))
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

/-- `n ∈ ℤ³` lies in the half-space whose first nonzero coordinate is positive. -/
private def Normalization_half (n : Idx) : Prop :=
  0 < n 0 ∨ (n 0 = 0 ∧ (0 < n 1 ∨ (n 1 = 0 ∧ 0 < n 2)))

private lemma Normalization_half_neg {n : Idx} (hn : n ≠ 0) :
    Normalization_half (-n) ↔ ¬ Normalization_half n := by
  have : n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hn
    funext i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  simp only [Normalization_half, Pi.neg_apply]
  omega

/-- The weight `z_n` of the regrouping: `L³` at `0`, `|λ_n|` in the box, `λ_n²` on the
half-space outside the box, and `0` elsewhere. -/
private def Normalization_z (V w : R3 → ℝ) (ρ L : ℝ) (b : ℤ) (n : Idx) : ℝ :=
  if n = 0 then L ^ 3 else if n ∈ Normalization_box b then |lam V w ρ L n|
  else if Normalization_half n then lam V w ρ L n ^ 2 else 0

private lemma Normalization_z_nonneg (V w : R3 → ℝ) (ρ : ℝ) {L : ℝ} (hL : 0 < L) (b : ℤ)
    (n : Idx) : 0 ≤ Normalization_z V w ρ L b n := by
  unfold Normalization_z
  split_ifs <;> positivity

/-- `τ = ε⁻¹ ρ^{1/2}`, the upper edge of `P_L` in Definition 3.1 [def1]. -/
private def Normalization_tau (ρ : ℝ) : ℝ := (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ)

private lemma Normalization_far_notPL {ρ L kc : ℝ} {n : Idx}
    (hn : max kc (Normalization_tau ρ) < ‖mom L n‖) : ¬ inPL ρ L n := by
  intro h
  have h1 := (le_max_right kc (Normalization_tau ρ)).trans_lt hn
  unfold Normalization_tau at h1
  linarith [h.2]

private lemma Normalization_z_summable (V w : R3 → ℝ) {ρ L kc : ℝ} (hL : 0 < L) {b : ℤ}
    (hb0 : 0 ≤ b) (hb : max kc (Normalization_tau ρ) * L / (2 * π) ≤ b) :
    Summable (Normalization_z V w ρ L b) := by
  set C := (∫ x, |gfun V w x|) ^ 2 / (2 * π / L) ^ 4 * 4
  have hC : 0 ≤ C := by positivity
  have h1 : Summable fun n : Idx =>
      if n ∈ Normalization_box b then L ^ 3 + |lam V w ρ L n| else 0 :=
    summable_of_ne_finset_zero (s := Normalization_box b) fun n hn => by simp [hn]
  refine Summable.of_nonneg_of_le (Normalization_z_nonneg V w ρ hL b) (fun n => ?_)
    (h1.add (Normalization_H_summable.mul_left C))
  have hH := Normalization_H_nonneg n
  by_cases hn : n ∈ Normalization_box b
  · simp only [Normalization_z, hn, ↓reduceIte]
    have : 0 ≤ C * Normalization_H n := mul_nonneg hC hH
    split_ifs <;> nlinarith [abs_nonneg (lam V w ρ L n), pow_pos hL 3]
  · have hn0 : n ≠ 0 := fun h => hn (h ▸ Normalization_zero_mem_box hb0)
    have hfar := Normalization_far hL hb hn
    have hlam := Normalization_lam_sq_le V w (Normalization_far_notPL hfar)
    rw [Normalization_norm_mom_sq] at hlam
    have hS := Normalization_S_inv_le hn0
    have hS1 := Normalization_S_ge_one hn0
    have hlam' : lam V w ρ L n ^ 2 ≤ C * Normalization_H n := by
      refine hlam.trans ?_
      rw [mul_pow, div_le_iff₀ (by positivity)]
      have : (∫ x, |gfun V w x|) ^ 2 =
          (∫ x, |gfun V w x|) ^ 2 / (2 * π / L) ^ 4 * ((2 * π / L) ^ 2) ^ 2 := by
        field_simp
      calc (∫ x, |gfun V w x|) ^ 2
          = (∫ x, |gfun V w x|) ^ 2 / (2 * π / L) ^ 4 * ((2 * π / L) ^ 2) ^ 2 *
              ((Normalization_S n ^ 2)⁻¹ * Normalization_S n ^ 2) := by
            rw [inv_mul_cancel₀ (by positivity), mul_one, ← this]
        _ ≤ (∫ x, |gfun V w x|) ^ 2 / (2 * π / L) ^ 4 * ((2 * π / L) ^ 2) ^ 2 *
              ((4 * Normalization_H n) * Normalization_S n ^ 2) := by
            gcongr
        _ = C * Normalization_H n * (((2 * π / L) ^ 2) ^ 2 * Normalization_S n ^ 2) := by
            ring
    simp only [Normalization_z, hn0, hn, ↓reduceIte, zero_add]
    split_ifs
    · exact hlam'
    · exact mul_nonneg hC hH

/-! ### Regrouping: a bound uniform in the finite set of occupations -/

private lemma Normalization_geom_le {x Z : ℝ} (hx : 0 ≤ x) (hxZ : x ≤ Z) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), x ^ k ≤ Real.exp (N * max 1 Z ^ N * x) := by
  have hM : 1 ≤ max 1 Z := le_max_left _ _
  have hxM : x ≤ max 1 Z := hxZ.trans (le_max_right _ _)
  have h1 : ∀ k ∈ Finset.range N, x ^ (k + 1) ≤ max 1 Z ^ N * x := by
    intro k hk
    rw [pow_succ]
    apply mul_le_mul_of_nonneg_right _ hx
    calc x ^ k ≤ max 1 Z ^ k := pow_le_pow_left₀ hx hxM k
      _ ≤ max 1 Z ^ N := pow_le_pow_right₀ hM (Finset.mem_range.1 hk).le
  rw [Finset.sum_range_succ', pow_zero]
  calc ∑ k ∈ Finset.range N, x ^ (k + 1) + 1
      ≤ ∑ k ∈ Finset.range N, max 1 Z ^ N * x + 1 := by
        have := Finset.sum_le_sum h1
        linarith
    _ = N * max 1 Z ^ N * x + 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ Real.exp (N * max 1 Z ^ N * x) := Real.add_one_le_exp _

/-- For nonnegative summable weights `z`, the sum of `∏_{n ∈ T} z_n^{β(n)}` over any finite set
of occupations `β` supported in `T` with all `β(n) ≤ N` is bounded independently of the set. -/
private lemma Normalization_regroup {z : Idx → ℝ} (hz : ∀ n, 0 ≤ z n) (hs : Summable z)
    (N : ℕ) (u : Finset Occ) (T : Finset Idx) (hu : ∀ β ∈ u, β.support ⊆ T)
    (hN : ∀ β ∈ u, ∀ n, β n ≤ N) :
    ∑ β ∈ u, ∏ n ∈ T, z n ^ (β n) ≤ Real.exp (N * max 1 (∑' n, z n) ^ N * ∑' n, z n) := by
  set Z := ∑' n, z n
  set E := (N : ℝ) * max 1 Z ^ N
  have hE : 0 ≤ E := by positivity
  let g : Occ → ((a : Idx) → a ∈ T → ℕ) := fun β a _ => β a
  have hinj : Set.InjOn g u := by
    intro β hβ β' hβ' h
    ext n
    by_cases hn : n ∈ T
    · exact congrFun (congrFun h n) hn
    · rw [Finsupp.notMem_support_iff.1 (fun h' => hn (hu β hβ h')),
        Finsupp.notMem_support_iff.1 (fun h' => hn (hu β' hβ' h'))]
  have hsub : u.image g ⊆ T.pi (fun _ => Finset.range (N + 1)) := by
    intro p hp
    obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hp
    rw [Finset.mem_pi]
    intro a _
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (hN β hβ a))
  calc ∑ β ∈ u, ∏ n ∈ T, z n ^ (β n)
      = ∑ β ∈ u, ∏ x ∈ T.attach, z x ^ (g β x.1 x.2) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        exact (Finset.prod_attach T (fun n => z n ^ (β n))).symm
    _ = ∑ p ∈ u.image g, ∏ x ∈ T.attach, z x ^ (p x.1 x.2) := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ p ∈ T.pi (fun _ => Finset.range (N + 1)), ∏ x ∈ T.attach, z x ^ (p x.1 x.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
          Finset.prod_nonneg fun x _ => pow_nonneg (hz _) _
    _ = ∏ n ∈ T, ∑ k ∈ Finset.range (N + 1), z n ^ k := by
        rw [Finset.prod_sum]
    _ ≤ ∏ n ∈ T, Real.exp (E * z n) :=
        Finset.prod_le_prod₀ (fun n _ => Finset.sum_nonneg fun k _ => pow_nonneg (hz n) k)
          fun n _ => Normalization_geom_le (hz n) (hs.le_tsum n fun j _ => hz j) N
    _ = Real.exp (E * ∑ n ∈ T, z n) := by rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ Real.exp (E * Z) := by
        gcongr
        exact hs.sum_le_tsum T (fun i _ => hz i)

/-! ### The bound on `|f(α)|²` for `α ∈ M` -/

private lemma Normalization_csqrt_norm_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  rw [sq, ← norm_mul, Regions_csqrt_mul_self, Complex.norm_real, Real.norm_eq_abs]

/-- `|f(α)|² / C_N²` written out from (3.18) [deffal]. -/
private lemma Normalization_norm_f0_sq (V w : R3 → ℝ) (ρ : ℝ) {L : ℝ} (hL : 0 < L) (α : Occ) :
    ‖f0 V w ρ L α‖ ^ 2 = (L ^ 3) ^ (α 0) / (Nat.factorial (α 0)) *
      (∏ n ∈ α.support.filter (· ≠ 0), |lam V w ρ L n| ^ (α n)) *
      ∏ u ∈ (α.support.image Neg.neg).filter (fun u => inPL ρ L u ∧ alphaStar α u = α u + 1),
        |4 * (alphaStar α u : ℝ) * lam V w ρ L u / L ^ 3| := by
  unfold f0
  rw [norm_mul, norm_mul, mul_pow, mul_pow, norm_prod, norm_prod, ← Finset.prod_pow,
    ← Finset.prod_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  congr 2
  · refine Finset.prod_congr rfl fun n _ => ?_
    rw [norm_pow, pow_right_comm, Normalization_csqrt_norm_sq]
  · funext u
    exact Normalization_csqrt_norm_sq _

/-- The momenta kept by the regrouping: the box and the half-space. -/
private def Normalization_P (b : ℤ) (n : Idx) : Prop :=
  n ∈ Normalization_box b ∨ Normalization_half n

/-- `α(n) = α(-n)` for `α ∈ M` and `|n| > max(k_c, ε⁻¹ρ^{1/2})`, by Definition 3.4 [M]. -/
private lemma Normalization_far_symm {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {α : Occ}
    (hα : InM ρ L kc N α) {n : Idx} (hn : max kc (Normalization_tau ρ) < ‖mom L n‖) :
    α n = α (-n) := by
  have h1 := (le_max_right kc (Normalization_tau ρ)).trans_lt hn
  have h2 := (le_max_left kc (Normalization_tau ρ)).trans_lt hn
  by_cases h : ‖mom L n‖ ≤ epsP ρ
  · exact MBasic_PI_symm hρ hα ⟨h1, h⟩
  · exact MBasic_PH_far_symm hρ hα (not_le.1 h) h2

private lemma Normalization_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  unfold Occ.num Finsupp.sum
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun m => α m) (fun _ _ => Nat.zero_le _) hn
  · simp [Finsupp.notMem_support_iff.1 hn]

private lemma Normalization_term_le (V w : R3 → ℝ) {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ)
    (hL : 0 < L) {b : ℤ} (hb0 : 0 ≤ b) (hb : max kc (Normalization_tau ρ) * L / (2 * π) ≤ b)
    {α : Occ} (hα : InM ρ L kc N α) (T : Finset Idx) (hT : α.support ⊆ T)
    (hT0 : (0 : Idx) ∈ T) (hTn : ∀ n ∈ T, -n ∈ T) :
    ‖f0 V w ρ L α‖ ^ 2 ≤
      (∏ u ∈ Normalization_box b, max 1 (4 * (mc ρ + 1) * |lam V w ρ L u| / L ^ 3)) *
      ∏ n ∈ T, Normalization_z V w ρ L b n ^ ((α.filter (Normalization_P b)) n) := by
  rw [Normalization_norm_f0_sq V w ρ hL α]
  set K := ∏ u ∈ Normalization_box b, max 1 (4 * (mc ρ + 1) * |lam V w ρ L u| / L ^ 3)
  set z := Normalization_z V w ρ L b
  set P1 := ∏ n ∈ α.support.filter (· ≠ 0), |lam V w ρ L n| ^ (α n)
  set P2 := ∏ u ∈ (α.support.image Neg.neg).filter
      (fun u => inPL ρ L u ∧ alphaStar α u = α u + 1),
    |4 * (alphaStar α u : ℝ) * lam V w ρ L u / L ^ 3|
  have hL3 : 0 < L ^ 3 := by positivity
  -- the factor `|Λ|^{α(0)} / α(0)!`
  have hA : (L ^ 3) ^ (α 0) / (Nat.factorial (α 0) : ℝ) ≤ (L ^ 3) ^ (α 0) :=
    div_le_self (by positivity) (by exact_mod_cast Nat.factorial_pos _)
  -- the asymmetric factors
  have hP2 : P2 ≤ K := by
    have hsub : (α.support.image Neg.neg).filter
        (fun u => inPL ρ L u ∧ alphaStar α u = α u + 1) ⊆ Normalization_box b := by
      intro u hu
      have hu' := (Finset.mem_filter.1 hu).2.1
      by_contra hnot
      exact Normalization_far_notPL (Normalization_far hL hb hnot) hu'
    refine (Finset.prod_le_prod₀ (fun u _ => abs_nonneg _) fun u hu => ?_).trans
      (Finset.prod_le_prod_of_subset_of_one_le₀ hsub (fun u _ => by positivity)
        fun u _ _ => le_max_left _ _)
    have hu' := (Finset.mem_filter.1 hu).2.1
    have hmc := MStar_PL_mc hρ hα hu'
    refine le_trans ?_ (le_max_right _ _)
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hL3, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_of_nonneg (Nat.cast_nonneg _)]
    gcongr
  -- the main product
  have hP1 : (L ^ 3) ^ (α 0) * P1 = ∏ n ∈ T, z n ^ ((α.filter (Normalization_P b)) n) := by
    let ψ : Idx → ℝ := fun n => if n = 0 then (L ^ 3) ^ (α n) else |lam V w ρ L n| ^ (α n)
    have ha : P1 = ∏ n ∈ T.erase 0, |lam V w ρ L n| ^ (α n) := by
      refine Finset.prod_subset (fun n hn => ?_) (fun n hn hn' => ?_)
      · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hn
        exact Finset.mem_erase.2 ⟨h2, hT h1⟩
      · have h0 := Finset.ne_of_mem_erase hn
        have : α n = 0 := by
          by_contra h
          exact hn' (Finset.mem_filter.2 ⟨Finsupp.mem_support_iff.2 h, h0⟩)
        rw [this, pow_zero]
    have hb' : (L ^ 3) ^ (α 0) * P1 = ∏ n ∈ T, ψ n := by
      have he : ∏ n ∈ T.erase 0, ψ n = ∏ n ∈ T.erase 0, |lam V w ρ L n| ^ (α n) :=
        Finset.prod_congr rfl fun n hn => by simp [ψ, Finset.ne_of_mem_erase hn]
      rw [← Finset.mul_prod_erase T ψ hT0, he, ha]
      simp [ψ]
    rw [hb', ← Finset.prod_filter_mul_prod_filter_not T (· ∈ Normalization_box b),
      ← Finset.prod_filter_mul_prod_filter_not T (· ∈ Normalization_box b)]
    congr 1
    · refine Finset.prod_congr rfl fun n hn => ?_
      have hn' := (Finset.mem_filter.1 hn).2
      have hP : Normalization_P b n := Or.inl hn'
      rw [Finsupp.filter_apply_pos _ _ hP]
      by_cases h0 : n = 0
      · simp [ψ, z, Normalization_z, h0]
      · simp [ψ, z, Normalization_z, h0, hn']
    · set G := T.filter (fun n => n ∉ Normalization_box b)
      rw [← Finset.prod_filter_mul_prod_filter_not G Normalization_half,
        ← Finset.prod_filter_mul_prod_filter_not G Normalization_half]
      have hG : ∀ n ∈ G, n ∈ T ∧ n ∉ Normalization_box b ∧ n ≠ 0 := by
        intro n hn
        obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hn
        exact ⟨h1, h2, fun h => h2 (h ▸ Normalization_zero_mem_box hb0)⟩
      have hm1 : ∏ n ∈ G.filter (fun n => ¬ Normalization_half n),
          z n ^ ((α.filter (Normalization_P b)) n) = 1 := by
        refine Finset.prod_eq_one fun n hn => ?_
        obtain ⟨hnG, hh⟩ := Finset.mem_filter.1 hn
        have hnot : ¬ Normalization_P b n := by
          rintro (h | h)
          · exact (hG n hnG).2.1 h
          · exact hh h
        rw [Finsupp.filter_apply_neg _ _ hnot, pow_zero]
      have hm2 : ∏ n ∈ G.filter (fun n => ¬ Normalization_half n), ψ n =
          ∏ n ∈ G.filter Normalization_half, ψ n := by
        refine Finset.prod_nbij' (fun n => -n) (fun n => -n) ?_ ?_ ?_ ?_ ?_
        · intro n hn
          obtain ⟨hnG, hh⟩ := Finset.mem_filter.1 hn
          obtain ⟨h1, h2, h3⟩ := hG n hnG
          refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hTn n h1, ?_⟩, ?_⟩
          · rwa [Normalization_box_neg]
          · exact (Normalization_half_neg h3).2 hh
        · intro n hn
          obtain ⟨hnG, hh⟩ := Finset.mem_filter.1 hn
          obtain ⟨h1, h2, h3⟩ := hG n hnG
          refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hTn n h1, ?_⟩, ?_⟩
          · rwa [Normalization_box_neg]
          · rw [Normalization_half_neg h3]
            exact not_not.2 hh
        · intro n _
          exact neg_neg n
        · intro n _
          exact neg_neg n
        · intro n hn
          obtain ⟨hnG, -⟩ := Finset.mem_filter.1 hn
          obtain ⟨-, h2, h3⟩ := hG n hnG
          have h3' : -n ≠ 0 := neg_ne_zero.2 h3
          have hs := Normalization_far_symm hρ hα (Normalization_far hL hb h2)
          simp only [ψ, h3, h3', ↓reduceIte, Regions_lam_neg, ← hs]
      have hm3 : ∏ n ∈ G.filter Normalization_half, z n ^ ((α.filter (Normalization_P b)) n) =
          ∏ n ∈ G.filter Normalization_half, (ψ n * ψ n) := by
        refine Finset.prod_congr rfl fun n hn => ?_
        obtain ⟨hnG, hh⟩ := Finset.mem_filter.1 hn
        obtain ⟨-, h2, h3⟩ := hG n hnG
        rw [Finsupp.filter_apply_pos (Normalization_P b) α
          (show Normalization_P b n from Or.inr hh)]
        simp only [ψ, z, Normalization_z, h3, h2, hh, ↓reduceIte]
        rw [← mul_pow, abs_mul_abs_self, sq]
      rw [hm1, hm2, hm3, Finset.prod_mul_distrib, mul_one]
  have hP1n : 0 ≤ P1 := Finset.prod_nonneg fun n _ => by positivity
  have hP2n : 0 ≤ P2 := Finset.prod_nonneg fun n _ => abs_nonneg _
  calc (L ^ 3) ^ (α 0) / (Nat.factorial (α 0) : ℝ) * P1 * P2
      ≤ (L ^ 3) ^ (α 0) * P1 * K := by
        gcongr
    _ = K * ∏ n ∈ T, z n ^ ((α.filter (Normalization_P b)) n) := by
        rw [hP1, mul_comm]

/-! ### Existence of `C_N` in (3.18) [deffal]

`Normalization_summable` and `Normalization_pos`: for every `ρ > 0`, `L > 0`, `k_c`, `N` and every
`V`, `w`, the sum `Σ_{α ∈ M} |f(α)|² / C_N²` over the set `M` of Definition 3.4 [M] is finite and
positive, so that `C_N` of (3.18) [deffal] exists. -/

theorem Normalization_summable (V w : R3 → ℝ) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L) (kc : ℝ)
    (N : ℕ) :
    Summable (fun β : Occ => if InM ρ L kc N β then ‖f0 V w ρ L β‖ ^ 2 else 0) := by
  have hτ : 0 < Normalization_tau ρ := by
    unfold Normalization_tau epsP
    positivity
  set b : ℤ := ⌈max kc (Normalization_tau ρ) * L / (2 * π)⌉ with hbdef
  have hb : max kc (Normalization_tau ρ) * L / (2 * π) ≤ b := Int.le_ceil _
  have hb0 : 0 ≤ b := by
    have h1 : 0 < max kc (Normalization_tau ρ) := lt_max_of_lt_right hτ
    have h2 : (0 : ℝ) ≤ b := (by positivity : (0 : ℝ) ≤ max kc (Normalization_tau ρ) * L /
      (2 * π)).trans hb
    exact_mod_cast h2
  set z := Normalization_z V w ρ L b
  set K := ∏ u ∈ Normalization_box b, max 1 (4 * (mc ρ + 1) * |lam V w ρ L u| / L ^ 3)
  have hK : 0 ≤ K := Finset.prod_nonneg fun u _ => by positivity
  have hz := Normalization_z_nonneg V w ρ hL b
  have hzs : Summable z := Normalization_z_summable V w (kc := kc) hL hb0 hb
  refine summable_of_sum_le (c := K * Real.exp (N * max 1 (∑' n, z n) ^ N * ∑' n, z n))
    (fun β => by dsimp only; split_ifs <;> positivity) (fun s => ?_)
  set s' := s.filter (fun α => InM ρ L kc N α)
  set T : Finset Idx := insert 0 (s.biUnion fun α => α.support ∪ α.support.image Neg.neg)
  set pr : Occ → Occ := fun α => α.filter (Normalization_P b)
  have hT0 : (0 : Idx) ∈ T := Finset.mem_insert_self _ _
  have hTs : ∀ α ∈ s, α.support ⊆ T := fun α hα n hn =>
    Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨α, hα, Finset.mem_union_left _ hn⟩)
  have hTn : ∀ n ∈ T, -n ∈ T := by
    intro n hn
    rcases Finset.mem_insert.1 hn with h | h
    · rw [h, neg_zero]
      exact hT0
    · obtain ⟨α, hα, hn'⟩ := Finset.mem_biUnion.1 h
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨α, hα, ?_⟩)
      rcases Finset.mem_union.1 hn' with h1 | h1
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h1)
      · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 h1
        rw [neg_neg]
        exact Finset.mem_union_left _ hm
  have hinj : Set.InjOn pr s' := by
    intro α hα α' hα' h
    have hM := (Finset.mem_filter.1 hα).2
    have hM' := (Finset.mem_filter.1 hα').2
    have key : ∀ n, Normalization_P b n → α n = α' n := by
      intro n hn
      have := congrArg (fun f : Occ => f n) h
      simpa [pr, Finsupp.filter_apply_pos _ _ hn] using this
    ext n
    by_cases hn : Normalization_P b n
    · exact key n hn
    · have h1 : n ∉ Normalization_box b := fun h => hn (Or.inl h)
      have h2 : ¬ Normalization_half n := fun h => hn (Or.inr h)
      have h0 : n ≠ 0 := fun h => h1 (h ▸ Normalization_zero_mem_box hb0)
      have hfar := Normalization_far hL hb h1
      have hneg : Normalization_P b (-n) := Or.inr ((Normalization_half_neg h0).2 h2)
      rw [Normalization_far_symm hρ hM hfar, Normalization_far_symm hρ hM' hfar]
      exact key (-n) hneg
  have hreg := Normalization_regroup hz hzs N (s'.image pr) T
    (fun β hβ => by
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hβ
      intro n hn
      rw [Finsupp.support_filter] at hn
      exact hTs α (Finset.mem_filter.1 hα).1 (Finset.mem_filter.1 hn).1)
    (fun β hβ n => by
      obtain ⟨α, hα, rfl⟩ := Finset.mem_image.1 hβ
      have hnum := MBasic_num hρ (Finset.mem_filter.1 hα).2
      calc (pr α) n ≤ α n := by
            simp only [pr, Finsupp.filter_apply]
            split_ifs <;> omega
        _ ≤ α.num := Normalization_le_num α n
        _ = N := hnum)
  calc ∑ α ∈ s, (if InM ρ L kc N α then ‖f0 V w ρ L α‖ ^ 2 else 0)
      = ∑ α ∈ s', ‖f0 V w ρ L α‖ ^ 2 := (Finset.sum_filter _ _).symm
    _ ≤ ∑ α ∈ s', K * ∏ n ∈ T, z n ^ ((pr α) n) :=
        Finset.sum_le_sum fun α hα => Normalization_term_le V w hρ hL hb0 hb
          (Finset.mem_filter.1 hα).2 T (hTs α (Finset.mem_filter.1 hα).1) hT0 hTn
    _ = K * ∑ β ∈ s'.image pr, ∏ n ∈ T, z n ^ (β n) := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ K * Real.exp (N * max 1 (∑' n, z n) ^ N * ∑' n, z n) :=
        mul_le_mul_of_nonneg_left hreg hK

theorem Normalization_pos (V w : R3 → ℝ) {ρ L : ℝ} (hρ : 0 < ρ) (hL : 0 < L) (kc : ℝ)
    (N : ℕ) :
    0 < ∑' β : Occ, if InM ρ L kc N β then ‖f0 V w ρ L β‖ ^ 2 else 0 := by
  refine (Normalization_summable V w hρ hL kc N).tsum_pos
    (fun β => by split_ifs <;> positivity) (Finsupp.single 0 N) ?_
  simp only [InM.free, ↓reduceIte]
  rw [Normalization_norm_f0_sq V w ρ hL]
  have h1 : ∏ n ∈ (Finsupp.single (0 : Idx) N).support.filter (· ≠ 0),
      |lam V w ρ L n| ^ ((Finsupp.single (0 : Idx) N) n) = 1 := by
    refine Finset.prod_eq_one fun n hn => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hn
    exact absurd (Finset.mem_singleton.1 (Finsupp.support_single_subset h1)) h2
  have h2 : ∏ u ∈ ((Finsupp.single (0 : Idx) N).support.image Neg.neg).filter
      (fun u => inPL ρ L u ∧
        alphaStar (Finsupp.single (0 : Idx) N) u = (Finsupp.single (0 : Idx) N) u + 1),
      |4 * (alphaStar (Finsupp.single (0 : Idx) N) u : ℝ) * lam V w ρ L u / L ^ 3| = 1 := by
    refine Finset.prod_eq_one fun u hu => ?_
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hu
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 h1
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hm), neg_zero] at h2
    exact absurd rfl (Regions_PL_ne_zero hρ h2)
  rw [h1, h2, mul_one, mul_one]
  positivity

/-- `Ψ` of (3.18) [deffal] is a normalized `N`-particle state. -/
theorem Normalization_isNState (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    IsNState N (trialState V w kc N) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 < rhoN N := by
    unfold rhoN
    positivity
  have hL : 0 < LN N := by
    unfold LN
    positivity
  set Z := ∑' β : Occ, if InM (rhoN N) (LN N) kc N β then
    ‖f0 V w (rhoN N) (LN N) β‖ ^ 2 else 0 with hZ
  have hZpos : 0 < Z := Normalization_pos V w hρ hL kc N
  have hsum := (Normalization_summable V w hρ hL kc N).hasSum
  have hCN : CN V w kc N = (Real.sqrt Z)⁻¹ := rfl
  refine ⟨?_, ?_⟩
  · have h1 : (fun α => ‖trialState V w kc N α‖ ^ 2) = fun α => Z⁻¹ *
        (if InM (rhoN N) (LN N) kc N α then ‖f0 V w (rhoN N) (LN N) α‖ ^ 2 else 0) := by
      funext α
      rw [FIdentities_trialState]
      split_ifs
      · rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hCN, inv_pow,
          Real.sq_sqrt hZpos.le]
      · simp
    rw [h1]
    have := hsum.mul_left Z⁻¹
    rwa [inv_mul_cancel₀ hZpos.ne'] at this
  · intro α hα
    rw [FIdentities_trialState] at hα
    split_ifs at hα with h
    · exact MBasic_num hρ h
    · exact absurd rfl hα

/-- Normalization part of the first conjunct of Theorem 3.1 [lemma2.1]. -/
theorem Normalization_eventually (V w : R3 → ℝ) :
    ∀ kc : ℝ, ∀ᶠ N in atTop, IsNState N (trialState V w kc N) := by
  intro kc
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact Normalization_isNState V w kc hN

end Normalization

end LHYUpper
