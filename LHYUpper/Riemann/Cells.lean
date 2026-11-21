module

public import LHYUpper.Riemann.Radial

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! Lattice cells of `Λ* = (2π/L)ℤ³` and bounds, uniform in `L`, of lattice sums of majorants
`min(|p|^{-a}, |p|^{-b})` by integrals. These are tools for the limit
`L^{-3} Σ_{p ∈ Λ*} F(p) → (2π)^{-3} ∫ F` recalled before (5.35) [3.1]. -/

/-! ### Lattice cells of `Λ* = δℤ³`, `δ = 2π/L` -/

/-- The cell `Q_n = p_n + δ(-½, ½]³` around `p_n = mom L n`, `δ = 2π/L`. -/
def Cells_cell (L : ℝ) (n : Idx) : Set R3 :=
  {q | ∀ i, q i ∈ Set.Ioc (2 * π / L * ((n i : ℝ) - 1 / 2)) (2 * π / L * ((n i : ℝ) + 1 / 2))}

/-- The index of the cell containing `q`: `n_i = ⌈q_i/δ - ½⌉`. -/
def Cells_index (L : ℝ) (q : R3) : Idx := fun i => ⌈q i / (2 * π / L) - 1 / 2⌉

/-- Coordinates of `p_n = mom L n`: `(p_n)_i = (2π/L) n_i`. -/
theorem Cells_mom_apply (L : ℝ) (n : Idx) (i : Fin 3) : mom L n i = 2 * π / L * (n i : ℝ) :=
  rfl

/-- `q ∈ Q_n` if and only if `n` is the index of `q`. -/
theorem Cells_mem_iff {L : ℝ} (hL : 0 < L) (q : R3) (n : Idx) :
    q ∈ Cells_cell L n ↔ Cells_index L q = n := by
  have hδ : 0 < 2 * π / L := by positivity
  simp only [Cells_cell, Set.mem_ofPred_eq, Set.mem_Ioc, Cells_index, funext_iff]
  refine forall_congr' fun i => ?_
  rw [Int.ceil_eq_iff]
  have hq : q i = 2 * π / L * (q i / (2 * π / L)) := by field_simp
  set x := q i / (2 * π / L)
  rw [hq, mul_lt_mul_iff_right₀ hδ, mul_le_mul_iff_right₀ hδ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- `p_n ∈ Q_n`. -/
theorem Cells_mom_mem {L : ℝ} (hL : 0 < L) (n : Idx) : mom L n ∈ Cells_cell L n := by
  have hδ : 0 < 2 * π / L := by positivity
  intro i
  rw [Cells_mom_apply]
  constructor <;> nlinarith

/-- The cells `Q_n` are measurable. -/
theorem Cells_measurableSet (L : ℝ) (n : Idx) : MeasurableSet (Cells_cell L n) := by
  have : Cells_cell L n = WithLp.ofLp ⁻¹' Set.univ.pi (fun i =>
      Set.Ioc (2 * π / L * ((n i : ℝ) - 1 / 2)) (2 * π / L * ((n i : ℝ) + 1 / 2))) := by
    ext q; simp [Cells_cell]
  rw [this]
  exact (MeasurableSet.univ_pi fun i => measurableSet_Ioc).preimage
    (PiLp.volume_preserving_ofLp (Fin 3)).measurable

/-- The cells `Q_n` are pairwise disjoint. -/
theorem Cells_pairwise_disjoint {L : ℝ} (hL : 0 < L) :
    Pairwise (Function.onFun Disjoint (Cells_cell L)) := by
  intro n m hnm
  refine Set.disjoint_left.2 fun q hn hm => hnm ?_
  rw [Cells_mem_iff hL] at hn hm
  exact hn.symm.trans hm

/-- The cells `Q_n` cover `ℝ³`. -/
theorem Cells_iUnion {L : ℝ} (hL : 0 < L) : ⋃ n, Cells_cell L n = Set.univ :=
  Set.eq_univ_of_forall fun q => Set.mem_iUnion.2 ⟨Cells_index L q, (Cells_mem_iff hL q _).2 rfl⟩

/-- `|Q_n| = δ³`. -/
theorem Cells_volume {L : ℝ} (hL : 0 < L) (n : Idx) :
    volume (Cells_cell L n) = ENNReal.ofReal ((2 * π / L) ^ 3) := by
  have hδ : 0 < 2 * π / L := by positivity
  have : Cells_cell L n = WithLp.ofLp ⁻¹' Set.univ.pi (fun i =>
      Set.Ioc (2 * π / L * ((n i : ℝ) - 1 / 2)) (2 * π / L * ((n i : ℝ) + 1 / 2))) := by
    ext q; simp [Cells_cell]
  rw [this, (PiLp.volume_preserving_ofLp (Fin 3)).measure_preimage
    (MeasurableSet.univ_pi fun i => measurableSet_Ioc).nullMeasurableSet, Real.volume_pi_Ioc]
  have h : ∀ i : Fin 3, 2 * π / L * ((n i : ℝ) + 1 / 2) - 2 * π / L * ((n i : ℝ) - 1 / 2) =
      2 * π / L := fun i => by ring
  simp only [h, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hδ.le]

/-- `Q_n ⊆ closedBall(p_n, (√3/2)δ)`. -/
theorem Cells_norm_sub_mom_le {L : ℝ} (hL : 0 < L) {n : Idx} {q : R3}
    (hq : q ∈ Cells_cell L n) : ‖q - mom L n‖ ≤ √3 / 2 * (2 * π / L) := by
  have hδ : 0 < 2 * π / L := by positivity
  have hi : ∀ i, (q - mom L n) i ^ 2 ≤ (2 * π / L / 2) ^ 2 := by
    intro i
    have h := hq i
    rw [PiLp.sub_apply, Cells_mom_apply]
    apply sq_le_sq' <;> linarith [h.1, h.2]
  have hsq : ‖q - mom L n‖ ^ 2 ≤ (√3 / 2 * (2 * π / L)) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, mul_pow, div_pow,
      Real.sq_sqrt (by norm_num)]
    have h0 := hi 0
    have h1 := hi 1
    have h2 := hi 2
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 hsq

/-- `|p_n| ≥ δ` for `n ≠ 0`. -/
theorem Cells_le_norm_mom {L : ℝ} (hL : 0 < L) {n : Idx} (hn : n ≠ 0) :
    2 * π / L ≤ ‖mom L n‖ := by
  have hδ : 0 < 2 * π / L := by positivity
  obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
    by_contra h
    push Not at h
    exact hn (funext h)
  have h1 : (1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast Int.one_le_abs hi
  calc 2 * π / L ≤ 2 * π / L * |(n i : ℝ)| := le_mul_of_one_le_right hδ.le h1
    _ = ‖mom L n i‖ := by rw [Cells_mom_apply, Real.norm_eq_abs, abs_mul, abs_of_pos hδ]
    _ ≤ ‖mom L n‖ := PiLp.norm_apply_le _ _

/-- Cell comparison: for `φ` nonincreasing on `(0, ∞)` and `n ≠ 0`,
`δ³ φ(|p_n|) ≤ ∫_{Q_n} φ(|q|/2) dq`. -/
theorem Cells_le_setIntegral {L : ℝ} (hL : 0 < L) {n : Idx} (hn : n ≠ 0) {φ : ℝ → ℝ}
    (hφ : AntitoneOn φ (Set.Ioi 0))
    (hint : IntegrableOn (fun q : R3 => φ (‖q‖ / 2)) (Cells_cell L n)) :
    (2 * π / L) ^ 3 * φ ‖mom L n‖ ≤ ∫ q in Cells_cell L n, φ (‖q‖ / 2) := by
  have hδ : 0 < 2 * π / L := by positivity
  have hs3 : √3 / 2 < 1 := by
    have : √3 < 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hpt : ∀ q ∈ Cells_cell L n, φ ‖mom L n‖ ≤ φ (‖q‖ / 2) := by
    intro q hq
    have h1 := Cells_norm_sub_mom_le hL hq
    have h2 := Cells_le_norm_mom hL hn
    have h3 : ‖q - mom L n‖ < 2 * π / L := lt_of_le_of_lt h1 (by nlinarith)
    have h4 : ‖mom L n‖ ≤ ‖q‖ + ‖q - mom L n‖ := by
      have := norm_sub_le q (q - mom L n)
      rwa [sub_sub_cancel] at this
    have h5 : ‖q‖ ≤ ‖mom L n‖ + ‖q - mom L n‖ := by
      have := norm_add_le (mom L n) (q - mom L n)
      rwa [add_sub_cancel] at this
    exact hφ (show (0 : ℝ) < ‖q‖ / 2 by linarith) (show (0 : ℝ) < ‖mom L n‖ by linarith)
      (show ‖q‖ / 2 ≤ ‖mom L n‖ by linarith)
  calc (2 * π / L) ^ 3 * φ ‖mom L n‖ = ∫ _ in Cells_cell L n, φ ‖mom L n‖ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, Cells_volume hL,
          ENNReal.toReal_ofReal (by positivity)]
    _ ≤ ∫ q in Cells_cell L n, φ (‖q‖ / 2) :=
        setIntegral_mono_on (integrableOn_const (by rw [Cells_volume hL]; simp)) hint
          (Cells_measurableSet L n) hpt

/-! ### Majorant sums -/

/-- The summand `[n ≠ 0, p_n ∈ A] F(p_n)` of `latSum L A F`. -/
private def Cells_term (L : ℝ) (A : Set R3) (F : R3 → ℝ) (n : Idx) : ℝ :=
  if n ≠ 0 ∧ mom L n ∈ A then F (mom L n) else 0

private lemma Cells_latSum_eq (L : ℝ) (A : Set R3) (F : R3 → ℝ) :
    latSum L A F = ∑' n, Cells_term L A F n := rfl

private lemma Cells_latSummable_iff (L : ℝ) (A : Set R3) (F : R3 → ℝ) :
    latSummable L A F ↔ Summable (Cells_term L A F) := Iff.rfl

private lemma Cells_term_univ (L : ℝ) (F : R3 → ℝ) (n : Idx) :
    Cells_term L Set.univ F n = if n ≠ 0 then F (mom L n) else 0 := by
  unfold Cells_term
  split_ifs <;> simp_all

/-- `r ↦ min(r^{-a}, r^{-b})` is nonincreasing on `(0, ∞)` for `a, b ≥ 0`. -/
private lemma Cells_minRpow_antitone {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    AntitoneOn (fun r : ℝ => min (r ^ (-a)) (r ^ (-b))) (Set.Ioi 0) :=
  fun _ hx _ _ hxy => min_le_min (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
    (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))

/-- `q ↦ min(|q|^{-a}, |q|^{-b})` is integrable on `ℝ³` for `0 ≤ a < 3 < b`. -/
private lemma Cells_minRpow_integrable {a b : ℝ} (ha3 : a < 3) (hb : 3 < b) :
    Integrable (fun q : R3 => min (‖q‖ ^ (-a)) (‖q‖ ^ (-b))) := by
  have hmeas : Measurable (fun s : ℝ => s ^ 2 * min (s ^ (-a)) (s ^ (-b))) := by fun_prop
  have hpow : ∀ s : ℝ, 0 < s → ∀ c : ℝ, s ^ 2 * s ^ (-c) = s ^ (2 - c) := by
    intro s hs c
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    norm_num
    ring_nf
  have hI1 : IntegrableOn (fun s : ℝ => s ^ 2 * min (s ^ (-a)) (s ^ (-b))) (Set.Ioc 0 1) := by
    have hint : IntegrableOn (fun s : ℝ => s ^ (2 - a)) (Set.Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := 2 - a) (by linarith))
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun s hs => ?_
    have hs0 : 0 < s := hs.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← hpow s hs0 a]
    exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
  have hI2 : IntegrableOn (fun s : ℝ => s ^ 2 * min (s ^ (-a)) (s ^ (-b))) (Set.Ioi 1) := by
    have hint : IntegrableOn (fun s : ℝ => s ^ (2 - b)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine hint.mono' hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun s hs => ?_
    have hs0 : 0 < s := lt_trans one_pos hs
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← hpow s hs0 b]
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
  have hI : IntegrableOn (fun s : ℝ => s ^ 2 * min (s ^ (-a)) (s ^ (-b))) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact hI1.union hI2
  rw [integrable_fun_norm_addHaar volume (f := fun s : ℝ => min (s ^ (-a)) (s ^ (-b)))]
  simpa [finrank_euclideanSpace_fin] using hI

/-- `|Λ|⁻¹ Σ_{p ∈ Λ*, p ≠ 0} |F(p)| ≤ K C` under the bound (H1). -/
theorem latSum_abs_le {a b : ℝ} (ha : 0 ≤ a) (ha3 : a < 3) (hb : 3 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (F : R3 → ℝ) (L : ℝ), 0 ≤ C → 2 * π ≤ L →
      (∀ p : R3, p ≠ 0 → |F p| ≤ C * min (‖p‖ ^ (-a)) (‖p‖ ^ (-b))) →
      latSummable L Set.univ (fun p => |F p|) ∧
      (L ^ 3)⁻¹ * latSum L Set.univ (fun p => |F p|) ≤ K * C := by
  set φ : ℝ → ℝ := fun r => min (r ^ (-a)) (r ^ (-b)) with hφ
  set Φ : R3 → ℝ := fun q => φ (‖q‖ / 2) with hΦ
  have hφ0 : ∀ r, 0 ≤ r → 0 ≤ φ r := fun r hr =>
    le_min (Real.rpow_nonneg hr _) (Real.rpow_nonneg hr _)
  have hΦ0 : ∀ q, 0 ≤ Φ q := fun q => hφ0 _ (by positivity)
  have hΦint : Integrable Φ := by
    have h := (Cells_minRpow_integrable ha3 hb).comp_smul (R := (2 : ℝ)⁻¹) (by norm_num)
    refine h.congr (Eventually.of_forall fun q => ?_)
    simp only [hΦ, hφ, norm_smul, Real.norm_eq_abs, abs_inv, abs_two]
    ring_nf
  refine ⟨((2 * π) ^ 3)⁻¹ * ∫ q, Φ q, mul_nonneg (by positivity) (integral_nonneg hΦ0), ?_⟩
  intro C F L hC hL hF
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hδ : 0 < 2 * π / L := by positivity
  have hsum : HasSum (fun n => ∫ q in Cells_cell L n, Φ q) (∫ q, Φ q) := by
    have h := hasSum_integral_iUnion (Cells_measurableSet L) (Cells_pairwise_disjoint hL0)
      (by rw [Cells_iUnion hL0]; exact hΦint.integrableOn)
    rwa [Cells_iUnion hL0, Measure.restrict_univ] at h
  set g : Idx → ℝ := Cells_term L Set.univ (fun p => |F p|) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => by
    simp only [hg, Cells_term_univ]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hgle : ∀ n, g n ≤ C * ((2 * π / L) ^ 3)⁻¹ * ∫ q in Cells_cell L n, Φ q := by
    intro n
    by_cases hn : n = 0
    · simp only [hg, Cells_term_univ, hn, ne_eq, not_true_eq_false, ite_false]
      exact mul_nonneg (by positivity)
        (setIntegral_nonneg (Cells_measurableSet L 0) fun q _ => hΦ0 q)
    · simp only [hg, Cells_term_univ, ne_eq, hn, not_false_eq_true, ite_true]
      have hm : mom L n ≠ 0 := by
        intro h0
        have := Cells_le_norm_mom hL0 hn
        rw [h0, norm_zero] at this
        linarith
      have h1 := hF _ hm
      have h2 := Cells_le_setIntegral hL0 hn (Cells_minRpow_antitone (a := a) (b := b) ha
        (by linarith)) (hΦint.integrableOn)
      calc |F (mom L n)| ≤ C * φ ‖mom L n‖ := h1
        _ = C * ((2 * π / L) ^ 3)⁻¹ * ((2 * π / L) ^ 3 * φ ‖mom L n‖) := by
          field_simp
        _ ≤ C * ((2 * π / L) ^ 3)⁻¹ * ∫ q in Cells_cell L n, Φ q :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hsum' := hsum.mul_left (C * ((2 * π / L) ^ 3)⁻¹)
  have hsumm : Summable g := Summable.of_nonneg_of_le hg0 hgle hsum'.summable
  refine ⟨(Cells_latSummable_iff _ _ _).2 hsumm, ?_⟩
  have htle : ∑' n, g n ≤ C * ((2 * π / L) ^ 3)⁻¹ * ∫ q, Φ q := by
    rw [← hsum'.tsum_eq]
    exact hsumm.tsum_le_tsum hgle hsum'.summable
  rw [Cells_latSum_eq]
  calc (L ^ 3)⁻¹ * ∑' n, g n ≤ (L ^ 3)⁻¹ * (C * ((2 * π / L) ^ 3)⁻¹ * ∫ q, Φ q) :=
        mul_le_mul_of_nonneg_left htle (by positivity)
    _ = ((2 * π) ^ 3)⁻¹ * (∫ q, Φ q) * C := by
        field_simp

/-- `mom L n = R • mom (L R) n`. -/
private lemma Cells_mom_scale {L R : ℝ} (hL : 0 < L) (hR : 0 < R) (n : Idx) :
    mom L n = R • mom (L * R) n := by
  ext i
  rw [PiLp.smul_apply, Cells_mom_apply, Cells_mom_apply, smul_eq_mul]
  field_simp

/-- `|Λ|⁻¹ Σ_{0 < |u| ≤ R} |u|^{-s} ≤ K R^{3−s}` for `s < 3`. -/
theorem sum_norm_rpow_le {s : ℝ} (hs : s < 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L R : ℝ, 0 < R → 2 * π ≤ L * R →
      (L ^ 3)⁻¹ * ∑' n : Idx, (if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-s) else 0)
        ≤ K * R ^ (3 - s) := by
  obtain ⟨K, hK, h⟩ := latSum_abs_le (a := max s 0) (b := 4) (le_max_right _ _)
    (max_lt hs (by norm_num)) (by norm_num)
  refine ⟨K, hK, fun L R hR hLR => ?_⟩
  have hL : 0 < L := by
    by_contra hL
    push Not at hL
    have : L * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL hR.le
    linarith [Real.pi_pos]
  set F : R3 → ℝ := fun k => if ‖k‖ ≤ 1 then ‖k‖ ^ (-s) else 0 with hF
  have hFb : ∀ k : R3, k ≠ 0 → |F k| ≤ 1 * min (‖k‖ ^ (-max s 0)) (‖k‖ ^ (-(4 : ℝ))) := by
    intro k hk
    have hk0 : 0 < ‖k‖ := norm_pos_iff.2 hk
    simp only [hF, one_mul]
    split_ifs with h1
    · rw [abs_of_nonneg (Real.rpow_nonneg hk0.le _)]
      exact le_min (Real.rpow_le_rpow_of_exponent_ge hk0 h1 (by simp))
        (Real.rpow_le_rpow_of_exponent_ge hk0 h1 (by linarith))
    · rw [abs_zero]
      exact le_min (Real.rpow_nonneg hk0.le _) (Real.rpow_nonneg hk0.le _)
  obtain ⟨-, hle⟩ := h 1 F (L * R) zero_le_one hLR hFb
  have hterm : ∀ n : Idx, (if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-s) else 0) =
      R ^ (-s) * Cells_term (L * R) Set.univ (fun p => |F p|) n := by
    intro n
    rw [Cells_mom_scale hL hR n, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hiff : R * ‖mom (L * R) n‖ ≤ R ↔ ‖mom (L * R) n‖ ≤ 1 := by
      constructor
      · intro h1; nlinarith
      · intro h1; nlinarith
    simp only [Cells_term_univ, hiff, hF]
    split_ifs <;> simp_all [Real.mul_rpow hR.le (norm_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  simp_rw [hterm]
  rw [tsum_mul_left]
  have hscale : (L ^ 3)⁻¹ * (R ^ (-s) * latSum (L * R) Set.univ (fun p => |F p|)) =
      R ^ (3 - s) * (((L * R) ^ 3)⁻¹ * latSum (L * R) Set.univ (fun p => |F p|)) := by
    rw [show (3 : ℝ) - s = -s + (3 : ℕ) by push_cast; ring, Real.rpow_add hR, Real.rpow_natCast]
    field_simp
  rw [← Cells_latSum_eq]
  rw [hscale]
  calc R ^ (3 - s) * (((L * R) ^ 3)⁻¹ * latSum (L * R) Set.univ (fun p => |F p|))
      ≤ R ^ (3 - s) * (K * 1) := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hR.le _)
    _ = K * R ^ (3 - s) := by ring

/-- `|Λ|⁻¹ Σ_{|u| > R} |u|^{-s} ≤ K R^{3−s}` for `s > 3`. -/
theorem sum_norm_rpow_gt {s : ℝ} (hs : 3 < s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L R : ℝ, 0 < R → 2 * π ≤ L * R →
      Summable (fun n : Idx => if R < ‖mom L n‖ then ‖mom L n‖ ^ (-s) else 0) ∧
      (L ^ 3)⁻¹ * ∑' n : Idx, (if R < ‖mom L n‖ then ‖mom L n‖ ^ (-s) else 0)
        ≤ K * R ^ (3 - s) := by
  obtain ⟨K, hK, h⟩ := latSum_abs_le (a := 0) (b := s) le_rfl (by norm_num) hs
  refine ⟨K, hK, fun L R hR hLR => ?_⟩
  have hL : 0 < L := by
    by_contra hL
    push Not at hL
    have : L * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL hR.le
    linarith [Real.pi_pos]
  set F : R3 → ℝ := fun k => if 1 < ‖k‖ then ‖k‖ ^ (-s) else 0 with hF
  have hFb : ∀ k : R3, k ≠ 0 → |F k| ≤ 1 * min (‖k‖ ^ (-(0 : ℝ))) (‖k‖ ^ (-s)) := by
    intro k hk
    have hk0 : 0 < ‖k‖ := norm_pos_iff.2 hk
    simp only [hF, one_mul, neg_zero, Real.rpow_zero]
    split_ifs with h1
    · rw [abs_of_nonneg (Real.rpow_nonneg hk0.le _)]
      exact le_min (Real.rpow_le_one_of_one_le_of_nonpos h1.le (by linarith)) le_rfl
    · rw [abs_zero]
      exact le_min zero_le_one (Real.rpow_nonneg hk0.le _)
  obtain ⟨hsm, hle⟩ := h 1 F (L * R) zero_le_one hLR hFb
  have hterm : ∀ n : Idx, (if R < ‖mom L n‖ then ‖mom L n‖ ^ (-s) else 0) =
      R ^ (-s) * Cells_term (L * R) Set.univ (fun p => |F p|) n := by
    intro n
    rw [Cells_mom_scale hL hR n, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    have hiff : R < R * ‖mom (L * R) n‖ ↔ 1 < ‖mom (L * R) n‖ := by
      constructor
      · intro h1; nlinarith
      · intro h1; nlinarith
    by_cases hn : n = 0
    · subst hn
      have h0 : mom (L * R) 0 = 0 := by
        ext i; rw [Cells_mom_apply]; simp
      rw [h0, norm_zero, mul_zero, ite_eq_right (not_lt.2 hR.le), Cells_term_univ,
        ite_eq_right (by simp), mul_zero]
    simp only [Cells_term_univ, hiff, hF, ne_eq, hn, not_false_eq_true, ite_true]
    split_ifs <;> simp_all [Real.mul_rpow hR.le (norm_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  simp_rw [hterm]
  refine ⟨((Cells_latSummable_iff _ _ _).1 hsm).mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hscale : (L ^ 3)⁻¹ * (R ^ (-s) * latSum (L * R) Set.univ (fun p => |F p|)) =
      R ^ (3 - s) * (((L * R) ^ 3)⁻¹ * latSum (L * R) Set.univ (fun p => |F p|)) := by
    rw [show (3 : ℝ) - s = -s + (3 : ℕ) by push_cast; ring, Real.rpow_add hR, Real.rpow_natCast]
    field_simp
  rw [← Cells_latSum_eq]
  rw [hscale]
  calc R ^ (3 - s) * (((L * R) ^ 3)⁻¹ * latSum (L * R) Set.univ (fun p => |F p|))
      ≤ R ^ (3 - s) * (K * 1) := mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hR.le _)
    _ = K * R ^ (3 - s) := by ring

end LHYUpper
