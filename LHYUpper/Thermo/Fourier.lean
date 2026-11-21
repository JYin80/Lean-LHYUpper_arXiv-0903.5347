module

public import LHYUpper.Position.Basic
public import LHYUpper.Position.SymWave

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! Fourier analysis on the period cell `[0, L]^{3N}` for the duplication step after
Lemma 2.1 [thm1] (§2): the coefficient state of a symmetric function in the occupation-number
basis, its wave function, and the convergence of its norm and kinetic energy (Parseval on the
torus `(ℝ/ℤ)^{3N}` after rescaling, integration by parts against the plane waves). -/

/-- The occupation `α(k) = #{i : p_i = k}` of a momentum assignment `p : Fin N → ℤ³`. -/
def occOf {N : ℕ} (p : Fin N → Idx) : Occ := ∑ i, Finsupp.single (p i) 1

/-- The occupations of `N` particles with all momenta in the box `|n|_∞ ≤ R` of `ℤ³`. -/
def occBox (N R : ℕ) : Finset Occ :=
  (Fintype.piFinset fun _ : Fin N => Finset.Icc (fun _ => -(R : ℤ)) (fun _ => (R : ℤ))).image
    occOf

/-- The truncated coefficient state of `Φ`: `Ψ_R(α) = ∫_{[0, L]^{3N}} conj(Φ_α) Φ` for the
occupations `α` of `occBox N R`, and `0` for all other `α`. -/
def coeffState (L : ℝ) (N R : ℕ) (Φ : Conf N → ℂ) : Occ →₀ ℂ :=
  Finsupp.indicator (occBox N R) fun α _ =>
    ∫ x in cellN L N, conj (symWave L N α x) * Φ x

/-! ### Products of plane waves, coefficients and projections -/

/-- The product plane wave `e_p(x) = ∏_i e_{p_i}(x_i)` on `(ℝ³)^N`. -/
private def Fourier_wave (L : ℝ) {N : ℕ} (p : Fin N → Idx) (x : Conf N) : ℂ :=
  ∏ i, planeWave L (p i) (x i)

/-- The coefficient `c_p(g) = ∫_{[0, L]^{3N}} conj(e_p) g`. -/
private def Fourier_coef (L : ℝ) {N : ℕ} (g : Conf N → ℂ) (p : Fin N → Idx) : ℂ :=
  ∫ y in cellN L N, conj (Fourier_wave L p y) * g y

/-- The box `B_R^N` of assignments with `|p_i|_∞ ≤ R` for all `i`. -/
private def Fourier_box (N R : ℕ) : Finset (Fin N → Idx) :=
  Fintype.piFinset fun _ : Fin N => Finset.Icc (fun _ => -(R : ℤ)) (fun _ => (R : ℤ))

/-- The projection `P_s g = Σ_{p ∈ s} c_p(g) e_p`. -/
private def Fourier_proj (L : ℝ) {N : ℕ} (s : Finset (Fin N → Idx)) (g : Conf N → ℂ)
    (x : Conf N) : ℂ :=
  ∑ p ∈ s, Fourier_coef L g p * Fourier_wave L p x

private lemma Fourier_planeWave_continuous (L : ℝ) (n : Idx) : Continuous (planeWave L n) := by
  unfold planeWave
  fun_prop

private lemma Fourier_wave_continuous (L : ℝ) {N : ℕ} (p : Fin N → Idx) :
    Continuous (Fourier_wave L p) := by
  unfold Fourier_wave
  exact continuous_finsetProd _ fun i _ =>
    (Fourier_planeWave_continuous L (p i)).comp (continuous_apply i)

private lemma Fourier_proj_continuous (L : ℝ) {N : ℕ} (s : Finset (Fin N → Idx))
    (g : Conf N → ℂ) : Continuous (Fourier_proj L s g) := by
  unfold Fourier_proj
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (Fourier_wave_continuous L p)

/-! ### The period cell -/

private lemma Fourier_cell_eq (L : ℝ) :
    cell L = (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin 3 => Set.Icc 0 L) := by
  ext y
  constructor
  · intro hy
    exact ⟨WithLp.ofLp y, fun a _ => hy a, by simp⟩
  · rintro ⟨z, hz, rfl⟩ a
    exact hz a (Set.mem_univ a)

private lemma Fourier_cellN_eq (L : ℝ) (N : ℕ) :
    cellN L N = Set.univ.pi fun _ : Fin N => cell L := by
  ext x
  simp [cellN]

private lemma Fourier_isCompact_cellN (L : ℝ) (N : ℕ) : IsCompact (cellN L N) := by
  rw [Fourier_cellN_eq]
  refine isCompact_univ_pi fun _ => ?_
  rw [Fourier_cell_eq]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

private lemma Fourier_integrableOn {L : ℝ} {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    {f : Conf N → E} (hf : Continuous f) : IntegrableOn f (cellN L N) :=
  hf.continuousOn.integrableOn_compact (Fourier_isCompact_cellN L N)

private lemma Fourier_integrableOn_wave_mul {L : ℝ} {N : ℕ} (q : Fin N → Idx)
    {g : Conf N → ℂ} (hg : Continuous g) :
    IntegrableOn (fun x => conj (Fourier_wave L q x) * g x) (cellN L N) :=
  Fourier_integrableOn ((Complex.continuous_conj.comp (Fourier_wave_continuous L q)).mul hg)

/-! ### Orthonormality of the product plane waves -/

private lemma Fourier_wave_orth {L : ℝ} (hL : 0 < L) {N : ℕ} (p q : Fin N → Idx) :
    ∫ x in cellN L N, conj (Fourier_wave L q x) * Fourier_wave L p x =
      if p = q then 1 else 0 := by
  have h : ∀ x : Conf N, conj (Fourier_wave L q x) * Fourier_wave L p x =
      ∏ i, conj (planeWave L (q i) (x i)) * planeWave L (p i) (x i) := by
    intro x
    simp [Fourier_wave, map_prod, Finset.prod_mul_distrib]
  simp_rw [h, Fourier_cellN_eq]
  rw [volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun i y => conj (planeWave L (q i) y) * planeWave L (p i) y)]
  simp_rw [planeWave_orthonormal hL]
  by_cases hpq : p = q
  · subst hpq
    simp
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hpq
    rw [ite_eq_right_iff.2 fun h => absurd h hpq]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Ne.symm hi])

/-! ### Occupations and assignments -/

private lemma Fourier_occOf_apply {N : ℕ} (p : Fin N → Idx) (k : Idx) :
    occOf p k = (Finset.univ.filter fun i => p i = k).card := by
  rw [occOf, Finsupp.finsetSum_apply, Finset.card_filter]
  simp only [Finsupp.single_apply]

private lemma Fourier_mem_occFns {N : ℕ} {α : Occ} {p : Fin N → Idx} :
    p ∈ occFns N α ↔ occOf p = α := by
  unfold occFns
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨-, h⟩
    ext k
    rw [Fourier_occOf_apply, h k]
  · rintro rfl
    refine ⟨fun i => ?_, fun k => (Fourier_occOf_apply p k).symm⟩
    rw [Finsupp.mem_support_iff, Fourier_occOf_apply]
    exact (Finset.card_pos.2 ⟨i, by simp⟩).ne'

private lemma Fourier_num_occOf {N : ℕ} (p : Fin N → Idx) : (occOf p).num = N := by
  unfold Occ.num occOf
  rw [← Finsupp.sum_finsetSum_index (fun _ => rfl) (fun _ _ _ => rfl)]
  simp [Finsupp.sum_single_index]

private lemma Fourier_exists_perm {N : ℕ} {p q : Fin N → Idx} (h : occOf q = occOf p) :
    ∃ σ : Equiv.Perm (Fin N), q = p ∘ σ := by
  have hc : ∀ k, Fintype.card {i // q i = k} = Fintype.card {i // p i = k} := by
    intro k
    rw [Fintype.card_subtype, Fintype.card_subtype, ← Fourier_occOf_apply,
      ← Fourier_occOf_apply, h]
  refine ⟨Equiv.ofFiberEquiv (fun k => Fintype.equivOfCardEq (hc k)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm

/-! ### Symmetry of the coefficients -/

private lemma Fourier_wave_comp (L : ℝ) {N : ℕ} (p : Fin N → Idx) (σ : Equiv.Perm (Fin N))
    (x : Conf N) : Fourier_wave L p (x ∘ σ.symm) = Fourier_wave L (p ∘ σ) x := by
  unfold Fourier_wave
  rw [← Equiv.prod_comp σ (fun i => planeWave L (p i) ((x ∘ σ.symm) i))]
  simp

private lemma Fourier_coef_comp (L : ℝ) {N : ℕ} {Φ : Conf N → ℂ}
    (hs : ∀ σ : Equiv.Perm (Fin N), ∀ x, Φ (x ∘ σ) = Φ x) (p : Fin N → Idx)
    (σ : Equiv.Perm (Fin N)) : Fourier_coef L Φ (p ∘ σ) = Fourier_coef L Φ p := by
  let τ : Conf N ≃ᵐ Conf N := MeasurableEquiv.arrowCongr' σ (MeasurableEquiv.refl R3)
  have hτ : MeasurePreserving τ volume volume :=
    measurePreserving_arrowCongr' (fun _ => volume) (fun _ => volume) σ (MeasurableEquiv.refl R3)
      fun _ => MeasurePreserving.id volume
  have hτx : ∀ x : Conf N, τ x = x ∘ σ.symm := fun x => rfl
  have key := hτ.setIntegral_preimage_emb τ.measurableEmbedding
    (fun y => conj (Fourier_wave L p y) * Φ y) (cellN L N)
  have hpre : τ ⁻¹' cellN L N = cellN L N := by
    ext x
    simp only [Set.mem_preimage, hτx, cellN, Set.mem_ofPred_eq, Function.comp_apply]
    exact ⟨fun h i => by simpa using h (σ i), fun h i => h _⟩
  simp only [hpre, hτx, Fourier_wave_comp, hs] at key
  exact key

/-! ### The normalization count -/

private lemma Fourier_count {N : ℕ} {α : Occ} (hα : α.num = N) :
    ((α.prod fun _ m => (m.factorial : ℝ)) / (N.factorial : ℝ)) * ((occFns N α).card : ℝ) = 1 := by
  set r : ℝ := (α.prod fun _ m => (m.factorial : ℝ)) / (N.factorial : ℝ) with hr
  have hr0 : 0 ≤ r := by
    rw [hr]
    refine div_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h := symWave_orthonormal (L := 1) one_pos hα hα
  simp only [ite_true] at h
  have hexp : ∀ x : Conf N, conj (symWave 1 N α x) * symWave 1 N α x =
      (r : ℂ) * ∑ q ∈ occFns N α, ∑ p ∈ occFns N α,
        conj (Fourier_wave 1 q x) * Fourier_wave 1 p x := by
    intro x
    have hs : ((Real.sqrt r : ℂ)) * (Real.sqrt r : ℂ) = (r : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr0]
    simp only [symWave, ← hr, map_mul, Complex.conj_ofReal, map_sum, Fourier_wave]
    calc _ = ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ)) *
          ((∑ q ∈ occFns N α, conj (∏ i, planeWave 1 (q i) (x i))) *
            ∑ p ∈ occFns N α, ∏ i, planeWave 1 (p i) (x i)) := by ring
      _ = _ := by rw [hs, Finset.sum_mul_sum]
  simp_rw [hexp] at h
  rw [integral_const_mul, integral_finsetSum _ fun q _ =>
    integrable_finsetSum _ fun p _ =>
      Fourier_integrableOn_wave_mul q (Fourier_wave_continuous 1 p)] at h
  have h2 : ∀ q : Fin N → Idx, ∫ x in cellN 1 N, ∑ p ∈ occFns N α,
      conj (Fourier_wave 1 q x) * Fourier_wave 1 p x =
        ∑ p ∈ occFns N α, if p = q then 1 else 0 := by
    intro q
    rw [integral_finsetSum _ fun p _ =>
      Fourier_integrableOn_wave_mul q (Fourier_wave_continuous 1 p)]
    exact Finset.sum_congr rfl fun p _ => Fourier_wave_orth one_pos p q
  simp only [h2, Finset.sum_ite_eq'] at h
  rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-! ### The wave function of the coefficient state -/

private lemma Fourier_occFns_eq {N R : ℕ} {α : Occ} (hα : α ∈ occBox N R) :
    occFns N α = (Fourier_box N R).filter fun p => occOf p = α := by
  obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.1 hα
  ext p
  rw [Fourier_mem_occFns, Finset.mem_filter]
  refine ⟨fun h => ⟨?_, h⟩, fun h => h.2⟩
  rw [Fourier_box, Fintype.mem_piFinset]
  intro i
  have h1 : 0 < occOf p₀ (p i) := by
    rw [← h, Fourier_occOf_apply]
    exact Finset.card_pos.2 ⟨i, by simp⟩
  rw [Fourier_occOf_apply] at h1
  obtain ⟨j, hj⟩ := Finset.card_pos.1 h1
  rw [Finset.mem_filter] at hj
  rw [← hj.2]
  exact Fintype.mem_piFinset.1 hp₀ j

private lemma Fourier_term {L : ℝ} {N R : ℕ} {Φ : Conf N → ℂ} (hc : Continuous Φ)
    (hs : ∀ σ : Equiv.Perm (Fin N), ∀ x, Φ (x ∘ σ) = Φ x) {α : Occ} (hα : α ∈ occBox N R)
    (x : Conf N) :
    coeffState L N R Φ α * symWave L N α x =
      ∑ p ∈ occFns N α, Fourier_coef L Φ p * Fourier_wave L p x := by
  obtain ⟨p₀, -, hp₀⟩ := Finset.mem_image.1 hα
  have hnum : α.num = N := hp₀ ▸ Fourier_num_occOf p₀
  have hconst : ∀ q ∈ occFns N α, Fourier_coef L Φ q = Fourier_coef L Φ p₀ := by
    intro q hq
    rw [Fourier_mem_occFns, ← hp₀] at hq
    obtain ⟨σ, rfl⟩ := Fourier_exists_perm hq
    exact Fourier_coef_comp L hs p₀ σ
  set r : ℝ := (α.prod fun _ m => (m.factorial : ℝ)) / (N.factorial : ℝ) with hr
  have hr0 : 0 ≤ r := by
    rw [hr]
    refine div_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hcount : (r : ℂ) * ((occFns N α).card : ℂ) = 1 := by
    have := Fourier_count hnum
    rw [← hr] at this
    exact_mod_cast this
  have hval : coeffState L N R Φ α =
      (Real.sqrt r : ℂ) * ((occFns N α).card : ℂ) * Fourier_coef L Φ p₀ := by
    rw [coeffState, Finsupp.indicator_of_mem hα]
    have hi : ∀ y : Conf N, conj (symWave L N α y) * Φ y =
        (Real.sqrt r : ℂ) * ∑ q ∈ occFns N α, conj (Fourier_wave L q y) * Φ y := by
      intro y
      simp only [symWave, ← hr, map_mul, Complex.conj_ofReal, map_sum, Finset.sum_mul,
        Finset.mul_sum, Fourier_wave]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    simp_rw [hi]
    rw [integral_const_mul, integral_finsetSum _ fun q _ => Fourier_integrableOn_wave_mul q hc]
    have h2 : ∑ q ∈ occFns N α, ∫ y in cellN L N, conj (Fourier_wave L q y) * Φ y =
        ∑ q ∈ occFns N α, Fourier_coef L Φ p₀ :=
      Finset.sum_congr rfl hconst
    rw [h2, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hval]
  have hsym : symWave L N α x = (Real.sqrt r : ℂ) * ∑ p ∈ occFns N α, Fourier_wave L p x := rfl
  rw [hsym, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hconst p hp]
  have hs2 : (Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) = (r : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hr0]
  calc _ = ((Real.sqrt r : ℂ) * (Real.sqrt r : ℂ) * ((occFns N α).card : ℂ)) *
        (Fourier_coef L Φ p₀ * Fourier_wave L p x) := by ring
    _ = _ := by rw [hs2, hcount, one_mul]

/-- For a continuous symmetric `Φ`, the wave function of the coefficient state is the projection
of `Φ` on the plane waves with momenta in the box:
`Φ_{Ψ_R}(x) = Σ_{p ∈ B_R^N} c(p) ∏_i e_{p_i}(x_i)`, `c(p) = ∫_{[0, L]^{3N}} conj(∏_i e_{p_i}) Φ`. -/
theorem stateFn_coeffState (L : ℝ) {N : ℕ} (R : ℕ) {Φ : Conf N → ℂ} (hc : Continuous Φ)
    (hs : ∀ σ : Equiv.Perm (Fin N), ∀ x, Φ (x ∘ σ) = Φ x) (x : Conf N) :
    stateFn L N (coeffState L N R Φ) x =
      ∑ p ∈ Fintype.piFinset (fun _ : Fin N => Finset.Icc (fun _ => -(R : ℤ)) (fun _ => (R : ℤ))),
        (∫ y in cellN L N, conj (∏ i, planeWave L (p i) (y i)) * Φ y) *
          ∏ i, planeWave L (p i) (x i) := by
  change _ = ∑ p ∈ Fourier_box N R, Fourier_coef L Φ p * Fourier_wave L p x
  unfold stateFn
  have hsub : (coeffState L N R Φ).support ⊆ occBox N R := Finsupp.support_indicator_subset _ _
  rw [Finset.sum_subset hsub fun α _ hα => by
    rw [Finsupp.notMem_support_iff.1 hα, zero_mul]]
  rw [Finset.sum_congr rfl fun α hα => Fourier_term hc hs hα x]
  have hmaps : ∀ p ∈ Fourier_box N R, occOf p ∈ occBox N R := fun p hp =>
    Finset.mem_image_of_mem occOf hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Fourier_occFns_eq hα]

/-! ### Projections in `L²([0, L]^{3N})` -/

private lemma Fourier_coef_proj {L : ℝ} (hL : 0 < L) {N : ℕ} (s : Finset (Fin N → Idx))
    (g : Conf N → ℂ) (q : Fin N → Idx) :
    Fourier_coef L (Fourier_proj L s g) q = if q ∈ s then Fourier_coef L g q else 0 := by
  change ∫ y in cellN L N, conj (Fourier_wave L q y) * Fourier_proj L s g y = _
  have h : ∀ p, ∫ y in cellN L N, conj (Fourier_wave L q y) *
      (Fourier_coef L g p * Fourier_wave L p y) = Fourier_coef L g p * if p = q then 1 else 0 := by
    intro p
    simp_rw [mul_left_comm (conj _) (Fourier_coef L g p)]
    rw [integral_const_mul, Fourier_wave_orth hL]
  simp only [Fourier_proj, Finset.mul_sum]
  rw [integral_finsetSum _ fun p _ => ?_]
  · simp_rw [h, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
  · exact Fourier_integrableOn_wave_mul q (continuous_const.mul (Fourier_wave_continuous L p))

private lemma Fourier_integral_conj_proj {L : ℝ} {N : ℕ} (s : Finset (Fin N → Idx))
    (h g : Conf N → ℂ) (hg : Continuous g) :
    ∫ x in cellN L N, conj (Fourier_proj L s h x) * g x =
      ∑ p ∈ s, conj (Fourier_coef L h p) * Fourier_coef L g p := by
  simp only [Fourier_proj, map_sum, map_mul, Finset.sum_mul]
  rw [integral_finsetSum _ fun p _ => ?_]
  · refine Finset.sum_congr rfl fun p _ => ?_
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    rfl
  · simp_rw [mul_assoc]
    exact (Fourier_integrableOn_wave_mul p hg).const_mul _

private lemma Fourier_ofReal_integral_norm_sq {N : ℕ} (S : Set (Conf N)) (u : Conf N → ℂ) :
    ((∫ x in S, ‖u x‖ ^ 2 : ℝ) : ℂ) = ∫ x in S, conj (u x) * u x := by
  simp_rw [Complex.conj_mul']
  rw [← integral_complex_ofReal]
  push_cast
  rfl

private lemma Fourier_integral_norm_proj {L : ℝ} (hL : 0 < L) {N : ℕ}
    (s : Finset (Fin N → Idx)) (g : Conf N → ℂ) :
    ∫ x in cellN L N, ‖Fourier_proj L s g x‖ ^ 2 = ∑ p ∈ s, ‖Fourier_coef L g p‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [Fourier_ofReal_integral_norm_sq, Fourier_integral_conj_proj _ _ _
    (Fourier_proj_continuous L s g)]
  push_cast
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Fourier_coef_proj hL, ite_eq_left_iff.2 fun h => absurd hp h, Complex.conj_mul']

private lemma Fourier_integral_norm_sub_proj {L : ℝ} (hL : 0 < L) {N : ℕ}
    (s : Finset (Fin N → Idx)) {g : Conf N → ℂ} (hg : Continuous g) :
    ∫ x in cellN L N, ‖Fourier_proj L s g x - g x‖ ^ 2 =
      (∫ x in cellN L N, ‖g x‖ ^ 2) - ∑ p ∈ s, ‖Fourier_coef L g p‖ ^ 2 := by
  set P := Fourier_proj L s g with hPdef
  have hP : Continuous P := Fourier_proj_continuous L s g
  set A : ℂ := ((∑ p ∈ s, ‖Fourier_coef L g p‖ ^ 2 : ℝ) : ℂ) with hA
  have e1 : ∫ x in cellN L N, conj (P x) * P x = A := by
    rw [← Fourier_ofReal_integral_norm_sq, Fourier_integral_norm_proj hL]
  have e2 : ∫ x in cellN L N, conj (P x) * g x = A := by
    rw [Fourier_integral_conj_proj _ _ _ hg, hA]
    push_cast
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.conj_mul']
  have e3 : ∫ x in cellN L N, conj (g x) * P x = A := by
    have h : ∀ x, conj (g x) * P x = conj (conj (P x) * g x) := fun x => by
      simp [mul_comm]
    simp_rw [h]
    rw [integral_conj, e2, hA, Complex.conj_ofReal]
  have hi : ∀ {u v : Conf N → ℂ}, Continuous u → Continuous v →
      Integrable (fun x => conj (u x) * v x) (volume.restrict (cellN L N)) :=
    fun hu hv => Fourier_integrableOn ((Complex.continuous_conj.comp hu).mul hv)
  apply Complex.ofReal_injective
  rw [Fourier_ofReal_integral_norm_sq]
  have hexp : ∀ x, conj (P x - g x) * (P x - g x) =
      (conj (P x) * P x - conj (P x) * g x) - (conj (g x) * P x - conj (g x) * g x) := by
    intro x
    rw [map_sub]
    ring
  simp_rw [hexp]
  rw [integral_sub ?h1 ?h2, integral_sub ?h3 ?h4, integral_sub ?h5 ?h6, e1, e2, e3,
    ← Fourier_ofReal_integral_norm_sq, hA]
  · push_cast
    ring
  all_goals first
    | exact (hi hP hP).sub (hi hP hg) | exact (hi hg hP).sub (hi hg hg)
    | exact hi hP hP | exact hi hP hg | exact hi hg hP | exact hi hg hg

/-! ### Transport to the unit torus `(ℝ/ℤ)^{3N}` -/

open scoped Pointwise

attribute [local instance] instMeasureSpaceUnitAddCircle

/-- The point of `(ℝ³)^N` with coordinates `t (i, a)`. -/
private def Fourier_flat {N : ℕ} (t : Fin N × Fin 3 → ℝ) : Conf N :=
  fun i => WithLp.toLp 2 (fun a => t (i, a))

private def Fourier_flatEquiv (N : ℕ) : (Fin N × Fin 3 → ℝ) ≃ᵐ Conf N :=
  (MeasurableEquiv.curry (Fin N) (Fin 3) ℝ).trans
    (MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

private lemma Fourier_curry_mp (N : ℕ) :
    MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin 3) ℝ) volume volume := by
  have h : MeasurePreserving (MeasurableEquiv.curry (Fin N) (Fin 3) ℝ).symm volume volume := by
    refine ⟨(MeasurableEquiv.curry (Fin N) (Fin 3) ℝ).symm.measurable, ?_⟩
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have hpre : (MeasurableEquiv.curry (Fin N) (Fin 3) ℝ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => Set.univ.pi fun a => s (i, a) := by
      ext t
      simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
    rw [hpre, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  simpa using h.symm

private lemma Fourier_flat_mp (N : ℕ) :
    MeasurePreserving (Fourier_flatEquiv N) volume volume :=
  (measurePreserving_pi (fun _ => volume) (fun _ => volume) fun _ =>
    PiLp.volume_preserving_toLp (Fin 3)).comp (Fourier_curry_mp N)

/-- The representative in `(0, 1]^{3N}` of a point of the unit torus. -/
private def Fourier_lift {N : ℕ} (z : UnitAddTorus (Fin N × Fin 3)) : Fin N × Fin 3 → ℝ :=
  (UnitAddTorus.measurableEquivPiIoc (fun _ => (0 : ℝ)) z).1

private lemma Fourier_lift_measurable (N : ℕ) : Measurable (Fourier_lift (N := N)) :=
  measurable_subtype_coe.comp (MeasurableEquiv.measurable _)

private lemma Fourier_lift_mem {N : ℕ} (z : UnitAddTorus (Fin N × Fin 3)) (j : Fin N × Fin 3) :
    Fourier_lift z j ∈ Set.Ioc (0 : ℝ) 1 := by
  have := (UnitAddTorus.measurableEquivPiIoc (fun _ => (0 : ℝ)) z).2 j
  simpa [Fourier_lift] using this

private lemma Fourier_lift_coe {N : ℕ} (z : UnitAddTorus (Fin N × Fin 3)) (j : Fin N × Fin 3) :
    ((Fourier_lift z j : ℝ) : UnitAddCircle) = z j :=
  AddCircle.coe_equivIoc

private lemma Fourier_lift_of_mem {N : ℕ} {t : Fin N × Fin 3 → ℝ}
    (ht : ∀ j, t j ∈ Set.Ioc (0 : ℝ) 1) :
    Fourier_lift (fun j => (t j : UnitAddCircle)) = t := by
  have := (UnitAddTorus.measurableEquivPiIoc (fun _ => (0 : ℝ))).apply_symm_apply
    ⟨t, fun j => by simpa using ht j⟩
  exact congrArg Subtype.val this

/-- `∫_{[0, L]^{3N}} F = L^{3N} ∫_{(ℝ/ℤ)^{3N}} F(L t)`. -/
private lemma Fourier_integral_cellN {L : ℝ} (hL : 0 < L) {N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (F : Conf N → E) :
    ∫ x in cellN L N, F x =
      (L ^ (3 * N)) •
        ∫ z : UnitAddTorus (Fin N × Fin 3), F (Fourier_flat (L • Fourier_lift z)) := by
  have h1 : ∫ z : UnitAddTorus (Fin N × Fin 3), F (Fourier_flat (L • Fourier_lift z)) =
      (L ^ (N * 3))⁻¹ • ∫ x in cellN L N, F x := by
    rw [UnitAddTorus.integral_preimage _ 0]
    have hset : {x : Fin N × Fin 3 → ℝ | ∀ i, x i ∈ Set.Ioc ((0 : Fin N × Fin 3 → ℝ) i)
        ((0 : Fin N × Fin 3 → ℝ) i + 1)} = Set.univ.pi fun _ => Set.Ioc 0 1 := by
      ext t
      simp
    rw [hset]
    have hS : MeasurableSet (Set.univ.pi fun _ : Fin N × Fin 3 => Set.Ioc (0 : ℝ) 1) :=
      MeasurableSet.univ_pi fun _ => measurableSet_Ioc
    rw [setIntegral_congr_fun hS fun t ht => by
      rw [Fourier_lift_of_mem fun j => ht j (Set.mem_univ j)]]
    have key := Measure.setIntegral_comp_smul_of_pos volume (fun s => F (Fourier_flat s))
      (Set.univ.pi fun _ : Fin N × Fin 3 => Set.Ioc (0 : ℝ) 1) hL
    rw [key, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin]
    congr 1
    have hsmul : L • (Set.univ.pi fun _ : Fin N × Fin 3 => Set.Ioc (0 : ℝ) 1) =
        Set.univ.pi fun j => Set.Ioc ((0 : Fin N × Fin 3 → ℝ) j) L := by
      ext t
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ hL.ne']
      simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc, Pi.smul_apply,
        smul_eq_mul, Pi.zero_apply]
      refine forall_congr' fun j => ?_
      constructor
      · rintro ⟨h1, h2⟩
        constructor
        · by_contra h
          push Not at h
          have : L⁻¹ * t j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hL.le) h
          linarith
        · have := mul_le_mul_of_nonneg_left h2 hL.le
          rwa [← mul_assoc, mul_inv_cancel₀ hL.ne', one_mul, mul_one] at this
      · rintro ⟨h1, h2⟩
        exact ⟨mul_pos (inv_pos.2 hL) h1, by
          rw [inv_mul_le_iff₀ hL, mul_one]; exact h2⟩
    have hae : (Set.univ.pi fun j => Set.Ioc ((0 : Fin N × Fin 3 → ℝ) j) L) =ᵐ[volume]
        Set.Icc (0 : Fin N × Fin 3 → ℝ) (fun _ => L) :=
      Measure.univ_pi_Ioc_ae_eq_Icc
    rw [hsmul, setIntegral_congr_set hae]
    have hpre : Set.Icc (0 : Fin N × Fin 3 → ℝ) (fun _ => L) =
        Fourier_flatEquiv N ⁻¹' cellN L N := by
      ext t
      simp only [Set.mem_Icc, Set.mem_preimage, Fourier_flat, cellN,
        cell, Set.mem_ofPred_eq, Pi.le_def, Pi.zero_apply, Prod.forall]
      constructor
      · rintro ⟨h1, h2⟩ i a
        exact ⟨h1 i a, h2 i a⟩
      · intro h
        exact ⟨fun i a => (h i a).1, fun i a => (h i a).2⟩
    rw [hpre]
    exact (Fourier_flat_mp N).setIntegral_preimage_emb
      (Fourier_flatEquiv N).measurableEmbedding F (cellN L N)
  rw [h1, smul_smul, mul_comm 3 N, mul_inv_cancel₀ (pow_ne_zero _ hL.ne'), one_smul]

/-! ### Parseval on `[0, L]^{3N}` -/

private lemma Fourier_wave_flat {L : ℝ} (hL : 0 < L) {N : ℕ} (p : Fin N → Idx)
    (z : UnitAddTorus (Fin N × Fin 3)) :
    conj (Fourier_wave L p (Fourier_flat (L • Fourier_lift z))) =
      (((Real.sqrt (L ^ 3))⁻¹ ^ N : ℝ) : ℂ) * UnitAddTorus.mFourier (-Function.uncurry p) z := by
  set t := Fourier_lift z
  have hz : z = fun j => ((t j : ℝ) : UnitAddCircle) :=
    funext fun j => (Fourier_lift_coe z j).symm
  have hR : UnitAddTorus.mFourier (-Function.uncurry p) z =
      ∏ i, ∏ a : Fin 3, Complex.exp (2 * π * Complex.I * (((-(p i a) : ℤ) : ℂ)) *
        ((t (i, a) : ℝ) : ℂ) / ((1 : ℝ) : ℂ)) := by
    conv_lhs => rw [hz]
    change ∏ j, fourier _ _ = _
    rw [Fintype.prod_prod_type]
    simp only [Pi.neg_apply, Function.uncurry_apply_pair, fourier_coe_apply]
  rw [hR]
  have hc : (((Real.sqrt (L ^ 3))⁻¹ ^ N : ℝ) : ℂ) =
      ∏ _i : Fin N, (((Real.sqrt (L ^ 3))⁻¹ : ℝ) : ℂ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Complex.ofReal_pow]
  rw [hc, ← Finset.prod_mul_distrib]
  unfold Fourier_wave
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold planeWave
  rw [map_mul, ← Complex.exp_conj, ← Complex.exp_sum]
  congr 1
  · simp
  · simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fourier_flat,
      Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hm : (mom L (p i)).ofLp a = 2 * π / L * (p i a : ℝ) := rfl
    rw [hm]
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp

/-- Parseval for continuous `g`: `Σ_p |c_p(g)|² = ∫_{[0, L]^{3N}} |g|²`. -/
private lemma Fourier_parseval {L : ℝ} (hL : 0 < L) {N : ℕ} {g : Conf N → ℂ}
    (hg : Continuous g) :
    HasSum (fun p => ‖Fourier_coef L g p‖ ^ 2) (∫ x in cellN L N, ‖g x‖ ^ 2) := by
  have : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
  set G : UnitAddTorus (Fin N × Fin 3) → ℂ := fun z => g (Fourier_flat (L • Fourier_lift z))
    with hGdef
  have hmem : ∀ z, Fourier_flat (L • Fourier_lift z) ∈ cellN L N := by
    intro z i a
    have h := Fourier_lift_mem z (i, a)
    simp only [Fourier_flat, Pi.smul_apply, smul_eq_mul, PiLp.toLp_apply]
    constructor
    · exact mul_nonneg hL.le h.1.le
    · calc L * Fourier_lift z (i, a) ≤ L * 1 := mul_le_mul_of_nonneg_left h.2 hL.le
        _ = L := mul_one L
  obtain ⟨C, hC⟩ := (Fourier_isCompact_cellN L N).exists_bound_of_continuousOn hg.continuousOn
  have hGm : Measurable G := hg.measurable.comp ((Fourier_flatEquiv N).measurable.comp
    ((measurable_const_smul L).comp (Fourier_lift_measurable N)))
  have hG : MemLp G 2 volume :=
    MemLp.of_bound hGm.aestronglyMeasurable C (ae_of_all _ fun z => hC _ (hmem z))
  have hP := UnitAddTorus.hasSum_sq_mFourierCoeff (hG.toLp G)
  have h1 : ∀ n, UnitAddTorus.mFourierCoeff (hG.toLp G) n = UnitAddTorus.mFourierCoeff G n :=
    fun n => integral_congr_ae (by filter_upwards [hG.coeFn_toLp] with z hz; rw [hz])
  have h2 : ∫ t, ‖(hG.toLp G) t‖ ^ 2 = ∫ t, ‖G t‖ ^ 2 :=
    integral_congr_ae (by filter_upwards [hG.coeFn_toLp] with z hz; rw [hz])
  simp only [h1, h2] at hP
  have hn : ∫ x in cellN L N, ‖g x‖ ^ 2 = L ^ (3 * N) * ∫ z, ‖G z‖ ^ 2 := by
    rw [Fourier_integral_cellN hL, smul_eq_mul]
  have hc : ∀ p : Fin N → Idx, ‖Fourier_coef L g p‖ ^ 2 =
      L ^ (3 * N) * ‖UnitAddTorus.mFourierCoeff G (Function.uncurry p)‖ ^ 2 := by
    intro p
    have hcoef : Fourier_coef L g p = ((L ^ (3 * N) * (Real.sqrt (L ^ 3))⁻¹ ^ N : ℝ) : ℂ) *
        UnitAddTorus.mFourierCoeff G (Function.uncurry p) := by
      rw [Fourier_coef, Fourier_integral_cellN hL]
      simp_rw [Fourier_wave_flat hL, mul_assoc]
      rw [integral_const_mul, Complex.real_smul]
      unfold UnitAddTorus.mFourierCoeff
      simp only [smul_eq_mul]
      push_cast
      ring
    have hs : (Real.sqrt (L ^ 3))⁻¹ ^ 2 = (L ^ 3)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (by positivity)]
    have hk : (L ^ (3 * N)) ^ 2 * ((Real.sqrt (L ^ 3))⁻¹ ^ N) ^ 2 = L ^ (3 * N) := by
      have hL3 : L ^ (3 * N) ≠ 0 := pow_ne_zero _ hL.ne'
      rw [← pow_mul (Real.sqrt (L ^ 3))⁻¹ N 2, mul_comm N 2, pow_mul (Real.sqrt (L ^ 3))⁻¹ 2 N,
        hs, inv_pow, ← pow_mul L 3 N, sq, mul_assoc, mul_inv_cancel₀ hL3, mul_one]
    rw [hcoef, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, hk]
  rw [hn]
  simp_rw [hc]
  exact (Equiv.hasSum_iff (Equiv.curry (Fin N) (Fin 3) ℤ).symm).mpr (hP.mul_left _)

private lemma Fourier_box_mono {N : ℕ} : Monotone (Fourier_box N) := by
  intro R R' h p hp
  rw [Fourier_box, Fintype.mem_piFinset] at hp ⊢
  intro i
  have hi := Finset.mem_Icc.1 (hp i)
  have h' : (R : ℤ) ≤ R' := by exact_mod_cast h
  refine Finset.mem_Icc.2 ⟨fun a => ?_, fun a => ?_⟩
  · have := hi.1 a
    simp only at this ⊢
    omega
  · have := hi.2 a
    simp only at this ⊢
    omega

private lemma Fourier_mem_box {N : ℕ} (p : Fin N → Idx) : ∃ R, p ∈ Fourier_box N R := by
  refine ⟨∑ i, ∑ a, (p i a).natAbs, ?_⟩
  rw [Fourier_box, Fintype.mem_piFinset]
  intro i
  have h : ∀ a, |p i a| ≤ ((∑ i, ∑ a, (p i a).natAbs : ℕ) : ℤ) := by
    intro a
    have h1 : (p i a).natAbs ≤ ∑ a, (p i a).natAbs :=
      Finset.single_le_sum (f := fun a => (p i a).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ a)
    have h2 : ∑ a, (p i a).natAbs ≤ ∑ i, ∑ a, (p i a).natAbs :=
      Finset.single_le_sum (f := fun i => ∑ a, (p i a).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    rw [← Int.natCast_natAbs]
    exact_mod_cast h1.trans h2
  refine Finset.mem_Icc.2 ⟨fun a => ?_, fun a => ?_⟩
  · exact (abs_le.1 (h a)).1
  · exact (abs_le.1 (h a)).2

private lemma Fourier_tendsto_box {N : ℕ} {f : (Fin N → Idx) → ℝ} {a : ℝ} (hf : HasSum f a) :
    Tendsto (fun R : ℕ => ∑ p ∈ Fourier_box N R, f p) atTop (𝓝 a) :=
  (show Tendsto (fun s => ∑ p ∈ s, f p) atTop (𝓝 a) from hf).comp
    (tendsto_atTop_finset_of_monotone Fourier_box_mono Fourier_mem_box)

private lemma Fourier_stateFn_eq (L : ℝ) {N : ℕ} (R : ℕ) {Φ : Conf N → ℂ} (hc : Continuous Φ)
    (hs : ∀ σ : Equiv.Perm (Fin N), ∀ x, Φ (x ∘ σ) = Φ x) :
    stateFn L N (coeffState L N R Φ) = Fourier_proj L (Fourier_box N R) Φ :=
  funext fun x => stateFn_coeffState L R hc hs x

/-- Parseval on `[0, L]^{3N}`: for a continuous symmetric `Φ`, the wave functions of the
coefficient states converge to `Φ` in `L²([0, L]^{3N})` as the box grows. -/
theorem coeffState_tendsto_norm {L : ℝ} (hL : 0 < L) {N : ℕ} {Φ : Conf N → ℂ}
    (hc : Continuous Φ) (hs : ∀ σ : Equiv.Perm (Fin N), ∀ x, Φ (x ∘ σ) = Φ x) :
    Tendsto (fun R : ℕ => ∫ x in cellN L N,
      ‖stateFn L N (coeffState L N R Φ) x - Φ x‖ ^ 2) atTop (𝓝 0) := by
  simp_rw [Fourier_stateFn_eq L _ hc hs, Fourier_integral_norm_sub_proj hL _ hc]
  have h := (tendsto_const_nhds (x := ∫ x in cellN L N, ‖Φ x‖ ^ 2)).sub
    (Fourier_tendsto_box (N := N) (Fourier_parseval hL hc))
  rwa [sub_self] at h

/-! ### Derivatives and integration by parts -/

private lemma Fourier_integral_sum_sum {L : ℝ} {N : ℕ} (f : Fin N → Fin 3 → Conf N → ℝ)
    (hf : ∀ i a, Continuous (f i a)) :
    ∫ x in cellN L N, ∑ i, ∑ a, f i a x = ∑ i, ∑ a, ∫ x in cellN L N, f i a x := by
  rw [integral_finsetSum _ fun i _ => ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun a _ => Fourier_integrableOn (hf i a)]
  · exact integrable_finsetSum _ fun a _ => Fourier_integrableOn (hf i a)

/-- The phase `ℓ_p(x) = Σ_i ⟨k_{p_i}, x_i⟩` of `e_p`. -/
private def Fourier_lin (L : ℝ) {N : ℕ} (p : Fin N → Idx) : Conf N →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (mom L (p i))).comp (ContinuousLinearMap.proj i)

private lemma Fourier_lin_apply (L : ℝ) {N : ℕ} (p : Fin N → Idx) (x : Conf N) :
    Fourier_lin L p x = ∑ i, inner ℝ (mom L (p i)) (x i) := by
  simp [Fourier_lin]

private lemma Fourier_lin_single (L : ℝ) {N : ℕ} (p : Fin N → Idx) (i : Fin N) (a : Fin 3) :
    Fourier_lin L p (Pi.single i (EuclideanSpace.single a 1)) = (mom L (p i)) a := by
  rw [Fourier_lin_apply, Finset.sum_eq_single i]
  · simp [EuclideanSpace.inner_single_right]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

private lemma Fourier_wave_eq (L : ℝ) {N : ℕ} (p : Fin N → Idx) (x : Conf N) :
    Fourier_wave L p x =
      ((Real.sqrt (L ^ 3))⁻¹ : ℂ) ^ N * Complex.exp (Complex.I * (Fourier_lin L p x : ℂ)) := by
  rw [Fourier_lin_apply]
  unfold Fourier_wave planeWave
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Complex.exp_sum]
  push_cast
  rw [Finset.mul_sum]

private lemma Fourier_wave_hasFDerivAt (L : ℝ) {N : ℕ} (p : Fin N → Idx) (x : Conf N) :
    HasFDerivAt (Fourier_wave L p)
      ((((Real.sqrt (L ^ 3))⁻¹ : ℂ) ^ N) • (Complex.exp (Complex.I * (Fourier_lin L p x : ℂ)) •
        (Complex.I • (Complex.ofRealCLM.comp (Fourier_lin L p))))) x := by
  have h := (((Complex.ofRealCLM.comp (Fourier_lin L p)).hasFDerivAt (x := x)).const_mul
    Complex.I).cexp.const_mul (((Real.sqrt (L ^ 3))⁻¹ : ℂ) ^ N)
  have hf : Fourier_wave L p = fun y => ((Real.sqrt (L ^ 3))⁻¹ : ℂ) ^ N *
      Complex.exp (Complex.I * (Complex.ofRealCLM.comp (Fourier_lin L p) y)) :=
    funext fun y => by rw [Fourier_wave_eq]; rfl
  rw [hf]
  exact h

private lemma Fourier_wave_fderiv (L : ℝ) {N : ℕ} (p : Fin N → Idx) (x w : Conf N) :
    fderiv ℝ (Fourier_wave L p) x w = Complex.I * (Fourier_lin L p w : ℂ) * Fourier_wave L p x := by
  rw [(Fourier_wave_hasFDerivAt L p x).fderiv, Fourier_wave_eq]
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  ring

private lemma Fourier_conj_wave (L : ℝ) {N : ℕ} (p : Fin N → Idx) (x : Conf N) :
    conj (Fourier_wave L p x) = Fourier_wave L (-p) x := by
  unfold Fourier_wave
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  unfold planeWave
  rw [map_mul, ← Complex.exp_conj]
  have hm : mom L ((-p) i) = -mom L (p i) := by
    ext a
    simp [mom]
  rw [hm, inner_neg_left]
  simp

/-- Integration by parts against `conj e_p`:
`c_p(∂_{x_i^a} Φ) = i (k_{p_i})_a c_p(Φ)` for `Φ` supported in the open box. -/
private lemma Fourier_coef_deriv {L : ℝ} {N : ℕ} {Φ : Conf N → ℂ}
    (hd : ContDiff ℝ 1 Φ) (hΦ : tsupport Φ ⊆ {x | ∀ i a, 0 < (x i) a ∧ (x i) a < L})
    (p : Fin N → Idx) (i : Fin N) (a : Fin 3) :
    Fourier_coef L (fun x => fderiv ℝ Φ x (Pi.single i (EuclideanSpace.single a 1))) p =
      Complex.I * ((mom L (p i)) a : ℂ) * Fourier_coef L Φ p := by
  set v : Conf N := Pi.single i (EuclideanSpace.single a 1) with hv
  have hsub : tsupport Φ ⊆ cellN L N := fun x hx j b => ⟨(hΦ hx j b).1.le, (hΦ hx j b).2.le⟩
  have hK : HasCompactSupport Φ :=
    IsCompact.of_isClosed_subset (Fourier_isCompact_cellN L N) (isClosed_tsupport Φ) hsub
  have hdiff : Differentiable ℝ Φ := hd.differentiable one_ne_zero
  have hzero : ∀ x ∉ cellN L N, Φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h => hx (hsub h)
  have hDzero : ∀ x ∉ cellN L N, fderiv ℝ Φ x v = 0 := by
    intro x hx
    have h0 : fderiv ℝ Φ x = 0 :=
      Function.notMem_support.1 fun h => hx (hsub (support_fderiv_subset ℝ h))
    rw [h0, zero_apply]
  have hneg : (mom L ((-p) i)) a = -(mom L (p i)) a := by
    simp [mom]
  have hderiv : ∀ x, fderiv ℝ (Fourier_wave L (-p)) x v =
      -(Complex.I * ((mom L (p i)) a : ℂ)) * Fourier_wave L (-p) x := by
    intro x
    rw [Fourier_wave_fderiv, hv, Fourier_lin_single, hneg]
    push_cast
    ring
  have hc1 : Continuous fun x => fderiv ℝ Φ x v :=
    (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hw := Fourier_wave_continuous L (-p)
  have i1 : Integrable fun x => fderiv ℝ (Fourier_wave L (-p)) x v * Φ x := by
    simp_rw [hderiv]
    exact ((continuous_const.mul hw).mul hd.continuous).integrable_of_hasCompactSupport
      hK.mul_left
  have i2 : Integrable fun x => Fourier_wave L (-p) x * fderiv ℝ Φ x v :=
    (hw.mul hc1).integrable_of_hasCompactSupport (hK.fderiv_apply ℝ v).mul_left
  have i3 : Integrable fun x => Fourier_wave L (-p) x * Φ x :=
    (hw.mul hd.continuous).integrable_of_hasCompactSupport hK.mul_left
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable i1 i2 i3
    (fun x _ => (Fourier_wave_hasFDerivAt L (-p) x).differentiableAt) (fun x _ => hdiff x)
  have hL1 : Fourier_coef L (fun x => fderiv ℝ Φ x v) p =
      ∫ x, Fourier_wave L (-p) x * fderiv ℝ Φ x v := by
    rw [Fourier_coef]
    simp_rw [Fourier_conj_wave]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hDzero x hx, mul_zero]
  have hL2 : Fourier_coef L Φ p = ∫ x, Fourier_wave L (-p) x * Φ x := by
    rw [Fourier_coef]
    simp_rw [Fourier_conj_wave]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hzero x hx, mul_zero]
  rw [hL1, hibp, hL2]
  simp_rw [hderiv, mul_assoc]
  rw [integral_const_mul]
  ring

private lemma Fourier_proj_fderiv {L : ℝ} {N : ℕ} {Φ : Conf N → ℂ}
    (hd : ContDiff ℝ 1 Φ) (hΦ : tsupport Φ ⊆ {x | ∀ i a, 0 < (x i) a ∧ (x i) a < L})
    (s : Finset (Fin N → Idx)) (i : Fin N) (a : Fin 3) (x : Conf N) :
    fderiv ℝ (Fourier_proj L s Φ) x (Pi.single i (EuclideanSpace.single a 1)) =
      Fourier_proj L s (fun y => fderiv ℝ Φ y (Pi.single i (EuclideanSpace.single a 1))) x := by
  have h : HasFDerivAt (Fourier_proj L s Φ)
      (∑ p ∈ s, Fourier_coef L Φ p • fderiv ℝ (Fourier_wave L p) x) x :=
    HasFDerivAt.fun_sum (u := s) (A := fun p y => Fourier_coef L Φ p * Fourier_wave L p y)
      fun p _ => ((Fourier_wave_hasFDerivAt L p x).differentiableAt.hasFDerivAt).const_mul
        (Fourier_coef L Φ p)
  rw [h.fderiv, sum_apply]
  unfold Fourier_proj
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_apply, Fourier_wave_fderiv, Fourier_coef_deriv hd hΦ,
    Fourier_lin_single, smul_eq_mul]
  ring

/-- For a `C¹` symmetric `Φ` supported in the open box `(0, L)^{3N}`, the kinetic energies
`∫_{[0, L]^{3N}} Σ_i |∇_i Φ_{Ψ_R}|²` of the coefficient states converge to that of `Φ` as the
box grows. -/
theorem coeffState_tendsto_kin {L : ℝ} (hL : 0 < L) {N : ℕ} {Φ : Conf N → ℂ}
    (hd : ContDiff ℝ 1 Φ) (hs : ∀ σ : Equiv.Perm (Fin N), ∀ x, Φ (x ∘ σ) = Φ x)
    (hΦ : tsupport Φ ⊆ {x | ∀ i a, 0 < (x i) a ∧ (x i) a < L}) :
    Tendsto (fun R : ℕ => ∫ x in cellN L N,
      kinD (stateFn L N (coeffState L N R Φ)) x) atTop
        (𝓝 (∫ x in cellN L N, kinD Φ x)) := by
  have hD : ∀ (i : Fin N) (a : Fin 3),
      Continuous fun x => fderiv ℝ Φ x (Pi.single i (EuclideanSpace.single a 1)) :=
    fun i a => (hd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hR : ∀ R : ℕ, ∫ x in cellN L N, kinD (stateFn L N (coeffState L N R Φ)) x =
      ∑ i, ∑ a : Fin 3, ∑ p ∈ Fourier_box N R, ‖Fourier_coef L
        (fun y => fderiv ℝ Φ y (Pi.single i (EuclideanSpace.single a 1))) p‖ ^ 2 := by
    intro R
    rw [Fourier_stateFn_eq L R hd.continuous hs]
    unfold kinD
    simp_rw [Fourier_proj_fderiv hd hΦ]
    refine (Fourier_integral_sum_sum (fun i a x => ‖Fourier_proj L (Fourier_box N R)
      (fun y => fderiv ℝ Φ y (Pi.single i (EuclideanSpace.single a 1))) x‖ ^ 2)
      fun i a => (Fourier_proj_continuous L _ _).norm.pow 2).trans ?_
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
      Fourier_integral_norm_proj hL _ _
  have h0 : ∫ x in cellN L N, kinD Φ x = ∑ i, ∑ a : Fin 3, ∫ x in cellN L N,
      ‖fderiv ℝ Φ x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2 := by
    unfold kinD
    exact Fourier_integral_sum_sum (fun i a x =>
      ‖fderiv ℝ Φ x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2) fun i a => (hD i a).norm.pow 2
  simp_rw [hR]
  rw [h0]
  exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun a _ =>
    Fourier_tendsto_box (Fourier_parseval hL (hD i a))

end LHYUpper
