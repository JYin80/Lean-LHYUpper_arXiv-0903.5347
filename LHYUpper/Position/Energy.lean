import LHYUpper.Scattering.Solution
import LHYUpper.Position.SymWave
import LHYUpper.Position.Periodize

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- The energy of (2.1) [ham] in position space on the torus `[0, L]³`:
`∫_{[0, L]^{3N}} Σ_i |∇_i Φ|² + Σ_{i ≠ j} V^P(x_i - x_j) |Φ|²`. -/
def torusEnergy (L : ℝ) (V : R3 → ℝ) {N : ℕ} (Φ : Conf N → ℂ) : ℝ :=
  ∫ x in cellN L N, (kinD Φ x + pairPot (periodize L V) x * ‖Φ x‖ ^ 2)

/-! Position form of the Hamiltonian (2.1) [ham] on the torus `[0, L]³`: for a finitely supported
`N`-particle state `Ψ`, the kinetic and interaction series of `⟨Ψ, H Ψ⟩` add up to the kinetic and
interaction integrals of `Φ_Ψ` over `[0, L]^{3N}`, with the periodized potential
`V^P = Σ_n V(· + nL)` of §12; consequently `H ≥ 0` on finitely supported states. -/

/-! ### Integration over the period cells -/

private lemma Energy_isCompact_cell (L : ℝ) : IsCompact (cell L) := by
  have h : cell L = (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin 3 => Set.Icc 0 L) := by
    ext y
    constructor
    · intro hy
      exact ⟨WithLp.ofLp y, fun a _ => hy a, by simp⟩
    · rintro ⟨z, hz, rfl⟩ a
      exact hz a (Set.mem_univ a)
  rw [h]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

private lemma Energy_cellN_eq (L : ℝ) (N : ℕ) :
    cellN L N = Set.pi Set.univ fun _ : Fin N => cell L := by
  ext x
  simp [cellN]

private lemma Energy_isCompact_cellN (L : ℝ) (N : ℕ) : IsCompact (cellN L N) := by
  rw [Energy_cellN_eq]
  exact isCompact_univ_pi fun _ => Energy_isCompact_cell L

private lemma Energy_integrable {E : Type*} [NormedAddCommGroup E] (L : ℝ) {N : ℕ}
    {f : Conf N → E} (hf : Continuous f) : Integrable f (volume.restrict (cellN L N)) :=
  hf.continuousOn.integrableOn_compact (Energy_isCompact_cellN L N)

/-- Splitting off the last particle in an integral over `[0, L]^{3(N+1)}`. -/
private lemma Energy_integral_cellN_succ (L : ℝ) (N : ℕ) (f : Conf (N + 1) → ℂ) :
    ∫ x in cellN L (N + 1), f x =
      ∫ z in cell L ×ˢ cellN L N, f (Fin.snoc z.2 z.1) ∂((volume : Measure R3).prod
        (volume : Measure (Conf N))) := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (N + 1) => (volume : Measure R3))
    (Fin.last N)
  have key := hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _)
    (fun z : R3 × (Fin N → R3) => f (Fin.snoc z.2 z.1)) (cell L ×ˢ cellN L N)
  have hset : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => R3) (Fin.last N)) ⁻¹'
      (cell L ×ˢ cellN L N) = cellN L (N + 1) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_prod, cellN, Set.mem_ofPred_eq,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Equiv.coe_fn_symm_mk]
    rw [Fin.forall_fin_succ', and_comm]
    simp [Fin.removeNth]
  have hf : ∀ x : Conf (N + 1),
      f (Fin.snoc ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => R3) (Fin.last N)) x).2
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 1) => R3) (Fin.last N)) x).1) = f x := by
    intro x
    congr 1
    simp only [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Equiv.coe_fn_symm_mk]
    have h : (Fin.last N).removeNth x = Fin.init x := by
      funext j
      simp [Fin.removeNth, Fin.init]
    rw [h]
    exact Fin.snoc_init_self x
  simp_rw [hf, hset] at key
  exact key

/-! ### Product plane waves -/

/-- The product wave `w_P(x) = ∏_i e_{P_i}(x_i)` of an assignment `P` of momenta. -/
private def Energy_pw (L : ℝ) {N : ℕ} (P : Fin N → Idx) (x : Conf N) : ℂ :=
  ∏ i, planeWave L (P i) (x i)

private lemma Energy_planeWave_continuous (L : ℝ) (n : Idx) : Continuous (planeWave L n) := by
  unfold planeWave
  refine continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul ?_))
  exact Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)

private lemma Energy_pw_continuous (L : ℝ) {N : ℕ} (P : Fin N → Idx) :
    Continuous (Energy_pw L P) := by
  unfold Energy_pw
  exact continuous_finsetProd _ fun i _ =>
    (Energy_planeWave_continuous L (P i)).comp (continuous_apply i)

/-- The product waves are orthonormal in `L²([0, L]^{3N})`. -/
private lemma Energy_pw_orthonormal {L : ℝ} (hL : 0 < L) {N : ℕ} (P P' : Fin N → Idx) :
    ∫ x in cellN L N, conj (Energy_pw L P' x) * Energy_pw L P x = if P' = P then 1 else 0 := by
  have h1 : ∀ x : Conf N, conj (Energy_pw L P' x) * Energy_pw L P x =
      ∏ i, (conj (planeWave L (P' i) (x i)) * planeWave L (P i) (x i)) := by
    intro x
    simp only [Energy_pw, map_prod, Finset.prod_mul_distrib]
  simp_rw [h1, Energy_cellN_eq]
  have hvol : (volume : Measure (Conf N)) = Measure.pi fun _ => volume := rfl
  rw [hvol, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (i : Fin N) (y : R3) =>
      conj (planeWave L (P' i) y) * planeWave L (P i) y)]
  simp_rw [planeWave_orthonormal hL]
  rw [Finset.prod_boole]
  simp [funext_iff]

/-- Parseval for product waves with pairwise different assignments. -/
private lemma Energy_parseval {L : ℝ} (hL : 0 < L) {N : ℕ} {ι : Type*} (T : Finset ι)
    (e : ι → Fin N → Idx) (he : Set.InjOn e T) (g : ι → ℂ) :
    ∫ x in cellN L N, ‖∑ t ∈ T, g t * Energy_pw L (e t) x‖ ^ 2 = ∑ t ∈ T, ‖g t‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h1 : ∀ x : Conf N, (((‖∑ t ∈ T, g t * Energy_pw L (e t) x‖ ^ 2 : ℝ)) : ℂ) =
      ∑ t' ∈ T, ∑ t ∈ T,
        (conj (g t') * g t) * (conj (Energy_pw L (e t') x) * Energy_pw L (e t) x) := by
    intro x
    have h := Complex.conj_mul' (∑ t ∈ T, g t * Energy_pw L (e t) x)
    push_cast
    rw [← h, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun t' _ => Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul]
    ring
  simp_rw [h1]
  have hint : ∀ t' t, Integrable (fun x : Conf N =>
      (conj (g t') * g t) * (conj (Energy_pw L (e t') x) * Energy_pw L (e t) x))
      (volume.restrict (cellN L N)) := fun t' t =>
    Energy_integrable L (continuous_const.mul
      ((Complex.continuous_conj.comp (Energy_pw_continuous L _)).mul (Energy_pw_continuous L _)))
  rw [integral_finsetSum _ fun t' _ => integrable_finsetSum _ fun t _ => hint t' t]
  push_cast
  refine Finset.sum_congr rfl fun t' ht' => ?_
  rw [integral_finsetSum _ fun t _ => hint t' t, Finset.sum_eq_single t']
  · rw [integral_const_mul, Energy_pw_orthonormal hL]
    simp [Complex.conj_mul']
  · intro t ht hne
    rw [integral_const_mul, Energy_pw_orthonormal hL]
    have : e t' ≠ e t := fun h => hne (he ht ht' h.symm)
    simp [this]
  · intro h
    exact absurd ht' h

/-! ### Symmetrized plane waves as sums of product waves -/

/-- The normalization `∏_k α(k)! / N!` of `Φ_α`. -/
private def Energy_c (N : ℕ) (α : Occ) : ℝ :=
  (α.prod fun _ m => (m.factorial : ℝ)) / (N.factorial : ℝ)

private lemma Energy_c_nonneg (N : ℕ) (α : Occ) : 0 ≤ Energy_c N α := by
  unfold Energy_c Finsupp.prod
  exact div_nonneg (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _) (Nat.cast_nonneg _)

private lemma Energy_symWave_eq (L : ℝ) (N : ℕ) (α : Occ) (x : Conf N) :
    symWave L N α x = ∑ P ∈ occFns N α, (Real.sqrt (Energy_c N α) : ℂ) * Energy_pw L P x := by
  rw [symWave, Finset.mul_sum]
  rfl

private lemma Energy_mem_occFns {N : ℕ} {α : Occ} {P : Fin N → Idx} (hP : P ∈ occFns N α)
    (k : Idx) : (Finset.univ.filter fun i => P i = k).card = α k :=
  (Finset.mem_filter.1 hP).2 k

private lemma Energy_occFns_inj {N : ℕ} {α β : Occ} {P : Fin N → Idx} (hα : P ∈ occFns N α)
    (hβ : P ∈ occFns N β) : α = β := by
  ext k
  rw [← Energy_mem_occFns hα k, ← Energy_mem_occFns hβ k]

private lemma Energy_occFns_maps {N : ℕ} {α : Occ} {P : Fin N → Idx} (hP : P ∈ occFns N α)
    (i : Fin N) : P i ∈ α.support :=
  Fintype.mem_piFinset.1 (Finset.mem_filter.1 hP).1 i

/-- `Σ_i f(P_i) = Σ_k α(k) f(k)` for an assignment `P` with occupation numbers `α`. -/
private lemma Energy_sum_fiber {N : ℕ} {α : Occ} {P : Fin N → Idx} (hP : P ∈ occFns N α)
    (f : Idx → ℝ) : ∑ i, f (P i) = ∑ n ∈ α.support, f n * (α n : ℝ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := P) (t := α.support)
    (fun i _ => Energy_occFns_maps hP i)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.1 hi).2]), Finset.sum_const,
    Energy_mem_occFns hP n, nsmul_eq_mul, mul_comm]

/-- The multinomial count: `(∏_k α(k)! / N!) · #{P : occupation α} = 1` for `Σ_k α(k) = N`. -/
private lemma Energy_card_occFns {L : ℝ} (hL : 0 < L) {N : ℕ} {α : Occ} (hα : α.num = N) :
    Energy_c N α * ((occFns N α).card : ℝ) = 1 := by
  have hc := Energy_c_nonneg N α
  have h1 := symWave_orthonormal hL hα hα
  simp only [ite_true] at h1
  have h2 : ∫ x in cellN L N, ‖symWave L N α x‖ ^ 2 = 1 := by
    apply Complex.ofReal_injective
    rw [← integral_complex_ofReal]
    have h3 : ∀ x, ((‖symWave L N α x‖ ^ 2 : ℝ) : ℂ) =
        conj (symWave L N α x) * symWave L N α x := by
      intro x
      rw [Complex.conj_mul']
      push_cast
      rfl
    simp_rw [h3, h1]
    simp
  have h3 := Energy_parseval hL (occFns N α) id (Set.injOn_id _)
    fun _ => (Real.sqrt (Energy_c N α) : ℂ)
  simp only [id] at h3
  have h4 : ∀ x : Conf N, ∑ P ∈ occFns N α, (Real.sqrt (Energy_c N α) : ℂ) * Energy_pw L P x =
      symWave L N α x := fun x => (Energy_symWave_eq L N α x).symm
  simp_rw [h4, h2, Finset.sum_const, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hc, nsmul_eq_mul] at h3
  linarith

/-! ### The kinetic part of (2.1) [ham] -/

private lemma Energy_stateFn_contDiff (L : ℝ) (N : ℕ) (Ψ : Occ →₀ ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (stateFn L N Ψ) := by
  have h : stateFn L N Ψ = fun x => ∑ α ∈ Ψ.support, Ψ α * symWave L N α x := by
    funext x
    rfl
  rw [h]
  exact ContDiff.sum fun α _ => contDiff_const.mul (symWave_contDiff L N α)

/-- `e_n(y + t ε_a) = e_n(y) e^{i t (k_n)_a}`. -/
private lemma Energy_planeWave_line (L : ℝ) (n : Idx) (y : R3) (a : Fin 3) (t : ℝ) :
    planeWave L n (y + t • EuclideanSpace.single a (1 : ℝ)) =
      planeWave L n y * Complex.exp (Complex.I * (((mom L n) a * t : ℝ) : ℂ)) := by
  unfold planeWave
  rw [inner_add_right, inner_smul_right, EuclideanSpace.inner_single_right]
  simp only [one_mul, conj_trivial]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private lemma Energy_pw_line (L : ℝ) {N : ℕ} (P : Fin N → Idx) (x : Conf N) (i : Fin N)
    (a : Fin 3) (t : ℝ) :
    Energy_pw L P (x + t • (Pi.single i (EuclideanSpace.single a (1 : ℝ)) : Conf N)) =
      Energy_pw L P x * Complex.exp (Complex.I * (((mom L (P i)) a * t : ℝ) : ℂ)) := by
  unfold Energy_pw
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j => planeWave L (P j) (x j)) (Finset.mem_univ i)]
  have h1 : ∏ j ∈ Finset.univ.erase i,
      planeWave L (P j) ((x + t • (Pi.single i (EuclideanSpace.single a (1 : ℝ)) : Conf N)) j) =
      ∏ j ∈ Finset.univ.erase i, planeWave L (P j) (x j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have : j ≠ i := Finset.ne_of_mem_erase hj
    simp [this]
  rw [h1]
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
  rw [Energy_planeWave_line]
  ring

/-- `∂_{x_i^a} Φ_Ψ = Σ_α Σ_P Ψ(α) c_α^{1/2} i (k_{P_i})_a w_P`. -/
private lemma Energy_fderiv_stateFn (L : ℝ) {N : ℕ} (Ψ : Occ →₀ ℂ) (x : Conf N) (i : Fin N)
    (a : Fin 3) :
    fderiv ℝ (stateFn L N Ψ) x (Pi.single i (EuclideanSpace.single a (1 : ℝ)) : Conf N) =
      ∑ α ∈ Ψ.support, ∑ P ∈ occFns N α,
        (Ψ α * (Real.sqrt (Energy_c N α) : ℂ) * (Complex.I * (((mom L (P i)) a : ℝ) : ℂ))) *
          Energy_pw L P x := by
  have hdiff : DifferentiableAt ℝ (stateFn L N Ψ) x :=
    ((Energy_stateFn_contDiff L N Ψ).differentiable (by simp)) x
  rw [← hdiff.lineDeriv_eq_fderiv]
  apply HasLineDerivAt.lineDeriv
  have hline : (fun t : ℝ =>
      stateFn L N Ψ (x + t • (Pi.single i (EuclideanSpace.single a (1 : ℝ)) : Conf N))) =
      fun t => ∑ α ∈ Ψ.support, ∑ P ∈ occFns N α,
        (Ψ α * (Real.sqrt (Energy_c N α) : ℂ) * Energy_pw L P x) *
          Complex.exp (Complex.I * (((mom L (P i)) a * t : ℝ) : ℂ)) := by
    funext t
    simp only [stateFn, Energy_symWave_eq, Energy_pw_line, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun P _ => ?_
    ring
  unfold HasLineDerivAt
  rw [hline]
  refine HasDerivAt.fun_sum fun α _ => HasDerivAt.fun_sum fun P _ => ?_
  have h0 : HasDerivAt (fun t : ℝ => (mom L (P i)) a * t) ((mom L (P i)) a) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul ((mom L (P i)) a)
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * (((mom L (P i)) a * t : ℝ) : ℂ)))
      (Complex.I * (((mom L (P i)) a : ℝ) : ℂ)) 0 := by
    have := (h0.ofReal_comp.const_mul Complex.I).cexp
    simpa using this
  convert h1.const_mul (Ψ α * (Real.sqrt (Energy_c N α) : ℂ) * Energy_pw L P x) using 1
  ring

/-- The kinetic part of (2.1) [ham] in position space: the kinetic summands of `Ψ` add up to
`∫_{[0, L]^{3N}} Σ_i |∇_i Φ_Ψ|²`. -/
theorem stateFn_kin_hasSum {L : ℝ} (hL : 0 < L) {N : ℕ} (Ψ : Occ →₀ ℂ)
    (hΨ : ∀ α, Ψ α ≠ 0 → α.num = N) :
    HasSum (kinTerm L Ψ) (∫ x in cellN L N, kinD (stateFn L N Ψ) x) := by
  set T := Ψ.support.sigma fun α => occFns N α
  have hT : Set.InjOn (fun t : (_ : Occ) × (Fin N → Idx) => t.2) T := by
    rintro ⟨α, P⟩ hα ⟨β, P'⟩ hβ h
    simp only at h
    subst h
    rw [Finset.mem_coe, Finset.mem_sigma] at hα hβ
    have h := Energy_occFns_inj (α := α) (β := β) hα.2 hβ.2
    subst h
    rfl
  set g : Fin N → Fin 3 → (_ : Occ) × (Fin N → Idx) → ℂ := fun i a t =>
    Ψ t.1 * (Real.sqrt (Energy_c N t.1) : ℂ) * (Complex.I * (((mom L (t.2 i)) a : ℝ) : ℂ))
  have hpt : ∀ x, kinD (stateFn L N Ψ) x =
      ∑ i, ∑ a : Fin 3, ‖∑ t ∈ T, g i a t * Energy_pw L t.2 x‖ ^ 2 := by
    intro x
    unfold kinD
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
    rw [Energy_fderiv_stateFn, Finset.sum_sigma]
  have hcont : ∀ i a, Continuous fun x => ‖∑ t ∈ T, g i a t * Energy_pw L t.2 x‖ ^ 2 :=
    fun i a => (continuous_finsetSum _ fun t _ =>
      continuous_const.mul (Energy_pw_continuous L t.2)).norm.pow 2
  have hS : ∀ α ∉ Ψ.support, kinTerm L Ψ α = 0 := fun α hα => by
    simp [kinTerm, Finsupp.notMem_support_iff.1 hα]
  suffices hval : (∫ x in cellN L N, kinD (stateFn L N Ψ) x) =
      ∑ α ∈ Ψ.support, kinTerm L Ψ α by
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero hS
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun a _ =>
      Energy_integrable L (hcont i a)]
  simp_rw [integral_finsetSum _ fun a _ => Energy_integrable L (hcont _ a),
    Energy_parseval hL T _ hT]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 3))) (t := T)]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin N))) (t := T), Finset.sum_sigma]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hnum := hΨ α (Finsupp.mem_support_iff.1 hα)
  have h1 : ∀ P ∈ occFns N α, ∑ i, ∑ a : Fin 3, ‖g i a ⟨α, P⟩‖ ^ 2 =
      ‖Ψ α‖ ^ 2 * Energy_c N α * ∑ n ∈ α.support, ‖mom L n‖ ^ 2 * (α n : ℝ) := by
    intro P hP
    have h2 : ∀ i (a : Fin 3), ‖g i a ⟨α, P⟩‖ ^ 2 =
        ‖Ψ α‖ ^ 2 * Energy_c N α * ((mom L (P i)) a) ^ 2 := by
      intro i a
      simp only [g, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Energy_c_nonneg N α), sq_abs]
      ring
    simp_rw [h2, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
    rw [Energy_sum_fiber hP (fun n => ‖mom L n‖ ^ 2)]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, kinTerm]
  have h3 := Energy_card_occFns hL hnum
  calc ((occFns N α).card : ℝ) * (‖Ψ α‖ ^ 2 * Energy_c N α *
        ∑ n ∈ α.support, ‖mom L n‖ ^ 2 * (α n : ℝ))
      = (Energy_c N α * (occFns N α).card) * (‖Ψ α‖ ^ 2 *
        ∑ n ∈ α.support, ‖mom L n‖ ^ 2 * (α n : ℝ)) := by ring
    _ = _ := by rw [h3, one_mul]

/-! ### Two-particle integrals on the torus -/

private lemma Energy_mom_apply (L : ℝ) (n : Idx) (a : Fin 3) :
    (mom L n) a = 2 * π / L * (n a : ℝ) := rfl

private lemma Energy_lat_apply (L : ℝ) (n : Idx) (a : Fin 3) : (lat L n) a = L * (n a : ℝ) := rfl

private lemma Energy_mom_add (L : ℝ) (m n : Idx) : mom L (m + n) = mom L m + mom L n := by
  ext a
  simp only [PiLp.add_apply, Energy_mom_apply, Pi.add_apply, Int.cast_add]
  ring

private lemma Energy_mom_sub (L : ℝ) (m n : Idx) : mom L (m - n) = mom L m - mom L n := by
  ext a
  simp only [PiLp.sub_apply, Energy_mom_apply, Pi.sub_apply, Int.cast_sub]
  ring

/-- Pairing of a momentum with a lattice vector: `⟨(2π/L) m, L n⟩ = 2π m·n`. -/
private lemma Energy_inner_mom_lat {L : ℝ} (hL : L ≠ 0) (m n : Idx) :
    inner ℝ (mom L m) (lat L n) = 2 * π * ((∑ a, m a * n a : ℤ) : ℝ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Energy_mom_apply,
    Energy_lat_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

/-- The phase `e^{-i⟨k_u, ·⟩}` is invariant under translation by `Ln`. -/
private lemma Energy_phase_lat {L : ℝ} (hL : 0 < L) (u n : Idx) (z : R3) :
    Complex.exp (-(Complex.I * ((inner ℝ (mom L u) (z + lat L n) : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ))) := by
  rw [inner_add_right, Energy_inner_mom_lat hL.ne']
  have h2 : -(Complex.I * ((inner ℝ (mom L u) z + 2 * π * ((∑ a, u a * n a : ℤ) : ℝ) : ℝ) : ℂ)) =
      ((-(∑ a, u a * n a : ℤ) : ℤ) : ℂ) * (2 * π * Complex.I) +
        -(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ)) := by
    push_cast; ring
  rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul]

private def Energy_basis {L : ℝ} (hL : 0 < L) : Module.Basis (Fin 3) ℝ R3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map (LinearEquiv.smulOfNeZero ℝ R3 L hL.ne')

private lemma Energy_basis_repr {L : ℝ} (hL : 0 < L) (x : R3) (i : Fin 3) :
    (Energy_basis hL).repr x i = L⁻¹ * x i := by
  simp [Energy_basis, Units.smul_def]

private lemma Energy_basis_apply {L : ℝ} (hL : 0 < L) (i a : Fin 3) :
    (Energy_basis hL) i a = if a = i then L else 0 := by
  simp [Energy_basis]

private lemma Energy_mem_span {L : ℝ} (hL : 0 < L) (x : R3) :
    x ∈ Submodule.span ℤ (Set.range (Energy_basis hL)) ↔ ∃ n : Idx, x = lat L n := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    ext a
    simp [Energy_basis_apply, Energy_lat_apply, Finset.sum_apply]
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    ext a
    simp [Energy_basis_apply, Energy_lat_apply, Finset.sum_apply]
    ring

private lemma Energy_cell_eq {L : ℝ} (hL : 0 < L) :
    parallelepiped (Energy_basis hL) = cell L := by
  rw [parallelepiped_basis_eq]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Energy_basis_repr, cell]
  refine forall_congr' fun a => ?_
  rw [mul_nonneg_iff_of_pos_left (inv_pos.2 hL), inv_mul_le_iff₀ hL, mul_one]

/-- The integral of an `L`-periodic function over the translated cell `z + [0, L]³` equals its
integral over `[0, L]³`. -/
private lemma Energy_integral_shift {L : ℝ} (hL : 0 < L) (g : R3 → ℂ)
    (hg : ∀ y n, g (y + lat L n) = g y) (z : R3) :
    ∫ y in cell L, g (z + y) = ∫ y in cell L, g y := by
  have hF := ZSpan.isAddFundamentalDomain' (Energy_basis hL) (volume : Measure R3)
  have hae : ZSpan.fundamentalDomain (Energy_basis hL) =ᵐ[volume] cell L := by
    rw [← Energy_cell_eq hL]
    exact ZSpan.fundamentalDomain_ae_parallelepiped _ _
  rw [← setIntegral_congr_set hae, ← setIntegral_congr_set hae]
  have hF' := hF.vadd_of_comm z
  have hinv : ∀ (γ : (Submodule.span ℤ (Set.range (Energy_basis hL))).toAddSubgroup) (x : R3),
      g (γ +ᵥ x) = g x := by
    rintro ⟨γ, hγ⟩ x
    obtain ⟨n, rfl⟩ := (Energy_mem_span hL γ).1 hγ
    change g (lat L n + x) = g x
    rw [add_comm]
    exact hg x n
  have hcount : Countable (Submodule.span ℤ (Set.range (Energy_basis hL))).toAddSubgroup := by
    have hs : Function.Surjective (fun n : Idx =>
        (⟨lat L n, (Energy_mem_span hL _).2 ⟨n, rfl⟩⟩ :
          (Submodule.span ℤ (Set.range (Energy_basis hL))).toAddSubgroup)) := by
      rintro ⟨γ, hγ⟩
      obtain ⟨n, rfl⟩ := (Energy_mem_span hL γ).1 hγ
      exact ⟨n, rfl⟩
    exact hs.countable
  rw [← hF'.setIntegral_eq hF hinv,
    ← (measurePreserving_add_left volume z).setIntegral_image_emb
      (measurableEmbedding_addLeft z)]
  rfl

/-- `∫_{[0, L]³} V^P(y - z) e^{-i⟨k_u, y⟩} dy = e^{-i⟨k_u, z⟩} V_u`. -/
private lemma Energy_shift_fourier {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L)
    (u : Idx) (z : R3) :
    ∫ y in cell L, (periodize L V (y - z) : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ (mom L u) y : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ))) * ft V (mom L u) := by
  set g : R3 → ℂ := fun y =>
    Complex.exp (-(Complex.I * ((inner ℝ (mom L u) y : ℝ) : ℂ))) * (periodize L V y : ℂ)
  have hg : ∀ y n, g (y + lat L n) = g y := by
    intro y n
    simp only [g]
    rw [Energy_phase_lat hL, periodize_periodic]
  have h1 : ∀ y, (periodize L V (y - z) : ℂ) *
      Complex.exp (-(Complex.I * ((inner ℝ (mom L u) y : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ))) * g (-z + y) := by
    intro y
    simp only [g]
    rw [neg_add_eq_sub, inner_sub_right]
    have : Complex.exp (-(Complex.I * ((inner ℝ (mom L u) y : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ))) *
          Complex.exp (-(Complex.I * ((inner ℝ (mom L u) y - inner ℝ (mom L u) z : ℝ) : ℂ))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [this]
    ring
  simp_rw [h1]
  rw [integral_const_mul, Energy_integral_shift hL g hg (-z), periodize_fourier hV hL u]

/-- `conj e_p(y) e_r(y) = L^{-3} e^{-i⟨k_{p-r}, y⟩}`. -/
private lemma Energy_conj_mul {L : ℝ} (hL : 0 < L) (p r : Idx) (y : R3) :
    conj (planeWave L p y) * planeWave L r y =
      (((L ^ 3)⁻¹ : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * ((inner ℝ (mom L (p - r)) y : ℝ) : ℂ))) := by
  have hs : ((Real.sqrt (L ^ 3))⁻¹ : ℂ) * ((Real.sqrt (L ^ 3))⁻¹ : ℂ) =
      (((L ^ 3)⁻¹ : ℝ) : ℂ) := by
    have h0 : (0 : ℝ) ≤ L ^ 3 := by positivity
    have : (Real.sqrt (L ^ 3))⁻¹ * (Real.sqrt (L ^ 3))⁻¹ = (L ^ 3)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt h0]
    exact_mod_cast this
  unfold planeWave
  rw [map_mul, ← Complex.exp_conj]
  have hc : conj (((Real.sqrt (L ^ 3))⁻¹ : ℂ)) = ((Real.sqrt (L ^ 3))⁻¹ : ℂ) := by
    simp
  rw [hc]
  calc _ = (((Real.sqrt (L ^ 3))⁻¹ : ℂ) * ((Real.sqrt (L ^ 3))⁻¹ : ℂ)) *
        (Complex.exp (conj (Complex.I * ((inner ℝ (mom L p) y : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((inner ℝ (mom L r) y : ℝ) : ℂ))) := by ring
    _ = _ := by
      rw [hs, ← Complex.exp_add, Energy_mom_sub, inner_sub_left]
      congr 2
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring

/-- `conj e_q(z) e^{-i⟨k_u, z⟩} = conj e_{q+u}(z)`. -/
private lemma Energy_conj_shift (L : ℝ) (q u : Idx) (z : R3) :
    conj (planeWave L q z) * Complex.exp (-(Complex.I * ((inner ℝ (mom L u) z : ℝ) : ℂ))) =
      conj (planeWave L (q + u) z) := by
  unfold planeWave
  rw [map_mul, map_mul, ← Complex.exp_conj, ← Complex.exp_conj, mul_assoc, ← Complex.exp_add,
    Energy_mom_add, inner_add_left]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The two-particle matrix element of `V^P(x_1 - x_2)`:
`∫∫ V^P(y - z) conj(e_p(y) e_q(z)) e_r(y) e_s(z) = L^{-3} V_{p-r} δ_{q + p - r, s}`. -/
private lemma Energy_I2 {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L)
    (p q r s : Idx) :
    ∫ z in cell L, ∫ y in cell L, (periodize L V (y - z) : ℂ) *
        (conj (planeWave L q z) * planeWave L s z) * (conj (planeWave L p y) * planeWave L r y) =
      (((L ^ 3)⁻¹ : ℝ) : ℂ) * ft V (mom L (p - r)) * (if q + (p - r) = s then 1 else 0) := by
  have hin : ∀ z, ∫ y in cell L, (periodize L V (y - z) : ℂ) *
      (conj (planeWave L q z) * planeWave L s z) * (conj (planeWave L p y) * planeWave L r y) =
      ((((L ^ 3)⁻¹ : ℝ) : ℂ) * ft V (mom L (p - r))) *
        (conj (planeWave L (q + (p - r)) z) * planeWave L s z) := by
    intro z
    simp_rw [Energy_conj_mul hL p r]
    have h1 : ∀ y, (periodize L V (y - z) : ℂ) * (conj (planeWave L q z) * planeWave L s z) *
        ((((L ^ 3)⁻¹ : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * ((inner ℝ (mom L (p - r)) y : ℝ) : ℂ)))) =
        ((conj (planeWave L q z) * planeWave L s z) * (((L ^ 3)⁻¹ : ℝ) : ℂ)) *
          ((periodize L V (y - z) : ℂ) *
            Complex.exp (-(Complex.I * ((inner ℝ (mom L (p - r)) y : ℝ) : ℂ)))) := by
      intro y
      ring
    simp_rw [h1]
    rw [integral_const_mul, Energy_shift_fourier hV hL, ← Energy_conj_shift L q (p - r) z]
    ring
  simp_rw [hin]
  rw [integral_const_mul, planeWave_orthonormal hL]

/-- Fubini for a function of the last two particles times a function of the others. -/
private lemma Energy_integral_two (L : ℝ) (M : ℕ) (W : R3 → R3 → ℂ)
    (hW : Continuous fun z : R3 × R3 => W z.1 z.2) (h : Conf M → ℂ) (hh : Continuous h) :
    ∫ x in cellN L (M + 2), W (x (Fin.last (M + 1))) (Fin.init x (Fin.last M)) *
        h (Fin.init (Fin.init x)) =
      (∫ z in cell L, ∫ y in cell L, W z y) * ∫ x in cellN L M, h x := by
  rw [Energy_integral_cellN_succ L (M + 1)]
  simp only [Fin.snoc_last, Fin.init_snoc]
  have hinit : ∀ K : ℕ, Continuous fun x : Conf (K + 1) => Fin.init x :=
    fun K => continuous_pi fun i => continuous_apply _
  rw [setIntegral_prod _ ?_]
  · have hin : ∀ z, ∫ x' in cellN L (M + 1), W z (x' (Fin.last M)) * h (Fin.init x') =
        (∫ y in cell L, W z y) * ∫ x in cellN L M, h x := by
      intro z
      rw [Energy_integral_cellN_succ L M]
      simp only [Fin.snoc_last, Fin.init_snoc]
      exact setIntegral_prod_mul (fun y => W z y) h (cell L) (cellN L M)
    simp_rw [hin]
    rw [integral_mul_const]
  · refine ContinuousOn.integrableOn_compact
      ((Energy_isCompact_cell L).prod (Energy_isCompact_cellN L (M + 1)))
      (Continuous.continuousOn ?_)
    have hs : Continuous fun z : R3 × Conf (M + 1) => z.2 := continuous_snd
    have hf : Continuous fun z : R3 × Conf (M + 1) => z.1 := continuous_fst
    have hl : Continuous fun z : R3 × Conf (M + 1) => z.2 (Fin.last M) :=
      (continuous_apply (Fin.last M)).comp hs
    exact (hW.comp (hf.prodMk hl)).mul (hh.comp ((hinit M).comp hs))

/-- Integrals over `[0, L]^{3N}` are invariant under permutations of the particles. -/
private lemma Energy_perm_integral (L : ℝ) {N : ℕ} (σ : Equiv.Perm (Fin N)) (G : Conf N → ℂ) :
    ∫ x in cellN L N, G (x ∘ σ) = ∫ x in cellN L N, G x := by
  have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin N => R3) σ.symm
  have hfun : ∀ x : Conf N, (MeasurableEquiv.piCongrLeft (fun _ : Fin N => R3) σ.symm) x =
      x ∘ σ := by
    intro x
    funext a
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have key := hmp.setIntegral_preimage_emb (MeasurableEquiv.measurableEmbedding _) G (cellN L N)
  have hset : (MeasurableEquiv.piCongrLeft (fun _ : Fin N => R3) σ.symm) ⁻¹' cellN L N =
      cellN L N := by
    ext x
    simp only [Set.mem_preimage, hfun, cellN, Set.mem_ofPred_eq, Function.comp_apply]
    constructor
    · intro h i
      simpa using h (σ.symm i)
    · intro h i
      exact h (σ i)
  simp_rw [hfun] at key
  rw [hset] at key
  exact key

private lemma Energy_exists_perm {n : ℕ} {i₀ j₀ i j : Fin n} (h₀ : i₀ ≠ j₀) (h : i ≠ j) :
    ∃ σ : Equiv.Perm (Fin n), σ i₀ = i ∧ σ j₀ = j := by
  refine ⟨Equiv.swap i₀ i * Equiv.swap j₀ (Equiv.swap i₀ i j), ?_, ?_⟩
  · have hne : i₀ ≠ Equiv.swap i₀ i j := by
      intro hj
      apply h
      have := congrArg (Equiv.swap i₀ i) hj
      rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
      exact this
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h₀ hne, Equiv.swap_apply_left]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- `∫ Σ_{i ≠ j} W(x_i - x_j) F = (M+2)(M+1) ∫ W(x_{M+1} - x_{M+2}) F` for symmetric `F`. -/
private lemma Energy_pairPot_integral (L : ℝ) (M : ℕ) {W : R3 → ℝ} (hW : Continuous W)
    {F : Conf (M + 2) → ℂ} (hF : Continuous F)
    (hsym : ∀ (σ : Equiv.Perm (Fin (M + 2))) x, F (x ∘ σ) = F x) :
    ∫ x in cellN L (M + 2), (pairPot W x : ℂ) * F x =
      ((M : ℂ) + 2) * ((M : ℂ) + 1) * ∫ x in cellN L (M + 2),
        (W (x (Fin.castSucc (Fin.last M)) - x (Fin.last (M + 1))) : ℂ) * F x := by
  set J := ∫ x in cellN L (M + 2),
    (W (x (Fin.castSucc (Fin.last M)) - x (Fin.last (M + 1))) : ℂ) * F x
  have h1 : ∀ x : Conf (M + 2), (pairPot W x : ℂ) * F x = ∑ i, ∑ j,
      (if i ≠ j then (W (x i - x j) : ℂ) * F x else 0) := by
    intro x
    simp only [pairPot]
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hint : ∀ i j : Fin (M + 2), Integrable (fun x : Conf (M + 2) =>
      if i ≠ j then (W (x i - x j) : ℂ) * F x else 0) (volume.restrict (cellN L (M + 2))) := by
    intro i j
    split_ifs
    · exact Energy_integrable L ((Complex.continuous_ofReal.comp (hW.comp
        ((continuous_apply i).sub (continuous_apply j)))).mul hF)
    · exact integrable_zero _ _ _
  simp_rw [h1]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  have h2 : ∀ i j : Fin (M + 2), ∫ x in cellN L (M + 2),
      (if i ≠ j then (W (x i - x j) : ℂ) * F x else 0) = if i ≠ j then J else 0 := by
    intro i j
    split_ifs with hij
    · have h₀ : Fin.castSucc (Fin.last M) ≠ Fin.last (M + 1) := Fin.castSucc_lt_last _ |>.ne
      obtain ⟨σ, hσi, hσj⟩ := Energy_exists_perm h₀ hij
      refine Eq.trans ?_ (Energy_perm_integral L σ (fun x : Conf (M + 2) =>
        (W (x (Fin.castSucc (Fin.last M)) - x (Fin.last (M + 1))) : ℂ) * F x))
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Function.comp_apply, hσi, hσj, hsym]
    · simp
  simp_rw [integral_finsetSum _ fun j _ => hint _ j, h2]
  have h3 : ∀ i : Fin (M + 2), ∑ j : Fin (M + 2), (if i ≠ j then J else 0) = ((M : ℂ) + 1) * J := by
    intro i
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
      Finset.filter_ne, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    push_cast
    ring
  simp_rw [h3]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-! ### Occupation numbers -/

private lemma Energy_support_tsub (α : Occ) (k : Idx) :
    (α - Finsupp.single k 1).support ⊆ α.support := by
  intro a ha
  rw [Finsupp.mem_support_iff] at ha ⊢
  intro h0
  apply ha
  simp [h0]

private lemma Energy_num_add_single (α : Occ) (k : Idx) :
    (α + Finsupp.single k 1).num = α.num + 1 := by
  unfold Occ.num
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

private lemma Energy_num_sub_single {α : Occ} {k : Idx} (hk : 0 < α k) :
    (α - Finsupp.single k 1).num + 1 = α.num := by
  have h : α = (α - Finsupp.single k 1) + Finsupp.single k 1 :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hk)).symm
  conv_rhs => rw [h]
  rw [Energy_num_add_single]

private lemma Energy_exists_add (r s : Idx) (α : Occ) (h1 : 0 < α s)
    (h2 : 0 < (α - Finsupp.single s 1 : Occ) r) :
    ∃ γ : Occ, α = γ + Finsupp.single r 1 + Finsupp.single s 1 :=
  ⟨α - Finsupp.single s 1 - Finsupp.single r 1, by
    rw [tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h2),
      tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h1)]⟩

private lemma Energy_a4_of_add (p q r s : Idx) (γ : Occ) :
    a4 p q r s (γ + Finsupp.single r 1 + Finsupp.single s 1) =
      (Real.sqrt ((γ + Finsupp.single r 1 + Finsupp.single s 1 : Occ) s : ℝ) *
        Real.sqrt ((γ + Finsupp.single r 1 : Occ) r : ℝ) *
        Real.sqrt ((γ + Finsupp.single q 1 : Occ) q : ℝ) *
        Real.sqrt ((γ + Finsupp.single q 1 + Finsupp.single p 1 : Occ) p : ℝ),
       γ + Finsupp.single q 1 + Finsupp.single p 1) := by
  simp only [a4, add_tsub_cancel_right]

private lemma Energy_sqrt4 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x₁ x₂ x₃ x₄ : ℝ) :
    a * b * ((Real.sqrt (x₁ / a) * Real.sqrt (x₂ / b)) *
      (Real.sqrt (x₃ / a) * Real.sqrt (x₄ / b))) =
      Real.sqrt x₁ * Real.sqrt x₂ * (Real.sqrt x₃ * Real.sqrt x₄) := by
  have hA : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha.le
  have hB : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb.le
  have ha' : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  have hb' : Real.sqrt b ≠ 0 := (Real.sqrt_pos.2 hb).ne'
  rw [Real.sqrt_div' _ ha.le, Real.sqrt_div' _ hb.le, Real.sqrt_div' _ ha.le,
    Real.sqrt_div' _ hb.le]
  have hab : a * b / ((Real.sqrt a * Real.sqrt a) * (Real.sqrt b * Real.sqrt b)) = 1 := by
    rw [hA, hB, div_self (mul_pos ha hb).ne']
  calc a * b * (Real.sqrt x₁ / Real.sqrt a * (Real.sqrt x₂ / Real.sqrt b) *
        (Real.sqrt x₃ / Real.sqrt a * (Real.sqrt x₄ / Real.sqrt b)))
      = Real.sqrt x₁ * Real.sqrt x₂ * (Real.sqrt x₃ * Real.sqrt x₄) *
        (a * b / ((Real.sqrt a * Real.sqrt a) * (Real.sqrt b * Real.sqrt b))) := by ring
    _ = _ := by rw [hab, mul_one]

/-- The coefficient of `a†_p a†_q a_r a_s` from expanding `Φ_β` and `Φ_α` in the last two
particles: `(M+2)(M+1) c_β(q, p) c_α(s, r) δ_{α - δ_s - δ_r, β - δ_q - δ_p}` is the `a4`
coefficient when `β` is the image occupation, and `0` otherwise. -/
private lemma Energy_coef {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (α β : Occ) (p q r s : Idx) :
    a * b * ((Real.sqrt ((β q : ℝ) / a) *
        Real.sqrt (((β - Finsupp.single q 1 : Occ) p : ℝ) / b)) *
      (Real.sqrt ((α s : ℝ) / a) * Real.sqrt (((α - Finsupp.single s 1 : Occ) r : ℝ) / b))) *
      (if α - Finsupp.single s 1 - Finsupp.single r 1 =
          β - Finsupp.single q 1 - Finsupp.single p 1 then 1 else 0) =
    if β = (a4 p q r s α).2 then (a4 p q r s α).1 else 0 := by
  rw [Energy_sqrt4 ha hb]
  by_cases hαs : α s = 0
  · simp [a4, hαs]
  by_cases hαr : (α - Finsupp.single s 1 : Occ) r = 0
  · simp [a4, hαr]
  obtain ⟨γ, rfl⟩ := Energy_exists_add r s α (Nat.pos_of_ne_zero hαs) (Nat.pos_of_ne_zero hαr)
  rw [Energy_a4_of_add]
  simp only [add_tsub_cancel_right]
  have hsub : γ + Finsupp.single q 1 + Finsupp.single p 1 - Finsupp.single q 1 =
      γ + Finsupp.single p 1 := by
    rw [add_right_comm, add_tsub_cancel_right]
  by_cases hβq : β q = 0
  · have : β ≠ γ + Finsupp.single q 1 + Finsupp.single p 1 := by
      rintro rfl
      simp at hβq
    simp [hβq, this]
  by_cases hβp : (β - Finsupp.single q 1 : Occ) p = 0
  · have : β ≠ γ + Finsupp.single q 1 + Finsupp.single p 1 := by
      rintro rfl
      rw [hsub] at hβp
      simp at hβp
    simp [hβp, this]
  obtain ⟨β', rfl⟩ := Energy_exists_add p q β (Nat.pos_of_ne_zero hβq) (Nat.pos_of_ne_zero hβp)
  simp only [add_tsub_cancel_right]
  have hcomm : β' + Finsupp.single p 1 + Finsupp.single q 1 =
      β' + Finsupp.single q 1 + Finsupp.single p 1 := add_right_comm _ _ _
  by_cases hγ : γ = β'
  · subst hγ
    simp only [hcomm, ite_true, mul_one]
    by_cases hpq : p = q
    · subst hpq
      ring
    · simp [Finsupp.single_apply, hpq, Ne.symm hpq]
      ring
  · have : β' + Finsupp.single p 1 + Finsupp.single q 1 ≠
        γ + Finsupp.single q 1 + Finsupp.single p 1 := by
      rw [hcomm]
      intro h
      exact hγ (add_right_cancel (add_right_cancel h)).symm
    simp only [hγ, this, ite_false, mul_zero]

private lemma Energy_a4_ne {p q r s : Idx} {α : Occ} (h : (a4 p q r s α).1 ≠ 0) :
    ∃ γ : Occ, α = γ + Finsupp.single r 1 + Finsupp.single s 1 := by
  have hs : 0 < α s := by
    by_contra h0
    apply h
    simp [a4, Nat.le_zero.1 (not_lt.1 h0)]
  have hr : 0 < (α - Finsupp.single s 1 : Occ) r := by
    by_contra h0
    apply h
    simp [a4, Nat.le_zero.1 (not_lt.1 h0)]
  exact Energy_exists_add r s α hs hr

/-- `a†_p a†_q a_r a_s` preserves the particle number. -/
private lemma Energy_a4_num {p q r s : Idx} {α : Occ} (h : (a4 p q r s α).1 ≠ 0) :
    (a4 p q r s α).2.num = α.num := by
  obtain ⟨γ, rfl⟩ := Energy_a4_ne h
  rw [Energy_a4_of_add]
  simp only [Energy_num_add_single]

/-! ### The interaction part of (2.1) [ham] -/

private lemma Energy_symWave_succ (L : ℝ) (N : ℕ) {α : Occ} {A : Finset Idx}
    (hA : α.support ⊆ A) (x : Conf (N + 1)) :
    symWave L (N + 1) α x = ∑ k ∈ A, (Real.sqrt ((α k : ℝ) / ((N : ℝ) + 1)) : ℂ) *
      planeWave L k (x (Fin.last N)) * symWave L N (α - Finsupp.single k 1) (Fin.init x) := by
  rw [symWave_succ]
  refine Finset.sum_subset hA fun k _ hk => ?_
  rw [Finsupp.notMem_support_iff.1 hk]
  simp

/-- Expansion of `Φ_α` in the last two particles. -/
private lemma Energy_symWave_succ2 (L : ℝ) (M : ℕ) {α : Occ} {A : Finset Idx}
    (hA : α.support ⊆ A) (x : Conf (M + 2)) :
    symWave L (M + 2) α x = ∑ s ∈ A, ∑ r ∈ A,
      ((Real.sqrt ((α s : ℝ) / (((M + 1 : ℕ) : ℝ) + 1)) *
        Real.sqrt (((α - Finsupp.single s 1 : Occ) r : ℝ) / ((M : ℝ) + 1)) : ℝ) : ℂ) *
        (planeWave L s (x (Fin.last (M + 1))) * planeWave L r (Fin.init x (Fin.last M)) *
          symWave L M (α - Finsupp.single s 1 - Finsupp.single r 1) (Fin.init (Fin.init x))) := by
  rw [Energy_symWave_succ L (M + 1) hA]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Energy_symWave_succ L M ((Energy_support_tsub α s).trans hA), Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  push_cast
  ring

private lemma Energy_pairPot_continuous {W : R3 → ℝ} (hW : Continuous W) (N : ℕ) :
    Continuous fun x : Conf N => pairPot W x := by
  unfold pairPot
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_if_const _ (fun _ => hW.comp ((continuous_apply i).sub (continuous_apply j)))
      fun _ => continuous_const

/-- The interaction matrix element between `Φ_β` and `Φ_α` for `Σ α = Σ β = M + 2`. -/
private lemma Energy_pot_matrix {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L)
    (M : ℕ) {α β : Occ} (hα : α.num = M + 2) (hβ : β.num = M + 2) {A : Finset Idx}
    (hAα : α.support ⊆ A) (hAβ : β.support ⊆ A) :
    ∫ x in cellN L (M + 2), (pairPot (periodize L V) x : ℂ) *
        (conj (symWave L (M + 2) β x) * symWave L (M + 2) α x) =
      ∑ q ∈ A, ∑ s ∈ A, ∑ p ∈ A, ∑ r ∈ A,
        ((if β = (a4 p q r s α).2 then (a4 p q r s α).1 else 0 : ℝ) : ℂ) *
          ((((L ^ 3)⁻¹ : ℝ) : ℂ) * ft V (mom L (p - r)) * (if q + (p - r) = s then 1 else 0)) := by
  have hVc := periodize_continuous hV hL
  have hcΦ : ∀ K γ, Continuous (symWave L K γ) := fun K γ => (symWave_contDiff L K γ).continuous
  have hpw := Energy_planeWave_continuous L
  rw [Energy_pairPot_integral L M hVc
    (F := fun x => conj (symWave L (M + 2) β x) * symWave L (M + 2) α x)
    ((Complex.continuous_conj.comp (hcΦ _ β)).mul (hcΦ _ α))
    (fun σ x => by simp only [symWave_perm])]
  set a : ℝ := ((M + 1 : ℕ) : ℝ) + 1 with ha
  set b : ℝ := (M : ℝ) + 1 with hb
  set c : Occ → Idx → Idx → ℝ := fun γ k k' =>
    Real.sqrt ((γ k : ℝ) / a) * Real.sqrt (((γ - Finsupp.single k 1 : Occ) k' : ℝ) / b) with hc
  set W : Idx → Idx → Idx → Idx → R3 → R3 → ℂ := fun p q r s z y =>
    (periodize L V (y - z) : ℂ) * (conj (planeWave L q z) * planeWave L s z) *
      (conj (planeWave L p y) * planeWave L r y) with hW
  set h : Idx → Idx → Idx → Idx → Conf M → ℂ := fun p q r s x =>
    conj (symWave L M (β - Finsupp.single q 1 - Finsupp.single p 1) x) *
      symWave L M (α - Finsupp.single s 1 - Finsupp.single r 1) x with hh
  have hWc : ∀ p q r s, Continuous fun z : R3 × R3 => W p q r s z.1 z.2 := by
    intro p q r s
    simp only [hW]
    exact ((Complex.continuous_ofReal.comp (hVc.comp (continuous_snd.sub continuous_fst))).mul
      ((Complex.continuous_conj.comp ((hpw q).comp continuous_fst)).mul
        ((hpw s).comp continuous_fst))).mul
      ((Complex.continuous_conj.comp ((hpw p).comp continuous_snd)).mul
        ((hpw r).comp continuous_snd))
  have hhc : ∀ p q r s, Continuous (h p q r s) := fun p q r s =>
    (Complex.continuous_conj.comp (hcΦ _ _)).mul (hcΦ _ _)
  have hexp : ∀ x : Conf (M + 2),
      (periodize L V (x (Fin.castSucc (Fin.last M)) - x (Fin.last (M + 1))) : ℂ) *
        (conj (symWave L (M + 2) β x) * symWave L (M + 2) α x) =
      ∑ q ∈ A, ∑ s ∈ A, ∑ p ∈ A, ∑ r ∈ A, ((c β q p * c α s r : ℝ) : ℂ) *
        (W p q r s (x (Fin.last (M + 1))) (Fin.init x (Fin.last M)) *
          h p q r s (Fin.init (Fin.init x))) := by
    intro x
    rw [show x (Fin.castSucc (Fin.last M)) = Fin.init x (Fin.last M) from rfl,
      Energy_symWave_succ2 L M hAβ x, Energy_symWave_succ2 L M hAα x, map_sum,
      Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [hW, hh, hc, ha, hb, map_mul, Complex.conj_ofReal]
    push_cast
    ring
  have hint : ∀ q s p r, Integrable (fun x : Conf (M + 2) => ((c β q p * c α s r : ℝ) : ℂ) *
      (W p q r s (x (Fin.last (M + 1))) (Fin.init x (Fin.last M)) *
        h p q r s (Fin.init (Fin.init x)))) (volume.restrict (cellN L (M + 2))) := by
    intro q s p r
    refine Energy_integrable L (continuous_const.mul ?_)
    have hinit : ∀ K : ℕ, Continuous fun x : Conf (K + 1) => Fin.init x :=
      fun K => continuous_pi fun i => continuous_apply _
    have h1 : Continuous fun x : Conf (M + 2) => (x (Fin.last (M + 1)), Fin.init x (Fin.last M)) :=
      (continuous_apply _).prodMk ((continuous_apply (Fin.last M)).comp (hinit (M + 1)))
    exact ((hWc p q r s).comp h1).mul ((hhc p q r s).comp ((hinit M).comp (hinit (M + 1))))
  rw [integral_congr_ae (Eventually.of_forall hexp),
    integral_finsetSum _ fun q _ => integrable_finsetSum _ fun s _ =>
      integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun r _ => hint q s p r,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_finsetSum _ fun s _ => integrable_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun r _ => hint q s p r, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finsetSum _ fun p _ => integrable_finsetSum _ fun r _ => hint q s p r,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ fun r _ => hint q s p r, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_const_mul, Energy_integral_two L M (W p q r s) (hWc p q r s) (h p q r s)
    (hhc p q r s)]
  have hI2 : ∫ z in cell L, ∫ y in cell L, W p q r s z y =
      (((L ^ 3)⁻¹ : ℝ) : ℂ) * ft V (mom L (p - r)) * (if q + (p - r) = s then 1 else 0) :=
    Energy_I2 hV hL p q r s
  rw [hI2]
  have hcoef := Energy_coef (by positivity : (0 : ℝ) < a) (by positivity : (0 : ℝ) < b)
    α β p q r s
  have hab : ((M : ℂ) + 2) * ((M : ℂ) + 1) = ((a * b : ℝ) : ℂ) := by
    simp only [ha, hb]
    push_cast
    ring
  have hortho : ((c β q p * c α s r : ℝ) : ℂ) * ∫ x in cellN L M, h p q r s x =
      ((c β q p * c α s r : ℝ) : ℂ) *
        ((if α - Finsupp.single s 1 - Finsupp.single r 1 =
          β - Finsupp.single q 1 - Finsupp.single p 1 then 1 else 0 : ℝ) : ℂ) := by
    by_cases h0 : c β q p * c α s r = 0
    · simp [h0]
    have hpos : ∀ {x y : ℝ}, Real.sqrt (x / y) ≠ 0 → 0 < y → 0 < x := by
      intro x y hxy hy
      by_contra hx
      apply hxy
      rw [Real.sqrt_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (not_lt.1 hx) hy.le)]
    have hb0 : (0 : ℝ) < b := by positivity
    have ha0 : (0 : ℝ) < a := by positivity
    simp only [hc, mul_eq_zero, not_or] at h0
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h0
    have e1 : 0 < β q := by exact_mod_cast hpos h1 ha0
    have e2 : 0 < (β - Finsupp.single q 1 : Occ) p := by exact_mod_cast hpos h2 hb0
    have e3 : 0 < α s := by exact_mod_cast hpos h3 ha0
    have e4 : 0 < (α - Finsupp.single s 1 : Occ) r := by exact_mod_cast hpos h4 hb0
    have n1 := Energy_num_sub_single e1
    have n2 := Energy_num_sub_single e2
    have n3 := Energy_num_sub_single e3
    have n4 := Energy_num_sub_single e4
    simp only [hh]
    rw [symWave_orthonormal hL (by omega) (by omega)]
    split_ifs <;> simp
  calc ((M : ℂ) + 2) * ((M : ℂ) + 1) * (((c β q p * c α s r : ℝ) : ℂ) *
        (((((L ^ 3)⁻¹ : ℝ) : ℂ) * ft V (mom L (p - r)) * (if q + (p - r) = s then 1 else 0)) *
          ∫ x in cellN L M, h p q r s x))
      = ((a * b : ℝ) : ℂ) * (((c β q p * c α s r : ℝ) : ℂ) * ∫ x in cellN L M, h p q r s x) *
        ((((L ^ 3)⁻¹ : ℝ) : ℂ) * ft V (mom L (p - r)) * (if q + (p - r) = s then 1 else 0)) := by
        rw [hab]
        ring
    _ = _ := by
        rw [hortho, ← hcoef]
        simp only [hc]
        push_cast
        ring

private lemma Energy_intTerm_ne {L : ℝ} {V : R3 → ℝ} {Ψ : Occ →₀ ℂ} {p q u : Idx} {α : Occ}
    (h : intTerm L V Ψ (p, q, u, α) ≠ 0) :
    Ψ α ≠ 0 ∧ ∃ γ : Occ, α = γ + Finsupp.single (p - u) 1 + Finsupp.single (q + u) 1 ∧
      Ψ (γ + Finsupp.single q 1 + Finsupp.single p 1) ≠ 0 := by
  have h1 : (a4 p q (p - u) (q + u) α).1 ≠ 0 := by
    intro h0
    apply h
    simp [intTerm, h0]
  refine ⟨fun h0 => h (by simp [intTerm, h0]), ?_⟩
  obtain ⟨γ, rfl⟩ := Energy_a4_ne h1
  refine ⟨γ, rfl, fun h0 => h ?_⟩
  simp [intTerm, Energy_a4_of_add, h0]

/-- The interaction part of (2.1) [ham] in position space: the interaction summands of `Ψ` add
up to `∫_{[0, L]^{3N}} Σ_{i ≠ j} V^P(x_i - x_j) |Φ_Ψ|²`. -/
theorem stateFn_pot_hasSum {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L) {N : ℕ}
    (Ψ : Occ →₀ ℂ) (hΨ : ∀ α, Ψ α ≠ 0 → α.num = N) :
    HasSum (intTerm L V Ψ)
      ((∫ x in cellN L N, pairPot (periodize L V) x * ‖stateFn L N Ψ x‖ ^ 2 : ℝ) : ℂ) := by
  set A : Finset Idx := Ψ.support.biUnion fun α => α.support with hAdef
  have hA : ∀ α ∈ Ψ.support, α.support ⊆ A := fun α hα => Finset.subset_biUnion_of_mem _ hα
  have hmem : ∀ (α : Occ) (k : Idx), Ψ α ≠ 0 → 0 < α k → k ∈ A := fun α k hα hk =>
    hA α (Finsupp.mem_support_iff.2 hα) (Finsupp.mem_support_iff.2 hk.ne')
  set T : Finset (Idx × Idx × Idx × Occ) :=
    (A ×ˢ A ×ˢ A ×ˢ Ψ.support).image fun t => (t.1, t.2.1, t.1 - t.2.2.1, t.2.2.2) with hTdef
  have hsupp : ∀ i ∉ T, intTerm L V Ψ i = 0 := by
    rintro ⟨p, q, u, α⟩ hi
    by_contra hne
    obtain ⟨hα, γ, rfl, hβ⟩ := Energy_intTerm_ne hne
    apply hi
    refine Finset.mem_image.2 ⟨(p, q, p - u, γ + Finsupp.single (p - u) 1 +
      Finsupp.single (q + u) 1), ?_, by simp⟩
    simp only [Finset.mem_product]
    refine ⟨hmem _ p hβ ?_, hmem _ q hβ ?_, hmem _ (p - u) hα ?_,
      Finsupp.mem_support_iff.2 hα⟩ <;> simp
  suffices hval : ((∫ x in cellN L N, pairPot (periodize L V) x * ‖stateFn L N Ψ x‖ ^ 2 : ℝ) :
      ℂ) = ∑ i ∈ T, intTerm L V Ψ i by
    rw [hval]
    exact hasSum_sum_of_ne_finset_zero hsupp
  rcases Nat.lt_or_ge N 2 with hN | hN
  · have hpp : ∀ x : Conf N, pairPot (periodize L V) x = 0 := by
      intro x
      have : Subsingleton (Fin N) := Fin.subsingleton_iff_le_one.2 (by omega)
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [Subsingleton.elim i j]
      simp
    have h0 : ∀ i ∈ T, intTerm L V Ψ i = 0 := by
      rintro ⟨p, q, u, α⟩ _
      by_contra hne
      obtain ⟨hα, γ, rfl, -⟩ := Energy_intTerm_ne hne
      have := hΨ _ hα
      rw [Energy_num_add_single, Energy_num_add_single] at this
      omega
    simp [hpp, Finset.sum_eq_zero h0]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
  have hVc := periodize_continuous hV hL
  have hcΦ : ∀ γ, Continuous (symWave L (M + 2) γ) := fun γ =>
    (symWave_contDiff L (M + 2) γ).continuous
  have hpt : ∀ x : Conf (M + 2),
      (((pairPot (periodize L V) x * ‖stateFn L (M + 2) Ψ x‖ ^ 2 : ℝ)) : ℂ) =
      ∑ β ∈ Ψ.support, ∑ α ∈ Ψ.support, (conj (Ψ β) * Ψ α) *
        ((pairPot (periodize L V) x : ℂ) *
          (conj (symWave L (M + 2) β x) * symWave L (M + 2) α x)) := by
    intro x
    have h := Complex.conj_mul' (stateFn L (M + 2) Ψ x)
    push_cast
    rw [← h]
    unfold stateFn
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [map_mul]
    ring
  have hint : ∀ β α, Integrable (fun x : Conf (M + 2) => (conj (Ψ β) * Ψ α) *
      ((pairPot (periodize L V) x : ℂ) *
        (conj (symWave L (M + 2) β x) * symWave L (M + 2) α x)))
      (volume.restrict (cellN L (M + 2))) := fun β α =>
    Energy_integrable L (continuous_const.mul
      ((Complex.continuous_ofReal.comp (Energy_pairPot_continuous hVc (M + 2))).mul
        ((Complex.continuous_conj.comp (hcΦ β)).mul (hcΦ α))))
  rw [← integral_complex_ofReal, integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun β _ => integrable_finsetSum _ fun α _ => hint β α]
  simp_rw [integral_finsetSum _ fun α _ => hint _ α, integral_const_mul]
  set G : Idx → Idx → Idx → Idx → ℂ := fun p q r s =>
    (((L ^ 3)⁻¹ : ℝ) : ℂ) * ft V (mom L (p - r)) * (if q + (p - r) = s then 1 else 0) with hG
  have hkey : ∀ α ∈ Ψ.support, ∑ β ∈ Ψ.support, conj (Ψ β) * Ψ α *
      ∫ x in cellN L (M + 2), (pairPot (periodize L V) x : ℂ) *
        (conj (symWave L (M + 2) β x) * symWave L (M + 2) α x) =
      ∑ p ∈ A, ∑ q ∈ A, ∑ r ∈ A, intTerm L V Ψ (p, q, p - r, α) := by
    intro α hα
    have hα0 := Finsupp.mem_support_iff.1 hα
    have hαN := hΨ α hα0
    rw [Finset.sum_congr rfl fun β hβ => by
      rw [Energy_pot_matrix hV hL M hαN (hΨ β (Finsupp.mem_support_iff.1 hβ)) (hA α hα)
        (hA β hβ)]]
    calc ∑ β ∈ Ψ.support, conj (Ψ β) * Ψ α * ∑ q ∈ A, ∑ s ∈ A, ∑ p ∈ A, ∑ r ∈ A,
          ((if β = (a4 p q r s α).2 then (a4 p q r s α).1 else 0 : ℝ) : ℂ) * G p q r s
        = ∑ q ∈ A, ∑ s ∈ A, ∑ p ∈ A, ∑ r ∈ A, ∑ β ∈ Ψ.support, conj (Ψ β) * Ψ α *
          (((if β = (a4 p q r s α).2 then (a4 p q r s α).1 else 0 : ℝ) : ℂ) * G p q r s) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ q ∈ A, ∑ s ∈ A, ∑ p ∈ A, ∑ r ∈ A, conj (Ψ (a4 p q r s α).2) * Ψ α *
          (((a4 p q r s α).1 : ℂ) * G p q r s) := by
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s _ =>
            Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_eq_single (a4 p q r s α).2]
          · simp
          · intro β _ hβ
            simp [hβ]
          · intro hY
            simp [Finsupp.notMem_support_iff.1 hY]
      _ = ∑ q ∈ A, ∑ p ∈ A, ∑ r ∈ A, ∑ s ∈ A, conj (Ψ (a4 p q r s α).2) * Ψ α *
          (((a4 p q r s α).1 : ℂ) * G p q r s) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ q ∈ A, ∑ p ∈ A, ∑ r ∈ A, intTerm L V Ψ (p, q, p - r, α) := by
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p _ =>
            Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_eq_single (q + (p - r))]
          · simp only [hG, intTerm, sub_sub_cancel, ite_true]
            push_cast
            ring
          · intro s _ hs
            simp [hG, Ne.symm hs]
          · intro hs
            have h0 : α (q + (p - r)) = 0 := by
              by_contra h
              exact hs (hmem α _ hα0 (Nat.pos_of_ne_zero h))
            simp [a4, h0]
      _ = ∑ p ∈ A, ∑ q ∈ A, ∑ r ∈ A, intTerm L V Ψ (p, q, p - r, α) := Finset.sum_comm
  rw [Finset.sum_comm, Finset.sum_congr rfl hkey]
  rw [hTdef, Finset.sum_image (by
    rintro ⟨p, q, r, α⟩ _ ⟨p', q', r', α'⟩ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, h3, rfl⟩ := h
    rw [sub_right_inj] at h3
    rw [h3])]
  simp only [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_comm]

/-! ### The position form of (2.1) [ham] and `H ≥ 0` -/

private lemma Energy_kinD_continuous {N : ℕ} {Φ : Conf N → ℂ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Continuous (kinD Φ) := by
  have h := hΦ.continuous_fderiv (by simp)
  unfold kinD
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun a _ =>
    (h.clm_apply continuous_const).norm.pow 2

private lemma Energy_kinD_nonneg {N : ℕ} (Φ : Conf N → ℂ) (x : Conf N) : 0 ≤ kinD Φ x := by
  unfold kinD
  positivity

private lemma Energy_pairPot_nonneg {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} {N : ℕ}
    (x : Conf N) : 0 ≤ pairPot (periodize L V) x := by
  unfold pairPot
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs
  · exact tsum_nonneg fun n => hV.nonneg _
  · exact le_rfl

/-- Position form of (2.1) [ham]: a finitely supported normalized `N`-particle state `Ψ` with
energy `E` gives a normalized wave function `Φ_Ψ` on `[0, L]^{3N}` with torus energy `E`. -/
theorem stateFn_norm_energy {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L) {N : ℕ}
    (Ψ : Occ →₀ ℂ) {E : ℝ} (hΨ : IsNState N Ψ) (hE : HasEnergy L V Ψ E) :
    ∫ x in cellN L N, ‖stateFn L N Ψ x‖ ^ 2 = 1 ∧ torusEnergy L V (stateFn L N Ψ) = E := by
  refine ⟨stateFn_norm hL Ψ hΨ, ?_⟩
  obtain ⟨K, I, hK, hI, hEKI⟩ := hE
  have hK' := (stateFn_kin_hasSum hL Ψ hΨ.2).unique hK
  have hI' := (stateFn_pot_hasSum hV hL Ψ hΨ.2).unique hI
  have hΦ := Energy_stateFn_contDiff L N Ψ
  have hkc : Continuous (kinD (stateFn L N Ψ)) := Energy_kinD_continuous hΦ
  have hpc : Continuous fun x => pairPot (periodize L V) x * ‖stateFn L N Ψ x‖ ^ 2 :=
    (Energy_pairPot_continuous (periodize_continuous hV hL) N).mul (hΦ.continuous.norm.pow 2)
  unfold torusEnergy
  rw [integral_add (Energy_integrable L hkc) (Energy_integrable L hpc)]
  apply Complex.ofReal_injective
  rw [hEKI, ← hK', ← hI']
  push_cast
  ring

/-- The Hamiltonian (2.1) [ham] is nonnegative on finitely supported states. -/
theorem hamiltonianNonneg {V : R3 → ℝ} (hV : PotentialHyp V) : Stmt.HamiltonianNonneg V := by
  intro L hL Ψ E hE
  obtain ⟨K, I, hK, hI, hEKI⟩ := hE
  set Ms : Finset ℕ := Ψ.support.image Occ.num with hMs
  set Ψs : ℕ → Occ →₀ ℂ := fun M => Ψ.filter fun α => α.num = M with hΨs
  have hΨs_apply : ∀ M α, Ψs M α = if α.num = M then Ψ α else 0 := fun M α => by
    simp only [hΨs, Finsupp.filter_apply]
  have hsec : ∀ M α, Ψs M α ≠ 0 → α.num = M := by
    intro M α h
    rw [hΨs_apply] at h
    by_contra h1
    simp [h1] at h
  have hnumM : ∀ α, Ψ α ≠ 0 → α.num ∈ Ms := fun α hα =>
    Finset.mem_image_of_mem _ (Finsupp.mem_support_iff.2 hα)
  have hkin : ∀ α, ∑ M ∈ Ms, kinTerm L (Ψs M) α = kinTerm L Ψ α := by
    intro α
    by_cases hα : Ψ α = 0
    · simp [kinTerm, hΨs_apply, hα]
    · rw [Finset.sum_eq_single α.num]
      · simp [kinTerm, hΨs_apply]
      · intro M _ hM
        simp [kinTerm, hΨs_apply, Ne.symm hM]
      · intro h
        exact absurd (hnumM α hα) h
  have hint : ∀ i, ∑ M ∈ Ms, intTerm L V (Ψs M) i = intTerm L V Ψ i := by
    rintro ⟨p, q, u, α⟩
    by_cases h1 : (a4 p q (p - u) (q + u) α).1 = 0
    · simp [intTerm, h1]
    have hnum := Energy_a4_num h1
    by_cases hα : Ψ α = 0
    · simp [intTerm, hΨs_apply, hα]
    rw [Finset.sum_eq_single α.num]
    · simp [intTerm, hΨs_apply, hnum]
    · intro M _ hM
      simp [intTerm, hΨs_apply, Ne.symm hM]
    · intro h
      exact absurd (hnumM α hα) h
  have hK2 := hasSum_sum fun M (_ : M ∈ Ms) => stateFn_kin_hasSum hL (Ψs M) (hsec M)
  have hI2 := hasSum_sum fun M (_ : M ∈ Ms) => stateFn_pot_hasSum hV hL (Ψs M) (hsec M)
  simp_rw [hkin] at hK2
  simp_rw [hint] at hI2
  have e1 := hK.unique hK2
  have e2 := hI.unique hI2
  have hE' : E = (∑ M ∈ Ms, ∫ x in cellN L M, kinD (stateFn L M (Ψs M)) x) +
      ∑ M ∈ Ms, ∫ x in cellN L M, pairPot (periodize L V) x * ‖stateFn L M (Ψs M) x‖ ^ 2 := by
    apply Complex.ofReal_injective
    rw [hEKI, e1, e2]
    push_cast
    ring
  rw [hE']
  refine add_nonneg (Finset.sum_nonneg fun M _ => integral_nonneg fun x => ?_)
    (Finset.sum_nonneg fun M _ => integral_nonneg fun x => ?_)
  · exact Energy_kinD_nonneg _ x
  · exact mul_nonneg (Energy_pairPot_nonneg hV x) (sq_nonneg _)

end LHYUpper
