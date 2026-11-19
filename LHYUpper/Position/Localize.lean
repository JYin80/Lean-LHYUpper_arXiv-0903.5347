import LHYUpper.Scattering.Solution
import LHYUpper.Position.Basic
import LHYUpper.Position.Periodize
import LHYUpper.Position.Profile

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- The map `𝓕^u Φ(x) = Φ(x) ∏_i h(x_i + u)` of (12.4) [defFu]. -/
def localize (ℓ L : ℝ) (u : R3) {N : ℕ} (Φ : Conf N → ℂ) (x : Conf N) : ℂ :=
  Φ x * ∏ i, (cutoff ℓ L (x i + u) : ℂ)

/-! ### Unfolding of `(ℝ³)^N` over the lattice `(Lℤ³)^N` -/

private lemma Loc_lat_apply (L : ℝ) (n : Idx) (a : Fin 3) : (lat L n) a = L * (n a : ℝ) := rfl

/-- The basis `L e_a` of `ℝ³`. -/
private def Loc_basis3 {L : ℝ} (hL : 0 < L) : Module.Basis (Fin 3) ℝ R3 :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map (LinearEquiv.smulOfNeZero ℝ R3 L hL.ne')

private lemma Loc_basis3_repr {L : ℝ} (hL : 0 < L) (x : R3) (i : Fin 3) :
    (Loc_basis3 hL).repr x i = L⁻¹ * x i := by
  simp [Loc_basis3, Units.smul_def]

private lemma Loc_basis3_apply {L : ℝ} (hL : 0 < L) (i a : Fin 3) :
    (Loc_basis3 hL) i a = if a = i then L else 0 := by
  simp [Loc_basis3]

/-- The basis `L e_{ia}` of `(ℝ³)^N`. -/
private def Loc_basis {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Module.Basis (Σ _ : Fin N, Fin 3) ℝ (Conf N) :=
  Pi.basis fun _ => Loc_basis3 hL

/-- The lattice vector `(L n_i)_i` of `(Lℤ³)^N`. -/
private def Loc_latN (L : ℝ) {N : ℕ} (n : Fin N → Idx) : Conf N := fun i => lat L (n i)

private lemma Loc_mem_span {L : ℝ} (hL : 0 < L) {N : ℕ} (x : Conf N) :
    x ∈ Submodule.span ℤ (Set.range (Loc_basis hL N)) ↔ ∃ n : Fin N → Idx, x = Loc_latN L n := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun i a => c ⟨i, a⟩, ?_⟩
    funext i
    ext a
    simp [Loc_basis, Loc_latN, Loc_lat_apply, Finset.sum_apply, Loc_basis3_apply,
      Fintype.sum_sigma, Pi.single_apply]
    ring
  · rintro ⟨n, rfl⟩
    refine ⟨fun p => n p.1 p.2, ?_⟩
    funext i
    ext a
    simp [Loc_basis, Loc_latN, Loc_lat_apply, Finset.sum_apply, Loc_basis3_apply,
      Fintype.sum_sigma, Pi.single_apply]
    ring

private lemma Loc_latN_injective {L : ℝ} (hL : 0 < L) (N : ℕ) :
    Function.Injective (Loc_latN L (N := N)) := by
  intro m n h
  funext i a
  have := congrArg (fun v : Conf N => v i a) h
  simp only [Loc_latN, Loc_lat_apply] at this
  have h2 : (m i a : ℝ) = n i a := mul_left_cancel₀ hL.ne' this
  exact_mod_cast h2

/-- The lattice `(Lℤ³)^N` as an additive subgroup of `(ℝ³)^N`, identified with `(ℤ³)^N`. -/
private def Loc_equiv {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (Fin N → Idx) ≃ (Submodule.span ℤ (Set.range (Loc_basis hL N))).toAddSubgroup :=
  Equiv.ofBijective (fun n => ⟨Loc_latN L n, (Loc_mem_span hL _).2 ⟨n, rfl⟩⟩)
    ⟨fun m n h => Loc_latN_injective hL N (congrArg Subtype.val h),
     fun g => by
       obtain ⟨n, hn⟩ := (Loc_mem_span hL g.1).1 g.2
       exact ⟨n, Subtype.ext hn.symm⟩⟩

private lemma Loc_cellN_eq {L : ℝ} (hL : 0 < L) (N : ℕ) :
    parallelepiped (Loc_basis hL N) = cellN L N := by
  rw [parallelepiped_basis_eq]
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Icc, Loc_basis, Pi.basis_repr, Loc_basis3_repr, cellN,
    cell]
  constructor
  · intro h i a
    have := h ⟨i, a⟩
    rw [mul_nonneg_iff_of_pos_left (inv_pos.2 hL), inv_mul_le_iff₀ hL, mul_one] at this
    exact this
  · intro h p
    rw [mul_nonneg_iff_of_pos_left (inv_pos.2 hL), inv_mul_le_iff₀ hL, mul_one]
    exact h p.1 p.2

/-- Unfolding of `(ℝ³)^N` over `(Lℤ³)^N`: `∫ G = Σ_n ∫_{[0,L]^{3N}} G(x + Ln)`. -/
private lemma Loc_unfold {L : ℝ} (hL : 0 < L) {N : ℕ} {G : Conf N → ℝ} (hG : Integrable G) :
    ∫ x, G x = ∑' n : Fin N → Idx, ∫ x in cellN L N, G (x + Loc_latN L n) := by
  have : Countable (Submodule.span ℤ (Set.range (Loc_basis hL N))).toAddSubgroup :=
    (Loc_equiv hL N).symm.injective.countable
  rw [(ZSpan.isAddFundamentalDomain' (Loc_basis hL N) volume).integral_eq_tsum'' G hG,
    ← (Loc_equiv hL N).tsum_eq]
  refine tsum_congr fun n => ?_
  have hae : ZSpan.fundamentalDomain (Loc_basis hL N) =ᵐ[volume] cellN L N := by
    rw [← Loc_cellN_eq hL N]
    exact ZSpan.fundamentalDomain_ae_parallelepiped _ _
  rw [setIntegral_congr_set hae]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Loc_equiv]
  change G (Loc_latN L n + x) = G (x + Loc_latN L n)
  rw [add_comm]


/-- A box `∏_b [α_b, β_b]` of `ℝ³` is compact. -/
private lemma Loc_box_compact (α β : Fin 3 → ℝ) :
    IsCompact {y : R3 | ∀ b, y b ∈ Set.Icc (α b) (β b)} := by
  have : {y : R3 | ∀ b, y b ∈ Set.Icc (α b) (β b)} =
      (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) '' Set.pi Set.univ (fun b => Set.Icc (α b) (β b)) := by
    ext y
    constructor
    · intro hy
      exact ⟨WithLp.ofLp y, fun b _ => hy b, rfl⟩
    · rintro ⟨z, hz, rfl⟩ b
      exact hz b (Set.mem_univ b)
  rw [this]
  exact (isCompact_univ_pi fun b => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

private lemma Loc_cellN_compact (L : ℝ) (N : ℕ) : IsCompact (cellN L N) := by
  have h : cellN L N = Set.pi Set.univ
      (fun _ : Fin N => {y : R3 | ∀ b, y b ∈ Set.Icc ((fun _ => (0 : ℝ)) b) ((fun _ => L) b)}) := by
    ext x
    simp only [cellN, cell, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc]
  rw [h]
  exact isCompact_univ_pi fun _ => Loc_box_compact _ _

private lemma Loc_cellN_meas (L : ℝ) (N : ℕ) : MeasurableSet (cellN L N) :=
  (Loc_cellN_compact L N).isClosed.measurableSet

/-- A continuous function vanishing unless every `x_{ja} + u_a ∈ [-ℓ/2, L + ℓ/2]` is
integrable. -/
private lemma Loc_integrable {ℓ L : ℝ} (u : R3) {N : ℕ} {G : Conf N → ℝ} (hG : Continuous G)
    (hs : ∀ x : Conf N, (∃ j b, x j b + u b ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2)) → G x = 0) :
    Integrable G := by
  refine hG.integrable_of_hasCompactSupport (HasCompactSupport.intro
    (K := Set.pi Set.univ fun _ : Fin N =>
      {y : R3 | ∀ b, y b ∈ Set.Icc (-(ℓ / 2) - u b) (L + ℓ / 2 - u b)})
    (isCompact_univ_pi fun _ => Loc_box_compact _ _) ?_)
  intro x hx
  apply hs
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq, not_forall] at hx
  obtain ⟨j, b, hb⟩ := hx
  refine ⟨j, b, fun h => hb ?_⟩
  simp only [Set.mem_Icc] at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- The number `M ≥ 1 + Σ_b |u_b| / L` bounding the translates that meet the support. -/
private def Loc_M (L : ℝ) (u : R3) : ℕ := ⌈(∑ b, |u b|) / L⌉₊ + 1

/-- The integers `|k| ≤ M + 2`. -/
private def Loc_S (L : ℝ) (u : R3) : Finset ℤ :=
  Finset.Icc (-((Loc_M L u : ℤ) + 2)) ((Loc_M L u : ℤ) + 2)

/-- The lattice points `n ∈ (ℤ³)^N` with all `|n_{ja}| ≤ M + 2`. -/
private def Loc_F (L : ℝ) (u : R3) (N : ℕ) : Finset (Fin N → Idx) :=
  Fintype.piFinset fun _ => Fintype.piFinset fun _ => Loc_S L u

private lemma Loc_u_le {L : ℝ} (hL : 0 < L) (u : R3) (b : Fin 3) :
    |u b| + L ≤ (Loc_M L u : ℝ) * L := by
  have h1 : |u b| ≤ ∑ c, |u c| :=
    Finset.single_le_sum (f := fun c => |u c|) (fun c _ => abs_nonneg _) (Finset.mem_univ b)
  have h2 : (∑ c, |u c|) / L ≤ ⌈(∑ c, |u c|) / L⌉₊ := Nat.le_ceil _
  rw [div_le_iff₀ hL] at h2
  unfold Loc_M
  push_cast
  rw [add_mul, one_mul]
  linarith

/-- For `t ∈ [0, L]` and `k ∉ S`, the point `t + u_b + kL` lies outside `[-ℓ/2, L + ℓ/2]`. -/
private lemma Loc_far {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (u : R3) (b : Fin 3) {t : ℝ}
    (ht0 : 0 ≤ t) (htL : t ≤ L) {k : ℤ} (hk : k ∉ Loc_S L u) :
    t + u b + k * L ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) := by
  have hL : 0 < L := by linarith
  have hM := Loc_u_le hL u b
  have hu1 := neg_abs_le (u b)
  have hu2 := le_abs_self (u b)
  unfold Loc_S at hk
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hk
  intro h
  rw [Set.mem_Icc] at h
  rcases hk with hk | hk
  · have hk' : (k : ℝ) + ((Loc_M L u : ℝ) + 3) ≤ 0 := by
      have : k + ((Loc_M L u : ℤ) + 3) ≤ 0 := by omega
      exact_mod_cast this
    nlinarith [mul_le_mul_of_nonneg_right hk' hL.le]
  · have hk' : 0 ≤ (k : ℝ) - ((Loc_M L u : ℝ) + 3) := by
      have : 0 ≤ k - ((Loc_M L u : ℤ) + 3) := by omega
      exact_mod_cast this
    nlinarith [mul_le_mul_of_nonneg_right hk' hL.le]

private lemma Loc_coord_shift (L : ℝ) {N : ℕ} (u : R3) (x : Conf N) (n : Fin N → Idx)
    (j : Fin N) (b : Fin 3) :
    (x + Loc_latN L n) j b + u b = x j b + u b + (n j b : ℝ) * L := by
  simp only [Pi.add_apply, PiLp.add_apply, Loc_latN, Loc_lat_apply]
  ring

/-- Only the translates `n ∈ F` contribute: `∫ G = ∫_{[0,L]^{3N}} Σ_{n ∈ F} G(x + Ln)`. -/
private lemma Loc_unfold_supp {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (u : R3) {N : ℕ}
    {G : Conf N → ℝ} (hG : Continuous G)
    (hs : ∀ x : Conf N, (∃ j b, x j b + u b ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2)) → G x = 0) :
    ∫ x, G x = ∫ x in cellN L N, ∑ n ∈ Loc_F L u N, G (x + Loc_latN L n) := by
  have hL : 0 < L := by linarith
  have hGi := Loc_integrable u hG hs
  rw [Loc_unfold hL hGi, tsum_eq_sum (s := Loc_F L u N)]
  · rw [integral_finsetSum]
    intro n _
    exact (hGi.comp_add_right (Loc_latN L n)).integrableOn
  · intro n hn
    refine setIntegral_eq_zero_of_forall_eq_zero fun x hx => hs _ ?_
    unfold Loc_F at hn
    rw [Fintype.mem_piFinset, not_forall] at hn
    obtain ⟨j, hj⟩ := hn
    rw [Fintype.mem_piFinset, not_forall] at hj
    obtain ⟨b, hb⟩ := hj
    refine ⟨j, b, ?_⟩
    rw [Loc_coord_shift]
    exact Loc_far hℓ hℓL u b (hx j b).1 (hx j b).2 hb

/-- `Σ_{n ∈ F} ∏_{j,b} g_{jb}(x_{jb} + u_b + n_{jb} L) = ∏_{j,b} Σ_k g_{jb}(x_{jb} + u_b + kL)`
on `[0, L]^{3N}`. -/
private lemma Loc_sum_prod {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (u : R3) {N : ℕ}
    {g : Fin N → Fin 3 → ℝ → ℝ}
    (hg : ∀ j b y, y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) → g j b y = 0)
    {x : Conf N} (hx : x ∈ cellN L N) :
    ∑ n ∈ Loc_F L u N, ∏ j, ∏ b, g j b ((x + Loc_latN L n) j b + u b) =
      ∏ j, ∏ b, ∑' k : ℤ, g j b (x j b + u b + k * L) := by
  simp_rw [Loc_coord_shift]
  have e2 : ∀ j b, ∑' k : ℤ, g j b (x j b + u b + k * L) =
      ∑ k ∈ Loc_S L u, g j b (x j b + u b + k * L) := fun j b =>
    tsum_eq_sum fun k hk => hg j b _ (Loc_far hℓ hℓL u b (hx j b).1 (hx j b).2 hk)
  simp_rw [e2]
  unfold Loc_F
  symm
  simp_rw [Finset.prod_univ_sum]

/-- The product form of the unfolding: for `K` periodic and `g_{jb}` supported in
`[-ℓ/2, L + ℓ/2]`,
`∫ K ∏ g_{jb}(x_{jb} + u_b) = ∫_{[0,L]^{3N}} K ∏ Σ_k g_{jb}(x_{jb} + u_b + kL)`. -/
private lemma Loc_unfold_prod {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (u : R3) {N : ℕ}
    {K : Conf N → ℝ} (hK : Continuous K) (hKp : ∀ x n, K (x + Loc_latN L n) = K x)
    {g : Fin N → Fin 3 → ℝ → ℝ} (hgc : ∀ j b, Continuous (g j b))
    (hg : ∀ j b y, y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) → g j b y = 0) :
    Integrable (fun x => K x * ∏ j, ∏ b, g j b (x j b + u b)) ∧
    ∫ x, K x * ∏ j, ∏ b, g j b (x j b + u b) =
      ∫ x in cellN L N, K x * ∏ j, ∏ b, ∑' k : ℤ, g j b (x j b + u b + k * L) := by
  have hGc : Continuous (fun x : Conf N => K x * ∏ j, ∏ b, g j b (x j b + u b)) := by
    refine hK.mul (continuous_finsetProd _ fun j _ => continuous_finsetProd _ fun b _ => ?_)
    exact (hgc j b).comp (by fun_prop)
  have hGs : ∀ x : Conf N, (∃ j b, x j b + u b ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2)) →
      K x * ∏ j, ∏ b, g j b (x j b + u b) = 0 := by
    rintro x ⟨j, b, h⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ j)
      (Finset.prod_eq_zero (Finset.mem_univ b) (hg j b _ h)), mul_zero]
  refine ⟨Loc_integrable u hGc hGs, ?_⟩
  rw [Loc_unfold_supp hℓ hℓL u hGc hGs]
  refine setIntegral_congr_fun (Loc_cellN_meas L N) fun x hx => ?_
  simp only [hKp, ← Finset.mul_sum]
  rw [Loc_sum_prod hℓ hℓL u hg hx]

/-! ### The cut-off `∏_i h(x_i + u)` -/

private lemma Loc_prof_zero {ℓ L : ℝ} (hℓ : 0 < ℓ) {y : ℝ}
    (hy : y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2)) : prof ℓ L y = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hy (tsupport_prof hℓ L h)

private lemma Loc_dprof_zero {ℓ L : ℝ} (hℓ : 0 < ℓ) {y : ℝ}
    (hy : y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2)) : deriv (prof ℓ L) y = 0 := by
  by_contra h0
  exact hy (tsupport_prof hℓ L (support_deriv_subset (f := prof ℓ L) h0))

private lemma Loc_prof_cont (ℓ L : ℝ) : Continuous (prof ℓ L) := (prof_contDiff ℓ L).continuous

private lemma Loc_dprof_cont (ℓ L : ℝ) : Continuous (deriv (prof ℓ L)) :=
  (prof_contDiff ℓ L).continuous_deriv (by simp)

/-- `(q²)' = 2 q q'`. -/
private lemma Loc_deriv_sq (ℓ L : ℝ) :
    deriv (fun y => prof ℓ L y ^ 2) = fun y => 2 * prof ℓ L y * deriv (prof ℓ L) y := by
  funext y
  have hd := (((prof_contDiff ℓ L).differentiable (by simp)) y).hasDerivAt
  have h2 : HasDerivAt (fun y => prof ℓ L y ^ 2)
      ((2 : ℕ) * prof ℓ L y ^ (2 - 1) * deriv (prof ℓ L) y) y := hd.pow 2
  rw [h2.deriv]
  simp

private lemma Loc_cutoff_prod (ℓ L : ℝ) (u : R3) {N : ℕ} (x : Conf N) :
    ∏ i, (cutoff ℓ L (x i + u) : ℂ) = ((∏ j, ∏ b, prof ℓ L (x j b + u b) : ℝ) : ℂ) := by
  simp [cutoff, Complex.ofReal_prod, PiLp.add_apply]

private lemma Loc_localize_eq (ℓ L : ℝ) (u : R3) {N : ℕ} (Φ : Conf N → ℂ) :
    localize ℓ L u Φ = fun x => Φ x * ((∏ j, ∏ b, prof ℓ L (x j b + u b) : ℝ) : ℂ) := by
  funext x
  rw [localize, Loc_cutoff_prod]

private lemma Loc_norm_sq (ℓ L : ℝ) (u : R3) {N : ℕ} (Φ : Conf N → ℂ) (x : Conf N) :
    ‖localize ℓ L u Φ x‖ ^ 2 = ‖Φ x‖ ^ 2 * ∏ j, ∏ b, prof ℓ L (x j b + u b) ^ 2 := by
  rw [Loc_localize_eq, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  simp only [← Finset.prod_pow]

/-- `∏_{j,b} (c if (j,b) = (i,a), else f_{jb}) = c ∏_{j,b} (1 if (j,b) = (i,a), else f_{jb})`. -/
private lemma Loc_prod_ite {N : ℕ} (i : Fin N) (a : Fin 3) (c : ℝ) (f : Fin N → Fin 3 → ℝ) :
    ∏ j, ∏ b, (if j = i ∧ b = a then c else f j b) =
      c * ∏ j, ∏ b, (if j = i ∧ b = a then 1 else f j b) := by
  have h : ∀ j b, (if j = i ∧ b = a then c else f j b) =
      (if j = i ∧ b = a then c else 1) * (if j = i ∧ b = a then 1 else f j b) := by
    intro j b
    split_ifs <;> simp
  simp_rw [h, Finset.prod_mul_distrib]
  congr 1
  rw [Fintype.prod_eq_single i (fun j hj => by simp [hj]),
    Fintype.prod_eq_single a (fun b hb => by simp [hb])]
  simp

/-- The factor `C(x) = ∏_{(j,b) ≠ (i,a)} q(x_{jb} + u_b)` of `∂_{ia}` of the cut-off. -/
private def Loc_C (ℓ L : ℝ) (u : R3) {N : ℕ} (i : Fin N) (a : Fin 3) (x : Conf N) : ℝ :=
  ∏ j, ∏ b, (if j = i ∧ b = a then 1 else prof ℓ L (x j b + u b))

/-- The factor `g_{jb} = s` at `(j,b) = (i,a)` and `q²` elsewhere. -/
private def Loc_g (ℓ L : ℝ) {N : ℕ} (i : Fin N) (a : Fin 3) (s : ℝ → ℝ) (j : Fin N) (b : Fin 3)
    (y : ℝ) : ℝ :=
  if j = i ∧ b = a then s y else prof ℓ L y ^ 2

/-- `∏_{j,b} g_{jb}(x_{jb} + u_b) = s(x_{ia} + u_a) C(x)²`. -/
private lemma Loc_prod_C (ℓ L : ℝ) (u : R3) {N : ℕ} (s : ℝ → ℝ) (x : Conf N) (i : Fin N)
    (a : Fin 3) :
    ∏ j, ∏ b, Loc_g ℓ L i a s j b (x j b + u b) = s (x i a + u a) * Loc_C ℓ L u i a x ^ 2 := by
  simp only [Loc_g]
  have h : ∀ j b, (if j = i ∧ b = a then s (x j b + u b) else prof ℓ L (x j b + u b) ^ 2) =
      (if j = i ∧ b = a then s (x i a + u a) else prof ℓ L (x j b + u b) ^ 2) := by
    intro j b
    split_ifs with hh
    · obtain ⟨rfl, rfl⟩ := hh
      rfl
    · rfl
  simp_rw [h]
  rw [Loc_prod_ite, Loc_C, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun b _ => ?_
  split_ifs <;> simp

/-- `∏_{j,b} Σ_k g_{jb}(x_{jb} + u_b + kL) = Σ_k s(x_{ia} + u_a + kL)`. -/
private lemma Loc_prod_tsum {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (u : R3) {N : ℕ}
    (s : ℝ → ℝ) (x : Conf N) (i : Fin N) (a : Fin 3) :
    ∏ j, ∏ b, ∑' k : ℤ, Loc_g ℓ L i a s j b (x j b + u b + k * L) =
      ∑' k : ℤ, s (x i a + u a + k * L) := by
  simp only [Loc_g]
  have h : ∀ j b, ∑' k : ℤ, (if j = i ∧ b = a then s (x j b + u b + k * L)
      else prof ℓ L (x j b + u b + k * L) ^ 2) =
      (if j = i ∧ b = a then ∑' k : ℤ, s (x i a + u a + k * L) else 1) := by
    intro j b
    by_cases hh : j = i ∧ b = a
    · obtain ⟨rfl, rfl⟩ := hh
      simp
    · simp only [hh, ite_false]
      exact (prof_sq_hasSum hℓ hℓL _).tsum_eq
  simp_rw [h]
  rw [Loc_prod_ite]
  simp

/-- The line derivative: `t ↦ f(x + t v)` has derivative `Df(x) v` at `0`. -/
private lemma Loc_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ}
    {f : Conf N → F} {x : Conf N} (v : Conf N) (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℝ) hl

private lemma Loc_line_coord {N : ℕ} (x : Conf N) (i : Fin N) (a : Fin 3) (t : ℝ) (j : Fin N)
    (b : Fin 3) :
    (x + t • (Pi.single i (EuclideanSpace.single a (1 : ℝ)) : Conf N)) j b =
      x j b + (if j = i ∧ b = a then t else 0) := by
  by_cases hj : j = i
  · subst hj
    by_cases hb : b = a
    · subst hb
      simp
    · simp [hb]
  · simp [hj]

/-- Along the line `x + t e_{ia}`: `∏_{j,b} q = q(x_{ia} + u_a + t) C(x)`. -/
private lemma Loc_H_line (ℓ L : ℝ) (u : R3) {N : ℕ} (x : Conf N) (i : Fin N) (a : Fin 3)
    (t : ℝ) :
    ∏ j, ∏ b, prof ℓ L ((x + t • (Pi.single i (EuclideanSpace.single a (1 : ℝ)) : Conf N)) j b +
      u b) = prof ℓ L (x i a + u a + t) * Loc_C ℓ L u i a x := by
  rw [Loc_C, ← Loc_prod_ite]
  refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun b _ => ?_
  rw [Loc_line_coord]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    congr 1
    ring
  · simp

private lemma Loc_H_zero (ℓ L : ℝ) (u : R3) {N : ℕ} (x : Conf N) (i : Fin N) (a : Fin 3) :
    ∏ j, ∏ b, prof ℓ L (x j b + u b) = prof ℓ L (x i a + u a) * Loc_C ℓ L u i a x := by
  have := Loc_H_line ℓ L u x i a 0
  simpa using this

private lemma Loc_H_contDiff (ℓ L : ℝ) (u : R3) (N : ℕ) :
    ContDiff ℝ 1 (fun x : Conf N => ∏ j, ∏ b, prof ℓ L (x j b + u b)) := by
  refine contDiff_prod fun j _ => contDiff_prod fun b _ => ?_
  exact ((prof_contDiff ℓ L).of_le (by simp)).comp (by fun_prop)

/-- `∂_{ia} (Φ ∏ q) = ∂_{ia} Φ · q C + Φ · q' C`. -/
private lemma Loc_fderiv_localize (ℓ L : ℝ) (u : R3) {N : ℕ} {Φ : Conf N → ℂ}
    (hd : ContDiff ℝ 1 Φ) (x : Conf N) (i : Fin N) (a : Fin 3) :
    fderiv ℝ (localize ℓ L u Φ) x (Pi.single i (EuclideanSpace.single a 1)) =
      fderiv ℝ Φ x (Pi.single i (EuclideanSpace.single a 1)) *
          ((prof ℓ L (x i a + u a) * Loc_C ℓ L u i a x : ℝ) : ℂ) +
        Φ x * ((deriv (prof ℓ L) (x i a + u a) * Loc_C ℓ L u i a x : ℝ) : ℂ) := by
  set v : Conf N := Pi.single i (EuclideanSpace.single a 1) with hv
  have hHc := Loc_H_contDiff ℓ L u N
  have hFc : ContDiff ℝ 1 (localize ℓ L u Φ) := by
    rw [Loc_localize_eq]
    exact hd.mul (Complex.ofRealCLM.contDiff.comp hHc)
  have hΦ : DifferentiableAt ℝ Φ x := hd.differentiable (by simp) x
  have h1 := Loc_line v (hFc.differentiable (by simp) x)
  have hq : HasDerivAt (prof ℓ L) (deriv (prof ℓ L) (x i a + u a + 0)) (x i a + u a + 0) :=
    ((prof_contDiff ℓ L).differentiable (by simp) _).hasDerivAt
  have hH : HasDerivAt (fun t : ℝ => ∏ j, ∏ b, prof ℓ L ((x + t • v) j b + u b))
      (deriv (prof ℓ L) (x i a + u a) * Loc_C ℓ L u i a x) 0 := by
    simp_rw [hv, Loc_H_line]
    have := (hq.comp_const_add (x i a + u a) 0).mul_const (Loc_C ℓ L u i a x)
    simpa using this
  have h2 := (Loc_line v hΦ).mul hH.ofReal_comp
  rw [Loc_localize_eq] at h1
  have h3 := h1.unique h2
  rw [Loc_localize_eq, h3]
  simp only [zero_smul, add_zero]
  rw [Loc_H_zero ℓ L u x i a]

/-- `‖A q C + P q' C‖² = ‖A‖² (qC)² + ‖P‖² (q'C)² + Re(P̄ A) · 2 q q' C²`. -/
private lemma Loc_expand (A P : ℂ) (q q' C : ℝ) :
    ‖A * ((q * C : ℝ) : ℂ) + P * ((q' * C : ℝ) : ℂ)‖ ^ 2 =
      ‖A‖ ^ 2 * (q ^ 2 * C ^ 2) + ‖P‖ ^ 2 * (q' ^ 2 * C ^ 2) +
        (P.re * A.re + P.im * A.im) * (2 * q * q' * C ^ 2) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

private lemma Loc_g_cont (ℓ L : ℝ) {N : ℕ} (i : Fin N) (a : Fin 3) {s : ℝ → ℝ}
    (hs : Continuous s) (j : Fin N) (b : Fin 3) : Continuous (Loc_g ℓ L i a s j b) := by
  by_cases hh : j = i ∧ b = a
  · have : Loc_g ℓ L i a s j b = s := funext fun y => by
      unfold Loc_g
      split_ifs
      rfl
    rw [this]
    exact hs
  · have : Loc_g ℓ L i a s j b = fun y => prof ℓ L y ^ 2 :=
      funext fun y => by
        unfold Loc_g
        split_ifs
        rfl
    rw [this]
    exact (Loc_prof_cont ℓ L).pow 2

private lemma Loc_g_zero {ℓ L : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (i : Fin N) (a : Fin 3) {s : ℝ → ℝ}
    (hs : ∀ y, y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) → s y = 0) (j : Fin N) (b : Fin 3) (y : ℝ)
    (hy : y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2)) : Loc_g ℓ L i a s j b y = 0 := by
  unfold Loc_g
  split_ifs
  · exact hs y hy
  · rw [Loc_prof_zero hℓ hy]
    ring

private lemma Loc_fderiv_periodic {L : ℝ} {N : ℕ} {Φ : Conf N → ℂ} (hp : IsPeriodicN L Φ)
    (x : Conf N) (n : Fin N → Idx) : fderiv ℝ Φ (x + Loc_latN L n) = fderiv ℝ Φ x := by
  have h : (fun y => Φ (y + Loc_latN L n)) = Φ := funext fun y => hp y n
  rw [← fderiv_comp_add_right, h]

/-- One direction `(i, a)` of the kinetic identity. -/
private lemma Loc_kin_term {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (u : R3) {N : ℕ}
    {Φ : Conf N → ℂ} (hd : ContDiff ℝ 1 Φ) (hp : IsPeriodicN L Φ) (i : Fin N) (a : Fin 3) :
    Integrable (fun x =>
      ‖fderiv ℝ (localize ℓ L u Φ) x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2) ∧
    ∫ x, ‖fderiv ℝ (localize ℓ L u Φ) x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2 =
      (∫ x in cellN L N, ‖fderiv ℝ Φ x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2) +
        ∫ x in cellN L N, ‖Φ x‖ ^ 2 * profW ℓ L (x i a + u a) := by
  set v : Conf N := Pi.single i (EuclideanSpace.single a 1) with hv
  have hΦc : Continuous Φ := hd.continuous
  have hAc : Continuous fun x => fderiv ℝ Φ x v :=
    (hd.continuous_fderiv (by simp)).clm_apply continuous_const
  have hAp : ∀ x n, fderiv ℝ Φ (x + Loc_latN L n) v = fderiv ℝ Φ x v := fun x n => by
    rw [Loc_fderiv_periodic hp]
  have hΦp : ∀ x n, Φ (x + Loc_latN L n) = Φ x := fun x n => hp x n
  have s1c : Continuous fun y => prof ℓ L y ^ 2 := (Loc_prof_cont ℓ L).pow 2
  have s2c : Continuous fun y => deriv (prof ℓ L) y ^ 2 := (Loc_dprof_cont ℓ L).pow 2
  have s3c : Continuous (deriv fun y => prof ℓ L y ^ 2) := by
    rw [Loc_deriv_sq]
    exact (continuous_const.mul (Loc_prof_cont ℓ L)).mul (Loc_dprof_cont ℓ L)
  have s1z : ∀ y, y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) → prof ℓ L y ^ 2 = 0 := fun y hy => by
    rw [Loc_prof_zero hℓ hy]
    ring
  have s2z : ∀ y, y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) → deriv (prof ℓ L) y ^ 2 = 0 :=
    fun y hy => by
      rw [Loc_dprof_zero hℓ hy]
      ring
  have s3z : ∀ y, y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) →
      deriv (fun y => prof ℓ L y ^ 2) y = 0 := fun y hy => by
    rw [Loc_deriv_sq]
    beta_reduce
    rw [Loc_prof_zero hℓ hy]
    ring
  have u1 := Loc_unfold_prod hℓ hℓL u (K := fun x => ‖fderiv ℝ Φ x v‖ ^ 2) (hAc.norm.pow 2)
    (fun x n => by simp only [hAp]) (Loc_g_cont ℓ L i a s1c) (Loc_g_zero hℓ i a s1z)
  have u2 := Loc_unfold_prod hℓ hℓL u (K := fun x => ‖Φ x‖ ^ 2) (hΦc.norm.pow 2)
    (fun x n => by simp only [hΦp]) (Loc_g_cont ℓ L i a s2c) (Loc_g_zero hℓ i a s2z)
  have u3 := Loc_unfold_prod hℓ hℓL u
    (K := fun x => (Φ x).re * (fderiv ℝ Φ x v).re + (Φ x).im * (fderiv ℝ Φ x v).im)
    (by fun_prop) (fun x n => by simp only [hAp, hΦp]) (Loc_g_cont ℓ L i a s3c)
    (Loc_g_zero hℓ i a s3z)
  simp only [Loc_prod_tsum hℓ hℓL u] at u1 u2 u3
  have t1 : ∀ x : Conf N, ∑' k : ℤ, prof ℓ L (x i a + u a + k * L) ^ 2 = 1 := fun x =>
    (prof_sq_hasSum hℓ hℓL _).tsum_eq
  have t3 : ∀ x : Conf N, ∑' k : ℤ, deriv (fun y => prof ℓ L y ^ 2) (x i a + u a + k * L) = 0 :=
    fun x => (deriv_prof_sq_hasSum hℓ hℓL _).tsum_eq
  simp only [t1, t3, mul_one, mul_zero, integral_zero] at u1 u3
  have e : (fun x => ‖fderiv ℝ (localize ℓ L u Φ) x v‖ ^ 2) = fun x =>
      ‖fderiv ℝ Φ x v‖ ^ 2 *
          (∏ j, ∏ b, Loc_g ℓ L i a (fun y => prof ℓ L y ^ 2) j b (x j b + u b)) +
        ‖Φ x‖ ^ 2 *
          (∏ j, ∏ b, Loc_g ℓ L i a (fun y => deriv (prof ℓ L) y ^ 2) j b (x j b + u b)) +
        ((Φ x).re * (fderiv ℝ Φ x v).re + (Φ x).im * (fderiv ℝ Φ x v).im) *
          ∏ j, ∏ b, Loc_g ℓ L i a (deriv fun y => prof ℓ L y ^ 2) j b (x j b + u b) := by
    funext x
    rw [hv, Loc_fderiv_localize ℓ L u hd x i a, Loc_expand, ← hv, Loc_prod_C, Loc_prod_C,
      Loc_prod_C, Loc_deriv_sq]
  rw [e]
  refine ⟨(u1.1.add u2.1).add u3.1, ?_⟩
  rw [integral_add, integral_add, u1.2, u2.2, u3.2, add_zero]
  · rfl
  · exact u1.1
  · exact u2.1
  · exact u1.1.add u2.1
  · exact u3.1

/-! ### The three identities -/

/-- `𝓕^u` is an isometry from periodic functions on `[0, L]^{3N}` to functions on
`(ℝ³)^N`, (12.2) [proh1] and (12.4) [defFu]. -/
theorem localize_norm {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (u : R3) {N : ℕ}
    {Φ : Conf N → ℂ} (hc : Continuous Φ) (hp : IsPeriodicN L Φ) :
    ∫ x, ‖localize ℓ L u Φ x‖ ^ 2 = ∫ x in cellN L N, ‖Φ x‖ ^ 2 := by
  have hU := Loc_unfold_prod hℓ hℓL u (K := fun x => ‖Φ x‖ ^ 2) (hc.norm.pow 2)
    (fun x n => by simp only [show Φ (x + Loc_latN L n) = Φ x from hp x n])
    (g := fun _ _ y => prof ℓ L y ^ 2) (fun _ _ => (Loc_prof_cont ℓ L).pow 2)
    (fun _ _ y hy => by
      show prof ℓ L y ^ 2 = 0
      rw [Loc_prof_zero hℓ hy]
      ring)
  have h1 : ∀ x : Conf N, ∏ j, ∏ b, ∑' k : ℤ, prof ℓ L (x j b + u b + k * L) ^ 2 = 1 :=
    fun x => by simp [(prof_sq_hasSum hℓ hℓL _).tsum_eq]
  simp only [h1, mul_one] at hU
  simp_rw [Loc_norm_sq]
  exact hU.2

/-- The kinetic energy of `𝓕^u Φ`, (12.3) [3.51] as an identity:
`∫ |∇ 𝓕^u Φ|² = ∫_{[0, L]^{3N}} |∇Φ|² + Σ_{i,a} ∫_{[0, L]^{3N}} |Φ|² w(x_{i,a} + u_a)`. -/
theorem localize_kin {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (u : R3) {N : ℕ}
    {Φ : Conf N → ℂ} (hd : ContDiff ℝ 1 Φ) (hp : IsPeriodicN L Φ) :
    ∫ x, kinD (localize ℓ L u Φ) x =
      (∫ x in cellN L N, kinD Φ x) +
        ∑ i, ∑ a : Fin 3, ∫ x in cellN L N, ‖Φ x‖ ^ 2 * profW ℓ L (x i a + u a) := by
  have hT := fun i a => Loc_kin_term hℓ hℓL u hd hp i a
  have hAc : ∀ (i : Fin N) (a : Fin 3), IntegrableOn
      (fun x => ‖fderiv ℝ Φ x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2) (cellN L N) :=
    fun i a => ((((hd.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow
      2).continuousOn).integrableOn_compact (Loc_cellN_compact L N)
  unfold kinD
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun a _ => (hT i a).1,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun a _ => hAc i a,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun a _ => (hT i a).1, integral_finsetSum _ fun a _ => hAc i a,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => (hT i a).2

private lemma Loc_pairPot_continuous {W : R3 → ℝ} (hW : Continuous W) {N : ℕ} :
    Continuous (fun x : Conf N => pairPot W x) := by
  unfold pairPot
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact hW.comp ((continuous_apply i).sub (continuous_apply j))
  · exact continuous_const

/-- `Σ_{i≠j} V(x_i - x_j + L(n_i - n_j)) ≤ Σ_{i≠j} V^P(x_i - x_j)`. -/
private lemma Loc_pairPot_le {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L) {N : ℕ}
    (x : Conf N) (n : Fin N → Idx) :
    pairPot V (x + Loc_latN L n) ≤ pairPot (periodize L V) x := by
  unfold pairPot
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  split_ifs with h
  · have e : (x + Loc_latN L n) i - (x + Loc_latN L n) j = (x i - x j) + lat L (n i - n j) := by
      ext b
      simp only [Pi.add_apply, PiLp.add_apply, PiLp.sub_apply, Loc_latN, Loc_lat_apply,
        Pi.sub_apply, Int.cast_sub]
      ring
    rw [e]
    exact (periodize_summable hV hL _).le_tsum _ (fun k _ => hV.nonneg _)
  · exact le_rfl

/-- The potential energy of `𝓕^u Φ` is at most the periodic one (§12, after (12.4) [defFu]). -/
theorem localize_pot {V : R3 → ℝ} (hV : PotentialHyp V) {ℓ L : ℝ} (hℓ : 0 < ℓ)
    (hℓL : 2 * ℓ < L) (u : R3) {N : ℕ} {Φ : Conf N → ℂ} (hc : Continuous Φ)
    (hp : IsPeriodicN L Φ) :
    ∫ x, pairPot V x * ‖localize ℓ L u Φ x‖ ^ 2 ≤
      ∫ x in cellN L N, pairPot (periodize L V) x * ‖Φ x‖ ^ 2 := by
  have hL : 0 < L := by linarith
  obtain ⟨S, hS⟩ := hV.schwartz
  have hVc : Continuous V := hS ▸ S.continuous
  set G : Conf N → ℝ := fun x =>
    pairPot V x * (‖Φ x‖ ^ 2 * ∏ j, ∏ b, prof ℓ L (x j b + u b) ^ 2) with hGdef
  have hGc : Continuous G := by
    refine (Loc_pairPot_continuous hVc).mul ((hc.norm.pow 2).mul
      (continuous_finsetProd _ fun j _ => continuous_finsetProd _ fun b _ => ?_))
    exact ((Loc_prof_cont ℓ L).pow 2).comp (by fun_prop)
  have hGs : ∀ x : Conf N, (∃ j b, x j b + u b ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2)) → G x = 0 := by
    rintro x ⟨j, b, h⟩
    simp only [hGdef]
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero (Finset.mem_univ b)
      (by rw [Loc_prof_zero hℓ h]; ring)), mul_zero, mul_zero]
  have e1 : ∫ x, pairPot V x * ‖localize ℓ L u Φ x‖ ^ 2 = ∫ x, G x := by
    simp_rw [Loc_norm_sq, hGdef]
  rw [e1, Loc_unfold_supp hℓ hℓL u hGc hGs]
  have hcpt := Loc_cellN_compact L N
  refine setIntegral_mono_on ?_ ?_ (Loc_cellN_meas L N) ?_
  · exact (continuous_finsetSum _ fun n _ =>
      hGc.comp (continuous_id.add continuous_const)).continuousOn.integrableOn_compact hcpt
  · exact ((Loc_pairPot_continuous (periodize_continuous hV hL)).mul
      (hc.norm.pow 2)).continuousOn.integrableOn_compact hcpt
  · intro x hx
    have hsum := Loc_sum_prod hℓ hℓL u (g := fun _ _ y => prof ℓ L y ^ 2)
      (fun _ _ y hy => by
        show prof ℓ L y ^ 2 = 0
        rw [Loc_prof_zero hℓ hy]
        ring) hx
    simp only [(prof_sq_hasSum hℓ hℓL _).tsum_eq, Finset.prod_const_one] at hsum
    calc ∑ n ∈ Loc_F L u N, G (x + Loc_latN L n)
        ≤ ∑ n ∈ Loc_F L u N, pairPot (periodize L V) x * (‖Φ x‖ ^ 2 *
            ∏ j, ∏ b, prof ℓ L ((x + Loc_latN L n) j b + u b) ^ 2) := by
          refine Finset.sum_le_sum fun n _ => ?_
          simp only [hGdef, show Φ (x + Loc_latN L n) = Φ x from hp x n]
          exact mul_le_mul_of_nonneg_right (Loc_pairPot_le hV hL x n) (by positivity)
      _ = pairPot (periodize L V) x * ‖Φ x‖ ^ 2 := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, hsum, mul_one]

end LHYUpper
