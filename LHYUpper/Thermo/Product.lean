module

public import LHYUpper.Position.Basic
public import LHYUpper.Position.DirichletFacts

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Product trial states in disjoint cubes (§2)

The duplication step after Lemma 2.1 [thm1] places Dirichlet trial states of small cubes in
disjoint cubes of a large box and symmetrizes their product. This file states that the result is a
Dirichlet trial state of the large box, with energy at most the sum of the cube energies plus a
bound `B` on the interaction between different cubes. -/

/-- Dirichlet trial states on `[0,L]³` are Dirichlet trial states on every larger cube
`[0,L']³` (§2). -/
theorem isDirichletTrial_mono {L L' : ℝ} (h : L ≤ L') {N : ℕ} {Ψ : Conf N → ℂ}
    (hΨ : IsDirichletTrial L N Ψ) : IsDirichletTrial L' N Ψ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hΨ
  exact ⟨h1, h2, fun x hx i a => ⟨(h3 hx i a).1, (h3 hx i a).2.trans_le h⟩, h4, h5⟩

/-- Translating a Dirichlet trial state on `[0,ℓ]³` by `c` gives a smooth, compactly supported,
symmetric, normalized function supported in the open cube `c + (0,ℓ)³`. -/
theorem isDirichletTrial_translate {ℓ : ℝ} {n : ℕ} {ψ : Conf n → ℂ}
    (hψ : IsDirichletTrial ℓ n ψ) (c : R3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Conf n => ψ (fun j => x j - c)) ∧
      HasCompactSupport (fun x : Conf n => ψ (fun j => x j - c)) ∧
      tsupport (fun x : Conf n => ψ (fun j => x j - c)) ⊆
        {x : Conf n | ∀ j a, c a < x j a ∧ x j a < c a + ℓ} ∧
      (∀ σ : Equiv.Perm (Fin n), ∀ x : Conf n,
        ψ (fun j => (x ∘ σ) j - c) = ψ (fun j => x j - c)) ∧
      ∫ x : Conf n, ‖ψ (fun j => x j - c)‖ ^ 2 = 1 := by
  set cc : Conf n := fun _ => c with hcc
  have hfun : (fun x : Conf n => ψ (fun j => x j - c)) = ψ ∘ (Homeomorph.subRight cc) := by
    funext x; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hψ.1.comp
      (contDiff_pi.2 fun j => (contDiff_apply ℝ (fun _ : Fin n => R3) j).sub contDiff_const)
  · rw [hfun]; exact hψ.2.1.comp_homeomorph _
  · intro x hx j a
    rw [hfun] at hx
    have h1 := tsupport_comp_subset_preimage ψ (Homeomorph.subRight cc).continuous hx
    have h2 := hψ.2.2.1 h1 j a
    simp only [Homeomorph.subRight_apply, Pi.sub_apply, hcc, PiLp.sub_apply] at h2
    constructor <;> linarith [h2.1, h2.2]
  · intro σ x
    exact hψ.2.2.2.1 σ (fun j => x j - c)
  · exact (integral_sub_right_eq_self (μ := (volume : Measure (Conf n)))
      (fun y => ‖ψ y‖ ^ 2) cc).trans hψ.2.2.2.2

/-! ### Kinetic and pair terms of the Dirichlet energy -/

/-- The kinetic integrand `Σ_{i,a} |∂_{ia} f(x)|²` of `energyD`. -/
private def Product_kin {N : ℕ} (f : Conf N → ℂ) (x : Conf N) : ℝ :=
  ∑ i, ∑ a : Fin 3, ‖fderiv ℝ f x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2

/-- The pair potential `Σ_{i≠j} V(x_i - x_j)` of `energyD`. -/
private def Product_pair (V : R3 → ℝ) {N : ℕ} (x : Conf N) : ℝ :=
  ∑ i, ∑ j, if i ≠ j then V (x i - x j) else 0

private lemma Product_energyD_eq (V : R3 → ℝ) {N : ℕ} (f : Conf N → ℂ) :
    energyD V f = ∫ x, (Product_kin f x + Product_pair V x * ‖f x‖ ^ 2) := rfl

private lemma Product_kin_continuous {N : ℕ} {f : Conf N → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (Product_kin f) := by
  have hd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun a _ =>
    ((hd.clm_apply continuous_const).norm.pow 2)

private lemma Product_kin_eq_zero {N : ℕ} {f : Conf N → ℂ} {x : Conf N}
    (hx : x ∉ tsupport f) : Product_kin f x = 0 := by
  have h1 : fderiv ℝ f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))
  simp [Product_kin, h1]

private lemma Product_pair_continuous {V : R3 → ℝ} (hV : Continuous V) {N : ℕ} :
    Continuous (Product_pair V (N := N)) := by
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact hV.comp ((continuous_apply i).sub (continuous_apply j))
  · exact continuous_const

/-- The energy integrand with a continuous pair potential `P` of a smooth compactly supported
function is integrable. -/
private lemma Product_integrable {N : ℕ} {f : Conf N → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) {P : Conf N → ℝ} (hP : Continuous P) :
    Integrable (fun x => Product_kin f x + P x * ‖f x‖ ^ 2) := by
  refine Continuous.integrable_of_hasCompactSupport
    ((Product_kin_continuous hf).add (hP.mul (hf.continuous.norm.pow 2))) ?_
  refine HasCompactSupport.intro hfc (fun x hx => ?_)
  have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
  simp [Product_kin_eq_zero hx, h0]

/-! ### Permutations of the particles -/

/-- The relabelling `x ↦ x ∘ σ` as a measurable equivalence. -/
private def Product_permEquiv {N : ℕ} (σ : Equiv.Perm (Fin N)) : Conf N ≃ᵐ Conf N :=
  MeasurableEquiv.piCongrLeft (fun _ => R3) σ.symm

private lemma Product_permEquiv_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Conf N) :
    Product_permEquiv σ x = x ∘ σ := by
  ext i : 1
  simp [Product_permEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

private lemma Product_integral_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) (F : Conf N → ℝ) :
    ∫ x, F (x ∘ σ) = ∫ x, F x := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : Fin N => R3) σ.symm).integral_comp'
    (f := Product_permEquiv σ) F
  simpa [Product_permEquiv_apply] using h

private lemma Product_integrable_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) {F : Conf N → ℝ}
    (hF : Integrable F) : Integrable (fun x => F (x ∘ σ)) := by
  have h := ((volume_measurePreserving_piCongrLeft (fun _ : Fin N => R3) σ.symm).integrable_comp_emb
    (f := Product_permEquiv σ) (Product_permEquiv σ).measurableEmbedding).2 hF
  have he : (F ∘ ⇑(Product_permEquiv σ)) = fun x => F (x ∘ σ) := by
    funext x; simp [Product_permEquiv_apply]
  rwa [he] at h

private lemma Product_continuous_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Continuous (fun x : Conf N => x ∘ σ) :=
  continuous_pi fun i => continuous_apply (σ i)

private lemma Product_contDiff_perm {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Conf N => x ∘ σ) :=
  contDiff_pi.2 fun i => contDiff_apply ℝ (fun _ : Fin N => R3) (σ i)

private lemma Product_single_comp {N : ℕ} (σ : Equiv.Perm (Fin N)) (i : Fin N) (u : R3) :
    (Pi.single i u : Conf N) ∘ σ = Pi.single (σ.symm i) u := by
  funext j
  simp only [Function.comp_apply, Pi.single_apply, Equiv.eq_symm_apply]

private lemma Product_kin_perm {N : ℕ} (f : Conf N → ℂ) (σ : Equiv.Perm (Fin N)) (x : Conf N) :
    Product_kin (fun y => f (y ∘ σ)) x = Product_kin f (x ∘ σ) := by
  set iso := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin N => R3) σ.symm with hiso
  have hiso_apply : ∀ y : Conf N, iso y = y ∘ σ := by
    intro y; ext i : 1
    simp [hiso, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
  have hfun : (fun y => f (y ∘ σ)) = f ∘ iso := by
    funext y; simp [hiso_apply]
  have hd : fderiv ℝ (fun y => f (y ∘ σ)) x = (fderiv ℝ f (x ∘ σ)).comp (iso : Conf N →L[ℝ] Conf N) := by
    rw [hfun, ContinuousLinearEquiv.comp_right_fderiv, hiso_apply]
  unfold Product_kin
  rw [hd]
  simp only [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    hiso_apply, Product_single_comp]
  exact Equiv.sum_comp σ.symm
    (fun i => ∑ a : Fin 3, ‖fderiv ℝ f (x ∘ σ) (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2)

private lemma Product_pair_perm (V : R3 → ℝ) {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Conf N) :
    Product_pair V (x ∘ σ) = Product_pair V x := by
  unfold Product_pair
  simp only [Function.comp_apply]
  have h : ∀ i j : Fin N, (if i ≠ j then V (x (σ i) - x (σ j)) else 0) =
      (if σ i ≠ σ j then V (x (σ i) - x (σ j)) else 0) := by
    intro i j; simp [σ.injective.ne_iff]
  simp_rw [h]
  symm
  rw [← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp σ]

/-- A symmetric function evaluated at two labellings of the same set of particles takes the
same value. -/
private lemma Product_sym_range {k N : ℕ} {φ : Conf k → ℂ}
    (hφ : ∀ (ρ : Equiv.Perm (Fin k)) (y : Conf k), φ (y ∘ ρ) = φ y)
    {f g : Fin k → Fin N} (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : Set.range f = Set.range g) (x : Conf N) :
    φ (fun j => x (f j)) = φ (fun j => x (g j)) := by
  let ρ : Equiv.Perm (Fin k) :=
    ((Equiv.ofInjective f hf).trans (Set.equivOfEq hr)).trans (Equiv.ofInjective g hg).symm
  have hρ : ∀ j, g (ρ j) = f j := by
    intro j
    simp only [ρ, Equiv.trans_apply]
    rw [Equiv.apply_ofInjective_symm hg]
    simp
  have h : (fun j => x (f j)) = (fun j => x (g j)) ∘ ρ := by
    funext j; simp [hρ]
  rw [h, hφ]

/-! ### Blocks of particles -/

section Blocks

variable {ι : Type*} [Fintype ι] {n : ι → ℕ} {N : ℕ}

/-- The block `(x_{e(m,k)})_k` of the particles assigned to cube `m`. -/
private def Product_blk (e : (Σ m, Fin (n m)) ≃ Fin N) (m : ι) (x : Conf N) : Conf (n m) :=
  fun k => x (e ⟨m, k⟩)

omit [Fintype ι] in
private lemma Product_blk_continuous (e : (Σ m, Fin (n m)) ≃ Fin N) (m : ι) :
    Continuous (Product_blk e m) :=
  continuous_pi fun k => continuous_apply (e ⟨m, k⟩)

omit [Fintype ι] in
private lemma Product_blk_contDiff (e : (Σ m, Fin (n m)) ≃ Fin N) (m : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (Product_blk e m) :=
  contDiff_pi.2 fun k => contDiff_apply ℝ (fun _ : Fin N => R3) (e ⟨m, k⟩)

/-- The block map as a continuous linear map. -/
private def Product_blkCLM (e : (Σ m, Fin (n m)) ≃ Fin N) (m : ι) :
    Conf N →L[ℝ] Conf (n m) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e ⟨m, k⟩)

omit [Fintype ι] in
private lemma Product_blkCLM_apply (e : (Σ m, Fin (n m)) ≃ Fin N) (m : ι) (x : Conf N) :
    Product_blkCLM e m x = Product_blk e m x := rfl

omit [Fintype ι] in
private lemma Product_range0 (e : (Σ m, Fin (n m)) ≃ Fin N) (m : ι) :
    Set.range (fun k : Fin (n m) => e ⟨m, k⟩) = {j | (e.symm j).1 = m} := by
  ext j
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨k, rfl⟩
    simp
  · intro h
    rcases hq : e.symm j with ⟨m', k⟩
    rw [hq] at h
    subst h
    exact ⟨k, by rw [← hq]; simp⟩

omit [Fintype ι] in
private lemma Product_card_fiber (e : (Σ m, Fin (n m)) ≃ Fin N) (m : ι) :
    (Finset.univ.filter (fun j => (e.symm j).1 = m)).card = n m := by
  have h : Finset.univ.filter (fun j => (e.symm j).1 = m) =
      Finset.univ.image (fun k : Fin (n m) => e ⟨m, k⟩) := by
    ext j
    have := Set.ext_iff.1 (Product_range0 e m) j
    simp only [Set.mem_range, Set.mem_ofPred_eq] at this
    simp [this]
  rw [h, Finset.card_image_of_injective _ (fun k k' hk => by simpa using e.injective hk)]
  simp

/-- The gluing `(y_m)_m ↦ x` with `x_{e(m,k)} = y_m(k)`, inverse to the blocks. -/
private def Product_glue (e : (Σ m, Fin (n m)) ≃ Fin N) : ((m : ι) → Conf (n m)) ≃ᵐ Conf N :=
  (MeasurableEquiv.piCurry (fun (m : ι) (_ : Fin (n m)) => R3)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => R3) e)

omit [Fintype ι] in
private lemma Product_glue_apply (e : (Σ m, Fin (n m)) ≃ Fin N) (y : (m : ι) → Conf (n m))
    (j : Fin N) : Product_glue e y j = y (e.symm j).1 (e.symm j).2 := by
  simp [Product_glue, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply,
    MeasurableEquiv.coe_piCurry_symm, Sigma.uncurry]

omit [Fintype ι] in
private lemma Product_blk_glue (e : (Σ m, Fin (n m)) ≃ Fin N) (y : (m : ι) → Conf (n m))
    (m : ι) : Product_blk e m (Product_glue e y) = y m := by
  funext k
  simp only [Product_blk, Product_glue_apply]
  rw [Equiv.symm_apply_apply]

omit [Fintype ι] in
private lemma Product_glue_blk (e : (Σ m, Fin (n m)) ≃ Fin N) (x : Conf N) :
    Product_glue e (fun m => Product_blk e m x) = x := by
  funext j
  simp [Product_blk, Product_glue_apply]

omit [Fintype ι] in
private lemma Product_glue_continuous (e : (Σ m, Fin (n m)) ≃ Fin N) :
    Continuous (Product_glue e) := by
  have h : ⇑(Product_glue e) = fun y j => y (e.symm j).1 (e.symm j).2 :=
    funext fun y => funext fun j => Product_glue_apply e y j
  rw [h]
  exact continuous_pi fun j => (continuous_apply _).comp (continuous_apply _)

private lemma Product_mp_uncurry :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (m : ι) (_ : Fin (n m)) => R3)).symm
      (volume : Measure ((m : ι) → Conf (n m))) (volume : Measure ((Σ m, Fin (n m)) → R3)) where
  measurable := (MeasurableEquiv.piCurry _).symm.measurable
  map_eq := by
    refine (Measure.pi_eq fun s _ => ?_).symm
    rw [MeasurableEquiv.map_apply]
    have h : (MeasurableEquiv.piCurry (fun (m : ι) (_ : Fin (n m)) => R3)).symm ⁻¹'
        Set.univ.pi s = Set.univ.pi (fun m => Set.univ.pi (fun k => s ⟨m, k⟩)) := by
      ext y
      simp [MeasurableEquiv.coe_piCurry_symm, Sigma.uncurry, Sigma.forall]
    rw [h]
    simp only [volume_pi, Measure.pi_pi]
    exact (Fintype.prod_sigma (fun q => volume (s q))).symm

/-- Block Fubini: `∫ Π_m h_m(x_{J_m}) dx = Π_m ∫ h_m`. -/
private lemma Product_integral_prod (e : (Σ m, Fin (n m)) ≃ Fin N)
    (h : (m : ι) → Conf (n m) → ℝ) :
    ∫ x : Conf N, ∏ m, h m (Product_blk e m x) = ∏ m, ∫ y, h m y := by
  have hmp : MeasurePreserving (Product_glue e) :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin N => R3) e).comp Product_mp_uncurry
  rw [← hmp.integral_comp' (fun x => ∏ m, h m (Product_blk e m x))]
  simp_rw [Product_blk_glue]
  exact integral_fintype_prod_volume_eq_prod _

/-- A product of block functions that vanish off compact sets has compact support. -/
private lemma Product_hasCompactSupport_prod {β : Type*} [CommMonoidWithZero β]
    (e : (Σ m, Fin (n m)) ≃ Fin N) {H : (m : ι) → Conf (n m) → β}
    {K : (m : ι) → Set (Conf (n m))} (hK : ∀ m, IsCompact (K m))
    (hH : ∀ m y, y ∉ K m → H m y = 0) :
    HasCompactSupport (fun x : Conf N => ∏ m, H m (Product_blk e m x)) := by
  refine HasCompactSupport.intro ((isCompact_univ_pi hK).image (Product_glue_continuous e))
    (fun x hx => ?_)
  have : ∃ m, Product_blk e m x ∉ K m := by
    by_contra h
    push Not at h
    exact hx ⟨fun m => Product_blk e m x, fun m _ => h m, Product_glue_blk e x⟩
  obtain ⟨m, hm⟩ := this
  exact Finset.prod_eq_zero (Finset.mem_univ m) (hH m _ hm)

/-- The block product `T(x) = Π_m φ_m(x_{J_m})`. -/
private def Product_T (e : (Σ m, Fin (n m)) ≃ Fin N) (φ : (m : ι) → Conf (n m) → ℂ)
    (x : Conf N) : ℂ :=
  ∏ m, φ m (Product_blk e m x)

private lemma Product_T_contDiff (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ} (hφ : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m)) :
    ContDiff ℝ (⊤ : ℕ∞) (Product_T e φ) :=
  contDiff_prod fun m _ => (hφ m).comp (Product_blk_contDiff e m)

private lemma Product_T_hasCompactSupport (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ} (hφ : ∀ m, HasCompactSupport (φ m)) :
    HasCompactSupport (Product_T e φ) :=
  Product_hasCompactSupport_prod e hφ (fun _ _ hy => image_eq_zero_of_notMem_tsupport hy)

private lemma Product_T_tsupport (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ} {ℓ : ℝ} {c : ι → R3}
    (hφ : ∀ m, tsupport (φ m) ⊆ {y | ∀ j a, c m a < y j a ∧ y j a < c m a + ℓ}) :
    tsupport (Product_T e φ) ⊆
      {x | ∀ j a, c (e.symm j).1 a < x j a ∧ x j a < c (e.symm j).1 a + ℓ} := by
  have hS : tsupport (Product_T e φ) ⊆ {x | ∀ m, Product_blk e m x ∈ tsupport (φ m)} := by
    refine closure_minimal (fun x hx => ?_) ?_
    · intro m
      have hx' : ∏ m, φ m (Product_blk e m x) ≠ 0 := hx
      exact subset_closure ((Finset.prod_ne_zero_iff.mp hx') m (Finset.mem_univ m))
    · rw [Set.ofPred_forall]
      exact isClosed_iInter fun m => (isClosed_tsupport _).preimage (Product_blk_continuous e m)
  intro x hx j a
  have h := hφ _ (hS hx (e.symm j).1) (e.symm j).2 a
  simpa [Product_blk] using h

private lemma Product_T_normSq (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ} (hφ : ∀ m, ∫ y, ‖φ m y‖ ^ 2 = 1) :
    ∫ x, ‖Product_T e φ x‖ ^ 2 = 1 := by
  simp only [Product_T, norm_prod, ← Finset.prod_pow]
  rw [Product_integral_prod e (fun m y => ‖φ m y‖ ^ 2)]
  simp [hφ]

/-- Permutations in the same class give the same permuted block product. -/
private lemma Product_T_perm (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ}
    (hφ : ∀ m (ρ : Equiv.Perm (Fin (n m))) (y : Conf (n m)), φ m (y ∘ ρ) = φ m y)
    {σ τ : Equiv.Perm (Fin N)}
    (h : (fun j => (e.symm j).1) ∘ σ.symm = (fun j => (e.symm j).1) ∘ τ.symm) (x : Conf N) :
    Product_T e φ (x ∘ σ) = Product_T e φ (x ∘ τ) := by
  unfold Product_T
  refine Finset.prod_congr rfl fun m _ => ?_
  have hr : ∀ ρ : Equiv.Perm (Fin N), Set.range (fun k : Fin (n m) => ρ (e ⟨m, k⟩)) =
      {i | (e.symm (ρ.symm i)).1 = m} := by
    intro ρ
    ext i
    have := Set.ext_iff.1 (Product_range0 e m) (ρ.symm i)
    simp only [Set.mem_range, Set.mem_ofPred_eq] at this ⊢
    rw [← this]
    constructor
    · rintro ⟨k, rfl⟩; exact ⟨k, by simp⟩
    · rintro ⟨k, hk⟩; exact ⟨k, by rw [hk]; simp⟩
  have hinj : ∀ ρ : Equiv.Perm (Fin N), Function.Injective (fun k : Fin (n m) => ρ (e ⟨m, k⟩)) :=
    fun ρ k k' hk => by simpa using e.injective (ρ.injective hk)
  have hrange : Set.range (fun k : Fin (n m) => σ (e ⟨m, k⟩)) =
      Set.range (fun k : Fin (n m) => τ (e ⟨m, k⟩)) := by
    rw [hr σ, hr τ]
    ext i
    have := congrFun h i
    simp only [Function.comp_apply] at this
    simp [this]
  exact Product_sym_range (hφ m) (hinj σ) (hinj τ) hrange x

end Blocks

/-! ### Symmetrization over disjoint supports -/

/-- `|Σ_s w_s|² = #{s : p s} · Σ_s |w_s|²` when `w_s` equals a common value on `{p}` and `0`
off it. -/
private lemma Product_sum_sq {S : Type*} [Fintype S] (w : S → ℂ) (p : S → Prop) (a : ℂ)
    (hw : ∀ s, w s = if p s then a else 0) :
    ‖∑ s, w s‖ ^ 2 = ((Finset.univ.filter p).card : ℝ) * ∑ s, ‖w s‖ ^ 2 := by
  have h1 : ∑ s, w s = ((Finset.univ.filter p).card : ℂ) * a := by
    simp_rw [hw]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ s, ‖w s‖ ^ 2 = ((Finset.univ.filter p).card : ℝ) * ‖a‖ ^ 2 := by
    have : ∀ s, ‖w s‖ ^ 2 = if p s then ‖a‖ ^ 2 else 0 := by
      intro s; rw [hw s]; split_ifs <;> simp
    simp_rw [this]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2, norm_mul, Complex.norm_natCast]
  ring

/-- Pointwise form of the orthogonality of permuted copies with disjoint supports: if copies in
one class coincide, copies in different classes have disjoint supports, and every class has `h`
elements, then `|Σ_σ f_σ|² = h Σ_σ |f_σ|²` and likewise for every directional derivative. -/
private lemma Product_pointwise {N : ℕ} {α : Type*} (f : Equiv.Perm (Fin N) → Conf N → ℂ)
    (cls : Equiv.Perm (Fin N) → α) (h : ℕ)
    (hd : ∀ σ, Differentiable ℝ (f σ))
    (hcls : ∀ σ τ, cls σ = cls τ → f σ = f τ)
    (hsup : ∀ x σ τ, x ∈ tsupport (f σ) → x ∈ tsupport (f τ) → cls σ = cls τ)
    (hcard : ∀ σ₀, (Finset.univ.filter (fun σ => cls σ = cls σ₀)).card = h) (x : Conf N) :
    ‖∑ σ, f σ x‖ ^ 2 = h * ∑ σ, ‖f σ x‖ ^ 2 ∧
      ∀ v, ‖fderiv ℝ (fun y => ∑ σ, f σ y) x v‖ ^ 2 = h * ∑ σ, ‖fderiv ℝ (f σ) x v‖ ^ 2 := by
  have hfd : fderiv ℝ (fun y => ∑ σ, f σ y) x = ∑ σ, fderiv ℝ (f σ) x := by
    have he : (fun y => ∑ σ, f σ y) = ∑ σ, f σ := by
      funext y; simp [Finset.sum_apply]
    rw [he]
    exact fderiv_sum (fun σ _ => (hd σ).differentiableAt)
  have hz : ∀ σ, x ∉ tsupport (f σ) → f σ x = 0 ∧ fderiv ℝ (f σ) x = 0 := fun σ hn =>
    ⟨image_eq_zero_of_notMem_tsupport hn,
      image_eq_zero_of_notMem_tsupport (fun h1 => hn (tsupport_fderiv_subset ℝ h1))⟩
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, ∀ σ, (f σ x = if cls σ = cls σ₀ then f σ₀ x else 0) ∧
      (fderiv ℝ (f σ) x = if cls σ = cls σ₀ then fderiv ℝ (f σ₀) x else 0) := by
    by_cases hx : ∃ σ₀, x ∈ tsupport (f σ₀)
    · obtain ⟨σ₀, h0⟩ := hx
      refine ⟨σ₀, fun σ => ?_⟩
      by_cases hc : cls σ = cls σ₀
      · rw [ite_eq_left hc, ite_eq_left hc, hcls σ σ₀ hc]
        exact ⟨rfl, rfl⟩
      · rw [ite_eq_right hc, ite_eq_right hc]
        exact hz σ (fun h1 => hc (hsup x σ σ₀ h1 h0))
    · push Not at hx
      refine ⟨1, fun σ => ?_⟩
      rw [(hz σ (hx σ)).1, (hz σ (hx σ)).2, (hz 1 (hx 1)).1, (hz 1 (hx 1)).2]
      simp
  constructor
  · rw [Product_sum_sq _ _ _ (fun σ => (hσ₀ σ).1), hcard]
  · intro v
    rw [hfd, sum_apply]
    rw [Product_sum_sq (fun σ => fderiv ℝ (f σ) x v) (fun σ => cls σ = cls σ₀)
      (fderiv ℝ (f σ₀) x v) (fun σ => by rw [(hσ₀ σ).2]; split_ifs <;> simp), hcard]

/-- All classes `{σ : κ ∘ σ⁻¹ = κ ∘ σ₀⁻¹}` have the same number of elements. -/
private lemma Product_card_class {N : ℕ} {α : Type*} (κ : Fin N → α) (σ₀ : Equiv.Perm (Fin N)) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => κ ∘ σ.symm = κ ∘ σ₀.symm)).card =
      (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) => κ ∘ σ.symm = κ)).card := by
  refine Finset.card_nbij' (fun σ => σ₀⁻¹ * σ) (fun σ => σ₀ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    funext i
    have := congrFun hσ (σ₀ i)
    simpa [Equiv.Perm.mul_def, Equiv.Perm.inv_def] using this
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    funext i
    have := congrFun hσ (σ₀.symm i)
    simpa [Equiv.Perm.mul_def, Equiv.Perm.inv_def] using this
  · intro σ _
    simp
  · intro σ _
    simp

/-- Open cubes `c_m + (0,ℓ)³` separated in some coordinate by at least `ℓ` are disjoint. -/
private lemma Product_cube_unique {ι : Type*} {ℓ : ℝ} {c : ι → R3}
    (hsep : ∀ m m', m ≠ m' → ∃ a, ℓ ≤ |c m a - c m' a|) {y : R3} {m m' : ι}
    (h : ∀ a, c m a < y a ∧ y a < c m a + ℓ) (h' : ∀ a, c m' a < y a ∧ y a < c m' a + ℓ) :
    m = m' := by
  by_contra hne
  obtain ⟨a, ha⟩ := hsep m m' hne
  have h1 := h a
  have h2 := h' a
  rcases le_abs.mp ha with h3 | h3 <;> linarith [h1.1, h1.2, h2.1, h2.2]

section BlockEnergy

variable {ι : Type*} [Fintype ι] {n : ι → ℕ} {N : ℕ}

omit [Fintype ι] in
private lemma Product_blk_single_self (e : (Σ m, Fin (n m)) ≃ Fin N) (m : ι) (k : Fin (n m))
    (u : R3) : Product_blk e m (Pi.single (e ⟨m, k⟩) u) = Pi.single k u := by
  funext k'
  simp only [Product_blk, Pi.single_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq,
    true_and]

omit [Fintype ι] in
private lemma Product_blk_single_ne (e : (Σ m, Fin (n m)) ≃ Fin N) {m m₀ : ι} (hm : m ≠ m₀)
    (k : Fin (n m₀)) (u : R3) : Product_blk e m (Pi.single (e ⟨m₀, k⟩) u) = 0 := by
  funext k'
  simp only [Product_blk, Pi.single_apply, e.injective.eq_iff, Sigma.mk.inj_iff, hm, false_and,
    ite_false, Pi.zero_apply]

/-- Directional derivative of the block product along the particle `e(m₀,k)`. -/
private lemma Product_fderiv_T (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ} (hφ : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m)) (x : Conf N)
    (m₀ : ι) (k : Fin (n m₀)) (u : R3) :
    fderiv ℝ (Product_T e φ) x (Pi.single (e ⟨m₀, k⟩) u) =
      (∏ m ∈ Finset.univ.erase m₀, φ m (Product_blk e m x)) *
        fderiv ℝ (φ m₀) (Product_blk e m₀ x) (Pi.single k u) := by
  have hD : ∀ m ∈ (Finset.univ : Finset ι), HasFDerivAt (fun y => φ m (Product_blk e m y))
      ((fderiv ℝ (φ m) (Product_blk e m x)).comp (Product_blkCLM e m)) x := by
    intro m _
    have h1 : HasFDerivAt (φ m) (fderiv ℝ (φ m) (Product_blk e m x)) (Product_blkCLM e m x) :=
      ((hφ m).differentiable (by simp) _).hasFDerivAt
    exact h1.comp x (Product_blkCLM e m).hasFDerivAt
  have hT := HasFDerivAt.finsetProd hD
  have hTe : (fun y => ∏ m ∈ (Finset.univ : Finset ι), φ m (Product_blk e m y)) =
      Product_T e φ := rfl
  rw [hTe] at hT
  rw [hT.fderiv, sum_apply]
  rw [Finset.sum_eq_single m₀]
  · simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Product_blkCLM_apply, Product_blk_single_self, smul_eq_mul]
  · intro m _ hm
    simp only [smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Product_blkCLM_apply, Product_blk_single_ne e hm, map_zero, smul_zero]
  · intro h; exact absurd (Finset.mem_univ m₀) h

/-- The kinetic integrand of the block product:
`Σ_{i,a} |∂_{ia} T|² = Σ_m (Σ_{k,a} |∂_{ka} φ_m|²)(x_{J_m}) · Π_{m'≠m} |φ_{m'}(x_{J_{m'}})|²`. -/
private lemma Product_kin_T (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ} (hφ : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m)) (x : Conf N) :
    Product_kin (Product_T e φ) x = ∑ m, Product_kin (φ m) (Product_blk e m x) *
      ∏ m' ∈ Finset.univ.erase m, ‖φ m' (Product_blk e m' x)‖ ^ 2 := by
  unfold Product_kin
  rw [← Equiv.sum_comp e, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Product_fderiv_T e hφ, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow, mul_comm]

/-- The intra-block pair sum is the sum of the pair potentials of the blocks. -/
private lemma Product_pair_T (e : (Σ m, Fin (n m)) ≃ Fin N) (V : R3 → ℝ) (x : Conf N) :
    (∑ i, ∑ j, if i ≠ j ∧ (e.symm i).1 = (e.symm j).1 then V (x i - x j) else 0) =
      ∑ m, Product_pair V (Product_blk e m x) := by
  rw [← Equiv.sum_comp e, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun m _ => ?_
  unfold Product_pair
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Equiv.sum_comp e, Fintype.sum_sigma, Finset.sum_eq_single m]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    simp only [Equiv.symm_apply_apply, Product_blk, ne_eq, e.injective.eq_iff, Sigma.mk.inj_iff,
      heq_eq_eq, true_and, and_true]
  · intro m' _ hm'
    refine Finset.sum_eq_zero fun k' _ => ?_
    simp only [Equiv.symm_apply_apply]
    rw [ite_eq_right]
    rintro ⟨_, h⟩
    exact hm' h.symm
  · intro h; exact absurd (Finset.mem_univ m) h

/-- The energy integrand of the block product, with the intra-block pair sum, is a sum over the
blocks of products of block functions. -/
private lemma Product_energy_T (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ} (hφ : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m)) (V : R3 → ℝ)
    (x : Conf N) :
    Product_kin (Product_T e φ) x +
        (∑ i, ∑ j, if i ≠ j ∧ (e.symm i).1 = (e.symm j).1 then V (x i - x j) else 0) *
          ‖Product_T e φ x‖ ^ 2 =
      ∑ m, ∏ m', (if m' = m then
        (fun y => Product_kin (φ m') y + Product_pair V y * ‖φ m' y‖ ^ 2)
        else fun y => ‖φ m' y‖ ^ 2) (Product_blk e m' x) := by
  rw [Product_kin_T e hφ, Product_pair_T, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hN : ‖Product_T e φ x‖ ^ 2 = ‖φ m (Product_blk e m x)‖ ^ 2 *
      ∏ m' ∈ Finset.univ.erase m, ‖φ m' (Product_blk e m' x)‖ ^ 2 := by
    rw [Finset.mul_prod_erase _ (fun m' => ‖φ m' (Product_blk e m' x)‖ ^ 2) (Finset.mem_univ m)]
    simp only [Product_T, norm_prod, Finset.prod_pow]
  rw [hN, ← Finset.mul_prod_erase _ _ (Finset.mem_univ m), ite_eq_left rfl]
  have hrest : ∏ m' ∈ Finset.univ.erase m, (if m' = m then
        (fun y => Product_kin (φ m') y + Product_pair V y * ‖φ m' y‖ ^ 2)
        else fun y => ‖φ m' y‖ ^ 2) (Product_blk e m' x) =
      ∏ m' ∈ Finset.univ.erase m, ‖φ m' (Product_blk e m' x)‖ ^ 2 :=
    Finset.prod_congr rfl fun m' hm' => by rw [ite_eq_right (Finset.ne_of_mem_erase hm')]
  rw [hrest]
  ring

/-- Block Fubini for the energy: `∫ (|∇T|² + Σ_{i≠j, same block} V |T|²) = Σ_m E_V(φ_m)`. -/
private lemma Product_integral_energy_T (e : (Σ m, Fin (n m)) ≃ Fin N)
    {φ : (m : ι) → Conf (n m) → ℂ} (hφ : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m))
    (hφc : ∀ m, HasCompactSupport (φ m)) (hφn : ∀ m, ∫ y, ‖φ m y‖ ^ 2 = 1)
    {V : R3 → ℝ} (hV : Continuous V) :
    ∫ x, (Product_kin (Product_T e φ) x +
        (∑ i, ∑ j, if i ≠ j ∧ (e.symm i).1 = (e.symm j).1 then V (x i - x j) else 0) *
          ‖Product_T e φ x‖ ^ 2) = ∑ m, energyD V (φ m) := by
  simp_rw [Product_energy_T e hφ V]
  set H : ι → (m' : ι) → Conf (n m') → ℝ := fun m m' => if m' = m then
        (fun y => Product_kin (φ m') y + Product_pair V y * ‖φ m' y‖ ^ 2)
        else fun y => ‖φ m' y‖ ^ 2 with hH
  have hHc : ∀ m m', Continuous (H m m') := by
    intro m m'
    simp only [hH]
    split_ifs
    · exact (Product_kin_continuous (hφ m')).add
        ((Product_pair_continuous hV).mul ((hφ m').continuous.norm.pow 2))
    · exact (hφ m').continuous.norm.pow 2
  have hH0 : ∀ m m' y, y ∉ tsupport (φ m') → H m m' y = 0 := by
    intro m m' y hy
    have h0 : φ m' y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp only [hH]
    split_ifs <;> simp [Product_kin_eq_zero hy, h0]
  have hint : ∀ m, Integrable (fun x : Conf N => ∏ m', H m m' (Product_blk e m' x)) := by
    intro m
    refine Continuous.integrable_of_hasCompactSupport ?_
      (Product_hasCompactSupport_prod e hφc (hH0 m))
    exact continuous_finsetProd _ fun m' _ => (hHc m m').comp (Product_blk_continuous e m')
  rw [integral_finsetSum _ (fun m _ => hint m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Product_integral_prod e (H m)]
  have hI : ∀ m', ∫ y, H m m' y = if m' = m then energyD V (φ m') else 1 := by
    intro m'
    simp only [hH]
    split_ifs
    · rfl
    · exact hφn m'
  simp_rw [hI]
  rw [Finset.prod_ite_eq']
  simp

end BlockEnergy

/-- Symmetrized product of Dirichlet trial states placed in disjoint cubes `c m + (0,ℓ)³` of
`(0,L)³`: it is a Dirichlet trial state of `N = Σ_m n_m` particles on `[0,L]³`, and its energy
with an interaction `W` is at most the sum of the cube energies with `V` plus `B`, whenever `W`
is bounded by the intra-cube `V` plus `B` on every configuration with `n_m` particles in cube
`m`. -/
theorem thermo_product {ι : Type*} [Fintype ι] {n : ι → ℕ} {N : ℕ} (hN : ∑ m, n m = N)
    {ℓ L : ℝ} {c : ι → R3} (hbox : ∀ m a, 0 ≤ c m a ∧ c m a + ℓ ≤ L)
    (hsep : ∀ m m', m ≠ m' → ∃ a, ℓ ≤ |c m a - c m' a|)
    {ψ : (m : ι) → Conf (n m) → ℂ} (hψ : ∀ m, IsDirichletTrial ℓ (n m) (ψ m))
    {V W : R3 → ℝ} (hV : Continuous V) (hW : Continuous W) {B : ℝ}
    (hWB : ∀ cell : Fin N → ι, (∀ m, (Finset.univ.filter (fun j => cell j = m)).card = n m) →
      ∀ x : Conf N, (∀ j a, c (cell j) a < x j a ∧ x j a < c (cell j) a + ℓ) →
        (∑ i, ∑ j, if i ≠ j then W (x i - x j) else 0) ≤
          (∑ i, ∑ j, if i ≠ j ∧ cell i = cell j then V (x i - x j) else 0) + B) :
    ∃ Φ : Conf N → ℂ, IsDirichletTrial L N Φ ∧ energyD W Φ ≤ (∑ m, energyD V (ψ m)) + B := by
  -- the blocks `J_m = e({m} × Fin n_m)` of particles
  have hcardS : Fintype.card (Σ m, Fin (n m)) = N := by
    rw [Fintype.card_sigma]; simpa using hN
  obtain ⟨e⟩ : Nonempty ((Σ m, Fin (n m)) ≃ Fin N) := ⟨Fintype.equivFinOfCardEq hcardS⟩
  -- the translated states `φ_m = ψ_m(· - c_m)`
  obtain ⟨φ, hφ⟩ : ∃ φ : (m : ι) → Conf (n m) → ℂ, φ = fun m y => ψ m (fun j => y j - c m) :=
    ⟨_, rfl⟩
  have hφd : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m) := fun m => by
    rw [hφ]; exact (isDirichletTrial_translate (hψ m) (c m)).1
  have hφc : ∀ m, HasCompactSupport (φ m) := fun m => by
    rw [hφ]; exact (isDirichletTrial_translate (hψ m) (c m)).2.1
  have hφs : ∀ m, tsupport (φ m) ⊆ {y | ∀ j a, c m a < y j a ∧ y j a < c m a + ℓ} := fun m => by
    rw [hφ]; exact (isDirichletTrial_translate (hψ m) (c m)).2.2.1
  have hφp : ∀ m (ρ : Equiv.Perm (Fin (n m))) (y : Conf (n m)), φ m (y ∘ ρ) = φ m y :=
    fun m ρ y => by rw [hφ]; exact (isDirichletTrial_translate (hψ m) (c m)).2.2.2.1 ρ y
  have hφn : ∀ m, ∫ y, ‖φ m y‖ ^ 2 = 1 := fun m => by
    rw [hφ]; exact (isDirichletTrial_translate (hψ m) (c m)).2.2.2.2
  have hφE : ∀ m, energyD V (φ m) = energyD V (ψ m) := fun m => by
    rw [hφ]; exact energyD_translate V (ψ m) (c m)
  -- the block product `T`
  obtain ⟨T, hT⟩ : ∃ T : Conf N → ℂ, T = Product_T e φ := ⟨_, rfl⟩
  have hTd : ContDiff ℝ (⊤ : ℕ∞) T := hT ▸ Product_T_contDiff e hφd
  have hTc : HasCompactSupport T := hT ▸ Product_T_hasCompactSupport e hφc
  have hTs : tsupport T ⊆
      {x | ∀ j a, c (e.symm j).1 a < x j a ∧ x j a < c (e.symm j).1 a + ℓ} :=
    hT ▸ Product_T_tsupport e hφs
  have hTn : ∫ x, ‖T x‖ ^ 2 = 1 := hT ▸ Product_T_normSq e hφn
  have hTp : ∀ σ τ : Equiv.Perm (Fin N),
      (fun j => (e.symm j).1) ∘ σ.symm = (fun j => (e.symm j).1) ∘ τ.symm →
      ∀ x, T (x ∘ σ) = T (x ∘ τ) := fun σ τ h x => hT ▸ Product_T_perm e hφp h x
  have hTE : ∫ x, (Product_kin T x +
      (∑ i, ∑ j, if i ≠ j ∧ (e.symm i).1 = (e.symm j).1 then V (x i - x j) else 0) *
        ‖T x‖ ^ 2) = ∑ m, energyD V (ψ m) := by
    rw [hT, Product_integral_energy_T e hφd hφc hφn hV]
    exact Finset.sum_congr rfl fun m _ => hφE m
  have hT2 : Integrable (fun y => ‖T y‖ ^ 2) := by
    have hTcont := hTd.continuous
    have hc2 : Continuous (fun y => ‖T y‖ ^ 2) := by fun_prop
    have hcs : HasCompactSupport (fun y => ‖T y‖ ^ 2) :=
      hTc.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) (by simp)
    exact hc2.integrable_of_hasCompactSupport hcs
  -- the permuted copies `T(x ∘ σ)` and their classes
  have hfd : ∀ σ : Equiv.Perm (Fin N), ContDiff ℝ (⊤ : ℕ∞) (fun x => T (x ∘ σ)) :=
    fun σ => hTd.comp (Product_contDiff_perm σ)
  have hfs : ∀ (σ : Equiv.Perm (Fin N)) x, x ∈ tsupport (fun x => T (x ∘ σ)) →
      ∀ j a, c (e.symm j).1 a < x (σ j) a ∧ x (σ j) a < c (e.symm j).1 a + ℓ :=
    fun σ x hx => hTs (tsupport_comp_subset_preimage T (Product_continuous_perm σ) hx)
  have hfc : ∀ σ : Equiv.Perm (Fin N), HasCompactSupport (fun x => T (x ∘ σ)) := by
    intro σ
    refine HasCompactSupport.intro (IsCompact.image hTc (Product_continuous_perm σ.symm))
      (fun x hx => ?_)
    have : x ∘ σ ∉ tsupport T := fun h => hx ⟨x ∘ σ, h, by funext i; simp⟩
    exact image_eq_zero_of_notMem_tsupport this
  have hsup : ∀ x (σ τ : Equiv.Perm (Fin N)), x ∈ tsupport (fun x => T (x ∘ σ)) →
      x ∈ tsupport (fun x => T (x ∘ τ)) →
      (fun j => (e.symm j).1) ∘ σ.symm = (fun j => (e.symm j).1) ∘ τ.symm := by
    intro x σ τ h1 h2
    funext i
    have a1 := hfs σ x h1 (σ.symm i)
    have a2 := hfs τ x h2 (τ.symm i)
    simp only [Equiv.apply_symm_apply] at a1 a2
    exact Product_cube_unique hsep a1 a2
  obtain ⟨h, hh⟩ : ∃ h : ℕ, h = (Finset.univ.filter (fun σ : Equiv.Perm (Fin N) =>
      (fun j => (e.symm j).1) ∘ σ.symm = (fun j => (e.symm j).1))).card := ⟨_, rfl⟩
  have hh1 : 1 ≤ h := by
    rw [hh]
    exact Finset.card_pos.mpr
      ⟨1, by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, by funext j; rfl⟩⟩
  have hPW := Product_pointwise (fun σ x => T (x ∘ σ))
    (fun σ => (fun j => (e.symm j).1) ∘ σ.symm) h
    (fun σ => (hfd σ).differentiable (by simp)) (fun σ τ hστ => funext (hTp σ τ hστ))
    hsup (fun σ₀ => by rw [hh]; convert Product_card_class (fun j => (e.symm j).1) σ₀)
  -- the normalization `s = (h N!)^{-1/2}`
  have hNf : (0 : ℝ) < (h : ℝ) * (N.factorial : ℝ) := by
    have : (0 : ℝ) < h := by exact_mod_cast hh1
    positivity
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (Real.sqrt ((h : ℝ) * N.factorial))⁻¹ := ⟨_, rfl⟩
  have hs2 : s ^ 2 * ((h : ℝ) * N.factorial) = 1 := by
    rw [hs, inv_pow, Real.sq_sqrt hNf.le, inv_mul_cancel₀ hNf.ne']
  have hcount : ∀ C : ℝ, ∑ _σ : Equiv.Perm (Fin N), C = N.factorial * C := by
    intro C
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
  -- the symmetrized state `Φ = s Σ_σ T(x ∘ σ)`
  obtain ⟨Φ₀, hΦ₀⟩ : ∃ Φ₀ : Conf N → ℂ, Φ₀ = fun x => ∑ σ : Equiv.Perm (Fin N), T (x ∘ σ) :=
    ⟨_, rfl⟩
  have hΦ₀d : ContDiff ℝ (⊤ : ℕ∞) Φ₀ := hΦ₀ ▸ ContDiff.sum fun σ _ => hfd σ
  have hΦ₀z : ∀ x, x ∉ ⋃ σ : Equiv.Perm (Fin N), tsupport (fun x => T (x ∘ σ)) → Φ₀ x = 0 := by
    intro x hx
    have : ∀ σ : Equiv.Perm (Fin N), T (x ∘ σ) = 0 := fun σ =>
      image_eq_zero_of_notMem_tsupport (f := fun x => T (x ∘ σ))
        (fun h => hx (Set.mem_iUnion.2 ⟨σ, h⟩))
    simp [hΦ₀, this]
  have hΦd : ContDiff ℝ (⊤ : ℕ∞) (fun x => (s : ℂ) * Φ₀ x) := contDiff_const.mul hΦ₀d
  have hΦc : HasCompactSupport (fun x => (s : ℂ) * Φ₀ x) :=
    HasCompactSupport.intro (isCompact_iUnion fun σ => hfc σ)
      (fun x hx => by simp [hΦ₀z x hx])
  have hnorm : ∀ x, ‖(s : ℂ) * Φ₀ x‖ ^ 2 = s ^ 2 * h * ∑ σ : Equiv.Perm (Fin N), ‖T (x ∘ σ)‖ ^ 2 := by
    intro x
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, hΦ₀, (hPW x).1,
      mul_assoc]
  have hkin : ∀ x, Product_kin (fun x => (s : ℂ) * Φ₀ x) x =
      s ^ 2 * h * ∑ σ : Equiv.Perm (Fin N), Product_kin T (x ∘ σ) := by
    intro x
    have hd : fderiv ℝ (fun x => (s : ℂ) * Φ₀ x) x = (s : ℂ) • fderiv ℝ Φ₀ x :=
      fderiv_const_mul ((hΦ₀d.differentiable (by simp)) x) _
    have h1 : ∀ v, ‖((s : ℂ) • fderiv ℝ Φ₀ x) v‖ ^ 2 =
        ∑ σ : Equiv.Perm (Fin N), s ^ 2 * h * ‖fderiv ℝ (fun x => T (x ∘ σ)) x v‖ ^ 2 := by
      intro v
      rw [smul_apply, norm_smul, mul_pow, Complex.norm_real,
        Real.norm_eq_abs, sq_abs, hΦ₀, (hPW x).2 v, ← mul_assoc, Finset.mul_sum]
    rw [show (∑ σ : Equiv.Perm (Fin N), Product_kin T (x ∘ σ)) =
        ∑ σ : Equiv.Perm (Fin N), Product_kin (fun x => T (x ∘ σ)) x from
      Finset.sum_congr rfl fun σ _ => (Product_kin_perm T σ x).symm]
    unfold Product_kin
    simp_rw [hd, h1, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  refine ⟨fun x => (s : ℂ) * Φ₀ x, ⟨hΦd, hΦc, ?_, ?_, ?_⟩, ?_⟩
  · -- support in the open box
    have hK : tsupport (fun x => (s : ℂ) * Φ₀ x) ⊆
        ⋃ σ : Equiv.Perm (Fin N), tsupport (fun x => T (x ∘ σ)) := by
      refine closure_minimal (fun x hx => ?_)
        (isClosed_iUnion_of_finite fun σ => isClosed_tsupport _)
      by_contra hn
      exact hx (by simp [hΦ₀z x hn])
    intro x hx i a
    obtain ⟨σ, hσ⟩ := Set.mem_iUnion.1 (hK hx)
    have h1 := hfs σ x hσ (σ.symm i) a
    simp only [Equiv.apply_symm_apply] at h1
    have h2 := hbox (e.symm (σ.symm i)).1 a
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · -- symmetry
    intro ρ x
    simp only [hΦ₀]
    congr 1
    exact Equiv.sum_comp (Equiv.mulLeft ρ) (fun σ => T (x ∘ σ))
  · -- normalization
    simp_rw [hnorm]
    rw [integral_const_mul, integral_finsetSum _ (fun σ _ => Product_integrable_perm σ hT2)]
    rw [Finset.sum_congr rfl fun σ _ => (Product_integral_perm σ (fun y => ‖T y‖ ^ 2)).trans hTn,
      hcount, mul_one, mul_assoc, hs2]
  · -- energy
    set G : Conf N → ℝ := fun y => Product_kin T y +
      ((∑ i, ∑ j, if i ≠ j ∧ (e.symm i).1 = (e.symm j).1 then V (y i - y j) else 0) + B) *
        ‖T y‖ ^ 2 with hG
    have hIc : Continuous (fun y : Conf N =>
        ∑ i, ∑ j, if i ≠ j ∧ (e.symm i).1 = (e.symm j).1 then V (y i - y j) else 0) := by
      refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
      split_ifs
      · exact hV.comp ((continuous_apply i).sub (continuous_apply j))
      · exact continuous_const
    have hGint : Integrable G := Product_integrable hTd hTc (hIc.add continuous_const)
    have hbound : ∀ x, Product_kin (fun x => (s : ℂ) * Φ₀ x) x +
        Product_pair W x * ‖(s : ℂ) * Φ₀ x‖ ^ 2 ≤
          s ^ 2 * h * ∑ σ : Equiv.Perm (Fin N), G (x ∘ σ) := by
      intro x
      rw [hkin, hnorm]
      have hr : s ^ 2 * h * (∑ σ : Equiv.Perm (Fin N), Product_kin T (x ∘ σ)) +
          Product_pair W x * (s ^ 2 * h * ∑ σ : Equiv.Perm (Fin N), ‖T (x ∘ σ)‖ ^ 2) =
          s ^ 2 * h * ∑ σ : Equiv.Perm (Fin N),
            (Product_kin T (x ∘ σ) + Product_pair W x * ‖T (x ∘ σ)‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        ring
      rw [hr]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun σ _ => ?_) (by positivity)
      simp only [hG]
      refine add_le_add le_rfl ?_
      by_cases hz : T (x ∘ σ) = 0
      · simp [hz]
      · have hQ := hTs (subset_tsupport T (Function.mem_support.mpr hz))
        have hB := hWB (fun j => (e.symm j).1) (Product_card_fiber e) (x ∘ σ) hQ
        have hP : Product_pair W x = ∑ i, ∑ j,
            if i ≠ j then W ((x ∘ σ) i - (x ∘ σ) j) else 0 :=
          (Product_pair_perm W σ x).symm
        rw [hP]
        exact mul_le_mul_of_nonneg_right hB (sq_nonneg _)
    rw [Product_energyD_eq]
    calc ∫ x, (Product_kin (fun x => (s : ℂ) * Φ₀ x) x +
          Product_pair W x * ‖(s : ℂ) * Φ₀ x‖ ^ 2)
        ≤ ∫ x, s ^ 2 * h * ∑ σ : Equiv.Perm (Fin N), G (x ∘ σ) :=
          integral_mono (Product_integrable hΦd hΦc (Product_pair_continuous hW))
            ((integrable_finsetSum _ fun σ _ => Product_integrable_perm σ hGint).const_mul _)
            hbound
      _ = s ^ 2 * h * (N.factorial * ∫ y, G y) := by
          rw [integral_const_mul, integral_finsetSum _ fun σ _ => Product_integrable_perm σ hGint,
            Finset.sum_congr rfl fun σ _ => Product_integral_perm σ G, hcount]
      _ = ∫ y, G y := by rw [← mul_assoc, mul_assoc (s ^ 2), hs2, one_mul]
      _ = (∑ m, energyD V (ψ m)) + B := by
          have hsplit : ∀ y, G y = (Product_kin T y +
              (∑ i, ∑ j, if i ≠ j ∧ (e.symm i).1 = (e.symm j).1 then V (y i - y j) else 0) *
                ‖T y‖ ^ 2) + B * ‖T y‖ ^ 2 := fun y => by simp only [hG]; ring
          simp_rw [hsplit]
          rw [integral_add (Product_integrable hTd hTc hIc) (hT2.const_mul B), integral_const_mul,
            hTn, hTE, mul_one]

end LHYUpper
