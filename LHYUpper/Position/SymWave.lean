module

public import LHYUpper.Scattering.Solution
public import LHYUpper.Position.Basic

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! Symmetrized plane waves `Φ_α` and state functions `Φ_Ψ` of the position form of
the Hamiltonian (2.1) [ham] on the torus `[0, L]³`: expansion in the last particle, smoothness,
permutation symmetry, orthonormality and the norm of `Φ_Ψ`. -/

/-! ### Occupation assignments -/

/-- `p ∈ occFns N α` iff every momentum `k` is taken by exactly `α k` particles. -/
private lemma SymWave_mem_occFns {N : ℕ} {α : Occ} {p : Fin N → Idx} :
    p ∈ occFns N α ↔ ∀ k, (Finset.univ.filter fun i => p i = k).card = α k := by
  unfold occFns
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun i => ?_, h⟩⟩
  rw [Finsupp.mem_support_iff, ← h (p i)]
  exact (Finset.card_pos.2 ⟨i, by simp⟩).ne'

/-- Splitting off the last particle in the occupation count. -/
private lemma SymWave_card_filter_succ {N : ℕ} (p : Fin (N + 1) → Idx) (m : Idx) :
    (Finset.univ.filter fun i => p i = m).card =
      (Finset.univ.filter fun i : Fin N => p i.castSucc = m).card +
        if p (Fin.last N) = m then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]

private lemma SymWave_mem_occFns_comp {N : ℕ} {α : Occ} {p : Fin N → Idx}
    (σ : Equiv.Perm (Fin N)) (hp : p ∈ occFns N α) : p ∘ σ ∈ occFns N α := by
  rw [SymWave_mem_occFns] at hp ⊢
  intro k
  rw [← hp k]
  exact Finset.card_equiv σ (by simp)

private lemma SymWave_sub_single_apply (α : Occ) (k m : Idx) :
    (α - Finsupp.single k 1 : Occ) m = α m - if k = m then 1 else 0 := by
  rw [Finsupp.tsub_apply, Finsupp.single_apply]

/-- `∏ α! = α(k) ∏ (α - δ_k)!` for `k` in the support. -/
private lemma SymWave_prod_fact (α : Occ) {k : Idx} (hk : k ∈ α.support) :
    (α.prod fun _ m => (m.factorial : ℝ)) =
      (α k : ℝ) * ((α - Finsupp.single k 1).prod fun _ m => (m.factorial : ℝ)) := by
  have hsub : (α - Finsupp.single k 1).support ⊆ α.support := by
    intro a ha
    rw [Finsupp.mem_support_iff] at ha ⊢
    intro h0
    apply ha
    simp [h0]
  rw [Finsupp.prod_of_support_subset _ hsub _ (by simp)]
  unfold Finsupp.prod
  rw [← Finset.mul_prod_erase α.support (fun a => ((α a).factorial : ℝ)) hk,
    ← Finset.mul_prod_erase α.support (fun a => (((α - Finsupp.single k 1 : Occ) a).factorial : ℝ))
      hk]
  have h1 : ∏ a ∈ α.support.erase k, ((α a).factorial : ℝ) =
      ∏ a ∈ α.support.erase k, (((α - Finsupp.single k 1 : Occ) a).factorial : ℝ) := by
    refine Finset.prod_congr rfl fun a ha => ?_
    have hne : k ≠ a := (Finset.ne_of_mem_erase ha).symm
    rw [SymWave_sub_single_apply]
    simp [hne]
  rw [h1, ← mul_assoc]
  congr 1
  obtain ⟨j, hj⟩ : ∃ j, α k = j + 1 := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hk)
  rw [SymWave_sub_single_apply, hj]
  simp [Nat.factorial_succ]

/-- The sum over `occFns (N+1) α` split by the momentum of the last particle. -/
private lemma SymWave_sum_succ (L : ℝ) (N : ℕ) (α : Occ) (x : Conf (N + 1)) :
    ∑ p ∈ occFns (N + 1) α, ∏ i, planeWave L (p i) (x i) =
      ∑ k ∈ α.support, planeWave L k (x (Fin.last N)) *
        ∑ p ∈ occFns N (α - Finsupp.single k 1), ∏ i, planeWave L (p i) (Fin.init x i) := by
  have hmaps : ∀ p ∈ occFns (N + 1) α, p (Fin.last N) ∈ α.support := by
    intro p hp
    rw [SymWave_mem_occFns] at hp
    rw [Finsupp.mem_support_iff, ← hp (p (Fin.last N))]
    exact (Finset.card_pos.2 ⟨Fin.last N, by simp⟩).ne'
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => p (Fin.last N)) hmaps]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mul_sum]
  have hk1 : 1 ≤ α k := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hk)
  refine Finset.sum_nbij' (fun p => Fin.init p) (fun p' => Fin.snoc p' k) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter, SymWave_mem_occFns] at hp
    rw [SymWave_mem_occFns]
    intro m
    have h1 := hp.1 m
    rw [SymWave_card_filter_succ, hp.2] at h1
    rw [SymWave_sub_single_apply]
    change (Finset.univ.filter fun i : Fin N => p i.castSucc = m).card = _
    by_cases h : k = m <;> simp only [h, ↓reduceIte] at h1 ⊢ <;> omega
  · intro p' hp'
    rw [Finset.mem_filter, SymWave_mem_occFns]
    refine ⟨?_, by simp⟩
    rw [SymWave_mem_occFns] at hp'
    intro m
    rw [SymWave_card_filter_succ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hp' m, SymWave_sub_single_apply]
    by_cases h : k = m
    · subst h; simp only [↓reduceIte]; omega
    · simp [h]
  · intro p hp
    rw [Finset.mem_filter] at hp
    conv_rhs => rw [← Fin.snoc_init_self p, hp.2]
  · intro p' hp'
    simp
  · intro p hp
    rw [Finset.mem_filter] at hp
    rw [Fin.prod_univ_castSucc, hp.2, mul_comm]
    rfl

private lemma SymWave_planeWave_contDiff (L : ℝ) (n : Idx) :
    ContDiff ℝ (⊤ : ℕ∞) (planeWave L n) := by
  unfold planeWave
  refine contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul ?_))
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : R3 => inner ℝ (mom L n) y) :=
    contDiff_const.inner ℝ contDiff_id
  exact Complex.ofRealCLM.contDiff.comp h1

/-- `Φ_α` is smooth. -/
theorem symWave_contDiff (L : ℝ) (N : ℕ) (α : Occ) : ContDiff ℝ (⊤ : ℕ∞) (symWave L N α) := by
  unfold symWave
  refine contDiff_const.mul (ContDiff.sum fun p _ => ?_)
  refine contDiff_prod fun i _ => ?_
  exact (SymWave_planeWave_contDiff L (p i)).comp (contDiff_apply ℝ (fun _ : Fin N => R3) i)

/-- `Φ_α` is symmetric under permutations of the particles. -/
theorem symWave_perm (L : ℝ) (N : ℕ) (α : Occ) (σ : Equiv.Perm (Fin N)) (x : Conf N) :
    symWave L N α (x ∘ σ) = symWave L N α x := by
  have h1 : ∀ p : Fin N → Idx, ∏ i, planeWave L (p i) ((x ∘ σ) i) =
      ∏ j, planeWave L ((p ∘ σ.symm) j) (x j) := by
    intro p
    rw [← Equiv.prod_comp σ (fun j => planeWave L ((p ∘ σ.symm) j) (x j))]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp
  have h2 : ∑ p ∈ occFns N α, ∏ i, planeWave L (p i) ((x ∘ σ) i) =
      ∑ p ∈ occFns N α, ∏ i, planeWave L (p i) (x i) := by
    simp_rw [h1]
    refine Finset.sum_nbij' (fun p => p ∘ σ.symm) (fun p => p ∘ σ) ?_ ?_ ?_ ?_ ?_
    · exact fun p hp => SymWave_mem_occFns_comp σ.symm hp
    · exact fun p hp => SymWave_mem_occFns_comp σ hp
    · intro p _
      funext i
      simp
    · intro p _
      funext i
      simp
    · intro p _
      rfl
  unfold symWave
  rw [h2]

/-- Expansion of `Φ_α` in the last particle:
`Φ_α(x', y) = Σ_k (α(k)/(N+1))^{1/2} e_k(y) Φ_{α - δ_k}(x')`. -/
theorem symWave_succ (L : ℝ) (N : ℕ) (α : Occ) (x : Conf (N + 1)) :
    symWave L (N + 1) α x = ∑ k ∈ α.support,
      (Real.sqrt ((α k : ℝ) / ((N : ℝ) + 1)) : ℂ) * planeWave L k (x (Fin.last N)) *
        symWave L N (α - Finsupp.single k 1) (Fin.init x) := by
  have hN : (N.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero N)
  have hc : ∀ k ∈ α.support,
      (Real.sqrt ((α.prod fun _ m => (m.factorial : ℝ)) / (((N + 1).factorial : ℕ) : ℝ)) : ℂ) =
        (Real.sqrt ((α k : ℝ) / ((N : ℝ) + 1)) : ℂ) *
          (Real.sqrt (((α - Finsupp.single k 1 : Occ).prod fun _ m => (m.factorial : ℝ)) /
            (N.factorial : ℝ)) : ℂ) := by
    intro k hk
    rw [← Complex.ofReal_mul, SymWave_prod_fact α hk, Nat.factorial_succ]
    congr 1
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  unfold symWave
  rw [SymWave_sum_succ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [hc k hk]
  ring

/-! ### Integration over the period cells -/

private lemma SymWave_isCompact_cell (L : ℝ) : IsCompact (cell L) := by
  have h : cell L = (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin 3 => Set.Icc 0 L) := by
    ext y
    constructor
    · intro hy
      exact ⟨WithLp.ofLp y, fun a _ => hy a, by simp⟩
    · rintro ⟨z, hz, rfl⟩ a
      exact hz a (Set.mem_univ a)
  rw [h]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

private lemma SymWave_isCompact_cellN (L : ℝ) (N : ℕ) : IsCompact (cellN L N) := by
  have h : cellN L N = Set.pi Set.univ fun _ : Fin N => cell L := by
    ext x
    simp [cellN]
  rw [h]
  exact isCompact_univ_pi fun _ => SymWave_isCompact_cell L

/-- Splitting off the last particle in an integral over `[0, L]^{3(N+1)}`. -/
private lemma SymWave_integral_cellN_succ (L : ℝ) (N : ℕ) (f : Conf (N + 1) → ℂ) :
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

/-! ### Particle numbers -/

private lemma SymWave_num_sub_single {α : Occ} {k : Idx} (hk : k ∈ α.support) :
    (α - Finsupp.single k 1 : Occ).num + 1 = α.num := by
  have hk1 : 1 ≤ α k := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hk)
  have h : α = (α - Finsupp.single k 1) + Finsupp.single k 1 :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 hk1)).symm
  conv_rhs => rw [h]
  unfold Occ.num
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

private lemma SymWave_num_eq_zero {α : Occ} (h : α.num = 0) : α = 0 := by
  by_contra hne
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.2 hne
  have := SymWave_num_sub_single hk
  omega

private lemma SymWave_eq_of_sub_single {α β : Occ} {k : Idx} (hα : k ∈ α.support)
    (hβ : k ∈ β.support) (h : (α - Finsupp.single k 1 : Occ) = β - Finsupp.single k 1) : α = β := by
  have h1 : 1 ≤ α k := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hα)
  have h2 : 1 ≤ β k := Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hβ)
  rw [← tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h1),
    ← tsub_add_cancel_of_le (Finsupp.single_le_iff.2 h2), h]

/-- The final bookkeeping of the orthonormality induction. -/
private lemma SymWave_final (N : ℕ) {α β : Occ} (hα : α.num = N + 1) :
    ∑ k' ∈ β.support, ∑ k ∈ α.support,
      (((Real.sqrt ((β k' : ℝ) / ((N : ℝ) + 1)) * Real.sqrt ((α k : ℝ) / ((N : ℝ) + 1)) : ℝ) : ℂ) *
        ((if k' = k then (1 : ℂ) else 0) *
          (if (α - Finsupp.single k 1 : Occ) = β - Finsupp.single k' 1 then (1 : ℂ) else 0))) =
      if α = β then 1 else 0 := by
  have h1 : ∀ k' ∈ β.support, ∑ k ∈ α.support,
      (((Real.sqrt ((β k' : ℝ) / ((N : ℝ) + 1)) * Real.sqrt ((α k : ℝ) / ((N : ℝ) + 1)) : ℝ) : ℂ) *
        ((if k' = k then (1 : ℂ) else 0) *
          (if (α - Finsupp.single k 1 : Occ) = β - Finsupp.single k' 1 then (1 : ℂ) else 0))) =
      (((Real.sqrt ((β k' : ℝ) / ((N : ℝ) + 1)) * Real.sqrt ((α k' : ℝ) / ((N : ℝ) + 1)) : ℝ) : ℂ) *
        (if (α - Finsupp.single k' 1 : Occ) = β - Finsupp.single k' 1 then (1 : ℂ) else 0)) := by
    intro k' _
    rw [Finset.sum_eq_single k']
    · simp
    · intro k _ hk
      simp [Ne.symm hk]
    · intro hk
      have : α k' = 0 := Finsupp.notMem_support_iff.1 hk
      simp [this]
  rw [Finset.sum_congr rfl h1]
  by_cases hab : α = β
  · subst hab
    simp only [mul_one, ↓reduceIte]
    have h2 : ∀ k' ∈ α.support, (((Real.sqrt ((α k' : ℝ) / ((N : ℝ) + 1)) *
        Real.sqrt ((α k' : ℝ) / ((N : ℝ) + 1)) : ℝ) : ℂ)) =
        (((α k' : ℝ) / ((N : ℝ) + 1) : ℝ) : ℂ) := by
      intro k' _
      rw [Real.mul_self_sqrt (by positivity)]
    rw [Finset.sum_congr rfl h2, ← Complex.ofReal_sum, ← Finset.sum_div]
    have h3 : ∑ k' ∈ α.support, (α k' : ℝ) = (N : ℝ) + 1 := by
      have : (α.num : ℝ) = (N : ℝ) + 1 := by exact_mod_cast hα
      rw [← this]
      simp [Occ.num, Finsupp.sum]
    rw [h3, div_self (by positivity)]
    simp
  · simp only [hab, ↓reduceIte]
    refine Finset.sum_eq_zero fun k' hk' => ?_
    by_cases hk : k' ∈ α.support
    · have : ¬ ((α - Finsupp.single k' 1 : Occ) = β - Finsupp.single k' 1) :=
        fun h => hab (SymWave_eq_of_sub_single hk hk' h)
      simp [this]
    · have : α k' = 0 := Finsupp.notMem_support_iff.1 hk
      simp [this]

private lemma SymWave_continuous (L : ℝ) (N : ℕ) (α : Occ) : Continuous (symWave L N α) :=
  (symWave_contDiff L N α).continuous

private lemma SymWave_integrableOn_prod {L : ℝ} {N : ℕ} {f : R3 × Conf N → ℂ}
    (hf : Continuous f) :
    Integrable f (((volume : Measure R3).prod (volume : Measure (Conf N))).restrict
      (cell L ×ˢ cellN L N)) :=
  hf.continuousOn.integrableOn_compact
    ((SymWave_isCompact_cell L).prod (SymWave_isCompact_cellN L N))

/-- The `(k', k)` summand of `conj Φ_β(x', y) · Φ_α(x', y)` after expanding in the last particle
`y`. -/
private def SymWave_T (L : ℝ) (N : ℕ) (α β : Occ) (k' k : Idx) (z : R3 × Conf N) : ℂ :=
  (((Real.sqrt ((β k' : ℝ) / ((N : ℝ) + 1)) * Real.sqrt ((α k : ℝ) / ((N : ℝ) + 1)) : ℝ) : ℂ) *
    ((conj (planeWave L k' z.1) * planeWave L k z.1) *
      (conj (symWave L N (β - Finsupp.single k' 1) z.2) *
        symWave L N (α - Finsupp.single k 1) z.2)))

private lemma SymWave_T_continuous (L : ℝ) (N : ℕ) (α β : Occ) (k' k : Idx) :
    Continuous (SymWave_T L N α β k' k) := by
  have h1 : Continuous (planeWave L k') := (SymWave_planeWave_contDiff L k').continuous
  have h2 : Continuous (planeWave L k) := (SymWave_planeWave_contDiff L k).continuous
  have h3 := SymWave_continuous L N (β - Finsupp.single k' 1)
  have h4 := SymWave_continuous L N (α - Finsupp.single k 1)
  unfold SymWave_T
  exact continuous_const.mul
    (((Complex.continuous_conj.comp (h1.comp continuous_fst)).mul (h2.comp continuous_fst)).mul
      ((Complex.continuous_conj.comp (h3.comp continuous_snd)).mul (h4.comp continuous_snd)))

private lemma SymWave_expand (L : ℝ) (N : ℕ) (α β : Occ) (z : R3 × Conf N) :
    conj (symWave L (N + 1) β (Fin.snoc z.2 z.1)) * symWave L (N + 1) α (Fin.snoc z.2 z.1) =
      ∑ k' ∈ β.support, ∑ k ∈ α.support, SymWave_T L N α β k' k z := by
  rw [symWave_succ, symWave_succ]
  simp only [Fin.snoc_last, Fin.init_snoc, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [SymWave_T, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- The induction step of the orthonormality of `Φ_α`: the last particle is integrated out. -/
private lemma SymWave_orthonormal_succ {L : ℝ} (hL : 0 < L) {N : ℕ} {α β : Occ}
    (hα : α.num = N + 1) (hβ : β.num = N + 1)
    (ih : ∀ α β : Occ, α.num = N → β.num = N →
      ∫ x in cellN L N, conj (symWave L N β x) * symWave L N α x = if α = β then 1 else 0) :
    ∫ x in cellN L (N + 1), conj (symWave L (N + 1) β x) * symWave L (N + 1) α x =
      if α = β then 1 else 0 := by
  rw [SymWave_integral_cellN_succ]
  simp_rw [SymWave_expand]
  have hint : ∀ k' k, Integrable (SymWave_T L N α β k' k)
      (((volume : Measure R3).prod (volume : Measure (Conf N))).restrict
        (cell L ×ˢ cellN L N)) := fun k' k =>
    SymWave_integrableOn_prod (SymWave_T_continuous L N α β k' k)
  rw [integral_finsetSum _ (fun k' _ => integrable_finsetSum _ (fun k _ => hint k' k))]
  have hk' : ∀ k' ∈ β.support,
      ∫ z in cell L ×ˢ cellN L N, ∑ k ∈ α.support, SymWave_T L N α β k' k z
          ∂((volume : Measure R3).prod (volume : Measure (Conf N))) =
      ∑ k ∈ α.support,
        (((Real.sqrt ((β k' : ℝ) / ((N : ℝ) + 1)) *
            Real.sqrt ((α k : ℝ) / ((N : ℝ) + 1)) : ℝ) : ℂ) *
          ((if k' = k then (1 : ℂ) else 0) *
            (if (α - Finsupp.single k 1 : Occ) = β - Finsupp.single k' 1 then (1 : ℂ)
              else 0))) := by
    intro k' hk'
    rw [integral_finsetSum _ (fun k _ => hint k' k)]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [SymWave_T]
    rw [integral_const_mul, setIntegral_prod_mul
      (fun y : R3 => conj (planeWave L k' y) * planeWave L k y)
      (fun x : Conf N => conj (symWave L N (β - Finsupp.single k' 1) x) *
        symWave L N (α - Finsupp.single k 1) x), planeWave_orthonormal hL,
      ih (α - Finsupp.single k 1) (β - Finsupp.single k' 1)
        (by have := SymWave_num_sub_single hk; omega)
        (by have := SymWave_num_sub_single hk'; omega)]
  rw [Finset.sum_congr rfl hk']
  exact SymWave_final N hα

/-- The symmetrized plane waves `Φ_α` with `Σ_k α(k) = N` are orthonormal in
`L²([0, L]^{3N})`. -/
theorem symWave_orthonormal {L : ℝ} (hL : 0 < L) {N : ℕ} {α β : Occ} (hα : α.num = N)
    (hβ : β.num = N) :
    ∫ x in cellN L N, conj (symWave L N β x) * symWave L N α x = if α = β then 1 else 0 := by
  induction N generalizing α β with
  | zero =>
    have hα0 := SymWave_num_eq_zero hα
    have hβ0 := SymWave_num_eq_zero hβ
    subst hα0
    subst hβ0
    have h0 : ∀ x : Conf 0, symWave L 0 0 x = 1 := by
      intro x
      have hocc : occFns 0 0 = {fun i => i.elim0} := by
        ext p
        rw [SymWave_mem_occFns, Finset.mem_singleton]
        constructor
        · intro _
          funext i
          exact i.elim0
        · intro _ k
          simp
      simp [symWave, hocc]
    have hcell : cellN L 0 = Set.univ := Set.eq_univ_of_forall fun x i => i.elim0
    simp only [h0, hcell, map_one, mul_one, Measure.restrict_univ, ↓reduceIte]
    rw [integral_const]
    have hvol : (volume : Measure (Conf 0)) Set.univ = 1 := by
      change (Measure.pi fun _ : Fin 0 => (volume : Measure R3)) Set.univ = 1
      rw [Measure.pi_univ]
      simp
    simp [Measure.real, hvol]
  | succ N ih => exact SymWave_orthonormal_succ hL hα hβ fun _ _ => ih

private lemma SymWave_integrable (L : ℝ) (N : ℕ) (f : Conf N → ℂ) (hf : Continuous f) :
    Integrable f (volume.restrict (cellN L N)) :=
  hf.continuousOn.integrableOn_compact (SymWave_isCompact_cellN L N)

/-- A finitely supported normalized `N`-particle state `Ψ` gives a normalized `Φ_Ψ` on
`[0, L]^{3N}`. -/
theorem stateFn_norm {L : ℝ} (hL : 0 < L) {N : ℕ} (Ψ : Occ →₀ ℂ) (hΨ : IsNState N Ψ) :
    ∫ x in cellN L N, ‖stateFn L N Ψ x‖ ^ 2 = 1 := by
  obtain ⟨hsum, hnum⟩ := hΨ
  have hnorm : ∑ α ∈ Ψ.support, ‖Ψ α‖ ^ 2 = 1 := by
    have h : HasSum (fun α : Occ => ‖Ψ α‖ ^ 2) (∑ α ∈ Ψ.support, ‖Ψ α‖ ^ 2) :=
      hasSum_sum_of_ne_finset_zero (fun b hb => by simp [Finsupp.notMem_support_iff.1 hb])
    exact h.unique hsum
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have h1 : ∀ x : Conf N, (((‖stateFn L N Ψ x‖ ^ 2 : ℝ)) : ℂ) =
      ∑ β ∈ Ψ.support, ∑ α ∈ Ψ.support,
        (conj (Ψ β) * Ψ α) * (conj (symWave L N β x) * symWave L N α x) := by
    intro x
    have h := Complex.conj_mul' (stateFn L N Ψ x)
    push_cast
    rw [← h]
    unfold stateFn
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
    rw [map_mul]
    ring
  simp_rw [h1]
  have hint : ∀ β α : Occ, Integrable (fun x : Conf N =>
      (conj (Ψ β) * Ψ α) * (conj (symWave L N β x) * symWave L N α x))
      (volume.restrict (cellN L N)) := fun β α =>
    SymWave_integrable L N _ (continuous_const.mul
      ((Complex.continuous_conj.comp (SymWave_continuous L N β)).mul
        (SymWave_continuous L N α)))
  rw [integral_finsetSum _ (fun β _ => integrable_finsetSum _ (fun α _ => hint β α))]
  have hβ : ∀ β ∈ Ψ.support,
      ∫ x in cellN L N, ∑ α ∈ Ψ.support,
        (conj (Ψ β) * Ψ α) * (conj (symWave L N β x) * symWave L N α x) = conj (Ψ β) * Ψ β := by
    intro β hβ
    have hβN : β.num = N := hnum β (Finsupp.mem_support_iff.1 hβ)
    rw [integral_finsetSum _ (fun α _ => hint β α), Finset.sum_eq_single β]
    · rw [integral_const_mul, symWave_orthonormal hL hβN hβN]
      simp
    · intro α hα hne
      rw [integral_const_mul, symWave_orthonormal hL (hnum α (Finsupp.mem_support_iff.1 hα)) hβN]
      simp [hne]
    · intro h
      exact absurd hβ h
  rw [Finset.sum_congr rfl hβ]
  have h2 : ∀ β ∈ Ψ.support, conj (Ψ β) * Ψ β = ((‖Ψ β‖ ^ 2 : ℝ) : ℂ) := by
    intro β _
    rw [Complex.conj_mul']
    push_cast
    rfl
  rw [Finset.sum_congr rfl h2, ← Complex.ofReal_sum, hnorm]

end LHYUpper
