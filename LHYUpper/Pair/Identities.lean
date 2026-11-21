module

public import LHYUpper.Assembly.Section4
public import LHYUpper.Fock.Decomp
public import LHYUpper.Fock.Expect
public import LHYUpper.Scattering.Solution
public import LHYUpper.TrialState.MStar
public import LHYUpper.TrialState.Normalization

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- `P = P_L ∪ P_I ∪ P_H` of Definition 3.1 [def1]. -/
def inP (ρ L : ℝ) (n : Idx) : Prop := inPL ρ L n ∨ inPI ρ L n ∨ inPH ρ L n

/-- `⟨Ψ| a†_{u₁} a†_{u₂} a_{u₃} a_{u₄} |Ψ⟩ = Σ_α conj(Ψ(T(α))) c(α) Ψ(α)`, the right side of
(7.4) [resultid4a], with `c(α) = √⟨α| A† A |α⟩` and `T(α)` the occupation of `A|α⟩`. -/
def Expect.E4 (Ψ : Occ → ℂ) (u₁ u₂ u₃ u₄ : Idx) : ℂ :=
  ∑' α : Occ, conj (Ψ (a4 u₁ u₂ u₃ u₄ α).2) * ((a4 u₁ u₂ u₃ u₄ α).1 : ℂ) * Ψ α

/-- Lemma 7.1 [id4a], (7.4) [resultid4a]: the series of `⟨Ψ| a†_{u₁} a†_{u₂} a_{u₃} a_{u₄} |Ψ⟩`
converges, and the expectation of the adjoint `a†_{u₄} a†_{u₃} a_{u₂} a_{u₁}` is its complex
conjugate. -/
theorem Lemma7_1 (N : ℕ) (Ψ : Occ → ℂ) (hΨ : IsNState N Ψ) (u₁ u₂ u₃ u₄ : Idx) :
    HasSum (fun α : Occ => conj (Ψ (a4 u₁ u₂ u₃ u₄ α).2) * ((a4 u₁ u₂ u₃ u₄ α).1 : ℂ) * Ψ α)
        (Expect.E4 Ψ u₁ u₂ u₃ u₄) ∧
      Expect.E4 Ψ u₄ u₃ u₂ u₁ = conj (Expect.E4 Ψ u₁ u₂ u₃ u₄) := by
  have hs := (Expect.id4a_summable N Ψ hΨ u₁ u₂ u₃ u₄).of_norm
  refine ⟨hs.hasSum, ?_⟩
  have hc : HasSum (fun α : Occ =>
      conj (conj (Ψ (a4 u₁ u₂ u₃ u₄ α).2) * ((a4 u₁ u₂ u₃ u₄ α).1 : ℂ) * Ψ α))
      (conj (Expect.E4 Ψ u₁ u₂ u₃ u₄)) := Complex.hasSum_conj'.mpr hs.hasSum
  have hne : ∀ α : Occ, conj (conj (Ψ (a4 u₁ u₂ u₃ u₄ α).2) * ((a4 u₁ u₂ u₃ u₄ α).1 : ℂ) * Ψ α)
      ≠ 0 → (a4 u₁ u₂ u₃ u₄ α).1 ≠ 0 := by
    intro α h h0
    apply h
    simp [h0]
  have key : HasSum
      (fun β : Occ => conj (Ψ (a4 u₄ u₃ u₂ u₁ β).2) * ((a4 u₄ u₃ u₂ u₁ β).1 : ℂ) * Ψ β)
      (conj (Expect.E4 Ψ u₁ u₂ u₃ u₄)) := by
    refine (hasSum_iff_hasSum_of_ne_zero_bij (fun x => (a4 u₁ u₂ u₃ u₄ x.1).2) ?_ ?_ ?_).mpr hc
    · intro x y hxy
      exact Subtype.ext (a4_injOn u₁ u₂ u₃ u₄ (hne _ x.2) (hne _ y.2) hxy)
    · intro β hβ
      have hβ' : (a4 u₄ u₃ u₂ u₁ β).1 ≠ 0 := by
        intro h0
        apply hβ
        simp [h0]
      have hadj := a4_adjoint u₄ u₃ u₂ u₁ β hβ'
      refine ⟨⟨(a4 u₄ u₃ u₂ u₁ β).2, ?_⟩, by simp [hadj]⟩
      simp only [Function.mem_support, hadj, ne_eq, map_mul, Complex.conj_conj,
        Complex.conj_ofReal]
      intro h0
      apply hβ
      simp only
      linear_combination h0
    · intro x
      have hadj := a4_adjoint u₁ u₂ u₃ u₄ x.1 (hne _ x.2)
      simp only [hadj, map_mul, Complex.conj_conj, Complex.conj_ofReal]
      ring
  exact key.tsum_eq

/-! ### Regrouping of the interaction series -/

/-- An occupation number is at most the particle number. -/
private lemma Identities_apply_le (α : Occ) (u : Idx) : α u ≤ α.num := by
  by_cases hu : u ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hu
  · rw [Finsupp.notMem_support_iff.mp hu]; exact Nat.zero_le _

/-- The particle number as a sum over the support. -/
private lemma Identities_num_eq (α : Occ) : (α.num : ℝ) = ∑ p ∈ α.support, (α p : ℝ) := by
  simp [Occ.num, Finsupp.sum]

/-- The series of `Q_Ψ(p, q)` of Definition 5.1 [1] converges. -/
private lemma Identities_Q_hasSum {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (p q : Idx) :
    HasSum (fun α : Occ => (α p : ℝ) * α q * ‖Ψ α‖ ^ 2) (Expect.Q Ψ [p, q]) := by
  have hs : Summable fun α : Occ => (α p : ℝ) * α q * ‖Ψ α‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_)
      (hΨ.1.summable.mul_left ((N : ℝ) ^ 2))
    by_cases h : Ψ α = 0
    · simp [h]
    · have hn := hΨ.2 α h
      have h1 : (α p : ℝ) ≤ N := by exact_mod_cast hn ▸ Identities_apply_le α p
      have h2 : (α q : ℝ) ≤ N := by exact_mod_cast hn ▸ Identities_apply_le α q
      have : (α p : ℝ) * α q ≤ (N : ℝ) ^ 2 := by
        rw [sq]; exact mul_le_mul h1 h2 (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right this (by positivity)
  have := hs.hasSum
  simpa [Expect.Q, mul_assoc] using this

/-- `Σ_{p, q} (α(p)α(q) − δ_{pq}α(p)) = n² − n` with `n = Σ_k α(k)`, (3.4) [number]. -/
private lemma Identities_diag_sum (α : Occ) :
    ∑ x ∈ α.support ×ˢ α.support,
      ((α x.1 : ℝ) * α x.2 - if x.1 = x.2 then (α x.1 : ℝ) else 0) =
      (α.num : ℝ) ^ 2 - α.num := by
  rw [Finset.sum_product, Identities_num_eq, sq, Finset.sum_mul_sum]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq]
  congr 1
  refine Finset.sum_congr rfl (fun p hp => ?_)
  simp [hp]

/-- `Σ_{p ≠ q} r_{pq} α(p)α(q) ≤ c (n² − α(0)²)` when `r ≤ c` and `c ≥ 0`. -/
private lemma Identities_offdiag_le (α : Occ) (r : Idx → Idx → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hr : ∀ p q, r p q ≤ c) :
    ∑ x ∈ α.support ×ˢ α.support,
      (if x.1 ≠ x.2 then r x.1 x.2 * ((α x.1 : ℝ) * α x.2) else 0) ≤
      c * ((α.num : ℝ) ^ 2 - α 0 * α 0) := by
  have h1 : ∀ x ∈ α.support ×ˢ α.support,
      (if x.1 ≠ x.2 then r x.1 x.2 * ((α x.1 : ℝ) * α x.2) else 0) ≤
        c * ((α x.1 : ℝ) * α x.2) - if x.1 = x.2 then c * ((α x.1 : ℝ) * α x.1) else 0 := by
    intro x _
    by_cases h : x.1 = x.2
    · simp [h]
    · simp only [ne_eq, h, not_false_eq_true, ite_true, ite_false, sub_zero]
      exact mul_le_mul_of_nonneg_right (hr _ _) (by positivity)
  refine (Finset.sum_le_sum h1).trans ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_product, Finset.sum_product,
    Identities_num_eq, sq, Finset.sum_mul_sum]
  simp only [Finset.sum_ite_eq]
  have h2 : ∑ p ∈ α.support, (if p ∈ α.support then c * ((α p : ℝ) * α p) else 0) =
      c * ∑ p ∈ α.support, (α p : ℝ) * α p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => by simp [hp])
  rw [h2, mul_sub]
  gcongr
  by_cases h0 : (0 : Idx) ∈ α.support
  · exact Finset.single_le_sum (f := fun p => (α p : ℝ) * α p) (fun _ _ => by positivity) h0
  · rw [Finsupp.notMem_support_iff.mp h0]
    simp only [Nat.cast_zero, mul_zero]
    exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- `mom L 0 = 0`. -/
private lemma Identities_mom_zero (L : ℝ) : mom L 0 = 0 := by
  ext i
  simp [mom]

/-- The summand of (4.3) on the branch `u = 0`: `a†_p a†_q a_p a_q`, (3.4) [number]. -/
private lemma Identities_intTerm_diag (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (p q : Idx) (α : Occ) :
    intTerm L V Ψ (p, q, 0, α) = (L ^ 3)⁻¹ * ft V 0 *
      ((((α p : ℝ) * α q - if p = q then (α p : ℝ) else 0) * ‖Ψ α‖ ^ 2 : ℝ) : ℂ) := by
  simp only [intTerm, sub_zero, add_zero, Identities_mom_zero]
  by_cases hc : (a4 p q p q α).1 = 0
  · rw [← a4_diag_fst, hc]
    simp
  · rw [a4_diag_snd p q α hc, ← a4_diag_fst]
    push_cast
    rw [← Complex.conj_mul']
    ring

/-- The summand of (4.3) on the branch `u = p − q`, `p ≠ q`: `a†_p a†_q a_q a_p`. -/
private lemma Identities_intTerm_exch (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) {p q : Idx}
    (hpq : p ≠ q) (α : Occ) :
    intTerm L V Ψ (p, q, p - q, α) = (L ^ 3)⁻¹ * ft V (mom L (p - q)) *
      (((α p : ℝ) * α q * ‖Ψ α‖ ^ 2 : ℝ) : ℂ) := by
  simp only [intTerm, sub_sub_cancel, add_sub_cancel]
  have hsq := a4_fst_sq p q q p α
  simp only [hpq, Ne.symm hpq, ite_true, ite_false, sub_zero, add_sub_cancel_right] at hsq
  have hc : (a4 p q q p α).1 = (α p : ℝ) * α q := by
    have h0 := a4_fst_nonneg p q q p α
    have : (a4 p q q p α).1 ^ 2 = ((α p : ℝ) * α q) ^ 2 := by rw [hsq]; ring
    exact (sq_eq_sq₀ h0 (by positivity)).mp this
  by_cases h0 : (a4 p q q p α).1 = 0
  · rw [hc] at h0
    rw [hc, h0]
    simp
  · obtain ⟨β, hβ⟩ := a4_exists_add p q q p α h0
    have hT : (a4 p q q p α).2 = α := by
      rw [hβ, a4_of_add]
    rw [hT, hc]
    push_cast
    rw [← Complex.conj_mul']
    ring

/-- Regrouping of a part of the interaction series of (2.1) [ham] along an injective
reindexing by a product: the part has sum `Σ_b h(b)`, where `h(b)` is the sum of the fiber
over `b`. -/
private lemma Identities_hasSum_reindex {β γ : Type*} {L : ℝ} {V : R3 → ℝ} {N : ℕ}
    {Ψ : Occ → ℂ} (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ)
    (F : Idx × Idx × Idx × Occ → ℂ) (hF : ∀ i, F i = 0 ∨ F i = intTerm L V Ψ i)
    (g : β × γ → Idx × Idx × Idx × Occ) (hg : Function.Injective g)
    (hrange : ∀ i, F i ≠ 0 → i ∈ Set.range g) (h : β → ℂ)
    (hf : ∀ b, HasSum (fun c => F (g (b, c))) (h b)) :
    HasSum F (∑' b, h b) ∧ HasSum h (∑' b, h b) := by
  have hG : Summable (F ∘ g) := by
    refine Summable.of_norm_bounded
      ((Decomp.intTerm_summable_norm L V N Ψ hV hΨ).comp_injective hg) (fun x => ?_)
    rcases hF (g x) with h0 | h0 <;> simp [h0]
  have hsum := hG.hasSum.prod_fiberwise hf
  rw [hsum.tsum_eq]
  refine ⟨(hg.hasSum_iff (fun i hi => ?_)).mp hG.hasSum, hsum⟩
  by_contra h0
  exact hi (hrange i h0)

/-- The branch `u = 0` of `H_{S1}`, (4.3): its sum is `|Λ|⁻¹ V₀ (N² − N)`. -/
private lemma Identities_S1_diag {L : ℝ} {V : R3 → ℝ} {N : ℕ} {Ψ : Occ → ℂ}
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    HasSum (fun i : Idx × Idx × Idx × Occ => if i.2.2.1 = 0 then intTerm L V Ψ i else 0)
      ((L ^ 3)⁻¹ * ft V 0 * (((N : ℝ) ^ 2 - N : ℝ) : ℂ)) := by
  have hg : Function.Injective
      (fun x : Occ × (Idx × Idx) => (x.2.1, x.2.2, (0 : Idx), x.1)) := by
    rintro ⟨α, p, q⟩ ⟨α', p', q'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -, rfl⟩ := h
    rfl
  have key := (Identities_hasSum_reindex hV hΨ
    (fun i : Idx × Idx × Idx × Occ => if i.2.2.1 = 0 then intTerm L V Ψ i else 0)
    (fun i => by split_ifs <;> simp) _ hg (fun i hi => ?_)
    (fun α => (L ^ 3)⁻¹ * ft V 0 * ((((α.num : ℝ) ^ 2 - α.num) * ‖Ψ α‖ ^ 2 : ℝ) : ℂ))
    (fun α => ?_)).1
  · have hval : ∑' α : Occ,
        (L ^ 3)⁻¹ * ft V 0 * ((((α.num : ℝ) ^ 2 - α.num) * ‖Ψ α‖ ^ 2 : ℝ) : ℂ) =
        (L ^ 3)⁻¹ * ft V 0 * (((N : ℝ) ^ 2 - N : ℝ) : ℂ) := by
      refine HasSum.tsum_eq ?_
      have hh := (Complex.hasSum_ofReal.mpr (hΨ.1.mul_left ((N : ℝ) ^ 2 - N))).mul_left
        ((L ^ 3)⁻¹ * ft V 0)
      rw [mul_one] at hh
      convert hh using 1
      funext α
      by_cases h : Ψ α = 0
      · simp [h]
      · rw [hΨ.2 α h]
    rw [hval] at key
    exact key
  · obtain ⟨p, q, u, α⟩ := i
    by_cases hu : u = 0
    · exact ⟨(α, p, q), by simp [hu]⟩
    · simp [hu] at hi
  · have hz : ∀ c ∉ α.support ×ˢ α.support, intTerm L V Ψ (c.1, c.2, 0, α) = 0 := by
      intro c hc
      rw [Identities_intTerm_diag]
      rw [Finset.mem_product, not_and_or, Finsupp.notMem_support_iff,
        Finsupp.notMem_support_iff] at hc
      rcases hc with h | h
      · simp [h]
      · by_cases hpq : c.1 = c.2
        · simp [hpq, h]
        · simp [hpq, h]
    have h2 : HasSum (fun c : Idx × Idx => intTerm L V Ψ (c.1, c.2, 0, α)) _ :=
      hasSum_sum_of_ne_finset_zero hz
    simp only [ite_true]
    convert h2 using 1
    simp only [Identities_intTerm_diag]
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, ← Finset.sum_mul, Identities_diag_sum]

/-- The branch `u = p − q`, `p ≠ q` of `H_{S1}`, (4.3), with the occupation `α` outside. -/
private lemma Identities_S1_exch_occ {L : ℝ} {V : R3 → ℝ} {N : ℕ} {Ψ : Occ → ℂ}
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    ∃ s : ℂ, HasSum (fun i : Idx × Idx × Idx × Occ =>
        if i.2.2.1 = i.1 - i.2.1 ∧ i.1 ≠ i.2.1 then intTerm L V Ψ i else 0) s ∧
      HasSum (fun α : Occ => ∑ x ∈ α.support ×ˢ α.support, if x.1 ≠ x.2 then
        (L ^ 3)⁻¹ * ft V (mom L (x.1 - x.2)) * (((α x.1 : ℝ) * α x.2 * ‖Ψ α‖ ^ 2 : ℝ) : ℂ)
        else 0) s := by
  have hg : Function.Injective
      (fun x : Occ × (Idx × Idx) => (x.2.1, x.2.2, x.2.1 - x.2.2, x.1)) := by
    rintro ⟨α, p, q⟩ ⟨α', p', q'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -, rfl⟩ := h
    rfl
  refine ⟨_, Identities_hasSum_reindex hV hΨ
    (fun i : Idx × Idx × Idx × Occ =>
      if i.2.2.1 = i.1 - i.2.1 ∧ i.1 ≠ i.2.1 then intTerm L V Ψ i else 0)
    (fun i => by split_ifs <;> simp) _ hg (fun i hi => ?_)
    (fun α : Occ => ∑ x ∈ α.support ×ˢ α.support, if x.1 ≠ x.2 then
        (L ^ 3)⁻¹ * ft V (mom L (x.1 - x.2)) * (((α x.1 : ℝ) * α x.2 * ‖Ψ α‖ ^ 2 : ℝ) : ℂ)
        else 0) (fun α => ?_)⟩
  · obtain ⟨p, q, u, α⟩ := i
    by_cases hu : u = p - q ∧ p ≠ q
    · exact ⟨(α, p, q), by simp [hu.1]⟩
    · simp only [hu, ite_false, ne_eq, not_true_eq_false] at hi
  · have he : ∀ c : Idx × Idx,
        (if c.1 - c.2 = c.1 - c.2 ∧ c.1 ≠ c.2 then
          intTerm L V Ψ (c.1, c.2, c.1 - c.2, α) else 0) =
        if c.1 ≠ c.2 then
          (L ^ 3)⁻¹ * ft V (mom L (c.1 - c.2)) * (((α c.1 : ℝ) * α c.2 * ‖Ψ α‖ ^ 2 : ℝ) : ℂ)
          else 0 := by
      intro c
      by_cases hpq : c.1 = c.2
      · simp [hpq]
      · simp only [ne_eq, hpq, not_false_eq_true, and_true, ite_true]
        exact Identities_intTerm_exch L V Ψ hpq α
    have h2 : HasSum (fun c : Idx × Idx => if c.1 ≠ c.2 then
          (L ^ 3)⁻¹ * ft V (mom L (c.1 - c.2)) * (((α c.1 : ℝ) * α c.2 * ‖Ψ α‖ ^ 2 : ℝ) : ℂ)
          else 0)
        (∑ x ∈ α.support ×ˢ α.support, if x.1 ≠ x.2 then
          (L ^ 3)⁻¹ * ft V (mom L (x.1 - x.2)) * (((α x.1 : ℝ) * α x.2 * ‖Ψ α‖ ^ 2 : ℝ) : ℂ)
          else 0) := by
      refine hasSum_sum_of_ne_finset_zero (fun c hc => ?_)
      rw [Finset.mem_product, not_and_or, Finsupp.notMem_support_iff,
        Finsupp.notMem_support_iff] at hc
      rcases hc with h | h <;> simp [h]
    convert h2 using 2 with c
    exact he c

/-- `H_{S1}` of (4.3) splits into the branches `u = 0` and `u = p − q`, `p ≠ q`. -/
private lemma Identities_S1_split (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) :
    Decomp.partTerm .S1 L V Ψ = fun i =>
      (if i.2.2.1 = 0 then intTerm L V Ψ i else 0) +
        (if i.2.2.1 = i.1 - i.2.1 ∧ i.1 ≠ i.2.1 then intTerm L V Ψ i else 0) := by
  funext ⟨p, q, u, α⟩
  simp only [Decomp.partTerm, Decomp.Part.mem, Decomp.InS1]
  by_cases hu : u = 0
  · subst hu
    have : ¬ (0 = p - q ∧ p ≠ q) := fun h => h.2 (sub_eq_zero.mp h.1.symm)
    simp [this]
  · by_cases h : u = p - q
    · have hpq : p ≠ q := fun e => hu (by rw [h, e, sub_self])
      subst h
      simp [sub_ne_zero.mpr hpq, hpq]
    · simp [hu, h]

/-- The summand of (4.4) at `(p, q, u) = (u, −u, u)`: `a†_u a†_{−u} a_0 a_0`. -/
private lemma Identities_intTerm_S2a (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (u : Idx) (α : Occ) :
    intTerm L V Ψ (u, -u, u, α) = (L ^ 3)⁻¹ * ft V (mom L u) *
      (conj (Ψ (a4 u (-u) 0 0 α).2) * ((a4 u (-u) 0 0 α).1 : ℂ) * Ψ α) := by
  simp only [intTerm, sub_self, neg_add_cancel]
  ring

/-- The summand of (4.4) at `(p, q, u) = (0, 0, u)`: `a†_0 a†_0 a_{−u} a_u`. -/
private lemma Identities_intTerm_S2b (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (u : Idx) (α : Occ) :
    intTerm L V Ψ (0, 0, u, α) = (L ^ 3)⁻¹ * ft V (mom L u) *
      (conj (Ψ (a4 0 0 (-u) u α).2) * ((a4 0 0 (-u) u α).1 : ℂ) * Ψ α) := by
  simp only [intTerm, zero_sub, zero_add]
  ring

/-- `H_{S2}` of (4.4) splits into the terms `(u, −u, u)` and `(0, 0, u)`, `u ≠ 0`. -/
private lemma Identities_S2_split (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) :
    Decomp.partTerm .S2 L V Ψ = fun i =>
      (if i.2.2.1 ≠ 0 ∧ i.1 = i.2.2.1 ∧ i.2.1 = -i.2.2.1 then intTerm L V Ψ i else 0) +
        (if i.2.2.1 ≠ 0 ∧ i.1 = 0 ∧ i.2.1 = 0 then intTerm L V Ψ i else 0) := by
  funext ⟨p, q, u, α⟩
  simp only [Decomp.partTerm, Decomp.Part.mem]
  by_cases hu : u = 0
  · simp [hu]
  · by_cases hp : p = u ∧ q = -u
    · simp [hu, hp]
    · simp [hu, hp]

/-- The two terms of `H_{S2}`, (4.4), summed over `α` for each `u`. -/
private lemma Identities_S2_parts {L : ℝ} {V : R3 → ℝ} {N : ℕ} {Ψ : Occ → ℂ}
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    (HasSum (fun i : Idx × Idx × Idx × Occ =>
        if i.2.2.1 ≠ 0 ∧ i.1 = i.2.2.1 ∧ i.2.1 = -i.2.2.1 then intTerm L V Ψ i else 0)
      (∑' u : Idx, if u ≠ 0 then (L ^ 3)⁻¹ * ft V (mom L u) * Expect.E4 Ψ u (-u) 0 0
        else 0) ∧
      HasSum (fun u : Idx => if u ≠ 0 then (L ^ 3)⁻¹ * ft V (mom L u) * Expect.E4 Ψ u (-u) 0 0
        else 0)
      (∑' u : Idx, if u ≠ 0 then (L ^ 3)⁻¹ * ft V (mom L u) * Expect.E4 Ψ u (-u) 0 0
        else 0)) ∧
    (HasSum (fun i : Idx × Idx × Idx × Occ =>
        if i.2.2.1 ≠ 0 ∧ i.1 = 0 ∧ i.2.1 = 0 then intTerm L V Ψ i else 0)
      (∑' u : Idx, if u ≠ 0 then (L ^ 3)⁻¹ * ft V (mom L u) * Expect.E4 Ψ 0 0 (-u) u
        else 0) ∧
      HasSum (fun u : Idx => if u ≠ 0 then (L ^ 3)⁻¹ * ft V (mom L u) * Expect.E4 Ψ 0 0 (-u) u
        else 0)
      (∑' u : Idx, if u ≠ 0 then (L ^ 3)⁻¹ * ft V (mom L u) * Expect.E4 Ψ 0 0 (-u) u
        else 0)) := by
  constructor
  · have hg : Function.Injective (fun x : Idx × Occ => (x.1, -x.1, x.1, x.2)) := by
      rintro ⟨u, α⟩ ⟨u', α'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, -, -, rfl⟩ := h
      rfl
    refine Identities_hasSum_reindex hV hΨ
      (fun i : Idx × Idx × Idx × Occ =>
        if i.2.2.1 ≠ 0 ∧ i.1 = i.2.2.1 ∧ i.2.1 = -i.2.2.1 then intTerm L V Ψ i else 0)
      (fun i => by split_ifs <;> simp) _ hg (fun i hi => ?_) _ (fun u => ?_)
    · obtain ⟨p, q, u, α⟩ := i
      by_cases h : u ≠ 0 ∧ p = u ∧ q = -u
      · obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨(p, α), rfl⟩
      · simp only [h, ite_false, ne_eq, not_true_eq_false] at hi
    · by_cases hu : u = 0
      · simp only [hu, ne_eq, not_true_eq_false, false_and, ite_false]
        exact hasSum_zero
      · simp only [ne_eq, hu, not_false_eq_true, and_self, ite_true, Identities_intTerm_S2a]
        exact (Lemma7_1 N Ψ hΨ u (-u) 0 0).1.mul_left _
  · have hg : Function.Injective (fun x : Idx × Occ => ((0 : Idx), (0 : Idx), x.1, x.2)) := by
      rintro ⟨u, α⟩ ⟨u', α'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, -, rfl, rfl⟩ := h
      rfl
    refine Identities_hasSum_reindex hV hΨ
      (fun i : Idx × Idx × Idx × Occ =>
        if i.2.2.1 ≠ 0 ∧ i.1 = 0 ∧ i.2.1 = 0 then intTerm L V Ψ i else 0)
      (fun i => by split_ifs <;> simp) _ hg (fun i hi => ?_) _ (fun u => ?_)
    · obtain ⟨p, q, u, α⟩ := i
      by_cases h : u ≠ 0 ∧ p = 0 ∧ q = 0
      · obtain ⟨-, rfl, rfl⟩ := h
        exact ⟨(u, α), rfl⟩
      · simp only [h, ite_false, ne_eq, not_true_eq_false] at hi
    · by_cases hu : u = 0
      · simp only [hu, ne_eq, not_true_eq_false, false_and, ite_false]
        exact hasSum_zero
      · simp only [ne_eq, hu, not_false_eq_true, and_self, ite_true, Identities_intTerm_S2b]
        exact (Lemma7_1 N Ψ hΨ 0 0 (-u) u).1.mul_left _

/-- The index set of `H_{S3}` at `(p, q, u) = (p, −p, p − v)`: `p, v ≠ 0` and `p ≠ ±v`. -/
private lemma Identities_S3_mem (p v : Idx) :
    Decomp.Part.S3.mem p (-p) (p - v) ↔ p ≠ 0 ∧ v ≠ 0 ∧ p ≠ v ∧ p + v ≠ 0 := by
  have h1 : -p + (p - v) = -v := by abel
  have h2 : p - v = p - -p ↔ p + v = 0 := by
    rw [sub_right_inj, eq_neg_iff_add_eq_zero, add_comm]
  simp only [Decomp.Part.mem, Decomp.zeros, Decomp.InS1, sub_sub_cancel, h1, neg_eq_zero,
    add_neg_cancel, h2, sub_eq_zero]
  constructor
  · rintro ⟨hz, -, hs⟩
    simp only [Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false] at hz
    exact ⟨hz.1.1.1, hz.1.2, (not_or.mp hs).1, (not_or.mp hs).2⟩
  · rintro ⟨hp, hv, hpv, hs⟩
    simp [hp, hv, hpv, hs]

/-- The summand of (4.5) at `(p, q, u) = (p, −p, p − v)`: `a†_p a†_{−p} a_v a_{−v}`. -/
private lemma Identities_intTerm_S3 (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (p v : Idx) (α : Occ) :
    intTerm L V Ψ (p, -p, p - v, α) = (L ^ 3)⁻¹ * ft V (mom L (p - v)) *
      (conj (Ψ (a4 p (-p) v (-v) α).2) * ((a4 p (-p) v (-v) α).1 : ℂ) * Ψ α) := by
  have h1 : -p + (p - v) = -v := by abel
  simp only [intTerm, sub_sub_cancel, h1]
  ring

/-- `⟨H_{S2}⟩_Ψ = |Λ|⁻¹ Σ_{u ≠ 0} V_u (⟨a†_u a†_{−u} a_0 a_0⟩_Ψ + c.c.)`, from (4.4) and
Lemma 7.1 [id4a]. -/
theorem Lemma7_1_S2 (L : ℝ) (V : R3 → ℝ) (N : ℕ) (Ψ : Occ → ℂ)
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    HasSum (Decomp.partTerm .S2 L V Ψ)
      ((L ^ 3)⁻¹ * (∑' u : Idx, if u ≠ 0 then
        ft V (mom L u) * (Expect.E4 Ψ u (-u) 0 0 + conj (Expect.E4 Ψ u (-u) 0 0)) else 0)) := by
  obtain ⟨⟨hA, hA'⟩, ⟨hB, hB'⟩⟩ := Identities_S2_parts hV hΨ
  rw [Identities_S2_split]
  convert hA.add hB using 1
  rw [← (hA'.add hB').tsum_eq, ← tsum_mul_left]
  congr 1
  funext u
  by_cases hu : u = 0
  · simp [hu]
  · simp only [ne_eq, hu, not_false_eq_true, ite_true, (Lemma7_1 N Ψ hΨ u (-u) 0 0).2]
    ring

/-- `⟨H_{S3}⟩_Ψ = |Λ|⁻¹ Σ_{u, v ≠ 0, u ≠ ±v} V_{u−v} ⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ`, from (4.5) summed
over `u ≠ ±v` and Lemma 7.1 [id4a]. -/
theorem Lemma7_1_S3 (L : ℝ) (V : R3 → ℝ) (N : ℕ) (Ψ : Occ → ℂ)
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    HasSum (Decomp.partTerm .S3 L V Ψ)
      ((L ^ 3)⁻¹ * (∑' uv : Idx × Idx,
        if uv.1 ≠ 0 ∧ uv.2 ≠ 0 ∧ uv.1 ≠ uv.2 ∧ uv.1 + uv.2 ≠ 0 then
          ft V (mom L (uv.1 - uv.2)) * Expect.E4 Ψ uv.1 (-uv.1) uv.2 (-uv.2) else 0)) := by
  have hg : Function.Injective
      (fun x : (Idx × Idx) × Occ => (x.1.1, -x.1.1, x.1.1 - x.1.2, x.2)) := by
    rintro ⟨⟨p, v⟩, α⟩ ⟨⟨p', v'⟩, α'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -, h3, rfl⟩ := h
    rw [sub_right_inj] at h3
    rw [h3]
  have key := (Identities_hasSum_reindex hV hΨ (Decomp.partTerm .S3 L V Ψ)
    (fun i => by unfold Decomp.partTerm; split_ifs <;> simp) _ hg (fun i hi => ?_)
    (fun uv => (L ^ 3)⁻¹ * (if uv.1 ≠ 0 ∧ uv.2 ≠ 0 ∧ uv.1 ≠ uv.2 ∧ uv.1 + uv.2 ≠ 0 then
          ft V (mom L (uv.1 - uv.2)) * Expect.E4 Ψ uv.1 (-uv.1) uv.2 (-uv.2) else 0))
    (fun uv => ?_)).1
  · rw [tsum_mul_left] at key
    exact key
  · obtain ⟨p, q, u, α⟩ := i
    by_cases h : Decomp.Part.S3.mem p q u
    · have hq : q = -p := eq_neg_of_add_eq_zero_right h.2.1
      subst hq
      exact ⟨((p, p - u), α), by simp⟩
    · simp [Decomp.partTerm, h] at hi
  · obtain ⟨p, v⟩ := uv
    simp only [Decomp.partTerm]
    by_cases h : p ≠ 0 ∧ v ≠ 0 ∧ p ≠ v ∧ p + v ≠ 0
    · simp only [(Identities_S3_mem p v).mpr h, h, ne_eq, not_false_eq_true, and_self,
        ite_true, Identities_intTerm_S3]
      convert (Lemma7_1 N Ψ hΨ p (-p) v (-v)).1.mul_left ((L ^ 3)⁻¹ * ft V (mom L (p - v)))
        using 1
      ring
    · have h' : ¬ Decomp.Part.S3.mem p (-p) (p - v) := fun hm =>
        h ((Identities_S3_mem p v).mp hm)
      simp only [h', h, ite_false, mul_zero]
      exact hasSum_zero

/-- `Q_Ψ(−u₁, …, −u_s) = Q_Ψ(u₁, …, u_s)` for the trial state (3.18) [deffal], which is invariant
under `k ↦ −k`. -/
theorem Pair_Q_neg (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (us : List Idx) :
    Expect.Q (trialState V w kc N) (us.map Neg.neg) = Expect.Q (trialState V w kc N) us := by
  have hΨ : ∀ α, trialState V w kc N (MStar_reflect α) = trialState V w kc N α := by
    intro α
    simp only [trialState, MStar_reflect_iff, MStar_f0_reflect]
  have happ : ∀ α n, MStar_reflect α n = α (-n) := by
    intro α n
    simp [MStar_reflect, Finsupp.equivMapDomain_apply]
  let e : Occ ≃ Occ :=
    ⟨MStar_reflect, MStar_reflect, fun α => by ext n; simp [happ], fun α => by ext n; simp [happ]⟩
  unfold Expect.Q
  rw [← e.tsum_eq]
  congr 1
  funext β
  simp only [e, Equiv.coe_fn_mk, hΨ, List.map_map, Function.comp_def, happ, neg_neg]

/-- (7.1)–(7.2): `⟨H_{S1}⟩_Ψ ≤ |Λ|⁻¹ V₀ (2N² − N − Q_Ψ(0, 0))` for every normalized `N`-particle
state, from `|V_p| ≤ V₀` and `a†_u a†_u a_u a_u ≤ (a†_u a_u)²`. -/
theorem Eq7_2 {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 1 ≤ L) {N : ℕ} {Ψ : Occ → ℂ}
    (hΨ : IsNState N Ψ) :
    ∃ I : ℝ, HasSum (Decomp.partTerm .S1 L V Ψ) (I : ℂ) ∧
      I ≤ (L ^ 3)⁻¹ * V0 V * (2 * (N : ℝ) ^ 2 - N - Expect.Q Ψ [0, 0]) := by
  have hL0 : 0 < L := by linarith
  have hV' : Summable fun u : Idx => ‖ft V (mom L u)‖ :=
    ((scat_lattice_V hV).choose_spec L hL).1
  have hV0 : V0 V = ∫ x, V x := by rw [V0, scat_ft_zero, Complex.ofReal_re]
  have hle : ∀ p, (ft V p).re ≤ V0 V := fun p =>
    (Complex.re_le_norm _).trans (hV0 ▸ scat_ft_V_norm_le hV p)
  have hV0nn : 0 ≤ V0 V := (norm_nonneg _).trans (hV0 ▸ scat_ft_V_norm_le hV 0)
  have h0 := Identities_S1_diag hV' hΨ
  obtain ⟨s, h1, hk⟩ := Identities_S1_exch_occ hV' hΨ
  have hF : HasSum (Decomp.partTerm .S1 L V Ψ)
      ((L ^ 3)⁻¹ * ft V 0 * (((N : ℝ) ^ 2 - N : ℝ) : ℂ) + s) := by
    rw [Identities_S1_split]
    exact h0.add h1
  have him := Decomp.im_eq_zero_of_hasSum _ _ _ _ _ hF
  refine ⟨((L ^ 3)⁻¹ * ft V 0 * (((N : ℝ) ^ 2 - N : ℝ) : ℂ) + s).re, ?_, ?_⟩
  · convert hF using 1
    exact Complex.ext (Complex.ofReal_re _) (by rw [Complex.ofReal_im, him])
  have hQ := Identities_Q_hasSum hΨ 0 0
  have hb : HasSum (fun α : Occ => (L ^ 3)⁻¹ * V0 V *
      ((N : ℝ) ^ 2 * ‖Ψ α‖ ^ 2 - (α 0 : ℝ) * α 0 * ‖Ψ α‖ ^ 2))
      ((L ^ 3)⁻¹ * V0 V * ((N : ℝ) ^ 2 - Expect.Q Ψ [0, 0])) := by
    have := ((hΨ.1.mul_left ((N : ℝ) ^ 2)).sub hQ).mul_left ((L ^ 3)⁻¹ * V0 V)
    rwa [mul_one] at this
  have hs : s.re ≤ (L ^ 3)⁻¹ * V0 V * ((N : ℝ) ^ 2 - Expect.Q Ψ [0, 0]) := by
    refine hasSum_le (fun α => ?_) (Complex.hasSum_re hk) hb
    have hre : ∀ x : Idx × Idx, (if x.1 ≠ x.2 then
        (L ^ 3)⁻¹ * ft V (mom L (x.1 - x.2)) * (((α x.1 : ℝ) * α x.2 * ‖Ψ α‖ ^ 2 : ℝ) : ℂ)
        else 0).re = ((L ^ 3)⁻¹ * ‖Ψ α‖ ^ 2) *
          (if x.1 ≠ x.2 then (ft V (mom L (x.1 - x.2))).re * ((α x.1 : ℝ) * α x.2) else 0) := by
      intro x
      split_ifs
      · rw [Complex.re_mul_ofReal, Complex.re_ofReal_mul]
        ring
      · simp
    simp only [Complex.re_sum, hre, ← Finset.mul_sum]
    have hW : 0 ≤ (L ^ 3)⁻¹ * ‖Ψ α‖ ^ 2 := by positivity
    calc (L ^ 3)⁻¹ * ‖Ψ α‖ ^ 2 * ∑ x ∈ α.support ×ˢ α.support,
          (if x.1 ≠ x.2 then (ft V (mom L (x.1 - x.2))).re * ((α x.1 : ℝ) * α x.2) else 0)
        ≤ (L ^ 3)⁻¹ * ‖Ψ α‖ ^ 2 * (V0 V * ((α.num : ℝ) ^ 2 - α 0 * α 0)) :=
          mul_le_mul_of_nonneg_left (Identities_offdiag_le α
            (fun p q => (ft V (mom L (p - q))).re) (V0 V) hV0nn (fun p q => hle _)) hW
      _ = (L ^ 3)⁻¹ * V0 V *
          ((N : ℝ) ^ 2 * ‖Ψ α‖ ^ 2 - (α 0 : ℝ) * α 0 * ‖Ψ α‖ ^ 2) := by
          by_cases hα : Ψ α = 0
          · simp [hα]
          · rw [hΨ.2 α hα]
            ring
  have h0re : ((L ^ 3)⁻¹ * ft V 0 * (((N : ℝ) ^ 2 - N : ℝ) : ℂ)).re =
      (L ^ 3)⁻¹ * V0 V * ((N : ℝ) ^ 2 - N) := by
    rw [hV0, scat_ft_zero, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [Complex.add_re, h0re]
  have : (L ^ 3)⁻¹ * V0 V * (2 * (N : ℝ) ^ 2 - N - Expect.Q Ψ [0, 0]) =
      (L ^ 3)⁻¹ * V0 V * ((N : ℝ) ^ 2 - N) +
        (L ^ 3)⁻¹ * V0 V * ((N : ℝ) ^ 2 - Expect.Q Ψ [0, 0]) := by ring
  rw [this]
  linarith

end LHYUpper
