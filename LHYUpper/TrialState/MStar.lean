module

public import LHYUpper.TrialState.MBasic

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # The values `α*(u)` on `M` and reflection symmetry

Properties of `α*(u) = max {α(u), α(-u)}` ((3.10) [def*]) on the set `M` of Definition 3.4 [M]: the
values at `±u`, `u ∈ P_L`, differ by at most one and `α*(u) - α(u) ∈ {0, 1}`, and `α*(u) < m_c + 1`
and `α*(u) ≤ ⌈m_c⌉` ((3.8) [defmc]). Shows that `M` is invariant under the reflection `α ↦ α(-·)`,
that the coefficient of (3.18) [deffal] is reflection invariant, and that `α ∈ M_u^a` and `𝓐^{u,k} α
∈ M` imply `α(u) = α(-u) + 1` (§5, after Lemma 5.1 [f]). -/

section MStar
variable {ρ L kc : ℝ} {N : ℕ}

private lemma MStar_norm_mom_neg (L : ℝ) (n : Idx) : ‖mom L (-n)‖ = ‖mom L n‖ := by
  have : mom L (-n) = -mom L n := by
    ext i
    simp [mom]
  rw [this, norm_neg]

private lemma MStar_neg_ne_self {u : Idx} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

/-- Value at `n ∈ P_L` of a strict pair creation. -/
private lemma MStar_strictPair_PL (hρ : 0 < ρ) {k : Idx} {α : Occ} {n : Idx}
    (hn : inPL ρ L n) :
    strictPair k α n = α n + (if n = k then 1 else 0) + (if n = -k then 1 else 0) := by
  rw [MBasic_strictPair_apply]
  simp [Regions_PL_ne_zero hρ hn]

/-- Value at `n ∈ P_L` of a soft pair creation with created momenta in `P_H`. -/
private lemma MStar_softPair_PL (hρ : 0 < ρ) {u p₁ p₂ : Idx} {α : Occ} {n : Idx}
    (h₁ : inPH ρ L p₁) (h₂ : inPH ρ L p₂) (hn : inPL ρ L n) :
    softPair u p₁ p₂ α n = α n - (if n = u then 1 else 0) := by
  rw [MBasic_softPair_apply]
  have e1 : n ≠ p₁ := fun h => Regions_PL_PH hρ hn (h ▸ h₁)
  have e2 : n ≠ p₂ := fun h => Regions_PL_PH hρ hn (h ▸ h₂)
  simp [Regions_PL_ne_zero hρ hn, e1, e2]

/-- A strict pair creation at `k ∈ P_I ∪ P_H` does not change the values at `±u`, `u ∈ P_L`. -/
private lemma MStar_strict_far (hρ : 0 < ρ) {k u : Idx} {α : Occ}
    (hk : inPI ρ L k ∨ inPH ρ L k) (hu : inPL ρ L u) :
    strictPair k α u = α u ∧ strictPair k α (-u) = α (-u) := by
  have key : ∀ {v : Idx}, inPL ρ L v → v ≠ k ∧ v ≠ -k := by
    intro v hv
    constructor
    · rintro rfl
      rcases hk with hk | hk
      · exact Regions_PL_PI hv hk
      · exact Regions_PL_PH hρ hv hk
    · intro h
      have hv' : inPL ρ L (-k) := h ▸ hv
      rcases hk with hk | hk
      · exact Regions_PL_PI (Regions_PL_neg.1 hv') hk
      · exact Regions_PL_PH hρ (Regions_PL_neg.1 hv') hk
  have hu' := Regions_PL_neg.2 hu
  rw [MStar_strictPair_PL hρ hu, MStar_strictPair_PL hρ hu']
  simp [(key hu).1, (key hu).2, (key hu').1, (key hu').2]

/-- A strict pair creation at `k ∈ P_L` raises the values at `±k` by one and does not change the
values at the other momenta of `±P_L`. -/
private lemma MStar_strict_near (hρ : 0 < ρ) {k u : Idx} {α : Occ}
    (hk : inPL ρ L k) (hu : inPL ρ L u) :
    (u = k ∨ u = -k → strictPair k α u = α u + 1 ∧ strictPair k α (-u) = α (-u) + 1) ∧
    (¬ (u = k ∨ u = -k) → strictPair k α u = α u ∧ strictPair k α (-u) = α (-u)) := by
  have hkn := MStar_neg_ne_self (Regions_PL_ne_zero hρ hk)
  have hu' := Regions_PL_neg.2 hu
  rw [MStar_strictPair_PL hρ hu, MStar_strictPair_PL hρ hu']
  constructor
  · rintro (rfl | rfl)
    · simp [hkn, hkn.symm]
    · simp [hkn, hkn.symm]
  · intro h
    rw [not_or] at h
    have h1 : -u ≠ -k := fun e => h.1 (neg_inj.1 e)
    have h2 : -u ≠ k := fun e => h.2 (by rw [← e]; simp)
    simp [h.1, h.2, h1, h2]

/-- The values at `±u`, `u ∈ P_L`, of a state in `M` differ by at most one. -/
private lemma MStar_PL_diff (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) {u : Idx}
    (hu : inPL ρ L u) : α u ≤ α (-u) + 1 ∧ α (-u) ≤ α u + 1 := by
  induction h generalizing u with
  | free =>
    have h1 := Regions_PL_ne_zero hρ hu
    have h2 := Regions_PL_ne_zero hρ (Regions_PL_neg.2 hu)
    simp [Ne.symm h1, Ne.symm h2]
  | @strictIH α k _ hk _ ih =>
    obtain ⟨e1, e2⟩ := MStar_strict_far (α := α) hρ hk hu
    rw [e1, e2]
    exact ih hu
  | @strictL α k _ hk _ _ ih =>
    by_cases hx : u = k ∨ u = -k
    · obtain ⟨e1, e2⟩ := (MStar_strict_near (α := α) hρ hk hu).1 hx
      rw [e1, e2]
      have := ih hu
      omega
    · obtain ⟨e1, e2⟩ := (MStar_strict_near (α := α) hρ hk hu).2 hx
      rw [e1, e2]
      exact ih hu
  | @soft α u₀ p₁ p₂ _ hu₀ hs _ h₁ h₂ _ _ _ _ ih =>
    have hu' := Regions_PL_neg.2 hu
    rw [MStar_softPair_PL hρ h₁ h₂ hu, MStar_softPair_PL hρ h₁ h₂ hu']
    have hn := MStar_neg_ne_self (Regions_PL_ne_zero hρ hu₀)
    have := ih hu
    by_cases hx : u = u₀
    · subst hx
      simp only [hn, ite_true, ite_false]
      omega
    · by_cases hy : -u = u₀
      · subst hy
        simp only [hx, ite_true, ite_false]
        simp only [neg_neg] at *
        omega
      · simp only [hx, hy, ite_false]
        omega

/-- `α*(u) < m_c + 1` for `u ∈ P_L` and a state in `M`. -/
private lemma MStar_PL_mc_aux (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) {u : Idx}
    (hu : inPL ρ L u) : ((alphaStar α u : ℕ) : ℝ) < mc ρ + 1 := by
  have hmc : 0 < mc ρ := Real.rpow_pos_of_pos hρ _
  induction h generalizing u with
  | free =>
    have h1 := Regions_PL_ne_zero hρ hu
    have h2 := Regions_PL_ne_zero hρ (Regions_PL_neg.2 hu)
    simp [alphaStar, Ne.symm h1, Ne.symm h2]
    linarith
  | @strictIH α k _ hk _ ih =>
    obtain ⟨e1, e2⟩ := MStar_strict_far (α := α) hρ hk hu
    unfold alphaStar
    rw [e1, e2]
    exact ih hu
  | @strictL α k _ hk hlt _ ih =>
    by_cases hx : u = k ∨ u = -k
    · obtain ⟨e1, e2⟩ := (MStar_strict_near (α := α) hρ hk hu).1 hx
      have e3 : alphaStar (strictPair k α) u = alphaStar α k + 1 := by
        unfold alphaStar at hlt ⊢
        rw [e1, e2]
        rcases hx with rfl | rfl
        · omega
        · simp only [neg_neg]
          omega
      rw [e3]
      push_cast
      linarith
    · obtain ⟨e1, e2⟩ := (MStar_strict_near (α := α) hρ hk hu).2 hx
      unfold alphaStar
      rw [e1, e2]
      exact ih hu
  | @soft α u₀ p₁ p₂ _ hu₀ hs _ h₁ h₂ _ _ _ _ ih =>
    have hu' := Regions_PL_neg.2 hu
    have hn := MStar_neg_ne_self (Regions_PL_ne_zero hρ hu₀)
    have key : alphaStar (softPair u₀ p₁ p₂ α) u ≤ alphaStar α u := by
      unfold alphaStar
      rw [MStar_softPair_PL hρ h₁ h₂ hu, MStar_softPair_PL hρ h₁ h₂ hu']
      by_cases hx : u = u₀
      · subst hx
        simp only [hn, ite_true, ite_false]
        omega
      · by_cases hy : -u = u₀
        · subst hy
          simp only [hx, ite_true, ite_false]
          simp only [neg_neg] at *
          omega
        · simp only [hx, hy, ite_false]
          omega
    have := ih hu
    have key' : ((alphaStar (softPair u₀ p₁ p₂ α) u : ℕ) : ℝ) ≤ alphaStar α u := by
      exact_mod_cast key
    linarith

/-- `α*(u) - α(u) ∈ {0, 1}` for `u ∈ P_L` (§3, after (3.10) [def*]). -/
theorem MStar_PL_star (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) {u : Idx}
    (hu : inPL ρ L u) : alphaStar α u = α u ∨ alphaStar α u = α u + 1 := by
  obtain ⟨h1, h2⟩ := MStar_PL_diff hρ h hu
  unfold alphaStar
  omega

/-- `α*(u) < m_c + 1` for `u ∈ P_L`, (3.8) [defmc]. -/
theorem MStar_PL_mc (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) {u : Idx}
    (hu : inPL ρ L u) : ((alphaStar α u : ℕ) : ℝ) < mc ρ + 1 := by
  exact MStar_PL_mc_aux hρ h hu

/-- `α*(u) ≤ ⌈m_c⌉` for `u ∈ P_L`, (3.8) [defmc]. -/
theorem MStar_PL_ceil (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) {u : Idx}
    (hu : inPL ρ L u) : alphaStar α u ≤ ⌈mc ρ⌉₊ := by
  by_contra hc
  rw [not_le] at hc
  have h1 : ((⌈mc ρ⌉₊ : ℕ) : ℝ) + 1 ≤ ((alphaStar α u : ℕ) : ℝ) := by
    exact_mod_cast hc
  have h2 := MStar_PL_mc hρ h hu
  have h3 := Nat.le_ceil (mc ρ)
  linarith

/-- The reflection `α ↦ α(-·)`. -/
def MStar_reflect (α : Occ) : Occ := Finsupp.equivMapDomain (Equiv.neg Idx) α

private lemma MStar_reflect_apply (α : Occ) (n : Idx) : MStar_reflect α n = α (-n) := by
  simp [MStar_reflect, Finsupp.equivMapDomain_apply]

private lemma MStar_reflect_reflect (α : Occ) : MStar_reflect (MStar_reflect α) = α := by
  ext n
  simp [MStar_reflect_apply]

private lemma MStar_reflect_single (n : ℕ) :
    MStar_reflect (Finsupp.single 0 n) = Finsupp.single 0 n := by
  simp [MStar_reflect, Finsupp.equivMapDomain_single]

private lemma MStar_reflect_strictPair (k : Idx) (α : Occ) :
    MStar_reflect (strictPair k α) = strictPair (-k) (MStar_reflect α) := by
  ext n
  rw [MStar_reflect_apply, MBasic_strictPair_apply, MBasic_strictPair_apply,
    MStar_reflect_apply]
  have e0 : (-n = 0) ↔ (n = 0) := neg_eq_zero
  have e1 : (-n = k) ↔ (n = -k) := neg_eq_iff_eq_neg
  have e2 : (-n = -k) ↔ (n = k) := neg_inj
  simp only [e0, e1, e2, neg_neg]

private lemma MStar_reflect_softPair (u p₁ p₂ : Idx) (α : Occ) :
    MStar_reflect (softPair u p₁ p₂ α) = softPair (-u) (-p₁) (-p₂) (MStar_reflect α) := by
  ext n
  rw [MStar_reflect_apply, MBasic_softPair_apply, MBasic_softPair_apply, MStar_reflect_apply]
  have e0 : (-n = 0) ↔ (n = 0) := neg_eq_zero
  have e1 : ∀ k : Idx, (-n = k) ↔ (n = -k) := fun k => neg_eq_iff_eq_neg
  simp only [e0, e1]

private lemma MStar_reflect_InM {α : Occ} (h : InM ρ L kc N α) :
    InM ρ L kc N (MStar_reflect α) := by
  induction h with
  | free =>
    rw [MStar_reflect_single]
    exact InM.free
  | @strictIH α k _ hk h2 ih =>
    rw [MStar_reflect_strictPair]
    refine InM.strictIH ih ?_ ?_
    · rcases hk with hk | hk
      · exact Or.inl (Regions_PI_neg.2 hk)
      · exact Or.inr (Regions_PH_neg.2 hk)
    · rw [MStar_reflect_apply, neg_zero]
      exact h2
  | @strictL α k _ hk hlt h2 ih =>
    rw [MStar_reflect_strictPair]
    refine InM.strictL ih (Regions_PL_neg.2 hk) ?_ ?_
    · have : alphaStar (MStar_reflect α) (-k) = alphaStar α k := by
        simp [alphaStar, MStar_reflect_apply]
      rw [this]
      exact hlt
    · rw [MStar_reflect_apply, neg_zero]
      exact h2
  | @soft α u p₁ p₂ _ hu hs hsum h₁ h₂ k₁ k₂ h0 h1 ih =>
    rw [MStar_reflect_softPair]
    refine InM.soft ih (Regions_PL_neg.2 hu) ?_ ?_ (Regions_PH_neg.2 h₁) (Regions_PH_neg.2 h₂)
      ?_ ?_ ?_ ?_
    · simpa [MStar_reflect_apply] using hs
    · rw [← neg_add, hsum]
    · rw [MStar_norm_mom_neg]
      exact k₁
    · rw [MStar_norm_mom_neg]
      exact k₂
    · simpa [MStar_reflect_apply] using h0
    · simpa [MStar_reflect_apply] using h1

/-- `M` is invariant under `k ↦ -k`. -/
theorem MStar_reflect_iff {α : Occ} :
    InM ρ L kc N (MStar_reflect α) ↔ InM ρ L kc N α := by
  refine ⟨fun h => ?_, MStar_reflect_InM⟩
  have := MStar_reflect_InM h
  rwa [MStar_reflect_reflect] at this

private lemma MStar_alphaStar_reflect (α : Occ) (u : Idx) :
    alphaStar (MStar_reflect α) u = alphaStar α (-u) := by
  simp [alphaStar, MStar_reflect_apply]

private lemma MStar_mem_neg_image {α : Occ} {u : Idx} :
    u ∈ α.support.image Neg.neg ↔ α (-u) ≠ 0 := by
  simp only [Finset.mem_image, Finsupp.mem_support_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa using ha
  · intro h
    exact ⟨-u, h, neg_neg u⟩

/-- `f(α(-·)) = f(α)` for (3.18) [deffal]. -/
theorem MStar_f0_reflect (V w : R3 → ℝ) (α : Occ) :
    f0 V w ρ L (MStar_reflect α) = f0 V w ρ L α := by
  have hA : (MStar_reflect α) 0 = α 0 := by simp [MStar_reflect_apply]
  have hB : (∏ n ∈ (MStar_reflect α).support.filter (· ≠ 0),
      csqrt (lam V w ρ L n) ^ ((MStar_reflect α) n)) =
      ∏ n ∈ α.support.filter (· ≠ 0), csqrt (lam V w ρ L n) ^ (α n) := by
    refine Finset.prod_nbij' Neg.neg Neg.neg ?_ ?_ ?_ ?_ ?_
    · intro n hn
      simpa [MStar_reflect_apply] using hn
    · intro n hn
      simpa [MStar_reflect_apply] using hn
    · intro n _
      exact neg_neg n
    · intro n _
      exact neg_neg n
    · intro n _
      simp [MStar_reflect_apply, Regions_lam_neg]
  have hC : (∏ u ∈ ((MStar_reflect α).support.image Neg.neg).filter
      (fun u => inPL ρ L u ∧ alphaStar (MStar_reflect α) u = (MStar_reflect α) u + 1),
      csqrt (4 * (alphaStar (MStar_reflect α) u : ℝ) * lam V w ρ L u / L ^ 3)) =
      ∏ u ∈ (α.support.image Neg.neg).filter
        (fun u => inPL ρ L u ∧ alphaStar α u = α u + 1),
      csqrt (4 * (alphaStar α u : ℝ) * lam V w ρ L u / L ^ 3) := by
    refine Finset.prod_nbij' Neg.neg Neg.neg ?_ ?_ ?_ ?_ ?_
    · intro u hu
      simp only [Finset.mem_filter, MStar_mem_neg_image, MStar_reflect_apply,
        MStar_alphaStar_reflect] at hu ⊢
      simpa [Regions_PL_neg] using hu
    · intro u hu
      simp only [Finset.mem_filter, MStar_mem_neg_image, MStar_reflect_apply,
        MStar_alphaStar_reflect] at hu ⊢
      simpa [Regions_PL_neg] using hu
    · intro u _
      exact neg_neg u
    · intro u _
      exact neg_neg u
    · intro u _
      simp [MStar_alphaStar_reflect, Regions_lam_neg]
  unfold f0
  rw [hA, hB, hC]

/-- `α ∈ M_u^a` and `𝓐^{u,k} α ∈ M` imply `α(u) = α(-u) + 1` (§5, after Lemma 5.1 [f]). -/
theorem MStar_asym_soft (hρ : 0 < ρ) {u p₁ p₂ : Idx} {α : Occ} (hu : inPL ρ L u)
    (hα : InMuA ρ L kc N u α) (h₁ : inPH ρ L p₁) (h₂ : inPH ρ L p₂)
    (hβ : InM ρ L kc N (softPair u p₁ p₂ α)) : α u = α (-u) + 1 := by
  obtain ⟨hαM, hne⟩ := hα
  obtain ⟨-, h1⟩ := MBasic_soft_le hρ hαM hβ
  obtain ⟨d1, d1'⟩ := MStar_PL_diff hρ hαM hu
  obtain ⟨d2, d2'⟩ := MStar_PL_diff hρ hβ hu
  have hu' := Regions_PL_neg.2 hu
  have hn := MStar_neg_ne_self (Regions_PL_ne_zero hρ hu)
  rw [MStar_softPair_PL hρ h₁ h₂ hu, MStar_softPair_PL hρ h₁ h₂ hu'] at d2 d2'
  simp only [hn, ite_true, ite_false] at d2 d2'
  omega

end MStar

end LHYUpper
