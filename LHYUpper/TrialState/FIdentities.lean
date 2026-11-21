module

public import LHYUpper.TrialState.MStar

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # The trial-state coefficients and the identities of Lemma 5.1

Writes the coefficient function `f` of the trial state (3.18) [deffal] as the product of its
prefactor, the product of `√λ_n^{α(n)}` over the support, and the factor at `u`, and proves the
identities of Lemma 5.1 [f] along strict and soft pair creations: (5.4) [properf1], (5.5)
[properf2], (5.6) [properf3], (5.7) [properf4] and (5.8) [properf5], the latter also in the form of
the paper for `g₀ > 0`. -/

section FIdentities
variable {V w : R3 → ℝ} {ρ L kc : ℝ} {N : ℕ}

/-- The prefactor `√((L³)^{α(0)} / α(0)!)` of (3.18) [deffal]. -/
private def FI_A (L : ℝ) (α : Occ) : ℂ :=
  (Real.sqrt ((L ^ 3) ^ (α 0) / (Nat.factorial (α 0))) : ℂ)

/-- One factor `csqrt(λ_n)^m` of the product over the support in (3.18) [deffal]; the factor at
`n = 0` is `1`. -/
private def FI_g (V w : R3 → ℝ) (ρ L : ℝ) (n : Idx) (m : ℕ) : ℂ :=
  if n ≠ 0 then csqrt (lam V w ρ L n) ^ m else 1

/-- The product `∏_{n ≠ 0} csqrt(λ_n)^{α(n)}` of (3.18) [deffal]. -/
private def FI_P (V w : R3 → ℝ) (ρ L : ℝ) (α : Occ) : ℂ := α.prod (FI_g V w ρ L)

/-- The factor at `u` of the last product of (3.18) [deffal]: the square root if `u ∈ P_L` and
`α*(u) = α(u) + 1`, and `1` otherwise. -/
private def FI_t (V w : R3 → ℝ) (ρ L : ℝ) (α : Occ) (u : Idx) : ℂ :=
  if inPL ρ L u ∧ alphaStar α u = α u + 1 then
    csqrt (4 * (alphaStar α u : ℝ) * lam V w ρ L u / L ^ 3)
  else 1

private lemma FI_neg_ne_self {u : Idx} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

private lemma FI_g_zero (n : Idx) : FI_g V w ρ L n 0 = 1 := by
  simp [FI_g]

private lemma FI_g_add (n : Idx) (a b : ℕ) :
    FI_g V w ρ L n (a + b) = FI_g V w ρ L n a * FI_g V w ρ L n b := by
  unfold FI_g
  split_ifs
  · exact pow_add _ _ _
  · simp

private lemma FI_g_one {n : Idx} (hn : n ≠ 0) :
    FI_g V w ρ L n 1 = csqrt (lam V w ρ L n) := by
  simp [FI_g, hn]

/-- `f0` as the product of its three factors, the last one over any finite set containing the
relevant indices. -/
private lemma FI_f0_eq (α : Occ) (F : Finset Idx) (hF : ∀ u, α (-u) ≠ 0 → u ∈ F) :
    f0 V w ρ L α = FI_A L α * FI_P V w ρ L α * ∏ u ∈ F, FI_t V w ρ L α u := by
  unfold f0 FI_A FI_P
  congr 1
  · congr 1
    unfold Finsupp.prod
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl fun n _ => ?_
    simp [FI_g]
  · rw [Finset.prod_filter]
    refine Finset.prod_subset ?_ ?_
    · intro u hu
      simp only [Finset.mem_image, Finsupp.mem_support_iff] at hu
      obtain ⟨a, ha, rfl⟩ := hu
      exact hF (-a) (by simpa using ha)
    · intro u _ hu
      have : ¬ (inPL ρ L u ∧ alphaStar α u = α u + 1) := by
        rintro ⟨-, h⟩
        apply hu
        simp only [Finset.mem_image, Finsupp.mem_support_iff]
        refine ⟨-u, ?_, neg_neg u⟩
        have : α (-u) ≠ 0 := by
          unfold alphaStar at h
          omega
        simpa using this
      simp [this]

/-- `f0` at two occupation numbers, written over a common finite index set containing a given
index `σ`. -/
private lemma FI_f0_two (α β : Occ) (σ : Idx) :
    ∃ F : Finset Idx, σ ∈ F ∧
      f0 V w ρ L α = FI_A L α * FI_P V w ρ L α * ∏ u ∈ F, FI_t V w ρ L α u ∧
      f0 V w ρ L β = FI_A L β * FI_P V w ρ L β * ∏ u ∈ F, FI_t V w ρ L β u := by
  refine ⟨insert σ ((α.support ∪ β.support).image Neg.neg), Finset.mem_insert_self _ _,
    FI_f0_eq α _ ?_, FI_f0_eq β _ ?_⟩
  · intro u hu
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-u, ?_, neg_neg u⟩)
    exact Finset.mem_union_left _ (by simpa using hu)
  · intro u hu
    refine Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-u, ?_, neg_neg u⟩)
    exact Finset.mem_union_right _ (by simpa using hu)

/-- Changing the factor at one index of a finite product. -/
private lemma FI_prod_modify {F : Finset Idx} {f g : Idx → ℂ} {σ : Idx} (hσ : σ ∈ F) (c : ℂ)
    (h : ∀ u ∈ F, u ≠ σ → g u = f u) (hσ' : g σ = c * f σ) :
    ∏ u ∈ F, g u = c * ∏ u ∈ F, f u := by
  rw [← Finset.mul_prod_erase F g hσ, ← Finset.mul_prod_erase F f hσ, hσ',
    Finset.prod_congr rfl (fun u hu => h u (Finset.mem_of_mem_erase hu)
      (Finset.ne_of_mem_erase hu))]
  ring

private lemma FI_t_not_PL {α : Occ} {u : Idx} (h : ¬ inPL ρ L u) :
    FI_t V w ρ L α u = 1 := by
  simp [FI_t, h]

private lemma FI_t_congr {α β : Occ} {u : Idx} (h1 : α u = β u) (h2 : α (-u) = β (-u)) :
    FI_t V w ρ L α u = FI_t V w ρ L β u := by
  unfold FI_t alphaStar
  rw [h1, h2]

/-- The factor at `u` is `1` when `α(-u) ≤ α(u)`. -/
private lemma FI_t_of_ge {α : Occ} {u : Idx} (h : α (-u) ≤ α u) :
    FI_t V w ρ L α u = 1 := by
  have : ¬ (inPL ρ L u ∧ alphaStar α u = α u + 1) := by
    rintro ⟨-, h'⟩
    unfold alphaStar at h'
    omega
  simp [FI_t, this]

private lemma FI_t_pos {α : Occ} {u : Idx} (h : inPL ρ L u ∧ alphaStar α u = α u + 1) :
    FI_t V w ρ L α u = csqrt (4 * (alphaStar α u : ℝ) * lam V w ρ L u / L ^ 3) := by
  unfold FI_t
  simp [h]

private lemma FI_t_sym {α : Occ} {u : Idx} (h : α u = α (-u)) :
    FI_t V w ρ L α u = 1 :=
  FI_t_of_ge h.symm.le

/-- Value at `n ∈ P_L` of a strict pair creation. -/
private lemma FI_strict_PL (hρ : 0 < ρ) {k : Idx} {α : Occ} {n : Idx} (hn : inPL ρ L n) :
    strictPair k α n = α n + (if n = k then 1 else 0) + (if n = -k then 1 else 0) := by
  rw [MBasic_strictPair_apply]
  simp [Regions_PL_ne_zero hρ hn]

/-- Value at `n ∈ P_L` of a soft pair creation with created momenta in `P_H`. -/
private lemma FI_soft_PL (hρ : 0 < ρ) {u p₁ p₂ : Idx} {α : Occ} {n : Idx}
    (h₁ : inPH ρ L p₁) (h₂ : inPH ρ L p₂) (hn : inPL ρ L n) :
    softPair u p₁ p₂ α n = α n - (if n = u then 1 else 0) := by
  rw [MBasic_softPair_apply]
  have e1 : n ≠ p₁ := fun h => Regions_PL_PH hρ hn (h ▸ h₁)
  have e2 : n ≠ p₂ := fun h => Regions_PL_PH hρ hn (h ▸ h₂)
  simp [Regions_PL_ne_zero hρ hn, e1, e2]

/-- A strict pair creation does not change the values at `±u`, `u ∈ P_L`, `u ≠ ±k`. -/
private lemma FI_strict_far (hρ : 0 < ρ) {k u : Idx} {α : Occ} (hu : inPL ρ L u)
    (h1 : u ≠ k) (h2 : u ≠ -k) :
    strictPair k α u = α u ∧ strictPair k α (-u) = α (-u) := by
  have hu' := Regions_PL_neg.2 hu
  have h3 : -u ≠ k := fun h => h2 (by rw [← h, neg_neg])
  have h4 : -u ≠ -k := fun h => h1 (neg_injective h)
  rw [FI_strict_PL hρ hu, FI_strict_PL hρ hu']
  simp [h1, h2, h3, h4]

/-- A soft pair creation does not change the values at `±u'`, `u' ∈ P_L`, `u' ≠ ±u`. -/
private lemma FI_soft_far (hρ : 0 < ρ) {u u' p₁ p₂ : Idx} {α : Occ} (h₁ : inPH ρ L p₁)
    (h₂ : inPH ρ L p₂) (hu' : inPL ρ L u') (e1 : u' ≠ u) (e2 : u' ≠ -u) :
    softPair u p₁ p₂ α u' = α u' ∧ softPair u p₁ p₂ α (-u') = α (-u') := by
  have hn := Regions_PL_neg.2 hu'
  have e3 : -u' ≠ u := fun h => e2 (by rw [← h, neg_neg])
  rw [FI_soft_PL hρ h₁ h₂ hu', FI_soft_PL hρ h₁ h₂ hn]
  simp [e1, e3]

private lemma FI_strict_pm (hρ : 0 < ρ) {k σ : Idx} {α : Occ} (hk : inPL ρ L k)
    (hσ : σ = k ∨ σ = -k) :
    strictPair k α σ = α σ + 1 ∧ strictPair k α (-σ) = α (-σ) + 1 := by
  have hk0 := Regions_PL_ne_zero hρ hk
  have hn := FI_neg_ne_self hk0
  rcases hσ with rfl | rfl
  · rw [FI_strict_PL hρ hk, FI_strict_PL hρ (Regions_PL_neg.2 hk)]
    simp [hn, hn.symm]
  · rw [FI_strict_PL hρ (Regions_PL_neg.2 hk), neg_neg, FI_strict_PL hρ hk]
    simp [hn, hn.symm]

/-- `P` along a strict pair creation. -/
private lemma FI_P_strict {k : Idx} (hk : k ≠ 0) {α : Occ} (h2 : 2 ≤ α 0) :
    FI_P V w ρ L (strictPair k α) =
      FI_P V w ρ L α * (csqrt (lam V w ρ L k) * csqrt (lam V w ρ L (-k))) := by
  have hα : α = (α - Finsupp.single 0 2) + Finsupp.single 0 2 :=
    (tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (by simpa using h2))).symm
  have hk' : -k ≠ 0 := neg_ne_zero.2 hk
  have e1 : FI_P V w ρ L α = FI_P V w ρ L (α - Finsupp.single 0 2) := by
    conv_lhs => rw [hα]
    unfold FI_P
    rw [Finsupp.prod_add_index' FI_g_zero FI_g_add, Finsupp.prod_single_index (FI_g_zero 0)]
    simp [FI_g]
  have e2 : strictPair k α = (α - Finsupp.single 0 2) + Finsupp.single k 1 +
      Finsupp.single (-k) 1 := rfl
  rw [e1, e2]
  unfold FI_P
  rw [Finsupp.prod_add_index' FI_g_zero FI_g_add, Finsupp.prod_add_index' FI_g_zero FI_g_add,
    Finsupp.prod_single_index (FI_g_zero k), Finsupp.prod_single_index (FI_g_zero (-k)),
    FI_g_one hk, FI_g_one hk', mul_assoc]

/-- `P` along a soft pair creation. -/
private lemma FI_P_soft {u p₁ p₂ : Idx} (hu : u ≠ 0) (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0) {α : Occ}
    (h0 : 1 ≤ α 0) (hu1 : 1 ≤ α u) :
    ∃ Q : ℂ, FI_P V w ρ L α = Q * csqrt (lam V w ρ L u) ∧
      FI_P V w ρ L (softPair u p₁ p₂ α) =
        Q * (csqrt (lam V w ρ L p₁) * csqrt (lam V w ρ L p₂)) := by
  have hα : α = (α - Finsupp.single 0 1 - Finsupp.single u 1) + Finsupp.single u 1 +
      Finsupp.single 0 1 := by
    ext n
    by_cases e1 : n = 0
    · subst e1
      simp [hu.symm]
      omega
    · by_cases e2 : n = u
      · subst e2
        simp [hu]
        omega
      · simp [Ne.symm e1, Ne.symm e2]
  have e2 : softPair u p₁ p₂ α = (α - Finsupp.single 0 1 - Finsupp.single u 1) +
      Finsupp.single p₁ 1 + Finsupp.single p₂ 1 := rfl
  refine ⟨FI_P V w ρ L (α - Finsupp.single 0 1 - Finsupp.single u 1), ?_, ?_⟩
  · conv_lhs => rw [hα]
    unfold FI_P
    rw [Finsupp.prod_add_index' FI_g_zero FI_g_add, Finsupp.prod_add_index' FI_g_zero FI_g_add,
      Finsupp.prod_single_index (FI_g_zero 0), Finsupp.prod_single_index (FI_g_zero u),
      FI_g_one hu]
    simp [FI_g]
  · rw [e2]
    unfold FI_P
    rw [Finsupp.prod_add_index' FI_g_zero FI_g_add, Finsupp.prod_add_index' FI_g_zero FI_g_add,
      Finsupp.prod_single_index (FI_g_zero p₁), Finsupp.prod_single_index (FI_g_zero p₂),
      FI_g_one h₁, FI_g_one h₂, mul_assoc]

/-- The prefactor after a strict pair creation, `α(0) = m + 2` and `β(0) = m`. -/
private lemma FI_A_strict (hL : 0 < L) {α β : Occ} {m : ℕ} (hα : α 0 = m + 2) (hβ : β 0 = m) :
    FI_A L β = ((Real.sqrt ((α 0 : ℝ) / L ^ 3) * Real.sqrt (((α 0 : ℝ) - 1) / L ^ 3) : ℝ) : ℂ) *
      FI_A L α := by
  unfold FI_A
  rw [hα, hβ, ← Complex.ofReal_mul]
  congr 1
  have h1 : (((m + 2 : ℕ) : ℝ) - 1) = (m : ℝ) + 1 := by push_cast; ring
  rw [h1, ← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- The prefactor after a soft pair creation, `α(0) = m + 1` and `β(0) = m`. -/
private lemma FI_A_soft (hL : 0 < L) {α β : Occ} {m : ℕ} (hα : α 0 = m + 1) (hβ : β 0 = m) :
    FI_A L β = ((Real.sqrt ((α 0 : ℝ) / L ^ 3) : ℝ) : ℂ) * FI_A L α := by
  unfold FI_A
  rw [hα, hβ, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

private lemma FI_csqrt_ratio (hL : 0 < L) {a : ℝ} (ha : 0 < a) (x : ℝ) :
    csqrt (4 * (a + 1) * x / L ^ 3) =
      ((Real.sqrt ((a + 1) / a) : ℝ) : ℂ) * csqrt (4 * a * x / L ^ 3) := by
  have : 4 * (a + 1) * x / L ^ 3 = ((a + 1) / a) * (4 * a * x / L ^ 3) := by
    field_simp
  rw [this, Regions_csqrt_mul (by positivity)]

private lemma FI_csqrt_two (hL : 0 < L) {b : ℝ} (hb : 0 ≤ b) (x : ℝ) :
    csqrt (4 * b * x / L ^ 3) = ((2 * Real.sqrt (b / L ^ 3) : ℝ) : ℂ) * csqrt x := by
  have : 4 * b * x / L ^ 3 = (4 * b / L ^ 3) * x := by ring
  rw [this, Regions_csqrt_mul (by positivity)]
  congr 2
  rw [show 4 * b / L ^ 3 = 2 ^ 2 * (b / L ^ 3) by ring, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num)]

/-- The last product of (3.18) after a strict pair creation at `k ∈ P_L` with
`α(-σ) = α(σ) + 1` for one `σ ∈ {k, -k}`. -/
private lemma FI_S_strict_asym (hρ : 0 < ρ) (hL : 0 < L) {k σ : Idx} {α : Occ}
    (hk : inPL ρ L k) (hσ : σ = k ∨ σ = -k) (hσα : α (-σ) = α σ + 1) {F : Finset Idx}
    (hFσ : σ ∈ F) :
    ∏ u ∈ F, FI_t V w ρ L (strictPair k α) u =
      ((Real.sqrt (((α (-σ) : ℝ) + 1) / (α (-σ) : ℝ)) : ℝ) : ℂ) *
        ∏ u ∈ F, FI_t V w ρ L α u := by
  have hσPL : inPL ρ L σ := by
    rcases hσ with rfl | rfl
    · exact hk
    · exact Regions_PL_neg.2 hk
  obtain ⟨hb1, hb2⟩ := FI_strict_pm hρ (α := α) hk hσ
  refine FI_prod_modify hFσ _ ?_ ?_
  · intro u _ hu
    by_cases hP : inPL ρ L u
    · by_cases hu2 : u = -σ
      · subst hu2
        rw [FI_t_of_ge, FI_t_of_ge]
        · rw [neg_neg]
          omega
        · rw [neg_neg, hb1, hb2]
          omega
      · have e1 : u ≠ k ∧ u ≠ -k := by
          rcases hσ with rfl | rfl
          · exact ⟨hu, by simpa using hu2⟩
          · exact ⟨by simpa using hu2, hu⟩
        obtain ⟨f1, f2⟩ := FI_strict_far hρ (α := α) hP e1.1 e1.2
        exact FI_t_congr f1 f2
    · rw [FI_t_not_PL hP, FI_t_not_PL hP]
  · have s1 : alphaStar α σ = α (-σ) := by
      unfold alphaStar
      omega
    have s2 : alphaStar (strictPair k α) σ = α (-σ) + 1 := by
      unfold alphaStar
      omega
    have c1 : inPL ρ L σ ∧ alphaStar α σ = α σ + 1 := ⟨hσPL, by omega⟩
    have c2 : inPL ρ L σ ∧ alphaStar (strictPair k α) σ = strictPair k α σ + 1 :=
      ⟨hσPL, by omega⟩
    have ha : (0 : ℝ) < (α (-σ) : ℝ) := by
      have : 0 < α (-σ) := by omega
      exact_mod_cast this
    rw [FI_t_pos c2, FI_t_pos c1, s1, s2]
    push_cast
    exact FI_csqrt_ratio hL ha _

/-- `f0` before and after a strict pair creation, over a common finite index set containing
`σ`. -/
private lemma FI_strict_decomp (hL : 0 < L) {k : Idx} (hk : k ≠ 0) {α : Occ} (h2 : 2 ≤ α 0)
    (σ : Idx) :
    ∃ F : Finset Idx, σ ∈ F ∧
      f0 V w ρ L α = FI_A L α * FI_P V w ρ L α * ∏ u ∈ F, FI_t V w ρ L α u ∧
      f0 V w ρ L (strictPair k α) =
        ((Real.sqrt ((α 0 : ℝ) / L ^ 3) * Real.sqrt (((α 0 : ℝ) - 1) / L ^ 3) : ℝ) : ℂ) *
          FI_A L α * (FI_P V w ρ L α * (csqrt (lam V w ρ L k) * csqrt (lam V w ρ L (-k)))) *
          ∏ u ∈ F, FI_t V w ρ L (strictPair k α) u := by
  obtain ⟨F, hF, h1, h2'⟩ := FI_f0_two (V := V) (w := w) (ρ := ρ) (L := L) α (strictPair k α) σ
  obtain ⟨m, hm⟩ : ∃ m, α 0 = m + 2 := ⟨α 0 - 2, by omega⟩
  have hβ0 : (strictPair k α) 0 = m := by
    rw [MBasic_strictPair_apply]
    simp [hk.symm, (neg_ne_zero.2 hk).symm, hm]
  refine ⟨F, hF, h1, ?_⟩
  rw [h2', FI_A_strict hL hm hβ0, FI_P_strict hk h2]

/-- `f0` before and after a soft pair creation, over a common finite index set containing `σ`. -/
private lemma FI_soft_decomp (hL : 0 < L) {u p₁ p₂ : Idx} (hu : u ≠ 0) (h₁ : p₁ ≠ 0)
    (h₂ : p₂ ≠ 0) {α : Occ} (h0 : 1 ≤ α 0) (hu1 : 1 ≤ α u) (σ : Idx) :
    ∃ (F : Finset Idx) (Q : ℂ), σ ∈ F ∧
      f0 V w ρ L α = FI_A L α * (Q * csqrt (lam V w ρ L u)) * ∏ x ∈ F, FI_t V w ρ L α x ∧
      f0 V w ρ L (softPair u p₁ p₂ α) =
        ((Real.sqrt ((α 0 : ℝ) / L ^ 3) : ℝ) : ℂ) * FI_A L α *
          (Q * (csqrt (lam V w ρ L p₁) * csqrt (lam V w ρ L p₂))) *
          ∏ x ∈ F, FI_t V w ρ L (softPair u p₁ p₂ α) x := by
  obtain ⟨F, hF, h1, h2'⟩ :=
    FI_f0_two (V := V) (w := w) (ρ := ρ) (L := L) α (softPair u p₁ p₂ α) σ
  obtain ⟨Q, hQ1, hQ2⟩ := FI_P_soft (V := V) (w := w) (ρ := ρ) (L := L) hu h₁ h₂ h0 hu1
  obtain ⟨m, hm⟩ : ∃ m, α 0 = m + 1 := ⟨α 0 - 1, by omega⟩
  have hβ0 : (softPair u p₁ p₂ α) 0 = m := by
    rw [MBasic_softPair_apply]
    simp [hu.symm, h₁.symm, h₂.symm, hm]
  refine ⟨F, Q, hF, ?_, ?_⟩
  · rw [h1, hQ1]
  · rw [h2', FI_A_soft hL hm hβ0, hQ2]

/-- (5.4) [properf1]. -/
theorem Lemma5_1_properf1 (hρ : 0 < ρ) (hL : 0 < L) {k : Idx} {α : Occ}
    (hk : inPI ρ L k ∨ inPH ρ L k) (hα : InM ρ L kc N α) (hβ : InM ρ L kc N (strictPair k α)) :
    f0 V w ρ L (strictPair k α) =
      ((Real.sqrt ((α 0 : ℝ) / L ^ 3) * Real.sqrt (((α 0 : ℝ) - 1) / L ^ 3) *
        lam V w ρ L k : ℝ) : ℂ) * f0 V w ρ L α := by
  have hk0 : k ≠ 0 := by
    rcases hk with h | h
    · exact Regions_PI_ne_zero hρ h
    · exact Regions_PH_ne_zero hρ h
  have h2 := MBasic_strict_le hρ hα hβ
  obtain ⟨F, -, hFα, hFβ⟩ := FI_strict_decomp (V := V) (w := w) (ρ := ρ) hL hk0 h2 0
  have hS : ∏ u ∈ F, FI_t V w ρ L (strictPair k α) u = ∏ u ∈ F, FI_t V w ρ L α u := by
    refine Finset.prod_congr rfl fun u _ => ?_
    by_cases hu : inPL ρ L u
    · have e1 : u ≠ k := by
        rintro rfl
        rcases hk with h | h
        · exact Regions_PL_PI hu h
        · exact Regions_PL_PH hρ hu h
      have e2 : u ≠ -k := by
        intro h
        have hk' : inPL ρ L k := by
          have := Regions_PL_neg.2 hu
          rwa [h, neg_neg] at this
        rcases hk with h | h
        · exact Regions_PL_PI hk' h
        · exact Regions_PL_PH hρ hk' h
      obtain ⟨f1, f2⟩ := FI_strict_far hρ (α := α) hu e1 e2
      exact FI_t_congr f1 f2
    · rw [FI_t_not_PL hu, FI_t_not_PL hu]
  rw [hFβ, hS, Regions_lam_neg, Regions_csqrt_mul_self, hFα]
  push_cast
  ring

/-- (5.5) [properf2]. -/
theorem Lemma5_1_properf2 (hρ : 0 < ρ) (hL : 0 < L) {k : Idx} {α : Occ}
    (hk : inPL ρ L k) (hα : InMuS ρ L kc N k α) (hβ : InM ρ L kc N (strictPair k α)) :
    f0 V w ρ L (strictPair k α) =
      ((Real.sqrt ((α 0 : ℝ) / L ^ 3) * Real.sqrt (((α 0 : ℝ) - 1) / L ^ 3) *
        lam V w ρ L k : ℝ) : ℂ) * f0 V w ρ L α := by
  have hk0 := Regions_PL_ne_zero hρ hk
  obtain ⟨hαM, hsym⟩ := hα
  have h2 := MBasic_strict_le hρ hαM hβ
  obtain ⟨F, -, hFα, hFβ⟩ := FI_strict_decomp (V := V) (w := w) (ρ := ρ) hL hk0 h2 0
  obtain ⟨hb1, hb2⟩ := FI_strict_pm hρ (α := α) hk (Or.inl rfl)
  have hS : ∏ u ∈ F, FI_t V w ρ L (strictPair k α) u = ∏ u ∈ F, FI_t V w ρ L α u := by
    refine Finset.prod_congr rfl fun u _ => ?_
    by_cases hu : inPL ρ L u
    · by_cases e1 : u = k
      · rw [e1, FI_t_sym hsym, FI_t_sym]
        rw [hb1, hb2]
        omega
      · by_cases e2 : u = -k
        · have hsym' : α (-k) = α (- -k) := by rw [neg_neg]; exact hsym.symm
          rw [e2, FI_t_sym hsym', FI_t_sym]
          rw [neg_neg, hb1, hb2]
          omega
        · obtain ⟨f1, f2⟩ := FI_strict_far hρ (α := α) hu e1 e2
          exact FI_t_congr f1 f2
    · rw [FI_t_not_PL hu, FI_t_not_PL hu]
  rw [hFβ, hS, Regions_lam_neg, Regions_csqrt_mul_self, hFα]
  push_cast
  ring

/-- (5.6) [properf3]. -/
theorem Lemma5_1_properf3 (hρ : 0 < ρ) (hL : 0 < L) {k : Idx} {α : Occ}
    (hk : inPL ρ L k) (hα : InMuA ρ L kc N k α) (hβ : InM ρ L kc N (strictPair k α)) :
    f0 V w ρ L (strictPair k α) =
      ((Real.sqrt ((α 0 : ℝ) / L ^ 3) * Real.sqrt (((α 0 : ℝ) - 1) / L ^ 3) *
        Real.sqrt (((alphaStar α k : ℝ) + 1) / (alphaStar α k : ℝ)) *
        lam V w ρ L k : ℝ) : ℂ) * f0 V w ρ L α := by
  have hk0 := Regions_PL_ne_zero hρ hk
  obtain ⟨hαM, hne⟩ := hα
  have h2 := MBasic_strict_le hρ hαM hβ
  have key : ∃ σ, (σ = k ∨ σ = -k) ∧ α (-σ) = α σ + 1 := by
    have s0 := MStar_PL_star hρ hαM hk
    have s1 := MStar_PL_star hρ hαM (Regions_PL_neg.2 hk)
    unfold alphaStar at s0 s1
    simp only [neg_neg] at s1
    by_cases hlt : α k < α (-k)
    · exact ⟨k, Or.inl rfl, by omega⟩
    · exact ⟨-k, Or.inr rfl, by rw [neg_neg]; omega⟩
  obtain ⟨σ, hσ, hσα⟩ := key
  obtain ⟨F, hF, hFα, hFβ⟩ := FI_strict_decomp (V := V) (w := w) (ρ := ρ) hL hk0 h2 σ
  have hS := FI_S_strict_asym (V := V) (w := w) hρ hL hk hσ hσα hF
  have hstar : alphaStar α k = α (-σ) := by
    unfold alphaStar
    rcases hσ with rfl | rfl
    · omega
    · rw [neg_neg] at hσα ⊢
      omega
  rw [hFβ, hS, hFα, hstar, Regions_lam_neg, Regions_csqrt_mul_self]
  push_cast
  ring

/-- (5.7) [properf4], soft pair creation parametrized by its created momenta. -/
theorem Lemma5_1_properf4 (hρ : 0 < ρ) (hL : 0 < L) {u p₁ p₂ : Idx} {α : Occ}
    (hu : inPL ρ L u) (h₁ : inPH ρ L p₁) (h₂ : inPH ρ L p₂) (hs : p₁ + p₂ = u)
    (hα : InMuS ρ L kc N u α) (hβ : InM ρ L kc N (softPair u p₁ p₂ α)) :
    f0 V w ρ L (softPair u p₁ p₂ α) =
      ((2 * Real.sqrt ((α 0 : ℝ) / L ^ 3) * Real.sqrt ((α u : ℝ) / L ^ 3) : ℝ) : ℂ) *
        csqrt (lam V w ρ L p₁) * csqrt (lam V w ρ L p₂) * f0 V w ρ L α := by
  have hu0 := Regions_PL_ne_zero hρ hu
  obtain ⟨-, -, hp1, hp2, -⟩ := Regions_soft_distinct hρ hu h₁ h₂ hs
  obtain ⟨hαM, hsym⟩ := hα
  obtain ⟨h0, hu1⟩ := MBasic_soft_le hρ hαM hβ
  obtain ⟨F, Q, hF, hFα, hFβ⟩ :=
    FI_soft_decomp (V := V) (w := w) (ρ := ρ) hL hu0 hp1 hp2 h0 hu1 u
  have hn := FI_neg_ne_self hu0
  have b1 : softPair u p₁ p₂ α u = α u - 1 := by
    rw [FI_soft_PL hρ h₁ h₂ hu]
    simp
  have b2 : softPair u p₁ p₂ α (-u) = α (-u) := by
    rw [FI_soft_PL hρ h₁ h₂ (Regions_PL_neg.2 hu)]
    simp [hn]
  have hS : ∏ x ∈ F, FI_t V w ρ L (softPair u p₁ p₂ α) x =
      (((2 * Real.sqrt ((α u : ℝ) / L ^ 3) : ℝ) : ℂ) * csqrt (lam V w ρ L u)) *
        ∏ x ∈ F, FI_t V w ρ L α x := by
    refine FI_prod_modify hF _ ?_ ?_
    · intro x _ hx
      by_cases hP : inPL ρ L x
      · by_cases hx2 : x = -u
        · have hsym' : α (-u) = α (- -u) := by rw [neg_neg]; exact hsym.symm
          rw [hx2, FI_t_sym hsym', FI_t_of_ge]
          rw [neg_neg, b1, b2]
          omega
        · obtain ⟨f1, f2⟩ := FI_soft_far hρ (α := α) h₁ h₂ hP hx hx2
          exact FI_t_congr f1 f2
      · rw [FI_t_not_PL hP, FI_t_not_PL hP]
    · have s2 : alphaStar (softPair u p₁ p₂ α) u = α u := by
        unfold alphaStar
        rw [b1, b2]
        omega
      have c2 : inPL ρ L u ∧ alphaStar (softPair u p₁ p₂ α) u = softPair u p₁ p₂ α u + 1 :=
        ⟨hu, by rw [s2, b1]; omega⟩
      rw [FI_t_sym hsym, mul_one, FI_t_pos c2, s2]
      exact FI_csqrt_two hL (Nat.cast_nonneg _) (lam V w ρ L u)
  rw [hFβ, hS, hFα]
  push_cast
  ring

/-- (5.8) [properf5], multiplied out (no division by `λ_u`). -/
theorem Lemma5_1_properf5_mul (hρ : 0 < ρ) (hL : 0 < L) {u p₁ p₂ : Idx} {α : Occ}
    (hu : inPL ρ L u) (h₁ : inPH ρ L p₁) (h₂ : inPH ρ L p₂) (hs : p₁ + p₂ = u)
    (hα : InMuA ρ L kc N u α) (hβ : InM ρ L kc N (softPair u p₁ p₂ α)) :
    ((2 * lam V w ρ L u * Real.sqrt ((α u : ℝ) / L ^ 3) : ℝ) : ℂ) *
        f0 V w ρ L (softPair u p₁ p₂ α) =
      ((Real.sqrt ((α 0 : ℝ) / L ^ 3) : ℝ) : ℂ) *
        csqrt (lam V w ρ L p₁) * csqrt (lam V w ρ L p₂) * f0 V w ρ L α := by
  have hu0 := Regions_PL_ne_zero hρ hu
  obtain ⟨-, -, hp1, hp2, -⟩ := Regions_soft_distinct hρ hu h₁ h₂ hs
  have hasym := MStar_asym_soft hρ hu hα h₁ h₂ hβ
  obtain ⟨hαM, -⟩ := hα
  obtain ⟨h0, hu1⟩ := MBasic_soft_le hρ hαM hβ
  obtain ⟨F, Q, hF, hFα, hFβ⟩ :=
    FI_soft_decomp (V := V) (w := w) (ρ := ρ) hL hu0 hp1 hp2 h0 hu1 (-u)
  have hn := FI_neg_ne_self hu0
  have b1 : softPair u p₁ p₂ α u = α u - 1 := by
    rw [FI_soft_PL hρ h₁ h₂ hu]
    simp
  have b2 : softPair u p₁ p₂ α (-u) = α (-u) := by
    rw [FI_soft_PL hρ h₁ h₂ (Regions_PL_neg.2 hu)]
    simp [hn]
  have hS : ∏ x ∈ F, FI_t V w ρ L α x =
      (((2 * Real.sqrt ((α u : ℝ) / L ^ 3) : ℝ) : ℂ) * csqrt (lam V w ρ L u)) *
        ∏ x ∈ F, FI_t V w ρ L (softPair u p₁ p₂ α) x := by
    refine FI_prod_modify hF _ ?_ ?_
    · intro x _ hx
      by_cases hP : inPL ρ L x
      · by_cases hx2 : x = u
        · have hsym' : softPair u p₁ p₂ α u = softPair u p₁ p₂ α (-u) := by
            rw [b1, b2]
            omega
          rw [hx2, FI_t_of_ge, FI_t_sym hsym']
          omega
        · have hx3 : x ≠ -u := by
            intro h
            exact hx (by rw [h])
          obtain ⟨f1, f2⟩ := FI_soft_far hρ (α := α) h₁ h₂ hP hx2 hx3
          exact FI_t_congr f1.symm f2.symm
      · rw [FI_t_not_PL hP, FI_t_not_PL hP]
    · have hsym' : softPair u p₁ p₂ α (-u) = softPair u p₁ p₂ α (- -u) := by
        rw [neg_neg, b1, b2]
        omega
      have s1 : alphaStar α (-u) = α u := by
        unfold alphaStar
        rw [neg_neg]
        omega
      have c1 : inPL ρ L (-u) ∧ alphaStar α (-u) = α (-u) + 1 :=
        ⟨Regions_PL_neg.2 hu, by rw [s1]; omega⟩
      rw [FI_t_sym hsym', mul_one, FI_t_pos c1, s1, Regions_lam_neg]
      exact FI_csqrt_two hL (Nat.cast_nonneg _) (lam V w ρ L u)
  have hcs : csqrt (lam V w ρ L u) * csqrt (lam V w ρ L u) = ((lam V w ρ L u : ℝ) : ℂ) :=
    Regions_csqrt_mul_self _
  rw [hFβ, hFα, hS]
  push_cast
  rw [← hcs]
  ring

/-- `λ_u < 0` on `P_L` when `g₀ > 0`, (3.15) [lambda]. -/
private lemma FI_lam_neg_PL (hρ : 0 < ρ) (hg : 0 < g0 V w) {u : Idx} (hu : inPL ρ L u) :
    lam V w ρ L u < 0 := by
  have he : 0 < epsP ρ := by
    unfold epsP
    positivity
  have hs : 0 < ρ ^ (1 / 2 : ℝ) := by positivity
  have hm : 0 < ‖mom L u‖ := lt_of_lt_of_le (mul_pos he hs) hu.1
  have hx : 0 < 4 * ρ * g0 V w / ‖mom L u‖ ^ 2 := by positivity
  have h1 : 1 < Real.sqrt (1 + 4 * ρ * g0 V w / ‖mom L u‖ ^ 2) := by
    rw [Real.lt_sqrt (by norm_num)]
    linarith
  unfold lam
  simp only [hu, ↓reduceIte]
  refine div_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) (by linarith)) hρ

/-- (5.8) [properf5], in the form of the paper, for `g₀ > 0`. -/
theorem Lemma5_1_properf5 (hρ : 0 < ρ) (hL : 0 < L) (hg : 0 < g0 V w) {u p₁ p₂ : Idx}
    {α : Occ} (hu : inPL ρ L u) (h₁ : inPH ρ L p₁) (h₂ : inPH ρ L p₂) (hs : p₁ + p₂ = u)
    (hα : InMuA ρ L kc N u α) (hβ : InM ρ L kc N (softPair u p₁ p₂ α)) :
    f0 V w ρ L (softPair u p₁ p₂ α) =
      ((1 / (2 * lam V w ρ L u) * Real.sqrt ((α 0 : ℝ) / L ^ 3) *
        Real.sqrt (L ^ 3 / (α u : ℝ)) : ℝ) : ℂ) *
        csqrt (lam V w ρ L p₁) * csqrt (lam V w ρ L p₂) * f0 V w ρ L α := by
  have hmul := Lemma5_1_properf5_mul (V := V) (w := w) (kc := kc) (N := N) hρ hL hu h₁ h₂ hs hα
    hβ
  have hasym := MStar_asym_soft hρ hu hα h₁ h₂ hβ
  have hlam := FI_lam_neg_PL (V := V) (w := w) (L := L) hρ hg hu
  have hαu : 0 < (α u : ℝ) := by
    have : 0 < α u := by omega
    exact_mod_cast this
  have hsq : 0 < Real.sqrt ((α u : ℝ) / L ^ 3) := Real.sqrt_pos.2 (by positivity)
  have hc : (2 * lam V w ρ L u * Real.sqrt ((α u : ℝ) / L ^ 3) : ℝ) ≠ 0 := by
    have : 2 * lam V w ρ L u < 0 := by linarith
    exact (mul_neg_of_neg_of_pos this hsq).ne
  have hcC : (((2 * lam V w ρ L u * Real.sqrt ((α u : ℝ) / L ^ 3) : ℝ)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 hc
  have hd : (1 / (2 * lam V w ρ L u) * Real.sqrt ((α 0 : ℝ) / L ^ 3) *
        Real.sqrt (L ^ 3 / (α u : ℝ)) : ℝ) =
      Real.sqrt ((α 0 : ℝ) / L ^ 3) /
        (2 * lam V w ρ L u * Real.sqrt ((α u : ℝ) / L ^ 3)) := by
    have : Real.sqrt (L ^ 3 / (α u : ℝ)) = (Real.sqrt ((α u : ℝ) / L ^ 3))⁻¹ := by
      rw [← Real.sqrt_inv, inv_div]
    rw [this]
    have h2 : lam V w ρ L u ≠ 0 := hlam.ne
    field_simp
  rw [hd]
  refine mul_left_cancel₀ hcC ?_
  rw [hmul, Complex.ofReal_div]
  field_simp

/-- The normalization constant `C_N` of (3.18) [deffal]. -/
def CN (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) : ℝ :=
  (Real.sqrt (∑' β, if InM (rhoN N) (LN N) kc N β then
    ‖f0 V w (rhoN N) (LN N) β‖ ^ 2 else 0))⁻¹

/-- `Ψ(α) = C_N f(α)` on `M`, (3.18) [deffal]. -/
theorem FIdentities_trialState (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (α : Occ) :
    trialState V w kc N α =
      if InM (rhoN N) (LN N) kc N α then (CN V w kc N : ℂ) * f0 V w (rhoN N) (LN N) α
      else 0 := by
  unfold trialState CN
  by_cases h : InM (rhoN N) (LN N) kc N α <;> simp [h]

end FIdentities

end LHYUpper
