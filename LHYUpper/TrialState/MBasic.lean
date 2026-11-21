module

public import LHYUpper.TrialState.Regions

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Basic properties of the set `M`

Elementary properties of the set `M` of Definition 3.4 [M]: pointwise values of the strict and soft
pair creations of Definition 3.3, the particle number `α.num = N` and total momentum zero on `M`,
supports in `P_0 ∪ P_L ∪ P_I ∪ P_H` (Definition 3.1 [def1]), the symmetry `α(u) = α(-u)` for `u ∈
P_I` and for `u ∈ P_H` with `|u| > k_c` (§3, after (3.10) [def*]), evenness of the particle number
in `P_{H,c}` (proof of Lemma 8.1 [posscombone0]), and the fact that pair creations between elements
of `M` do not truncate. -/

section MBasic
variable {ρ L kc : ℝ} {N : ℕ}

private lemma MBasic_norm_mom_neg (L : ℝ) (n : Idx) : ‖mom L (-n)‖ = ‖mom L n‖ := by
  have : mom L (-n) = -mom L n := by
    ext i
    simp [mom]
  rw [this, norm_neg]

/-- Pointwise value of the strict pair creation of Definition 3.3 (item 1). -/
theorem MBasic_strictPair_apply (k : Idx) (α : Occ) (n : Idx) :
    strictPair k α n = α n - (if n = 0 then 2 else 0) + (if n = k then 1 else 0) +
      (if n = -k then 1 else 0) := by
  simp [strictPair, Finsupp.single_apply, eq_comm]

/-- Pointwise value of the soft pair creation of Definition 3.3 (item 2). -/
theorem MBasic_softPair_apply (u p₁ p₂ : Idx) (α : Occ) (n : Idx) :
    softPair u p₁ p₂ α n = α n - (if n = 0 then 1 else 0) - (if n = u then 1 else 0) +
      (if n = p₁ then 1 else 0) + (if n = p₂ then 1 else 0) := by
  simp [softPair, Finsupp.single_apply, eq_comm]

/-- Additive functionals of `α` split along a strict pair creation that does not truncate. -/
private lemma MBasic_strict_split {M : Type*} [AddCommMonoid M] (g : Idx → ℕ → M)
    (hz : ∀ n, g n 0 = 0) (ha : ∀ n a b, g n (a + b) = g n a + g n b) (k : Idx) {α : Occ}
    (h : 2 ≤ α 0) :
    α.sum g = (α - Finsupp.single 0 2).sum g + g 0 2 ∧
    (strictPair k α).sum g = (α - Finsupp.single 0 2).sum g + (g k 1 + g (-k) 1) := by
  have hle : Finsupp.single 0 2 ≤ α := Finsupp.single_le_iff.2 h
  constructor
  · conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [Finsupp.sum_add_index' hz ha, Finsupp.sum_single_index (hz 0)]
  · unfold strictPair
    rw [Finsupp.sum_add_index' hz ha, Finsupp.sum_add_index' hz ha,
      Finsupp.sum_single_index (hz k), Finsupp.sum_single_index (hz (-k)), add_assoc]

/-- Additive functionals of `α` split along a soft pair creation that does not truncate. -/
private lemma MBasic_soft_split {M : Type*} [AddCommMonoid M] (g : Idx → ℕ → M)
    (hz : ∀ n, g n 0 = 0) (ha : ∀ n a b, g n (a + b) = g n a + g n b) (u p₁ p₂ : Idx)
    {α : Occ} (hu : u ≠ 0) (h0 : 1 ≤ α 0) (h1 : 1 ≤ α u) :
    α.sum g = (α - Finsupp.single 0 1 - Finsupp.single u 1).sum g + (g 0 1 + g u 1) ∧
    (softPair u p₁ p₂ α).sum g =
      (α - Finsupp.single 0 1 - Finsupp.single u 1).sum g + (g p₁ 1 + g p₂ 1) := by
  have hle : Finsupp.single 0 1 + Finsupp.single u 1 ≤ α := by
    rw [Finsupp.le_def]
    intro n
    by_cases hn0 : n = 0
    · subst hn0
      simpa [Finsupp.single_apply, hu.symm] using h0
    · by_cases hnu : n = u
      · subst hnu
        simpa [Finsupp.single_apply, hn0, Ne.symm hn0] using h1
      · simp [Ne.symm hn0, Ne.symm hnu]
  constructor
  · conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [tsub_tsub, Finsupp.sum_add_index' hz ha, Finsupp.sum_add_index' hz ha,
      Finsupp.sum_single_index (hz 0), Finsupp.sum_single_index (hz u)]
  · unfold softPair
    rw [Finsupp.sum_add_index' hz ha, Finsupp.sum_add_index' hz ha,
      Finsupp.sum_single_index (hz p₁), Finsupp.sum_single_index (hz p₂), add_assoc]

/-- Induction principle for `InM` with the two strict rules treated as one case. -/
private lemma MBasic_rec {P : Occ → Prop} (hfree : P (Finsupp.single 0 N))
    (hstrict : ∀ (k : Idx) (α : Occ), P α → 2 ≤ α 0 →
      (inPL ρ L k ∨ inPI ρ L k ∨ inPH ρ L k) → P (strictPair k α))
    (hsoft : ∀ (u p₁ p₂ : Idx) (α : Occ), P α → inPL ρ L u → p₁ + p₂ = u → inPH ρ L p₁ →
      inPH ρ L p₂ → ‖mom L p₁‖ ≤ kc → ‖mom L p₂‖ ≤ kc → 1 ≤ α 0 → 1 ≤ α u →
      P (softPair u p₁ p₂ α))
    {α : Occ} (h : InM ρ L kc N α) : P α := by
  induction h with
  | free => exact hfree
  | strictIH _ hk h2 ih => exact hstrict _ _ ih h2 (hk.elim (Or.inr ∘ Or.inl) (Or.inr ∘ Or.inr))
  | strictL _ hk _ h2 ih => exact hstrict _ _ ih h2 (Or.inl hk)
  | soft _ hu _ hs h1 h2 hk1 hk2 h0 hu1 ih => exact hsoft _ _ _ _ ih hu hs h1 h2 hk1 hk2 h0 hu1

/-- `Σ_k α(k) = N` on `M` (Definition 3.4 [M] inside `M̃`). -/
theorem MBasic_num (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) : α.num = N := by
  refine MBasic_rec (P := fun α => α.num = N) ?_ ?_ ?_ h
  · simp [Occ.num, Finsupp.sum_single_index]
  · intro k α ih h2 _
    obtain ⟨e1, e2⟩ := MBasic_strict_split (fun _ m => m) (fun _ => rfl) (fun _ _ _ => rfl) k h2
    unfold Occ.num at ih ⊢
    omega
  · intro u p₁ p₂ α ih hu _ _ _ _ _ h0 h1
    obtain ⟨e1, e2⟩ := MBasic_soft_split (fun _ m => m) (fun _ => rfl) (fun _ _ _ => rfl) u p₁ p₂
      (Regions_PL_ne_zero hρ hu) h0 h1
    unfold Occ.num at ih ⊢
    omega

/-- Supports of elements of `M` lie in `P = P_0 ∪ P_L ∪ P_I ∪ P_H` (Definition 3.1 [def1]). -/
theorem MBasic_support {α : Occ} (h : InM ρ L kc N α) (n : Idx) (hn : α n ≠ 0) :
    n = 0 ∨ inPL ρ L n ∨ inPI ρ L n ∨ inPH ρ L n := by
  refine MBasic_rec (P := fun α => ∀ n : Idx, α n ≠ 0 →
    n = 0 ∨ inPL ρ L n ∨ inPI ρ L n ∨ inPH ρ L n) ?_ ?_ ?_ h n hn
  · intro n hn
    left
    by_contra hne
    exact hn (Finsupp.single_eq_of_ne' (Ne.symm hne))
  · intro k α ih _ hk n hn
    rw [MBasic_strictPair_apply] at hn
    by_cases h0 : n = 0
    · exact Or.inl h0
    by_cases hk' : n = k
    · subst hk'
      rcases hk with hk | hk | hk
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr (Or.inl hk))
      · exact Or.inr (Or.inr (Or.inr hk))
    by_cases hk'' : n = -k
    · subst hk''
      rcases hk with hk | hk | hk
      · exact Or.inr (Or.inl (Regions_PL_neg.2 hk))
      · exact Or.inr (Or.inr (Or.inl (Regions_PI_neg.2 hk)))
      · exact Or.inr (Or.inr (Or.inr (Regions_PH_neg.2 hk)))
    · apply ih n
      simpa [h0, hk', hk''] using hn
  · intro u p₁ p₂ α ih _ _ h₁ h₂ _ _ _ _ n hn
    rw [MBasic_softPair_apply] at hn
    by_cases h1 : n = p₁
    · subst h1
      exact Or.inr (Or.inr (Or.inr h₁))
    by_cases h2 : n = p₂
    · subst h2
      exact Or.inr (Or.inr (Or.inr h₂))
    · apply ih n
      intro h0
      apply hn
      simp [h0, h1, h2]

/-- Total momentum zero on `M`. -/
theorem MBasic_momentum (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) :
    α.sum (fun n m => m • n) = 0 := by
  refine MBasic_rec (P := fun α => α.sum (fun n m => m • n) = 0) ?_ ?_ ?_ h
  · simp [Finsupp.sum_single_index]
  · intro k α ih h2 _
    obtain ⟨e1, e2⟩ := MBasic_strict_split (fun n m => m • n) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _) k h2
    rw [e2]
    rw [e1] at ih
    simpa using ih
  · intro u p₁ p₂ α ih hu hs _ _ _ _ h0 h1
    obtain ⟨e1, e2⟩ := MBasic_soft_split (fun n m => m • n) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _) u p₁ p₂ (Regions_PL_ne_zero hρ hu) h0 h1
    rw [e2]
    rw [e1] at ih
    simp only [one_smul, smul_zero, zero_add] at ih ⊢
    rw [hs]
    exact ih

/-- The momenta at which every element of `M` is symmetric: `P_I`, and `P_H` above `k_c`. -/
private def MBasic_Sym (ρ L kc : ℝ) (w : Idx) : Prop :=
  inPI ρ L w ∨ (inPH ρ L w ∧ kc < ‖mom L w‖)

private lemma MBasic_Sym_neg {w : Idx} (h : MBasic_Sym ρ L kc w) : MBasic_Sym ρ L kc (-w) := by
  unfold MBasic_Sym at h ⊢
  rw [Regions_PI_neg, Regions_PH_neg, MBasic_norm_mom_neg]
  exact h

private lemma MBasic_Sym_ne_zero (hρ : 0 < ρ) {w : Idx} (h : MBasic_Sym ρ L kc w) : w ≠ 0 :=
  h.elim (Regions_PI_ne_zero hρ) fun h => Regions_PH_ne_zero hρ h.1

private lemma MBasic_Sym_ne_PL (hρ : 0 < ρ) {w q : Idx} (h : MBasic_Sym ρ L kc w)
    (hq : inPL ρ L q) : w ≠ q := by
  rintro rfl
  rcases h with h | h
  · exact Regions_PL_PI hq h
  · exact Regions_PL_PH hρ hq h.1

private lemma MBasic_Sym_ne_PH {w q : Idx} (h : MBasic_Sym ρ L kc w) (hq : inPH ρ L q)
    (hk : ‖mom L q‖ ≤ kc) : w ≠ q := by
  rintro rfl
  rcases h with h | h
  · exact Regions_PI_PH h hq
  · exact absurd hk (not_le.2 h.2)

private lemma MBasic_symm {α : Occ} (hρ : 0 < ρ) (h : InM ρ L kc N α) {u : Idx}
    (hu : MBasic_Sym ρ L kc u) : α u = α (-u) := by
  refine MBasic_rec (P := fun α => ∀ u : Idx, MBasic_Sym ρ L kc u → α u = α (-u)) ?_ ?_ ?_ h u hu
  · intro u hu
    have h1 := MBasic_Sym_ne_zero hρ hu
    have h2 := MBasic_Sym_ne_zero hρ (MBasic_Sym_neg hu)
    simp [Ne.symm h1, Ne.symm h2]
  · intro k α ih _ _ u hu
    have h1 := MBasic_Sym_ne_zero hρ hu
    have h2 := MBasic_Sym_ne_zero hρ (MBasic_Sym_neg hu)
    have e1 : (if u = k then 1 else 0 : ℕ) = if -u = -k then 1 else 0 := by
      simp only [neg_inj]
    have e2 : (if u = -k then 1 else 0 : ℕ) = if -u = k then 1 else 0 := by
      simp only [neg_eq_iff_eq_neg]
    rw [MBasic_strictPair_apply, MBasic_strictPair_apply, ih u hu, e1, e2]
    simp only [h1, h2, ite_false]
    ring
  · intro u₀ p₁ p₂ α ih hu₀ _ h₁ h₂ k₁ k₂ _ _ u hu
    have h1 := MBasic_Sym_ne_zero hρ hu
    have h2 := MBasic_Sym_ne_zero hρ (MBasic_Sym_neg hu)
    have hn := MBasic_Sym_neg hu
    rw [MBasic_softPair_apply, MBasic_softPair_apply, ih u hu]
    simp [h1, h2, MBasic_Sym_ne_PL hρ hu hu₀, MBasic_Sym_ne_PL hρ hn hu₀,
      MBasic_Sym_ne_PH hu h₁ k₁, MBasic_Sym_ne_PH hu h₂ k₂,
      MBasic_Sym_ne_PH hn h₁ k₁, MBasic_Sym_ne_PH hn h₂ k₂]

/-- `α(u) = α(-u)` for `u ∈ P_I` (§3, after (3.10) [def*]). -/
theorem MBasic_PI_symm (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) {u : Idx}
    (hu : inPI ρ L u) : α u = α (-u) := by
  exact MBasic_symm hρ h (Or.inl hu)

/-- `α(u) = α(-u)` for `u ∈ P_H` with `|u| > k_c`. -/
theorem MBasic_PH_far_symm (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) {u : Idx}
    (hu : inPH ρ L u) (hk : kc < ‖mom L u‖) : α u = α (-u) := by
  exact MBasic_symm hρ h (Or.inr ⟨hu, hk⟩)

private lemma MBasic_PHc_neg (ρ L kc : ℝ) (n : Idx) :
    inPHc ρ L kc (-n) ↔ inPHc ρ L kc n := by
  unfold inPHc
  rw [Regions_PH_neg, MBasic_norm_mom_neg]

/-- The number of particles in `P_{H,c}` is even (proof of Lemma 8.1 [posscombone0]). -/
theorem MBasic_PHc_even (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α) :
    Even (α.sum fun n m => if inPHc ρ L kc n then m else 0) := by
  have hz : ∀ n : Idx, (fun (n : Idx) (m : ℕ) => if inPHc ρ L kc n then m else 0) n 0 = 0 := by
    intro n
    by_cases hn : inPHc ρ L kc n <;> simp [hn]
  have ha : ∀ (n : Idx) (a b : ℕ),
      (fun (n : Idx) (m : ℕ) => if inPHc ρ L kc n then m else 0) n (a + b) =
        (fun (n : Idx) (m : ℕ) => if inPHc ρ L kc n then m else 0) n a +
          (fun (n : Idx) (m : ℕ) => if inPHc ρ L kc n then m else 0) n b := by
    intro n a b
    by_cases hn : inPHc ρ L kc n <;> simp [hn]
  have h0 : ¬ inPHc ρ L kc 0 := fun h0 => Regions_PH_ne_zero hρ h0.1 rfl
  refine MBasic_rec (P := fun α => Even (α.sum fun n m => if inPHc ρ L kc n then m else 0))
    ?_ ?_ ?_ h
  · simp [Finsupp.sum_single_index, h0]
  · intro k α ih h2 _
    obtain ⟨e1, e2⟩ := MBasic_strict_split
      (fun (n : Idx) (m : ℕ) => if inPHc ρ L kc n then m else 0) hz ha k h2
    rw [e2]
    rw [e1] at ih
    simp only [h0, ite_false, add_zero] at ih
    have hk : (if inPHc ρ L kc (-k) then 1 else 0) = (if inPHc ρ L kc k then 1 else 0) := by
      simp only [MBasic_PHc_neg]
    simp only [hk]
    exact ih.add ⟨_, rfl⟩
  · intro u p₁ p₂ α ih hu _ h₁ h₂ k₁ k₂ h0' h1
    obtain ⟨e1, e2⟩ := MBasic_soft_split
      (fun (n : Idx) (m : ℕ) => if inPHc ρ L kc n then m else 0) hz ha u p₁ p₂
      (Regions_PL_ne_zero hρ hu) h0' h1
    rw [e2]
    rw [e1] at ih
    have hu' : ¬ inPHc ρ L kc u := fun h' => Regions_PL_PH hρ hu h'.1
    simp only [h0, hu', ite_false, add_zero] at ih
    simp only [inPHc, h₁, h₂, k₁, k₂, and_self, ite_true]
    exact ih.add ⟨1, rfl⟩

private lemma MBasic_num_add (a b : Occ) : (a + b).num = a.num + b.num :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private lemma MBasic_num_single (i : Idx) (m : ℕ) : Occ.num (Finsupp.single i m) = m := by
  simp [Occ.num, Finsupp.sum_single_index]

/-- Particle number of a strict pair creation, including the truncation at `α(0) < 2`. -/
private lemma MBasic_strict_num (k : Idx) (α : Occ) :
    (strictPair k α).num + min (α 0) 2 = α.num + 2 := by
  have e : α = (α - Finsupp.single 0 2) + Finsupp.single 0 (min (α 0) 2) := by
    ext n
    by_cases hn : n = 0
    · subst hn
      simp
    · simp [Ne.symm hn]
  have e3 : α.num = (α - Finsupp.single 0 2).num + min (α 0) 2 := by
    conv_lhs => rw [e]
    rw [MBasic_num_add, MBasic_num_single]
  have e4 : (strictPair k α).num = (α - Finsupp.single 0 2).num + 2 := by
    unfold strictPair
    rw [MBasic_num_add, MBasic_num_add, MBasic_num_single, MBasic_num_single]
  omega

/-- Particle number of a soft pair creation, including the truncation at `α(0) < 1` or
`α(u) < 1`, for `u ≠ 0`. -/
private lemma MBasic_soft_num {u : Idx} (p₁ p₂ : Idx) (α : Occ) (hu : u ≠ 0) :
    (softPair u p₁ p₂ α).num + min (α 0) 1 + min (α u) 1 = α.num + 2 := by
  have e : α = (α - Finsupp.single 0 1 - Finsupp.single u 1) + Finsupp.single 0 (min (α 0) 1) +
      Finsupp.single u (min (α u) 1) := by
    ext n
    by_cases hn : n = 0
    · subst hn
      simp [hu.symm]
    · by_cases hnu : n = u
      · subst hnu
        simp [hn]
      · simp [Ne.symm hn, Ne.symm hnu]
  have e3 : α.num = (α - Finsupp.single 0 1 - Finsupp.single u 1).num + min (α 0) 1 +
      min (α u) 1 := by
    conv_lhs => rw [e]
    rw [MBasic_num_add, MBasic_num_add, MBasic_num_single, MBasic_num_single]
  have e4 : (softPair u p₁ p₂ α).num = (α - Finsupp.single 0 1 - Finsupp.single u 1).num + 2 := by
    unfold softPair
    rw [MBasic_num_add, MBasic_num_add, MBasic_num_single, MBasic_num_single]
  omega

/-- Particle number of a soft pair creation with `u = 0`. -/
private lemma MBasic_soft_num_zero (p₁ p₂ : Idx) (α : Occ) :
    (softPair 0 p₁ p₂ α).num + min (α 0) 2 = α.num + 2 := by
  have e : α = (α - Finsupp.single 0 1 - Finsupp.single 0 1) + Finsupp.single 0 (min (α 0) 2) := by
    ext n
    by_cases hn : n = 0
    · subst hn
      simp
      omega
    · simp [Ne.symm hn]
  have e3 : α.num = (α - Finsupp.single 0 1 - Finsupp.single 0 1).num + min (α 0) 2 := by
    conv_lhs => rw [e]
    rw [MBasic_num_add, MBasic_num_single]
  have e4 : (softPair 0 p₁ p₂ α).num =
      (α - Finsupp.single 0 1 - Finsupp.single 0 1).num + 2 := by
    unfold softPair
    rw [MBasic_num_add, MBasic_num_add, MBasic_num_single, MBasic_num_single]
  omega

/-- A strict pair creation between two elements of `M` does not truncate. -/
theorem MBasic_strict_le (hρ : 0 < ρ) {α : Occ} {k : Idx} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N (strictPair k α)) : 2 ≤ α 0 := by
  have h1 := MBasic_num hρ hα
  have h2 := MBasic_num hρ hβ
  have h3 := MBasic_strict_num k α
  omega

/-- A soft pair creation between two elements of `M` does not truncate. -/
theorem MBasic_soft_le (hρ : 0 < ρ) {α : Occ} {u p₁ p₂ : Idx} (hα : InM ρ L kc N α)
    (hβ : InM ρ L kc N (softPair u p₁ p₂ α)) : 1 ≤ α 0 ∧ 1 ≤ α u := by
  have h1 := MBasic_num hρ hα
  have h2 := MBasic_num hρ hβ
  by_cases hu : u = 0
  · subst hu
    have h3 := MBasic_soft_num_zero p₁ p₂ α
    constructor <;> omega
  · have h3 := MBasic_soft_num p₁ p₂ α hu
    constructor <;> omega

end MBasic

end LHYUpper
