module

public import LHYUpper.Fock.DecompDefs
public import LHYUpper.Fock.A4
public import LHYUpper.Scattering.FourierBasic

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Decomposition of the interaction energy into five parts

Proves that the five index sets of §4 ((4.3)–(4.7)) partition the interaction indices
(`existsUnique_part`), that the sum of the five part terms is the interaction sum, that each part
has a real sum (via the involution `(p, q, u, α) ↦ (p - u, q + u, -u, T(α))`), and that the
interaction summands are absolutely summable for a normalized `N`-particle state. The result
`hasEnergy_iff` is the decomposition of §4 of `⟨H⟩_Ψ = E` into the kinetic sum and the five parts. -/

namespace Decomp

private theorem decomp_zeros_ne_one_of_inS1 {p q u : Idx} (h : InS1 p q u) : zeros p q u ≠ 1 := by
  rcases h with rfl | rfl
  · simp only [zeros, sub_zero, add_zero]
    split_ifs <;> omega
  · simp only [zeros, sub_sub_cancel, add_sub_cancel]
    split_ifs <;> omega

private theorem decomp_two_le_zeros_of_S2 {p q u : Idx} (h : Part.S2.mem p q u) :
    2 ≤ zeros p q u := by
  obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := h
  · simp only [zeros, sub_self, neg_add_cancel, ite_true]
    split_ifs <;> omega
  · simp only [zeros, ite_true]
    split_ifs <;> omega

private theorem decomp_exists_part (p q u : Idx) : ∃ j : Part, j.mem p q u := by
  by_cases h1 : InS1 p q u
  · exact ⟨.S1, h1⟩
  by_cases h2 : Part.S2.mem p q u
  · exact ⟨.S2, h2⟩
  have hz : zeros p q u ≤ 1 := by
    simp only [InS1, not_or] at h1
    obtain ⟨hu0, hupq⟩ := h1
    have hpq : ¬(p = 0 ∧ q = 0) := fun h => h2 ⟨hu0, Or.inr h⟩
    have hrs : ¬(p - u = 0 ∧ q + u = 0) := fun ⟨hr, hs⟩ =>
      h2 ⟨hu0, Or.inl ⟨sub_eq_zero.mp hr, eq_neg_of_add_eq_zero_left hs⟩⟩
    have hpr : ¬(p = 0 ∧ p - u = 0) := fun ⟨hp, hr⟩ => hu0 (by rw [← sub_eq_zero.mp hr, hp])
    have hps : ¬(p = 0 ∧ q + u = 0) := fun ⟨hp, hs⟩ =>
      hupq (by rw [hp, eq_neg_of_add_eq_zero_right hs]; abel)
    have hqr : ¬(q = 0 ∧ p - u = 0) := fun ⟨hq, hr⟩ =>
      hupq (by rw [hq, sub_zero, sub_eq_zero.mp hr])
    have hqs : ¬(q = 0 ∧ q + u = 0) := fun ⟨hq, hs⟩ => hu0 (by rw [hq, zero_add] at hs; exact hs)
    simp only [zeros]
    split_ifs <;> first | omega | (exfalso; tauto)
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hz with hz | hz
  · by_cases hpq : p + q = 0
    · exact ⟨.S3, hz, hpq, h1⟩
    · exact ⟨.A2, hz, hpq, h1⟩
  · exact ⟨.A1, hz⟩

private theorem decomp_part_unique {p q u : Idx} {j k : Part} (hj : j.mem p q u)
    (hk : k.mem p q u) : j = k := by
  have hS1S2 : Part.S1.mem p q u → ¬ Part.S2.mem p q u := by
    rintro (rfl | h) ⟨hu, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hu rfl
    · exact hu rfl
    · refine hu ?_
      have h' : p + p = p := by rw [← sub_neg_eq_add]; exact h.symm
      simpa using h'
    · exact hu (by simpa using h)
  have hS1 := @decomp_zeros_ne_one_of_inS1 p q u
  have hS2 := @decomp_two_le_zeros_of_S2 p q u
  cases j <;> cases k <;> simp only [Part.mem] at hj hk <;> first
    | rfl
    | (exfalso; exact hS1S2 hj hk)
    | (exfalso; exact hS1S2 hk hj)
    | (exfalso; exact hS1 hj hk)
    | (exfalso; exact hS1 hk hj)
    | (exfalso; have := hS2 hj; omega)
    | (exfalso; have := hS2 hk; omega)
    | (exfalso; tauto)
    | omega

theorem existsUnique_part (p q u : Idx) : ∃! j : Part, j.mem p q u := by
  obtain ⟨j, hj⟩ := decomp_exists_part p q u
  exact ⟨j, hj, fun k hk => decomp_part_unique hk hj⟩

theorem sum_partTerm (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) :
    ∑ j : Part, partTerm j L V Ψ i = intTerm L V Ψ i := by
  obtain ⟨j, hj, hu⟩ := existsUnique_part i.1 i.2.1 i.2.2.1
  rw [Finset.sum_eq_single j]
  · simp [partTerm, hj]
  · intro k _ hk
    simp only [partTerm]
    rw [ite_eq_right_iff.mpr fun h => absurd (hu k h) hk]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- The involution `(p, q, u, α) ↦ (p - u, q + u, -u, T(α))` of the interaction index set, which
pairs each term of (2.1) [ham] with the term of its adjoint. -/
private def decompInv (i : Idx × Idx × Idx × Occ) : Idx × Idx × Idx × Occ :=
  (i.1 - i.2.2.1, i.2.1 + i.2.2.1, -i.2.2.1,
    (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2)

/-- Coefficient of `a4` at the index `i`. -/
private def decompCoef (i : Idx × Idx × Idx × Occ) : ℝ :=
  (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).1

private theorem decomp_a4_inv (i : Idx × Idx × Idx × Occ) (h : decompCoef i ≠ 0) :
    a4 (decompInv i).1 (decompInv i).2.1 ((decompInv i).1 - (decompInv i).2.2.1)
      ((decompInv i).2.1 + (decompInv i).2.2.1) (decompInv i).2.2.2 = (decompCoef i, i.2.2.2) := by
  obtain ⟨p, q, u, α⟩ := i
  simp only [decompInv, decompCoef] at h ⊢
  rw [sub_neg_eq_add, sub_add_cancel, add_neg_cancel_right, a4_comm]
  exact a4_adjoint p q (p - u) (q + u) α h

private theorem decomp_coef_inv (i : Idx × Idx × Idx × Occ) (h : decompCoef i ≠ 0) :
    decompCoef (decompInv i) = decompCoef i := by
  have := decomp_a4_inv i h
  simp only [decompCoef]
  rw [this]
  rfl

private theorem decomp_inv_inv (i : Idx × Idx × Idx × Occ) (h : decompCoef i ≠ 0) :
    decompInv (decompInv i) = i := by
  have h4 := decomp_a4_inv i h
  obtain ⟨p, q, u, α⟩ := i
  simp only [decompInv] at h4 ⊢
  rw [h4]
  simp only [sub_neg_eq_add, sub_add_cancel, add_neg_cancel_right, neg_neg]

private theorem decomp_ft_conj (V : R3 → ℝ) (x : R3) : conj (ft V x) = ft V (-x) := by
  unfold ft
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I,
    inner_neg_left]
  push_cast
  ring_nf

private theorem decomp_mom_neg (L : ℝ) (u : Idx) : mom L (-u) = -mom L u := by
  ext k
  simp [mom]

private theorem decomp_intTerm_inv (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ)
    (h : decompCoef i ≠ 0) : intTerm L V Ψ (decompInv i) = conj (intTerm L V Ψ i) := by
  have h4 := decomp_a4_inv i h
  obtain ⟨p, q, u, α⟩ := i
  simp only [intTerm] at h4 ⊢
  rw [h4]
  simp only [decompInv, decompCoef, map_mul, Complex.conj_ofReal,
    Complex.conj_conj, decomp_ft_conj, decomp_mom_neg]
  ring

private theorem decomp_mem_inv (j : Part) (p q u : Idx) :
    j.mem (p - u) (q + u) (-u) ↔ j.mem p q u := by
  have hz : zeros (p - u) (q + u) (-u) = zeros p q u := by
    simp only [zeros, sub_neg_eq_add, sub_add_cancel, add_neg_cancel_right]
    omega
  have hS1 : InS1 (p - u) (q + u) (-u) ↔ InS1 p q u := by
    simp only [InS1, neg_eq_zero]
    refine or_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · linear_combination h
    · linear_combination h
  have hpq : p - u + (q + u) = p + q := by abel
  cases j <;> simp only [Part.mem, hz, hS1, hpq]
  simp only [ne_eq, neg_eq_zero]
  refine and_congr Iff.rfl ⟨?_, ?_⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right
      constructor
      · linear_combination h1
      · linear_combination h2
    · left
      constructor
      · linear_combination h1
      · linear_combination h2
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right
      constructor
      · linear_combination h1
      · linear_combination h2
    · left
      constructor
      · linear_combination h1
      · linear_combination h2

private theorem decomp_partTerm_inv (j : Part) (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ)
    (i : Idx × Idx × Idx × Occ) (h : decompCoef i ≠ 0) :
    partTerm j L V Ψ (decompInv i) = conj (partTerm j L V Ψ i) := by
  obtain ⟨p, q, u, α⟩ := i
  have hm := decomp_mem_inv j p q u
  have hi := decomp_intTerm_inv L V Ψ (p, q, u, α) h
  simp only [partTerm, decompInv] at hm hi ⊢
  by_cases hj : j.mem p q u
  · have hj' := hm.mpr hj
    simp [hj, hj', hi]
  · have hj' : ¬ j.mem (p - u) (q + u) (-u) := fun h => hj (hm.mp h)
    simp [hj, hj']

private theorem decomp_coef_ne_zero (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ)
    {i : Idx × Idx × Idx × Occ} (h : intTerm L V Ψ i ≠ 0) : decompCoef i ≠ 0 := by
  intro h0
  apply h
  simp only [intTerm]
  simp only [decompCoef] at h0
  rw [h0]
  simp

private theorem decomp_partTerm_ne_zero {j : Part} {L : ℝ} {V : R3 → ℝ} {Ψ : Occ → ℂ}
    {i : Idx × Idx × Idx × Occ} (h : partTerm j L V Ψ i ≠ 0) : intTerm L V Ψ i ≠ 0 := by
  intro h0
  apply h
  simp [partTerm, h0]

/-- Each part has a real sum. -/
theorem im_eq_zero_of_hasSum (j : Part) (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (I : ℂ)
    (h : HasSum (partTerm j L V Ψ) I) : I.im = 0 := by
  set f := partTerm j L V Ψ with hf
  have hc : ∀ x, f x ≠ 0 → decompCoef x ≠ 0 := fun x hx =>
    decomp_coef_ne_zero L V Ψ (decomp_partTerm_ne_zero hx)
  have hconj : HasSum (fun x => conj (f x)) (conj I) := Complex.hasSum_conj'.mpr h
  have hsupp : ∀ x : Function.support (fun x => conj (f x)), f x.1 ≠ 0 := fun x hx =>
    x.2 (by simp [hx])
  have key : HasSum f I ↔ HasSum (fun x => conj (f x)) I := by
    refine hasSum_iff_hasSum_of_ne_zero_bij (fun x => decompInv x.1) ?_ ?_ ?_
    · intro x y hxy
      apply Subtype.ext
      have := congrArg decompInv hxy
      simp only at this
      rwa [decomp_inv_inv _ (hc _ (hsupp x)), decomp_inv_inv _ (hc _ (hsupp y))] at this
    · intro y hy
      have hy' : f y ≠ 0 := hy
      refine ⟨⟨decompInv y, ?_⟩, decomp_inv_inv y (hc y hy')⟩
      simp only [Function.mem_support, hf, decomp_partTerm_inv j L V Ψ y (hc y hy'),
        Complex.conj_conj]
      exact hy'
    · intro x
      exact decomp_partTerm_inv j L V Ψ x.1 (hc _ (hsupp x))
  have h2 := key.mp h
  have := h2.unique hconj
  exact Complex.conj_eq_iff_im.mp this.symm

private theorem decomp_card_support_le (α : Occ) : α.support.card ≤ α.num := by
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun n hn => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hn)

private theorem decomp_mem_support_of_coef {i : Idx × Idx × Idx × Occ} (h : decompCoef i ≠ 0) :
    (i.1 - i.2.2.1, i.2.1 + i.2.2.1) ∈ i.2.2.2.support ×ˢ i.2.2.2.support := by
  obtain ⟨β, hβ⟩ := a4_exists_add _ _ _ _ _ h
  rw [Finset.mem_product, Finsupp.mem_support_iff, Finsupp.mem_support_iff, hβ]
  simp [Finsupp.add_apply]

private theorem decomp_norm_ft_neg (L : ℝ) (V : R3 → ℝ) (u : Idx) :
    ‖ft V (mom L (-u))‖ = ‖ft V (mom L u)‖ := by
  rw [decomp_mom_neg, ← decomp_ft_conj, Complex.norm_conj]

/-- Summand `|V_u| |Ψ(α)|²` on the indices with a nonzero coefficient. -/
private def decompPhi (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) : ℝ :=
  if decompCoef i ≠ 0 then ‖ft V (mom L i.2.2.1)‖ * ‖Ψ i.2.2.2‖ ^ 2 else 0

/-- Summand `|V_u| |Ψ(T(α))|²` on the indices with a nonzero coefficient. -/
private def decompPsi (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) : ℝ :=
  if decompCoef i ≠ 0 then ‖ft V (mom L i.2.2.1)‖ * ‖Ψ (decompInv i).2.2.2‖ ^ 2 else 0

private theorem decomp_phi_nonneg (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) :
    0 ≤ decompPhi L V Ψ i := by
  unfold decompPhi
  split_ifs <;> positivity

private theorem decomp_psi_nonneg (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) :
    0 ≤ decompPsi L V Ψ i := by
  unfold decompPsi
  split_ifs <;> positivity

/-- The change of variables `(p, q, u, α) ↦ (u, α, p - u, q + u)`. -/
private def decompEquiv : Idx × Idx × Idx × Occ ≃ Idx × (Occ × (Idx × Idx)) where
  toFun i := (i.2.2.1, i.2.2.2, i.1 - i.2.2.1, i.2.1 + i.2.2.1)
  invFun x := (x.2.2.1 + x.1, x.2.2.2 - x.1, x.1, x.2.1)
  left_inv i := by
    obtain ⟨p, q, u, α⟩ := i
    simp
  right_inv x := by
    obtain ⟨u, α, r, s⟩ := x
    simp

private theorem decomp_phi_summable (L : ℝ) (V : R3 → ℝ) (N : ℕ) (Ψ : Occ → ℂ)
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    Summable (decompPhi L V Ψ) := by
  set G : Occ × (Idx × Idx) → ℝ := fun x =>
    if x.2 ∈ x.1.support ×ˢ x.1.support then ‖Ψ x.1‖ ^ 2 else 0 with hG
  have hG0 : 0 ≤ G := fun x => by
    simp only [hG, Pi.zero_apply]
    split_ifs <;> positivity
  have hGsum : Summable G := by
    refine (summable_prod_of_nonneg hG0).mpr ⟨fun α => ?_, ?_⟩
    · exact summable_of_ne_finset_zero (s := α.support ×ˢ α.support) fun b hb => by
        simp only [hG]; exact ite_eq_right hb
    · refine Summable.of_nonneg_of_le (fun α => tsum_nonneg fun _ => hG0 _)
        (fun α => ?_) (hΨ.1.summable.mul_left ((N : ℝ) ^ 2))
      rw [tsum_eq_sum (s := α.support ×ˢ α.support) fun b hb => by
        simp only [hG]; exact ite_eq_right hb]
      rw [Finset.sum_congr rfl fun b hb => (ite_eq_left_iff.mpr fun h => absurd hb h :
        G (α, b) = ‖Ψ α‖ ^ 2)]
      simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
      by_cases hα : Ψ α = 0
      · simp [hα]
      · have hc := decomp_card_support_le α
        rw [hΨ.2 α hα] at hc
        have hc' : ((α.support.card * α.support.card : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
          rw [sq]; exact_mod_cast Nat.mul_le_mul hc hc
        exact mul_le_mul_of_nonneg_right hc' (by positivity)
  have hprod := Summable.mul_of_nonneg hV hGsum (fun _ => norm_nonneg _) hG0
  have hcomp := (decompEquiv.summable_iff
    (f := fun x : Idx × (Occ × (Idx × Idx)) => ‖ft V (mom L x.1)‖ * G x.2)).mpr hprod
  refine Summable.of_nonneg_of_le (decomp_phi_nonneg L V Ψ) (fun i => ?_) hcomp
  simp only [decompPhi, Function.comp, decompEquiv, Equiv.coe_fn_mk, hG]
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (decomp_mem_support_of_coef h1) h2
  all_goals positivity

private theorem decomp_psi_summable (L : ℝ) (V : R3 → ℝ) (N : ℕ) (Ψ : Occ → ℂ)
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    Summable (decompPsi L V Ψ) := by
  set S : Set (Idx × Idx × Idx × Occ) := {i | decompCoef i ≠ 0}
  have hinj : Function.Injective (fun x : S => decompInv x.1) := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg decompInv hxy
    simp only at this
    rwa [decomp_inv_inv _ x.2, decomp_inv_inv _ y.2] at this
  have h1 := (decomp_phi_summable L V N Ψ hV hΨ).comp_injective hinj
  have h2 : (decompPhi L V Ψ ∘ fun x : S => decompInv x.1) = decompPsi L V Ψ ∘ Subtype.val := by
    funext x
    have hx : decompCoef x.1 ≠ 0 := x.2
    simp only [Function.comp, decompPhi, decompPsi, decomp_coef_inv _ hx, ite_eq_left hx]
    obtain ⟨⟨p, q, u, α⟩, -⟩ := x
    simp only [decompInv, decomp_norm_ft_neg]
  rw [h2, summable_subtype_iff_indicator] at h1
  convert h1 using 1
  funext i
  by_cases hi : i ∈ S
  · rw [Set.indicator_of_mem hi]
  · rw [Set.indicator_of_notMem hi]
    simp only [S, Set.mem_ofPred_eq, not_not] at hi
    simp [decompPsi, hi]

/-- Absolute summability of the interaction summands for a normalized `N`-particle state. -/
theorem intTerm_summable_norm (L : ℝ) (V : R3 → ℝ) (N : ℕ) (Ψ : Occ → ℂ)
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    Summable fun i => ‖intTerm L V Ψ i‖ := by
  have hsum := ((decomp_phi_summable L V N Ψ hV hΨ).add
    (decomp_psi_summable L V N Ψ hV hΨ)).mul_left (|(L ^ 3)⁻¹| * (N : ℝ) ^ 2)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hsum
  obtain ⟨p, q, u, α⟩ := i
  by_cases hc : decompCoef (p, q, u, α) = 0
  · have : intTerm L V Ψ (p, q, u, α) = 0 := by
      by_contra h
      exact decomp_coef_ne_zero L V Ψ h hc
    rw [this, norm_zero]
    exact mul_nonneg (by positivity)
      (add_nonneg (decomp_phi_nonneg L V Ψ _) (decomp_psi_nonneg L V Ψ _))
  by_cases hα : Ψ α = 0
  · simp only [intTerm, hα, mul_zero, norm_zero]
    exact mul_nonneg (by positivity)
      (add_nonneg (decomp_phi_nonneg L V Ψ _) (decomp_psi_nonneg L V Ψ _))
  have hcN : decompCoef (p, q, u, α) ≤ (N : ℝ) ^ 2 := a4_fst_le _ _ _ _ α N (hΨ.2 α hα)
  have hc0 : 0 ≤ decompCoef (p, q, u, α) := a4_fst_nonneg _ _ _ _ α
  simp only [decompPhi, decompPsi, ite_eq_left hc, decompInv]
  simp only [intTerm, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  set a := ‖Ψ (a4 p q (p - u) (q + u) α).2‖
  set b := ‖Ψ α‖
  set v := ‖ft V (mom L u)‖
  set k := |(L ^ 3)⁻¹|
  have hc' : |(a4 p q (p - u) (q + u) α).1| ≤ (N : ℝ) ^ 2 := by
    rw [abs_of_nonneg (show 0 ≤ (a4 p q (p - u) (q + u) α).1 from hc0)]; exact hcN
  have hab : a * b ≤ b ^ 2 + a ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hv : 0 ≤ v := norm_nonneg _
  have hk : 0 ≤ k := abs_nonneg _
  calc k * v * a * |(a4 p q (p - u) (q + u) α).1| * b
      ≤ k * v * (N : ℝ) ^ 2 * (a * b) := by
        have := mul_le_mul_of_nonneg_left hc' (by positivity : 0 ≤ k * v * a * b)
        nlinarith
    _ ≤ k * v * (N : ℝ) ^ 2 * (b ^ 2 + a ^ 2) := by gcongr
    _ = k * (N : ℝ) ^ 2 * (v * b ^ 2 + v * a ^ 2) := by ring

/-- Decomposition of §4: `⟨H⟩_Ψ = E` iff the kinetic sum and the five interaction parts have
(real) sums adding to `E`. -/
theorem hasEnergy_iff (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (E : ℝ) :
    HasEnergy L V Ψ E ↔ ∃ K : ℝ, ∃ I : Part → ℝ, HasSum (kinTerm L Ψ) K ∧
      (∀ j, HasSum (partTerm j L V Ψ) (I j : ℂ)) ∧ E = K + ∑ j, I j := by
  have hsum : ∀ J : Part → ℂ, (∀ j, HasSum (partTerm j L V Ψ) (J j)) →
      HasSum (intTerm L V Ψ) (∑ j, J j) := fun J hJ => by
    have := hasSum_sum (s := Finset.univ) fun j _ => hJ j
    simpa only [sum_partTerm] using this
  constructor
  · rintro ⟨K, I, hK, hI, hE⟩
    have hJ : ∀ j, HasSum (partTerm j L V Ψ) (∑' i, partTerm j L V Ψ i) := fun j => by
      have : partTerm j L V Ψ = {i | j.mem i.1 i.2.1 i.2.2.1}.indicator (intTerm L V Ψ) := by
        funext i
        simp only [partTerm, Set.indicator, Set.mem_ofPred_eq]
      rw [this]
      exact (hI.summable.indicator _).hasSum
    have hre : ∀ j, (((∑' i, partTerm j L V Ψ i).re : ℝ) : ℂ) = ∑' i, partTerm j L V Ψ i :=
      fun j => Complex.ext rfl (by simp [im_eq_zero_of_hasSum j L V Ψ _ (hJ j)])
    refine ⟨K, fun j => (∑' i, partTerm j L V Ψ i).re, hK, fun j => (hre j).symm ▸ hJ j, ?_⟩
    have hI' := hI.unique (hsum _ hJ)
    apply Complex.ofReal_injective
    rw [hE, hI']
    push_cast
    simp only [hre]
  · rintro ⟨K, I, hK, hI, hE⟩
    refine ⟨K, ∑ j, (I j : ℂ), hK, hsum _ hI, ?_⟩
    rw [hE]
    push_cast
    rfl

end Decomp

end LHYUpper
