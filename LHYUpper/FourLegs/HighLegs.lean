module

public import LHYUpper.Particles.UpperIH
public import LHYUpper.FourLegs.Defs
public import LHYUpper.FourLegs.Classes

@[expose] public section

/-!
# The four nonzero legs of `H_{A2}`: special legs, the exact identity, Lemma 11.1 from Lemma 11.2

The terms of `H_{A2}`, (4.7), with four legs in `P_{H,c}` and two of them equal up to sign
(Lemma 10.1), bounded by the Schwarz inequality together with (5.40) [temp5.19] and (5.42)
[boundpsifixeduv]; the exact value (10.11) [temp8.140] of the inner sum of (10.10)
[resultinMk1k2], with the complex conjugate of Lemma 7.1 [id4a]; and Lemma 11.1 [113] from
Lemma 11.2 [thehardestlemma], where the terms with an occupation above `3` are bounded by
(5.41) [boundpsiuvmn] and (5.42) [boundpsifixeduv].
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

private lemma HL_L3 {N : ℕ} (hN : 1 ≤ N) : LN N ^ 3 = rhoN N ^ (-(25 / 8 : ℝ)) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  rw [LN, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  norm_num

/-- Lattice points of a ball are in a box -/
private lemma HL_count {L R : ℝ} (hL : 1 ≤ L) (hR : 1 ≤ R) :
    ∃ F : Finset Idx, (∀ n : Idx, ‖mom L n‖ ≤ R → n ∈ F) ∧ (F.card : ℝ) ≤ (4 * L * R) ^ 3 := by
  set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
  refine ⟨Finset.Icc (fun _ : Fin 3 => -B) (fun _ => B), ?_, ?_⟩
  · intro n hn
    have hL0 : 0 < L := by linarith
    have hi : ∀ i : Fin 3, |(n i : ℝ)| ≤ B := by
      intro i
      have h1 : |(mom L n).ofLp i| ≤ R := by
        have := PiLp.norm_apply_le (mom L n) i
        rw [Real.norm_eq_abs] at this
        exact this.trans hn
      have e : (mom L n).ofLp i = 2 * π / L * (n i : ℝ) := rfl
      rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
      have h2 : |(n i : ℝ)| ≤ L * R / (2 * π) := by
        rw [le_div_iff₀ (by positivity)]
        have := h1
        rw [div_mul_eq_mul_div, div_le_iff₀ hL0] at this
        nlinarith
      exact h2.trans (Int.le_ceil _)
    rw [Finset.mem_Icc]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := (abs_le.1 (hi i)).1
      exact_mod_cast this
    · have := (abs_le.1 (hi i)).2
      exact_mod_cast this
  · have hB1 : (B : ℝ) < L * R / (2 * π) + 1 := Int.ceil_lt_add_one _
    have hB0 : (0 : ℝ) ≤ B := by
      have : (0 : ℝ) < L * R / (2 * π) := by positivity
      exact_mod_cast (Int.ceil_pos.2 this).le
    rw [Pi.card_Icc]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h3 := Real.pi_gt_three
    have hLR : 1 ≤ L * R := by nlinarith
    have hq : L * R / (2 * π) ≤ L * R / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hb : (2 * (B : ℝ) + 1) ≤ 4 * L * R := by nlinarith
    have : ((B + 1 - -B).toNat : ℝ) = 2 * (B : ℝ) + 1 := by
      have : (0 : ℤ) ≤ B + 1 - -B := by
        have : (0 : ℤ) ≤ B := by exact_mod_cast hB0
        omega
      rw [← Int.cast_natCast, Int.toNat_of_nonneg this]
      push_cast; ring
    push_cast [this]
    exact pow_le_pow_left₀ (by linarith) hb 3

/-- A nonnegative family on `(p, q, u, α)` supported on finitely many tuples `(p, q, u)` is
summable, with sum at most `#T` times the bound of the fibre sums. -/
private lemma HL_tuples (T : Finset (Idx × Idx × Idx)) (F : Idx × Idx × Idx × Occ → ℝ)
    (hT : ∀ i, F i ≠ 0 → (i.1, i.2.1, i.2.2.1) ∈ T) {B : ℝ}
    (hs : ∀ t ∈ T, Summable fun α : Occ => F (t.1, t.2.1, t.2.2, α))
    (hB : ∀ t ∈ T, ∑' α : Occ, F (t.1, t.2.1, t.2.2, α) ≤ B) :
    Summable F ∧ ∑' i, F i ≤ T.card * B := by
  set Ft : Idx × Idx × Idx → Idx × Idx × Idx × Occ → ℝ := fun t i =>
    if (i.1, i.2.1, i.2.2.1) = t then F i else 0 with hFt
  have hinj : ∀ t : Idx × Idx × Idx, Function.Injective fun α : Occ => (t.1, t.2.1, t.2.2, α) := by
    intro t a b h
    simpa using h
  have hFts : ∀ t ∈ T, Summable (Ft t) := by
    intro t ht
    rw [← (hinj t).summable_iff]
    · simpa [Function.comp_def, hFt] using hs t ht
    · intro i hi
      simp only [hFt]
      rw [ite_eq_right]
      intro h
      apply hi
      obtain ⟨p, q, u, α⟩ := i
      obtain ⟨p', q', u'⟩ := t
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨α, rfl⟩
  have hFt_tsum : ∀ t ∈ T, ∑' i, Ft t i = ∑' α : Occ, F (t.1, t.2.1, t.2.2, α) := by
    intro t ht
    rw [← (hinj t).tsum_eq]
    · simp [hFt]
    · intro i hi
      simp only [Function.mem_support, hFt] at hi
      by_cases h : (i.1, i.2.1, i.2.2.1) = t
      · obtain ⟨p, q, u, α⟩ := i
        obtain ⟨p', q', u'⟩ := t
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨α, rfl⟩
      · exact absurd (by simp [h]) hi
  have hsum : ∀ i, F i = ∑ t ∈ T, Ft t i := by
    intro i
    by_cases h : F i = 0
    · simp [h, hFt]
    · have := hT i h
      simp only [hFt]
      rw [Finset.sum_ite_eq T]
      simp [this]
  have hSum : Summable F := by
    have : F = fun i => ∑ t ∈ T, Ft t i := funext hsum
    rw [this]
    exact summable_sum hFts
  refine ⟨hSum, ?_⟩
  have : F = fun i => ∑ t ∈ T, Ft t i := funext hsum
  rw [this, Summable.tsum_finsetSum hFts]
  calc ∑ t ∈ T, ∑' i, Ft t i = ∑ t ∈ T, ∑' α : Occ, F (t.1, t.2.1, t.2.2, α) :=
        Finset.sum_congr rfl hFt_tsum
    _ ≤ ∑ t ∈ T, B := Finset.sum_le_sum hB
    _ = T.card * B := by simp

/-- `⟨β| a†_{v₁} a†_{v₂} a_{v₃} a_{v₄} |α⟩ = √(w₃₄(α)) √(w₁₂(β))`. -/
private lemma HL_a4_fst (v₁ v₂ v₃ v₄ : Idx) (α : Occ) :
    (a4 v₁ v₂ v₃ v₄ α).1 =
      Real.sqrt ((α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0) *
        Real.sqrt (((a4 v₁ v₂ v₃ v₄ α).2 v₁ : ℝ) * (a4 v₁ v₂ v₃ v₄ α).2 v₂ -
          if v₁ = v₂ then ((a4 v₁ v₂ v₃ v₄ α).2 v₁ : ℝ) else 0) := by
  simp only [a4]
  set γ := α - Finsupp.single v₄ 1 - Finsupp.single v₃ 1 + Finsupp.single v₂ 1 with hγ
  have e1 : ((α v₄ : ℕ) : ℝ) * (((α - Finsupp.single v₄ 1 : Occ) v₃ : ℕ) : ℝ) =
      (α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0 := by
    by_cases h : v₃ = v₄
    · subst h
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, ite_true]
      rcases Nat.eq_zero_or_pos (α v₃) with h0 | h0
      · simp [h0]
      · rw [Nat.cast_sub h0]; push_cast; ring
    · simp only [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm h, ite_false, h, tsub_zero]
      ring
  have e2 : ((γ v₂ : ℕ) : ℝ) * (((γ + Finsupp.single v₁ 1 : Occ) v₁ : ℕ) : ℝ) =
      ((γ + Finsupp.single v₁ 1 : Occ) v₁ : ℝ) * (γ + Finsupp.single v₁ 1 : Occ) v₂ -
        if v₁ = v₂ then ((γ + Finsupp.single v₁ 1 : Occ) v₁ : ℝ) else 0 := by
    by_cases h : v₁ = v₂
    · subst h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, ite_true]
      push_cast; ring
    · simp only [Finsupp.add_apply, Finsupp.single_apply, h, ite_false, add_zero]
      ring
  rw [← e1, ← e2, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

/-- Schwarz bound for `⟨a†_{v₁} a†_{v₂} a_{v₃} a_{v₄}⟩_Ψ` with absolute values, with the sums
restricted to `α ∈ P` and the two norms to `β ∈ R`, `α ∈ S`. -/
private lemma HL_schwarz {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ v₂ v₃ v₄ : Idx)
    (P R S : Occ → Prop) [DecidablePred P] [DecidablePred R] [DecidablePred S]
    (hPRS : ∀ α, P α → (a4 v₁ v₂ v₃ v₄ α).1 ≠ 0 → R (a4 v₁ v₂ v₃ v₄ α).2 ∧ S α) :
    ∑' α : Occ, (if P α then
        ‖conj (Ψ (a4 v₁ v₂ v₃ v₄ α).2) * ((a4 v₁ v₂ v₃ v₄ α).1 : ℂ) * Ψ α‖ else 0) ≤
      Real.sqrt (∑' β : Occ, if R β then
          ((β v₁ : ℝ) * β v₂ - if v₁ = v₂ then (β v₁ : ℝ) else 0) * ‖Ψ β‖ ^ 2 else 0) *
        Real.sqrt (∑' α : Occ, if S α then
          ((α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0) * ‖Ψ α‖ ^ 2 else 0) := by
  set w₁₂ : Occ → ℝ := fun β => (β v₁ : ℝ) * β v₂ - if v₁ = v₂ then (β v₁ : ℝ) else 0
    with hw₁₂
  set w₃₄ : Occ → ℝ := fun α => (α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0
    with hw₃₄
  set b : Occ → Occ := fun α => (a4 v₁ v₂ v₃ v₄ α).2 with hb
  set S₀ : Set Occ := {α | (a4 v₁ v₂ v₃ v₄ α).1 ≠ 0} with hS₀
  have hw₁₂0 : ∀ β, 0 ≤ w₁₂ β := fun β => by
    rw [hw₁₂]; simp only; rw [← a4_diag_fst]; exact a4_fst_nonneg _ _ _ _ _
  have hw₃₄0 : ∀ α, 0 ≤ w₃₄ α := fun α => by
    rw [hw₃₄]; simp only; rw [← a4_diag_fst]; exact a4_fst_nonneg _ _ _ _ _
  have hwle : ∀ (x y : Idx) (β : Occ), Ψ β ≠ 0 →
      (β x : ℝ) * β y - (if x = y then (β x : ℝ) else 0) ≤ (N : ℝ) ^ 2 := fun x y β h => by
    rw [← a4_diag_fst]; exact a4_fst_le _ _ _ _ _ _ (hΨ.2 β h)
  have hsq : Summable fun β : Occ => ‖Ψ β‖ ^ 2 := hΨ.1.summable
  have hwsum : ∀ (x y : Idx), Summable fun β : Occ =>
      ((β x : ℝ) * β y - (if x = y then (β x : ℝ) else 0)) * ‖Ψ β‖ ^ 2 := fun x y => by
    refine Summable.of_nonneg_of_le (fun β => ?_) (fun β => ?_) (hsq.mul_left ((N : ℝ) ^ 2))
    · refine mul_nonneg ?_ (sq_nonneg _)
      rw [← a4_diag_fst]; exact a4_fst_nonneg _ _ _ _ _
    · by_cases h : Ψ β = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (hwle x y β h) (sq_nonneg _)
  set H : Occ → ℝ := fun β => if R β then w₁₂ β * ‖Ψ β‖ ^ 2 else 0 with hH
  have hH0 : ∀ β, 0 ≤ H β := fun β => by
    rw [hH]; simp only; split_ifs
    · exact mul_nonneg (hw₁₂0 β) (sq_nonneg _)
    · exact le_rfl
  have hw12sum : Summable fun β => w₁₂ β * ‖Ψ β‖ ^ 2 := hwsum v₁ v₂
  have hw34sum : Summable fun α => w₃₄ α * ‖Ψ α‖ ^ 2 := hwsum v₃ v₄
  have hHle : ∀ β, H β ≤ w₁₂ β * ‖Ψ β‖ ^ 2 := fun β => by
    by_cases h : R β
    · simp [hH, h]
    · simp only [hH, h, ite_false]
      exact mul_nonneg (hw₁₂0 β) (sq_nonneg _)
  have hHsum : Summable H := Summable.of_nonneg_of_le hH0 hHle hw12sum
  set K : Occ → ℝ := fun α => if S α then w₃₄ α * ‖Ψ α‖ ^ 2 else 0 with hK
  have hKle : ∀ α, K α ≤ w₃₄ α * ‖Ψ α‖ ^ 2 := fun α => by
    by_cases h : S α
    · simp [hK, h]
    · simp only [hK, h, ite_false]
      exact mul_nonneg (hw₃₄0 α) (sq_nonneg _)
  have hK0 : ∀ α, 0 ≤ K α := fun α => by
    by_cases h : S α
    · simp only [hK, h, ite_true]
      exact mul_nonneg (hw₃₄0 α) (sq_nonneg _)
    · simp [hK, h]
  have hKsum : Summable K := Summable.of_nonneg_of_le hK0 hKle hw34sum
  set F : Occ → ℝ := fun α => if α ∈ S₀ ∧ P α then Real.sqrt (w₁₂ (b α)) * ‖Ψ (b α)‖ else 0
    with hF
  set G : Occ → ℝ := fun α => if S α then Real.sqrt (w₃₄ α) * ‖Ψ α‖ else 0 with hG
  have hF0 : ∀ α, 0 ≤ F α := fun α => by
    rw [hF]; simp only; split_ifs <;> positivity
  have hG0 : ∀ α, 0 ≤ G α := fun α => by rw [hG]; simp only; split_ifs <;> positivity
  have hterm : ∀ α : Occ,
      (if P α then ‖conj (Ψ (a4 v₁ v₂ v₃ v₄ α).2) * ((a4 v₁ v₂ v₃ v₄ α).1 : ℂ) * Ψ α‖ else 0) =
        F α * G α := by
    intro α
    by_cases hP : P α
    · by_cases hα : α ∈ S₀
      · obtain ⟨hR, hS⟩ := hPRS α hP hα
        rw [ite_eq_left hP, hF, hG]
        simp only [hα, hP, hS, and_self, ite_true]
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (a4_fst_nonneg _ _ _ _ _), HL_a4_fst]
        simp only [hw₁₂, hw₃₄, hb]
        ring
      · have h0 : (a4 v₁ v₂ v₃ v₄ α).1 = 0 := by simpa [hS₀] using hα
        rw [ite_eq_left hP, hF]
        simp only [hα, false_and, ite_false, zero_mul, h0]
        simp
    · rw [ite_eq_right hP, hF]
      simp [hP]
  have hinj : Function.Injective fun α : S₀ => b α.1 := by
    intro x y h
    exact Subtype.ext (a4_injOn v₁ v₂ v₃ v₄ x.2 y.2 h)
  have hFsq : ∀ α, F α ^ (2 : ℝ) ≤ S₀.indicator (fun α => H (b α)) α := by
    intro α
    rw [Real.rpow_two]
    by_cases hα : α ∈ S₀
    · rw [Set.indicator_of_mem hα]
      by_cases hP : P α
      · obtain ⟨hR, -⟩ := hPRS α hP hα
        have hR' : R (b α) := hR
        have : F α = Real.sqrt (w₁₂ (b α)) * ‖Ψ (b α)‖ := by simp [hF, hα, hP]
        rw [this, mul_pow, Real.sq_sqrt (hw₁₂0 _)]
        simp [hH, hR']
      · have : F α = 0 := by simp [hF, hP]
        rw [this]; simpa using hH0 (b α)
    · rw [Set.indicator_of_notMem hα]
      have : F α = 0 := by simp [hF, hα]
      rw [this]; simp
  have hFsq0 : ∀ α, 0 ≤ S₀.indicator (fun α => H (b α)) α := fun α => by
    by_cases hα : α ∈ S₀
    · rw [Set.indicator_of_mem hα]; exact hH0 _
    · rw [Set.indicator_of_notMem hα]
  have hGsq : ∀ α, G α ^ (2 : ℝ) = K α := by
    intro α
    rw [Real.rpow_two, hG, hK]
    simp only
    split_ifs
    · rw [mul_pow, Real.sq_sqrt (hw₃₄0 _)]
    · simp
  have hIsum : Summable (S₀.indicator fun α => H (b α)) :=
    (summable_subtype_iff_indicator (s := S₀)).1 (hHsum.comp_injective hinj)
  have hFsum : Summable fun α => F α ^ (2 : ℝ) :=
    Summable.of_nonneg_of_le (fun α => by positivity) hFsq hIsum
  have hGsum : Summable fun α => G α ^ (2 : ℝ) := by
    simp only [hGsq]
    exact hKsum
  have hCS := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hF0 hG0
    hFsum hGsum
  have hFle : ∑' α, F α ^ (2 : ℝ) ≤ ∑' β, H β := by
    refine (hFsum.tsum_le_tsum hFsq hIsum).trans ?_
    rw [← tsum_subtype S₀ (fun α => H (b α))]
    exact tsum_comp_le_tsum_of_inj hHsum hH0 hinj
  simp only [hterm]
  refine hCS.trans ?_
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  simp only [hGsq]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hFle) (Real.sqrt_nonneg _)

/-- `Σ_α W(key α) |Ψ(α)|² ≤ Σ_i W(i) b(i)` when the fibre masses of `|Ψ|²` are at most `b`. -/
private lemma HL_fiber {ι : Type*} (key : Occ → ι) (Ψ : Occ → ℂ)
    (hs : Summable fun α => ‖Ψ α‖ ^ 2) (W b : ι → ℝ) (hW : ∀ i, 0 ≤ W i)
    (hb : Summable fun i => W i * b i)
    (hab : ∀ i, (∑' α : Occ, if key α = i then ‖Ψ α‖ ^ 2 else 0) ≤ b i) :
    ∑' α : Occ, W (key α) * ‖Ψ α‖ ^ 2 ≤ ∑' i, W i * b i := by
  have hb0 : ∀ i, 0 ≤ b i := fun i =>
    (tsum_nonneg fun α => by split_ifs <;> positivity).trans (hab i)
  set F : Occ → ℝ := fun α => W (key α) * ‖Ψ α‖ ^ 2 with hF
  by_cases hFs : Summable F
  swap
  · rw [tsum_eq_zero_of_not_summable hFs]
    exact tsum_nonneg fun i => mul_nonneg (hW i) (hb0 i)
  let e := Equiv.sigmaFiberEquiv key
  have hfib : ∀ i, HasSum (fun c : {α : Occ // key α = i} => F (e ⟨i, c⟩))
      (W i * ∑' α : Occ, if key α = i then ‖Ψ α‖ ^ 2 else 0) := by
    intro i
    have h1 : HasSum (fun c : {α : Occ // key α = i} => ‖Ψ c.1‖ ^ 2)
        (∑' α : Occ, if key α = i then ‖Ψ α‖ ^ 2 else 0) := by
      have h2 : HasSum (Set.indicator {α : Occ | key α = i} fun α => ‖Ψ α‖ ^ 2)
          (∑' α : Occ, if key α = i then ‖Ψ α‖ ^ 2 else 0) := by
        have : (∑' α : Occ, if key α = i then ‖Ψ α‖ ^ 2 else 0) =
            ∑' α, Set.indicator {α : Occ | key α = i} (fun α => ‖Ψ α‖ ^ 2) α := by
          congr 1
        rw [this]
        exact (hs.indicator _).hasSum
      exact (hasSum_subtype_iff_indicator (f := fun α : Occ => ‖Ψ α‖ ^ 2)
        (s := {α : Occ | key α = i})).mpr h2
    convert h1.mul_left (W i) using 1
    funext c
    obtain ⟨c, hc⟩ := c
    subst hc
    simp [e, hF]
  have hall : HasSum (fun i => W i * ∑' α : Occ, if key α = i then ‖Ψ α‖ ^ 2 else 0)
      (∑' α, F α) :=
    HasSum.sigma (f := fun x => F (e x)) (e.hasSum_iff.mpr hFs.hasSum) hfib
  rw [← hall.tsum_eq]
  exact hall.summable.tsum_le_tsum
    (fun i => mul_le_mul_of_nonneg_left (hab i) (hW i)) hb

/-- `Σ_m (m² - m) x^m ≤ K x²` for `0 ≤ x ≤ 1/2`. -/
private lemma HL_geo1 : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 →
    Summable (fun m : ℕ => ((m : ℝ) * m - m) * x ^ m) ∧
      ∑' m : ℕ, ((m : ℝ) * m - m) * x ^ m ≤ K * x ^ 2 := by
  have hs : Summable fun m : ℕ => ((m : ℝ) ^ 2) * (1 / 2 : ℝ) ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num)
  set K₀ : ℝ := ∑' m : ℕ, ((m : ℝ) ^ 2) * (1 / 2 : ℝ) ^ m with hK₀
  have hK₀0 : 0 ≤ K₀ := tsum_nonneg fun m => by positivity
  refine ⟨4 * K₀, by positivity, fun x hx0 hx1 => ?_⟩
  have hle : ∀ m : ℕ, ((m : ℝ) * m - m) * x ^ m ≤
      4 * x ^ 2 * (((m : ℝ) ^ 2) * (1 / 2 : ℝ) ^ m) := by
    intro m
    rcases Nat.lt_or_ge m 2 with h | h
    · have h0 : ((m : ℝ) * m - m) = 0 := by interval_cases m <;> simp
      rw [h0, zero_mul]
      positivity
    · have h1 : x ^ m ≤ x ^ 2 * (1 / 2 : ℝ) ^ (m - 2) := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [pow_add, show 2 + j - 2 = j by omega]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 j) (by positivity)
      have h2 : (1 / 2 : ℝ) ^ (m - 2) = 4 * (1 / 2 : ℝ) ^ m := by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [show 2 + j - 2 = j by omega, pow_add]
        ring
      have hm : ((m : ℝ) * m - m) ≤ (m : ℝ) ^ 2 := by
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        nlinarith
      have hm0 : 0 ≤ ((m : ℝ) * m - m) := by
        have : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
        nlinarith
      calc ((m : ℝ) * m - m) * x ^ m ≤ (m : ℝ) ^ 2 * (x ^ 2 * (4 * (1 / 2 : ℝ) ^ m)) := by
            rw [h2] at h1
            exact mul_le_mul hm h1 (by positivity) (by positivity)
        _ = 4 * x ^ 2 * (((m : ℝ) ^ 2) * (1 / 2 : ℝ) ^ m) := by ring
  have hnn : ∀ m : ℕ, 0 ≤ ((m : ℝ) * m - m) * x ^ m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp
    · have : (1 : ℝ) ≤ m := by exact_mod_cast h
      have : 0 ≤ (m : ℝ) * m - m := by nlinarith
      positivity
  have hsum := Summable.of_nonneg_of_le hnn hle (hs.mul_left (4 * x ^ 2))
  refine ⟨hsum, ?_⟩
  calc ∑' m : ℕ, ((m : ℝ) * m - m) * x ^ m
      ≤ ∑' m : ℕ, 4 * x ^ 2 * (((m : ℝ) ^ 2) * (1 / 2 : ℝ) ^ m) :=
        hsum.tsum_le_tsum hle (hs.mul_left _)
    _ = 4 * K₀ * x ^ 2 := by rw [tsum_mul_left, hK₀]; ring

/-- `Σ_{m ≥ 4, n} m n x^{m+n} ≤ K x⁵` for `0 ≤ x ≤ 1/2`. -/
private lemma HL_geo2 : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 →
    Summable (fun p : ℕ × ℕ => (if 4 ≤ p.1 then (p.1 : ℝ) * p.2 else 0) * (x ^ p.1 * x ^ p.2)) ∧
      ∑' p : ℕ × ℕ, (if 4 ≤ p.1 then (p.1 : ℝ) * p.2 else 0) * (x ^ p.1 * x ^ p.2) ≤ K * x ^ 5 := by
  have hs : Summable fun m : ℕ => ((m : ℝ) ^ 1) * (1 / 2 : ℝ) ^ m :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have hs' : Summable fun m : ℕ => (m : ℝ) * (1 / 2 : ℝ) ^ m := by simpa using hs
  set K₀ : ℝ := ∑' m : ℕ, (m : ℝ) * (1 / 2 : ℝ) ^ m with hK₀
  have hK₀0 : 0 ≤ K₀ := tsum_nonneg fun m => by positivity
  have hprod := hs'.mul_of_nonneg hs' (fun m => by positivity) (fun m => by positivity)
  refine ⟨32 * (K₀ * K₀), by positivity, fun x hx0 hx1 => ?_⟩
  set g : ℕ × ℕ → ℝ := fun p => ((p.1 : ℝ) * (1 / 2 : ℝ) ^ p.1) * ((p.2 : ℝ) * (1 / 2 : ℝ) ^ p.2)
    with hg
  have hle : ∀ p : ℕ × ℕ, (if 4 ≤ p.1 then (p.1 : ℝ) * p.2 else 0) * (x ^ p.1 * x ^ p.2) ≤
      32 * x ^ 5 * g p := by
    rintro ⟨m, n⟩
    simp only [hg]
    by_cases h : 4 ≤ m ∧ 1 ≤ n
    · obtain ⟨h1, h2⟩ := h
      simp only [h1, ite_true]
      have h3 : x ^ m * x ^ n ≤ x ^ 5 * (1 / 2 : ℝ) ^ (m + n - 5) := by
        rw [← pow_add]
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show 5 ≤ m + n by omega)
        rw [hj, pow_add]
        simp only [Nat.add_sub_cancel_left]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx1 j) (by positivity)
      have h4 : (1 / 2 : ℝ) ^ (m + n - 5) = 32 * ((1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ^ n) := by
        obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (show 5 ≤ m + n by omega)
        rw [hj, Nat.add_sub_cancel_left, ← pow_add, hj, pow_add]
        ring
      rw [h4] at h3
      calc (m : ℝ) * n * (x ^ m * x ^ n) ≤ (m : ℝ) * n * (x ^ 5 * (32 * ((1 / 2 : ℝ) ^ m *
            (1 / 2 : ℝ) ^ n))) := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 32 * x ^ 5 * (((m : ℝ) * (1 / 2 : ℝ) ^ m) * ((n : ℝ) * (1 / 2 : ℝ) ^ n)) := by ring
    · have : (if 4 ≤ m then (m : ℝ) * n else 0) = 0 := by
        by_cases h4 : 4 ≤ m
        · have : n = 0 := by omega
          simp [this]
        · simp [h4]
      rw [this, zero_mul]
      positivity
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ (if 4 ≤ p.1 then (p.1 : ℝ) * p.2 else 0) * (x ^ p.1 * x ^ p.2) := by
    intro p
    split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnn hle (hprod.mul_left (32 * x ^ 5))
  refine ⟨hsum, ?_⟩
  calc ∑' p : ℕ × ℕ, (if 4 ≤ p.1 then (p.1 : ℝ) * p.2 else 0) * (x ^ p.1 * x ^ p.2)
      ≤ ∑' p : ℕ × ℕ, 32 * x ^ 5 * g p := hsum.tsum_le_tsum hle (hprod.mul_left _)
    _ = 32 * x ^ 5 * ∑' p : ℕ × ℕ, g p := by rw [tsum_mul_left]
    _ = 32 * (K₀ * K₀) * x ^ 5 := by
        rw [hs'.tsum_mul_tsum hs' hprod |>.symm]
        ring

/-- `ρ_N^a → 0` for `a > 0`. -/
private lemma HL_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := 8 / 17 * a) (by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp, rhoN]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  ring_nf

/-- `ρ^x = ε^k` for `x = k/200`, `ε = ρ^{1/200}`. -/
private lemma HL_rpow_eps {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {x : ℝ} (hx : x = (k : ℝ) / 200) :
    ρ ^ x = epsP ρ ^ k := by
  rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ, hx]
  ring_nf

/-- `ρ^m / ε^k = ρ^{m - k/200}`. -/
private lemma HL_ratio {ρ : ℝ} (hρ : 0 < ρ) (m k : ℕ) :
    ρ ^ m / epsP ρ ^ k = ρ ^ ((m : ℝ) - (k : ℝ) / 200) := by
  rw [Real.rpow_sub hρ, Real.rpow_natCast, HL_rpow_eps hρ.le k rfl]

/-- `C ρ² / ε⁴ ≤ 1/2` for all large `N`. -/
private lemma HL_small (C : ℝ) : ∀ᶠ N : ℕ in atTop, C * rhoN N ^ 2 / epsP (rhoN N) ^ 4 ≤ 1 / 2 := by
  have h0 : Tendsto (fun N : ℕ => C * rhoN N ^ (2 - 4 / 200 : ℝ)) atTop (𝓝 0) := by
    simpa using (HL_tendsto (a := 2 - 4 / 200) (by norm_num)).const_mul C
  have h := (h0.eventually_lt_const (show (0 : ℝ) < 1 / 2 from by norm_num)).mono
    fun _ h => h.le
  filter_upwards [h, eventually_ge_atTop 1] with N hN hN1
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN1
  have := HL_ratio hρ 2 4
  rw [mul_div_assoc, this]
  simpa using hN

/-- `Q_Ψ({u, m})` as a restricted sum. -/
private lemma HL_Qm_single (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) :
    Expect.Qm Ψ [(u, m)] = ∑' α : Occ, if α u = m then ‖Ψ α‖ ^ 2 else 0 := by
  simp [Expect.Qm, Expect.Ev]

/-- `Q_Ψ({u, m}, {v, n})` as a restricted sum. -/
private lemma HL_Qm_pair (Ψ : Occ → ℂ) (u v : Idx) (m n : ℕ) :
    Expect.Qm Ψ [(u, m), (v, n)] =
      ∑' α : Occ, if α u = m ∧ α v = n then ‖Ψ α‖ ^ 2 else 0 := by
  simp [Expect.Qm, Expect.Ev]



/-- `Σ_β (β(k)β(k') - δ_{kk'}β(k)) |Ψ(β)|² ≤ C ρ⁴ / ε⁸` for `k, k' ∈ P_H` with `k + k' ≠ 0`:
(5.40) [temp5.19] for `k = k'`, (5.42) [boundpsifixeduv] otherwise. -/
private lemma HL_pair {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ k k' : Idx,
      inPH (rhoN N) (LN N) k → inPH (rhoN N) (LN N) k' → k + k' ≠ 0 →
      ∑' β : Occ, ((β k : ℝ) * β k' - if k = k' then (β k : ℝ) else 0) *
          ‖trialState V w kc N β‖ ^ 2 ≤ C * rhoN N ^ 4 / epsP (rhoN N) ^ 8 := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C₀, hC₀, N₀, h40⟩ := Eq5_40 V w
  obtain ⟨C₂, hC₂, N₂, h42⟩ := Eq5_42 V w
  obtain ⟨K, hK, hKb⟩ := HL_geo1
  refine ⟨C₂ * g0 V w ^ 2 + K * (C₀ * g0 V w) ^ 2, by positivity, ?_⟩
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    (((eventually_ge_atTop N₀).and (eventually_ge_atTop N₂)).and
      ((eventually_ge_atTop 1).and (HL_small (C₀ * g0 V w))))
  refine ⟨N₁, fun N hN kc k k' hk hk' hkk => ?_⟩
  obtain ⟨⟨hN0, hN2⟩, hN1, hsm⟩ := hN₁ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := by unfold epsP; positivity
  have hlam : ∀ n : Idx, inPH (rhoN N) (LN N) n →
      |lam V w (rhoN N) (LN N) n| ≤ g0 V w / epsP (rhoN N) ^ 2 :=
    fun n hn => scat_lam_PH hV hw _ hρ _ n hn
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN1).1.summable
  by_cases hne : k = k'
  · subst hne
    set x : ℝ := C₀ * g0 V w * rhoN N ^ 2 / epsP (rhoN N) ^ 4 with hx
    have hx0 : 0 ≤ x := by positivity
    obtain ⟨hsum, hle⟩ := hKb x hx0 hsm
    have hab : ∀ m : ℕ, (∑' α : Occ, if α k = m then ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        x ^ m := by
      intro m
      rw [← HL_Qm_single]
      refine (h40 N hN0 kc k hk m).trans (pow_le_pow_left₀ (by positivity) ?_ m)
      have hk1 : epsP (rhoN N) < ‖mom (LN N) k‖ := hk
      have hmom : epsP (rhoN N) ^ 2 ≤ ‖mom (LN N) k‖ ^ 2 :=
        pow_le_pow_left₀ hε.le hk1.le 2
      calc C₀ * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) k| / ‖mom (LN N) k‖ ^ 2
          ≤ C₀ * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2 := by
            refine div_le_div₀ (by positivity) ?_ (by positivity) hmom
            exact mul_le_mul_of_nonneg_left (hlam k hk) (by positivity)
        _ = x := by rw [hx]; field_simp
    have hfib := HL_fiber (fun α : Occ => α k) (trialState V w kc N) hs
      (fun m : ℕ => (m : ℝ) * m - m) (fun m : ℕ => x ^ m)
      (fun m => by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp
        · have : (1 : ℝ) ≤ m := by exact_mod_cast h
          nlinarith)
      hsum (fun m => by convert hab m)
    simp only [ite_true]
    refine hfib.trans (hle.trans ?_)
    have e : K * x ^ 2 = K * (C₀ * g0 V w) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 8 := by
      rw [hx]; field_simp
    rw [e]
    have : 0 ≤ C₂ * g0 V w ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 8 := by positivity
    rw [add_mul, add_div]
    linarith
  · simp only [hne, ite_false, sub_zero]
    have hQ : (∑' β : Occ, (β k : ℝ) * β k' * ‖trialState V w kc N β‖ ^ 2) =
        Expect.Q (trialState V w kc N) [k, k'] := by
      simp [Expect.Q, mul_assoc]
    rw [hQ]
    refine (h42 N hN2 kc k k' hk hk' hne hkk).trans ?_
    have hl : |lam V w (rhoN N) (LN N) k * lam V w (rhoN N) (LN N) k'| ≤
        g0 V w ^ 2 / epsP (rhoN N) ^ 4 := by
      rw [abs_mul]
      calc |lam V w (rhoN N) (LN N) k| * |lam V w (rhoN N) (LN N) k'|
          ≤ (g0 V w / epsP (rhoN N) ^ 2) * (g0 V w / epsP (rhoN N) ^ 2) :=
            mul_le_mul (hlam k hk) (hlam k' hk') (abs_nonneg _) (by positivity)
        _ = g0 V w ^ 2 / epsP (rhoN N) ^ 4 := by field_simp
    calc C₂ * |lam V w (rhoN N) (LN N) k * lam V w (rhoN N) (LN N) k'| * rhoN N ^ 4 /
          epsP (rhoN N) ^ 4
        ≤ C₂ * (g0 V w ^ 2 / epsP (rhoN N) ^ 4) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 := by
          gcongr
      _ = C₂ * g0 V w ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 8 := by field_simp
      _ ≤ (C₂ * g0 V w ^ 2 + K * (C₀ * g0 V w) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 8 := by
          gcongr
          have : 0 ≤ K * (C₀ * g0 V w) ^ 2 := by positivity
          linarith



/-- `Σ_{β(a) ≥ 4} β(a) β(b) |Ψ(β)|² ≤ C ρ^{10} / ε^{20}` for `a ≠ ±b` in `P_H`: (5.41)
[boundpsiuvmn]. -/
private lemma HL_pair_tail {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ a b : Idx,
      inPH (rhoN N) (LN N) a → inPH (rhoN N) (LN N) b → a ≠ b → a + b ≠ 0 →
      ∑' β : Occ, (if 4 ≤ β a then (β a : ℝ) * β b * ‖trialState V w kc N β‖ ^ 2 else 0) ≤
        C * rhoN N ^ 10 / epsP (rhoN N) ^ 20 := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C₁, hC₁, N₁, h41⟩ := Eq5_41 V w
  obtain ⟨K, hK, hKb⟩ := HL_geo2
  refine ⟨K * (C₁ * g0 V w) ^ 5, by positivity, ?_⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((eventually_ge_atTop N₁).and ((eventually_ge_atTop 1).and (HL_small (C₁ * g0 V w))))
  refine ⟨N₀, fun N hN kc a b ha hb hab hsum => ?_⟩
  obtain ⟨hN1', hN1, hsm⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := by unfold epsP; positivity
  have hlam : ∀ n : Idx, inPH (rhoN N) (LN N) n →
      |lam V w (rhoN N) (LN N) n| ≤ g0 V w / epsP (rhoN N) ^ 2 :=
    fun n hn => scat_lam_PH hV hw _ hρ _ n hn
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN1).1.summable
  set x : ℝ := C₁ * g0 V w * rhoN N ^ 2 / epsP (rhoN N) ^ 4 with hx
  have hx0 : 0 ≤ x := by positivity
  obtain ⟨hsumx, hle⟩ := hKb x hx0 hsm
  have hbd : ∀ n : Idx, inPH (rhoN N) (LN N) n →
      C₁ * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) n| / epsP (rhoN N) ^ 2 ≤ x := by
    intro n hn
    calc C₁ * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) n| / epsP (rhoN N) ^ 2
        ≤ C₁ * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2 := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left (hlam n hn) (by positivity)
      _ = x := by rw [hx]; field_simp
  have hpb : ∀ m n : ℕ, Expect.Qm (trialState V w kc N) [(a, m), (b, n)] ≤ x ^ m * x ^ n := by
    intro m n
    refine (h41 N hN1' kc a b ha hb hab hsum m n).trans ?_
    exact mul_le_mul (pow_le_pow_left₀ (by positivity) (hbd a ha) m)
      (pow_le_pow_left₀ (by positivity) (hbd b hb) n) (by positivity) (by positivity)
  have hfib := HL_fiber (fun α : Occ => (α a, α b)) (trialState V w kc N) hs
    (fun p : ℕ × ℕ => if 4 ≤ p.1 then (p.1 : ℝ) * p.2 else 0) (fun p : ℕ × ℕ => x ^ p.1 * x ^ p.2)
    (fun p => by split_ifs <;> positivity) hsumx
    (fun p => by
      rw [← Prod.mk.eta (p := p)]
      refine le_trans (le_of_eq ?_) (hpb p.1 p.2)
      rw [HL_Qm_pair]
      congr 1
      funext α
      simp [Prod.ext_iff])
  have e : K * x ^ 5 = K * (C₁ * g0 V w) ^ 5 * rhoN N ^ 10 / epsP (rhoN N) ^ 20 := by
    rw [hx]; field_simp
  refine le_trans (le_of_eq ?_) (hfib.trans (hle.trans_eq e))
  congr 1
  funext β
  by_cases h : 4 ≤ β a <;> simp [h, mul_assoc]





set_option linter.flexible false in
set_option linter.unusedTactic false in
/-- If two of the legs `p, q, p - u, q + u` agree up to sign, one of nine linear relations holds. -/
private lemma HL_rel {p q u : Idx} (h : ¬ FourLegs.Gen (FourLegs.legs p q u)) :
    q = p ∨ q = -p ∨ u = 0 ∨ u = p + p ∨ u = p - q ∨ u = -p - q ∨ u = p + q ∨
      u = -(q + q) ∨ (∀ k, 2 * u k = p k - q k) := by
  unfold FourLegs.Gen at h
  push Not at h
  obtain ⟨i, j, hij, hl⟩ := h
  unfold Legs_pm at hl
  have hl' : FourLegs.legs p q u i = FourLegs.legs p q u j ∨
      FourLegs.legs p q u i = -FourLegs.legs p q u j := by
    by_contra hc
    push Not at hc
    exact hl hc
  clear hl
  fin_cases i <;> fin_cases j <;> simp [FourLegs.legs] at hij hl' <;> rcases hl' with h | h <;>
  first
    | exact Or.inl (funext fun k => by have := congrFun h k; (try simp at this ⊢); omega)
    | exact Or.inr (Or.inl (funext fun k => by have := congrFun h k; (try simp at this ⊢); omega))
    | exact Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega)))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega))))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (fun k => by
        have := congrFun h k; (try simp at this ⊢); omega))))))))



/-- The nine families of tuples `(p, q, u)` on which two legs agree up to sign, each determined
by two of the legs `p, q, p - u`. -/
private def HL_img (F : Finset Idx) : Finset (Idx × Idx × Idx) :=
  (F ×ˢ F).biUnion fun x => ([(x.1, x.1, x.1 - x.2), (x.1, -x.1, x.1 - x.2), (x.1, x.2, 0),
    (x.1, x.2, x.1 + x.1), (x.1, x.2, x.1 - x.2), (x.1, x.2, -x.1 - x.2), (x.1, x.2, x.1 + x.2),
    (x.1, x.2, -(x.2 + x.2)), (x.1, x.2, fun k => (x.1 k - x.2 k) / 2)] :
      List (Idx × Idx × Idx)).toFinset

private lemma HL_img_card (F : Finset Idx) : (HL_img F).card ≤ 9 * F.card ^ 2 := by
  unfold HL_img
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ x ∈ F ×ˢ F, (([(x.1, x.1, x.1 - x.2), (x.1, -x.1, x.1 - x.2), (x.1, x.2, 0),
        (x.1, x.2, x.1 + x.1), (x.1, x.2, x.1 - x.2), (x.1, x.2, -x.1 - x.2),
        (x.1, x.2, x.1 + x.2), (x.1, x.2, -(x.2 + x.2)),
        (x.1, x.2, fun k => (x.1 k - x.2 k) / 2)] : List (Idx × Idx × Idx)).toFinset.card)
      ≤ ∑ _x ∈ F ×ˢ F, 9 := Finset.sum_le_sum fun x _ => List.toFinset_card_le _
    _ = 9 * F.card ^ 2 := by
        rw [Finset.sum_const, Finset.card_product, smul_eq_mul, sq]
        ring

private lemma HL_img_mem {F : Finset Idx} {p q u : Idx} (hp : p ∈ F) (hq : q ∈ F)
    (hr : p - u ∈ F) (hng : ¬ FourLegs.Gen (FourLegs.legs p q u)) : (p, q, u) ∈ HL_img F := by
  unfold HL_img
  rw [Finset.mem_biUnion]
  have hu : p - (p - u) = u := by abel
  rcases HL_rel hng with h | h | h | h | h | h | h | h | h
  · refine ⟨(p, p - u), Finset.mem_product.2 ⟨hp, hr⟩, ?_⟩
    simp [hu, h]
  · refine ⟨(p, p - u), Finset.mem_product.2 ⟨hp, hr⟩, ?_⟩
    simp [hu, h]
  all_goals refine ⟨(p, q), Finset.mem_product.2 ⟨hp, hq⟩, ?_⟩
  · simp [h]
  · simp [h]
  · simp [h]
  · simp [h]
  · simp [h]
  · simp [h]
  · have h' : u = fun k => (p k - q k) / 2 := funext fun k => by have := h k; omega
    simp [h']



/-- `‖partTerm‖ ≤ |Λ|⁻¹ V₀ ‖conj(Ψ(β)) c Ψ(α)‖` when `‖V_u‖ ≤ V₀`. -/
private lemma HL_partTerm_le {V : R3 → ℝ} {V₀ : ℝ} (hV₀ : ∀ p, ‖ft V p‖ ≤ V₀) {L : ℝ}
    (hL : 0 < L) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) :
    ‖Decomp.partTerm .A2 L V Ψ i‖ ≤ (L ^ 3)⁻¹ * V₀ *
      ‖conj (Ψ (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2) *
        (((a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).1 : ℝ) : ℂ) *
          Ψ i.2.2.2‖ := by
  have hV0 : 0 ≤ V₀ := (norm_nonneg _).trans (hV₀ 0)
  unfold Decomp.partTerm
  split_ifs
  · simp only [intTerm]
    rw [mul_assoc, mul_assoc, norm_mul, norm_mul]
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    gcongr
    · exact hV₀ _
    · rw [mul_assoc]
  · simp only [norm_zero]
    positivity



/-- `‖V_p‖ ≤ V₀` for all `p`. -/
private lemma HL_ftV_bdd {V : R3 → ℝ} (hV : PotentialHyp V) : ∃ V₀ : ℝ, ∀ p, ‖ft V p‖ ≤ V₀ := by
  obtain ⟨C, hC⟩ := scat_ft_V_decay hV 0
  exact ⟨C, fun p => by simpa using hC p⟩

/-- The sum over `α` of the terms of one tuple `(p, q, u)` with legs in `P_H`, for the
special legs of Lemma 10.1. -/
private lemma HL_tuple10 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ p q u : Idx,
      inPH (rhoN N) (LN N) p → inPH (rhoN N) (LN N) q → inPH (rhoN N) (LN N) (p - u) →
      inPH (rhoN N) (LN N) (q + u) →
      Summable (fun α : Occ => ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖) ∧
      ∑' α : Occ, ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ ≤
        (LN N ^ 3)⁻¹ * (C * rhoN N ^ 4 / epsP (rhoN N) ^ 8) := by
  obtain ⟨V₀, hV₀⟩ := HL_ftV_bdd hV
  have hV0 : 0 ≤ V₀ := (norm_nonneg _).trans (hV₀ 0)
  obtain ⟨C₁, hC₁, N₁, h⟩ := HL_pair hV hw
  refine ⟨V₀ * C₁, by positivity, max N₁ 1, fun N hN kc p q u hp hq hpu hqu => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN2 : N₁ ≤ N := le_of_max_le_left hN
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := by unfold epsP; positivity
  have hM0 : 0 ≤ C₁ * rhoN N ^ 4 / epsP (rhoN N) ^ 8 := by positivity
  by_cases hpq : p + q = 0
  · have h0 : ∀ α : Occ, Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α) = 0 :=
      fun α => by simp [Decomp.partTerm, Decomp.Part.mem, hpq]
    simp only [h0, norm_zero, tsum_zero]
    exact ⟨summable_zero, by positivity⟩
  have hpq' : (p - u) + (q + u) ≠ 0 := by
    intro h0
    apply hpq
    have : (p - u) + (q + u) = p + q := by abel
    rwa [this] at h0
  have hΨ := Normalization_isNState V w kc hN1
  have hSch := FourLegs_schwarz hΨ p q (p - u) (q + u)
  have hs1 := h N hN2 kc p q hp hq hpq
  have hs2 := h N hN2 kc (p - u) (q + u) hpu hqu hpq'
  have hsum := Expect.id4a_summable N _ hΨ p q (p - u) (q + u)
  have hle : ∀ α : Occ, ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ ≤
      (LN N ^ 3)⁻¹ * V₀ * ‖conj (trialState V w kc N (a4 p q (p - u) (q + u) α).2) *
        (((a4 p q (p - u) (q + u) α).1 : ℝ) : ℂ) * trialState V w kc N α‖ :=
    fun α => HL_partTerm_le hV₀ hL _ (p, q, u, α)
  have hsum' : Summable fun α : Occ =>
      ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle (hsum.mul_left _)
  refine ⟨hsum', (hsum'.tsum_le_tsum hle (hsum.mul_left _)).trans ?_⟩
  rw [tsum_mul_left]
  have hS : Real.sqrt (∑' β : Occ, ((β p : ℝ) * β q - if p = q then (β p : ℝ) else 0) *
        ‖trialState V w kc N β‖ ^ 2) *
      Real.sqrt (∑' α : Occ, ((α (p - u) : ℝ) * α (q + u) - if p - u = q + u then
        (α (p - u) : ℝ) else 0) * ‖trialState V w kc N α‖ ^ 2) ≤
      C₁ * rhoN N ^ 4 / epsP (rhoN N) ^ 8 := by
    calc _ ≤ Real.sqrt (C₁ * rhoN N ^ 4 / epsP (rhoN N) ^ 8) *
          Real.sqrt (C₁ * rhoN N ^ 4 / epsP (rhoN N) ^ 8) :=
          mul_le_mul (Real.sqrt_le_sqrt hs1) (Real.sqrt_le_sqrt hs2) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hM0
  have hLpos : 0 ≤ (LN N ^ 3)⁻¹ := by positivity
  calc (LN N ^ 3)⁻¹ * V₀ * ∑' α : Occ, ‖conj (trialState V w kc N (a4 p q (p - u) (q + u) α).2) *
          (((a4 p q (p - u) (q + u) α).1 : ℝ) : ℂ) * trialState V w kc N α‖
      ≤ (LN N ^ 3)⁻¹ * V₀ * (C₁ * rhoN N ^ 4 / epsP (rhoN N) ^ 8) :=
        mul_le_mul_of_nonneg_left (hSch.trans hS) (by positivity)
    _ = (LN N ^ 3)⁻¹ * (V₀ * C₁ * rhoN N ^ 4 / epsP (rhoN N) ^ 8) := by ring



private lemma HL_forall_legs {P : Idx → Prop} (p q u : Idx) :
    (∀ j, P (FourLegs.legs p q u j)) ↔ P p ∧ P q ∧ P (p - u) ∧ P (q + u) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3

/-- `ρ⁴ / ε⁸ ≤ ρ · ρ^{5/2}` for `0 < ρ ≤ 1`. -/
private lemma HL_key10 {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ρ ^ 4 / epsP ρ ^ 8 ≤ ρ * ρ ^ (5 / 2 : ℝ) := by
  rw [HL_ratio hρ 4 8]
  calc ρ ^ ((4 : ℕ) - (8 : ℕ) / 200 : ℝ) ≤ ρ ^ ((1 : ℝ) + 5 / 2) :=
        Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
    _ = ρ * ρ ^ (5 / 2 : ℝ) := by rw [Real.rpow_add hρ, Real.rpow_one]

/-- Lemma 10.1, (10.2) [4kspecialresult1], (10.3) [4kspecialresult2] and the other coincidences
`k_i = ±k_j`, with a rate. -/
theorem Lemma10_1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc →
      FourLegs.absPart V w .fourSpecial kc N ≤ C * kc ^ 6 * rhoN N := by
  obtain ⟨C₁, hC₁, N₁, h⟩ := HL_tuple10 hV hw
  refine ⟨9 * 4 ^ 6 * C₁, by positivity, max N₁ 1, fun N hN kc hkc => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN2 : N₁ ≤ N := le_of_max_le_left hN
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := by unfold epsP; positivity
  have hL1 : 1 ≤ LN N :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  obtain ⟨F, hF, hFc⟩ := HL_count hL1 hkc
  set T : Finset (Idx × Idx × Idx) := (HL_img F).filter (fun t =>
    inPH (rhoN N) (LN N) t.1 ∧ inPH (rhoN N) (LN N) t.2.1 ∧
      inPH (rhoN N) (LN N) (t.1 - t.2.2) ∧ inPH (rhoN N) (LN N) (t.2.1 + t.2.2)) with hTdef
  set Ψ := trialState V w kc N with hΨ
  set H : Idx × Idx × Idx × Occ → ℝ := fun i =>
    if (i.1, i.2.1, i.2.2.1) ∈ T then ‖Decomp.partTerm .A2 (LN N) V Ψ i‖ else 0 with hH
  set B : ℝ := (LN N ^ 3)⁻¹ * (C₁ * rhoN N ^ 4 / epsP (rhoN N) ^ 8) with hB
  have hT : ∀ i, H i ≠ 0 → (i.1, i.2.1, i.2.2.1) ∈ T := by
    intro i hi
    by_contra hc
    exact hi (by simp [hH, hc])
  have hTb : ∀ t ∈ T, Summable (fun α : Occ => H (t.1, t.2.1, t.2.2, α)) ∧
      ∑' α : Occ, H (t.1, t.2.1, t.2.2, α) ≤ B := by
    intro t ht
    have ht' := (Finset.mem_filter.1 ht).2
    obtain ⟨p, q, u⟩ := t
    obtain ⟨hs, hb⟩ := h N hN2 kc p q u ht'.1 ht'.2.1 ht'.2.2.1 ht'.2.2.2
    have e : ∀ α : Occ, H (p, q, u, α) =
        ‖Decomp.partTerm .A2 (LN N) V Ψ (p, q, u, α)‖ := fun α => by simp [hH, ht]
    simp only [e]
    exact ⟨hs, hb⟩
  obtain ⟨hHs, hHle⟩ := HL_tuples T H hT (fun t ht => (hTb t ht).1) (fun t ht => (hTb t ht).2)
  have hG : ∀ i, (if (FourLegs.Cls.fourSpecial).mem (rhoN N) (LN N) kc N i then
      ‖Decomp.partTerm .A2 (LN N) V Ψ i‖ else 0) ≤ H i := by
    intro i
    by_cases hm : (FourLegs.Cls.fourSpecial).mem (rhoN N) (LN N) kc N i
    · obtain ⟨p, q, u, α⟩ := i
      simp only [hm, ite_true]
      obtain ⟨hall, hng⟩ := hm
      obtain ⟨h1, h2, h3, h4⟩ := (HL_forall_legs (P := inPHc (rhoN N) (LN N) kc) p q u).1 hall
      have hmem : (p, q, u) ∈ T := by
        refine Finset.mem_filter.2 ⟨HL_img_mem (hF p h1.2) (hF q h2.2) (hF _ h3.2) hng,
          h1.1, h2.1, h3.1, h4.1⟩
      simp [hH, hmem]
    · simp only [hm, ite_false]
      by_cases hmem : (i.1, i.2.1, i.2.2.1) ∈ T <;> simp [hH, hmem]
  have hGs : Summable fun i => (if (FourLegs.Cls.fourSpecial).mem (rhoN N) (LN N) kc N i then
      ‖Decomp.partTerm .A2 (LN N) V Ψ i‖ else 0) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs <;> positivity) hG hHs
  have hS : ∑' i, (if (FourLegs.Cls.fourSpecial).mem (rhoN N) (LN N) kc N i then
      ‖Decomp.partTerm .A2 (LN N) V Ψ i‖ else 0) ≤ 9 * (4 * LN N * kc) ^ 6 * B := by
    refine (hGs.tsum_le_tsum hG hHs).trans (hHle.trans ?_)
    have hB0 : 0 ≤ B := by positivity
    have hc1 : (T.card : ℝ) ≤ 9 * (F.card : ℝ) ^ 2 := by
      have hTc : T.card ≤ (HL_img F).card := Finset.card_le_card (Finset.filter_subset _ _)
      exact_mod_cast hTc.trans (HL_img_card F)
    have hc2 : (F.card : ℝ) ^ 2 ≤ (4 * LN N * kc) ^ 6 := by
      calc (F.card : ℝ) ^ 2 ≤ ((4 * LN N * kc) ^ 3) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hFc 2
        _ = (4 * LN N * kc) ^ 6 := by ring
    exact mul_le_mul_of_nonneg_right (hc1.trans (by linarith)) hB0
  unfold FourLegs.absPart
  rw [div_le_iff₀ (by positivity)]
  refine hS.trans ?_
  have hkey := HL_key10 hρ hρ1
  have hM : 0 ≤ C₁ * 9 * 4 ^ 6 * kc ^ 6 * LN N ^ 3 := by positivity
  calc 9 * (4 * LN N * kc) ^ 6 * B
      = C₁ * 9 * 4 ^ 6 * kc ^ 6 * LN N ^ 3 * (rhoN N ^ 4 / epsP (rhoN N) ^ 8) := by
        rw [hB]; field_simp
    _ ≤ C₁ * 9 * 4 ^ 6 * kc ^ 6 * LN N ^ 3 * (rhoN N * rhoN N ^ (5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hkey hM
    _ = 9 * 4 ^ 6 * C₁ * kc ^ 6 * rhoN N * (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ)) := by ring



/-- The four legs of `Gen` as the six pairwise relations. -/
private lemma HL_gen {k₁ k₂ k₃ k₄ : Idx} (hg : FourLegs.Gen ![k₁, k₂, k₃, k₄]) :
    k₁ ≠ k₂ ∧ k₁ ≠ -k₂ ∧ k₁ ≠ k₃ ∧ k₁ ≠ -k₃ ∧ k₁ ≠ k₄ ∧ k₁ ≠ -k₄ ∧ k₂ ≠ k₃ ∧ k₂ ≠ -k₃ ∧
      k₂ ≠ k₄ ∧ k₂ ≠ -k₄ ∧ k₃ ≠ k₄ ∧ k₃ ≠ -k₄ := by
  have g01 := hg 0 1 (by decide)
  have g02 := hg 0 2 (by decide)
  have g03 := hg 0 3 (by decide)
  have g12 := hg 1 2 (by decide)
  have g13 := hg 1 3 (by decide)
  have g23 := hg 2 3 (by decide)
  simp only [Legs_pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val, Matrix.tail_cons] at g01 g02 g03 g12 g13 g23
  exact ⟨g01.1, g01.2, g02.1, g02.2, g03.1, g03.2, g12.1, g12.2, g13.1, g13.2, g23.1, g23.2⟩



/-- The states `𝓐^{v,k₁,k₂} α` and `𝓐^{v,k₃,k₄} α` of `M`, and the matrix element between them. -/
private lemma HL_soft_data {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {k₁ k₂ k₃ k₄ : Idx}
    (hk : inPHc (rhoN N) (LN N) kc k₁ ∧ inPHc (rhoN N) (LN N) kc k₂ ∧
      inPHc (rhoN N) (LN N) kc k₃ ∧ inPHc (rhoN N) (LN N) kc k₄)
    (hg : FourLegs.Gen ![k₁, k₂, k₃, k₄]) (hs : k₁ + k₂ = k₃ + k₄)
    (hv : inPL (rhoN N) (LN N) (k₁ + k₂)) {α : Occ}
    (hα : InMuS (rhoN N) (LN N) kc N (k₁ + k₂) α) (h0 : 1 ≤ α 0) (h1 : 1 ≤ α (k₁ + k₂)) :
    InM (rhoN N) (LN N) kc N (softPair (k₁ + k₂) k₁ k₂ α) ∧
    InM (rhoN N) (LN N) kc N (softPair (k₁ + k₂) k₃ k₄ α) ∧
    (a4 k₁ k₂ k₃ k₄ (softPair (k₁ + k₂) k₃ k₄ α)).2 = softPair (k₁ + k₂) k₁ k₂ α ∧
    (a4 k₁ k₂ k₃ k₄ (softPair (k₁ + k₂) k₃ k₄ α)).1 =
      Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) * ((α k₄ : ℝ) + 1)) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  obtain ⟨⟨hk1, hk1'⟩, ⟨hk2, hk2'⟩, ⟨hk3, hk3'⟩, ⟨hk4, hk4'⟩⟩ := hk
  obtain ⟨hαM, hsym⟩ := hα
  obtain ⟨h12, -, h13, -, h14, -, h23, -, h24, -, h34, -⟩ := HL_gen hg
  have hM1 := InM.soft hαM hv hsym rfl hk1 hk2 hk1' hk2' h0 h1
  have hM2 := InM.soft hαM hv hsym hs.symm hk3 hk4 hk3' hk4' h0 h1
  have hv0 : k₁ + k₂ ≠ 0 := Regions_PL_ne_zero hρ hv
  have hnv : ¬ inPH (rhoN N) (LN N) (k₁ + k₂) := Regions_PL_PH hρ hv
  have n1 := Regions_PH_ne_zero hρ hk1
  have n2 := Regions_PH_ne_zero hρ hk2
  have n3 := Regions_PH_ne_zero hρ hk3
  have n4 := Regions_PH_ne_zero hρ hk4
  have v1 : k₁ ≠ k₁ + k₂ := fun e => hnv (e ▸ hk1)
  have v2 : k₂ ≠ k₁ + k₂ := fun e => hnv (e ▸ hk2)
  have v3 : k₃ ≠ k₁ + k₂ := fun e => hnv (e ▸ hk3)
  have v4 : k₄ ≠ k₁ + k₂ := fun e => hnv (e ▸ hk4)
  refine ⟨hM1, hM2, ?_, ?_⟩
  · simp only [a4, softPair, add_tsub_cancel_right]
    rw [add_right_comm]
  · have hsq := a4_fst_sq k₁ k₂ k₃ k₄ (softPair (k₁ + k₂) k₃ k₄ α)
    have hnn := a4_fst_nonneg k₁ k₂ k₃ k₄ (softPair (k₁ + k₂) k₃ k₄ α)
    have e : ∀ n : Idx, softPair (k₁ + k₂) k₃ k₄ α n = α n - (if n = 0 then 1 else 0) -
        (if n = k₁ + k₂ then 1 else 0) + (if n = k₃ then 1 else 0) + (if n = k₄ then 1 else 0) :=
      fun n => MBasic_softPair_apply _ _ _ _ n
    have g1 : softPair (k₁ + k₂) k₃ k₄ α k₁ = α k₁ := by
      rw [e]; simp [n1, v1, h13, h14]
    have g2 : softPair (k₁ + k₂) k₃ k₄ α k₂ = α k₂ := by
      rw [e]; simp [n2, v2, h23, h24]
    have g3 : softPair (k₁ + k₂) k₃ k₄ α k₃ = α k₃ + 1 := by
      rw [e]; simp [n3, v3, h34]
    have g4 : softPair (k₁ + k₂) k₃ k₄ α k₄ = α k₄ + 1 := by
      rw [e]; simp [n4, v4, Ne.symm h34]
    rw [g1, g2, g3, g4] at hsq
    simp only [h12, h13, h14, h23, h24, h34, ite_false, sub_zero, add_zero] at hsq
    rw [← Real.sqrt_sq hnn, hsq]
    push_cast
    congr 1
    ring



/-- The product `conj Ψ(𝓐^{v,k₁,k₂} α) c Ψ(𝓐^{v,k₃,k₄} α)` of (10.11) [temp8.140]. -/
private lemma HL_term_eq (V w : R3 → ℝ) {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {k₁ k₂ k₃ k₄ : Idx}
    (hk : inPHc (rhoN N) (LN N) kc k₁ ∧ inPHc (rhoN N) (LN N) kc k₂ ∧
      inPHc (rhoN N) (LN N) kc k₃ ∧ inPHc (rhoN N) (LN N) kc k₄)
    (hg : FourLegs.Gen ![k₁, k₂, k₃, k₄]) (hs : k₁ + k₂ = k₃ + k₄)
    (hv : inPL (rhoN N) (LN N) (k₁ + k₂)) {α : Occ}
    (hα : InMuS (rhoN N) (LN N) kc N (k₁ + k₂) α) (h0 : 1 ≤ α 0) (h1 : 1 ≤ α (k₁ + k₂)) :
    conj (trialState V w kc N (softPair (k₁ + k₂) k₁ k₂ α)) *
        (((a4 k₁ k₂ k₃ k₄ (softPair (k₁ + k₂) k₃ k₄ α)).1 : ℝ) : ℂ) *
          trialState V w kc N (softPair (k₁ + k₂) k₃ k₄ α) =
      4 * conj (csqrt (lam V w (rhoN N) (LN N) k₁) * csqrt (lam V w (rhoN N) (LN N) k₂)) *
        (csqrt (lam V w (rhoN N) (LN N) k₃) * csqrt (lam V w (rhoN N) (LN N) k₄)) /
          (((LN N ^ 3) ^ 2 : ℝ) : ℂ) *
        (((α 0 : ℝ) * (α (k₁ + k₂) : ℝ) *
              Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) *
                ((α k₄ : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hM1, hM2, -, hc⟩ := HL_soft_data hN hk hg hs hv hα h0 h1
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  obtain ⟨⟨hk1, -⟩, ⟨hk2, -⟩, ⟨hk3, -⟩, ⟨hk4, -⟩⟩ := hk
  have hαM := hα.1
  have f1 := Lemma5_1_properf4 (V := V) (w := w) hρ hL hv hk1 hk2 rfl hα hM1
  have f2 := Lemma5_1_properf4 (V := V) (w := w) hρ hL hv hk3 hk4 hs.symm hα hM2
  rw [hc]
  simp only [FIdentities_trialState, ite_eq_left hM1, ite_eq_left hM2, ite_eq_left hαM, f1, f2]
  set f := f0 V w (rhoN N) (LN N) α with hf
  set C := CN V w kc N with hC
  set v := k₁ + k₂ with hv'
  set Lr := LN N with hLr
  set r : ℝ := 2 * Real.sqrt ((α 0 : ℝ) / Lr ^ 3) * Real.sqrt ((α v : ℝ) / Lr ^ 3) with hr
  have hr2 : r ^ 2 = 4 * (α 0 : ℝ) * (α v : ℝ) / (Lr ^ 3) ^ 2 := by
    rw [hr, mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    field_simp
    ring
  have hff : conj f * f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']
    push_cast
    rfl
  have hnorm : ‖(C : ℂ) * f‖ ^ 2 = C ^ 2 * ‖f‖ ^ 2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hnorm]
  have hr2c : (r : ℂ) ^ 2 = 4 * (α 0 : ℂ) * (α v : ℂ) / ((Lr : ℂ) ^ 3) ^ 2 := by
    have := congrArg (fun x : ℝ => (x : ℂ)) hr2
    push_cast at this
    exact this
  have hff' : conj f * f = (‖f‖ : ℂ) ^ 2 := by
    rw [hff]; push_cast; rfl
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  set c : ℝ := Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) *
    ((α k₄ : ℝ) + 1)) with hcdef
  set s₁ := csqrt (lam V w (rhoN N) Lr k₁)
  set s₂ := csqrt (lam V w (rhoN N) Lr k₂)
  set s₃ := csqrt (lam V w (rhoN N) Lr k₃)
  set s₄ := csqrt (lam V w (rhoN N) Lr k₄)
  linear_combination ((C : ℂ) ^ 2 * c * (conj s₁ * conj s₂ * s₃ * s₄) * (conj f * f)) * hr2c +
    ((C : ℂ) ^ 2 * c * (conj s₁ * conj s₂ * s₃ * s₄) *
      (4 * (α 0 : ℂ) * (α v : ℂ) / ((Lr : ℂ) ^ 3) ^ 2)) * hff'



/-- `Ψ` vanishes off `M`. -/
private lemma HL_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hM
  exact h (by simp [trialState, hM])

/-- (10.11) [temp8.140], with the complex conjugate of Lemma 7.1 [id4a]: for legs (10.7)
[conditionk2] with `v = k₁ + k₂ ∈ P_L`, the inner sum of (10.10) [resultinMk1k2] equals
`4 conj(√λ_{k₁} √λ_{k₂}) √λ_{k₃} √λ_{k₄} |Λ|^{-2} Σ_{α ∈ M_v^s} α(0) α(v) ∏ √(α(k_i)+1) |Ψ(α)|²`. -/
theorem Eq10_11 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {k₁ k₂ k₃ k₄ : Idx}
    (hk : inPHc (rhoN N) (LN N) kc k₁ ∧ inPHc (rhoN N) (LN N) kc k₂ ∧
      inPHc (rhoN N) (LN N) kc k₃ ∧ inPHc (rhoN N) (LN N) kc k₄)
    (hg : FourLegs.Gen ![k₁, k₂, k₃, k₄]) (hs : k₁ + k₂ = k₃ + k₄)
    (hv : inPL (rhoN N) (LN N) (k₁ + k₂)) :
    FourLegs.mainTuple V w kc N k₁ k₂ k₃ k₄ =
      4 * conj (csqrt (lam V w (rhoN N) (LN N) k₁) * csqrt (lam V w (rhoN N) (LN N) k₂)) *
        (csqrt (lam V w (rhoN N) (LN N) k₃) * csqrt (lam V w (rhoN N) (LN N) k₄)) /
          (((LN N ^ 3) ^ 2 : ℝ) : ℂ) *
        ((∑' α : Occ, if InMuS (rhoN N) (LN N) kc N (k₁ + k₂) α then
            (α 0 : ℝ) * (α (k₁ + k₂) : ℝ) *
              Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) *
                ((α k₄ : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 2 else 0 : ℝ) : ℂ) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hv0 : k₁ + k₂ ≠ 0 := Regions_PL_ne_zero hρ hv
  set S : Set Occ := {α | InMuS (rhoN N) (LN N) kc N (k₁ + k₂) α ∧ 1 ≤ α 0 ∧
    1 ≤ α (k₁ + k₂)} with hS
  set F : Occ → Occ := softPair (k₁ + k₂) k₃ k₄ with hF
  set g : Occ → ℂ := fun γ => if FourLegs.InMk (rhoN N) (LN N) kc N k₁ k₂ (a4 k₁ k₂ k₃ k₄ γ).2 then
    conj (trialState V w kc N (a4 k₁ k₂ k₃ k₄ γ).2) * ((a4 k₁ k₂ k₃ k₄ γ).1 : ℂ) *
      trialState V w kc N γ else 0 with hgdef
  have hmain : FourLegs.mainTuple V w kc N k₁ k₂ k₃ k₄ = ∑' γ, g γ := rfl
  have hinj : Function.Injective (fun a : S => F a.1) := by
    intro a b h
    exact Subtype.ext (Reorder_softPair_injOn hv0 k₃ k₄ ⟨a.2.2.1, a.2.2.2⟩ ⟨b.2.2.1, b.2.2.2⟩ h)
  have hsupp : Function.support g ⊆ Set.range (fun a : S => F a.1) := by
    intro γ hγ
    have hγ' : g γ ≠ 0 := hγ
    by_cases hmk : FourLegs.InMk (rhoN N) (LN N) kc N k₁ k₂ (a4 k₁ k₂ k₃ k₄ γ).2
    · obtain ⟨hβM, -, α, hα, hαβ⟩ := hmk
      simp only [hgdef, ite_eq_left (show FourLegs.InMk (rhoN N) (LN N) kc N k₁ k₂
        (a4 k₁ k₂ k₃ k₄ γ).2 from ⟨hβM, hv, α, hα, hαβ⟩)] at hγ'
      rw [mul_ne_zero_iff, mul_ne_zero_iff] at hγ'
      obtain ⟨⟨-, hc⟩, hΨγ⟩ := hγ'
      have hc' : (a4 k₁ k₂ k₃ k₄ γ).1 ≠ 0 := by
        intro h0; apply hc; simp [h0]
      have hγM := HL_inM hΨγ
      have h109 := Eq10_9 hρ hα.1 hβM hγM hc' rfl
      have hγeq : softPair (k₁ + k₂) k₃ k₄ α = γ := by
        have := h109.2.1 hαβ
        rwa [← hs] at this
      have hβ' : InM (rhoN N) (LN N) kc N (softPair (k₁ + k₂) k₁ k₂ α) := by rw [hαβ]; exact hβM
      obtain ⟨h0, h1⟩ := MBasic_soft_le hρ hα.1 hβ'
      exact ⟨⟨α, hα, h0, h1⟩, hγeq⟩
    · exact absurd (by simp [hgdef, hmk]) hγ'
  rw [hmain, ← hinj.tsum_eq hsupp, tsum_subtype S (fun α => g (F α))]
  set K : ℂ := 4 * conj (csqrt (lam V w (rhoN N) (LN N) k₁) * csqrt (lam V w (rhoN N) (LN N) k₂)) *
    (csqrt (lam V w (rhoN N) (LN N) k₃) * csqrt (lam V w (rhoN N) (LN N) k₄)) /
      (((LN N ^ 3) ^ 2 : ℝ) : ℂ) with hK
  have hpt : ∀ α : Occ, S.indicator (fun α => g (F α)) α =
      K * ((if InMuS (rhoN N) (LN N) kc N (k₁ + k₂) α then
            (α 0 : ℝ) * (α (k₁ + k₂) : ℝ) *
              Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) *
                ((α k₄ : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 2 else 0 : ℝ) : ℂ) := by
    intro α
    by_cases hαS : α ∈ S
    · obtain ⟨hα, h0, h1⟩ := hαS
      rw [Set.indicator_of_mem (show α ∈ S from ⟨hα, h0, h1⟩)]
      obtain ⟨hM1, hM2, hb, -⟩ := HL_soft_data hN hk hg hs hv hα h0 h1
      have hmk : FourLegs.InMk (rhoN N) (LN N) kc N k₁ k₂
          (a4 k₁ k₂ k₃ k₄ (softPair (k₁ + k₂) k₃ k₄ α)).2 := by
        rw [hb]
        exact ⟨hM1, hv, α, hα, rfl⟩
      simp only [hgdef, hF]
      rw [ite_eq_left hmk, ite_eq_left hα]
      rw [hb]
      exact HL_term_eq V w hN hk hg hs hv hα h0 h1
    · rw [Set.indicator_of_notMem hαS]
      by_cases hα : InMuS (rhoN N) (LN N) kc N (k₁ + k₂) α
      · have : α 0 = 0 ∨ α (k₁ + k₂) = 0 := by
          by_contra hc
          push Not at hc
          exact hαS ⟨hα, Nat.one_le_iff_ne_zero.2 hc.1, Nat.one_le_iff_ne_zero.2 hc.2⟩
        rcases this with h | h <;> simp [hα, h]
      · simp [hα]
  simp only [hpt]
  rw [tsum_mul_left, Complex.ofReal_tsum]



/-- `√A √B ≤ √C₁ √C₂ x y` from `A ≤ C₁ x²` and `B ≤ C₂ y²`. -/
private lemma HL_sqrt_prod {A B C₁ C₂ x y : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hA : A ≤ C₁ * x ^ 2) (hB : B ≤ C₂ * y ^ 2) :
    Real.sqrt A * Real.sqrt B ≤ Real.sqrt C₁ * Real.sqrt C₂ * (x * y) := by
  have h1 : Real.sqrt A ≤ Real.sqrt C₁ * x := by
    calc Real.sqrt A ≤ Real.sqrt (C₁ * x ^ 2) := Real.sqrt_le_sqrt hA
      _ = Real.sqrt C₁ * x := by rw [Real.sqrt_mul hC₁, Real.sqrt_sq hx]
  have h2 : Real.sqrt B ≤ Real.sqrt C₂ * y := by
    calc Real.sqrt B ≤ Real.sqrt (C₂ * y ^ 2) := Real.sqrt_le_sqrt hB
      _ = Real.sqrt C₂ * y := by rw [Real.sqrt_mul hC₂, Real.sqrt_sq hy]
  calc Real.sqrt A * Real.sqrt B ≤ (Real.sqrt C₁ * x) * (Real.sqrt C₂ * y) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = Real.sqrt C₁ * Real.sqrt C₂ * (x * y) := by ring

/-- `α(v₁) + 1 ≤ β(v₁)` for `β = a†_{v₁} a†_{v₂} a_{v₃} a_{v₄} α` and `v₁ ∉ {v₃, v₄}`. -/
private lemma HL_a4_snd_ge {v₁ v₂ v₃ v₄ : Idx} (h13 : v₁ ≠ v₃) (h14 : v₁ ≠ v₄) (α : Occ) :
    α v₁ + 1 ≤ (a4 v₁ v₂ v₃ v₄ α).2 v₁ := by
  simp only [a4, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply]
  rw [ite_eq_right (Ne.symm h13), ite_eq_right (Ne.symm h14)]
  split_ifs <;> omega



/-- Terms with `α(v₃) ≥ 4`: the norm `‖a_{v₃} a_{v₄} Ψ‖` restricted to `α(v₃) ≥ 4` is small
by (5.41) [boundpsiuvmn], and `‖a_{v₁} a_{v₂} Ψ‖` by (5.42) [boundpsifixeduv]. -/
private lemma HL_tailA {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ v₁ v₂ v₃ v₄ : Idx,
      inPH (rhoN N) (LN N) v₁ → inPH (rhoN N) (LN N) v₂ → inPH (rhoN N) (LN N) v₃ →
      inPH (rhoN N) (LN N) v₄ → v₁ + v₂ ≠ 0 → v₃ ≠ v₄ → v₃ + v₄ ≠ 0 →
      ∑' α : Occ, (if 4 ≤ α v₃ then
        ‖conj (trialState V w kc N (a4 v₁ v₂ v₃ v₄ α).2) * ((a4 v₁ v₂ v₃ v₄ α).1 : ℂ) *
          trialState V w kc N α‖ else 0) ≤ C * rhoN N ^ 7 / epsP (rhoN N) ^ 14 := by
  obtain ⟨C₁, hC₁, N₁, h1⟩ := HL_pair hV hw
  obtain ⟨C₂, hC₂, N₂, h2⟩ := HL_pair_tail hV hw
  refine ⟨Real.sqrt C₁ * Real.sqrt C₂, by positivity, max N₁ (max N₂ 1), fun N hN kc v₁ v₂ v₃ v₄
    hp₁ hp₂ hp₃ hp₄ h12 h34 h34' => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂ : N₂ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := by unfold epsP; positivity
  have hΨ := Normalization_isNState V w kc hN1
  have hsch := HL_schwarz hΨ v₁ v₂ v₃ v₄ (fun α => 4 ≤ α v₃) (fun _ => True)
    (fun α => 4 ≤ α v₃) (fun α hP _ => ⟨trivial, hP⟩)
  have e1 : (∑' β : Occ, if True then
      ((β v₁ : ℝ) * β v₂ - if v₁ = v₂ then (β v₁ : ℝ) else 0) * ‖trialState V w kc N β‖ ^ 2
        else 0) ≤ C₁ * (rhoN N ^ 2 / epsP (rhoN N) ^ 4) ^ 2 := by
    simp only [ite_true]
    refine (h1 N hN₁ kc v₁ v₂ hp₁ hp₂ h12).trans (le_of_eq ?_)
    field_simp
  have e2 : (∑' α : Occ, if 4 ≤ α v₃ then
      ((α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0) * ‖trialState V w kc N α‖ ^ 2
        else 0) ≤ C₂ * (rhoN N ^ 5 / epsP (rhoN N) ^ 10) ^ 2 := by
    refine le_trans (le_of_eq ?_) ((h2 N hN₂ kc v₃ v₄ hp₃ hp₄ h34 h34').trans (le_of_eq ?_))
    · congr 1
      funext α
      simp [h34, mul_assoc]
    · field_simp
  refine hsch.trans ?_
  refine (HL_sqrt_prod hC₁ hC₂ (by positivity) (by positivity) e1 e2).trans (le_of_eq ?_)
  field_simp

/-- Terms with `α(v₁) ≥ 4`, for `v₁ ∉ {v₃, v₄}`: then `β(v₁) ≥ 4`, and the norm
`‖a_{v₁} a_{v₂} Ψ‖` restricted to `β(v₁) ≥ 4` is small by (5.41) [boundpsiuvmn]. -/
private lemma HL_tailB {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ v₁ v₂ v₃ v₄ : Idx,
      inPH (rhoN N) (LN N) v₁ → inPH (rhoN N) (LN N) v₂ → inPH (rhoN N) (LN N) v₃ →
      inPH (rhoN N) (LN N) v₄ → v₁ ≠ v₂ → v₁ + v₂ ≠ 0 → v₃ + v₄ ≠ 0 → v₁ ≠ v₃ → v₁ ≠ v₄ →
      ∑' α : Occ, (if 4 ≤ α v₁ then
        ‖conj (trialState V w kc N (a4 v₁ v₂ v₃ v₄ α).2) * ((a4 v₁ v₂ v₃ v₄ α).1 : ℂ) *
          trialState V w kc N α‖ else 0) ≤ C * rhoN N ^ 7 / epsP (rhoN N) ^ 14 := by
  obtain ⟨C₁, hC₁, N₁, h1⟩ := HL_pair hV hw
  obtain ⟨C₂, hC₂, N₂, h2⟩ := HL_pair_tail hV hw
  refine ⟨Real.sqrt C₁ * Real.sqrt C₂, by positivity, max N₁ (max N₂ 1), fun N hN kc v₁ v₂ v₃ v₄
    hp₁ hp₂ hp₃ hp₄ h12 h12' h34' h13 h14 => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN₂ : N₂ ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := by unfold epsP; positivity
  have hΨ := Normalization_isNState V w kc hN1
  have hsch := HL_schwarz hΨ v₁ v₂ v₃ v₄ (fun α => 4 ≤ α v₁) (fun β => 4 ≤ β v₁)
    (fun _ => True) (fun α hP _ => ⟨by
      have := HL_a4_snd_ge (v₂ := v₂) h13 h14 α
      omega, trivial⟩)
  have e1 : (∑' β : Occ, if 4 ≤ β v₁ then
      ((β v₁ : ℝ) * β v₂ - if v₁ = v₂ then (β v₁ : ℝ) else 0) * ‖trialState V w kc N β‖ ^ 2
        else 0) ≤ C₂ * (rhoN N ^ 5 / epsP (rhoN N) ^ 10) ^ 2 := by
    refine le_trans (le_of_eq ?_) ((h2 N hN₂ kc v₁ v₂ hp₁ hp₂ h12 h12').trans (le_of_eq ?_))
    · congr 1
      funext α
      simp [h12, mul_assoc]
    · field_simp
  have e2 : (∑' α : Occ, if True then
      ((α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0) * ‖trialState V w kc N α‖ ^ 2
        else 0) ≤ C₁ * (rhoN N ^ 2 / epsP (rhoN N) ^ 4) ^ 2 := by
    simp only [ite_true]
    refine (h1 N hN₁ kc v₃ v₄ hp₃ hp₄ h34').trans (le_of_eq ?_)
    field_simp
  refine hsch.trans ?_
  refine (HL_sqrt_prod hC₂ hC₁ (by positivity) (by positivity) e1 e2).trans (le_of_eq ?_)
  field_simp



/-- The restricted sum of `‖partTerm‖` over `α` for one tuple, from the restricted Schwarz bound. -/
private lemma HL_tail_sum {V w : R3 → ℝ} {V₀ : ℝ} (hV₀ : ∀ p, ‖ft V p‖ ≤ V₀) {kc : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (p q u a : Idx) {M : ℝ}
    (hM : ∑' α : Occ, (if 4 ≤ α a then
      ‖conj (trialState V w kc N (a4 p q (p - u) (q + u) α).2) *
        ((a4 p q (p - u) (q + u) α).1 : ℂ) * trialState V w kc N α‖ else 0) ≤ M) :
    Summable (fun α : Occ => if 4 ≤ α a then
        ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ else 0) ∧
      ∑' α : Occ, (if 4 ≤ α a then
        ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ else 0) ≤
        (LN N ^ 3)⁻¹ * V₀ * M := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hV0 : 0 ≤ V₀ := (norm_nonneg _).trans (hV₀ 0)
  have hΨ := Normalization_isNState V w kc hN
  have hsum := Expect.id4a_summable N _ hΨ p q (p - u) (q + u)
  set X : Occ → ℝ := fun α => ‖conj (trialState V w kc N (a4 p q (p - u) (q + u) α).2) *
        ((a4 p q (p - u) (q + u) α).1 : ℂ) * trialState V w kc N α‖ with hX
  have hX0 : ∀ α, 0 ≤ X α := fun α => norm_nonneg _
  have hsumI : Summable fun α : Occ => if 4 ≤ α a then X α else 0 :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> simp [hX0 α])
      (fun α => by split_ifs <;> simp [hX0 α]) hsum
  have hle : ∀ α : Occ, (if 4 ≤ α a then
      ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ else 0) ≤
      (LN N ^ 3)⁻¹ * V₀ * (if 4 ≤ α a then X α else 0) := by
    intro α
    by_cases h : 4 ≤ α a
    · simp only [h, ite_true]
      exact HL_partTerm_le hV₀ hL _ (p, q, u, α)
    · simp [h]
  have h0 : ∀ α : Occ, 0 ≤ (if 4 ≤ α a then
      ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ else 0) := fun α => by
    split_ifs <;> simp
  have hs' := Summable.of_nonneg_of_le h0 hle (hsumI.mul_left ((LN N ^ 3)⁻¹ * V₀))
  refine ⟨hs', (hs'.tsum_le_tsum hle (hsumI.mul_left _)).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hM (by positivity)

/-- The four sums with an occupation `≥ 4` for one tuple with legs (10.7) [conditionk2] in `P_H`. -/
private lemma HL_tuple11 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ p q u : Idx,
      inPH (rhoN N) (LN N) p → inPH (rhoN N) (LN N) q → inPH (rhoN N) (LN N) (p - u) →
      inPH (rhoN N) (LN N) (q + u) → FourLegs.Gen (FourLegs.legs p q u) →
      ∀ a ∈ ({p, q, p - u, q + u} : Finset Idx),
      Summable (fun α : Occ => if 4 ≤ α a then
        ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ else 0) ∧
      ∑' α : Occ, (if 4 ≤ α a then
        ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ else 0) ≤
        (LN N ^ 3)⁻¹ * (C * rhoN N ^ 7 / epsP (rhoN N) ^ 14) := by
  obtain ⟨V₀, hV₀⟩ := HL_ftV_bdd hV
  have hV0 : 0 ≤ V₀ := (norm_nonneg _).trans (hV₀ 0)
  obtain ⟨CA, hCA, NA, hA⟩ := HL_tailA hV hw
  obtain ⟨CB, hCB, NB, hB⟩ := HL_tailB hV hw
  refine ⟨V₀ * max CA CB, by positivity, max NA (max NB 1),
    fun N hN kc p q u hp hq hpu hqu hg a ha => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  have hNA : NA ≤ N := le_trans (le_max_left _ _) hN
  have hNB : NB ≤ N := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN)
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := by unfold epsP; positivity
  obtain ⟨g12, g12', g13, g13', g14, g14', g23, g23', g24, g24', g34, g34'⟩ := HL_gen hg
  have hpq : p + q ≠ 0 := fun h => g12' (by rw [eq_neg_iff_add_eq_zero]; exact h)
  have hqp : q + p ≠ 0 := by rw [add_comm]; exact hpq
  have hsum34 : (p - u) + (q + u) ≠ 0 := by
    have : (p - u) + (q + u) = p + q := by abel
    rw [this]; exact hpq
  have hsum43 : (q + u) + (p - u) ≠ 0 := by rw [add_comm]; exact hsum34
  have hM0 : 0 ≤ max CA CB * rhoN N ^ 7 / epsP (rhoN N) ^ 14 := by positivity
  have e : (LN N ^ 3)⁻¹ * V₀ * (max CA CB * rhoN N ^ 7 / epsP (rhoN N) ^ 14) =
      (LN N ^ 3)⁻¹ * (V₀ * max CA CB * rhoN N ^ 7 / epsP (rhoN N) ^ 14) := by ring
  rw [← e]
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with h | h | h | h <;> rw [h]
  · refine HL_tail_sum hV₀ hN1 p q u _
      ((hB N hNB kc p q (p - u) (q + u) hp hq hpu hqu g12 hpq hsum34 g13 g14).trans ?_)
    gcongr
    exact le_max_right _ _
  · have h := hB N hNB kc q p (q + u) (p - u) hq hp hqu hpu (Ne.symm g12) hqp hsum43 g24 g23
    simp only [a4_comm q p (q + u) (p - u)] at h
    refine HL_tail_sum hV₀ hN1 p q u _ (h.trans ?_)
    gcongr
    exact le_max_right _ _
  · refine HL_tail_sum hV₀ hN1 p q u _ ((hA N hNA kc p q (p - u) (q + u) hp hq hpu hqu hpq g34
      hsum34).trans ?_)
    gcongr
    exact le_max_left _ _
  · have h := hA N hNA kc q p (q + u) (p - u) hq hp hqu hpu hqp (Ne.symm g34) hsum43
    simp only [a4_comm q p (q + u) (p - u)] at h
    refine HL_tail_sum hV₀ hN1 p q u _ (h.trans ?_)
    gcongr
    exact le_max_left _ _



/-- The exponent arithmetic of the tail bound of Lemma 11.1 [113]: `|Λ|^{-1} ρ^{-5/2} = ρ^{5/8}`,
`|Λ| ρ^{9/2} ε^{-14} = ρ^{261/200}` and `ρ^{9/2} ρ^{5/2} = ρ^7`. -/
private lemma HL_exp11 {N : ℕ} (hN : 1 ≤ N) :
    (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ))⁻¹ = rhoN N ^ (5 / 8 : ℝ) ∧
    LN N ^ 3 * rhoN N ^ (9 / 2 : ℝ) / epsP (rhoN N) ^ 14 = rhoN N ^ (261 / 200 : ℝ) ∧
    rhoN N ^ (9 / 2 : ℝ) * rhoN N ^ (5 / 2 : ℝ) = rhoN N ^ 7 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hL3 := HL_L3 hN
  refine ⟨?_, ?_, ?_⟩
  · rw [hL3, ← Real.rpow_add hρ, ← Real.rpow_neg hρ.le]
    congr 1
    norm_num
  · rw [hL3, ← Real.rpow_add hρ, ← HL_rpow_eps hρ.le 14 rfl, ← Real.rpow_sub hρ]
    congr 1
    norm_num
  · rw [← Real.rpow_add hρ, ← Real.rpow_natCast]
    congr 1
    norm_num



/-- The coefficient of `a†_{v₁} a†_{v₂} a_{v₃} a_{v₄}` is at most `12` when all occupations
at the pairwise different legs are at most `3`. -/
private lemma HL_coeff_le {v₁ v₂ v₃ v₄ : Idx} (h12 : v₁ ≠ v₂) (h13 : v₁ ≠ v₃) (h14 : v₁ ≠ v₄)
    (h23 : v₂ ≠ v₃) (h24 : v₂ ≠ v₄) (h34 : v₃ ≠ v₄) (α : Occ) (a1 : α v₁ ≤ 3) (a2 : α v₂ ≤ 3)
    (a3 : α v₃ ≤ 3) (a4' : α v₄ ≤ 3) : (a4 v₁ v₂ v₃ v₄ α).1 ≤ 12 := by
  have hsq := a4_fst_sq v₁ v₂ v₃ v₄ α
  have hnn := a4_fst_nonneg v₁ v₂ v₃ v₄ α
  simp only [h12, h13, h14, h23, h24, h34, ite_false, sub_zero, add_zero] at hsq
  have b1 : (α v₁ : ℝ) ≤ 3 := by exact_mod_cast a1
  have b2 : (α v₂ : ℝ) ≤ 3 := by exact_mod_cast a2
  have b3 : (α v₃ : ℝ) ≤ 3 := by exact_mod_cast a3
  have b4 : (α v₄ : ℝ) ≤ 3 := by exact_mod_cast a4'
  have p1 : (0 : ℝ) ≤ α v₁ := Nat.cast_nonneg _
  have p2 : (0 : ℝ) ≤ α v₂ := Nat.cast_nonneg _
  have p3 : (0 : ℝ) ≤ α v₃ := Nat.cast_nonneg _
  have p4 : (0 : ℝ) ≤ α v₄ := Nat.cast_nonneg _
  have h144 : (a4 v₁ v₂ v₃ v₄ α).1 ^ 2 ≤ 12 ^ 2 := by
    rw [hsq]
    have e1 : (α v₄ : ℝ) * α v₃ ≤ 9 := by nlinarith
    have e2 : ((α v₂ : ℝ) + 1) * ((α v₁ : ℝ) + 1) ≤ 16 := by nlinarith
    calc (α v₄ : ℝ) * α v₃ * ((α v₂ : ℝ) + 1) * ((α v₁ : ℝ) + 1)
        = ((α v₄ : ℝ) * α v₃) * (((α v₂ : ℝ) + 1) * ((α v₁ : ℝ) + 1)) := by ring
      _ ≤ 9 * 16 := mul_le_mul e1 e2 (by positivity) (by norm_num)
      _ ≤ 12 ^ 2 := by norm_num
  exact (pow_le_pow_iff_left₀ hnn (by norm_num) (by norm_num)).1 h144



/-- Lemma 11.1 [113] from Lemma 11.2 [thehardestlemma] (proof of Lemma 11.1, with (5.41)
[boundpsiuvmn] and (5.42) [boundpsifixeduv] for the occupations above `3`). -/
theorem Lemma11_1_of_Lemma11_2 {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) (h : Stmt.Lemma11_2 V w) : Stmt.Lemma11_1 V w := by
  obtain ⟨V₀, hV₀⟩ := HL_ftV_bdd hV
  have hV0 : 0 ≤ V₀ := (norm_nonneg _).trans (hV₀ 0)
  obtain ⟨C₁, hC₁, N₁, h11⟩ := HL_tuple11 hV hw
  intro kc
  set K : ℝ := max kc 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  set A : ℝ := 4 ^ 10 * K ^ 9 * C₁ with hA
  have hA0 : 0 ≤ A := by positivity
  have hev1 : ∀ᶠ N : ℕ in atTop, 12 * V₀ * rhoN N ^ (1 / 8 : ℝ) ≤ 1 / 2 := by
    have h0 : Tendsto (fun N : ℕ => 12 * V₀ * rhoN N ^ (1 / 8 : ℝ)) atTop (𝓝 0) := by
      simpa using (HL_tendsto (a := 1 / 8) (by norm_num)).const_mul (12 * V₀)
    exact (h0.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).mono fun _ h => h.le
  have hev2 : ∀ᶠ N : ℕ in atTop, A * rhoN N ^ (161 / 200 : ℝ) ≤ 1 / 2 := by
    have h0 : Tendsto (fun N : ℕ => A * rhoN N ^ (161 / 200 : ℝ)) atTop (𝓝 0) := by
      simpa using (HL_tendsto (a := 161 / 200) (by norm_num)).const_mul A
    exact (h0.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)).mono fun _ h => h.le
  filter_upwards [h kc, eventually_ge_atTop N₁, eventually_ge_atTop 1, hev1, hev2] with N hh hN₁
    hN1 e1 e2
  obtain ⟨hhs, hhle⟩ := hh
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := by unfold epsP; positivity
  have hL1 : 1 ≤ LN N := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  obtain ⟨F, hF, hFc⟩ := HL_count hL1 hK1
  set T : Finset (Idx × Idx × Idx) :=
    ((F ×ˢ F ×ˢ F).image (fun x => (x.1, x.2.1, x.1 - x.2.2))).filter (fun t =>
      inPH (rhoN N) (LN N) t.1 ∧ inPH (rhoN N) (LN N) t.2.1 ∧
        inPH (rhoN N) (LN N) (t.1 - t.2.2) ∧ inPH (rhoN N) (LN N) (t.2.1 + t.2.2) ∧
          FourLegs.Gen (FourLegs.legs t.1 t.2.1 t.2.2)) with hT
  set B : ℝ := (LN N ^ 3)⁻¹ * (C₁ * rhoN N ^ 7 / epsP (rhoN N) ^ 14) with hB
  have hB0 : 0 ≤ B := by positivity
  set Tl : Fin 4 → Idx × Idx × Idx × Occ → ℝ := fun j i =>
    if (i.1, i.2.1, i.2.2.1) ∈ T then
      (if 4 ≤ i.2.2.2 (FourLegs.legs i.1 i.2.1 i.2.2.1 j) then
        ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i‖ else 0) else 0 with hTl
  have hTl0 : ∀ j i, 0 ≤ Tl j i := fun j i => by
    simp only [hTl]; split_ifs <;> simp
  have hTlb : ∀ j : Fin 4, Summable (Tl j) ∧ ∑' i, Tl j i ≤ T.card * B := by
    intro j
    refine HL_tuples T (Tl j) (fun i hi => ?_) (fun t ht => ?_) (fun t ht => ?_)
    · by_contra hc
      exact hi (by simp [hTl, hc])
    · obtain ⟨p, q, u⟩ := t
      obtain ⟨hp, hq, hpu, hqu, hg⟩ := (Finset.mem_filter.1 ht).2
      have hmem : FourLegs.legs p q u j ∈ ({p, q, p - u, q + u} : Finset Idx) := by
        fin_cases j <;> simp [FourLegs.legs]
      have := (h11 N hN₁ kc p q u hp hq hpu hqu hg _ hmem).1
      refine this.congr fun α => ?_
      simp [hTl, ht]
    · obtain ⟨p, q, u⟩ := t
      obtain ⟨hp, hq, hpu, hqu, hg⟩ := (Finset.mem_filter.1 ht).2
      have hmem : FourLegs.legs p q u j ∈ ({p, q, p - u, q + u} : Finset Idx) := by
        fin_cases j <;> simp [FourLegs.legs]
      have := (h11 N hN₁ kc p q u hp hq hpu hqu hg _ hmem).2
      refine le_trans (le_of_eq ?_) this
      congr 1
      funext α
      simp [hTl, ht]
  set Bk : Idx × Idx × Idx × Occ → ℝ := fun i =>
    (LN N ^ 3)⁻¹ * V₀ * 12 * FourLegs.hardTerm V w kc N i with hBk
  have hhard0 : ∀ i, 0 ≤ FourLegs.hardTerm V w kc N i := fun i => by
    unfold FourLegs.hardTerm; split_ifs <;> positivity
  have hBk0 : ∀ i, 0 ≤ Bk i := fun i => by
    have := hhard0 i
    simp only [hBk]; positivity
  have hBks : Summable Bk := hhs.mul_left _
  have hBkle : ∑' i, Bk i ≤ 12 * V₀ := by
    simp only [hBk]
    rw [tsum_mul_left]
    calc (LN N ^ 3)⁻¹ * V₀ * 12 * ∑' i, FourLegs.hardTerm V w kc N i
        ≤ (LN N ^ 3)⁻¹ * V₀ * 12 * LN N ^ 3 :=
          mul_le_mul_of_nonneg_left hhle (by positivity)
      _ = 12 * V₀ := by field_simp
  set G : Idx × Idx × Idx × Occ → ℝ := fun i =>
    if (FourLegs.Cls.fourRest).mem (rhoN N) (LN N) kc N i then
      ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i‖ else 0 with hG
  have hG0 : ∀ i, 0 ≤ G i := fun i => by simp only [hG]; split_ifs <;> simp
  have hGle : ∀ i, G i ≤ Bk i + ∑ j : Fin 4, Tl j i := by
    intro i
    have hsum0 : 0 ≤ ∑ j : Fin 4, Tl j i := Finset.sum_nonneg fun j _ => hTl0 j i
    by_cases hm : (FourLegs.Cls.fourRest).mem (rhoN N) (LN N) kc N i
    swap
    · simp only [hG, hm, ite_false]
      exact add_nonneg (hBk0 i) hsum0
    have hm' := hm
    obtain ⟨p, q, u, α⟩ := i
    simp only [hG, hm, ite_true]
    obtain ⟨hall, hg, hnmk⟩ := hm
    obtain ⟨h1, h2, h3, h4⟩ := (HL_forall_legs (P := inPHc (rhoN N) (LN N) kc) p q u).1 hall
    have hmemT : (p, q, u) ∈ T := by
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(p, q, p - u), ?_, ?_⟩, h1.1, h2.1, h3.1,
        h4.1, hg⟩
      · simp only [Finset.mem_product]
        exact ⟨hF p (h1.2.trans (le_max_left _ _)), hF q (h2.2.trans (le_max_left _ _)),
          hF _ (h3.2.trans (le_max_left _ _))⟩
      · simp
    by_cases hb : ∀ j : Fin 4, α (FourLegs.legs p q u j) ≤ 3
    · obtain ⟨g12, -, g13, -, g14, -, g23, -, g24, -, g34, -⟩ := HL_gen hg
      have hc12 := HL_coeff_le g12 g13 g14 g23 g24 g34 α (by simpa [FourLegs.legs] using hb 0)
        (by simpa [FourLegs.legs] using hb 1) (by simpa [FourLegs.legs] using hb 2)
        (by simpa [FourLegs.legs] using hb 3)
      have hpt := HL_partTerm_le hV₀ hL (trialState V w kc N) (p, q, u, α)
      simp only at hpt
      have hc0 := a4_fst_nonneg p q (p - u) (q + u) α
      set c := (a4 p q (p - u) (q + u) α).1 with hcdef
      have hnorm : ‖conj (trialState V w kc N (a4 p q (p - u) (q + u) α).2) * ((c : ℝ) : ℂ) *
          trialState V w kc N α‖ = ‖trialState V w kc N (a4 p q (p - u) (q + u) α).2‖ * c *
            ‖trialState V w kc N α‖ := by
        rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg hc0]
      rw [hnorm] at hpt
      have hBk' : (LN N ^ 3)⁻¹ * V₀ * (‖trialState V w kc N (a4 p q (p - u) (q + u) α).2‖ * c *
          ‖trialState V w kc N α‖) ≤ Bk (p, q, u, α) := by
        by_cases hc : c = 0
        · rw [hc]; simp only [mul_zero, zero_mul]; exact hBk0 _
        · have hh : FourLegs.hardTerm V w kc N (p, q, u, α) =
              ‖trialState V w kc N (a4 p q (p - u) (q + u) α).2‖ * ‖trialState V w kc N α‖ := by
            unfold FourLegs.hardTerm
            rw [ite_eq_left ⟨hm', hc⟩]
          simp only [hBk, hh]
          have hx : 0 ≤ ‖trialState V w kc N (a4 p q (p - u) (q + u) α).2‖ := norm_nonneg _
          have hy : 0 ≤ ‖trialState V w kc N α‖ := norm_nonneg _
          have : ‖trialState V w kc N (a4 p q (p - u) (q + u) α).2‖ * c *
              ‖trialState V w kc N α‖ ≤ 12 * (‖trialState V w kc N
                (a4 p q (p - u) (q + u) α).2‖ * ‖trialState V w kc N α‖) := by
            nlinarith [mul_nonneg hx hy]
          calc (LN N ^ 3)⁻¹ * V₀ * (‖trialState V w kc N (a4 p q (p - u) (q + u) α).2‖ * c *
                ‖trialState V w kc N α‖)
              ≤ (LN N ^ 3)⁻¹ * V₀ * (12 * (‖trialState V w kc N
                (a4 p q (p - u) (q + u) α).2‖ * ‖trialState V w kc N α‖)) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = _ := by ring
      linarith
    · push Not at hb
      obtain ⟨j, hj⟩ := hb
      have hTlj : Tl j (p, q, u, α) =
          ‖Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α)‖ := by
        simp [hTl, hmemT, show 4 ≤ α (FourLegs.legs p q u j) from hj]
      have : Tl j (p, q, u, α) ≤ ∑ j : Fin 4, Tl j (p, q, u, α) :=
        Finset.single_le_sum (fun j _ => hTl0 j _) (Finset.mem_univ j)
      linarith [hBk0 (p, q, u, α)]
  have hGs : Summable G :=
    Summable.of_nonneg_of_le hG0 hGle (hBks.add (summable_sum fun j _ => (hTlb j).1))
  have hsumle : ∑' i, G i ≤ 12 * V₀ + 4 * ((T.card : ℝ) * B) := by
    calc ∑' i, G i ≤ ∑' i, (Bk i + ∑ j : Fin 4, Tl j i) :=
          hGs.tsum_le_tsum hGle (hBks.add (summable_sum fun j _ => (hTlb j).1))
      _ = (∑' i, Bk i) + ∑ j : Fin 4, ∑' i, Tl j i := by
          rw [hBks.tsum_add (summable_sum fun j _ => (hTlb j).1),
            Summable.tsum_finsetSum fun j _ => (hTlb j).1]
      _ ≤ 12 * V₀ + ∑ j : Fin 4, ((T.card : ℝ) * B) :=
          add_le_add hBkle (Finset.sum_le_sum fun j _ => (hTlb j).2)
      _ = 12 * V₀ + 4 * ((T.card : ℝ) * B) := by simp
  have hTc : (T.card : ℝ) ≤ (4 * LN N * K) ^ 9 := by
    have h1 : T.card ≤ F.card ^ 3 := by
      calc T.card ≤ ((F ×ˢ F ×ˢ F).image (fun x => (x.1, x.2.1, x.1 - x.2.2))).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
        _ ≤ (F ×ˢ F ×ˢ F).card := Finset.card_image_le
        _ = F.card ^ 3 := by simp [Finset.card_product]; ring
    calc (T.card : ℝ) ≤ (F.card : ℝ) ^ 3 := by exact_mod_cast h1
      _ ≤ ((4 * LN N * K) ^ 3) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hFc 3
      _ = (4 * LN N * K) ^ 9 := by ring
  obtain ⟨hZ, hY, hρ7⟩ := HL_exp11 hN1
  unfold FourLegs.absPart
  rw [div_le_iff₀ (by positivity)]
  refine hsumle.trans ?_
  have hZpos : 0 < LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ) := by positivity
  have hZ1 : rhoN N ^ (5 / 8 : ℝ) * (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ)) = 1 := by
    rw [← hZ]; exact inv_mul_cancel₀ hZpos.ne'
  have hT2 : 4 * ((4 * LN N * K) ^ 9 * B) =
      A * rhoN N ^ (261 / 200 : ℝ) * (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ)) := by
    rw [← hY, hA, hB]
    have : A * (LN N ^ 3 * rhoN N ^ (9 / 2 : ℝ) / epsP (rhoN N) ^ 14) *
        (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ)) =
        A * LN N ^ 6 * (rhoN N ^ (9 / 2 : ℝ) * rhoN N ^ (5 / 2 : ℝ)) / epsP (rhoN N) ^ 14 := by
      ring
    rw [hA] at this
    rw [this, hρ7]
    field_simp
  have hR : rhoN N ^ (5 / 8 : ℝ) = rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (1 / 8 : ℝ) := by
    rw [← Real.rpow_add hρ]; norm_num
  have hR' : rhoN N ^ (261 / 200 : ℝ) = rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (161 / 200 : ℝ) := by
    rw [← Real.rpow_add hρ]; norm_num
  have hpos : 0 ≤ rhoN N ^ (1 / 2 : ℝ) := by positivity
  calc 12 * V₀ + 4 * ((T.card : ℝ) * B) ≤ 12 * V₀ + 4 * ((4 * LN N * K) ^ 9 * B) := by
        have := mul_le_mul_of_nonneg_right hTc hB0
        linarith
    _ = (12 * V₀ * rhoN N ^ (5 / 8 : ℝ) + A * rhoN N ^ (261 / 200 : ℝ)) *
          (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ)) := by
        rw [hT2]
        have : 12 * V₀ = 12 * V₀ * (rhoN N ^ (5 / 8 : ℝ) * (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ))) := by
          rw [hZ1, mul_one]
        conv_lhs => rw [this]
        ring
    _ = rhoN N ^ (1 / 2 : ℝ) * (12 * V₀ * rhoN N ^ (1 / 8 : ℝ) +
          A * rhoN N ^ (161 / 200 : ℝ)) * (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ)) := by
        rw [hR, hR']; ring
    _ ≤ rhoN N ^ (1 / 2 : ℝ) * 1 * (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ)) := by
        gcongr
        linarith
    _ = rhoN N ^ (1 / 2 : ℝ) * (LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ)) := by ring



end LHYUpper
