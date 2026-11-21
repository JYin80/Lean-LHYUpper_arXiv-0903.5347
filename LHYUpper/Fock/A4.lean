module

public import LHYUpper.Model.Fock

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Matrix elements of the quartic operator `a†a†aa` on occupation states

Properties of `a4`, the action of `a†_p a†_q a_r a_s` on a normalized occupation state `|α⟩`: its
value on states of the form `β + e_r + e_s`, the adjoint, the identity `c(α)² = ⟨α| A† A |α⟩` and
the injectivity statement of Lemma 7.1 [id4a], the diagonal case (3.4) [number], and the
preservation of the particle number with the bound `N²` on the coefficient. -/

/-- `a4` evaluated on a state of the form `β + e_r + e_s`, where `e_n = Finsupp.single n 1`,
written in terms of `β`: all subtractions in the definition of `a4` are exact. -/
theorem a4_of_add (p q r s : Idx) (β : Occ) :
    a4 p q r s (β + Finsupp.single r 1 + Finsupp.single s 1) =
      (Real.sqrt ((β + Finsupp.single r 1 + Finsupp.single s 1 : Occ) s : ℝ) *
        Real.sqrt ((β + Finsupp.single r 1 : Occ) r : ℝ) *
        Real.sqrt ((β + Finsupp.single q 1 : Occ) q : ℝ) *
        Real.sqrt ((β + Finsupp.single q 1 + Finsupp.single p 1 : Occ) p : ℝ),
       β + Finsupp.single q 1 + Finsupp.single p 1) := by
  simp only [a4, add_tsub_cancel_right]

/-- A state in which a particle can be annihilated at `s` and then at `r` is of the form
`β + e_r + e_s`, where `e_n = Finsupp.single n 1`. -/
theorem a4_exists_add_of_pos (r s : Idx) (α : Occ) (h1 : 0 < α s)
    (h2 : 0 < (α - Finsupp.single s 1 : Occ) r) :
    ∃ β : Occ, α = β + Finsupp.single r 1 + Finsupp.single s 1 := by
  refine ⟨α - Finsupp.single s 1 - Finsupp.single r 1, ?_⟩
  ext n
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply,
    Finsupp.tsub_apply] at *
  by_cases hs : s = n <;> by_cases hr : r = n <;> simp_all <;> omega

/-- If the coefficient of `a4` is nonzero, the state is of the form `β + e_r + e_s`. -/
theorem a4_exists_add (p q r s : Idx) (α : Occ) (h : (a4 p q r s α).1 ≠ 0) :
    ∃ β : Occ, α = β + Finsupp.single r 1 + Finsupp.single s 1 := by
  simp only [a4, ne_eq, mul_eq_zero, Real.sqrt_eq_zero', not_or, not_le, Nat.cast_pos] at h
  obtain ⟨⟨⟨h1, h2⟩, _⟩, _⟩ := h
  exact a4_exists_add_of_pos r s α h1 h2

/-- `c(α)² = ⟨α| A† A |α⟩` for `A = a†_{u₁} a†_{u₂} a_{u₃} a_{u₄}`, Lemma 7.1 [id4a]. -/
theorem a4_fst_sq (u₁ u₂ u₃ u₄ : Idx) (α : Occ) :
    (a4 u₁ u₂ u₃ u₄ α).1 ^ 2 =
      (α u₄ : ℝ) * ((α u₃ : ℝ) - if u₃ = u₄ then 1 else 0) *
        ((α u₂ : ℝ) + 1 - (if u₂ = u₃ then 1 else 0) - (if u₂ = u₄ then 1 else 0)) *
        ((α u₁ : ℝ) + 1 + (if u₁ = u₂ then 1 else 0) - (if u₁ = u₃ then 1 else 0) -
          (if u₁ = u₄ then 1 else 0)) := by
  by_cases hs : α u₄ = 0
  · simp [a4, hs]
  by_cases hr : (α - Finsupp.single u₄ 1 : Occ) u₃ = 0
  · have : (α u₃ : ℝ) - (if u₃ = u₄ then 1 else 0) = 0 := by
      by_cases h : u₃ = u₄
      · subst h
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same] at hr
        simp only [ite_true]
        have : α u₃ = 1 := by omega
        simp [this]
      · simp only [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm h, ite_false] at hr
        have : α u₃ = 0 := by omega
        simp [h, this]
    have h0 : (a4 u₁ u₂ u₃ u₄ α).1 = 0 := by
      simp only [a4, hr, Nat.cast_zero, Real.sqrt_zero, mul_zero, zero_mul]
    rw [h0, this]
    ring
  obtain ⟨β, rfl⟩ := a4_exists_add_of_pos u₃ u₄ α (Nat.pos_of_ne_zero hs) (Nat.pos_of_ne_zero hr)
  rw [a4_of_add]
  simp only [mul_pow]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  by_cases h1 : u₁ = u₂ <;> by_cases h2 : u₁ = u₃ <;> by_cases h3 : u₁ = u₄ <;>
    by_cases h4 : u₂ = u₃ <;> by_cases h5 : u₂ = u₄ <;> by_cases h6 : u₃ = u₄ <;>
    simp_all [eq_comm]

theorem a4_fst_nonneg (u₁ u₂ u₃ u₄ : Idx) (α : Occ) : 0 ≤ (a4 u₁ u₂ u₃ u₄ α).1 := by
  simp only [a4]
  positivity

/-- Adjoint of `a†_{u₁} a†_{u₂} a_{u₃} a_{u₄}` on `|α⟩` when the coefficient is nonzero. -/
theorem a4_adjoint (u₁ u₂ u₃ u₄ : Idx) (α : Occ) (h : (a4 u₁ u₂ u₃ u₄ α).1 ≠ 0) :
    a4 u₄ u₃ u₂ u₁ (a4 u₁ u₂ u₃ u₄ α).2 = ((a4 u₁ u₂ u₃ u₄ α).1, α) := by
  obtain ⟨β, rfl⟩ := a4_exists_add u₁ u₂ u₃ u₄ α h
  rw [a4_of_add u₁ u₂ u₃ u₄ β]
  simp only
  rw [a4_of_add u₄ u₃ u₂ u₁ β]
  refine Prod.ext ?_ rfl
  simp only
  ring

/-- (3.4) [number] in the quartic encoding: `⟨α| a†_p a†_q a_p a_q |α⟩ = α(p)α(q) - δ_{pq}α(p)`. -/
theorem a4_diag_fst (p q : Idx) (α : Occ) :
    (a4 p q p q α).1 = (α p : ℝ) * α q - if p = q then (α p : ℝ) else 0 := by
  have hsq := a4_fst_sq p q p q α
  have hnn := a4_fst_nonneg p q p q α
  by_cases h : p = q
  · subst h
    simp only [ite_true] at hsq ⊢
    have hx : 0 ≤ (α p : ℝ) * α p - α p := by
      rcases Nat.eq_zero_or_pos (α p) with h0 | h0
      · simp [h0]
      · have : (1 : ℝ) ≤ α p := by exact_mod_cast h0
        nlinarith
    have : (a4 p p p p α).1 ^ 2 = ((α p : ℝ) * α p - α p) ^ 2 := by rw [hsq]; ring
    exact (sq_eq_sq₀ hnn hx).mp this
  · have hx : 0 ≤ (α p : ℝ) * α q := by positivity
    simp only [h, Ne.symm h, ite_true, ite_false] at hsq ⊢
    have : (a4 p q p q α).1 ^ 2 = ((α p : ℝ) * α q - 0) ^ 2 := by rw [hsq]; ring
    simpa using (sq_eq_sq₀ hnn (by simpa using hx)).mp this

theorem a4_diag_snd (p q : Idx) (α : Occ) (h : (a4 p q p q α).1 ≠ 0) :
    (a4 p q p q α).2 = α := by
  obtain ⟨β, rfl⟩ := a4_exists_add p q p q α h
  rw [a4_of_add p q p q β]
  simp only
  rw [add_right_comm]

/-- `T` of Lemma 7.1 [id4a] is injective where `A|α⟩ ≠ 0`. -/
theorem a4_injOn (u₁ u₂ u₃ u₄ : Idx) :
    Set.InjOn (fun α => (a4 u₁ u₂ u₃ u₄ α).2) {α | (a4 u₁ u₂ u₃ u₄ α).1 ≠ 0} := by
  intro α hα α' hα' h
  have h1 := a4_adjoint u₁ u₂ u₃ u₄ α hα
  have h2 := a4_adjoint u₁ u₂ u₃ u₄ α' hα'
  simp only at h
  rw [h] at h1
  exact (Prod.ext_iff.mp (h1.symm.trans h2)).2

/-- `a†_p a†_q a_r a_s = a†_q a†_p a_s a_r` on occupation states. -/
theorem a4_comm (p q r s : Idx) (α : Occ) : a4 p q r s α = a4 q p s r α := by
  have h2 : α - Finsupp.single s 1 - Finsupp.single r 1 =
      α - Finsupp.single r 1 - Finsupp.single s 1 := tsub_right_comm
  simp only [a4]
  rw [h2, add_right_comm (α - Finsupp.single r 1 - Finsupp.single s 1) (Finsupp.single p 1)]
  refine Prod.ext ?_ rfl
  simp only
  set γ : Occ := α - Finsupp.single r 1 - Finsupp.single s 1 with hγ
  have e1 : r ≠ s → (α - Finsupp.single s 1 : Occ) r = α r := by
    intro h; simp [Finsupp.tsub_apply, h]
  have e2 : r ≠ s → (α - Finsupp.single r 1 : Occ) s = α s := by
    intro h; simp [Finsupp.tsub_apply, Ne.symm h]
  have e3 : p ≠ q → (γ + Finsupp.single q 1 + Finsupp.single p 1 : Occ) p =
      (γ + Finsupp.single p 1 : Occ) p := by
    intro h; simp [Finsupp.add_apply, Ne.symm h]
  have e4 : p ≠ q → (γ + Finsupp.single q 1 + Finsupp.single p 1 : Occ) q =
      (γ + Finsupp.single q 1 : Occ) q := by
    intro h; simp [Finsupp.add_apply, h]
  by_cases hpq : p = q <;> by_cases hrs : r = s
  · subst hpq hrs; rfl
  · subst hpq
    rw [e1 hrs, e2 hrs]; ring
  · subst hrs
    rw [e3 hpq, e4 hpq]; ring
  · rw [e1 hrs, e2 hrs, e3 hpq, e4 hpq]; ring

private theorem a4_num_add (α β : Occ) : (α + β).num = α.num + β.num :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

private theorem a4_num_single (n : Idx) : Occ.num (Finsupp.single n 1) = 1 := by
  unfold Occ.num
  exact Finsupp.sum_single_index rfl

private theorem a4_apply_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases h : n ∈ α.support
  · exact Finset.single_le_sum (f := fun x => α x) (fun _ _ => Nat.zero_le _) h
  · simp [Finsupp.notMem_support_iff.mp h]

/-- If the coefficient of `a4` is nonzero, the particle number is preserved. -/
theorem a4_snd_num (p q r s : Idx) (α : Occ) (h : (a4 p q r s α).1 ≠ 0) :
    (a4 p q r s α).2.num = α.num := by
  obtain ⟨β, rfl⟩ := a4_exists_add p q r s α h
  rw [a4_of_add p q r s β]
  simp only [a4_num_add, a4_num_single]

/-- The coefficient of `a4` on an `N`-particle state is at most `N ^ 2`. -/
theorem a4_fst_le (p q r s : Idx) (α : Occ) (N : ℕ) (hα : α.num = N) :
    (a4 p q r s α).1 ≤ (N : ℝ) ^ 2 := by
  by_cases h : (a4 p q r s α).1 = 0
  · rw [h]; positivity
  have hT := a4_snd_num p q r s α h
  obtain ⟨β, rfl⟩ := a4_exists_add p q r s α h
  rw [a4_of_add p q r s β] at hT ⊢
  simp only at hT ⊢
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hm : ∀ (γ δ : Occ) (n : Idx), γ n ≤ (γ + δ) n := fun γ δ n => by
    simp [Finsupp.add_apply]
  have h1 : (β + Finsupp.single r 1 + Finsupp.single s 1 : Occ) s ≤ N :=
    (a4_apply_le_num _ s).trans hα.le
  have h2 : (β + Finsupp.single r 1 : Occ) r ≤ N :=
    (hm _ _ r).trans ((a4_apply_le_num _ r).trans hα.le)
  have h3 : (β + Finsupp.single q 1 + Finsupp.single p 1 : Occ) p ≤ N :=
    (a4_apply_le_num _ p).trans (hT.trans hα).le
  have h4 : (β + Finsupp.single q 1 : Occ) q ≤ N :=
    (hm _ _ q).trans ((a4_apply_le_num _ q).trans (hT.trans hα).le)
  calc _ ≤ Real.sqrt N * Real.sqrt N * Real.sqrt N * Real.sqrt N := by
        gcongr
    _ = (N : ℝ) ^ 2 := by
        have := Real.mul_self_sqrt hN
        calc _ = (Real.sqrt N * Real.sqrt N) * (Real.sqrt N * Real.sqrt N) := by ring
          _ = _ := by rw [this]; ring

end LHYUpper
