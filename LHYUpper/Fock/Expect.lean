import LHYUpper.Fock.A4

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Expectation values `Q_Ψ` of occupation numbers

Defines the quantities `Q`, `Qm` and `Qc` of Definition 5.1 [1] (expectations of products of
occupation numbers, probabilities of occupation events, and their conditional forms) for a state `Ψ`
on occupation numbers. Proves the absolute convergence of the series of Lemma 7.1 [id4a] for a
normalized `N`-particle state, the bound `Q_Ψ(u) ≤ N`, and the normalization `Σ_m Q_Ψ({u, m}) = 1`. -/

namespace Expect

/-- `Q_Ψ(u₁, …, u_s) = Σ_α ∏_i α(u_i) |Ψ(α)|²`, Definition 5.1 [1] item 1. -/
def Q (Ψ : Occ → ℂ) (us : List Idx) : ℝ :=
  ∑' α : Occ, (us.map fun u => (α u : ℝ)).prod * ‖Ψ α‖ ^ 2

/-- The event `A = {α : α(u_i) = m_i ∀ i}` of Definition 5.1 [1] item 2. -/
def Ev (um : List (Idx × ℕ)) (α : Occ) : Prop := ∀ x ∈ um, α x.1 = x.2

/-- `Q_Ψ({u₁, m₁}, …, {u_t, m_t}) = Σ_{α ∈ A} |Ψ(α)|²`, Definition 5.1 [1] item 2. -/
def Qm (Ψ : Occ → ℂ) (um : List (Idx × ℕ)) : ℝ :=
  ∑' α : Occ, if Ev um α then ‖Ψ α‖ ^ 2 else 0

/-- `Q_Ψ(k₁, …, k_s | {u₁, m₁}, …)`, Definition 5.1 [1] item 3 (value `0` when the
denominator vanishes). -/
def Qc (Ψ : Occ → ℂ) (ks : List Idx) (um : List (Idx × ℕ)) : ℝ :=
  (∑' α : Occ, if Ev um α then (ks.map fun k => (α k : ℝ)).prod * ‖Ψ α‖ ^ 2 else 0) / Qm Ψ um

/-- A single occupation number is at most the particle number. -/
private theorem occ_apply_le_num (α : Occ) (u : Idx) : α u ≤ α.num := by
  by_cases hu : u ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hu
  · rw [Finsupp.notMem_support_iff.mp hu]; exact Nat.zero_le _

/-- The series of Lemma 7.1 [id4a] converges absolutely for a normalized `N`-particle state. -/
theorem id4a_summable (N : ℕ) (Ψ : Occ → ℂ) (hΨ : IsNState N Ψ) (u₁ u₂ u₃ u₄ : Idx) :
    Summable fun α : Occ =>
      ‖conj (Ψ (a4 u₁ u₂ u₃ u₄ α).2) * ((a4 u₁ u₂ u₃ u₄ α).1 : ℂ) * Ψ α‖ := by
  set S : Set Occ := {α | (a4 u₁ u₂ u₃ u₄ α).1 ≠ 0} with hS
  have hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have hinj : Function.Injective fun α : S => (a4 u₁ u₂ u₃ u₄ α.1).2 := by
    intro a b h
    exact Subtype.ext (a4_injOn u₁ u₂ u₃ u₄ a.2 b.2 h)
  have hsub : Summable fun α : S => ‖Ψ (a4 u₁ u₂ u₃ u₄ α.1).2‖ ^ 2 :=
    hs.comp_injective hinj
  have hind : Summable (S.indicator fun α : Occ => ‖Ψ (a4 u₁ u₂ u₃ u₄ α).2‖ ^ 2) :=
    summable_subtype_iff_indicator.mp hsub
  have hB : Summable fun α : Occ =>
      (N : ℝ) ^ 2 / 2 * (S.indicator (fun α : Occ => ‖Ψ (a4 u₁ u₂ u₃ u₄ α).2‖ ^ 2) α +
        ‖Ψ α‖ ^ 2) :=
    (hind.add hs).mul_left _
  refine Summable.of_nonneg_of_le (fun α => norm_nonneg _) (fun α => ?_) hB
  have hc := a4_fst_nonneg u₁ u₂ u₃ u₄ α
  have hnorm : ‖conj (Ψ (a4 u₁ u₂ u₃ u₄ α).2) * ((a4 u₁ u₂ u₃ u₄ α).1 : ℂ) * Ψ α‖ =
      ‖Ψ (a4 u₁ u₂ u₃ u₄ α).2‖ * (a4 u₁ u₂ u₃ u₄ α).1 * ‖Ψ α‖ := by
    rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg hc]
  rw [hnorm]
  by_cases h0 : (a4 u₁ u₂ u₃ u₄ α).1 = 0
  · rw [h0]
    have : 0 ≤ (N : ℝ) ^ 2 / 2 * (S.indicator (fun α : Occ => ‖Ψ (a4 u₁ u₂ u₃ u₄ α).2‖ ^ 2) α +
        ‖Ψ α‖ ^ 2) := by
      apply mul_nonneg (by positivity)
      apply add_nonneg
      · exact Set.indicator_nonneg (fun _ _ => by positivity) _
      · positivity
    simpa using this
  · have hαS : α ∈ S := h0
    rw [Set.indicator_of_mem hαS]
    by_cases hΨα : Ψ α = 0
    · rw [hΨα]
      simp only [norm_zero, mul_zero]
      positivity
    · have hn : α.num = N := hΨ.2 α hΨα
      have hle := a4_fst_le u₁ u₂ u₃ u₄ α N hn
      set x := ‖Ψ (a4 u₁ u₂ u₃ u₄ α).2‖
      set y := ‖Ψ α‖
      set c := (a4 u₁ u₂ u₃ u₄ α).1
      have hx : 0 ≤ x := norm_nonneg _
      have hy : 0 ≤ y := norm_nonneg _
      calc x * c * y ≤ x * (N : ℝ) ^ 2 * y := by gcongr
        _ = (N : ℝ) ^ 2 * (x * y) := by ring
        _ ≤ (N : ℝ) ^ 2 * ((x ^ 2 + y ^ 2) / 2) := by
            gcongr
            nlinarith [sq_nonneg (x - y)]
        _ = (N : ℝ) ^ 2 / 2 * (x ^ 2 + y ^ 2) := by ring

/-- `Q_Ψ(u) ≤ N` for a normalized `N`-particle state. -/
theorem Q_single_le (N : ℕ) (Ψ : Occ → ℂ) (hΨ : IsNState N Ψ) (u : Idx) :
    Q Ψ [u] ≤ N := by
  have hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have hle : ∀ α : Occ, (α u : ℝ) * ‖Ψ α‖ ^ 2 ≤ (N : ℝ) * ‖Ψ α‖ ^ 2 := by
    intro α
    by_cases h : Ψ α = 0
    · simp [h]
    · have := (occ_apply_le_num α u).trans (hΨ.2 α h).le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) (by positivity)
  have hB : Summable fun α : Occ => (N : ℝ) * ‖Ψ α‖ ^ 2 := hs.mul_left _
  have hA : Summable fun α : Occ => (α u : ℝ) * ‖Ψ α‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun α => by positivity) hle hB
  have := hA.tsum_le_tsum hle hB
  rw [tsum_mul_left, hΨ.1.tsum_eq, mul_one] at this
  simpa [Q] using this

/-- `Σ_m Q_Ψ({u, m}) = 1` for a normalized state. -/
theorem tsum_Qm_single (N : ℕ) (Ψ : Occ → ℂ) (hΨ : IsNState N Ψ) (u : Idx) :
    ∑' m : ℕ, Qm Ψ [(u, m)] = 1 := by
  have hev : ∀ (m : ℕ) (α : Occ), Ev [(u, m)] α ↔ α u = m := by
    intro m α
    simp [Ev]
  have hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have hind : ∀ m : ℕ, (fun α : Occ => if Ev [(u, m)] α then ‖Ψ α‖ ^ 2 else 0) =
      Set.indicator {α : Occ | α u = m} fun α : Occ => ‖Ψ α‖ ^ 2 := by
    intro m
    funext α
    simp only [Set.indicator, Set.mem_setOf_eq, hev]
  let e : (Σ m : ℕ, {α : Occ // α u = m}) ≃ Occ := Equiv.sigmaFiberEquiv fun α : Occ => α u
  have hfib : ∀ m : ℕ, HasSum (fun c : {α : Occ // α u = m} => ‖Ψ c.1‖ ^ 2) (Qm Ψ [(u, m)]) := by
    intro m
    have h1 : Summable (Set.indicator {α : Occ | α u = m} fun α : Occ => ‖Ψ α‖ ^ 2) :=
      hs.indicator _
    have h2 : HasSum (Set.indicator {α : Occ | α u = m} fun α : Occ => ‖Ψ α‖ ^ 2)
        (Qm Ψ [(u, m)]) := by
      have : Qm Ψ [(u, m)] =
          ∑' α, Set.indicator {α : Occ | α u = m} (fun α : Occ => ‖Ψ α‖ ^ 2) α := by
        unfold Qm; rw [hind m]
      rw [this]; exact h1.hasSum
    exact (hasSum_subtype_iff_indicator (f := fun α : Occ => ‖Ψ α‖ ^ 2)
      (s := {α : Occ | α u = m})).mpr h2
  have hall : HasSum (fun m : ℕ => Qm Ψ [(u, m)]) 1 := by
    apply HasSum.sigma (f := fun x : (Σ m : ℕ, {α : Occ // α u = m}) => ‖Ψ (e x)‖ ^ 2)
    · exact (e.hasSum_iff.mpr hΨ.1)
    · intro m
      exact hfib m
  exact hall.tsum_eq

end Expect

end LHYUpper
