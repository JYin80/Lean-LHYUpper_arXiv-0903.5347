module

public import LHYUpper.Scattering.Solution

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Elementary facts on the Dirichlet energy `e₀^D` (§2, §12)

Nonemptiness of the class of Dirichlet trial functions, nonnegativity and finiteness of `e₀^D`,
monotonicity in the box, invariance of the energy under a common translation, and the existence of
near-minimizers. They are the position-space facts about `e₀^D` of §2 (definition of `e0D`), used in
the duplication step (12.5)-(12.7) and in Lemma 2.1 [thm1]. -/

/-- A product of bumps `x ↦ ∏ᵢ b(xᵢ)` for a bump `b` of radius `r` around `z`. -/
private def DirichletFacts_prodBump {N : ℕ} {z : R3} (b : ContDiffBump z) (x : Conf N) : ℝ :=
  ∏ i, b (x i)

/-- The product of bumps is smooth. -/
private lemma DirichletFacts_prodBump_contDiff {N : ℕ} {z : R3} (b : ContDiffBump z) :
    ContDiff ℝ (⊤ : ℕ∞) (DirichletFacts_prodBump (N := N) b) := by
  unfold DirichletFacts_prodBump
  refine contDiff_prod (fun i _ => ?_)
  exact b.contDiff.comp (contDiff_apply ℝ (fun _ : Fin N => R3) i)

/-- The product of bumps is symmetric. -/
private lemma DirichletFacts_prodBump_perm {N : ℕ} {z : R3} (b : ContDiffBump z)
    (σ : Equiv.Perm (Fin N)) (x : Conf N) :
    DirichletFacts_prodBump b (x ∘ σ) = DirichletFacts_prodBump b x := by
  unfold DirichletFacts_prodBump
  exact Equiv.prod_comp σ (fun i => b (x i))

/-- The topological support of the product of bumps lies in a product of closed balls. -/
private lemma DirichletFacts_tsupport_prodBump {N : ℕ} {z : R3} (b : ContDiffBump z) :
    tsupport (DirichletFacts_prodBump (N := N) b) ⊆
      Set.pi Set.univ (fun _ => Metric.closedBall z b.rOut) := by
  refine closure_minimal ?_ (isClosed_set_pi (fun _ _ => Metric.isClosed_closedBall))
  intro x hx i _
  have hx' : ∏ j, b (x j) ≠ 0 := hx
  have hi : b (x i) ≠ 0 := (Finset.prod_ne_zero_iff.mp hx') i (Finset.mem_univ i)
  have : x i ∈ tsupport b := subset_closure (Function.mem_support.mpr hi)
  rwa [b.tsupport_eq] at this

/-- The product of bumps has compact support. -/
private lemma DirichletFacts_compact_prodBump {N : ℕ} {z : R3} (b : ContDiffBump z) :
    HasCompactSupport (DirichletFacts_prodBump (N := N) b) :=
  (isCompact_univ_pi (fun _ => isCompact_closedBall z b.rOut)).of_isClosed_subset
    (isClosed_tsupport _) (DirichletFacts_tsupport_prodBump b)

/-- The class of Dirichlet trial functions on `[0, L]³` is nonempty. -/
theorem isDirichletTrial_nonempty {L : ℝ} (hL : 0 < L) (N : ℕ) :
    ∃ Ψ : Conf N → ℂ, IsDirichletTrial L N Ψ := by
  set z : R3 := (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun _ => L / 2) with hz
  let b : ContDiffBump z := ⟨L / 8, L / 4, by positivity, by linarith⟩
  have hb : b.rOut = L / 4 := rfl
  set P : Conf N → ℝ := DirichletFacts_prodBump b with hP
  have hPcont : Continuous P := (DirichletFacts_prodBump_contDiff b).continuous
  have hPc : HasCompactSupport P := DirichletFacts_compact_prodBump b
  have hP2c : HasCompactSupport (fun x => P x ^ 2) := hPc.comp_left (g := fun t : ℝ => t ^ 2)
    (by simp)
  have hP0 : 0 < P (fun _ => z) := by
    refine Finset.prod_pos (fun i _ => ?_)
    exact b.pos_of_mem_ball (by simpa [b] using b.rIn_pos.trans b.rIn_lt_rOut)
  have hI : 0 < ∫ x, P x ^ 2 := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero (f := fun x => P x ^ 2)
      (hPcont.pow 2) hP2c (fun x => sq_nonneg _) (x := fun _ => z) ?_
    exact (pow_pos hP0 2).ne'
  set I : ℝ := ∫ x, P x ^ 2 with hIdef
  set s : ℝ := (Real.sqrt I)⁻¹ with hs
  have hs2 : s ^ 2 = I⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt hI.le]
  refine ⟨fun x => ((s * P x : ℝ) : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (DirichletFacts_prodBump_contDiff b))
  · have h1 : HasCompactSupport (fun x => s * P x) := hPc.mul_left
    exact h1.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  · intro x hx
    have h1 : tsupport (fun x => ((s * P x : ℝ) : ℂ)) ⊆ tsupport P := by
      refine (tsupport_comp_subset (g := fun t : ℝ => (t : ℂ)) (by simp)
        (fun x => s * P x)).trans ?_
      exact tsupport_mul_subset_right (f := fun _ => s) (g := P)
    have h2 := DirichletFacts_tsupport_prodBump b (h1 hx)
    intro i a
    have h3 : x i ∈ Metric.closedBall z (L / 4) := h2 i (Set.mem_univ i)
    have h4 : |(x i) a - L / 2| ≤ L / 4 := by
      have h5 : ‖x i - z‖ ≤ L / 4 := by
        rw [← dist_eq_norm]; exact h3
      have h6 := PiLp.norm_apply_le (x i - z) a
      have h7 : (x i - z) a = (x i) a - L / 2 := by simp [hz]
      rw [h7, Real.norm_eq_abs] at h6
      exact h6.trans h5
    rw [abs_le] at h4
    constructor <;> linarith [h4.1, h4.2]
  · intro σ x
    simp only [hP] at *
    rw [DirichletFacts_prodBump_perm b σ x]
  · have h : ∀ x : Conf N, ‖((s * P x : ℝ) : ℂ)‖ ^ 2 = s ^ 2 * P x ^ 2 := by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
    simp_rw [h]
    rw [integral_const_mul, ← hIdef, hs2, inv_mul_cancel₀ hI.ne']

/-- The Dirichlet energy is nonnegative for `V ≥ 0`. -/
theorem energyD_nonneg {V : R3 → ℝ} (hV : ∀ x, 0 ≤ V x) {N : ℕ} (Ψ : Conf N → ℂ) :
    0 ≤ energyD V Ψ := by
  refine integral_nonneg (fun x => ?_)
  refine add_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun a _ => sq_nonneg _)))
    (mul_nonneg (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))) (sq_nonneg _))
  split_ifs
  · exact hV _
  · exact le_rfl

/-- `e₀^D ≥ 0` for `V ≥ 0`. -/
theorem e0D_nonneg {V : R3 → ℝ} (hV : ∀ x, 0 ≤ V x) (L : ℝ) (N : ℕ) : 0 ≤ e0D L V N := by
  refine le_iInf₂ (fun Ψ _ => ?_)
  exact EReal.coe_nonneg.mpr (div_nonneg (energyD_nonneg hV Ψ) (Nat.cast_nonneg _))

/-- `e₀^D < ∞` on a box of positive side. -/
theorem e0D_lt_top {L : ℝ} (hL : 0 < L) (V : R3 → ℝ) (N : ℕ) : e0D L V N < ⊤ := by
  obtain ⟨Ψ, hΨ⟩ := isDirichletTrial_nonempty hL N
  exact (iInf₂_le (f := fun (Ψ : Conf N → ℂ) (_ : IsDirichletTrial L N Ψ) =>
    ((energyD V Ψ / N : ℝ) : EReal)) Ψ hΨ).trans_lt (EReal.coe_lt_top _)

/-- The Dirichlet energy is invariant under a common translation of all particles. -/
theorem energyD_translate (V : R3 → ℝ) {N : ℕ} (Ψ : Conf N → ℂ) (c : R3) :
    energyD V (fun x => Ψ (fun i => x i - c)) = energyD V Ψ := by
  set cc : Conf N := fun _ => c with hcc
  have hsub : ∀ x : Conf N, (fun i => x i - c) = x - cc := fun x => rfl
  have hder : ∀ x : Conf N, fderiv ℝ (fun x : Conf N => Ψ (fun i => x i - c)) x =
      fderiv ℝ Ψ (x - cc) := by
    intro x
    simp_rw [hsub]
    exact fderiv_comp_sub (f := Ψ) cc
  set F : Conf N → ℝ := fun x =>
    ((∑ i, ∑ a : Fin 3, ‖fderiv ℝ Ψ x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2) +
    (∑ i, ∑ j, if i ≠ j then V (x i - x j) else 0) * ‖Ψ x‖ ^ 2) with hF
  have hpt : ∀ x : Conf N, ((∑ i, ∑ a : Fin 3, ‖fderiv ℝ (fun x : Conf N =>
      Ψ (fun i => x i - c)) x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2) +
      (∑ i, ∑ j, if i ≠ j then V (x i - x j) else 0) * ‖Ψ (fun i => x i - c)‖ ^ 2) =
      F (x - cc) := by
    intro x
    simp only [hder, hF]
    have : ∀ i j : Fin N, (x - cc) i - (x - cc) j = x i - x j := by
      intro i j; simp [hcc]
    simp only [this]
    rfl
  unfold energyD
  simp_rw [hpt]
  exact integral_sub_right_eq_self F cc

/-- Near-minimizers of `e₀^D`: for every `δ > 0` a Dirichlet trial function has energy per
particle below `e₀^D + δ`. -/
theorem exists_lt_e0D {V : R3 → ℝ} (hV : ∀ x, 0 ≤ V x) {L : ℝ} (hL : 0 < L) (N : ℕ) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ Ψ : Conf N → ℂ, IsDirichletTrial L N Ψ ∧
      ((energyD V Ψ / N : ℝ) : EReal) < e0D L V N + ((δ : ℝ) : EReal) := by
  have h0 : 0 ≤ e0D L V N := e0D_nonneg hV L N
  have h1 : e0D L V N < ⊤ := e0D_lt_top hL V N
  obtain ⟨r, hr⟩ : ∃ r : ℝ, e0D L V N = (r : EReal) :=
    ⟨(e0D L V N).toReal, (EReal.coe_toReal h1.ne (ne_bot_of_le_ne_bot (by simp) h0)).symm⟩
  have h2 : e0D L V N < e0D L V N + ((δ : ℝ) : EReal) := by
    rw [hr, ← EReal.coe_add]
    exact EReal.coe_lt_coe_iff.mpr (by linarith)
  have h3 : ⨅ (Ψ : Conf N → ℂ) (_ : IsDirichletTrial L N Ψ), ((energyD V Ψ / N : ℝ) : EReal) <
      e0D L V N + ((δ : ℝ) : EReal) := h2
  obtain ⟨Ψ, hΨ⟩ := iInf_lt_iff.mp h3
  obtain ⟨hT, hlt⟩ := iInf_lt_iff.mp hΨ
  exact ⟨Ψ, hT, hlt⟩

end LHYUpper
