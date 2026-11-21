module

public import LHYUpper.Riemann.Shell

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ENNReal

noncomputable section
open Classical

namespace LHYUpper

/-! # The lattice `Λ*` in the scaled variable `k = ρ^{-1/2} u`

Rewrites the lattice of momenta in the variable `k = ρ^{-1/2} u` (`mom_eq_smul`), identifies `P_L`
of Definition 3.1 [def1] with the lattice points in the shell `ε_L ≤ |k| ≤ ε_L⁻¹` (`inPL_iff`), and
states the Riemann-sum lemma on `P_L` (`riemann_PL`) with lattice spacing `ρ^{-1/2}·2π/L`. -/

/-- `p_n(L) = ρ^{1/2} p_n(Lρ^{1/2})`: the lattice `Λ*` in the variable `k = ρ^{-1/2} u`. -/
theorem mom_eq_smul {ρ : ℝ} (hρ : 0 < ρ) (L : ℝ) (n : Idx) :
    mom L n = ρ ^ (1/2 : ℝ) • mom (L * ρ ^ (1/2 : ℝ)) n := by
  have h : ρ ^ (1/2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hρ _).ne'
  ext i
  simp only [mom, PiLp.smul_apply, smul_eq_mul]
  simp only [WithLp.equiv_symm_apply]
  by_cases hL : L = 0
  · simp [hL]
  · field_simp

/-- `u ∈ P_L` iff `ρ^{-1/2} u` lies in the shell `ε_L ≤ |k| ≤ ε_L⁻¹`. -/
theorem inPL_iff {ρ L : ℝ} (hρ : 0 < ρ) (n : Idx) :
    inPL ρ L n ↔ mom (L * ρ ^ (1/2 : ℝ)) n ∈ shellPL ρ := by
  have hs : 0 < ρ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hm : ‖mom L n‖ = ρ ^ (1/2 : ℝ) * ‖mom (L * ρ ^ (1/2 : ℝ)) n‖ := by
    rw [mom_eq_smul hρ L n, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  simp only [inPL, shellPL, Set.mem_ofPred_eq, hm]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

/-- The Riemann-sum lemma on `P_L` in the variable `k = ρ^{-1/2} u`, with lattice spacing
`2π/(Lρ^{1/2})`. -/
theorem riemann_PL {a b : ℝ} (ha : 0 ≤ a) (ha3 : a < 3) (hb : 3 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ) (F : R3 → ℝ) (ρ L : ℝ), 0 ≤ C → SingDecay a b C F → 0 < ρ →
      2 * π ≤ L * ρ ^ (1/2 : ℝ) →
      IntegrableOn F (shellPL ρ) ∧
      |(L ^ 3)⁻¹ * ρ ^ (-(3/2 : ℝ)) *
          (∑' n : Idx, (if inPL ρ L n then F ((ρ ^ (1/2 : ℝ))⁻¹ • mom L n) else 0))
        - ((2 * π) ^ 3)⁻¹ * ∫ k in shellPL ρ, F k|
        ≤ K * C * riemannRate a (2 * π / (L * ρ ^ (1/2 : ℝ))) := by
  obtain ⟨K, hK, h⟩ := riemann_shell ha ha3 hb
  refine ⟨K, hK, ?_⟩
  intro C F ρ L hC hF hρ hL
  have hs : 0 < ρ ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hL0 : 0 < L := by
    have : 0 < L * ρ ^ (1/2 : ℝ) := lt_of_lt_of_le (by positivity) hL
    exact pos_of_mul_pos_left this hs.le
  have hε : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hmeas : MeasurableSet (shellPL ρ) :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hshell : IsShell (epsP ρ) (ENNReal.ofReal (epsP ρ)⁻¹) 0 (shellPL ρ) := by
    refine ⟨fun p h1 h2 => ?_, fun p hp => ⟨hp.1, ENNReal.ofReal_le_ofReal hp.2⟩⟩
    simp only [add_zero] at h1 h2
    exact ⟨h1.le, ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg p)).1 h2).le⟩
  have hsum : (∑' n : Idx, (if inPL ρ L n then F ((ρ ^ (1/2 : ℝ))⁻¹ • mom L n) else 0))
      = latSum (L * ρ ^ (1/2 : ℝ)) (shellPL ρ) F := by
    unfold latSum
    refine tsum_congr fun n => ?_
    have key : (ρ ^ (1/2 : ℝ))⁻¹ • mom L n = mom (L * ρ ^ (1/2 : ℝ)) n := by
      rw [mom_eq_smul hρ L n, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
    have hiff : inPL ρ L n ↔ n ≠ 0 ∧ mom (L * ρ ^ (1/2 : ℝ)) n ∈ shellPL ρ := by
      rw [inPL_iff hρ n]
      refine ⟨fun hn => ⟨?_, hn⟩, fun hn => hn.2⟩
      rintro rfl
      have h0 : mom (L * ρ ^ (1/2 : ℝ)) 0 = 0 := by
        ext i
        simp [mom]
      have := hn.1
      rw [h0, norm_zero] at this
      linarith
    rw [key]
    exact if_congr hiff rfl rfl
  have hpre : (L ^ 3)⁻¹ * ρ ^ (-(3/2 : ℝ)) = ((L * ρ ^ (1/2 : ℝ)) ^ 3)⁻¹ := by
    have h3 : (ρ ^ (1/2 : ℝ)) ^ 3 = ρ ^ (3/2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      norm_num
    rw [mul_pow, h3, mul_inv, Real.rpow_neg hρ.le]
  obtain ⟨hint, -, hbd⟩ := h C F (L * ρ ^ (1/2 : ℝ)) (epsP ρ) (ENNReal.ofReal (epsP ρ)⁻¹)
    (shellPL ρ) hC hF hL hmeas hshell
  refine ⟨hint, ?_⟩
  rw [hsum, hpre]
  exact hbd

end LHYUpper
