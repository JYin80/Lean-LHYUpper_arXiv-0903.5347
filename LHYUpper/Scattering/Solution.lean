import LHYUpper.Scattering.Regularity
import LHYUpper.Scattering.MaxPrinciple
import LHYUpper.Scattering.Gaussian
import LHYUpper.Statements

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! # The zero-energy scattering solution

For a potential `V` satisfying the hypotheses of Theorem 2.1 [mainthm], the zero-energy scattering
solution of §2 exists and is unique: it is the solution `bornSol V` of the Born equation, and any
function `w` with `-Δ(1 - w) + V(1 - w) = 0`, `0 ≤ w < 1`, `w → 0` at infinity equals it.
Consequently `w` is even, `g = V(1 - w)` ((3.12) [gdef]) satisfies `0 ≤ g ≤ V` and is even, and
`g₀ = ∫ g = 4πa` satisfies `0 < g₀ ≤ ∫ V`. -/

/-- Existence and uniqueness of the zero-energy scattering solution of §2 under the hypotheses of
Theorem 2.1 [mainthm]. -/
theorem scattering_exists_unique (V : R3 → ℝ) (hV : PotentialHyp V) :
    Stmt.ScatteringSolutionExistsUnique V := by
  refine ⟨bornSol V, scat_bornSol_isScatteringSolution hV, fun w' hw' => ?_⟩
  exact (scat_solution_unique hV.nonneg (scat_bornSol_isScatteringSolution hV) hw').symm

section Position
variable {V w : R3 → ℝ}

/-- Every zero-energy scattering solution is the solution of the Born equation. -/
theorem scat_eq_bornSol (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    w = bornSol V := by
  exact (scat_solution_unique hV.nonneg (scat_bornSol_isScatteringSolution hV) hw).symm

/-- The scattering solution is even (§2, `V` even). -/
theorem scat_w_even (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ x, w (-x) = w x := by
  intro x
  rw [scat_eq_bornSol hV hw]
  exact bornSol_even hV x

/-- `g = V(1 - w) ≥ 0`, (3.12) [gdef]. -/
theorem scat_g_nonneg (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ x, 0 ≤ gfun V w x := by
  intro x
  have h1 : 0 ≤ 1 - w x := by linarith [hw.lt_one x]
  exact mul_nonneg (hV.nonneg x) h1

/-- `g = V(1 - w) ≤ V`. -/
theorem scat_g_le (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ x, gfun V w x ≤ V x := by
  intro x
  have h1 : 0 ≤ V x * w x := mul_nonneg (hV.nonneg x) (hw.nonneg x)
  simp only [gfun]
  linarith

/-- `g` is even. -/
theorem scat_g_even (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ x, gfun V w (-x) = gfun V w x := by
  intro x
  simp only [gfun]
  rw [hV.even x, scat_w_even hV hw x]

/-- `g` is a Schwartz function for every scattering solution `w`. -/
private lemma scat_gfun_schwartz (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ S : SchwartzMap R3 ℝ, (S : R3 → ℝ) = gfun V w := by
  rw [scat_eq_bornSol hV hw]
  exact scat_bornSol_g_schwartz hV

/-- `g₀ = 4πa > 0`. -/
theorem scat_g0_pos (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    0 < g0 V w := by
  obtain ⟨S, hS⟩ := scat_gfun_schwartz hV hw
  obtain ⟨x₀, hx₀⟩ := hV.ne_zero
  have hVx : 0 < V x₀ := lt_of_le_of_ne (hV.nonneg x₀) (Ne.symm hx₀)
  have hgx : 0 < gfun V w x₀ := mul_pos hVx (by linarith [hw.lt_one x₀])
  have hcont : Continuous (gfun V w) := by rw [← hS]; exact S.continuous
  have hint : Integrable (gfun V w) := by rw [← hS]; exact S.integrable
  have hnn : 0 ≤ gfun V w := fun x => scat_g_nonneg hV hw x
  unfold g0
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  exact IsOpen.measure_pos volume hcont.isOpen_support ⟨x₀, hgx.ne'⟩

/-- `g₀ ≤ V₀ = ∫ V`. -/
theorem scat_g0_le (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    g0 V w ≤ ∫ x, V x := by
  obtain ⟨S, hS⟩ := scat_gfun_schwartz hV hw
  obtain ⟨T, hT⟩ := hV.schwartz
  have hgi : Integrable (gfun V w) := by rw [← hS]; exact S.integrable
  have hVi : Integrable V := by rw [← hT]; exact T.integrable
  exact integral_mono hgi hVi (scat_g_le hV hw)

end Position

end LHYUpper
