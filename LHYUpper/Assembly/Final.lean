module

public import LHYUpper.Assembly.Theorem31
public import LHYUpper.Kinetic.Lemma41
public import LHYUpper.Pair.S1S2
public import LHYUpper.Pair.S3
public import LHYUpper.OneLeg.Lemma45
public import LHYUpper.FourLegs.HardAssembly
public import LHYUpper.Scattering.Identities
public import LHYUpper.TrialState.Normalization

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- `‖∇w‖₂² = ∫ ‖fderiv ℝ w‖²`, since `gradient w x` is the image of `fderiv ℝ w x` under the
isometry `(toDual ℝ R3).symm` (§4, end). -/
private lemma Final_normGradW2_eq (w : R3 → ℝ) :
    normGradW2 w = ∫ x, ‖fderiv ℝ w x‖ ^ 2 := by
  unfold normGradW2
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  simp only [gradient, LinearIsometryEquiv.norm_map]

/-- `‖Vw‖₁ = ∫ V w` for `V ≥ 0`, `w ≥ 0` (§4, end). -/
private lemma Final_normVw_eq {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) : normVw V w = ∫ x, V x * w x := by
  unfold normVw
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  exact abs_of_nonneg (mul_nonneg (hV.nonneg x) (hw.nonneg x))

/-- `‖Vw²‖₁ = ∫ V w²` for `V ≥ 0` (§4, end). -/
private lemma Final_normVw2_eq {V w : R3 → ℝ} (hV : PotentialHyp V) :
    normVw2 V w = ∫ x, V x * w x ^ 2 := by
  unfold normVw2
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  exact abs_of_nonneg (mul_nonneg (hV.nonneg x) (sq_nonneg _))

/-- `V₀ = ∫ V`, since `V̂(0) = ∫ V` is real. -/
private lemma Final_V0_eq (V : R3 → ℝ) : V0 V = ∫ x, V x := by
  rw [V0, scat_ft_zero, Complex.ofReal_re]

/-- The first identity at the end of §4 in the form used by the assembly:
`‖∇w‖₂² − ‖Vw‖₁ + ‖Vw²‖₁ = 0`. -/
theorem Final_I1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    normGradW2 w - normVw V w + normVw2 V w = 0 := by
  rw [Final_normGradW2_eq, Final_normVw_eq hV hw, Final_normVw2_eq hV]
  exact scat_I2 hV hw

/-- The second identity at the end of §4 in the form used by the assembly: `V₀ − ‖Vw‖₁ = g₀`,
with `V₀ = Re V̂(0)`. -/
theorem Final_I2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    V0 V - normVw V w = g0 V w := by
  rw [Final_V0_eq, Final_normVw_eq hV hw]
  exact scat_I1 hV hw

/-- Theorem 3.1 [lemma2.1]. -/
theorem Theorem3_1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Theorem3_1 V w :=
  Theorem31.theorem3_1_of_lemmas V w (lemma4_1 hV hw) (Lemma4_2 hV hw) (Lemma4_3 hV hw)
    (Lemma4_4 hV hw) (lemma4_5 hV hw) (Lemma4_6 hV hw) (Final_I1 hV hw) (Final_I2 hV hw)
    (Normalization_eventually V w)

/-- Theorem 2.2 [lemma2]. -/
theorem Theorem2_2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Theorem2_2 V w :=
  Theorem31.theorem2_2_of_theorem3_1 V w (Theorem3_1 hV hw)

/-- The hypothesis of Lemma 2.2 [lemma1]: the upper limit of the ratio for `e₀^P` on the torus of
side `L_N` at density `ρ_N` is at most `16/(15π²)`. -/
theorem e0P_limsup_le {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    limsup (fun N : ℕ => ratio (g0 V w) (rhoN N) (e0P (LN N) V N)) atTop ≤ (cLHY : EReal) :=
  Theorem31.limsup_ratio_e0P_le V w hV (Theorem2_2 hV hw)

/-! ### Checks at the Gaussian potential -/

section Checks

/-- The Gaussian potential and its scattering solution. -/
private def PV : R3 → ℝ := fun x => Real.exp (-‖x‖ ^ 2)
private def Pw : R3 → ℝ := (scattering_exists_unique PV scat_gaussian_potentialHyp).choose
private lemma Pw_spec : IsScatteringSolution PV Pw :=
  (scattering_exists_unique PV scat_gaussian_potentialHyp).choose_spec.1

/-- The first identity at the end of §4 at the Gaussian potential. -/
example := Final_I1 scat_gaussian_potentialHyp Pw_spec

/-- The second identity at the end of §4 at the Gaussian potential. -/
example := Final_I2 scat_gaussian_potentialHyp Pw_spec

/-- Theorem 3.1 [lemma2.1] at the Gaussian potential. -/
example := Theorem3_1 scat_gaussian_potentialHyp Pw_spec

/-- Theorem 2.2 [lemma2] at the Gaussian potential. -/
example := Theorem2_2 scat_gaussian_potentialHyp Pw_spec

/-- The hypothesis of Lemma 2.2 [lemma1] at the Gaussian potential. -/
example := e0P_limsup_le scat_gaussian_potentialHyp Pw_spec

end Checks

end LHYUpper
