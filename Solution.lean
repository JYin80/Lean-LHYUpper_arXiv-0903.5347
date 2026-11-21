module

public import LHYUpper

public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-!
# Proof of the statement of `Challenge.lean`

The theorem below has the same name and the same statement as its counterpart in
`Challenge.lean`, and is proved by the theorem of the library `LHYUpper` named in its proof. The
definitions that occur in the statement (`PotentialHyp`, `IsScatteringSolution`, `g0`, `ratio`,
`cLHY`, `thermo`, `HasEnergy`, `e0P` and the definitions these use) are those of
`LHYUpper/Model/Basic.lean` and `LHYUpper/Model/Fock.lean`; `Challenge.lean` repeats them
verbatim, and Comparator checks that the two copies agree.

`mainTheorem` (`LHYUpper/Thermo/Duplication.lean`) is Theorem 2.1 of the paper; its statement
`Stmt.MainTheorem V w` (`LHYUpper/Statements.lean`) unfolds to the statement written out here.
-/

/-- **Theorem 2.1 of Yau–Yin (the Lee–Huang–Yang upper bound).** If `V` satisfies the hypotheses
`PotentialHyp V` and `1 - w` is the zero-energy scattering solution, then the upper limit as
`ρ → 0⁺` of the upper limit as `L → ∞` with `N/L³ → ρ` of
`(e₀^P - g₀ρ) / (g₀^{5/2} ρ^{3/2})` is at most `16/(15π²)`, where `g₀ = ∫ V(1 - w) = 4πa` and
`e₀^P` is the ground state energy per particle of `N` bosons in `[0, L]³` with periodic boundary
condition. -/
theorem leeHuangYangUpperBound {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    limsup (fun ρ : ℝ => limsup (fun x : ℕ × ℝ => ratio (g0 V w) ρ (e0P x.2 V x.1))
      (thermo ρ)) (𝓝[>] 0) ≤ (cLHY : EReal) :=
  mainTheorem hV hw

end LHYUpper
