import LHYUpper.Model.Fock

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Definitions for the decomposition of the interaction energy

Defines `zeros`, the number of vanishing momenta among `p, q, p - u, q + u`, the five interaction
parts of §4 ((4.3)–(4.7)), the index sets `Part.mem` of the parts on `(p, q, u)` with the convention
that `H_{S3}` omits the terms `v = -u`, and the summands `partTerm` of each part. -/

namespace Decomp

/-- Number of zeros among `p, q, p - u, q + u` (the four momenta of `a†_p a†_q a_{p-u} a_{q+u}`). -/
def zeros (p q u : Idx) : ℕ :=
  (if p = 0 then 1 else 0) + (if q = 0 then 1 else 0) + (if p - u = 0 then 1 else 0) +
    (if q + u = 0 then 1 else 0)

/-- `{p - u, q + u} = {p, q}` as multisets: the terms of `H_{S1}`, (4.3). -/
def InS1 (p q u : Idx) : Prop := u = 0 ∨ u = p - q

/-- The five interaction parts of §4, (4.3)–(4.7). -/
inductive Part
  | S1 | S2 | S3 | A1 | A2
  deriving DecidableEq

instance : Fintype Part :=
  ⟨⟨{Part.S1, Part.S2, Part.S3, Part.A1, Part.A2}, by decide⟩, fun j => by cases j <;> decide⟩

/-- Index set of each part on `(p, q, u)`; `H_{S3}` without the terms `v = -u` (they lie in
`H_{S1}`). -/
def Part.mem : Part → Idx → Idx → Idx → Prop
  | .S1, p, q, u => InS1 p q u
  | .S2, p, q, u => u ≠ 0 ∧ ((p = u ∧ q = -u) ∨ (p = 0 ∧ q = 0))
  | .S3, p, q, u => zeros p q u = 0 ∧ p + q = 0 ∧ ¬ InS1 p q u
  | .A1, p, q, u => zeros p q u = 1
  | .A2, p, q, u => zeros p q u = 0 ∧ p + q ≠ 0 ∧ ¬ InS1 p q u

/-- The summands of part `j` of the interaction energy. -/
def partTerm (j : Part) (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) : ℂ :=
  if j.mem i.1 i.2.1 i.2.2.1 then intTerm L V Ψ i else 0

end Decomp

end LHYUpper
