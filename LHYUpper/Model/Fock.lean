import LHYUpper.Model.Basic

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # Occupation-number description of the periodic Hamiltonian

Describes the Hamiltonian (2.1) [ham] on the torus in the occupation-number basis: the type `Occ` of
occupation numbers with particle number `Occ.num`, the action `a4` of `a†_p a†_q a_r a_s` on `|α⟩`,
the kinetic and interaction summands `kinTerm` and `intTerm` of `⟨Ψ, H Ψ⟩`, the energy predicate
`HasEnergy`, normalized states `IsNState`, and the periodic ground state energy per particle `e0P`.
The free condensate is shown to be a normalized state with the energy `V₀ N (N - 1)/|Λ|`. -/

/-- Occupation numbers `α : Λ* → ℕ` with finite support. -/
abbrev Occ := Idx →₀ ℕ

/-- Particle number `Σ_k α(k)`. -/
def Occ.num (α : Occ) : ℕ := α.sum (fun _ m => m)

/-- Action of `a†_p a†_q a_r a_s` on the normalized occupation state `|α⟩`, under
`[a_p, a†_q] = δ_{pq}`: the coefficient and the resulting occupation. -/
def a4 (p q r s : Idx) (α : Occ) : ℝ × Occ :=
  let α1 := α - Finsupp.single s 1
  let α2 := α1 - Finsupp.single r 1
  let α3 := α2 + Finsupp.single q 1
  let α4 := α3 + Finsupp.single p 1
  (Real.sqrt (α s) * Real.sqrt (α1 r) * Real.sqrt (α3 q) * Real.sqrt (α4 p), α4)

/-- Kinetic summand `|Ψ(α)|² Σ_k |k|² α(k)` of `⟨Ψ, H Ψ⟩` for (2.1) [ham]. -/
def kinTerm (L : ℝ) (Ψ : Occ → ℂ) (α : Occ) : ℝ :=
  ‖Ψ α‖ ^ 2 * ∑ n ∈ α.support, ‖mom L n‖ ^ 2 * (α n : ℝ)

/-- Interaction summand of `⟨Ψ, H Ψ⟩` for (2.1) [ham], indexed by `(p, q, u, α)`:
`|Λ|⁻¹ V_u conj(Ψ(β)) ⟨β| a†_p a†_q a_{p-u} a_{q+u} |α⟩ Ψ(α)`. -/
def intTerm (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Idx × Occ) : ℂ :=
  let p := i.1; let q := i.2.1; let u := i.2.2.1; let α := i.2.2.2
  let t := a4 p q (p - u) (q + u) α
  (L ^ 3)⁻¹ * ft V (mom L u) * conj (Ψ t.2) * (t.1 : ℂ) * Ψ α

/-- `Ψ` has energy `E = ⟨Ψ, H Ψ⟩` for (2.1) [ham] on the torus of side `L`: the kinetic and
the interaction series converge unconditionally and add up to `E`. -/
def HasEnergy (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (E : ℝ) : Prop :=
  ∃ K : ℝ, ∃ I : ℂ, HasSum (kinTerm L Ψ) K ∧ HasSum (intTerm L V Ψ) I ∧ (E : ℂ) = K + I

/-- `Ψ` is a normalized state of `𝓗_N` in the occupation-number basis. -/
def IsNState (N : ℕ) (Ψ : Occ → ℂ) : Prop :=
  HasSum (fun α => ‖Ψ α‖ ^ 2) 1 ∧ ∀ α, Ψ α ≠ 0 → α.num = N

/-- The ground state energy per particle `e₀^P(ρ, Λ)` for (2.1) [ham] on `Λ = [0,L]³` with
periodic boundary condition (§2), as the infimum of `⟨Ψ, HΨ⟩ / N` over finitely supported
normalized `Ψ ∈ 𝓗_N`. -/
def e0P (L : ℝ) (V : R3 → ℝ) (N : ℕ) : EReal :=
  ⨅ (Ψ : Occ →₀ ℂ) (E : ℝ) (_ : IsNState N Ψ ∧ HasEnergy L V Ψ E), ((E / N : ℝ) : EReal)

/-- The free condensate `|N, 0, 0, …⟩` is a normalized state of `𝓗_N`. -/
example (N : ℕ) : IsNState N (Finsupp.single (Finsupp.single (0 : Idx) N) (1 : ℂ)) := by
  refine ⟨?_, ?_⟩
  · have h := hasSum_single
      (f := fun α : Occ => ‖(Finsupp.single (Finsupp.single (0 : Idx) N) (1 : ℂ)) α‖ ^ 2)
      (Finsupp.single (0 : Idx) N)
      (fun b hb => by simp [Ne.symm hb])
    simpa using h
  · intro α hα
    rw [Finsupp.single_apply] at hα
    split_ifs at hα with h
    · subst h
      simp [Occ.num, Finsupp.sum_single_index]
    · exact absurd rfl hα

/-- The free condensate has energy `V₀ N (N - 1) / |Λ|` for (2.1) [ham]. -/
example (L : ℝ) (V : R3 → ℝ) (N : ℕ) :
    HasEnergy L V (Finsupp.single (Finsupp.single (0 : Idx) N) (1 : ℂ))
      ((ft V 0).re * N * ((N : ℝ) - 1) / L ^ 3) := by
  set α₀ : Occ := Finsupp.single (0 : Idx) N with hα₀
  have hΨ : ∀ β, (Finsupp.single α₀ (1 : ℂ) : Occ → ℂ) β = if β = α₀ then 1 else 0 := by
    intro β
    simp [Finsupp.single_apply, eq_comm]
  have hmom : mom L 0 = 0 := by
    ext i
    simp [mom]
  have hft : ft V 0 = ((ft V 0).re : ℂ) := by
    have h : ft V 0 = ((∫ x, V x : ℝ) : ℂ) := by
      simp only [ft, inner_zero_left, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
        one_mul]
      exact integral_ofReal
    rw [h, Complex.ofReal_re]
  refine ⟨0, (L ^ 3)⁻¹ * ft V 0 * ((N : ℂ) * ((N : ℂ) - 1)), ?_, ?_, ?_⟩
  · have h : kinTerm L (Finsupp.single α₀ (1 : ℂ)) = 0 := by
      funext β
      by_cases hβ : β = α₀
      · subst hβ
        refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun n hn => ?_)
        rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hn), hmom]
        simp
      · simp [kinTerm, hΨ, hβ]
    rw [h]
    exact hasSum_zero
  · have hzero : ∀ i ≠ ((0 : Idx), (0 : Idx), (0 : Idx), α₀),
        intTerm L V (Finsupp.single α₀ (1 : ℂ)) i = 0 := by
      rintro ⟨p, q, u, α⟩ hi
      by_contra hne
      simp only [intTerm, a4, mul_eq_zero, not_or, map_eq_zero, Complex.ofReal_eq_zero,
        hΨ, ite_eq_right_iff, one_ne_zero, imp_false, not_not, Real.sqrt_eq_zero',
        not_le, Nat.cast_pos] at hne
      obtain ⟨⟨⟨⟨hL, hV⟩, h2⟩, ⟨⟨h3, h4⟩, h5⟩, h6⟩, h7⟩ := hne
      subst h7
      have hs : q + u = 0 := by
        by_contra h
        simp [hα₀, Ne.symm h] at h3
      have hr : p - u = 0 := by
        by_contra h
        simp [hα₀, Ne.symm h, hs] at h4
      have hp : p = 0 := by
        by_contra h
        have := congrArg (fun f : Occ => f p) h2
        simp [hα₀, Finsupp.single_apply, Ne.symm h] at this
      have hq : q = 0 := by
        by_contra h
        have := congrArg (fun f : Occ => f q) h2
        simp [hα₀, Finsupp.single_apply, Ne.symm h] at this
      subst hp hq
      have hu : u = 0 := by simpa using hs
      exact hi (by rw [hu])
    convert hasSum_single _ hzero using 1
    simp only [intTerm, a4, sub_self, add_zero, hmom, hΨ]
    rcases Nat.lt_or_ge N 2 with hN | hN
    · interval_cases N <;> simp [hα₀]
    · obtain ⟨M, rfl⟩ : ∃ M, N = M + 2 := ⟨N - 2, by omega⟩
      have h4 : (((α₀ - Finsupp.single 0 1) - Finsupp.single 0 1) + Finsupp.single 0 1) +
          Finsupp.single 0 1 = α₀ := by
        ext n
        by_cases hn : n = 0 <;> simp [hα₀, hn]
      rw [h4]
      simp [hα₀]
      left
      have ha : (√((M : ℝ) + 2) : ℂ) * √((M : ℝ) + 2) = (M : ℂ) + 2 := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
        push_cast
        ring
      have hb : (√((M : ℝ) + 1) : ℂ) * √((M : ℝ) + 1) = (M : ℂ) + 1 := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
        push_cast
        ring
      linear_combination (-(↑M + 1 : ℂ)) * ha - (√((M : ℝ) + 2) : ℂ) * √((M : ℝ) + 2) * hb
  · rw [hft, Complex.ofReal_re]
    push_cast
    ring

end LHYUpper
