module

public import LHYUpper.Fock.Decomp
public import LHYUpper.Statements

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # The variational principle for the periodic ground state energy

Proves `variational_principle`: every normalized `N`-particle state `Ψ` with finite energy `E` on
the torus of side `L` satisfies `e₀^P ≤ E/N` (the ground state energy of the Hamiltonian (2.1)
[ham]). The proof truncates `Ψ` to finitely supported normalized states whose energies converge to
`E` (`exists_finsupp_tendsto`). -/

namespace Variational

/-- Multiplication of a state by a real coefficient function. -/
private def reweight (c : Occ → ℝ) (Ψ : Occ → ℂ) : Occ → ℂ := fun α => (c α : ℂ) * Ψ α

private theorem kinTerm_reweight (L : ℝ) (c : Occ → ℝ) (Ψ : Occ → ℂ) (α : Occ) :
    kinTerm L (reweight c Ψ) α = (c α) ^ 2 * kinTerm L Ψ α := by
  simp only [kinTerm, reweight, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

private theorem intTerm_reweight (L : ℝ) (V : R3 → ℝ) (c : Occ → ℝ) (Ψ : Occ → ℂ)
    (i : Idx × Idx × Idx × Occ) :
    intTerm L V (reweight c Ψ) i =
      ((c (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2 * c i.2.2.2 : ℝ) : ℂ) *
        intTerm L V Ψ i := by
  obtain ⟨p, q, u, α⟩ := i
  simp only [intTerm, reweight, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- A state with summable kinetic and interaction series has a real energy: the interaction sum
has vanishing imaginary part, as each of the five parts of §4 does. -/
private theorem hasEnergy_of_summable (L : ℝ) (V : R3 → ℝ) (Φ : Occ → ℂ) (K : ℝ)
    (hK : HasSum (kinTerm L Φ) K) (hS : Summable (intTerm L V Φ)) :
    HasEnergy L V Φ (K + (∑' i, intTerm L V Φ i).re) := by
  have hJ : ∀ j, HasSum (Decomp.partTerm j L V Φ) (∑' i, Decomp.partTerm j L V Φ i) := fun j => by
    have : Decomp.partTerm j L V Φ =
        {i : Idx × Idx × Idx × Occ | j.mem i.1 i.2.1 i.2.2.1}.indicator (intTerm L V Φ) := by
      funext i
      simp only [Decomp.partTerm, Set.indicator, Set.mem_ofPred_eq]
    rw [this]
    exact (hS.indicator _).hasSum
  have hsum := hasSum_sum (s := Finset.univ) fun j _ => hJ j
  simp only [Decomp.sum_partTerm] at hsum
  have him : (∑' i, intTerm L V Φ i).im = 0 := by
    rw [hS.hasSum.unique hsum, Complex.im_sum]
    exact Finset.sum_eq_zero fun j _ => Decomp.im_eq_zero_of_hasSum j L V Φ _ (hJ j)
  refine ⟨K, ∑' i, intTerm L V Φ i, hK, hS.hasSum, ?_⟩
  apply Complex.ext <;> simp [him]

/-- Truncation: finitely supported normalized states with energies converging to `E`. -/
theorem exists_finsupp_tendsto (L : ℝ) (V : R3 → ℝ) (N : ℕ) (Ψ : Occ → ℂ) (E : ℝ)
    (hΨ : IsNState N Ψ) (hE : HasEnergy L V Ψ E) :
    ∃ (Ψn : ℕ → Occ →₀ ℂ) (En : ℕ → ℝ),
      (∀ n, IsNState N (Ψn n) ∧ HasEnergy L V (Ψn n) (En n)) ∧ Tendsto En atTop (𝓝 E) := by
  obtain ⟨K, I, hK, hI, hKI⟩ := hE
  -- a point of the support
  obtain ⟨α₀, hα₀⟩ : ∃ α₀, Ψ α₀ ≠ 0 := by
    by_contra h
    have h' : ∀ α, Ψ α = 0 := fun α => by_contra fun hα => h ⟨α, hα⟩
    have h0 : HasSum (fun α => ‖Ψ α‖ ^ 2) 0 := by simp [h']
    exact one_ne_zero (hΨ.1.unique h0)
  have hα₀pos : 0 < ‖Ψ α₀‖ ^ 2 := by positivity
  -- an exhausting sequence of finite sets, all containing `α₀`
  obtain ⟨G, hG⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset Occ))
  set F : ℕ → Finset Occ := fun n => G n ∪ {α₀} with hFdef
  have hF : Tendsto F atTop atTop := tendsto_atTop_mono (fun n => Finset.subset_union_left) hG
  have hα₀F : ∀ n, α₀ ∈ F n := fun n => Finset.mem_union_right _ (Finset.mem_singleton_self _)
  set Z : ℕ → ℝ := fun n => ∑ α ∈ F n, ‖Ψ α‖ ^ 2 with hZdef
  have hZge : ∀ n, ‖Ψ α₀‖ ^ 2 ≤ Z n := fun n =>
    Finset.single_le_sum (f := fun α => ‖Ψ α‖ ^ 2) (fun α _ => by positivity) (hα₀F n)
  have hZpos : ∀ n, 0 < Z n := fun n => lt_of_lt_of_le hα₀pos (hZge n)
  have hZ : Tendsto Z atTop (𝓝 1) := (show Tendsto (fun s : Finset Occ => ∑ α ∈ s, ‖Ψ α‖ ^ 2)
    atTop (𝓝 1) from hΨ.1).comp hF
  -- the normalized truncations
  set c : ℕ → Occ → ℝ := fun n α => if α ∈ F n then (Real.sqrt (Z n))⁻¹ else 0 with hcdef
  have hc2 : ∀ n α, (c n α) ^ 2 = if α ∈ F n then (Z n)⁻¹ else 0 := by
    intro n α
    by_cases h : α ∈ F n
    · simp only [hcdef, h, ite_true, inv_pow, Real.sq_sqrt (hZpos n).le]
    · simp [hcdef, h]
  set Φ : ℕ → Occ → ℂ := fun n => reweight (c n) Ψ with hΦdef
  have hΦsupp : ∀ n α, Φ n α ≠ 0 → α ∈ F n := by
    intro n α h
    by_contra hα
    exact h (by simp [hΦdef, reweight, hcdef, hα])
  -- kinetic part
  have hKΦ : ∀ n, HasSum (kinTerm L (Φ n)) ((Z n)⁻¹ * ∑ α ∈ F n, kinTerm L Ψ α) := by
    intro n
    have h : HasSum (kinTerm L (Φ n)) (∑ α ∈ F n, kinTerm L (Φ n) α) :=
      hasSum_sum_of_ne_finset_zero (fun α hα => by
        rw [hΦdef, kinTerm_reweight, hc2]
        simp [hα])
    convert h using 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [hΦdef, kinTerm_reweight, hc2]
    simp [hα]
  have hKlim : Tendsto (fun n => (Z n)⁻¹ * ∑ α ∈ F n, kinTerm L Ψ α) atTop (𝓝 K) := by
    have h1 : Tendsto (fun n => ∑ α ∈ F n, kinTerm L Ψ α) atTop (𝓝 K) :=
      (show Tendsto (fun s : Finset Occ => ∑ α ∈ s, kinTerm L Ψ α) atTop (𝓝 K) from hK).comp hF
    simpa using (hZ.inv₀ one_ne_zero).mul h1
  -- interaction part
  have hInorm : Summable fun i => ‖intTerm L V Ψ i‖ := summable_norm_iff.mpr hI.summable
  set B : ℝ := (‖Ψ α₀‖ ^ 2)⁻¹ with hBdef
  have hprod : ∀ n m m', c n m * c n m' = if m ∈ F n ∧ m' ∈ F n then (Z n)⁻¹ else 0 := by
    intro n m m'
    by_cases h : m ∈ F n ∧ m' ∈ F n
    · rw [ite_eq_left h]
      simp only [hcdef, h.1, h.2, ite_true]
      rw [← mul_inv, Real.mul_self_sqrt (hZpos n).le]
    · rw [ite_eq_right h]
      by_cases h1 : m ∈ F n
      · have h2 : m' ∉ F n := fun h2 => h ⟨h1, h2⟩
        simp [hcdef, h2]
      · simp [hcdef, h1]
  have hBpos : ∀ n, (Z n)⁻¹ ≤ B := fun n => inv_anti₀ hα₀pos (hZge n)
  have hcc : ∀ n i, ‖intTerm L V (Φ n) i‖ ≤ B * ‖intTerm L V Ψ i‖ := by
    intro n i
    rw [hΦdef, intTerm_reweight, norm_mul, Complex.norm_real, Real.norm_eq_abs, hprod]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    split_ifs
    · rw [abs_of_nonneg (inv_nonneg.mpr (hZpos n).le)]
      exact hBpos n
    · rw [abs_zero]
      exact le_trans (inv_nonneg.mpr (hZpos n).le) (hBpos n)
  have hIsum : ∀ n, Summable (intTerm L V (Φ n)) := fun n =>
    Summable.of_norm_bounded (hInorm.mul_left B) (hcc n)
  have hIlim : Tendsto (fun n => ∑' i, intTerm L V (Φ n) i) atTop (𝓝 I) := by
    rw [← hI.tsum_eq]
    refine tendsto_tsum_of_dominated_convergence (hInorm.mul_left B) (fun i => ?_)
      (Eventually.of_forall hcc)
    have hev : ∀ᶠ n in atTop, (Z n)⁻¹ =
        c n (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2 * c n i.2.2.2 := by
      filter_upwards [hF.eventually (eventually_ge_atTop
        ({(a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2, i.2.2.2} : Finset Occ))]
        with n hn
      rw [hprod, ite_eq_left ⟨hn (by simp), hn (by simp)⟩]
    have hlim : Tendsto (fun n => (((Z n)⁻¹ : ℝ) : ℂ) * intTerm L V Ψ i) atTop
        (𝓝 (intTerm L V Ψ i)) := by
      have h1 : Tendsto (fun n => (((Z n)⁻¹ : ℝ) : ℂ)) atTop (𝓝 (((1 : ℝ) : ℂ))) :=
        (Complex.continuous_ofReal.tendsto 1).comp (by simpa using hZ.inv₀ one_ne_zero)
      simpa using h1.mul_const (intTerm L V Ψ i)
    refine hlim.congr' ?_
    filter_upwards [hev] with n hn
    rw [hΦdef, intTerm_reweight, ← hn]
  -- assembling
  have hIre : I.re = E - K := by
    have := congrArg Complex.re hKI
    simp at this
    linarith
  have hnorm : ∀ n α, ‖Φ n α‖ ^ 2 = (c n α) ^ 2 * ‖Ψ α‖ ^ 2 := by
    intro n α
    simp only [hΦdef, reweight, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hNs : ∀ n, IsNState N (Φ n) := by
    intro n
    refine ⟨?_, fun α hα => hΨ.2 α fun h0 => hα (by simp [hΦdef, reweight, h0])⟩
    have h : HasSum (fun α => ‖Φ n α‖ ^ 2) (∑ α ∈ F n, ‖Φ n α‖ ^ 2) :=
      hasSum_sum_of_ne_finset_zero (fun α hα => by
        have h0 : Φ n α = 0 := by
          by_contra h0
          exact hα (hΦsupp n α h0)
        simp [h0])
    convert h using 1
    rw [Finset.sum_congr rfl fun α hα => by rw [hnorm, hc2, ite_eq_left hα], ← Finset.mul_sum]
    exact (inv_mul_cancel₀ (hZpos n).ne').symm
  refine ⟨fun n => Finsupp.onFinset (F n) (Φ n) (hΦsupp n),
    fun n => (Z n)⁻¹ * (∑ α ∈ F n, kinTerm L Ψ α) + (∑' i, intTerm L V (Φ n) i).re,
    fun n => ⟨hNs n, hasEnergy_of_summable L V (Φ n) _ (hKΦ n) (hIsum n)⟩, ?_⟩
  have h := hKlim.add ((Complex.continuous_re.tendsto I).comp hIlim)
  have hE' : K + I.re = E := by linarith
  rw [hE'] at h
  exact h

end Variational

theorem variational_principle (V : R3 → ℝ) (hV : PotentialHyp V) :
    Stmt.VariationalPrinciple V := by
  intro L _ N Ψ E hΨ hE
  obtain ⟨Ψn, En, hn, hlim⟩ := Variational.exists_finsupp_tendsto L V N Ψ E hΨ hE
  have hle : ∀ n, e0P L V N ≤ ((En n / N : ℝ) : EReal) := fun n =>
    iInf_le_of_le (Ψn n) (iInf_le_of_le (En n) (iInf_le_of_le (hn n) le_rfl))
  exact ge_of_tendsto' ((continuous_coe_real_ereal.tendsto _).comp (hlim.div_const (N : ℝ))) hle

end LHYUpper
