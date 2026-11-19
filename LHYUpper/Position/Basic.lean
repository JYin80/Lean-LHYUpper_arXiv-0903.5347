import LHYUpper.Scattering.Solution

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Position-space plane waves and the symmetrized wave function

Position-space objects of the torus `[0, L]³`: the lattice vectors `lat`, the cells `cell` and
`cellN`, the normalized plane waves `planeWave` (orthonormal in `L²([0, L]³)`), the symmetrized wave
`symWave` `Φ_α` and the wave function `stateFn` `Φ_Ψ = Σ_α Ψ(α) Φ_α`, together with its periodicity.
Also defines the kinetic density `kinD`, the pair potential `pairPot`, and `L`-periodicity
`IsPeriodicN` on configurations (§2). -/

/-- The lattice vector `L n ∈ Lℤ³` of the torus `[0, L]³`. -/
def lat (L : ℝ) (n : Idx) : R3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun a => L * (n a : ℝ))

/-- The period cell `[0, L]³`. -/
def cell (L : ℝ) : Set R3 := {y | ∀ a, 0 ≤ y a ∧ y a ≤ L}

/-- The period cell `[0, L]^{3N}` of `N` particles. -/
def cellN (L : ℝ) (N : ℕ) : Set (Conf N) := {x | ∀ i, x i ∈ cell L}

/-- The normalized plane wave `e_n(y) = L^{-3/2} e^{i k·y}`, `k = (2π/L) n ∈ Λ*`. -/
def planeWave (L : ℝ) (n : Idx) (y : R3) : ℂ :=
  ((Real.sqrt (L ^ 3))⁻¹ : ℂ) * Complex.exp (Complex.I * ((inner ℝ (mom L n) y : ℝ) : ℂ))

/-- The momentum assignments `p : Fin N → ℤ³` with occupation numbers `α`. -/
def occFns (N : ℕ) (α : Occ) : Finset (Fin N → Idx) :=
  (Fintype.piFinset fun _ : Fin N => α.support).filter
    (fun p => ∀ k, (Finset.univ.filter fun i => p i = k).card = α k)

/-- The symmetrized plane wave `Φ_α = (∏_k α(k)! / N!)^{1/2} Σ_p ∏_i e_{p_i}(x_i)` of the
occupation state `|α⟩ ∈ 𝓗_N`; the sum runs over the assignments `p` with occupation `α`. -/
def symWave (L : ℝ) (N : ℕ) (α : Occ) (x : Conf N) : ℂ :=
  (Real.sqrt ((α.prod fun _ m => (m.factorial : ℝ)) / (N.factorial : ℝ)) : ℂ) *
    ∑ p ∈ occFns N α, ∏ i, planeWave L (p i) (x i)

/-- The wave function `Φ_Ψ = Σ_α Ψ(α) Φ_α` of a finitely supported state `Ψ`. -/
def stateFn (L : ℝ) (N : ℕ) (Ψ : Occ →₀ ℂ) (x : Conf N) : ℂ :=
  ∑ α ∈ Ψ.support, Ψ α * symWave L N α x

private lemma mom_apply (L : ℝ) (n : Idx) (a : Fin 3) :
    (mom L n) a = 2 * π / L * (n a : ℝ) := rfl

private lemma lat_apply (L : ℝ) (n : Idx) (a : Fin 3) : (lat L n) a = L * (n a : ℝ) := rfl

/-- Pairing of a momentum with a lattice vector: `⟨(2π/L) m, L n⟩ = 2π m·n`. -/
private lemma inner_mom_lat {L : ℝ} (hL : L ≠ 0) (m n : Idx) :
    inner ℝ (mom L m) (lat L n) = 2 * π * ((∑ a, m a * n a : ℤ) : ℝ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mom_apply, lat_apply,
    Int.cast_sum, Int.cast_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  field_simp

private lemma planeWave_add_lat (L : ℝ) (m n : Idx) (y : R3) :
    planeWave L m (y + lat L n) = planeWave L m y := by
  unfold planeWave
  by_cases hL : L = 0
  · subst hL
    simp [PiLp.inner_apply, mom_apply, lat_apply, inner_add_right]
  · rw [inner_add_right, inner_mom_lat hL]
    rw [Complex.ofReal_add, mul_add]
    have h2 : Complex.I * ((2 * π * ((∑ a, m a * n a : ℤ) : ℝ) : ℝ) : ℂ) =
        ((∑ a, m a * n a : ℤ) : ℂ) * (2 * π * Complex.I) := by
      push_cast; ring
    rw [h2, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `conj e_m(y) · e_n(y) = L^{-3} ∏_a e^{i (2π/L)(n_a - m_a) y_a}`. -/
private lemma planeWave_conj_mul {L : ℝ} (hL : 0 < L) (m n : Idx) (y : R3) :
    conj (planeWave L m y) * planeWave L n y =
      (((L ^ 3)⁻¹ : ℝ) : ℂ) *
        ∏ a : Fin 3, Complex.exp (Complex.I * (((2 * π / L * ((n a - m a : ℤ) : ℝ) : ℝ) : ℂ) *
          ((y a : ℝ) : ℂ))) := by
  have hs : ((Real.sqrt (L ^ 3))⁻¹ : ℂ) * ((Real.sqrt (L ^ 3))⁻¹ : ℂ) = (((L ^ 3)⁻¹ : ℝ) : ℂ) := by
    have h0 : (0 : ℝ) ≤ L ^ 3 := by positivity
    have : (Real.sqrt (L ^ 3))⁻¹ * (Real.sqrt (L ^ 3))⁻¹ = (L ^ 3)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt h0]
    exact_mod_cast this
  have hprod : ∏ a : Fin 3, Complex.exp (Complex.I *
      (((2 * π / L * ((n a - m a : ℤ) : ℝ) : ℝ) : ℂ) * ((y a : ℝ) : ℂ))) =
      Complex.exp (∑ a : Fin 3, Complex.I * (((2 * π / L * ((n a - m a : ℤ) : ℝ) : ℝ) : ℂ) *
          ((y a : ℝ) : ℂ))) := by
    rw [Complex.exp_sum]
  rw [hprod, planeWave, planeWave, map_mul, ← Complex.exp_conj]
  have hc : conj (((Real.sqrt (L ^ 3))⁻¹ : ℂ)) = ((Real.sqrt (L ^ 3))⁻¹ : ℂ) := by
    simp
  rw [hc]
  calc _ = (((Real.sqrt (L ^ 3))⁻¹ : ℂ) * ((Real.sqrt (L ^ 3))⁻¹ : ℂ)) *
        (Complex.exp (conj (Complex.I * ((inner ℝ (mom L m) y : ℝ) : ℂ))) *
          Complex.exp (Complex.I * ((inner ℝ (mom L n) y : ℝ) : ℂ))) := by ring
    _ = _ := by
      rw [hs, ← Complex.exp_add]
      congr 2
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mom_apply,
        map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring

private lemma cell_eq (L : ℝ) :
    cell L = (WithLp.ofLp : R3 → Fin 3 → ℝ) ⁻¹' (Set.pi Set.univ fun _ : Fin 3 => Set.Icc 0 L) := by
  ext y
  simp only [cell, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
    Set.mem_Icc]

private lemma integral_exp_cell {L : ℝ} (hL : 0 < L) (d : ℤ) :
    ∫ t in Set.Icc (0 : ℝ) L, Complex.exp (Complex.I * (((2 * π / L * (d : ℝ) : ℝ) : ℂ) *
      (t : ℂ))) = if d = 0 then (L : ℂ) else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le]
  by_cases hd : d = 0
  · subst hd
    simp
  · simp only [hd, ite_false]
    have hc : Complex.I * ((2 * π / L * (d : ℝ) : ℝ) : ℂ) ≠ 0 := by
      have : (2 * π / L * (d : ℝ) : ℝ) ≠ 0 := by
        have := Real.pi_pos
        positivity
      simpa using this
    have h1 : ∀ t : ℝ, Complex.exp (Complex.I * (((2 * π / L * (d : ℝ) : ℝ) : ℂ) * (t : ℂ))) =
        Complex.exp ((Complex.I * ((2 * π / L * (d : ℝ) : ℝ) : ℂ)) * (t : ℂ)) := fun t => by
      ring_nf
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : (Complex.I * ((2 * π / L * (d : ℝ) : ℝ) : ℂ)) * (L : ℂ) =
        (d : ℂ) * (2 * π * Complex.I) := by
      have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
    rw [h2, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- The plane waves `e_n`, `n ∈ ℤ³`, are orthonormal in `L²([0, L]³)`. -/
theorem planeWave_orthonormal {L : ℝ} (hL : 0 < L) (m n : Idx) :
    ∫ y in cell L, conj (planeWave L m y) * planeWave L n y = if m = n then 1 else 0 := by
  have hL0 : L ≠ 0 := hL.ne'
  have h1 : ∀ y : R3, conj (planeWave L m y) * planeWave L n y =
      (fun z : Fin 3 → ℝ => (((L ^ 3)⁻¹ : ℝ) : ℂ) *
        ∏ a : Fin 3, Complex.exp (Complex.I * (((2 * π / L * ((n a - m a : ℤ) : ℝ) : ℝ) : ℂ) *
          ((z a : ℝ) : ℂ)))) (WithLp.ofLp y) := fun y => planeWave_conj_mul hL m n y
  simp_rw [h1, cell_eq]
  have key := (PiLp.volume_preserving_ofLp (Fin 3)).setIntegral_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
    (fun z : Fin 3 → ℝ => (((L ^ 3)⁻¹ : ℝ) : ℂ) *
        ∏ a : Fin 3, Complex.exp (Complex.I * (((2 * π / L * ((n a - m a : ℤ) : ℝ) : ℝ) : ℂ) *
          ((z a : ℝ) : ℂ)))) (Set.pi Set.univ fun _ : Fin 3 => Set.Icc 0 L)
  rw [key, MeasureTheory.integral_const_mul]
  have hvol : (volume : Measure (Fin 3 → ℝ)) = Measure.pi fun _ => volume := rfl
  rw [hvol, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun (a : Fin 3) (t : ℝ) =>
      Complex.exp (Complex.I * (((2 * π / L * ((n a - m a : ℤ) : ℝ) : ℝ) : ℂ) * (t : ℂ))))]
  simp_rw [integral_exp_cell hL]
  by_cases hmn : m = n
  · subst hmn
    simp only [sub_self, ite_true, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp
  · simp only [hmn, ite_false]
    obtain ⟨a, ha⟩ : ∃ a, m a ≠ n a := by
      by_contra h
      exact hmn (funext fun a => by by_contra h'; exact h ⟨a, h'⟩)
    have : ∏ a : Fin 3, (if n a - m a = 0 then (L : ℂ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (by simp [sub_eq_zero, Ne.symm ha])
    rw [this, mul_zero]

/-- `Φ_α` is `L`-periodic in every particle coordinate. -/
theorem symWave_periodic (L : ℝ) (N : ℕ) (α : Occ) (x : Conf N) (n : Fin N → Idx) :
    symWave L N α (fun i => x i + lat L (n i)) = symWave L N α x := by
  unfold symWave
  have h : ∀ p : Fin N → Idx, ∏ i, planeWave L (p i) (x i + lat L (n i)) =
      ∏ i, planeWave L (p i) (x i) := fun p =>
    Finset.prod_congr rfl fun i _ => planeWave_add_lat L (p i) (n i) (x i)
  simp only [h]

/-- The kinetic density `Σ_i |∇_i Ψ(x)|²`. -/
def kinD {N : ℕ} (Ψ : Conf N → ℂ) (x : Conf N) : ℝ :=
  ∑ i, ∑ a : Fin 3, ‖fderiv ℝ Ψ x (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2

/-- The pair potential `Σ_{i ≠ j} W(x_i - x_j)`. -/
def pairPot (W : R3 → ℝ) {N : ℕ} (x : Conf N) : ℝ :=
  ∑ i, ∑ j, if i ≠ j then W (x i - x j) else 0

/-- `Φ` is `L`-periodic in every particle coordinate. -/
def IsPeriodicN (L : ℝ) {N : ℕ} (Φ : Conf N → ℂ) : Prop :=
  ∀ (x : Conf N) (n : Fin N → Idx), Φ (fun i => x i + lat L (n i)) = Φ x

end LHYUpper
