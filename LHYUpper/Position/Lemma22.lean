import LHYUpper.Scattering.Solution
import LHYUpper.Position.SymWave
import LHYUpper.Position.Energy
import LHYUpper.Position.DirichletFacts
import LHYUpper.Position.Localize

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # From periodic to Dirichlet: (12.5)–(12.7) and Lemma 2.2 [lemma1]

A finitely supported normalized `N`-particle state on the torus `[0, L]³` is cut off by the maps
`𝓕^u` of (12.4) [defFu]. Averaging the kinetic error of (12.3) [3.51] over the shifts `u` gives a
Dirichlet trial function on `[0, L + 2ℓ]³` with energy at most the periodic one plus
`C_q N / (ℓL)`, (12.5)–(12.7). With `ℓ = ℓ_N = L_N ρ_N^{25/48}` and the density change
`ρ_N → ρ̃_N` this gives Lemma 2.2 [lemma1]. -/

/-- The constant `C_q = 3π² C_s / 8` of (12.7). -/
def cutConst : ℝ := 3 * π ^ 2 * rampConst / 8

/-! ### The weight `w` of (12.3) [3.51] -/

/-- The weight `w(x) = Σ_m q'(x + mL)²` of (12.3) [3.51] is `L`-periodic. -/
private lemma Lemma22_profW_periodic (ℓ L : ℝ) : Function.Periodic (profW ℓ L) L := by
  intro x
  unfold profW
  have h := (Equiv.addRight (1 : ℤ)).tsum_eq (fun m : ℤ => deriv (prof ℓ L) (x + m * L) ^ 2)
  rw [← h]
  refine tsum_congr fun m => ?_
  simp only [Equiv.coe_addRight]
  have e : x + L + m * L = x + ((m + 1 : ℤ) : ℝ) * L := by push_cast; ring
  rw [e]

/-- The weight `w` is continuous: on a bounded interval only finitely many of the translates
`q'(· + mL)²` are nonzero, since `q` vanishes outside `[-ℓ/2, L + ℓ/2]`. -/
private lemma Lemma22_profW_continuous {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) :
    Continuous (profW ℓ L) := by
  have hg : Continuous (fun y => deriv (prof ℓ L) y ^ 2) :=
    ((prof_contDiff ℓ L).continuous_deriv (by simp)).pow 2
  have hz : ∀ y, y ∉ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) → deriv (prof ℓ L) y ^ 2 = 0 := by
    intro y hy
    have h0 : deriv (prof ℓ L) y = 0 := by
      by_contra h
      exact hy (tsupport_prof hℓ L (support_deriv_subset h))
    rw [h0]
    ring
  rw [continuous_iff_continuousAt]
  intro x₀
  set B : ℤ := ⌈(L + ℓ + |x₀| + 2) / L⌉ with hB
  set S : Finset ℤ := Finset.Icc (-B) B with hS
  have key : ∀ x ∈ Set.Ioo (x₀ - 1) (x₀ + 1),
      profW ℓ L x = ∑ m ∈ S, deriv (prof ℓ L) (x + m * L) ^ 2 := by
    intro x hx
    unfold profW
    refine tsum_eq_sum fun m hm => hz _ fun hmem => hm ?_
    obtain ⟨h1, h2⟩ := hmem
    have hxa : |x - x₀| < 1 := abs_lt.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hx0 : x₀ ≤ |x₀| := le_abs_self _
    have hx1 : -|x₀| ≤ x₀ := neg_abs_le _
    have hxl : x < x₀ + 1 := hx.2
    have hxg : x₀ - 1 < x := hx.1
    have hceil : (L + ℓ + |x₀| + 2) / L ≤ (B : ℝ) := Int.le_ceil _
    have hdiv : (L + ℓ + |x₀| + 2) / L * L = L + ℓ + |x₀| + 2 := by field_simp
    have hBL : L + ℓ + |x₀| + 2 ≤ (B : ℝ) * L := by
      calc L + ℓ + |x₀| + 2 = (L + ℓ + |x₀| + 2) / L * L := hdiv.symm
        _ ≤ (B : ℝ) * L := mul_le_mul_of_nonneg_right hceil hL.le
    rw [hS, Finset.mem_Icc]
    constructor
    · have : (-(B : ℝ)) ≤ m := by
        by_contra hlt
        have hlt := not_le.1 hlt
        nlinarith
      exact_mod_cast this
    · have : (m : ℝ) ≤ B := by
        by_contra hlt
        have hlt := not_le.1 hlt
        nlinarith
      exact_mod_cast this
  have hcont : ContinuousAt (fun x => ∑ m ∈ S, deriv (prof ℓ L) (x + m * L) ^ 2) x₀ := by
    refine (continuous_finsetSum _ fun m _ => ?_).continuousAt
    exact hg.comp (continuous_id.add continuous_const)
  exact hcont.congr (eventually_of_mem (Ioo_mem_nhds (by linarith) (by linarith : x₀ < x₀ + 1))
    fun x hx => (key x hx).symm)


/-- A box `∏_b [α_b, β_b]` of `ℝ³` is compact. -/
private lemma Lemma22_box_compact (α β : Fin 3 → ℝ) :
    IsCompact {y : R3 | ∀ b, y b ∈ Set.Icc (α b) (β b)} := by
  have : {y : R3 | ∀ b, y b ∈ Set.Icc (α b) (β b)} =
      (WithLp.toLp 2 : (Fin 3 → ℝ) → R3) '' Set.pi Set.univ (fun b => Set.Icc (α b) (β b)) := by
    ext y
    constructor
    · intro hy
      exact ⟨WithLp.ofLp y, fun b _ => hy b, rfl⟩
    · rintro ⟨z, hz, rfl⟩ b
      exact hz b (Set.mem_univ b)
  rw [this]
  exact (isCompact_univ_pi fun b => isCompact_Icc).image (PiLp.continuous_toLp 2 _)

private lemma Lemma22_cellN_compact (L : ℝ) (N : ℕ) : IsCompact (cellN L N) := by
  have h : cellN L N = Set.pi Set.univ
      (fun _ : Fin N => {y : R3 | ∀ b, y b ∈ Set.Icc ((fun _ => (0 : ℝ)) b) ((fun _ => L) b)}) := by
    ext x
    simp only [cellN, cell, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_Icc]
  rw [h]
  exact isCompact_univ_pi fun _ => Lemma22_box_compact _ _

/-! ### Averaging over the shift `u`, (12.6) -/

/-- `∫_{s ∈ [0, L]} w(c + s) ds = ∫_0^L w = C_s π² / (8ℓ)`, by periodicity of `w`. -/
private lemma Lemma22_integral_shift {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) (c : ℝ) :
    ∫ s in Set.Icc (0 : ℝ) L, profW ℓ L (c + s) = rampConst * π ^ 2 / (8 * ℓ) := by
  have hL : 0 < L := by linarith
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le,
    intervalIntegral.integral_comp_add_left (profW ℓ L) c]
  have h := (Lemma22_profW_periodic ℓ L).intervalIntegral_add_eq c 0
  rw [add_zero, h, zero_add]
  exact integral_profW hℓ hℓL

/-- The averaging step of (12.6) in one coordinate: for a continuous `Φ` with
`∫_{[0, L]^{3N}} |Φ|² = 1` some shift `s ∈ [0, L]` gives
`Σ_i ∫_{[0, L]^{3N}} |Φ|² w(x_{ia} + s) ≤ N C_s π² / (8ℓL)`. -/
private lemma Lemma22_exists_shift {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) {N : ℕ}
    {Φ : Conf N → ℂ} (hc : Continuous Φ) (hn : ∫ x in cellN L N, ‖Φ x‖ ^ 2 = 1) (a : Fin 3) :
    ∃ s ∈ Set.Icc (0 : ℝ) L,
      ∫ x in cellN L N, ∑ i, ‖Φ x‖ ^ 2 * profW ℓ L (x i a + s) ≤
        N * (rampConst * π ^ 2 / (8 * ℓ)) / L := by
  have hL : 0 < L := by linarith
  have hw := Lemma22_profW_continuous hℓ hL
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = rampConst * π ^ 2 / (8 * ℓ) := ⟨_, rfl⟩
  have hshift : ∀ c : ℝ, ∫ s in Set.Icc (0 : ℝ) L, profW ℓ L (c + s) = I := fun c => by
    rw [hI]
    exact Lemma22_integral_shift hℓ hℓL c
  rw [← hI]
  set f : Conf N → ℝ → ℝ := fun x s => ∑ i, ‖Φ x‖ ^ 2 * profW ℓ L (x i a + s) with hf
  have hfc : Continuous (Function.uncurry f) := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact ((hc.comp continuous_fst).norm.pow 2).mul (hw.comp (by fun_prop))
  have hcpt := Lemma22_cellN_compact L N
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (cellN L N)).prod (volume.restrict (Set.Icc (0 : ℝ) L))) := by
    rw [Measure.prod_restrict]
    exact hfc.continuousOn.integrableOn_compact (hcpt.prod isCompact_Icc)
  have hswap := integral_integral_swap hint
  have hinner : ∀ x : Conf N, ∫ s in Set.Icc (0 : ℝ) L, f x s = N * (‖Φ x‖ ^ 2 * I) := by
    intro x
    simp only [hf]
    rw [integral_finsetSum]
    · simp_rw [integral_const_mul, hshift]
      simp
    · intro i _
      exact (continuous_const.mul (hw.comp (by fun_prop))).continuousOn.integrableOn_compact
        isCompact_Icc
  have hL1 : ∫ x in cellN L N, ∫ s in Set.Icc (0 : ℝ) L, f x s = N * I := by
    simp_rw [hinner]
    rw [integral_const_mul, integral_mul_const, hn]
    ring
  have hκ : Integrable (fun s => ∫ x in cellN L N, f x s) (volume.restrict (Set.Icc (0 : ℝ) L)) :=
    hint.integral_prod_right
  have hR : ∫ s in Set.Icc (0 : ℝ) L, ∫ x in cellN L N, f x s = N * I := by
    rw [← hswap, hL1]
  obtain ⟨s, hs, hle⟩ := exists_le_setAverage (μ := volume) (s := Set.Icc (0 : ℝ) L)
    (f := fun s => ∫ x in cellN L N, f x s) (by simp [hL]) (by simp) hκ
  refine ⟨s, hs, ?_⟩
  rw [setAverage_eq, hR] at hle
  have hvol : volume.real (Set.Icc (0 : ℝ) L) = L := by
    simp [measureReal_def, hL.le]
  rw [hvol, smul_eq_mul] at hle
  calc _ ≤ _ := hle
    _ = N * I / L := by ring


/-! ### The localized state -/

/-- The cut-off product `∏_j ∏_b q(x_{jb} + u_b)` of (12.4) [defFu]. -/
private def Lemma22_G (ℓ L : ℝ) (u : R3) {N : ℕ} (x : Conf N) : ℝ :=
  ∏ j, ∏ b, prof ℓ L (x j b + u b)

/-- `𝓕^u Φ = Φ · ∏_{j,b} q(x_{jb} + u_b)` (12.4) [defFu]. -/
private lemma Lemma22_localize_eq (ℓ L : ℝ) (u : R3) {N : ℕ} (Φ : Conf N → ℂ) :
    localize ℓ L u Φ = fun x => Φ x * ((Lemma22_G ℓ L u x : ℝ) : ℂ) := by
  funext x
  simp [localize, cutoff, Lemma22_G, Complex.ofReal_prod, PiLp.add_apply]

/-- The cut-off product is smooth. -/
private lemma Lemma22_G_contDiff (ℓ L : ℝ) (u : R3) (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Conf N => Lemma22_G ℓ L u x) :=
  contDiff_prod fun j _ => contDiff_prod fun b _ =>
    (prof_contDiff ℓ L).comp (by fun_prop)

/-- The cut-off product is symmetric. -/
private lemma Lemma22_G_perm (ℓ L : ℝ) (u : R3) {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Conf N) :
    Lemma22_G ℓ L u (x ∘ σ) = Lemma22_G ℓ L u x := by
  unfold Lemma22_G
  exact Equiv.prod_comp σ (fun j => ∏ b, prof ℓ L (x j b + u b))

/-- The cut-off product vanishes unless every `x_{jb} + u_b` lies in `[-ℓ/2, L + ℓ/2]`. -/
private lemma Lemma22_G_support {ℓ L : ℝ} (hℓ : 0 < ℓ) (u : R3) {N : ℕ} {x : Conf N}
    (h : Lemma22_G ℓ L u x ≠ 0) : ∀ j b, x j b + u b ∈ Set.Icc (-(ℓ / 2)) (L + ℓ / 2) := by
  intro j b
  by_contra hb
  apply h
  unfold Lemma22_G
  refine Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero (Finset.mem_univ b) ?_)
  by_contra h0
  exact hb (tsupport_prof hℓ L (subset_tsupport _ h0))

/-- `Φ_Ψ = Σ_α Ψ(α) Φ_α`. -/
private lemma Lemma22_stateFn_eq (L : ℝ) (N : ℕ) (Ψ : Occ →₀ ℂ) :
    stateFn L N Ψ = fun x => ∑ α ∈ Ψ.support, Ψ α * symWave L N α x := rfl

/-- `Φ_Ψ` is smooth. -/
private lemma Lemma22_stateFn_contDiff (L : ℝ) (N : ℕ) (Ψ : Occ →₀ ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (stateFn L N Ψ) := by
  rw [Lemma22_stateFn_eq]
  exact ContDiff.sum fun α _ => contDiff_const.mul (symWave_contDiff L N α)

/-- `Φ_Ψ` is `L`-periodic in every particle coordinate. -/
private lemma Lemma22_stateFn_periodic (L : ℝ) (N : ℕ) (Ψ : Occ →₀ ℂ) :
    IsPeriodicN L (stateFn L N Ψ) := by
  intro x n
  rw [Lemma22_stateFn_eq]
  simp only [symWave_periodic]

/-- `Φ_Ψ` is symmetric. -/
private lemma Lemma22_stateFn_perm (L : ℝ) (N : ℕ) (Ψ : Occ →₀ ℂ) (σ : Equiv.Perm (Fin N))
    (x : Conf N) : stateFn L N Ψ (x ∘ σ) = stateFn L N Ψ x := by
  rw [Lemma22_stateFn_eq]
  simp only [symWave_perm]

/-- The pair potential of a continuous `W` is continuous. -/
private lemma Lemma22_pairPot_continuous {W : R3 → ℝ} (hW : Continuous W) {N : ℕ} :
    Continuous (fun x : Conf N => pairPot W x) := by
  unfold pairPot
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  split_ifs
  · exact hW.comp ((continuous_apply i).sub (continuous_apply j))
  · exact continuous_const

/-- The kinetic density of a smooth function is continuous. -/
private lemma Lemma22_kinD_continuous {N : ℕ} {Φ : Conf N → ℂ}
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) : Continuous (kinD Φ) := by
  have h := hΦ.continuous_fderiv (by simp)
  unfold kinD
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun a _ =>
    (h.clm_apply continuous_const).norm.pow 2

/-- A continuous function is integrable over `[0, L]^{3N}`. -/
private lemma Lemma22_integrable_cell {L : ℝ} {N : ℕ} {f : Conf N → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict (cellN L N)) :=
  hf.continuousOn.integrableOn_compact (Lemma22_cellN_compact L N)

/-- The set `{y | ∀ i a, y_{ia} ∈ [ℓ/2, L + 3ℓ/2]}` that contains the support of the shifted trial
function. -/
private def Lemma22_B (ℓ L : ℝ) (N : ℕ) : Set (Conf N) :=
  Set.pi Set.univ fun _ : Fin N => {y : R3 | ∀ b, y b ∈ Set.Icc (ℓ / 2) (L + 3 * ℓ / 2)}

/-- The box `{y | ∀ i a, y_{ia} ∈ [ℓ/2, L + 3ℓ/2]}` is compact. -/
private lemma Lemma22_B_compact (ℓ L : ℝ) (N : ℕ) : IsCompact (Lemma22_B ℓ L N) :=
  isCompact_univ_pi fun _ => Lemma22_box_compact (fun _ => ℓ / 2) (fun _ => L + 3 * ℓ / 2)

/-- Membership in the box `{y | ∀ i a, y_{ia} ∈ [ℓ/2, L + 3ℓ/2]}`. -/
private lemma Lemma22_mem_B {ℓ L : ℝ} {N : ℕ} {y : Conf N} :
    y ∈ Lemma22_B ℓ L N ↔ ∀ i b, y i b ∈ Set.Icc (ℓ / 2) (L + 3 * ℓ / 2) := by
  simp [Lemma22_B]

/-- The set `{x | ∀ j b, x_{jb} + u_b ∈ [-ℓ/2, L + ℓ/2]}`, the support of `𝓕^uΦ`. -/
private def Lemma22_Bu (ℓ L : ℝ) (u : R3) (N : ℕ) : Set (Conf N) :=
  Set.pi Set.univ fun _ : Fin N =>
    {y : R3 | ∀ b, y b ∈ Set.Icc (-(ℓ / 2) - u b) (L + ℓ / 2 - u b)}

/-- The set `{x | ∀ j b, x_{jb} + u_b ∈ [-ℓ/2, L + ℓ/2]}` is compact. -/
private lemma Lemma22_Bu_compact (ℓ L : ℝ) (u : R3) (N : ℕ) : IsCompact (Lemma22_Bu ℓ L u N) :=
  isCompact_univ_pi fun _ => Lemma22_box_compact _ _

/-- `𝓕^u Φ` vanishes outside `{x | ∀ j b, x_{jb} + u_b ∈ [-ℓ/2, L + ℓ/2]}`. -/
private lemma Lemma22_support_localize {ℓ L : ℝ} (hℓ : 0 < ℓ) (u : R3) {N : ℕ}
    (Φ : Conf N → ℂ) (x : Conf N) (hx : x ∉ Lemma22_Bu ℓ L u N) : localize ℓ L u Φ x = 0 := by
  rw [Lemma22_localize_eq]
  dsimp only
  by_contra hne
  have hG : Lemma22_G ℓ L u x ≠ 0 := fun h => hne (by rw [h]; simp)
  apply hx
  have := Lemma22_G_support hℓ u hG
  simp only [Lemma22_Bu, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq,
    Set.mem_Icc]
  intro j b
  have h := this j b
  constructor <;> linarith [h.1, h.2]


/-- The averaging step (12.6): a shift `u` with
`Σ_{i,a} ∫_{[0, L]^{3N}} |Φ|² w(x_{ia} + u_a) ≤ C_q N / (ℓL)`. -/
private lemma Lemma22_exists_u {ℓ L : ℝ} (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) {N : ℕ}
    {Φ : Conf N → ℂ} (hc : Continuous Φ) (hn : ∫ x in cellN L N, ‖Φ x‖ ^ 2 = 1) :
    ∃ u : R3, ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x in cellN L N, ‖Φ x‖ ^ 2 * profW ℓ L (x i a + u a) ≤ cutConst * N / (ℓ * L) := by
  have hL : 0 < L := by linarith
  have hw := Lemma22_profW_continuous hℓ hL
  choose s _ hs using fun a : Fin 3 => Lemma22_exists_shift hℓ hℓL hc hn a
  refine ⟨(WithLp.equiv 2 (Fin 3 → ℝ)).symm s, ?_⟩
  have hcomm : ∑ i : Fin N, ∑ a : Fin 3,
      ∫ x in cellN L N, ‖Φ x‖ ^ 2 * profW ℓ L (x i a + ((WithLp.equiv 2 (Fin 3 → ℝ)).symm s) a) =
      ∑ a : Fin 3, ∫ x in cellN L N, ∑ i, ‖Φ x‖ ^ 2 * profW ℓ L (x i a + s a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum]
    · rfl
    · intro i _
      exact Lemma22_integrable_cell (((hc.norm.pow 2).mul (hw.comp (by fun_prop))))
  rw [hcomm]
  calc ∑ a : Fin 3, ∫ x in cellN L N, ∑ i, ‖Φ x‖ ^ 2 * profW ℓ L (x i a + s a)
      ≤ ∑ _a : Fin 3, N * (rampConst * π ^ 2 / (8 * ℓ)) / L :=
        Finset.sum_le_sum fun a _ => hs a
    _ = cutConst * N / (ℓ * L) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, cutConst]
        field_simp
        push_cast
        ring

/-- (12.5)–(12.7): a finitely supported normalized `N`-particle state with energy `E` on the
torus `[0, L]³` gives a Dirichlet trial function on `[0, L + 2ℓ]³` with energy at most
`E + C_q N / (ℓL)`. -/
theorem exists_dirichlet_of_periodic {V : R3 → ℝ} (hV : PotentialHyp V) {L ℓ : ℝ}
    (hℓ : 0 < ℓ) (hℓL : 2 * ℓ < L) {N : ℕ} (Ψ : Occ →₀ ℂ) {E : ℝ} (hΨ : IsNState N Ψ)
    (hE : HasEnergy L V Ψ E) :
    ∃ Φ : Conf N → ℂ, IsDirichletTrial (L + 2 * ℓ) N Φ ∧
      energyD V Φ ≤ E + cutConst * N / (ℓ * L) := by
  have hL : 0 < L := by linarith
  obtain ⟨hnorm, hen⟩ := stateFn_norm_energy hV hL Ψ hΨ hE
  set Φ : Conf N → ℂ := stateFn L N Ψ with hΦdef
  have hΦd : ContDiff ℝ (⊤ : ℕ∞) Φ := Lemma22_stateFn_contDiff L N Ψ
  have hΦc : Continuous Φ := hΦd.continuous
  have hΦp : IsPeriodicN L Φ := Lemma22_stateFn_periodic L N Ψ
  obtain ⟨u, hu⟩ := Lemma22_exists_u hℓ hℓL hΦc hnorm
  set H : Conf N → ℂ := localize ℓ L u Φ with hHdef
  have hHeq : H = fun x => Φ x * ((Lemma22_G ℓ L u x : ℝ) : ℂ) := Lemma22_localize_eq ℓ L u Φ
  have hHd : ContDiff ℝ (⊤ : ℕ∞) H := by
    rw [hHeq]
    exact hΦd.mul (Complex.ofRealCLM.contDiff.comp (Lemma22_G_contDiff ℓ L u N))
  have hHc : Continuous H := hHd.continuous
  have hHcs : HasCompactSupport H :=
    HasCompactSupport.intro (Lemma22_Bu_compact ℓ L u N)
      (fun x hx => Lemma22_support_localize hℓ u Φ x hx)
  -- the energy of `H`
  have hkin_int : Integrable (kinD H) := by
    refine (Lemma22_kinD_continuous hHd).integrable_of_hasCompactSupport ?_
    have h1 := (hHcs.fderiv ℝ)
    exact h1.comp_left (g := fun A : Conf N →L[ℝ] ℂ =>
      ∑ i, ∑ a : Fin 3, ‖A (Pi.single i (EuclideanSpace.single a 1))‖ ^ 2) (by simp)
  have hpot_int : Integrable (fun x => pairPot V x * ‖H x‖ ^ 2) := by
    obtain ⟨S, hS⟩ := hV.schwartz
    have hVc : Continuous V := hS ▸ S.continuous
    refine ((Lemma22_pairPot_continuous hVc).mul (hHc.norm.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro (Lemma22_Bu_compact ℓ L u N) fun x hx => ?_)
    have h0 : H x = 0 := Lemma22_support_localize hℓ u Φ x hx
    simp [h0]
  have hE_H : energyD V H = (∫ x, kinD H x) + ∫ x, pairPot V x * ‖H x‖ ^ 2 := by
    rw [← integral_add hkin_int hpot_int]
    rfl
  have hk := localize_kin hℓ hℓL u (Φ := Φ) (hΦd.of_le (by simp)) hΦp
  have hp := localize_pot hV hℓ hℓL u (Φ := Φ) hΦc hΦp
  rw [← hHdef] at hk hp
  have hkΦ : Continuous (kinD Φ) := Lemma22_kinD_continuous hΦd
  have hpΦ : Continuous (fun x => pairPot (periodize L V) x * ‖Φ x‖ ^ 2) :=
    (Lemma22_pairPot_continuous (periodize_continuous hV hL)).mul (hΦc.norm.pow 2)
  have hT : torusEnergy L V Φ = (∫ x in cellN L N, kinD Φ x) +
      ∫ x in cellN L N, pairPot (periodize L V) x * ‖Φ x‖ ^ 2 := by
    unfold torusEnergy
    exact integral_add (Lemma22_integrable_cell hkΦ) (Lemma22_integrable_cell hpΦ)
  have hbound : energyD V H ≤ E + cutConst * N / (ℓ * L) := by
    rw [hE_H, hk, ← hen, hT]
    linarith
  -- the translated trial function
  set c : R3 := u + (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun _ => ℓ) with hcdef
  have hcu : ∀ (y : Conf N) (i : Fin N) (b : Fin 3), (y i - c) b + u b = y i b - ℓ := by
    intro y i b
    simp [hcdef]
    ring
  have hsuppB : ∀ y : Conf N, H (fun i => y i - c) ≠ 0 → y ∈ Lemma22_B ℓ L N := by
    intro y hy
    have hG : Lemma22_G ℓ L u (fun i => y i - c) ≠ 0 := by
      intro h0
      apply hy
      rw [hHeq]
      dsimp only
      rw [h0]
      simp
    have := Lemma22_G_support hℓ u hG
    rw [Lemma22_mem_B]
    intro i b
    have h := this i b
    rw [hcu] at h
    constructor <;> linarith [h.1, h.2]
  refine ⟨fun y => H (fun i => y i - c), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hHd.comp (contDiff_pi.2 fun i =>
      (contDiff_apply ℝ (fun _ : Fin N => R3) i).sub contDiff_const)
  · exact HasCompactSupport.intro (Lemma22_B_compact ℓ L N) fun y hy => by
      by_contra h
      exact hy (hsuppB y h)
  · refine (closure_minimal (fun y hy => hsuppB y hy) (Lemma22_B_compact ℓ L N).isClosed).trans ?_
    intro y hy i b
    have := Lemma22_mem_B.1 hy i b
    constructor <;> linarith [this.1, this.2]
  · intro σ y
    have e : (fun i => (y ∘ σ) i - c) = (fun i => y i - c) ∘ σ := rfl
    change H (fun i => (y ∘ σ) i - c) = H (fun i => y i - c)
    rw [e, hHeq]
    dsimp only
    have hperm : ∀ (σ : Equiv.Perm (Fin N)) (x : Conf N), Φ (x ∘ σ) = Φ x :=
      fun σ x => Lemma22_stateFn_perm L N Ψ σ x
    rw [Lemma22_G_perm, hperm]
  · set cc : Conf N → Conf N := fun _ => fun _ => c with hcc
    have e : ∀ y : Conf N, (fun i => y i - c) = y - (fun _ => c) := fun y => rfl
    simp_rw [e]
    rw [integral_sub_right_eq_self (fun x : Conf N => ‖H x‖ ^ 2) (fun _ => c)]
    have := localize_norm hℓ hℓL u hΦc hΦp
    rw [← hHdef] at this
    rw [this, hnorm]
  · rw [energyD_translate V H c]
    exact hbound


/-- `C_s ≥ 0`, as an integral of a square. -/
private lemma Lemma22_rampConst_nonneg : 0 ≤ rampConst :=
  intervalIntegral.integral_nonneg (by norm_num) fun _ _ => sq_nonneg _

/-- `C_q ≥ 0`. -/
private lemma Lemma22_cutConst_nonneg : 0 ≤ cutConst := by
  unfold cutConst
  have := Lemma22_rampConst_nonneg
  positivity

/-- (12.7) for the ground state energies: `e₀^D` on `[0, L + 2ℓ]³` is at most `e₀^P` on
`[0, L]³` plus `C_q / (ℓL)`. -/
theorem e0D_le_e0P {V : R3 → ℝ} (hV : PotentialHyp V) {L ℓ : ℝ} (hℓ : 0 < ℓ)
    (hℓL : 2 * ℓ < L) (N : ℕ) :
    e0D (L + 2 * ℓ) V N ≤ e0P L V N + ((cutConst / (ℓ * L) : ℝ) : EReal) := by
  have hL : 0 < L := by linarith
  have hL' : 0 < L + 2 * ℓ := by linarith
  have hc : 0 ≤ cutConst / (ℓ * L) := div_nonneg Lemma22_cutConst_nonneg (by positivity)
  obtain ⟨d, hd⟩ : ∃ d : ℝ, e0D (L + 2 * ℓ) V N = (d : EReal) :=
    ⟨(e0D (L + 2 * ℓ) V N).toReal, (EReal.coe_toReal (e0D_lt_top hL' V N).ne
      (ne_bot_of_le_ne_bot (by simp) (e0D_nonneg hV.nonneg _ _))).symm⟩
  have key : ∀ (Ψ : Occ →₀ ℂ) (E : ℝ), IsNState N Ψ ∧ HasEnergy L V Ψ E →
      d ≤ E / N + cutConst / (ℓ * L) := by
    intro Ψ E h
    obtain ⟨Φ, hΦ, hΦE⟩ := exists_dirichlet_of_periodic hV hℓ hℓL Ψ h.1 h.2
    have h1 : e0D (L + 2 * ℓ) V N ≤ ((energyD V Φ / N : ℝ) : EReal) :=
      iInf₂_le (f := fun (Ψ : Conf N → ℂ) (_ : IsDirichletTrial (L + 2 * ℓ) N Ψ) =>
        ((energyD V Ψ / N : ℝ) : EReal)) Φ hΦ
    rw [hd, EReal.coe_le_coe_iff] at h1
    refine h1.trans ?_
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN
      simpa using hc
    · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      calc energyD V Φ / N ≤ (E + cutConst * N / (ℓ * L)) / N :=
            div_le_div_of_nonneg_right hΦE hNpos.le
        _ = E / N + cutConst / (ℓ * L) := by
            field_simp
  have hle : ((d - cutConst / (ℓ * L) : ℝ) : EReal) ≤ e0P L V N :=
    le_iInf fun Ψ => le_iInf fun E => le_iInf fun h =>
      EReal.coe_le_coe_iff.2 (by linarith [key Ψ E h])
  calc e0D (L + 2 * ℓ) V N = ((d : ℝ) : EReal) := hd
    _ = ((d - cutConst / (ℓ * L) : ℝ) : EReal) + ((cutConst / (ℓ * L) : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        norm_num
    _ ≤ e0P L V N + ((cutConst / (ℓ * L) : ℝ) : EReal) := add_le_add hle le_rfl


/-! ### Lemma 2.2 [lemma1]: the density change `ρ → ρ̃` -/

/-- `ρ_N > 0`, `L_N > 0` and `ρ_N L_N³ = N` for `N ≥ 1`. -/
private lemma Lemma22_rhoN_facts {N : ℕ} (hN : 1 ≤ N) :
    0 < rhoN N ∧ 0 < LN N ∧ rhoN N * LN N ^ 3 = N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 < rhoN N := Real.rpow_pos_of_pos hNpos _
  have hL : LN N = (N : ℝ) ^ (25 / 51 : ℝ) := by
    rw [LN, rhoN, ← Real.rpow_mul hNpos.le]
    norm_num
  refine ⟨hρ, ?_, ?_⟩
  · rw [hL]
    exact Real.rpow_pos_of_pos hNpos _
  · rw [hL, rhoN, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    norm_num

/-- `ρ̃_N = ρ_N / (1 + 2ρ_N^{25/48})³`. -/
private lemma Lemma22_rhotN_eq {N : ℕ} (hN : 1 ≤ N) :
    rhotN N = rhoN N / (1 + 2 * rhoN N ^ (25 / 48 : ℝ)) ^ 3 := by
  obtain ⟨hρ, hL, hρL⟩ := Lemma22_rhoN_facts hN
  have hs : 0 < 1 + 2 * rhoN N ^ (25 / 48 : ℝ) := by positivity
  unfold rhotN LtN
  rw [← hρL, mul_pow]
  field_simp

/-- `κ(ρ̃) = κ(ρ) (1 + 2ρ^{25/48})^{9/2}` with `ρ̃ = ρ / s³`. -/
private lemma Lemma22_kappa {g ρ s : ℝ} (hg : 0 < g) (hρ : 0 < ρ) (hs : 0 < s) :
    (g ^ (5 / 2 : ℝ) * (ρ / s ^ 3) ^ (3 / 2 : ℝ))⁻¹ =
      (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹ * s ^ (9 / 2 : ℝ) := by
  have h1 : (s ^ 3) ^ (3 / 2 : ℝ) = s ^ (9 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  have h2 : 0 < s ^ (9 / 2 : ℝ) := Real.rpow_pos_of_pos hs _
  have h3 : 0 < g ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hg _
  have h4 : 0 < ρ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  rw [Real.div_rpow hρ.le (by positivity), h1]
  field_simp

/-- `ρ - ρ/(1 + 2t)³ ≤ 6ρt`. -/
private lemma Lemma22_diff {ρ t : ℝ} (hρ : 0 < ρ) (ht : 0 ≤ t) :
    ρ - ρ / (1 + 2 * t) ^ 3 ≤ 6 * ρ * t := by
  have hs : 0 < (1 + 2 * t) ^ 3 := by positivity
  have h : ρ * (1 - 6 * t) ≤ ρ / (1 + 2 * t) ^ 3 := by
    rw [le_div_iff₀ hs]
    have e : (1 - 6 * t) * (1 + 2 * t) ^ 3 = 1 - 24 * t ^ 2 - 64 * t ^ 3 - 48 * t ^ 4 := by ring
    have h1 : 0 ≤ ρ * (24 * t ^ 2 + 64 * t ^ 3 + 48 * t ^ 4) := by positivity
    calc ρ * (1 - 6 * t) * (1 + 2 * t) ^ 3 = ρ * ((1 - 6 * t) * (1 + 2 * t) ^ 3) := by ring
      _ = ρ - ρ * (24 * t ^ 2 + 64 * t ^ 3 + 48 * t ^ 4) := by rw [e]; ring
      _ ≤ ρ := by linarith
  linarith

/-- The sum `6 g^{-3/2} ρ^{1/48} + C_q g^{-5/2} ρ^{3/48}` of the density-shift and the kinetic
errors of Lemma 2.2 [lemma1], after the division by `g^{5/2} ρ^{3/2}`. -/
private def Lemma22_E (g ρ : ℝ) : ℝ :=
  6 * (g ^ (3 / 2 : ℝ))⁻¹ * ρ ^ (1 / 48 : ℝ) + cutConst * (g ^ (5 / 2 : ℝ))⁻¹ * ρ ^ (3 / 48 : ℝ)

/-- The factor `(1 + 2ρ^{25/48})^{9/2} = κ(ρ̃)/κ(ρ)`. -/
private def Lemma22_f (ρ : ℝ) : ℝ := (1 + 2 * ρ ^ (25 / 48 : ℝ)) ^ (9 / 2 : ℝ)

/-- The two error terms of Lemma 2.2 [lemma1], `6gρ·ρ^{25/48}` (density shift) and
`C_q/(ℓL)` with `ℓ = L ρ^{25/48}` (kinetic error), multiplied by `(g^{5/2} ρ^{3/2})⁻¹`, are
`Lemma22_E g ρ`, of order `ρ^{1/48}` and `ρ^{3/48}`. -/
private lemma Lemma22_E_eq {g ρ : ℝ} (hg : 0 < g) (hρ : 0 < ρ) :
    (6 * ρ * ρ ^ (25 / 48 : ℝ) * g +
        cutConst / ((ρ ^ (-(25 / 24) : ℝ) * ρ ^ (25 / 48 : ℝ)) * ρ ^ (-(25 / 24) : ℝ))) *
      (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹ = Lemma22_E g ρ := by
  have e1 : ρ * ρ ^ (25 / 48 : ℝ) = ρ ^ (1 / 48 : ℝ) * ρ ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hρ, show (1 / 48 + 3 / 2 : ℝ) = 1 + 25 / 48 by norm_num,
      Real.rpow_add hρ, Real.rpow_one]
  have e2 : (ρ ^ (-(25 / 24) : ℝ) * ρ ^ (25 / 48 : ℝ)) * ρ ^ (-(25 / 24) : ℝ) =
      (ρ ^ (3 / 48 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_neg hρ.le]
    congr 1
    norm_num
  have e3 : g ^ (5 / 2 : ℝ) = g * g ^ (3 / 2 : ℝ) := by
    rw [show (5 / 2 : ℝ) = 1 + 3 / 2 by norm_num, Real.rpow_add hg, Real.rpow_one]
  have h3 : 0 < g ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hg _
  have h4 : 0 < ρ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have h5 : 0 < ρ ^ (3 / 48 : ℝ) := Real.rpow_pos_of_pos hρ _
  rw [e2, mul_assoc 6 ρ, e1, e3, Lemma22_E, div_inv_eq_mul]
  field_simp
  rw [e3]
  ring


/-- Lemma 2.2 [lemma1], one `N`: the periodic bound `ratio ≤ M` at density `ρ_N` gives the
Dirichlet bound `ratio ≤ (M + E) f` at density `ρ̃_N`. -/
private lemma Lemma22_pointwise {V : R3 → ℝ} (hV : PotentialHyp V) {g : ℝ} (hg : 0 < g) {N : ℕ}
    (hN : 1 ≤ N) (ht : rhoN N ^ (25 / 48 : ℝ) < 1 / 2) {M : ℝ}
    (hM : ratio g (rhoN N) (e0P (LN N) V N) ≤ (M : EReal)) :
    ratio g (rhotN N) (e0D (LtN N) V N) ≤
      (((M + Lemma22_E g (rhoN N)) * Lemma22_f (rhoN N) : ℝ) : EReal) := by
  obtain ⟨hρ, hL, hρL⟩ := Lemma22_rhoN_facts hN
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set t := ρ ^ (25 / 48 : ℝ) with htdef
  have ht0 : 0 < t := Real.rpow_pos_of_pos hρ _
  have hs : 0 < 1 + 2 * t := by positivity
  have hℓ : 0 < L * t := mul_pos hL ht0
  have h2 : 2 * (L * t) < L := by nlinarith
  have hLt : LtN N = L + 2 * (L * t) := by
    unfold LtN
    rw [← hLdef, ← hρdef, ← htdef]
    ring
  have hD := e0D_le_e0P hV hℓ h2 N
  rw [← hLt] at hD
  have hL' : 0 < LtN N := by rw [hLt]; linarith
  obtain ⟨d, hd⟩ : ∃ d : ℝ, e0D (LtN N) V N = (d : EReal) :=
    ⟨(e0D (LtN N) V N).toReal, (EReal.coe_toReal (e0D_lt_top hL' V N).ne
      (ne_bot_of_le_ne_bot (by simp) (e0D_nonneg hV.nonneg _ _))).symm⟩
  set κ : ℝ := (g ^ (5 / 2 : ℝ) * ρ ^ (3 / 2 : ℝ))⁻¹ with hκdef
  have hκ : 0 < κ := by
    have h1 : 0 < g ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hg _
    have h2 : 0 < ρ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
    positivity
  have hf : 0 < Lemma22_f ρ := Real.rpow_pos_of_pos hs _
  have hκt : (g ^ (5 / 2 : ℝ) * (rhotN N) ^ (3 / 2 : ℝ))⁻¹ = κ * Lemma22_f ρ := by
    rw [Lemma22_rhotN_eq hN]
    exact Lemma22_kappa hg hρ hs
  have hρt : rhotN N = ρ / (1 + 2 * t) ^ 3 := Lemma22_rhotN_eq hN
  -- `e0P` is a real number
  have hPtop : e0P L V N ≠ ⊤ := by
    intro h
    rw [h] at hM
    unfold ratio at hM
    rw [EReal.top_sub_coe, EReal.top_mul_coe_of_pos hκ] at hM
    exact EReal.coe_ne_top M (top_le_iff.1 hM)
  have hPbot : e0P L V N ≠ ⊥ := by
    intro h
    rw [h, hd] at hD
    simp at hD
  obtain ⟨p, hp⟩ : ∃ p : ℝ, e0P L V N = (p : EReal) :=
    ⟨(e0P L V N).toReal, (EReal.coe_toReal hPtop hPbot).symm⟩
  rw [hp, hd, ← EReal.coe_add, EReal.coe_le_coe_iff] at hD
  rw [hp] at hM
  unfold ratio at hM
  rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hM
  unfold ratio
  rw [hd, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  set c : ℝ := cutConst / (L * t * L) with hcdef
  have hdiff := Lemma22_diff (ρ := ρ) (t := t) hρ ht0.le
  rw [← hρt] at hdiff
  have hbE : (6 * ρ * t * g + c) * κ = Lemma22_E g ρ := by
    have := Lemma22_E_eq hg hρ
    rw [hLdef, hρdef] at *
    simpa [LN, htdef, hcdef, hκdef] using this
  have hκf : 0 < κ * Lemma22_f ρ := mul_pos hκ hf
  calc (d - g * rhotN N) * (g ^ (5 / 2 : ℝ) * (rhotN N) ^ (3 / 2 : ℝ))⁻¹
      = (d - g * rhotN N) * (κ * Lemma22_f ρ) := by rw [hκt]
    _ ≤ (p + c - g * rhotN N) * (κ * Lemma22_f ρ) :=
        mul_le_mul_of_nonneg_right (by linarith) hκf.le
    _ = (p - g * ρ) * κ * Lemma22_f ρ + (g * (ρ - rhotN N) + c) * (κ * Lemma22_f ρ) := by ring
    _ ≤ M * Lemma22_f ρ + (6 * ρ * t * g + c) * κ * Lemma22_f ρ := by
        refine add_le_add (mul_le_mul_of_nonneg_right hM hf.le) ?_
        have : g * (ρ - rhotN N) + c ≤ 6 * ρ * t * g + c := by nlinarith
        calc (g * (ρ - rhotN N) + c) * (κ * Lemma22_f ρ)
            ≤ (6 * ρ * t * g + c) * (κ * Lemma22_f ρ) :=
              mul_le_mul_of_nonneg_right this hκf.le
          _ = _ := by ring
    _ = (M + Lemma22_E g ρ) * Lemma22_f ρ := by rw [← hbE]; ring


/-- `ρ_N → 0`. -/
private lemma Lemma22_tendsto_rhoN : Tendsto (fun N : ℕ => rhoN N) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 8 / 17)).comp tendsto_natCast_atTop_atTop

/-- `ρ_N^{25/48} → 0`. -/
private lemma Lemma22_tendsto_t :
    Tendsto (fun N : ℕ => rhoN N ^ (25 / 48 : ℝ)) atTop (𝓝 0) := by
  have h : ContinuousAt (fun x : ℝ => x ^ (25 / 48 : ℝ)) 0 :=
    Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))
  have := h.tendsto.comp Lemma22_tendsto_rhoN
  rwa [Real.zero_rpow (by norm_num)] at this

/-- `(M + E(g, ρ_N)) f(ρ_N) → M`: the density shift and the kinetic error vanish, and
`f(ρ_N) → 1`. -/
private lemma Lemma22_tendsto_bound (g M : ℝ) :
    Tendsto (fun N : ℕ => (M + Lemma22_E g (rhoN N)) * Lemma22_f (rhoN N)) atTop (𝓝 M) := by
  have hc : ∀ q : ℝ, 0 < q → ContinuousAt (fun x : ℝ => x ^ q) 0 :=
    fun q hq => Real.continuousAt_rpow_const _ _ (Or.inr hq.le)
  have hφ : ContinuousAt (fun x : ℝ => (M + (6 * (g ^ (3 / 2 : ℝ))⁻¹ * x ^ (1 / 48 : ℝ) +
      cutConst * (g ^ (5 / 2 : ℝ))⁻¹ * x ^ (3 / 48 : ℝ))) *
        (1 + 2 * x ^ (25 / 48 : ℝ)) ^ (9 / 2 : ℝ)) 0 := by
    refine ContinuousAt.mul (continuousAt_const.add
      ((continuousAt_const.mul (hc _ (by norm_num))).add
        (continuousAt_const.mul (hc _ (by norm_num))))) ?_
    exact (continuousAt_const.add (continuousAt_const.mul (hc _ (by norm_num)))).rpow_const
      (Or.inr (by norm_num))
  have h := hφ.tendsto.comp Lemma22_tendsto_rhoN
  have z1 : (0 : ℝ) ^ (1 / 48 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  have z2 : (0 : ℝ) ^ (3 / 48 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  have z3 : (0 : ℝ) ^ (25 / 48 : ℝ) = 0 := Real.zero_rpow (by norm_num)
  simp only [z1, z2, z3, mul_zero, add_zero, Real.one_rpow, mul_one] at h
  exact h

/-- Lemma 2.2 [lemma1]. -/
theorem Lemma2_2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma2_2 V w := by
  intro hlim
  have hg := scat_g0_pos hV hw
  set g := g0 V w with hgdef
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
  have hε : 0 < z - cLHY := by
    have := EReal.coe_lt_coe_iff.1 hz
    linarith
  have e1 : ∀ᶠ N : ℕ in atTop, 1 ≤ N := eventually_ge_atTop 1
  have e2 : ∀ᶠ N : ℕ in atTop, rhoN N ^ (25 / 48 : ℝ) < 1 / 2 :=
    Lemma22_tendsto_t.eventually_lt_const (by norm_num)
  have e3 : ∀ᶠ N : ℕ in atTop,
      ratio g (rhoN N) (e0P (LN N) V N) < ((cLHY + (z - cLHY) / 2 : ℝ) : EReal) :=
    eventually_lt_of_limsup_lt
      (lt_of_le_of_lt hlim (EReal.coe_lt_coe_iff.2 (by linarith)))
  have e4 : ∀ᶠ N : ℕ in atTop,
      (cLHY + (z - cLHY) / 2 + Lemma22_E g (rhoN N)) * Lemma22_f (rhoN N) < z :=
    (Lemma22_tendsto_bound g (cLHY + (z - cLHY) / 2)).eventually_lt_const (by linarith)
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [e1, e2, e3, e4] with N h1 h2 h3 h4
  exact (Lemma22_pointwise hV hg h1 h2 h3.le).trans (EReal.coe_le_coe_iff.2 h4.le)

end LHYUpper
