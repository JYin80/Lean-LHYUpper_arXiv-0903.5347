import LHYUpper.Scattering.Born
import LHYUpper.Scattering.NewtonDeriv
import LHYUpper.Scattering.NewtonFourier

open MeasureTheory Filter Topology Real
open scoped BigOperators RealInnerProductSpace FourierTransform

noncomputable section
open Classical

namespace LHYUpper

/-! # Regularity of the zero-energy scattering solution

The bounded continuous solution `w` of the Born equation `w = G ∗ (V(1 - w))` is smooth with
bounded derivatives of every order, `g = V(1 - w)` ((3.12) [gdef]) is a Schwartz function, and
`1 - w` is the zero-energy scattering solution of §2 (display after (2.1) [ham]):
`-Δ(1 - w) + V(1 - w) = 0`, `0 ≤ w < 1`, `w → 0` at infinity. The regularity is obtained by
induction on the order of differentiability: if all derivatives of `h` up to order `n` are
`O((1 + |y|)^{-5})`, then `G ∗ h` is `C^{n+1}` with bounded derivatives up to order `n + 1`,
because `D(G ∗ h) v = G ∗ (Dh · v)`. -/

/-! ### Derivative classes -/

/-- `h` is `C^n` and its derivatives of order `≤ n` are bounded by `C (1 + |y|)^{-5}`. -/
private def DecayN (n : ℕ) (h : R3 → ℝ) : Prop :=
  ContDiff ℝ n h ∧ ∃ C, ∀ j ≤ n, ∀ y, ‖iteratedFDeriv ℝ j h y‖ ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ))

/-- `f` is `C^n` and its derivatives of order `≤ n` are bounded. -/
private def BddN (n : ℕ) (f : R3 → ℝ) : Prop :=
  ContDiff ℝ n f ∧ ∃ C, ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C

private lemma decayN_abs {n : ℕ} {h : R3 → ℝ} {C : ℝ}
    (hC : ∀ j ≤ n, ∀ y, ‖iteratedFDeriv ℝ j h y‖ ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ))) (y : R3) :
    |h y| ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
  have := hC 0 (Nat.zero_le _) y
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

private lemma div_le_abs_of_one_le (c : ℝ) {t : ℝ} (ht : 1 ≤ t) : c / t ≤ |c| :=
  (div_le_div_of_nonneg_right (le_abs_self c) (by linarith)).trans
    (div_le_self (abs_nonneg c) ht)

/-! ### Derivatives of the Newton potential -/

/-- Base case: for continuous `h = O((1 + |y|)^{-5})`, `G ∗ h` is `C¹` with `G ∗ h` and
`D(G ∗ h)` bounded. -/
private lemma newton_bddN_zero {h : R3 → ℝ} (hh : DecayN 0 h) : BddN 1 (newton h) := by
  obtain ⟨hc, C, hC⟩ := hh
  have hcont : Continuous h := contDiff_zero.1 hc
  have hb := decayN_abs hC
  obtain ⟨C0, hC0⟩ := newton_decay (by norm_num : (4 : ℝ) < 5) hcont hb
  obtain ⟨C1, hC1⟩ := newton_fderiv_decay (by norm_num : (3 : ℝ) < 5) hcont hb
  refine ⟨newton_contDiff_one (by norm_num : (3 : ℝ) < 5) hcont hb, max |C0| |C1|,
    fun j hj x => ?_⟩
  interval_cases j
  · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact ((hC0 x).trans (div_le_abs_of_one_le C0 (by linarith [norm_nonneg x]))).trans
      (le_max_left _ _)
  · rw [norm_iteratedFDeriv_one]
    exact ((hC1 x).trans (div_le_abs_of_one_le C1
      (one_le_pow₀ (by linarith [norm_nonneg x])))).trans (le_max_right _ _)

private lemma decayN_mono {n m : ℕ} (hmn : m ≤ n) {h : R3 → ℝ} (hh : DecayN n h) :
    DecayN m h := by
  obtain ⟨hc, C, hC⟩ := hh
  exact ⟨hc.of_le (by exact_mod_cast hmn), C, fun j hj y => hC j (hj.trans hmn) y⟩

/-- Directional derivatives stay in the decay class, with one order less. -/
private lemma decayN_fderiv_apply {n : ℕ} {h : R3 → ℝ} (hh : DecayN (n + 1) h) (v : R3) :
    DecayN n (fun y => fderiv ℝ h y v) := by
  obtain ⟨hc, C, hC⟩ := hh
  have hfd : ContDiff ℝ n (fderiv ℝ h) := by
    have hc' : ContDiff ℝ ((n : WithTop ℕ∞) + 1) h := by exact_mod_cast hc
    exact (contDiff_succ_iff_fderiv.1 hc').2.2
  set L : (R3 →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v
  have he : (fun y => fderiv ℝ h y v) = L ∘ fderiv ℝ h := rfl
  refine ⟨hfd.clm_apply contDiff_const, ‖L‖ * C, fun j hj y => ?_⟩
  rw [he]
  calc ‖iteratedFDeriv ℝ j (L ∘ fderiv ℝ h) y‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ h) y‖ :=
        L.norm_iteratedFDeriv_comp_left hfd.contDiffAt (by exact_mod_cast hj)
    _ = ‖L‖ * ‖iteratedFDeriv ℝ (j + 1) h y‖ := by rw [norm_iteratedFDeriv_fderiv]
    _ ≤ ‖L‖ * (C * (1 + ‖y‖) ^ (-(5 : ℝ))) :=
        mul_le_mul_of_nonneg_left (hC (j + 1) (by omega) y) (by positivity)
    _ = ‖L‖ * C * (1 + ‖y‖) ^ (-(5 : ℝ)) := by ring

/-- A linear functional on ℝ³ is the sum of its values on the coordinate vectors times the
coordinate functionals. -/
private lemma clm_eq_sum (φ : R3 →L[ℝ] ℝ) :
    φ = ∑ i : Fin 3, φ (EuclideanSpace.single i 1) • EuclideanSpace.proj i := by
  ext v
  have hv : v = ∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, map_smul, mul_comm]

/-- If all derivatives of `h` up to order `n` are `O((1 + |y|)^{-5})`, then `G ∗ h` is
`C^{n+1}` with bounded derivatives up to order `n + 1`. -/
private lemma newton_bddN : ∀ n : ℕ, ∀ h : R3 → ℝ, DecayN n h → BddN (n + 1) (newton h)
  | 0 => fun _ hh => newton_bddN_zero hh
  | n + 1 => fun h hh => by
    obtain ⟨hc0, C00, hC00⟩ := newton_bddN_zero (decayN_mono (Nat.zero_le _) hh)
    obtain ⟨hc, C, hC⟩ := hh
    have hcont : Continuous h := hc.continuous
    have hb := decayN_abs hC
    have hc1 : ContDiff ℝ 1 h := hc.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    have hd : ∀ y, ‖fderiv ℝ h y‖ ≤ C * (1 + ‖y‖) ^ (-(5 : ℝ)) := fun y => by
      have := hC 1 (by omega) y
      rwa [norm_iteratedFDeriv_one] at this
    set e : Fin 3 → R3 := fun i => EuclideanSpace.single i 1
    set hi : Fin 3 → R3 → ℝ := fun i y => fderiv ℝ h y (e i)
    have hIH : ∀ i, BddN (n + 1) (newton (hi i)) := fun i =>
      newton_bddN n (hi i) (decayN_fderiv_apply ⟨hc, C, hC⟩ (e i))
    choose hci Ci hCi using hIH
    set L : Fin 3 → ℝ →L[ℝ] (R3 →L[ℝ] ℝ) := fun i =>
      ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.proj i)
    have hD : fderiv ℝ (newton h) = fun x => ∑ i : Fin 3, (L i ∘ newton (hi i)) x := by
      funext x
      rw [clm_eq_sum (fderiv ℝ (newton h) x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Function.comp_apply, L, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, hi, e]
      rw [newton_fderiv_apply (by norm_num : (3 : ℝ) < 5) hc1 hb hd x]
    have hLi : ∀ i, ContDiff ℝ (n + 1 : ℕ) (L i ∘ newton (hi i)) := fun i =>
      (L i).contDiff.comp (hci i)
    have hDc : ContDiff ℝ (n + 1 : ℕ) (fderiv ℝ (newton h)) := by
      rw [hD]
      exact ContDiff.sum fun i _ => hLi i
    refine ⟨?_, max C00 (∑ i : Fin 3, ‖L i‖ * Ci i), fun j hj x => ?_⟩
    · have hdiff : Differentiable ℝ (newton h) :=
        (newton_contDiff_one (by norm_num : (3 : ℝ) < 5) hcont hb).differentiable (by norm_num)
      have : ContDiff ℝ (((n + 1 : ℕ) : WithTop ℕ∞) + 1) (newton h) :=
        contDiff_succ_iff_fderiv.2 ⟨hdiff, fun h => by simp at h, hDc⟩
      exact_mod_cast this
    · rcases j with _ | j
      · exact (hC00 0 (Nat.zero_le _) x).trans (le_max_left _ _)
      · refine le_trans ?_ (le_max_right _ _)
        rw [← norm_iteratedFDeriv_fderiv, hD,
          iteratedFDeriv_sum fun i _ => (hLi i).of_le (by exact_mod_cast (by omega : j ≤ n + 1)),
          Finset.sum_apply]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        exact ((L i).norm_iteratedFDeriv_comp_left (hci i).contDiffAt
          (by exact_mod_cast (by omega : j ≤ n + 1))).trans
          (mul_le_mul_of_nonneg_left (hCi i j (by omega) x) (by positivity))

/-! ### `g = V(1 - w)` -/

private lemma bddN_one_sub {n : ℕ} {w : R3 → ℝ} (hw : BddN n w) : BddN n (fun x => 1 - w x) := by
  obtain ⟨hc, C, hC⟩ := hw
  refine ⟨contDiff_const.sub hc, 1 + C, fun j hj x => ?_⟩
  have e : (fun x => 1 - w x) = (fun _ : R3 => (1 : ℝ)) - w := rfl
  rw [e, iteratedFDeriv_sub (contDiff_const.of_le le_top) (hc.of_le (by exact_mod_cast hj)),
    Pi.sub_apply]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (hC j hj x))
  rcases j with _ | j
  · simp
  · simp [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]

/-- For a Schwartz function `S` and `u ∈ C^n` with bounded derivatives up to order `n`, the
derivatives of `S u` up to order `n` are `O((1 + |y|)^{-5})` (Leibniz rule). -/
private lemma decayN_mul {n : ℕ} (S : SchwartzMap R3 ℝ) {u : R3 → ℝ} (hu : BddN n u) :
    DecayN n (fun y => S y * u y) := by
  obtain ⟨hc, B, hB⟩ := hu
  set A := 2 ^ 5 * (Finset.Iic ((5 : ℕ), n)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S with hA
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  have hS : ∀ i ≤ n, ∀ y : R3, ‖iteratedFDeriv ℝ i S y‖ ≤ A * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
    intro i hi y
    have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((5 : ℕ), n))
      (k := 5) (n := i) le_rfl hi S y
    have hpos : 0 < (1 + ‖y‖) ^ (5 : ℕ) := by positivity
    rw [Real.rpow_neg (by positivity), show ((5 : ℝ)) = ((5 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact h1
  refine ⟨(S.smooth ⊤).of_le (by exact_mod_cast le_top) |>.mul hc,
    2 ^ n * (A * B), fun j hj y => ?_⟩
  have hw : 0 ≤ (1 + ‖y‖) ^ (-(5 : ℝ)) := by positivity
  calc ‖iteratedFDeriv ℝ j (fun y => S y * u y) y‖
      ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i S y‖ * ‖iteratedFDeriv ℝ (j - i) u y‖ :=
        norm_iteratedFDeriv_mul_le ((S.smooth ⊤).of_le (by exact_mod_cast le_top)) hc y
          (by exact_mod_cast hj)
    _ ≤ ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (A * (1 + ‖y‖) ^ (-(5 : ℝ))) * B := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hS i (hi'.trans hj) y) (by positivity))
          (hB (j - i) (by omega) y) (norm_nonneg _) (by positivity)
    _ = 2 ^ j * (A * B) * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [this]
        ring
    _ ≤ 2 ^ n * (A * B) * (1 + ‖y‖) ^ (-(5 : ℝ)) := by
        gcongr
        · norm_num

section
variable {V : R3 → ℝ}

/-- The solution of the Born equation is `C^n` with bounded derivatives up to order `n`, for
every `n`. -/
private lemma bornSol_bddN (hV : PotentialHyp V) : ∀ n : ℕ, BddN n (bornSol V)
  | 0 => by
    obtain ⟨hc, ⟨M, hM⟩, -⟩ := bornSol_isBornSolution hV
    refine ⟨contDiff_zero.2 hc, M, fun j hj x => ?_⟩
    obtain rfl : j = 0 := by omega
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
    exact hM x
  | n + 1 => by
    obtain ⟨S, hS⟩ := hV.schwartz
    have hg := decayN_mul S (bddN_one_sub (bornSol_bddN hV n))
    have heq : newton (fun y => S y * (1 - bornSol V y)) = bornSol V := by
      funext x
      rw [hS]
      exact ((bornSol_isBornSolution hV).2.2 x).symm
    have := newton_bddN n _ hg
    rwa [heq] at this

/-- The solution of the Born equation is smooth. -/
theorem scat_bornSol_contDiff (hV : PotentialHyp V) : ContDiff ℝ (⊤ : ℕ∞) (bornSol V) := by
  exact contDiff_infty.2 fun n => (bornSol_bddN hV n).1

/-- `g = V(1 - w)` is a Schwartz function for the solution `w` of the Born equation. -/
theorem scat_bornSol_g_schwartz (hV : PotentialHyp V) :
    ∃ S : SchwartzMap R3 ℝ, (S : R3 → ℝ) = gfun V (bornSol V) := by
  obtain ⟨S, hS⟩ := hV.schwartz
  have ht : Function.HasTemperateGrowth (fun x => 1 - bornSol V x) := by
    refine ⟨contDiff_const.sub (scat_bornSol_contDiff hV), fun n => ?_⟩
    obtain ⟨-, C, hC⟩ := bddN_one_sub (bornSol_bddN hV n)
    exact ⟨0, C, fun x => by simpa using hC n le_rfl x⟩
  refine ⟨SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℝ ℝ) ht S, ?_⟩
  rw [SchwartzMap.bilinLeftCLM_apply]
  funext x
  simp [gfun, ← hS]

/-- The solution of the Born equation is the zero-energy scattering solution of §2:
`-Δ(1 - w) + V(1 - w) = 0`, `0 ≤ w < 1`, `w → 0`. -/
theorem scat_bornSol_isScatteringSolution (hV : PotentialHyp V) :
    IsScatteringSolution V (bornSol V) := by
  have hsm : ContDiff ℝ 2 (bornSol V) :=
    (scat_bornSol_contDiff hV).of_le (WithTop.coe_le_coe.2 le_top)
  refine ⟨hsm, fun x => ?_, bornSol_nonneg hV, fun x => ?_, bornSol_tendsto hV⟩
  · obtain ⟨S, hS⟩ := scat_bornSol_g_schwartz hV
    have heq : newton (S : R3 → ℝ) = bornSol V := by
      funext y
      rw [hS]
      exact ((bornSol_isBornSolution hV).2.2 y).symm
    have hlap : Laplacian.laplacian (bornSol V) x = -gfun V (bornSol V) x := by
      rw [← heq, newton_laplacian_schwartz S x, heq, hS]
    have hsub : Laplacian.laplacian (fun y => 1 - bornSol V y) x =
        -Laplacian.laplacian (bornSol V) x := by
      have := (contDiffAt_const (c := (1 : ℝ))).laplacian_sub (hsm.contDiffAt (x := x))
      have e : (fun y => 1 - bornSol V y) = (fun _ : R3 => (1 : ℝ)) - bornSol V := rfl
      rw [e, this]
      simp
    rw [hsub, hlap]
    simp [gfun]
  · obtain ⟨c, hc1, hc⟩ := bornSol_lt_one hV
    exact (hc x).trans_lt hc1

end

end LHYUpper
