module

public import LHYUpper.TrialState.Legs

@[expose] public section

/-!
# The weights `f(α)` and their ratios: (3.18), (8.11), Lemma 9.1

The last product of (3.18) [deffal] as `FRatio_asym` and the factorization of `f(α)`; the exact
form of the ratios of (8.11) [relationalbe] and of Lemma 9.1 [fourlegslemma1], in which only the
last product and the factors at the legs change; and the two-sided bounds of these ratios with
explicit constants, under the bound (5.10) [lublambdaPL0] on `λ` over `P_L` taken as a hypothesis.
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

section FRatio
variable {V w : R3 → ℝ} {ρ L kc : ℝ} {N : ℕ}

/-- The last product of (3.18) [deffal]: the factors `√(4α*(u)λ_u/|Λ|)` over `u ∈ P_L` with
`α*(u) - α(u) = 1`. -/
def FRatio_asym (V w : R3 → ℝ) (ρ L : ℝ) (α : Occ) : ℂ :=
  ∏ u ∈ (α.support.image Neg.neg).filter (fun u => inPL ρ L u ∧ alphaStar α u = α u + 1),
    csqrt (4 * (alphaStar α u : ℝ) * lam V w ρ L u / L ^ 3)

/-- One factor `csqrt(λ_n)^m` of the product over the support in (3.18) [deffal]; the factor at
`n = 0` is `1`. -/
private def FR_g (V w : R3 → ℝ) (ρ L : ℝ) (n : Idx) (m : ℕ) : ℂ :=
  if n ≠ 0 then csqrt (lam V w ρ L n) ^ m else 1

private lemma FR_g_zero (n : Idx) : FR_g V w ρ L n 0 = 1 := by
  simp [FR_g]

private lemma FR_g_add (n : Idx) (a b : ℕ) :
    FR_g V w ρ L n (a + b) = FR_g V w ρ L n a * FR_g V w ρ L n b := by
  unfold FR_g
  split_ifs
  · exact pow_add _ _ _
  · simp

private lemma FR_g_one {n : Idx} (hn : n ≠ 0) :
    FR_g V w ρ L n 1 = csqrt (lam V w ρ L n) := by
  simp [FR_g, hn]

private lemma FR_g_one_zero : FR_g V w ρ L 0 1 = 1 := by
  simp [FR_g]

/-- The product `∏_{n ≠ 0} csqrt(λ_n)^{α(n)}` of (3.18) [deffal] as a product over the finitely
supported function `α`. -/
private lemma FR_S_eq (α : Occ) :
    ∏ n ∈ α.support.filter (· ≠ 0), csqrt (lam V w ρ L n) ^ (α n) =
      α.prod (FR_g V w ρ L) := by
  unfold Finsupp.prod
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun n _ => ?_
  simp [FR_g]

/-- The exact identity of occupation numbers carries over to the product of (3.18) [deffal]. -/
private lemma FR_S_id {α β : Occ} {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1) :
    α.prod (FR_g V w ρ L) * FR_g V w ρ L s 1 * FR_g V w ρ L r 1 =
      β.prod (FR_g V w ρ L) * FR_g V w ρ L q 1 * FR_g V w ρ L p 1 := by
  have key : (α + Finsupp.single s 1 + Finsupp.single r 1).prod (FR_g V w ρ L) =
      (β + Finsupp.single q 1 + Finsupp.single p 1).prod (FR_g V w ρ L) := by rw [h]
  rwa [Finsupp.prod_add_index' FR_g_zero FR_g_add, Finsupp.prod_add_index' FR_g_zero FR_g_add,
    Finsupp.prod_single_index (FR_g_zero r), Finsupp.prod_single_index (FR_g_zero s),
    Finsupp.prod_add_index' FR_g_zero FR_g_add, Finsupp.prod_add_index' FR_g_zero FR_g_add,
    Finsupp.prod_single_index (FR_g_zero p), Finsupp.prod_single_index (FR_g_zero q)] at key

/-- A nonzero coefficient of `a†_p a†_q a_r a_s` on `|β⟩` means that nothing is truncated:
`α + δ_s + δ_r = β + δ_q + δ_p` for the resulting state `α`. -/
private lemma FR_a4_id {p q r s : Idx} {α β : Occ} (hne : (a4 p q r s β).1 ≠ 0)
    (heq : (a4 p q r s β).2 = α) :
    1 ≤ β s ∧ 1 ≤ β r ∧ 1 ≤ α p ∧ 1 ≤ α q ∧
      α + Finsupp.single s 1 + Finsupp.single r 1 =
        β + Finsupp.single q 1 + Finsupp.single p 1 := by
  have hpos : 1 ≤ β s ∧ 1 ≤ ((β - Finsupp.single s 1 : Occ) r) := by
    simp only [a4] at hne
    rw [mul_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff] at hne
    obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hne
    rw [Ne, Real.sqrt_eq_zero', not_le] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  obtain ⟨h1, h2⟩ := hpos
  subst heq
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply] at h2
  have key : ∀ n : Idx, ((a4 p q r s β).2 n) + (if s = n then 1 else 0) + (if r = n then 1 else 0)
      = β n + (if q = n then 1 else 0) + (if p = n then 1 else 0) := by
    intro n
    simp only [a4, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    by_cases hs : s = n <;> by_cases hr : r = n <;> subst_vars <;> simp_all <;> omega
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · split_ifs at h2 <;> omega
  · simp only [a4, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs <;> omega
  · simp only [a4, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs <;> omega
  · ext n
    have := key n
    simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
    omega

/-- The exact identity, pointwise. -/
private lemma FR_id_apply {α β : Occ} {p q r s : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1) (n : Idx) :
    α n + (if s = n then 1 else 0) + (if r = n then 1 else 0) =
      β n + (if q = n then 1 else 0) + (if p = n then 1 else 0) := by
  have := DFunLike.congr_fun h n
  simpa only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply] using this

/-- The prefactor of (3.18) [deffal] when the occupation of `0` drops from `m + 1` to `m`. -/
private lemma FR_Z_shift (hL : 0 < L) {α β : Occ} {m : ℕ} (hα : α 0 = m + 1) (hβ : β 0 = m) :
    (Real.sqrt ((L ^ 3) ^ (β 0) / (Nat.factorial (β 0))) : ℂ) =
      ((Real.sqrt ((α 0 : ℝ) / L ^ 3) : ℝ) : ℂ) *
        (Real.sqrt ((L ^ 3) ^ (α 0) / (Nat.factorial (α 0))) : ℂ) := by
  rw [hα, hβ, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- `f(α)` of (3.18) [deffal] split into the zero-mode factor, the symmetric product and the
last product. -/
theorem FRatio_f0 (V w : R3 → ℝ) (ρ L : ℝ) (α : Occ) :
    f0 V w ρ L α = (Real.sqrt ((L ^ 3) ^ (α 0) / (Nat.factorial (α 0))) : ℂ) *
      (∏ n ∈ α.support.filter (· ≠ 0), csqrt (lam V w ρ L n) ^ (α n)) *
      FRatio_asym V w ρ L α := rfl

/-- Exact form of (8.11) [relationalbe]: only the last product of (3.18) [deffal] changes. -/
theorem FRatio_shift3 (hL : 0 < L) {β : Occ} {v₁ v₂ v₃ : Idx} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (hne : (a4 0 v₁ v₂ v₃ β).1 ≠ 0) :
    f0 V w ρ L β * csqrt (lam V w ρ L v₁) * FRatio_asym V w ρ L (a4 0 v₁ v₂ v₃ β).2 =
      f0 V w ρ L (a4 0 v₁ v₂ v₃ β).2 * csqrt (lam V w ρ L v₂) * csqrt (lam V w ρ L v₃) *
        (Real.sqrt (((a4 0 v₁ v₂ v₃ β).2 0 : ℝ) / L ^ 3) : ℂ) * FRatio_asym V w ρ L β := by
  obtain ⟨-, -, -, -, hid⟩ := FR_a4_id (p := 0) (q := v₁) (r := v₂) (s := v₃) hne rfl
  generalize (a4 0 v₁ v₂ v₃ β).2 = α' at hid ⊢
  have h0 := FR_id_apply hid 0
  simp only [h₁, h₂, h₃, ite_false, ite_true] at h0
  have hS := FR_S_id (V := V) (w := w) (ρ := ρ) (L := L) hid
  rw [FR_g_one h₃, FR_g_one h₂, FR_g_one h₁, FR_g_one_zero] at hS
  have hZ := FR_Z_shift hL (α := α') (β := β) (m := β 0) (by omega) rfl
  rw [FRatio_f0 V w ρ L β, FRatio_f0 V w ρ L α', FR_S_eq, FR_S_eq, hZ]
  linear_combination
    (-(((Real.sqrt ((α' 0 : ℝ) / L ^ 3) : ℝ) : ℂ) *
      (Real.sqrt ((L ^ 3) ^ (α' 0) / (Nat.factorial (α' 0))) : ℂ) * FRatio_asym V w ρ L β *
      FRatio_asym V w ρ L α')) * hS

/-- Exact form of the ratio of Lemma 9.1 [fourlegslemma1]. -/
theorem FRatio_shift4 {β : Occ} {v₁ v₂ v₃ v₄ : Idx} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (h₄ : v₄ ≠ 0) (hne : (a4 v₁ v₂ v₃ v₄ β).1 ≠ 0) :
    f0 V w ρ L β * csqrt (lam V w ρ L v₁) * csqrt (lam V w ρ L v₂) *
        FRatio_asym V w ρ L (a4 v₁ v₂ v₃ v₄ β).2 =
      f0 V w ρ L (a4 v₁ v₂ v₃ v₄ β).2 * csqrt (lam V w ρ L v₃) * csqrt (lam V w ρ L v₄) *
        FRatio_asym V w ρ L β := by
  obtain ⟨-, -, -, -, hid⟩ := FR_a4_id (p := v₁) (q := v₂) (r := v₃) (s := v₄) hne rfl
  generalize (a4 v₁ v₂ v₃ v₄ β).2 = α' at hid ⊢
  have h0 := FR_id_apply hid 0
  simp only [h₁, h₂, h₃, h₄, ite_false] at h0
  have hS := FR_S_id (V := V) (w := w) (ρ := ρ) (L := L) hid
  rw [FR_g_one h₁, FR_g_one h₂, FR_g_one h₃, FR_g_one h₄] at hS
  have hZ : α' 0 = β 0 := by omega
  rw [FRatio_f0 V w ρ L β, FRatio_f0 V w ρ L α', FR_S_eq, FR_S_eq, hZ]
  linear_combination
    (-((Real.sqrt ((L ^ 3) ^ (β 0) / (Nat.factorial (β 0))) : ℂ) * FRatio_asym V w ρ L β *
      FRatio_asym V w ρ L α')) * hS

/-- One factor of the last product of (3.18) [deffal]: the square root if `u ∈ P_L` and
`α*(u) = α(u) + 1`, and `1` otherwise. -/
private def FR_t (V w : R3 → ℝ) (ρ L : ℝ) (α : Occ) (u : Idx) : ℂ :=
  if inPL ρ L u ∧ alphaStar α u = α u + 1 then
    csqrt (4 * (alphaStar α u : ℝ) * lam V w ρ L u / L ^ 3)
  else 1

/-- The squared modulus of the factor `FR_t`. -/
private def FR_tau (V w : R3 → ℝ) (ρ L : ℝ) (α : Occ) (u : Idx) : ℝ :=
  ‖FR_t V w ρ L α u‖ ^ 2

private lemma FR_neg_ne_self {u : Idx} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

private lemma FR_norm_csqrt_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h, abs_of_nonneg h]
  · have h' : 0 ≤ -x := by linarith [not_le.1 h]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt h', abs_of_neg (not_le.1 h)]

/-- The last product of (3.18) [deffal] over any finite set containing the relevant indices. -/
private lemma FR_asym_eq (α : Occ) (F : Finset Idx) (hF : ∀ u, α (-u) ≠ 0 → u ∈ F) :
    FRatio_asym V w ρ L α = ∏ u ∈ F, FR_t V w ρ L α u := by
  unfold FRatio_asym
  rw [Finset.prod_filter]
  refine Finset.prod_subset ?_ ?_
  · intro u hu
    simp only [Finset.mem_image, Finsupp.mem_support_iff] at hu
    obtain ⟨a, ha, rfl⟩ := hu
    exact hF (-a) (by simpa using ha)
  · intro u _ hu
    have : ¬ (inPL ρ L u ∧ alphaStar α u = α u + 1) := by
      rintro ⟨-, h⟩
      apply hu
      simp only [Finset.mem_image, Finsupp.mem_support_iff]
      refine ⟨-u, ?_, neg_neg u⟩
      have : α (-u) ≠ 0 := by
        unfold alphaStar at h
        omega
      simpa using this
    simp [this]

private lemma FR_tau_one {γ : Occ} {u : Idx} (h : ¬ (inPL ρ L u ∧ alphaStar γ u = γ u + 1)) :
    FR_tau V w ρ L γ u = 1 := by
  simp [FR_tau, FR_t, h]

private lemma FR_tau_congr {γ γ' : Occ} {u : Idx} (h1 : γ u = γ' u) (h2 : γ (-u) = γ' (-u)) :
    FR_tau V w ρ L γ u = FR_tau V w ρ L γ' u := by
  unfold FR_tau FR_t alphaStar
  rw [h1, h2]

private lemma FR_tau_val {γ : Occ} {u : Idx} (hu : inPL ρ L u) (hs : alphaStar γ u = γ u + 1) :
    FR_tau V w ρ L γ u = |4 * (alphaStar γ u : ℝ) * lam V w ρ L u / L ^ 3| := by
  unfold FR_tau FR_t
  simp only [ite_true, hu, hs, and_self, FR_norm_csqrt_sq]

private lemma FR_lam_neg (hρ : 0 < ρ) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ u, inPL ρ L u → c ≤ -(ρ * lam V w ρ L u) ∧ -(ρ * lam V w ρ L u) ≤ 1) {u : Idx}
    (hu : inPL ρ L u) : lam V w ρ L u < 0 := by
  have h := (hlam u hu).1
  by_contra h'
  nlinarith [mul_nonneg hρ.le (not_lt.1 h')]

private lemma FR_tau_pos (hρ : 0 < ρ) (hL : 0 < L) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ u, inPL ρ L u → c ≤ -(ρ * lam V w ρ L u) ∧ -(ρ * lam V w ρ L u) ≤ 1) (γ : Occ)
    (u : Idx) : 0 < FR_tau V w ρ L γ u := by
  by_cases h : inPL ρ L u ∧ alphaStar γ u = γ u + 1
  · rw [FR_tau_val h.1 h.2]
    apply abs_pos.2
    have ha : (0 : ℝ) < alphaStar γ u := by
      have : 0 < alphaStar γ u := by omega
      exact_mod_cast this
    exact div_ne_zero (mul_ne_zero (mul_ne_zero four_ne_zero ha.ne')
      (FR_lam_neg hρ hc hlam h.1).ne) (by positivity)
  · rw [FR_tau_one h]
    exact one_pos

/-- At `u ∈ P_L` with `γ(-u) = γ(u) + 1`, the squared modulus of the factor is `q / N` with
`q ∈ [1/K, K]`. -/
private lemma FR_tau_asym (hρ : 0 < ρ) (hL : 0 < L) (hN : ρ * L ^ 3 = N) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ u, inPL ρ L u → c ≤ -(ρ * lam V w ρ L u) ∧ -(ρ * lam V w ρ L u) ≤ 1) {K : ℝ}
    (hK1 : 4 * (mc ρ + 1) ≤ K) (hK2 : 1 / (4 * c) ≤ K) {γ : Occ} (hγ : InM ρ L kc N γ)
    {u : Idx} (hu : inPL ρ L u) (hs : γ (-u) = γ u + 1) :
    1 ≤ K * ((N : ℝ) * FR_tau V w ρ L γ u) ∧ (N : ℝ) * FR_tau V w ρ L γ u ≤ K := by
  have hst : alphaStar γ u = γ u + 1 := by
    unfold alphaStar
    omega
  have hmc := MStar_PL_mc hρ hγ hu
  obtain ⟨hl1, hl2⟩ := hlam u hu
  have hlam0 := FR_lam_neg hρ hc hlam hu
  have hLpos : 0 < L ^ 3 := by positivity
  have hge : (1 : ℝ) ≤ alphaStar γ u := by
    have : 1 ≤ alphaStar γ u := by omega
    exact_mod_cast this
  have hq : (N : ℝ) * FR_tau V w ρ L γ u =
      4 * (alphaStar γ u : ℝ) * (-(ρ * lam V w ρ L u)) := by
    rw [FR_tau_val hu hst, abs_of_nonpos]
    · rw [← hN]
      field_simp
    · have : 4 * (alphaStar γ u : ℝ) * lam V w ρ L u ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hlam0.le
      exact div_nonpos_of_nonpos_of_nonneg this hLpos.le
  have hmc0 : 0 < mc ρ := by unfold mc; positivity
  have hKpos : 0 < K := by linarith
  have hKc : 1 ≤ K * (4 * c) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * c)).1 hK2
    exact this
  rw [hq]
  constructor
  · calc (1 : ℝ) ≤ K * (4 * c) := hKc
      _ ≤ K * (4 * (alphaStar γ u : ℝ) * (-(ρ * lam V w ρ L u))) := by
        apply mul_le_mul_of_nonneg_left _ hKpos.le
        nlinarith
  · have h1 : 4 * (alphaStar γ u : ℝ) * (-(ρ * lam V w ρ L u)) ≤ 4 * (alphaStar γ u : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hl2 (by positivity)
    have h2 : 4 * (alphaStar γ u : ℝ) * 1 ≤ 4 * (mc ρ + 1) := by nlinarith
    linarith

/-- The pair `{x, -x}` of one leg: with `e = |γ(x) - γ(-x)|` if `x ∈ P_L` and `e = 0` otherwise,
`N^e` times the product of the squared moduli of the factors at `x` and `-x` lies in
`[K^{-e}, K^e]`. -/
private lemma FR_leg (hρ : 0 < ρ) (hL : 0 < L) (hN : ρ * L ^ 3 = N) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ u, inPL ρ L u → c ≤ -(ρ * lam V w ρ L u) ∧ -(ρ * lam V w ρ L u) ≤ 1) {K : ℝ}
    (hK1 : 4 * (mc ρ + 1) ≤ K) (hK2 : 1 / (4 * c) ≤ K) {γ : Occ} (hγ : InM ρ L kc N γ)
    (x : Idx) {e : ℕ} (he : e = if inPL ρ L x then Int.natAbs ((γ x : ℤ) - γ (-x)) else 0) :
    1 ≤ K ^ e * ((N : ℝ) ^ e * (FR_tau V w ρ L γ x * FR_tau V w ρ L γ (-x))) ∧
      (N : ℝ) ^ e * (FR_tau V w ρ L γ x * FR_tau V w ρ L γ (-x)) ≤ K ^ e := by
  by_cases hx : inPL ρ L x
  · simp only [hx, ↓reduceIte] at he
    have s1 := MStar_PL_star hρ hγ hx
    have s2 := MStar_PL_star hρ hγ (Regions_PL_neg.2 hx)
    unfold alphaStar at s1 s2
    simp only [neg_neg] at s2
    have hx' : inPL ρ L (-x) := Regions_PL_neg.2 hx
    rcases (show γ x = γ (-x) ∨ γ (-x) = γ x + 1 ∨ γ x = γ (-x) + 1 by omega) with h | h | h
    · have he0 : e = 0 := by rw [he, h]; simp
      have t1 : FR_tau V w ρ L γ x = 1 :=
        FR_tau_one (fun h' => by have := h'.2; unfold alphaStar at this; omega)
      have t2 : FR_tau V w ρ L γ (-x) = 1 :=
        FR_tau_one (fun h' => by have := h'.2; unfold alphaStar at this; simp only [neg_neg] at this; omega)
      rw [he0, t1, t2]
      simp
    · have he1 : e = 1 := by rw [he, h]; simp
      have t2 : FR_tau V w ρ L γ (-x) = 1 :=
        FR_tau_one (fun h' => by have := h'.2; unfold alphaStar at this; simp only [neg_neg] at this; omega)
      obtain ⟨b1, b2⟩ := FR_tau_asym hρ hL hN hc hlam hK1 hK2 hγ hx h
      rw [he1, t2]
      simpa using ⟨b1, b2⟩
    · have he1 : e = 1 := by rw [he, h]; simp
      have t1 : FR_tau V w ρ L γ x = 1 :=
        FR_tau_one (fun h' => by have := h'.2; unfold alphaStar at this; omega)
      obtain ⟨b1, b2⟩ := FR_tau_asym hρ hL hN hc hlam hK1 hK2 hγ hx' (by rw [neg_neg]; exact h)
      rw [he1, t1]
      simpa using ⟨b1, b2⟩
  · simp only [hx, ↓reduceIte] at he
    have t1 : FR_tau V w ρ L γ x = 1 := FR_tau_one (fun h' => hx h'.1)
    have t2 : FR_tau V w ρ L γ (-x) = 1 :=
      FR_tau_one (fun h' => hx (Regions_PL_neg.1 h'.1))
    rw [he, t1, t2]
    simp

/-- The pairs `{v i, -(v i)}` together: `N^{F(γ)}` times the product of the squared moduli of the
factors lies in `[K^{-F(γ)}, K^{F(γ)}]`. -/
private lemma FR_near (hρ : 0 < ρ) (hL : 0 < L) (hN : ρ * L ^ 3 = N) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ u, inPL ρ L u → c ≤ -(ρ * lam V w ρ L u) ∧ -(ρ * lam V w ρ L u) ≤ 1) {K : ℝ}
    (hK1 : 4 * (mc ρ + 1) ≤ K) (hK2 : 1 / (4 * c) ≤ K) {n : ℕ} (v : Fin n → Idx) {γ : Occ}
    (hγ : InM ρ L kc N γ) :
    1 ≤ K ^ Fal ρ L v γ * ((N : ℝ) ^ Fal ρ L v γ *
        ∏ i, (FR_tau V w ρ L γ (v i) * FR_tau V w ρ L γ (-(v i)))) ∧
      (N : ℝ) ^ Fal ρ L v γ * ∏ i, (FR_tau V w ρ L γ (v i) * FR_tau V w ρ L γ (-(v i))) ≤
        K ^ Fal ρ L v γ := by
  have hF : Fal ρ L v γ =
      ∑ i, (if inPL ρ L (v i) then Int.natAbs ((γ (v i) : ℤ) - γ (-(v i))) else 0) := rfl
  have e1 : K ^ Fal ρ L v γ = ∏ i, K ^ (if inPL ρ L (v i) then
      Int.natAbs ((γ (v i) : ℤ) - γ (-(v i))) else 0) := by
    rw [hF, Finset.prod_pow_eq_pow_sum]
  have e2 : (N : ℝ) ^ Fal ρ L v γ = ∏ i, (N : ℝ) ^ (if inPL ρ L (v i) then
      Int.natAbs ((γ (v i) : ℤ) - γ (-(v i))) else 0) := by
    rw [hF, Finset.prod_pow_eq_pow_sum]
  have hleg := fun i => FR_leg hρ hL hN hc hlam hK1 hK2 hγ (v i) (e := if inPL ρ L (v i) then
      Int.natAbs ((γ (v i) : ℤ) - γ (-(v i))) else 0) rfl
  rw [e1, e2, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  constructor
  · calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => (hleg i).1)
  · refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => (hleg i).2)
    exact mul_nonneg (pow_nonneg (by positivity) _)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The map from `(i, b)` to `v i` (for `b = true`) or `-(v i)` (for `b = false`). -/
private def FR_phi {n : ℕ} (v : Fin n → Idx) (x : Fin n × Bool) : Idx :=
  if x.2 then v x.1 else -(v x.1)

private lemma FR_phi_injOn {n : ℕ} (v : Fin n → Idx) (h0 : ∀ i, v i ≠ 0)
    (hpm : ∀ i j, i ≠ j → Legs_pm (v i) (v j)) : Function.Injective (FR_phi v) := by
  rintro ⟨i, b⟩ ⟨j, b'⟩ h
  simp only [FR_phi] at h
  by_cases hij : i = j
  · subst hij
    cases b <;> cases b' <;> simp at h ⊢
    · exact FR_neg_ne_self (h0 i) h
    · exact FR_neg_ne_self (h0 i) h.symm
  · exfalso
    obtain ⟨p1, p2⟩ := hpm i j hij
    cases b <;> cases b' <;> simp at h
    · exact p1 h
    · exact (hpm j i (Ne.symm hij)).2 h.symm
    · exact p2 h
    · exact p1 h

private lemma FR_prod_D {n : ℕ} (v : Fin n → Idx) (h0 : ∀ i, v i ≠ 0)
    (hpm : ∀ i j, i ≠ j → Legs_pm (v i) (v j)) (f : Idx → ℝ) :
    ∏ u ∈ Finset.univ.image (FR_phi v), f u = ∏ i, (f (v i) * f (-(v i))) := by
  rw [Finset.prod_image (fun x _ y _ h => FR_phi_injOn v h0 hpm h), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp [FR_phi]

/-- The ratio estimate. If `Y ‖A(α)‖² = X ‖A(β)‖²`, and the occupation numbers of `α` and `β` agree
at `±u` for every `u ∈ P_L` which is not `±` a leg, then `N^{F(β)} Y` and `N^{F(α)} X` differ by
at most the factor `K^{F(α)+F(β)}`. -/
private theorem FR_core (hρ : 0 < ρ) (hL : 0 < L) (hN : ρ * L ^ 3 = N) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ u, inPL ρ L u → c ≤ -(ρ * lam V w ρ L u) ∧ -(ρ * lam V w ρ L u) ≤ 1) {K : ℝ}
    (hK1 : 4 * (mc ρ + 1) ≤ K) (hK2 : 1 / (4 * c) ≤ K) {n : ℕ} (v : Fin n → Idx)
    (h0 : ∀ i, v i ≠ 0) (hpm : ∀ i j, i ≠ j → Legs_pm (v i) (v j)) {α β : Occ}
    (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    (hfar : ∀ u, inPL ρ L u → (∀ i, u ≠ v i ∧ u ≠ -(v i)) → α u = β u ∧ α (-u) = β (-u))
    {Y X : ℝ} (hY : 0 ≤ Y) (hX : 0 ≤ X)
    (hYX : Y * ‖FRatio_asym V w ρ L α‖ ^ 2 = X * ‖FRatio_asym V w ρ L β‖ ^ 2) :
    (N : ℝ) ^ Fal ρ L v β * Y ≤
        K ^ (Fal ρ L v α + Fal ρ L v β) * (N : ℝ) ^ Fal ρ L v α * X ∧
      (N : ℝ) ^ Fal ρ L v α * X ≤
        K ^ (Fal ρ L v α + Fal ρ L v β) * (N : ℝ) ^ Fal ρ L v β * Y := by
  set D : Finset Idx := Finset.univ.image (FR_phi v) with hD
  set F : Finset Idx := (α.support ∪ β.support).image Neg.neg ∪ D with hF
  have hFα : ∀ u, α (-u) ≠ 0 → u ∈ F := fun u hu =>
    Finset.mem_union_left _ (Finset.mem_image.2 ⟨-u, Finset.mem_union_left _ (by simpa using hu),
      neg_neg u⟩)
  have hFβ : ∀ u, β (-u) ≠ 0 → u ∈ F := fun u hu =>
    Finset.mem_union_left _ (Finset.mem_image.2 ⟨-u, Finset.mem_union_right _ (by simpa using hu),
      neg_neg u⟩)
  have hR : ∀ γ : Occ, (∀ u, γ (-u) ≠ 0 → u ∈ F) →
      ‖FRatio_asym V w ρ L γ‖ ^ 2 = ∏ u ∈ F, FR_tau V w ρ L γ u := by
    intro γ hγ
    rw [FR_asym_eq γ F hγ, norm_prod, ← Finset.prod_pow]
    rfl
  have hsplit : ∀ γ : Occ, ∏ u ∈ F, FR_tau V w ρ L γ u =
      (∏ u ∈ F \ D, FR_tau V w ρ L γ u) * ∏ u ∈ D, FR_tau V w ρ L γ u := fun γ =>
    (Finset.prod_sdiff (Finset.subset_union_right)).symm
  have hfarEq : ∏ u ∈ F \ D, FR_tau V w ρ L α u = ∏ u ∈ F \ D, FR_tau V w ρ L β u := by
    refine Finset.prod_congr rfl fun u hu => ?_
    have huD : u ∉ D := (Finset.mem_sdiff.1 hu).2
    by_cases hP : inPL ρ L u
    · have hall : ∀ i, u ≠ v i ∧ u ≠ -(v i) := by
        intro i
        refine ⟨fun h => huD ?_, fun h => huD ?_⟩
        · exact Finset.mem_image.2 ⟨(i, true), Finset.mem_univ _, by simp [FR_phi, h]⟩
        · exact Finset.mem_image.2 ⟨(i, false), Finset.mem_univ _, by simp [FR_phi, h]⟩
      obtain ⟨e1, e2⟩ := hfar u hP hall
      exact FR_tau_congr e1 e2
    · rw [FR_tau_one (fun h => hP h.1), FR_tau_one (fun h => hP h.1)]
  have hG : 0 < ∏ u ∈ F \ D, FR_tau V w ρ L α u :=
    Finset.prod_pos fun u _ => FR_tau_pos hρ hL hc hlam α u
  set G := ∏ u ∈ F \ D, FR_tau V w ρ L α u with hGdef
  set Pα := ∏ i, (FR_tau V w ρ L α (v i) * FR_tau V w ρ L α (-(v i))) with hPα
  set Pβ := ∏ i, (FR_tau V w ρ L β (v i) * FR_tau V w ρ L β (-(v i))) with hPβ
  have hRα : ‖FRatio_asym V w ρ L α‖ ^ 2 = G * Pα := by
    rw [hR α hFα, hsplit α, hD, FR_prod_D v h0 hpm]
  have hRβ : ‖FRatio_asym V w ρ L β‖ ^ 2 = G * Pβ := by
    rw [hR β hFβ, hsplit β, hD, FR_prod_D v h0 hpm, ← hfarEq]
  have hYP : Y * Pα = X * Pβ := by
    rw [hRα, hRβ] at hYX
    have : G * (Y * Pα) = G * (X * Pβ) := by linarith
    exact mul_left_cancel₀ hG.ne' this
  obtain ⟨nα1, nα2⟩ := FR_near hρ hL hN hc hlam hK1 hK2 v hα
  obtain ⟨nβ1, nβ2⟩ := FR_near hρ hL hN hc hlam hK1 hK2 v hβ
  have hmc0 : 0 < mc ρ := by unfold mc; positivity
  have hK0 : 0 ≤ K := by linarith
  have hNpos : (0 : ℝ) < N := by rw [← hN]; positivity
  set a := Fal ρ L v α with ha
  set b := Fal ρ L v β with hb
  have hPαpos : 0 < Pα := by
    by_contra h
    have : (N : ℝ) ^ a * Pα ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 h)
    nlinarith [pow_nonneg hK0 a]
  have hPβpos : 0 < Pβ := by
    by_contra h
    have : (N : ℝ) ^ b * Pβ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.1 h)
    nlinarith [pow_nonneg hK0 b]
  constructor
  · refine le_of_mul_le_mul_right ?_ hPαpos
    have e1 : (N : ℝ) ^ b * Y * Pα = X * ((N : ℝ) ^ b * Pβ) := by
      calc (N : ℝ) ^ b * Y * Pα = (N : ℝ) ^ b * (Y * Pα) := by ring
        _ = _ := by rw [hYP]; ring
    have e2 : K ^ (a + b) * (N : ℝ) ^ a * X * Pα =
        X * K ^ b * (K ^ a * ((N : ℝ) ^ a * Pα)) := by
      rw [pow_add]; ring
    rw [e1, e2]
    calc X * ((N : ℝ) ^ b * Pβ) ≤ X * K ^ b := mul_le_mul_of_nonneg_left nβ2 hX
      _ ≤ X * K ^ b * (K ^ a * ((N : ℝ) ^ a * Pα)) :=
        le_mul_of_one_le_right (mul_nonneg hX (pow_nonneg hK0 b)) nα1
  · refine le_of_mul_le_mul_right ?_ hPβpos
    have e1 : (N : ℝ) ^ a * X * Pβ = Y * ((N : ℝ) ^ a * Pα) := by
      calc (N : ℝ) ^ a * X * Pβ = (N : ℝ) ^ a * (X * Pβ) := by ring
        _ = _ := by rw [← hYP]; ring
    have e2 : K ^ (a + b) * (N : ℝ) ^ b * Y * Pβ =
        Y * K ^ a * (K ^ b * ((N : ℝ) ^ b * Pβ)) := by
      rw [pow_add]; ring
    rw [e1, e2]
    calc Y * ((N : ℝ) ^ a * Pα) ≤ Y * K ^ a := mul_le_mul_of_nonneg_left nα2 hY
      _ ≤ Y * K ^ a * (K ^ b * ((N : ℝ) ^ b * Pβ)) :=
        le_mul_of_one_le_right (mul_nonneg hY (pow_nonneg hK0 a)) nβ1

private lemma FR_pm_symm {a b : Idx} (h : Legs_pm a b) : Legs_pm b a :=
  ⟨Ne.symm h.1, fun e => h.2 (by rw [e, neg_neg])⟩

/-- Equality of the occupation numbers at an index which is none of the four legs. -/
private lemma FR_far_of_id {α β : Occ} {p q r s u : Idx}
    (h : α + Finsupp.single s 1 + Finsupp.single r 1 =
      β + Finsupp.single q 1 + Finsupp.single p 1)
    (hp : p ≠ u) (hq : q ≠ u) (hr : r ≠ u) (hs : s ≠ u) : α u = β u := by
  have := FR_id_apply h u
  simp [hp, hq, hr, hs] at this
  exact this

/-- (8.11) [relationalbe] of Lemma 8.2 [FalFbe0], with the bound on `λ` over `P_L` as a
hypothesis and explicit constants. -/
theorem Lemma8_2_ratio (hρ : 0 < ρ) (hL : 0 < L) (hN : ρ * L ^ 3 = N) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ u, inPL ρ L u → c ≤ -(ρ * lam V w ρ L u) ∧ -(ρ * lam V w ρ L u) ≤ 1)
    {α β : Occ} {v₁ v₂ v₃ : Idx} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0)
    (h₃ : v₃ ≠ 0) (h₁₂ : Legs_pm v₁ v₂) (h₁₃ : Legs_pm v₁ v₃) (h₂₃ : Legs_pm v₂ v₃)
    (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    (hne : (a4 0 v₁ v₂ v₃ β).1 ≠ 0) (heq : (a4 0 v₁ v₂ v₃ β).2 = α) :
    let K := max (4 * (mc ρ + 1)) (1 / (4 * c))
    let Y := ‖f0 V w ρ L β * csqrt (lam V w ρ L v₁)‖ ^ 2
    let X := ‖f0 V w ρ L α * csqrt (lam V w ρ L v₂) * csqrt (lam V w ρ L v₃)‖ ^ 2 *
      ((α 0 : ℝ) / L ^ 3)
    (N : ℝ) ^ Fal ρ L ![v₁, v₂, v₃] β * Y ≤ K ^ 3 * (N : ℝ) ^ Fal ρ L ![v₁, v₂, v₃] α * X ∧
    (N : ℝ) ^ Fal ρ L ![v₁, v₂, v₃] α * X ≤ K ^ 3 * (N : ℝ) ^ Fal ρ L ![v₁, v₂, v₃] β * Y := by
  intro K Y X
  have hK1 : 4 * (mc ρ + 1) ≤ K := le_max_left _ _
  have hK2 : 1 / (4 * c) ≤ K := le_max_right _ _
  have hmc0 : 0 < mc ρ := by unfold mc; positivity
  have hKone : 1 ≤ K := by linarith
  obtain ⟨-, -, -, -, hid⟩ := FR_a4_id hne heq
  have hshift := FRatio_shift3 (V := V) (w := w) (ρ := ρ) hL h₁ h₂ h₃ hne
  rw [heq] at hshift
  have hX0 : 0 ≤ (α 0 : ℝ) / L ^ 3 := by positivity
  have hYX : Y * ‖FRatio_asym V w ρ L α‖ ^ 2 = X * ‖FRatio_asym V w ρ L β‖ ^ 2 := by
    have h2 := congrArg (fun z : ℂ => ‖z‖ ^ 2) hshift
    simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt hX0] at h2
    simp only [Y, X, norm_mul, mul_pow]
    exact h2
  have hpm : ∀ i j, i ≠ j →
      Legs_pm ((![v₁, v₂, v₃] : Fin 3 → Idx) i) ((![v₁, v₂, v₃] : Fin 3 → Idx) j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd rfl hij
      | exact h₁₂
      | exact h₁₃
      | exact h₂₃
      | exact FR_pm_symm h₁₂
      | exact FR_pm_symm h₁₃
      | exact FR_pm_symm h₂₃
  have h0 : ∀ i, (![v₁, v₂, v₃] : Fin 3 → Idx) i ≠ 0 := by
    intro i
    fin_cases i <;> assumption
  have hfar : ∀ u, inPL ρ L u →
      (∀ i, u ≠ (![v₁, v₂, v₃] : Fin 3 → Idx) i ∧ u ≠ -((![v₁, v₂, v₃] : Fin 3 → Idx) i)) →
      α u = β u ∧ α (-u) = β (-u) := by
    intro u hu hall
    have hu0 := Regions_PL_ne_zero hρ hu
    obtain ⟨a1, a1'⟩ := hall 0
    obtain ⟨a2, a2'⟩ := hall 1
    obtain ⟨a3, a3'⟩ := hall 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons] at a1 a1' a2 a2' a3 a3'
    refine ⟨FR_far_of_id hid (Ne.symm hu0) (Ne.symm a1) (Ne.symm a2) (Ne.symm a3),
      FR_far_of_id hid (Ne.symm (neg_ne_zero.2 hu0)) (fun h => a1' (by rw [h, neg_neg]))
        (fun h => a2' (by rw [h, neg_neg])) (fun h => a3' (by rw [h, neg_neg]))⟩
  have hY0 : 0 ≤ Y := sq_nonneg _
  have hX0' : 0 ≤ X := mul_nonneg (sq_nonneg _) hX0
  obtain ⟨c1, c2⟩ := FR_core (kc := kc) hρ hL hN hc hlam hK1 hK2 ![v₁, v₂, v₃] h0 hpm hα hβ
    hfar hY0 hX0' hYX
  have hF := Lemma8_2_F (kc := kc) (N := N) hρ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ hα hβ hne heq
  have hcard : Fal ρ L ![v₁, v₂, v₃] α + Fal ρ L ![v₁, v₂, v₃] β ≤ 3 := by
    rw [hF]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hKpow : K ^ (Fal ρ L ![v₁, v₂, v₃] α + Fal ρ L ![v₁, v₂, v₃] β) ≤ K ^ 3 :=
    pow_le_pow_right₀ hKone hcard
  exact ⟨c1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKpow (by positivity)) hX0'),
    c2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKpow (by positivity)) hY0)⟩

/-- Ratio bound of Lemma 9.1 [fourlegslemma1], with the bound on `λ` over `P_L` as a
hypothesis and explicit constants. -/
theorem Lemma9_1_ratio (hρ : 0 < ρ) (hL : 0 < L) (hN : ρ * L ^ 3 = N) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ u, inPL ρ L u → c ≤ -(ρ * lam V w ρ L u) ∧ -(ρ * lam V w ρ L u) ≤ 1)
    {α β : Occ} {v : Fin 4 → Idx} (h0 : ∀ i, v i ≠ 0)
    (hpm : ∀ i j, i ≠ j → Legs_pm (v i) (v j))
    (hα : InM ρ L kc N α) (hβ : InM ρ L kc N β)
    (hne : (a4 (v 0) (v 1) (v 2) (v 3) β).1 ≠ 0) (heq : (a4 (v 0) (v 1) (v 2) (v 3) β).2 = α) :
    let K := max (4 * (mc ρ + 1)) (1 / (4 * c))
    let Y := ‖f0 V w ρ L β * csqrt (lam V w ρ L (v 0)) * csqrt (lam V w ρ L (v 1))‖ ^ 2
    let X := ‖f0 V w ρ L α * csqrt (lam V w ρ L (v 2)) * csqrt (lam V w ρ L (v 3))‖ ^ 2
    (N : ℝ) ^ Fal ρ L v β * Y ≤ K ^ 4 * (N : ℝ) ^ Fal ρ L v α * X ∧
    (N : ℝ) ^ Fal ρ L v α * X ≤ K ^ 4 * (N : ℝ) ^ Fal ρ L v β * Y := by
  intro K Y X
  have hK1 : 4 * (mc ρ + 1) ≤ K := le_max_left _ _
  have hK2 : 1 / (4 * c) ≤ K := le_max_right _ _
  have hmc0 : 0 < mc ρ := by unfold mc; positivity
  have hKone : 1 ≤ K := by linarith
  obtain ⟨-, -, -, -, hid⟩ := FR_a4_id hne heq
  have hshift := FRatio_shift4 (V := V) (w := w) (ρ := ρ) (L := L) (h0 0) (h0 1) (h0 2) (h0 3) hne
  rw [heq] at hshift
  have hYX : Y * ‖FRatio_asym V w ρ L α‖ ^ 2 = X * ‖FRatio_asym V w ρ L β‖ ^ 2 := by
    have h2 := congrArg (fun z : ℂ => ‖z‖ ^ 2) hshift
    simp only [norm_mul, mul_pow] at h2
    simp only [Y, X, norm_mul, mul_pow]
    exact h2
  have hfar : ∀ u, inPL ρ L u → (∀ i, u ≠ v i ∧ u ≠ -(v i)) →
      α u = β u ∧ α (-u) = β (-u) := by
    intro u hu hall
    obtain ⟨a0, a0'⟩ := hall 0
    obtain ⟨a1, a1'⟩ := hall 1
    obtain ⟨a2, a2'⟩ := hall 2
    obtain ⟨a3, a3'⟩ := hall 3
    exact ⟨FR_far_of_id hid (Ne.symm a0) (Ne.symm a1) (Ne.symm a2) (Ne.symm a3),
      FR_far_of_id hid (fun h => a0' (by rw [h, neg_neg])) (fun h => a1' (by rw [h, neg_neg]))
        (fun h => a2' (by rw [h, neg_neg])) (fun h => a3' (by rw [h, neg_neg]))⟩
  have hY0 : 0 ≤ Y := sq_nonneg _
  have hX0' : 0 ≤ X := sq_nonneg _
  obtain ⟨c1, c2⟩ := FR_core (kc := kc) hρ hL hN hc hlam hK1 hK2 v h0 hpm hα hβ hfar hY0 hX0'
    hYX
  have hF := Lemma9_1_F (kc := kc) (N := N) hρ h0 hpm hα hβ hne heq
  have hcard : Fal ρ L v α + Fal ρ L v β ≤ 4 := by
    rw [hF]
    exact (Finset.card_filter_le _ _).trans (by simp)
  have hKpow : K ^ (Fal ρ L v α + Fal ρ L v β) ≤ K ^ 4 := pow_le_pow_right₀ hKone hcard
  exact ⟨c1.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKpow (by positivity)) hX0'),
    c2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKpow (by positivity)) hY0)⟩

end FRatio

end LHYUpper
