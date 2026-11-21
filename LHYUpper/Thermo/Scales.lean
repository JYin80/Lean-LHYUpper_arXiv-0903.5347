module

public import LHYUpper.Scattering.Solution

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- `L̃_N = N^{25/51} + 2 N^{25/102}`. -/
private lemma Scales_LtN_eq (N : ℕ) :
    LtN N = (N : ℝ) ^ (25/51 : ℝ) + 2 * (N : ℝ) ^ (25/102 : ℝ) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [LtN, LN, rhoN]
  · have hx : (0 : ℝ) < N := by exact_mod_cast hN
    unfold LtN LN rhoN
    have h1 : ((N : ℝ) ^ (-(8/17 : ℝ))) ^ (-(25/24 : ℝ)) = (N : ℝ) ^ (25/51 : ℝ) := by
      rw [← Real.rpow_mul hx.le]; norm_num
    have h2 : ((N : ℝ) ^ (-(8/17 : ℝ))) ^ (25/48 : ℝ) = (N : ℝ) ^ (-(25/102 : ℝ)) := by
      rw [← Real.rpow_mul hx.le]; norm_num
    have h3 : (N : ℝ) ^ (25/51 : ℝ) * (N : ℝ) ^ (-(25/102 : ℝ)) = (N : ℝ) ^ (25/102 : ℝ) := by
      rw [← Real.rpow_add hx]; norm_num
    rw [h1, h2, mul_add, mul_one, ← mul_assoc, mul_comm _ (2:ℝ), mul_assoc, h3]


private lemma Scales_LtN_ge (N : ℕ) : (N : ℝ) ^ (25/51 : ℝ) ≤ LtN N := by
  rw [Scales_LtN_eq]
  have : 0 ≤ (N : ℝ) ^ (25/102 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  linarith

private lemma Scales_LtN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < LtN N := by
  rw [Scales_LtN_eq]
  have hx : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

/-- Concavity bound `(x + h)^p ≤ x^p + p h` for `x ≥ 1`, `0 ≤ p ≤ 1`. -/
private lemma Scales_rpow_add_le {x h p : ℝ} (hx : 1 ≤ x) (hh : 0 ≤ h) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) : (x + h) ^ p ≤ x ^ p + p * h := by
  have hx0 : 0 < x := by linarith
  have h1 : (x + h) = x * (1 + h / x) := by field_simp
  have hhx : 0 ≤ h / x := by positivity
  have h2 : (1 + h / x) ^ p ≤ 1 + p * (h / x) :=
    rpow_one_add_le_one_add_mul_self (by linarith) hp0 hp1
  have h3 : x ^ p ≤ x := by
    calc x ^ p ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hp1
      _ = x := Real.rpow_one x
  rw [h1, Real.mul_rpow hx0.le (by positivity)]
  calc x ^ p * (1 + h / x) ^ p ≤ x ^ p * (1 + p * (h / x)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = x ^ p + p * h * (x ^ p / x) := by field_simp
    _ ≤ x ^ p + p * h * 1 := by
        gcongr
        rw [div_le_one hx0]; exact h3
    _ = x ^ p + p * h := by ring

/-- `L̃_{N+h} ≤ L̃_N + h` for `N ≥ 1`. -/
private lemma Scales_LtN_add {N : ℕ} (hN : 1 ≤ N) (h : ℕ) : LtN (N + h) ≤ LtN N + h := by
  rw [Scales_LtN_eq, Scales_LtN_eq]
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hh : (0 : ℝ) ≤ h := Nat.cast_nonneg h
  have h1 := Scales_rpow_add_le hx hh (by norm_num : (0:ℝ) ≤ 25/51) (by norm_num)
  have h2 := Scales_rpow_add_le hx hh (by norm_num : (0:ℝ) ≤ 25/102) (by norm_num)
  push_cast
  nlinarith

/-- A lower bound for `M^{25/51}` from `M ≥ ρ^{-17/8}/4`. -/
private lemma Scales_H {ρ M : ℝ} (hρ : 0 < ρ) (hM : ρ ^ (-(17/8 : ℝ)) / 4 ≤ M) :
    ρ ^ (-(25/24 : ℝ)) / 2 ≤ M ^ (25/51 : ℝ) := by
  have ha : 0 < ρ ^ (-(25/24 : ℝ)) := Real.rpow_pos_of_pos hρ _
  have h2 : (4 : ℝ) ≤ (2 : ℝ) ^ (51/25 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by norm_num : (2:ℝ) ≤ 51/25)
    norm_num at this
    exact this
  have h1 : (ρ ^ (-(25/24 : ℝ)) / 2) ^ (51/25 : ℝ) ≤ ρ ^ (-(17/8 : ℝ)) / 4 := by
    rw [Real.div_rpow ha.le (by norm_num), ← Real.rpow_mul hρ.le]
    have e : (-(25/24 : ℝ)) * (51/25) = -(17/8) := by norm_num
    rw [e]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hρ.le _) (by norm_num) h2
  calc ρ ^ (-(25/24 : ℝ)) / 2
      = ((ρ ^ (-(25/24 : ℝ)) / 2) ^ (51/25 : ℝ)) ^ (25/51 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]; norm_num
    _ ≤ M ^ (25/51 : ℝ) := Real.rpow_le_rpow (by positivity) (h1.trans hM) (by norm_num)

/-- `ρ y^{25/17} = y (y ρ^{17/8})^{8/17}`. -/
private lemma Scales_key {ρ y : ℝ} (hρ : 0 < ρ) (hy : 0 < y) :
    ρ * y ^ (25/17 : ℝ) = y * (y * ρ ^ (17/8 : ℝ)) ^ (8/17 : ℝ) := by
  rw [Real.mul_rpow hy.le (Real.rpow_nonneg hρ.le _), ← Real.rpow_mul hρ.le]
  have e : (17/8 : ℝ) * (8/17) = 1 := by norm_num
  have e2 : y ^ (25/17 : ℝ) = y * y ^ (8/17 : ℝ) := by
    rw [← Real.rpow_one_add' hy.le (by norm_num)]; norm_num
  rw [e, Real.rpow_one, e2]; ring


/-- Members of the set defining `N₀` are bounded. -/
private lemma Scales_upper {ρ : ℝ} (hρ : 0 < ρ) {N : ℕ}
    (h : ρ ≤ ((N : ℝ) + 1/2) / (LtN (N + 1) + 2 * ρ ^ (-(1/2 : ℝ))) ^ 3) :
    (N : ℝ) + 1 ≤ ρ ^ (-(17/8 : ℝ)) := by
  by_contra hcon
  rw [not_le] at hcon
  have hy : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hLt : ((N : ℝ) + 1) ^ (25/51 : ℝ) ≤ LtN (N + 1) := by
    have := Scales_LtN_ge (N + 1)
    push_cast at this
    exact this
  have hd : 0 ≤ 2 * ρ ^ (-(1/2 : ℝ)) := by positivity
  have hp : 0 < ((N : ℝ) + 1) ^ (25/51 : ℝ) := Real.rpow_pos_of_pos hy _
  have hA : ((N : ℝ) + 1) ^ (25/51 : ℝ) ≤ LtN (N + 1) + 2 * ρ ^ (-(1/2 : ℝ)) := by linarith
  have hA3 : (((N : ℝ) + 1) ^ (25/51 : ℝ)) ^ 3 ≤ (LtN (N + 1) + 2 * ρ ^ (-(1/2 : ℝ))) ^ 3 :=
    pow_le_pow_left₀ hp.le hA 3
  have hA0 : 0 < (LtN (N + 1) + 2 * ρ ^ (-(1/2 : ℝ))) ^ 3 := pow_pos (lt_of_lt_of_le hp hA) 3
  rw [le_div_iff₀ hA0] at h
  have e1 : (((N : ℝ) + 1) ^ (25/51 : ℝ)) ^ 3 = ((N : ℝ) + 1) ^ (25/17 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
  rw [e1] at hA3
  have h1 : ρ * ((N : ℝ) + 1) ^ (25/17 : ℝ) ≤ (N : ℝ) + 1/2 := by
    calc ρ * ((N : ℝ) + 1) ^ (25/17 : ℝ)
        ≤ ρ * (LtN (N + 1) + 2 * ρ ^ (-(1/2 : ℝ))) ^ 3 := by gcongr
      _ ≤ (N : ℝ) + 1/2 := by linarith
  rw [Scales_key hρ hy] at h1
  have hρp : 0 < ρ ^ (17/8 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hone : 1 < ((N : ℝ) + 1) * ρ ^ (17/8 : ℝ) := by
    have e : ρ ^ (-(17/8 : ℝ)) * ρ ^ (17/8 : ℝ) = 1 := by
      rw [← Real.rpow_add hρ]; norm_num
    calc (1 : ℝ) = ρ ^ (-(17/8 : ℝ)) * ρ ^ (17/8 : ℝ) := e.symm
      _ < ((N : ℝ) + 1) * ρ ^ (17/8 : ℝ) := mul_lt_mul_of_pos_right hcon hρp
  have h2 : 1 < (((N : ℝ) + 1) * ρ ^ (17/8 : ℝ)) ^ (8/17 : ℝ) :=
    Real.one_lt_rpow hone (by norm_num)
  nlinarith

/-- `(y ρ^{17/8})^{8/17} ≤ 4/5` when `y ρ^{17/8} ≤ 51/100`. -/
private lemma Scales_W {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 51/100) : u ^ (8/17 : ℝ) ≤ 4/5 := by
  have h1 : u ^ (8/17 : ℝ) ≤ u ^ (1/3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hu0 (by linarith) (by norm_num)
  have h2 : u ^ (1/3 : ℝ) ≤ 4/5 := by
    rw [one_div, Real.rpow_inv_le_iff_of_pos hu0.le (by norm_num) (by norm_num)]
    norm_num
    linarith
  exact h1.trans h2

/-- The witness `⌊ρ^{-17/8}/2⌋` belongs to the set defining `N₀`. -/
private lemma Scales_exists {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hb : 160 ≤ ρ ^ (-(25/48 : ℝ))) :
    ρ ≤ (((⌊ρ ^ (-(17/8 : ℝ)) / 2⌋₊ : ℕ) : ℝ) + 1/2) /
      (LtN (⌊ρ ^ (-(17/8 : ℝ)) / 2⌋₊ + 1) + 2 * ρ ^ (-(1/2 : ℝ))) ^ 3 := by
  set X := ρ ^ (-(17/8 : ℝ)) with hX
  set b := ρ ^ (-(25/48 : ℝ)) with hbdef
  set d := ρ ^ (-(1/2 : ℝ)) with hd
  set N' := ⌊X / 2⌋₊ with hN'
  have hb0 : 0 < b := by linarith
  have hXb : X = b ^ (102/25 : ℝ) := by
    rw [hbdef, ← Real.rpow_mul hρ.le, hX]; norm_num
  have hX160 : 160 ≤ X := by
    rw [hXb]
    calc (160 : ℝ) ≤ b := hb
      _ = b ^ (1 : ℝ) := (Real.rpow_one b).symm
      _ ≤ b ^ (102/25 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hab : ρ ^ (-(25/24 : ℝ)) = b * b := by
    rw [hbdef, ← Real.rpow_add hρ]; norm_num
  have hdb : d ≤ b := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hXq : X ^ (25/102 : ℝ) = b := by
    rw [hX, ← Real.rpow_mul hρ.le, hbdef]; norm_num
  have hXρ : X * ρ ^ (17/8 : ℝ) = 1 := by
    rw [hX, ← Real.rpow_add hρ]; norm_num
  set y : ℝ := (N' : ℝ) + 1 with hy
  have hy1 : X / 2 < y := Nat.lt_floor_add_one (X / 2)
  have hy2 : y ≤ X / 2 + 1 := by
    have := Nat.floor_le (by positivity : (0 : ℝ) ≤ X / 2); linarith
  have hypos : 0 < y := by positivity
  have hyX : y ≤ X := by linarith
  have hp : b * b / 2 ≤ y ^ (25/51 : ℝ) := by
    rw [← hab]; apply Scales_H hρ; linarith
  have hq : y ^ (25/102 : ℝ) ≤ b := by
    rw [← hXq]; exact Real.rpow_le_rpow hypos.le hyX (by norm_num)
  have hLt : LtN (N' + 1) = y ^ (25/51 : ℝ) + 2 * y ^ (25/102 : ℝ) := by
    rw [Scales_LtN_eq]; push_cast; rfl
  have hpb : 80 * b ≤ y ^ (25/51 : ℝ) := by nlinarith
  have hp0 : 0 < y ^ (25/51 : ℝ) := Real.rpow_pos_of_pos hypos _
  have hA : LtN (N' + 1) + 2 * d ≤ (21/20) * y ^ (25/51 : ℝ) := by
    rw [hLt]; linarith
  have hA0 : 0 < LtN (N' + 1) + 2 * d := by
    rw [hLt]; have : 0 < y ^ (25/102 : ℝ) := Real.rpow_pos_of_pos hypos _
    have : 0 < d := Real.rpow_pos_of_pos hρ _
    linarith [hp0]
  have hA3 : (LtN (N' + 1) + 2 * d) ^ 3 ≤ ((21/20) * y ^ (25/51 : ℝ)) ^ 3 :=
    pow_le_pow_left₀ hA0.le hA 3
  have e1 : (y ^ (25/51 : ℝ)) ^ 3 = y ^ (25/17 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hypos.le]; norm_num
  have hu0 : 0 < y * ρ ^ (17/8 : ℝ) := by positivity
  have hu : y * ρ ^ (17/8 : ℝ) ≤ 51/100 := by
    have hρp : 0 < ρ ^ (17/8 : ℝ) := Real.rpow_pos_of_pos hρ _
    have : y ≤ 51/100 * X := by linarith
    calc y * ρ ^ (17/8 : ℝ) ≤ 51/100 * X * ρ ^ (17/8 : ℝ) := by gcongr
      _ = 51/100 := by rw [mul_assoc, hXρ]; ring
  have hW := Scales_W hu0 hu
  have hkey := Scales_key hρ hypos
  have hmain : ρ * ((21/20) * y ^ (25/51 : ℝ)) ^ 3 ≤ (N' : ℝ) + 1/2 := by
    have : ρ * ((21/20) * y ^ (25/51 : ℝ)) ^ 3 = (21/20) ^ 3 * (ρ * y ^ (25/17 : ℝ)) := by
      rw [mul_pow, e1]; ring
    rw [this, hkey]
    have h4 : y * (y * ρ ^ (17/8 : ℝ)) ^ (8/17 : ℝ) ≤ y * (4/5) := by gcongr
    have hyN : y = (N' : ℝ) + 1 := hy
    nlinarith
  rw [le_div_iff₀ (pow_pos hA0 3)]
  calc ρ * (LtN (N' + 1) + 2 * d) ^ 3 ≤ ρ * ((21/20) * y ^ (25/51 : ℝ)) ^ 3 := by gcongr
    _ ≤ (N' : ℝ) + 1/2 := hmain

/-- Density bound from `M < ρ (Q + c)³` and `c ≤ 8 t Q`, `t ≤ 1/25`. -/
private lemma Scales_dens {ρ M Q c t : ℝ} (hρ : 0 < ρ) (hQ : 0 < Q) (hc : 0 ≤ c)
    (hct : c ≤ 8 * t * Q) (ht0 : 0 ≤ t) (ht : t ≤ 1/25) (h : M < ρ * (Q + c) ^ 3) :
    M / Q ^ 3 ≤ ρ * (1 + 33 * t) := by
  rw [div_le_iff₀ (pow_pos hQ 3)]
  have h1 : (Q + c) ^ 3 ≤ (Q + 8 * t * Q) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have h2 : (Q + 8 * t * Q) ^ 3 = Q ^ 3 * (1 + 8 * t) ^ 3 := by ring
  have h3 : (1 + 8 * t) ^ 3 ≤ 1 + 33 * t := by
    have e1 : t * t ≤ t / 25 := by nlinarith
    have e2 : t * t * t ≤ t / 625 := by nlinarith
    nlinarith
  have hQ3 : 0 < Q ^ 3 := pow_pos hQ 3
  calc M ≤ ρ * (Q + c) ^ 3 := h.le
    _ ≤ ρ * (Q ^ 3 * (1 + 8 * t) ^ 3) := by rw [← h2]; gcongr
    _ ≤ ρ * (Q ^ 3 * (1 + 33 * t)) := by gcongr
    _ = ρ * (1 + 33 * t) * Q ^ 3 := by ring


private lemma Scales_rhotN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < rhotN N := by
  have hx : (0 : ℝ) < N := by exact_mod_cast hN
  have := Scales_LtN_pos hN
  unfold rhotN; positivity

/-- Two particle counts: `N` particles with `|ι| N₀ ≤ N ≤ |ι| (N₀ + 1)` are distributed over the
cells `ι` with `N₀` or `N₀ + 1` particles in each cell. -/
theorem thermo_counts {ι : Type*} [Fintype ι] {N₀ N : ℕ} (h₁ : Fintype.card ι * N₀ ≤ N)
    (h₂ : N ≤ Fintype.card ι * (N₀ + 1)) :
    ∃ n : ι → ℕ, (∀ m, n m = N₀ ∨ n m = N₀ + 1) ∧ ∑ m, n m = N := by
  set j := N - Fintype.card ι * N₀ with hj
  have hjk : j ≤ Fintype.card ι := by
    rw [hj]; have : Fintype.card ι * (N₀ + 1) = Fintype.card ι * N₀ + Fintype.card ι := by ring
    omega
  let e := Fintype.equivFin ι
  refine ⟨fun m => if (e m : ℕ) < j then N₀ + 1 else N₀, fun m => ?_, ?_⟩
  · by_cases h : (e m : ℕ) < j <;> simp [h]
  · have : ∑ m, (if (e m : ℕ) < j then N₀ + 1 else N₀)
        = ∑ i : Fin (Fintype.card ι), (if (i : ℕ) < j then N₀ + 1 else N₀) :=
      Equiv.sum_comp e (fun i : Fin (Fintype.card ι) => if (i : ℕ) < j then N₀ + 1 else N₀)
    rw [this]
    have h2 : ∀ i : Fin (Fintype.card ι), (if (i : ℕ) < j then N₀ + 1 else N₀) =
        N₀ + (if (i : ℕ) < j then 1 else 0) := by
      intro i; split_ifs <;> simp
    simp only [h2, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
    rw [Fin.sum_univ_eq_sum_range (fun i => if i < j then 1 else 0) (Fintype.card ι)]
    rw [Finset.sum_boole]
    have : ((Finset.range (Fintype.card ι)).filter (· < j)) = Finset.range j := by
      ext i; simp; omega
    rw [this]; simp; omega

/-- The side `L̃_N = L_N (1 + 2ρ_N^{25/48})` of Lemma 2.2 [lemma1] increases with `N`. -/
theorem LtN_monotone : Monotone LtN := by
  intro a b hab
  rw [Scales_LtN_eq, Scales_LtN_eq]
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have h1 := Real.rpow_le_rpow (Nat.cast_nonneg a) hab' (by norm_num : (0:ℝ) ≤ 25/51)
  have h2 := Real.rpow_le_rpow (Nat.cast_nonneg a) hab' (by norm_num : (0:ℝ) ≤ 25/102)
  linarith

/-- Scales of the duplication: for small `ρ`, with corridor `d = ρ^{-1/2}`, there is a box
particle number `N₀ ∈ [ρ^{-17/8}/4, ρ^{-17/8} - 1]` such that the cube of side
`L̃_{N₀+1}` with a corridor `d` on each side fits in the cell of side `((N₀ + 1/2)/ρ)^{1/3}`, and
the box densities `ρ̃_{N₀}`, `ρ̃_{N₀+1}` exceed `ρ` by at most the factor `1 + 33ρ^{13/24}`. -/
theorem thermo_scales : ∃ ρa : ℝ, 0 < ρa ∧ ∀ ρ : ℝ, 0 < ρ → ρ < ρa → ∃ N₀ : ℕ,
    ρ ^ (-(17/8 : ℝ)) / 4 ≤ N₀ ∧ (N₀ : ℝ) + 1 ≤ ρ ^ (-(17/8 : ℝ)) ∧
    LtN (N₀ + 1) + 2 * ρ ^ (-(1/2 : ℝ)) ≤ (((N₀ : ℝ) + 1/2) / ρ) ^ (1/3 : ℝ) ∧
    rhotN N₀ ≤ ρ * (1 + 33 * ρ ^ (13/24 : ℝ)) ∧
    rhotN (N₀ + 1) ≤ ρ * (1 + 33 * ρ ^ (13/24 : ℝ)) := by
  refine ⟨(1/160 : ℝ) ^ (48/25 : ℝ), by positivity, fun ρ hρ hρa => ?_⟩
  have hρ1 : ρ ≤ 1 := by
    have : (1/160 : ℝ) ^ (48/25 : ℝ) ≤ 1 :=
      Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)
    linarith
  have hρ25 : ρ ^ (25/48 : ℝ) < 1/160 := by
    have := Real.rpow_lt_rpow hρ.le hρa (by norm_num : (0:ℝ) < 25/48)
    rwa [← Real.rpow_mul (by norm_num), show (48/25 : ℝ) * (25/48) = 1 by norm_num,
      Real.rpow_one] at this
  have hp25 : 0 < ρ ^ (25/48 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hb : 160 ≤ ρ ^ (-(25/48 : ℝ)) := by
    rw [Real.rpow_neg hρ.le, le_inv_comm₀ (by norm_num) hp25]
    linarith
  have ht : ρ ^ (13/24 : ℝ) ≤ 1/25 := by
    have : ρ ^ (13/24 : ℝ) ≤ ρ ^ (25/48 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
    linarith
  have ht0 : 0 ≤ ρ ^ (13/24 : ℝ) := Real.rpow_nonneg hρ.le _
  set X := ρ ^ (-(17/8 : ℝ)) with hX
  set b := ρ ^ (-(25/48 : ℝ)) with hbdef
  set d := ρ ^ (-(1/2 : ℝ)) with hd
  have hb0 : 0 < b := by linarith
  have hXb : X = b ^ (102/25 : ℝ) := by
    rw [hbdef, ← Real.rpow_mul hρ.le, hX]; norm_num
  have hX160 : 160 ≤ X := by
    rw [hXb]
    calc (160 : ℝ) ≤ b := hb
      _ = b ^ (1 : ℝ) := (Real.rpow_one b).symm
      _ ≤ b ^ (102/25 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hd1 : 1 ≤ d := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  have hd0 : 0 < d := by linarith
  have hta : ρ ^ (13/24 : ℝ) * ρ ^ (-(25/24 : ℝ)) = d := by
    rw [← Real.rpow_add hρ, hd]; norm_num
  let P : ℕ → Prop := fun N => ρ ≤ ((N : ℝ) + 1/2) / (LtN (N + 1) + 2 * d) ^ 3
  have hN'le : ⌊X / 2⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor (by linarith)
  have hPN' : P ⌊X / 2⌋₊ := Scales_exists hρ hρ1 hb
  set N₀ := Nat.findGreatest P ⌊X⌋₊ with hN₀
  have hspec : P N₀ := Nat.findGreatest_spec hN'le hPN'
  have hN'N₀ : ⌊X / 2⌋₊ ≤ N₀ := Nat.le_findGreatest hN'le hPN'
  have hup : (N₀ : ℝ) + 1 ≤ X := Scales_upper hρ hspec
  have hfl : N₀ + 1 ≤ ⌊X⌋₊ := Nat.le_floor (by push_cast; exact hup)
  have hmax : ¬ P (N₀ + 1) := Nat.findGreatest_is_greatest (Nat.lt_succ_self N₀) hfl
  have hN₀X : X / 4 ≤ (N₀ : ℝ) := by
    have h1 : X / 2 < (⌊X / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (X / 2)
    have h2 : (⌊X / 2⌋₊ : ℝ) ≤ N₀ := by exact_mod_cast hN'N₀
    linarith
  have hN₀1 : 1 ≤ N₀ := by
    have : (1 : ℝ) ≤ N₀ := by linarith
    exact_mod_cast this
  -- the fit and the maximality
  have hA0 : 0 < LtN (N₀ + 1) + 2 * d := by
    have := Scales_LtN_pos (by omega : 1 ≤ N₀ + 1)
    linarith
  have hfit : LtN (N₀ + 1) + 2 * d ≤ (((N₀ : ℝ) + 1/2) / ρ) ^ (1/3 : ℝ) := by
    have h1 : ρ * (LtN (N₀ + 1) + 2 * d) ^ 3 ≤ (N₀ : ℝ) + 1/2 := by
      have := hspec
      simp only [P] at this
      rw [le_div_iff₀ (pow_pos hA0 3)] at this
      exact this
    rw [show (1/3 : ℝ) = (3 : ℝ)⁻¹ by norm_num,
      Real.le_rpow_inv_iff_of_pos hA0.le (by positivity) (by norm_num)]
    have e : (LtN (N₀ + 1) + 2 * d) ^ (3 : ℝ) = (LtN (N₀ + 1) + 2 * d) ^ 3 := by norm_cast
    rw [e, le_div_iff₀ hρ]
    linarith
  have hmax' : ((N₀ : ℝ) + 1 + 1/2) < ρ * (LtN (N₀ + 2) + 2 * d) ^ 3 := by
    have := hmax
    simp only [P, not_le] at this
    have hpos : 0 < (LtN (N₀ + 1 + 1) + 2 * d) ^ 3 := by
      have := Scales_LtN_pos (by omega : 1 ≤ N₀ + 1 + 1)
      positivity
    rw [div_lt_iff₀ hpos] at this
    push_cast at this
    have e : N₀ + 1 + 1 = N₀ + 2 := rfl
    rw [e] at this
    linarith
  -- the density bounds
  have hQ : ρ ^ (-(25/24 : ℝ)) / 2 ≤ LtN N₀ :=
    (Scales_H hρ hN₀X).trans (Scales_LtN_ge N₀)
  have hQ0 : 0 < ρ ^ (-(25/24 : ℝ)) := Real.rpow_pos_of_pos hρ _
  have hinc : LtN (N₀ + 2) ≤ LtN N₀ + 2 := by
    have := Scales_LtN_add hN₀1 2
    simpa using this
  have hmono : LtN N₀ ≤ LtN (N₀ + 1) := LtN_monotone (Nat.le_succ N₀)
  have hct : 2 + 2 * d ≤ 8 * ρ ^ (13/24 : ℝ) * LtN N₀ := by
    have : 8 * ρ ^ (13/24 : ℝ) * (ρ ^ (-(25/24 : ℝ)) / 2) ≤ 8 * ρ ^ (13/24 : ℝ) * LtN N₀ := by
      gcongr
    have e : 8 * ρ ^ (13/24 : ℝ) * (ρ ^ (-(25/24 : ℝ)) / 2) = 4 * d := by
      rw [← hta]; ring
    linarith
  have hQ1 : 0 < LtN N₀ := lt_of_lt_of_le (by positivity) hQ
  have hQ2 : 0 < LtN (N₀ + 2) + 2 * d := by
    have := Scales_LtN_pos (by omega : 1 ≤ N₀ + 2)
    linarith
  have hcube : ρ * (LtN (N₀ + 2) + 2 * d) ^ 3 ≤ ρ * (LtN N₀ + (2 + 2 * d)) ^ 3 := by
    have h3 : LtN (N₀ + 2) + 2 * d ≤ LtN N₀ + (2 + 2 * d) := by linarith
    gcongr
  refine ⟨N₀, hN₀X, hup, hfit, ?_, ?_⟩
  · unfold rhotN
    refine Scales_dens hρ hQ1 (by positivity) hct ht0 ht ?_
    linarith
  · have hQ1' : 0 < LtN (N₀ + 1) := lt_of_lt_of_le hQ1 hmono
    have hct' : 2 + 2 * d ≤ 8 * ρ ^ (13/24 : ℝ) * LtN (N₀ + 1) :=
      hct.trans (by gcongr)
    have hcube' : ρ * (LtN (N₀ + 2) + 2 * d) ^ 3 ≤ ρ * (LtN (N₀ + 1) + (2 + 2 * d)) ^ 3 := by
      have h3 : LtN (N₀ + 2) + 2 * d ≤ LtN (N₀ + 1) + (2 + 2 * d) := by linarith
      gcongr
    unfold rhotN
    push_cast
    refine Scales_dens hρ hQ1' (by positivity) hct' ht0 ht ?_
    linarith

/-- Eventually along `L → ∞, N/L³ → ρ`, with `K = ⌊L/s⌋` cells per side and `ρ s³ = N₀ + 1/2`,
the particle number satisfies `K³ N₀ ≤ N < K³ (N₀ + 1)`. -/
theorem thermo_eventually_counts {ρ s : ℝ} {N₀ : ℕ} (hρ : 0 < ρ) (hs : 0 < s)
    (hs3 : ρ * s ^ 3 = (N₀ : ℝ) + 1/2) :
    ∀ᶠ x in thermo ρ, 0 < x.2 ∧ 1 ≤ x.1 ∧ 1 ≤ ⌊x.2 / s⌋₊ ∧ ⌊x.2 / s⌋₊ ^ 3 * N₀ ≤ x.1 ∧
      x.1 < ⌊x.2 / s⌋₊ ^ 3 * (N₀ + 1) := by
  have hL : Tendsto (fun x : ℕ × ℝ => x.2) (thermo ρ) atTop :=
    (tendsto_comap).mono_left inf_le_left
  have hq : Tendsto (fun x : ℕ × ℝ => (x.1 : ℝ) / x.2 ^ 3) (thermo ρ) (𝓝 ρ) :=
    (tendsto_comap).mono_left inf_le_right
  -- K / L → 1 / s
  have hK : Tendsto (fun x : ℕ × ℝ => (⌊x.2 / s⌋₊ : ℝ) / x.2) (thermo ρ) (𝓝 (1 / s)) := by
    have h1 : Tendsto (fun L : ℝ => (⌊L / s⌋₊ : ℝ) / (L / s)) atTop (𝓝 1) :=
      tendsto_nat_floor_div_atTop.comp (tendsto_id.atTop_div_const hs)
    have h2 := (h1.mul_const (1 / s)).comp hL
    simp only [one_mul] at h2
    refine h2.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with x hx
    simp only [Function.comp]
    field_simp
  have hlim : Tendsto (fun x : ℕ × ℝ => ((x.1 : ℝ) / x.2 ^ 3) / ((⌊x.2 / s⌋₊ : ℝ) / x.2) ^ 3)
      (thermo ρ) (𝓝 (ρ / (1 / s) ^ 3)) :=
    hq.div (hK.pow 3) (by positivity)
  have hval : ρ / (1 / s) ^ 3 = (N₀ : ℝ) + 1/2 := by
    rw [← hs3]; field_simp
  rw [hval] at hlim
  have hmem : Set.Ioo (N₀ : ℝ) (N₀ + 1) ∈ 𝓝 ((N₀ : ℝ) + 1/2) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hev := hlim.eventually hmem
  have hqpos : ∀ᶠ x in thermo ρ, ρ / 2 < (x.1 : ℝ) / x.2 ^ 3 :=
    hq.eventually (lt_mem_nhds (by linarith))
  filter_upwards [hev, hqpos, hL.eventually_ge_atTop s, hL.eventually_gt_atTop 0] with x hx hxq hxL hx0
  obtain ⟨hl, hr⟩ := hx
  have hK1 : 1 ≤ ⌊x.2 / s⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hs]; linarith
  have hKpos : (0 : ℝ) < ⌊x.2 / s⌋₊ := by exact_mod_cast hK1
  have hN : (0 : ℝ) < x.1 := by
    have : 0 < (x.1 : ℝ) / x.2 ^ 3 := by linarith
    have h3 : 0 < x.2 ^ 3 := by positivity
    exact (div_pos_iff_of_pos_right h3).1 this
  have hN1 : 1 ≤ x.1 := by exact_mod_cast hN
  have e : ((x.1 : ℝ) / x.2 ^ 3) / ((⌊x.2 / s⌋₊ : ℝ) / x.2) ^ 3 = (x.1 : ℝ) / (⌊x.2 / s⌋₊ : ℝ) ^ 3 := by
    field_simp
  rw [e] at hl hr
  have hK3 : (0 : ℝ) < (⌊x.2 / s⌋₊ : ℝ) ^ 3 := by positivity
  rw [lt_div_iff₀ hK3] at hl
  rw [div_lt_iff₀ hK3] at hr
  refine ⟨hx0, hN1, hK1, ?_, ?_⟩
  · have : ((⌊x.2 / s⌋₊ ^ 3 * N₀ : ℕ) : ℝ) ≤ x.1 := by push_cast; linarith
    exact_mod_cast this
  · have : (x.1 : ℝ) < ((⌊x.2 / s⌋₊ ^ 3 * (N₀ + 1) : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this

/-- The bound of Lemma 2.1 [thm1] in eventual form: for every `ε > 0`, eventually in `N` the
state `Ψ_N` is a Dirichlet trial state on `[0,L̃_N]³` with
`⟨H_N⟩/N ≤ g₀ρ̃_N + (16/(15π²) + ε) g₀^{5/2} ρ̃_N^{3/2}`. -/
theorem thermo_eventually_box_bound {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) {Ψ : (N : ℕ) → Conf N → ℂ}
    (hΨ : ∀ᶠ N in atTop, IsDirichletTrial (LtN N) N (Ψ N))
    (hlim : limsup (fun N : ℕ => ratio (g0 V w) (rhotN N) ((energyD V (Ψ N) / N : ℝ) : EReal))
      atTop ≤ (cLHY : EReal)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, IsDirichletTrial (LtN N) N (Ψ N) ∧
      energyD V (Ψ N) / N ≤
        g0 V w * rhotN N + (cLHY + ε) * g0 V w ^ (5/2 : ℝ) * rhotN N ^ (3/2 : ℝ) := by
  have hg : 0 < g0 V w := scat_g0_pos hV hw
  have hlt : limsup (fun N : ℕ => ratio (g0 V w) (rhotN N) ((energyD V (Ψ N) / N : ℝ) : EReal))
      atTop < ((cLHY + ε : ℝ) : EReal) :=
    lt_of_le_of_lt hlim (by exact_mod_cast (lt_add_of_pos_right cLHY hε))
  have hev := Filter.eventually_lt_of_limsup_lt hlt
  filter_upwards [hΨ, hev, eventually_ge_atTop 1] with N hΨN hN hN1
  refine ⟨hΨN, ?_⟩
  have hρ := Scales_rhotN_pos hN1
  set ρ := rhotN N with hρdef
  set E := energyD V (Ψ N) / N with hE
  set m : ℝ := (g0 V w ^ (5/2 : ℝ) * ρ ^ (3/2 : ℝ))⁻¹ with hm
  have hmpos : 0 < m := by rw [hm]; positivity
  have h1 : ratio (g0 V w) ρ ((E : ℝ) : EReal) = (((E - g0 V w * ρ) * m : ℝ) : EReal) := by
    unfold ratio
    rw [← EReal.coe_sub, ← EReal.coe_mul]
  rw [h1] at hN
  have h2 : (E - g0 V w * ρ) * m < cLHY + ε := by exact_mod_cast hN
  have h3 : E - g0 V w * ρ < (cLHY + ε) * (g0 V w ^ (5/2 : ℝ) * ρ ^ (3/2 : ℝ)) := by
    have hmi : m⁻¹ = g0 V w ^ (5/2 : ℝ) * ρ ^ (3/2 : ℝ) := by rw [hm, inv_inv]
    have := (mul_lt_mul_iff_of_pos_right (inv_pos.2 hmpos)).2 h2
    rw [mul_assoc, mul_inv_cancel₀ hmpos.ne', mul_one, hmi] at this
    exact this
  linarith

/-! ### Compiled instances of the hypotheses -/

/-- The filter `thermo ρ` of §2 is proper for every `ρ > 0`: the pairs `(⌊ρ n³⌋₊, n)` tend to it,
so the lim sup in Theorem 2.1 [mainthm] is not taken over the empty filter. -/
theorem thermo_neBot {ρ : ℝ} (hρ : 0 < ρ) : (thermo ρ).NeBot := by
  have hf : Tendsto (fun n : ℕ => (⌊ρ * (n : ℝ) ^ 3⌋₊, (n : ℝ))) atTop (thermo ρ) := by
    refine tendsto_inf.2 ⟨tendsto_comap_iff.2 ?_, tendsto_comap_iff.2 ?_⟩
    · exact tendsto_natCast_atTop_atTop
    · have h1 : Tendsto (fun x : ℝ => (⌊ρ * x⌋₊ : ℝ) / x) atTop (𝓝 ρ) :=
        tendsto_nat_floor_mul_div_atTop hρ.le
      have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ 3) atTop atTop :=
        (tendsto_pow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
      exact h1.comp h2
  exact hf.neBot

example : (thermo (7/2 : ℝ)).NeBot := thermo_neBot (by norm_num)

end LHYUpper
