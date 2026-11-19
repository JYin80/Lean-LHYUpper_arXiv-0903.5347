import LHYUpper.Scattering.Solution

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Counting and series bounds for the hardest lemma

Elementary bounds used in Section 11: the number of lattice points `n ∈ ℤ³` with `|2πn/L| ≤ R` is at
most `8 (RL)³ / π³` when `RL ≥ π` (`HardBounds_card_ball`), and the `(s, t)` series after Lemma 11.3
[lem11.1] is bounded through geometric partial sums with ratio at most `1/2` (`HardBounds_series`). -/

/-- Each coordinate of a lattice point with `|2πn/L| ≤ R` is bounded by `RL/(2π)`. -/
private lemma HardBounds_coord_le {L R : ℝ} (hL : 0 < L) {n : Idx} (hn : ‖mom L n‖ ≤ R)
    (i : Fin 3) : |(n i : ℝ)| ≤ R * L / (2 * π) := by
  have h1 : |(mom L n).ofLp i| ≤ R := by
    have := PiLp.norm_apply_le (mom L n) i
    rw [Real.norm_eq_abs] at this
    exact this.trans hn
  have e : (mom L n).ofLp i = 2 * π / L * (n i : ℝ) := rfl
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
  rw [le_div_iff₀ (by positivity)]
  rw [div_mul_eq_mul_div, div_le_iff₀ hL] at h1
  nlinarith

/-- The number of `n ∈ ℤ³` with `|2πn/L| ≤ R` is at most `8 (RL)³ / π³` when `RL ≥ π`
(the counts of `P_L` and `P_{H,c}` before (11.18) [temp8.178]). -/
theorem HardBounds_card_ball {L R : ℝ} (hL : 0 < L) (hR : π ≤ R * L) :
    {n : Idx | ‖mom L n‖ ≤ R}.Finite ∧
      ({n : Idx | ‖mom L n‖ ≤ R}.ncard : ℝ) ≤ 8 / π ^ 3 * (R * L) ^ 3 := by
  have hπ : 0 < π := Real.pi_pos
  set x : ℝ := R * L / (2 * π) with hx
  set M : ℕ := ⌊x⌋₊ with hM
  have hx0 : 0 ≤ x := by
    have : 0 ≤ R * L := hπ.le.trans hR
    positivity
  have hsub : {n : Idx | ‖mom L n‖ ≤ R} ⊆
      (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-(M : ℤ)) (M : ℤ)) : Set Idx) := by
    intro n hn
    simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    have h := HardBounds_coord_le hL hn i
    have h2 : |n i| ≤ (M : ℤ) := by
      have h3 : (|n i| : ℤ) ≤ ⌊x⌋ := by
        rw [Int.le_floor]
        push_cast
        exact h
      have h4 : (⌊x⌋ : ℤ) = (M : ℤ) := by
        rw [hM, Int.natCast_floor_eq_floor hx0]
      omega
    exact abs_le.1 h2
  have hfin : {n : Idx | ‖mom L n‖ ≤ R}.Finite := (Finset.finite_toSet _).subset hsub
  refine ⟨hfin, ?_⟩
  have hcard : ({n : Idx | ‖mom L n‖ ≤ R}.ncard : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) ^ 3 := by
    have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset, Fintype.card_piFinset] at h1
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    rw [h2] at h1
    exact_mod_cast h1
  have hMx : (M : ℝ) ≤ x := Nat.floor_le hx0
  have hx1 : (1 : ℝ) / 2 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity)]
    linarith
  have h2M : ((2 * M + 1 : ℕ) : ℝ) ≤ 2 * R * L / (2 * π) * 2 := by
    push_cast
    have : 2 * R * L / (2 * π) = 2 * x := by rw [hx]; ring
    rw [this]
    linarith
  have h2M' : ((2 * M + 1 : ℕ) : ℝ) ≤ 2 * (R * L) / π := by
    have : 2 * R * L / (2 * π) * 2 = 2 * (R * L) / π := by field_simp
    linarith
  calc ({n : Idx | ‖mom L n‖ ≤ R}.ncard : ℝ) ≤ ((2 * M + 1 : ℕ) : ℝ) ^ 3 := hcard
    _ ≤ (2 * (R * L) / π) ^ 3 := pow_le_pow_left₀ (by positivity) h2M' 3
    _ = 8 / π ^ 3 * (R * L) ^ 3 := by field_simp; ring

/-- A geometric partial sum with ratio `y ≤ 1/2` is at most `2`. -/
private lemma HardBounds_geom {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (n : ℕ) :
    ∑ s ∈ Finset.range n, y ^ s ≤ 2 := by
  have h := mul_neg_geom_sum y n
  have h0 : 0 ≤ ∑ s ∈ Finset.range n, y ^ s := Finset.sum_nonneg fun s _ => by positivity
  have : 0 ≤ y ^ n := by positivity
  nlinarith

/-- The closed form of `Σ_{t=2}^{n+1} t² 2^{2-t}`. -/
private lemma HardBounds_closed (n : ℕ) :
    ∑ t ∈ Finset.Icc 2 (n + 1), (t : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (t - 2) =
      22 - 2 * ((n : ℝ) ^ 2 + 6 * n + 11) * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have : n + 1 + 1 - 2 = n := by omega
    rw [this]
    push_cast
    ring

/-- The `t`-th row of the series is bounded by `2ay` at `t = 1` and by `2a² t² 2^{2-t}` for
`t ≥ 2`. -/
private lemma HardBounds_row {a y : ℝ} (ha : 0 ≤ a) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (S t : ℕ)
    (ht1 : 1 ≤ t) (hat : a * Real.sqrt t ≤ 1 / 2) :
    ∑ s ∈ Finset.range (S + 1),
      (if 2 ≤ s + t then (t : ℝ) * (a * Real.sqrt t) ^ t * y ^ s else 0) ≤
        (if t = 1 then 2 * a * y else 0) +
          (if 2 ≤ t then 2 * a ^ 2 * ((t : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (t - 2)) else 0) := by
  rcases Nat.eq_or_lt_of_le ht1 with h | h
  · subst h
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_one, Real.sqrt_one, mul_one, pow_one, one_mul]
    have h1 : ∀ i : ℕ, (if 2 ≤ i + 1 + 1 then a * y ^ (i + 1) else 0) = a * y * y ^ i := by
      intro i
      rw [if_pos (by omega)]
      ring
    simp only [h1]
    have e2 : ¬ ((2 : ℕ) ≤ 1) := by norm_num
    simp only [e2, if_true, if_false, add_zero]
    rw [← Finset.mul_sum]
    have := HardBounds_geom hy0 hy S
    have h3 : 0 ≤ a * y := by positivity
    nlinarith
  · have hne : t ≠ 1 := by omega
    rw [if_neg hne, if_pos (by omega), zero_add]
    have hall : ∀ s ∈ Finset.range (S + 1),
        (if 2 ≤ s + t then (t : ℝ) * (a * Real.sqrt t) ^ t * y ^ s else 0) =
          (t : ℝ) * (a * Real.sqrt t) ^ t * y ^ s := fun s _ => if_pos (by omega)
    rw [Finset.sum_congr rfl hall, ← Finset.mul_sum]
    have hg := HardBounds_geom hy0 hy (S + 1)
    obtain ⟨m, rfl⟩ : ∃ m, t = m + 2 := ⟨t - 2, by omega⟩
    have hsq : (a * Real.sqrt ((m + 2 : ℕ) : ℝ)) ^ 2 = a ^ 2 * ((m + 2 : ℕ) : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
    have hpow : (a * Real.sqrt ((m + 2 : ℕ) : ℝ)) ^ m ≤ (1 / 2 : ℝ) ^ m :=
      pow_le_pow_left₀ (by positivity) hat m
    have hpos : (0 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by positivity
    have e : (m + 2 - 2) = m := by omega
    rw [e, pow_add, mul_comm ((a * Real.sqrt _) ^ m), hsq]
    have h4 : (((m + 2 : ℕ) : ℝ)) *
          (a ^ 2 * ((m + 2 : ℕ) : ℝ) * (a * Real.sqrt ((m + 2 : ℕ) : ℝ)) ^ m)
        ≤ ((m + 2 : ℕ) : ℝ) * (a ^ 2 * ((m + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ m) := by
      apply mul_le_mul_of_nonneg_left _ hpos
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
    have hX0 : 0 ≤ ((m + 2 : ℕ) : ℝ) *
        (a ^ 2 * ((m + 2 : ℕ) : ℝ) * (a * Real.sqrt ((m + 2 : ℕ) : ℝ)) ^ m) := by positivity
    have h6 := mul_le_mul_of_nonneg_left hg hX0
    linarith

/-- The `(s, t)` series after Lemma 11.3 [lem11.1]:
`Σ_{1 ≤ t ≤ T} Σ_{s + t ≥ 2} t (a √t)^t y^s ≤ 2ay + 44a²` for `a √T ≤ 1/2`, `0 ≤ y ≤ 1/2`. -/
theorem HardBounds_series {a y : ℝ} (ha : 0 ≤ a) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (T S : ℕ)
    (haT : a * Real.sqrt T ≤ 1 / 2) :
    ∑ t ∈ Finset.Icc 1 T, ∑ s ∈ Finset.range (S + 1),
      (if 2 ≤ s + t then (t : ℝ) * (a * Real.sqrt t) ^ t * y ^ s else 0) ≤
        2 * a * y + 44 * a ^ 2 := by
  have hrow : ∀ t ∈ Finset.Icc 1 T,
      ∑ s ∈ Finset.range (S + 1),
        (if 2 ≤ s + t then (t : ℝ) * (a * Real.sqrt t) ^ t * y ^ s else 0) ≤
          (if t = 1 then 2 * a * y else 0) +
            (if 2 ≤ t then 2 * a ^ 2 * ((t : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (t - 2)) else 0) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    refine HardBounds_row ha hy0 hy S t ht.1 ?_
    have : Real.sqrt (t : ℝ) ≤ Real.sqrt (T : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast ht.2)
    nlinarith [mul_le_mul_of_nonneg_left this ha]
  refine (Finset.sum_le_sum hrow).trans ?_
  rw [Finset.sum_add_distrib]
  have h1 : ∑ t ∈ Finset.Icc 1 T, (if t = 1 then 2 * a * y else 0) ≤ 2 * a * y := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have h2 : ∑ t ∈ Finset.Icc 1 T,
      (if 2 ≤ t then 2 * a ^ 2 * ((t : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (t - 2)) else 0) ≤ 44 * a ^ 2 := by
    rw [← Finset.sum_filter]
    have hf : (Finset.Icc 1 T).filter (fun t => 2 ≤ t) = Finset.Icc 2 T := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hf, ← Finset.mul_sum]
    have h22 : ∑ t ∈ Finset.Icc 2 T, (t : ℝ) ^ 2 * (1 / 2 : ℝ) ^ (t - 2) ≤ 22 := by
      rcases T with _ | n
      · simp
      · rw [HardBounds_closed n]
        have : 0 ≤ 2 * ((n : ℝ) ^ 2 + 6 * n + 11) * (1 / 2 : ℝ) ^ n := by positivity
        linarith
    nlinarith [sq_nonneg a]
  linarith

end LHYUpper
