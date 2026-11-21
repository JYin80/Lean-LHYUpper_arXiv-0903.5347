module

public import LHYUpper.Position.Periodize

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- The decay constant `sup_z |V(z)| |z|⁸` of the potential (fast decay of order 8). -/
def decayConst8 (V : R3 → ℝ) : ℝ := ⨆ z, |V z| * ‖z‖ ^ 8

/-- Under the hypotheses of Theorem 2.1 [mainthm], `|V(z)| |z|⁸ ≤ decayConst8 V` for all `z`. -/
theorem decayConst8_spec {V : R3 → ℝ} (hV : PotentialHyp V) (z : R3) :
    |V z| * ‖z‖ ^ 8 ≤ decayConst8 V := by
  obtain ⟨S, hS⟩ := hV.schwartz
  refine le_ciSup (f := fun z => |V z| * ‖z‖ ^ 8) ⟨SchwartzMap.seminorm ℝ 8 0 S, ?_⟩ z
  rintro _ ⟨y, rfl⟩
  have h := SchwartzMap.le_seminorm ℝ 8 0 S y
  rw [norm_iteratedFDeriv_zero, hS] at h
  simpa [mul_comm, Real.norm_eq_abs] using h

/-! ### Lattice sums of `|m|_∞⁻⁸` over `ℤ³`

The decay bound `|V(z)| |z|⁸ ≤ C` reduces the interaction between cells (and with the periodic
images) of the duplication step after Lemma 2.1 [thm1] to the lattice sum of `|m|_∞⁻⁸`, which is
at most `27` by the shell count `(2r+1)³ - (2r-1)³ = 24 r² + 2` (Theorem 2.1 [mainthm], with
`V^P` the lattice sum of (2.1) [ham]). -/

/-- The sup-norm `max_a |m_a|` of a lattice index. -/
private def InterBox_nm (m : Idx) : ℕ := Finset.univ.sup fun a => (m a).natAbs

/-- The weight `|m|_∞⁻⁸` (zero at the origin). -/
private def InterBox_F (m : Idx) : ℝ := (((InterBox_nm m : ℕ) : ℝ) ^ 8)⁻¹

private lemma InterBox_F_nonneg (m : Idx) : 0 ≤ InterBox_F m := by
  unfold InterBox_F; positivity

private lemma InterBox_nm_le_iff (m : Idx) (R : ℕ) : InterBox_nm m ≤ R ↔ ∀ a, |m a| ≤ (R : ℤ) := by
  unfold InterBox_nm
  rw [Finset.sup_le_iff]
  refine forall_congr' fun a => ?_
  simp only [Finset.mem_univ, true_implies]
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Iff.rfl

private lemma InterBox_nm_zero : InterBox_nm 0 = 0 := by
  simp [InterBox_nm]

private lemma InterBox_nm_pos {m : Idx} (hm : m ≠ 0) : 0 < InterBox_nm m := by
  obtain ⟨a, ha⟩ : ∃ a, m a ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  have h1 : (m a).natAbs ≤ InterBox_nm m :=
    Finset.le_sup (f := fun a => (m a).natAbs) (Finset.mem_univ a)
  have h2 : 0 < (m a).natAbs := Int.natAbs_pos.2 ha
  omega

/-- The box `{m : |m|_∞ ≤ R}` of lattice indices. -/
private def InterBox_box (R : ℕ) : Finset Idx :=
  Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-(R : ℤ)) R

private lemma InterBox_mem_box (R : ℕ) (m : Idx) : m ∈ InterBox_box R ↔ InterBox_nm m ≤ R := by
  rw [InterBox_nm_le_iff, InterBox_box, Fintype.mem_piFinset]
  refine forall_congr' fun a => ?_
  rw [Finset.mem_Icc, abs_le]

private lemma InterBox_card_box (R : ℕ) : (InterBox_box R).card = (2 * R + 1) ^ 3 := by
  rw [InterBox_box, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

private lemma InterBox_box_mono (R : ℕ) : InterBox_box R ⊆ InterBox_box (R + 1) := by
  intro m hm
  rw [InterBox_mem_box] at hm ⊢
  omega

private lemma InterBox_F_sdiff {R : ℕ} {m : Idx} (hm : m ∈ InterBox_box (R + 1) \ InterBox_box R) :
    InterBox_F m = (((R : ℝ) + 1) ^ 8)⁻¹ := by
  rw [Finset.mem_sdiff, InterBox_mem_box, InterBox_mem_box] at hm
  have : InterBox_nm m = R + 1 := by omega
  rw [InterBox_F, this]
  push_cast
  rfl

/-- The partial sum of the weight over the box of radius `R`. -/
private lemma InterBox_sum_box_succ (R : ℕ) :
    ∑ m ∈ InterBox_box (R + 1), InterBox_F m =
      (∑ m ∈ InterBox_box R, InterBox_F m) +
        (24 * ((R : ℝ) + 1) ^ 2 + 2) * (((R : ℝ) + 1) ^ 8)⁻¹ := by
  rw [← Finset.sum_sdiff (InterBox_box_mono R)]
  rw [add_comm]
  congr 1
  rw [Finset.sum_congr rfl fun m hm => InterBox_F_sdiff hm, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have h := Finset.card_sdiff_add_card_eq_card (InterBox_box_mono R)
  rw [InterBox_card_box, InterBox_card_box] at h
  have h' : ((InterBox_box (R + 1) \ InterBox_box R).card : ℝ) + (2 * R + 1) ^ 3 =
      (2 * ((R + 1 : ℕ) : ℝ) + 1) ^ 3 := by exact_mod_cast h
  push_cast at h'
  linarith

private lemma InterBox_sum_box_zero : ∑ m ∈ InterBox_box 0, InterBox_F m = 0 := by
  have : InterBox_box 0 = {0} := by
    ext m
    rw [InterBox_mem_box, Finset.mem_singleton]
    constructor
    · intro h
      by_contra hm
      have := InterBox_nm_pos hm
      omega
    · rintro rfl
      simp [InterBox_nm_zero]
  rw [this, Finset.sum_singleton, InterBox_F, InterBox_nm_zero]
  simp

private lemma InterBox_shell_step (R : ℕ) (hR : 1 ≤ R) :
    (24 * ((R : ℝ) + 1) ^ 2 + 2) * (((R : ℝ) + 1) ^ 8)⁻¹ ≤ 1 / (R : ℝ) - 1 / ((R : ℝ) + 1) := by
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  obtain ⟨t, ht, ht'⟩ : ∃ t : ℝ, 0 ≤ t ∧ (R : ℝ) = 1 + t := ⟨R - 1, by linarith, by ring⟩
  rw [ht']
  have h1 : (0 : ℝ) < 1 + t := by linarith
  have h2 : (0 : ℝ) < 1 + t + 1 := by linarith
  rw [div_sub_div _ _ h1.ne' h2.ne', inv_eq_one_div, ← mul_div_assoc,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_nonneg ht 2, pow_nonneg ht 3, pow_nonneg ht 4, pow_nonneg ht 5, pow_nonneg ht 6,
    pow_nonneg ht 7, pow_nonneg ht 8, pow_nonneg ht 9]


private lemma InterBox_sum_box_le (R : ℕ) : ∑ m ∈ InterBox_box R, InterBox_F m ≤ 27 := by
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · rw [InterBox_sum_box_zero]; norm_num
  · have key : ∀ R : ℕ, 1 ≤ R → ∑ m ∈ InterBox_box R, InterBox_F m ≤ 27 - 1 / (R : ℝ) := by
      intro R hR
      induction R, hR using Nat.le_induction with
      | base =>
        have h := InterBox_sum_box_succ 0
        rw [InterBox_sum_box_zero] at h
        norm_num at h ⊢
        linarith
      | succ R hR ih =>
        rw [InterBox_sum_box_succ]
        have := InterBox_shell_step R hR
        push_cast
        linarith
    have h1 := key R hR
    have : (0 : ℝ) ≤ 1 / (R : ℝ) := by positivity
    linarith

/-- Every finite partial sum of the weight `|m|_∞⁻⁸` is at most `27`. -/
private lemma InterBox_sum_le (u : Finset Idx) : ∑ m ∈ u, InterBox_F m ≤ 27 := by
  have hsub : u ⊆ InterBox_box (u.sup InterBox_nm) := fun m hm =>
    (InterBox_mem_box _ _).2 (Finset.le_sup (f := InterBox_nm) hm)
  exact (Finset.sum_le_sum_of_subset_of_nonneg hsub fun m _ _ => InterBox_F_nonneg m).trans
    (InterBox_sum_box_le _)

/-- The weight `|m|_∞⁻⁸` composed with an injective map is summable, with sum at most `27`. -/
private lemma InterBox_comp {ι : Type*} {Φ : ι → Idx} (hΦ : Function.Injective Φ) :
    Summable (fun x => InterBox_F (Φ x)) ∧ ∑' x, InterBox_F (Φ x) ≤ 27 := by
  have h : ∀ u : Finset ι, ∑ x ∈ u, InterBox_F (Φ x) ≤ 27 := fun u => by
    rw [← Finset.sum_image (f := InterBox_F) (fun x _ y _ h => hΦ h)]
    exact InterBox_sum_le _
  exact ⟨summable_of_sum_le (fun x => InterBox_F_nonneg _) h,
    Real.tsum_le_of_sum_le (fun x => InterBox_F_nonneg _) h⟩

/-! ### Cells and images -/

/-- The index `c - e - K n` of the image `n` of a particle in the cell `c`. -/
private def InterBox_idx (K : ℕ) (e : Idx) (c : Fin 3 → Fin K) (n : Idx) : Idx :=
  fun a => ((c a : ℕ) : ℤ) - e a - (K : ℤ) * n a

private lemma InterBox_div {K : ℕ} {p q : Fin K} {t : ℤ}
    (h : ((p : ℕ) : ℤ) - ((q : ℕ) : ℤ) = (K : ℤ) * t) : p = q ∧ t = 0 := by
  have hK : (0 : ℤ) < K := by exact_mod_cast p.pos
  have hp : ((p : ℕ) : ℤ) < K := by exact_mod_cast p.isLt
  have hq : ((q : ℕ) : ℤ) < K := by exact_mod_cast q.isLt
  have h0 : ((p : ℕ) : ℤ) - ((q : ℕ) : ℤ) = 0 :=
    Int.eq_zero_of_abs_lt_dvd ⟨t, h⟩ (by rw [abs_lt]; omega)
  refine ⟨Fin.ext (by omega), ?_⟩
  rw [h0] at h
  rcases mul_eq_zero.1 h.symm with h1 | h1
  · omega
  · exact h1

private lemma InterBox_idx_inj (K : ℕ) (e : Idx) :
    Function.Injective (fun p : (Fin 3 → Fin K) × Idx => InterBox_idx K e p.1 p.2) := by
  rintro ⟨c, n⟩ ⟨c', n'⟩ h
  have h' : ∀ a, ((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) = (K : ℤ) * (n a - n' a) := fun a => by
    have := congrFun h a
    simp only [InterBox_idx] at this
    linarith
  refine Prod.ext (funext fun a => (InterBox_div (h' a)).1) (funext fun a => ?_)
  have := (InterBox_div (h' a)).2
  simpa [sub_eq_zero] using this

private lemma InterBox_idx_inj_n (K : ℕ) (e : Idx) (c : Fin 3 → Fin K) :
    Function.Injective (fun n : Idx => InterBox_idx K e c n) := fun n n' h =>
  (Prod.mk.inj (InterBox_idx_inj K e (a₁ := (c, n)) (a₂ := (c, n')) h)).2

private lemma InterBox_idx_eq_zero {K : ℕ} {ci cj : Fin 3 → Fin K} {n : Idx}
    (h : InterBox_idx K (fun a => ((ci a : ℕ) : ℤ)) cj n = 0) : n = 0 ∧ cj = ci := by
  have h' : ∀ a, ((cj a : ℕ) : ℤ) - ((ci a : ℕ) : ℤ) = (K : ℤ) * n a := fun a => by
    have := congrFun h a
    simp only [InterBox_idx, Pi.zero_apply] at this
    linarith
  exact ⟨funext fun a => (InterBox_div (h' a)).2, funext fun a => (InterBox_div (h' a)).1⟩


private lemma InterBox_lat_apply (L : ℝ) (n : Idx) (a : Fin 3) : (lat L n) a = L * (n a : ℝ) := rfl

private lemma InterBox_lat_zero (L : ℝ) : lat L 0 = 0 := by
  ext a
  simp [InterBox_lat_apply]

/-- Two points in cells at sup-distance `r ≥ 1` (after the image shift `n`) are at distance at
least `2 d r`. -/
private lemma InterBox_dist {K : ℕ} {sL d ℓ : ℝ} (hd : 0 < d) (hfit : ℓ + 2 * d ≤ sL)
    {ci cj : Fin 3 → Fin K} {xi xj : R3}
    (hi : ∀ a, sL * ((ci a : ℕ) : ℝ) + d < xi a ∧ xi a < sL * ((ci a : ℕ) : ℝ) + d + ℓ)
    (hj : ∀ a, sL * ((cj a : ℕ) : ℝ) + d < xj a ∧ xj a < sL * ((cj a : ℕ) : ℝ) + d + ℓ)
    (n : Idx) (hm : InterBox_idx K (fun a => ((ci a : ℕ) : ℤ)) cj n ≠ 0) :
    2 * d * (InterBox_nm (InterBox_idx K (fun a => ((ci a : ℕ) : ℤ)) cj n) : ℝ) ≤
      ‖xi - xj + lat (K * sL) n‖ := by
  set m := InterBox_idx K (fun a => ((ci a : ℕ) : ℤ)) cj n with hmdef
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3))
    Finset.univ_nonempty (fun a => (m a).natAbs)
  have hnm : InterBox_nm m = (m a).natAbs := ha
  have hpos : 0 < InterBox_nm m := InterBox_nm_pos hm
  have hr : (1 : ℝ) ≤ ((m a).natAbs : ℝ) := by
    have : 1 ≤ (m a).natAbs := by omega
    exact_mod_cast this
  have hℓ : 0 < ℓ := by
    have h0 := hi 0
    linarith [h0.1, h0.2]
  have hs : 0 ≤ sL := by linarith
  set w := xi - xj + lat (K * sL) n with hw
  have hwa : w a = xi a - xj a + (K : ℝ) * sL * (n a : ℝ) := by
    simp [hw, InterBox_lat_apply]
  have hma : ((m a : ℤ) : ℝ) = ((cj a : ℕ) : ℝ) - ((ci a : ℕ) : ℝ) - (K : ℝ) * (n a : ℝ) := by
    simp [hmdef, InterBox_idx]
  have hI := hi a
  have hJ := hj a
  have hsum : w a + sL * ((m a : ℤ) : ℝ) =
      (xi a - sL * ((ci a : ℕ) : ℝ)) - (xj a - sL * ((cj a : ℕ) : ℝ)) := by
    rw [hwa, hma]; ring
  have hlt : |w a + sL * ((m a : ℤ) : ℝ)| < ℓ := by
    rw [hsum, abs_lt]; constructor <;> linarith [hI.1, hI.2, hJ.1, hJ.2]
  have hab : sL * ((m a).natAbs : ℝ) ≤ |w a| + |w a + sL * ((m a : ℤ) : ℝ)| := by
    have e1 : sL * ((m a).natAbs : ℝ) = |sL * ((m a : ℤ) : ℝ)| := by
      rw [abs_mul, abs_of_nonneg hs, Nat.cast_natAbs, Int.cast_abs]
    rw [e1]
    calc |sL * ((m a : ℤ) : ℝ)| = |(w a + sL * ((m a : ℤ) : ℝ)) - w a| := by ring_nf
      _ ≤ |w a + sL * ((m a : ℤ) : ℝ)| + |w a| := abs_sub _ _
      _ = _ := add_comm _ _
  have hwn : |w a| ≤ ‖w‖ := by
    have := PiLp.norm_apply_le w a
    simpa [Real.norm_eq_abs] using this
  rw [hnm]
  have h1 : 2 * d * ((m a).natAbs : ℝ) ≤ sL * ((m a).natAbs : ℝ) - ℓ := by
    nlinarith [mul_nonneg (sub_nonneg.2 hfit) (by linarith : (0 : ℝ) ≤ ((m a).natAbs : ℝ)),
      mul_nonneg hℓ.le (sub_nonneg.2 hr)]
  linarith

private lemma InterBox_term {V : R3 → ℝ} {C : ℝ} (hC : ∀ z, |V z| * ‖z‖ ^ 8 ≤ C) {d : ℝ}
    (hd : 0 < d) {w : R3} {r : ℝ} (hr : 1 ≤ r) (hw : 2 * d * r ≤ ‖w‖) :
    |V w| ≤ C / (2 * d) ^ 8 * (r ^ 8)⁻¹ := by
  have h0 : 0 < 2 * d * r := by positivity
  have h1 : (2 * d * r) ^ 8 ≤ ‖w‖ ^ 8 := pow_le_pow_left₀ h0.le hw 8
  have h2 : |V w| * (2 * d * r) ^ 8 ≤ C :=
    (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)).trans (hC w)
  have h3 : C / (2 * d) ^ 8 * (r ^ 8)⁻¹ = C / (2 * d * r) ^ 8 := by
    rw [mul_pow]; field_simp
  rw [h3, le_div_iff₀ (by positivity)]
  exact h2


/-- Interaction of one pair of particles with all images of the second one: the periodized
interaction exceeds the direct term (present only for equal cells) by at most the lattice sum
of the weights. -/
private lemma InterBox_pair {V : R3 → ℝ} {C : ℝ} (hC : ∀ z, |V z| * ‖z‖ ^ 8 ≤ C) {K : ℕ}
    {sL d ℓ : ℝ} (hd : 0 < d) (hfit : ℓ + 2 * d ≤ sL) {ci cj : Fin 3 → Fin K} {xi xj : R3}
    (hi : ∀ a, sL * ((ci a : ℕ) : ℝ) + d < xi a ∧ xi a < sL * ((ci a : ℕ) : ℝ) + d + ℓ)
    (hj : ∀ a, sL * ((cj a : ℕ) : ℝ) + d < xj a ∧ xj a < sL * ((cj a : ℕ) : ℝ) + d + ℓ) :
    periodize (K * sL) V (xi - xj) ≤ (if ci = cj then V (xi - xj) else 0) +
      C / (2 * d) ^ 8 *
        ∑' n : Idx, InterBox_F (InterBox_idx K (fun a => ((ci a : ℕ) : ℤ)) cj n) := by
  set e : Idx := fun a => ((ci a : ℕ) : ℤ) with he
  set κ : ℝ := C / (2 * d) ^ 8 with hκ
  have hC0 : 0 ≤ C := by simpa using hC 0
  have hκ0 : 0 ≤ κ := by positivity
  have hcomp := InterBox_comp (InterBox_idx_inj_n K e cj)
  set g : Idx → ℝ := fun n => κ * InterBox_F (InterBox_idx K e cj n) with hg
  have hgs : Summable g := hcomp.1.mul_left κ
  set δ : Idx → ℝ := fun n => if n = 0 ∧ ci = cj then V (xi - xj) else 0 with hδ
  have hδs : Summable δ := summable_of_ne_finset_zero (s := {0}) fun n hn => by
    have : n ≠ 0 := by simpa using hn
    simp [hδ, this]
  have hδt : ∑' n, δ n = if ci = cj then V (xi - xj) else 0 := by
    rw [tsum_eq_single 0 fun n hn => by simp [hδ, hn]]
    simp [hδ]
  set f : Idx → ℝ := fun n => V (xi - xj + lat (K * sL) n) with hf
  have hbound : ∀ n, |f n| ≤ |δ n| + g n ∧ f n ≤ δ n + g n := by
    intro n
    by_cases hn : n = 0 ∧ ci = cj
    · obtain ⟨rfl, rfl⟩ := hn
      have h0 : InterBox_idx K e ci 0 = 0 := by
        funext a; simp [InterBox_idx, he]
      have hF : InterBox_F (InterBox_idx K e ci 0) = 0 := by
        rw [h0, InterBox_F, InterBox_nm_zero]; simp
      have : f 0 = V (xi - xj) := by simp [hf, InterBox_lat_zero]
      simp [hδ, hg, this, hF]
    · have hδ0 : δ n = 0 := by simp [hδ, hn]
      have hm : InterBox_idx K e cj n ≠ 0 := fun h0 => hn (by
        obtain ⟨h1, h2⟩ := InterBox_idx_eq_zero (ci := ci) (cj := cj) h0
        exact ⟨h1, h2.symm⟩)
      have hdist := InterBox_dist hd hfit hi hj n hm
      have hr : (1 : ℝ) ≤ (InterBox_nm (InterBox_idx K e cj n) : ℝ) := by
        exact_mod_cast InterBox_nm_pos hm
      have hV := InterBox_term hC hd hr hdist
      have hfg : |f n| ≤ g n := by
        simpa [hf, hg, hκ, InterBox_F] using hV
      rw [hδ0]
      exact ⟨by simpa using hfg, by simpa using (le_abs_self _).trans hfg⟩
  have hfs : Summable f :=
    Summable.of_norm_bounded (hδs.norm.add hgs) fun n => by
      simpa [Real.norm_eq_abs] using (hbound n).1
  calc periodize (K * sL) V (xi - xj) = ∑' n, f n := rfl
    _ ≤ ∑' n, (δ n + g n) := hfs.tsum_le_tsum (fun n => (hbound n).2) (hδs.add hgs)
    _ = (∑' n, δ n) + ∑' n, g n := hδs.tsum_add hgs
    _ = _ := by
      rw [hδt]
      congr 1
      exact hcomp.1.tsum_mul_left κ


/-- At most `M` particles per cell: the sum over particles of the image sums is at most `27 M`. -/
private lemma InterBox_count {K : ℕ} (e : Idx) {N M : ℕ} (cell : Fin N → Fin 3 → Fin K)
    (hM : ∀ m, (Finset.univ.filter (fun j => cell j = m)).card ≤ M) :
    ∑ j, ∑' n : Idx, InterBox_F (InterBox_idx K e (cell j) n) ≤ 27 * M := by
  have hcomp := InterBox_comp (InterBox_idx_inj K e)
  set E : (Fin 3 → Fin K) → ℝ := fun c => ∑' n, InterBox_F (InterBox_idx K e c n) with hE
  have hE0 : ∀ c, 0 ≤ E c := fun c => tsum_nonneg fun n => InterBox_F_nonneg _
  have hprod : ∑ c, E c ≤ 27 := by
    have h1 : ∑' p : (Fin 3 → Fin K) × Idx, InterBox_F (InterBox_idx K e p.1 p.2) =
        ∑' c, E c := hcomp.1.tsum_prod
    have h2 : ∑' c, E c = ∑ c, E c := tsum_fintype E
    rw [← h2, ← h1]
    exact hcomp.2
  calc ∑ j, E (cell j)
      = ∑ c, ∑ j ∈ Finset.univ.filter (fun j => cell j = c), E (cell j) :=
        (Finset.sum_fiberwise _ _ _).symm
    _ = ∑ c, (Finset.univ.filter (fun j => cell j = c)).card • E c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_congr rfl (fun j hj => by rw [(Finset.mem_filter.1 hj).2]), Finset.sum_const]
    _ ≤ ∑ c, M • E c := Finset.sum_le_sum fun c _ => nsmul_le_nsmul_left (hE0 c) (hM c)
    _ = M * ∑ c, E c := by simp [Finset.mul_sum]
    _ ≤ M * 27 := mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = 27 * M := mul_comm _ _

/-- Inter-cube and image interaction: `K³` cells of side `sL` tile the torus of side `K sL`, each
cell `m` holding the cube `sL m + d + (0,ℓ)³` with corridor `d` and at most `M` particles; if
`|V(z)| |z|⁸ ≤ C`, the periodized interaction exceeds the intra-cube interaction by at most
`27 C N M / (2d)⁸` at every such configuration. -/
theorem thermo_interBox {V : R3 → ℝ} {C : ℝ} (hC : ∀ z, |V z| * ‖z‖ ^ 8 ≤ C) {K : ℕ}
    {sL d ℓ : ℝ} (hd : 0 < d) (hfit : ℓ + 2 * d ≤ sL) {N M : ℕ} (cell : Fin N → Fin 3 → Fin K)
    (hM : ∀ m, (Finset.univ.filter (fun j => cell j = m)).card ≤ M) (x : Conf N)
    (hx : ∀ j a, sL * ((cell j a : ℕ) : ℝ) + d < x j a ∧ x j a < sL * ((cell j a : ℕ) : ℝ) + d + ℓ) :
    (∑ i, ∑ j, if i ≠ j then periodize (K * sL) V (x i - x j) else 0) ≤
      (∑ i, ∑ j, if i ≠ j ∧ cell i = cell j then V (x i - x j) else 0) +
        27 * C * N * M / (2 * d) ^ 8 := by
  have hC0 : 0 ≤ C := by simpa using hC 0
  set κ : ℝ := C / (2 * d) ^ 8 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hpair : ∀ i j, (if i ≠ j then periodize (K * sL) V (x i - x j) else 0) ≤
      (if i ≠ j ∧ cell i = cell j then V (x i - x j) else 0) +
        κ * ∑' n : Idx, InterBox_F (InterBox_idx K (fun a => ((cell i a : ℕ) : ℤ)) (cell j) n) := by
    intro i j
    by_cases hij : i = j
    · simp only [hij, ne_eq, not_true_eq_false, ite_false, false_and, zero_add]
      exact mul_nonneg hκ0 (tsum_nonneg fun n => InterBox_F_nonneg _)
    · simp only [hij, ne_eq, not_false_eq_true, true_and, ite_true]
      exact InterBox_pair hC hd hfit (hx i) (hx j)
  calc (∑ i, ∑ j, if i ≠ j then periodize (K * sL) V (x i - x j) else 0)
      ≤ ∑ i, ∑ j, ((if i ≠ j ∧ cell i = cell j then V (x i - x j) else 0) +
          κ * ∑' n : Idx, InterBox_F (InterBox_idx K (fun a => ((cell i a : ℕ) : ℤ)) (cell j) n)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = (∑ i, ∑ j, if i ≠ j ∧ cell i = cell j then V (x i - x j) else 0) +
          κ * ∑ i, ∑ j, ∑' n : Idx,
            InterBox_F (InterBox_idx K (fun a => ((cell i a : ℕ) : ℤ)) (cell j) n) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (∑ i, ∑ j, if i ≠ j ∧ cell i = cell j then V (x i - x j) else 0) +
          κ * ∑ _i : Fin N, (27 * (M : ℝ)) := by
        gcongr with i _
        exact InterBox_count _ cell hM
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hκ]
        ring

/-- Inter-cube and image interaction under the hypotheses of Theorem 2.1 [mainthm], with the
decay constant `decayConst8 V`. -/
theorem thermo_interBox_paper {V : R3 → ℝ} (hV : PotentialHyp V) {K : ℕ} {sL d ℓ : ℝ}
    (hd : 0 < d) (hfit : ℓ + 2 * d ≤ sL) {N M : ℕ} (cell : Fin N → Fin 3 → Fin K)
    (hM : ∀ m, (Finset.univ.filter (fun j => cell j = m)).card ≤ M) (x : Conf N)
    (hx : ∀ j a, sL * ((cell j a : ℕ) : ℝ) + d < x j a ∧ x j a < sL * ((cell j a : ℕ) : ℝ) + d + ℓ) :
    (∑ i, ∑ j, if i ≠ j then periodize (K * sL) V (x i - x j) else 0) ≤
      (∑ i, ∑ j, if i ≠ j ∧ cell i = cell j then V (x i - x j) else 0) +
        27 * decayConst8 V * N * M / (2 * d) ^ 8 := by
  exact thermo_interBox (decayConst8_spec hV) hd hfit cell hM x hx

end LHYUpper
