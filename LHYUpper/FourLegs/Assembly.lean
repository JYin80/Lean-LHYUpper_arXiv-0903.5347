module

public import LHYUpper.Assembly.Section4
public import LHYUpper.Scattering.Solution
public import LHYUpper.FourLegs.Section9
public import LHYUpper.FourLegs.HighLegs
public import LHYUpper.FourLegs.MainTerm

@[expose] public section

/-!
# Lemma 4.6 [lemHAS2] from §9, §10 and Lemma 11.1 (§4, §9–§11)

The sum of the part `H_{A2}`, (4.7), splits over the seven classes of Lemma 9.1
[fourlegslemma1]. The classes `one`, `two`, `twoAdj`, `three` (Lemma 9.2), `fourSpecial`
(Lemma 10.1) and `fourRest` (Lemma 11.1 [113], taken as a hypothesis) have absolute value
tending to `0`; the class `fourMain` is bounded by Lemma 10.2 [101]. Summing the class bounds
gives (4.13) in the shape `Stmt.Lemma4_6`.
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Auxiliary facts -/

/-- `ρ_N ^ a → 0` for `a > 0`. -/
private lemma Asm_tendsto_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := 8 / 17 * a) (by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp, rhoN]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  ring_nf

/-- `0 ≤ ρ_N`. -/
private lemma Asm_rho_nonneg (N : ℕ) : 0 ≤ rhoN N := by unfold rhoN; positivity

/-- The absolute class sums are nonnegative. -/
private lemma Asm_absPart_nonneg (V w : R3 → ℝ) (c : FourLegs.Cls) (kc : ℝ) (N : ℕ) :
    0 ≤ FourLegs.absPart V w c kc N := by
  unfold FourLegs.absPart
  refine div_nonneg (tsum_nonneg fun i => ?_) ?_
  · split_ifs <;> positivity
  · have : 0 ≤ LN N := Real.rpow_nonneg (Asm_rho_nonneg N) _
    have : 0 ≤ rhoN N ^ (5 / 2 : ℝ) := Real.rpow_nonneg (Asm_rho_nonneg N) _
    positivity

/-- A nonnegative sequence bounded by `C ρ_N^a` with `a > 0` tends to `0`. -/
private lemma Asm_tendsto_of_le {f : ℕ → ℝ} {C a : ℝ} (ha : 0 < a) (h0 : ∀ N, 0 ≤ f N)
    (h : ∀ᶠ N in atTop, f N ≤ C * rhoN N ^ a) : Tendsto f atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall h0) h (by simpa using (Asm_tendsto_rpow ha).const_mul C)

/-- If `F kc` tends to `0` for each `kc ≥ 1`, then `lim sup_{k_c} lim sup_N F ≤ 0`. -/
private lemma Asm_limsup2_le_zero {F : ℝ → ℕ → ℝ}
    (h : ∀ kc : ℝ, 1 ≤ kc → Tendsto (F kc) atTop (𝓝 0)) :
    Section4.limsup2 F ≤ ((0 : ℝ) : EReal) := by
  unfold Section4.limsup2
  refine limsup_le_of_le (h := ?_)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with kc hkc
  have : limsup (fun N : ℕ => (F kc N : EReal)) atTop = ((0 : ℝ) : EReal) := by
    apply Tendsto.limsup_eq
    exact (continuous_coe_real_ereal.tendsto _).comp (h kc hkc)
  exact this.le

/-- `lim sup_{k_c} lim sup_N` is monotone under eventual pointwise `≤`. -/
private lemma Asm_limsup2_mono {F G : ℝ → ℕ → ℝ}
    (h : ∀ kc : ℝ, ∀ᶠ N : ℕ in atTop, F kc N ≤ G kc N) :
    Section4.limsup2 F ≤ Section4.limsup2 G := by
  unfold Section4.limsup2
  refine limsup_le_limsup (Eventually.of_forall fun kc => ?_)
  refine limsup_le_limsup ((h kc).mono fun N hN => ?_)
  exact_mod_cast hN

/-- A restriction of the summands of `H_{A2}` is bounded in norm by the interaction summand. -/
private lemma Asm_norm_le (P : Idx × Idx × Idx × Occ → Prop) (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ)
    (i : Idx × Idx × Idx × Occ) :
    ‖(if P i then Decomp.partTerm .A2 L V Ψ i else 0)‖ ≤ ‖intTerm L V Ψ i‖ := by
  unfold Decomp.partTerm
  split_ifs <;> simp

/-- Absolute summability of every restriction of the summands of `H_{A2}`. -/
private lemma Asm_summable_norm (P : Idx × Idx × Idx × Occ → Prop) {L : ℝ} {V : R3 → ℝ}
    {Ψ : Occ → ℂ} (h : Summable fun i => ‖intTerm L V Ψ i‖) :
    Summable fun i : Idx × Idx × Idx × Occ =>
      ‖(if P i then Decomp.partTerm .A2 L V Ψ i else 0)‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => Asm_norm_le P L V Ψ i) h

/-- Summability of every restriction of the summands of `H_{A2}`. -/
private lemma Asm_summable (P : Idx × Idx × Idx × Occ → Prop) {L : ℝ} {V : R3 → ℝ}
    {Ψ : Occ → ℂ} (h : Summable fun i => ‖intTerm L V Ψ i‖) :
    Summable fun i : Idx × Idx × Idx × Occ => (if P i then Decomp.partTerm .A2 L V Ψ i else 0) :=
  Summable.of_norm_bounded h (fun i => Asm_norm_le P L V Ψ i)

/-- Absolute summability of the interaction summands of the trial state, `N ≥ 1`. -/
private lemma Asm_intTerm_summable {V : R3 → ℝ} (hV : PotentialHyp V) (w : R3 → ℝ) (kc : ℝ)
    {N : ℕ} (hN : 1 ≤ N) :
    Summable fun i => ‖intTerm (LN N) V (trialState V w kc N) i‖ :=
  Decomp.intTerm_summable_norm (LN N) V N _
    (FourLegs_ftV_summable hV (Particles_rhoN_LN hN).2.2.2) (Normalization_isNState V w kc hN)

/-- A class sum is at most the absolute class sum. -/
private lemma Asm_part_le_absPart {V : R3 → ℝ} (hV : PotentialHyp V) (w : R3 → ℝ)
    (c : FourLegs.Cls) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    FourLegs.part V w c kc N ≤ FourLegs.absPart V w c kc N := by
  unfold FourLegs.part FourLegs.absPart
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hD : 0 < LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ) := by positivity
  refine div_le_div_of_nonneg_right ?_ hD.le
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_tsum_le_tsum_norm
    (Asm_summable_norm (c.mem (rhoN N) (LN N) kc N) (Asm_intTerm_summable hV w kc hN))).trans_eq
    ?_
  refine tsum_congr fun i => ?_
  split_ifs <;> simp

/-- The class decomposition, summed: `E / (L³ρ^{5/2})` is the sum of the class sums. -/
private lemma Asm_excess_eq {V : R3 → ℝ} (hV : PotentialHyp V) (w : R3 → ℝ) (kc : ℝ) {N : ℕ}
    (hN : 1 ≤ N) :
    Section4.excess (g0 V w) 0
        (∑' i, Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i).re N =
      ∑ c : FourLegs.Cls, FourLegs.part V w c kc N := by
  have hsum : ∑ c : FourLegs.Cls, (∑' i, if c.mem (rhoN N) (LN N) kc N i then
        Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i else 0) =
      ∑' i, Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i := by
    rw [← Summable.tsum_finsetSum (fun c _ => Asm_summable (c.mem (rhoN N) (LN N) kc N)
      (Asm_intTerm_summable hV w kc hN))]
    exact tsum_congr fun i => (FourLegs_partTerm_eq_sum V w kc hN i).symm
  have hre : ∑ c : FourLegs.Cls, (∑' i, if c.mem (rhoN N) (LN N) kc N i then
        Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i else 0).re =
      (∑' i, Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i).re := by
    rw [← Complex.re_sum, hsum]
  unfold Section4.excess FourLegs.part
  rw [← Finset.sum_div, hre, zero_mul, sub_zero, div_div]

/-! ### The assembly -/

/-- Lemma 4.6 [lemHAS2], (4.13), from §9, §10 and Lemma 11.1 [113]. -/
theorem Lemma4_6_of_Lemma11_1 {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) (h : Stmt.Lemma11_1 V w) : Stmt.Lemma4_6 V w := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Lemma9_2_case1 hV hw
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := Lemma9_2_case2 hV hw
  obtain ⟨C₃, hC₃, N₃, h₃⟩ := Lemma9_2_case3 hV hw
  obtain ⟨C₄, hC₄, N₄, h₄⟩ := Lemma10_1 hV hw
  -- every class except `fourMain` has absolute sum tending to `0`
  have hT : ∀ c : FourLegs.Cls, c ≠ .fourMain → ∀ kc : ℝ, 1 ≤ kc →
      Tendsto (fun N => FourLegs.absPart V w c kc N) atTop (𝓝 0) := by
    intro c hc kc hkc
    cases c
    · exact Asm_tendsto_of_le (C := C₁) (a := 2 / 5) (by norm_num)
        (fun N => Asm_absPart_nonneg V w _ kc N)
        ((eventually_ge_atTop N₁).mono fun N hN => h₁ N hN kc)
    · exact Asm_tendsto_of_le (C := C₂ * kc ^ 3) (a := 1 / 20) (by norm_num)
        (fun N => Asm_absPart_nonneg V w _ kc N)
        ((eventually_ge_atTop N₂).mono fun N hN => (h₂ N hN kc hkc).1)
    · exact Asm_tendsto_of_le (C := C₂ * kc ^ 3) (a := 1 / 20) (by norm_num)
        (fun N => Asm_absPart_nonneg V w _ kc N)
        ((eventually_ge_atTop N₂).mono fun N hN => (h₂ N hN kc hkc).2)
    · exact Asm_tendsto_of_le (C := C₃ * kc ^ 6) (a := 1 / 50) (by norm_num)
        (fun N => Asm_absPart_nonneg V w _ kc N)
        ((eventually_ge_atTop N₃).mono fun N hN => h₃ N hN kc hkc)
    · exact Asm_tendsto_of_le (C := C₄ * kc ^ 6) (a := 1) one_pos
        (fun N => Asm_absPart_nonneg V w _ kc N)
        ((eventually_ge_atTop N₄).mono fun N hN => by
          rw [Real.rpow_one]; exact h₄ N hN kc hkc)
    · exact absurd rfl hc
    · exact Asm_tendsto_of_le (C := 1) (a := 1 / 2) (by norm_num)
        (fun N => Asm_absPart_nonneg V w _ kc N)
        ((h kc).mono fun N hN => by rw [one_mul]; exact hN)
  -- the class bounds
  let X : FourLegs.Cls → ℝ → ℕ → ℝ := fun c kc N =>
    if c = .fourMain then FourLegs.part V w .fourMain kc N else FourLegs.absPart V w c kc N
  let R : FourLegs.Cls → ℝ := fun c =>
    if c = .fourMain then 4 * normVw2 V w * Section4.G V w / 3 else 0
  have hX : ∀ c ∈ (Finset.univ : Finset FourLegs.Cls), Section4.limsup2 (X c) ≤ (R c : EReal) := by
    intro c _
    by_cases hc : c = .fourMain
    · subst hc
      simpa [X, R] using Lemma10_2 hV hw
    · have h0 : R c = 0 := by simp [R, hc]
      rw [h0]
      refine Asm_limsup2_le_zero (F := X c) fun kc hkc => ?_
      have : X c kc = fun N => FourLegs.absPart V w c kc N := by
        funext N; simp [X, hc]
      rw [this]
      exact hT c hc kc hkc
  have hmain := Section4.limsup2_sum_add_le Finset.univ X R (fun _ => 0) 0 hX tendsto_const_nhds
  have hR : (∑ c : FourLegs.Cls, R c) + 0 = 4 * normVw2 V w * Section4.G V w / 3 := by
    simp [R]
  rw [hR] at hmain
  -- the real sums
  unfold Stmt.Lemma4_6 Section4.PartBound
  refine ⟨fun kc N => (∑' i, Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i).re,
    fun kc => ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hs : Summable (Decomp.partTerm .A2 (LN N) V (trialState V w kc N)) :=
      (Asm_summable (fun _ => True) (Asm_intTerm_summable hV w kc hN)).congr (fun i => by simp)
    have him := Decomp.im_eq_zero_of_hasSum .A2 (LN N) V _ _ hs.hasSum
    have hre : (((∑' i, Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i).re : ℝ) : ℂ) =
        ∑' i, Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i :=
      Complex.ext rfl (by simp [him])
    rw [hre]
    exact hs.hasSum
  · refine (Asm_limsup2_mono (G := fun kc N => (∑ c, X c kc N) + 0) fun kc => ?_).trans hmain
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [Asm_excess_eq hV w kc hN, add_zero]
    refine Finset.sum_le_sum fun c _ => ?_
    by_cases hc : c = .fourMain
    · subst hc; simp [X]
    · simpa [X, hc] using Asm_part_le_absPart hV w c kc hN

end LHYUpper
