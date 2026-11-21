module

public import LHYUpper.Particles.Ratios
public import LHYUpper.Riemann.Cells

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Elementary facts on nonnegative series and on the parameters -/

/-- A restriction of a nonnegative summable family is summable. -/
private lemma UpperL_summable_ite {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (p : Occ → Prop) [DecidablePred p] : Summable fun α => if p α then ψ α else 0 :=
  Summable.of_nonneg_of_le (fun α => by split_ifs <;> simp [hψ α])
    (fun α => by split_ifs <;> simp [hψ α]) hs

/-- A restricted sum is at most the full sum. -/
private lemma UpperL_tsum_le_one {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (h1 : ∑' α, ψ α = 1) (P : Occ → Prop) [DecidablePred P] :
    (∑' α, if P α then ψ α else 0) ≤ 1 := by
  rw [← h1]
  exact (UpperL_summable_ite hs hψ P).tsum_le_tsum
    (fun α => by split_ifs <;> simp [hψ α]) hs

/-- Monotonicity of restricted sums in the restricting event. -/
private lemma UpperL_tsum_mono {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    {P Q : Occ → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ α, P α → Q α) :
    (∑' α, if P α then ψ α else 0) ≤ ∑' α, if Q α then ψ α else 0 :=
  (UpperL_summable_ite hs hψ P).tsum_le_tsum
    (fun α => by
      by_cases hp : P α
      · simp [hp, h α hp]
      · simp only [hp, ite_false]
        split_ifs <;> simp [hψ α])
    (UpperL_summable_ite hs hψ Q)

/-- Equivalent events give equal restricted sums. -/
private lemma UpperL_tsum_iff {ψ : Occ → ℝ} {p q : Occ → Prop} {dp : DecidablePred p}
    {dq : DecidablePred q} (h : ∀ α, p α ↔ q α) :
    (∑' α, @ite _ (p α) (dp α) (ψ α) 0) = ∑' α, @ite _ (q α) (dq α) (ψ α) 0 :=
  tsum_congr fun α => @if_congr _ _ _ (dp α) (dq α) _ _ _ _ (h α) rfl rfl

/-- The sum over the fibres of a counting function `k` bounded by `M` on the event `P`:
`Σ_α [P α] c(k α) ψ(α) = Σ_{m ≤ M} c(m) Σ_α [P α, k α = m] ψ(α)`. -/
private lemma UpperL_fibre {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (P : Occ → Prop) [DecidablePred P] (k : Occ → ℕ) (M : ℕ) (hk : ∀ α, P α → k α ≤ M)
    (c : ℕ → ℝ) :
    (∑' α, if P α then c (k α) * ψ α else 0) =
      ∑ m ∈ Finset.range (M + 1), c m * ∑' α, if P α ∧ k α = m then ψ α else 0 := by
  have hsum : ∀ m, Summable fun α => if P α ∧ k α = m then c m * ψ α else 0 := by
    intro m
    refine ((UpperL_summable_ite hs hψ (fun α => P α ∧ k α = m)).mul_left (c m)).congr
      (fun α => ?_)
    split_ifs <;> simp
  have h1 : ∀ m, c m * (∑' α, if P α ∧ k α = m then ψ α else 0) =
      ∑' α, if P α ∧ k α = m then c m * ψ α else 0 := by
    intro m
    rw [← tsum_mul_left]
    exact tsum_congr fun α => by split_ifs <;> simp
  simp_rw [h1]
  rw [← Summable.tsum_finsetSum (fun m _ => hsum m)]
  refine tsum_congr fun α => ?_
  by_cases hP : P α
  · rw [ite_eq_left hP, Finset.sum_eq_single (k α)]
    · simp [hP]
    · intro m _ hm
      simp [Ne.symm hm]
    · intro h
      exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (hk α hP))) h
  · simp [hP]

/-- `ρ_N ≤ 1/8` for `N ≥ 84`. -/
private lemma UpperL_rho_le {N : ℕ} (hN : 84 ≤ N) : rhoN N ≤ 1 / 8 := by
  have hN' : (84 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hx0 : 0 < (N : ℝ) ^ (8 / 17 : ℝ) := Real.rpow_pos_of_pos hNpos _
  have hx17 : ((N : ℝ) ^ (8 / 17 : ℝ)) ^ 17 = (N : ℝ) ^ 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_natCast]
    norm_num
  have h8 : (8 : ℝ) ≤ (N : ℝ) ^ (8 / 17 : ℝ) := by
    by_contra h
    push Not at h
    have h1 := pow_lt_pow_left₀ h hx0.le (by norm_num : (17 : ℕ) ≠ 0)
    rw [hx17] at h1
    have h84 : (84 : ℝ) ^ 8 ≤ (N : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) hN' 8
    norm_num at h1 h84
    linarith
  rw [rhoN, Real.rpow_neg hNpos.le, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h8

/-- For `N ≥ 84`, `2π ≤ L_N ε`. -/
private lemma UpperL_two_pi_le {N : ℕ} (hN : 84 ≤ N) : 2 * π ≤ LN N * epsP (rhoN N) := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN (by omega : 1 ≤ N)
  have h8 := UpperL_rho_le hN
  have e : LN N * epsP (rhoN N) = rhoN N ^ (-(622 / 600 : ℝ)) := by
    rw [LN, epsP, ← Real.rpow_add hρ]
    norm_num
  have h1 : rhoN N ^ (-1 : ℝ) ≤ rhoN N ^ (-(622 / 600 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  rw [Real.rpow_neg_one] at h1
  have h2 : (8 : ℝ) ≤ (rhoN N)⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hρ]
    simpa using h8
  have hπ := pi_lt_d2
  rw [e]
  linarith

/-- For `N ≥ 84` and `u ∈ P_L`, `|p_u| ≤ ε/2`. -/
private lemma UpperL_mom_le {N : ℕ} (hN : 84 ≤ N) {u : Idx} (hu : inPL (rhoN N) (LN N) u) :
    ‖mom (LN N) u‖ ≤ epsP (rhoN N) / 2 := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN (by omega : 1 ≤ N)
  have h8 := UpperL_rho_le hN
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hcube : (rhoN N ^ (1 / 3 : ℝ)) ^ 3 = rhoN N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have ht0 : 0 < rhoN N ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hρ _
  have ht : rhoN N ^ (1 / 3 : ℝ) ≤ 1 / 2 := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)
    rw [hcube] at this
    norm_num at this
    linarith
  have h49 : rhoN N ^ (49 / 100 : ℝ) ≤ 1 / 2 :=
    (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num : (1 / 3 : ℝ) ≤ 49 / 100)).trans ht
  have h1 : rhoN N ^ (1 / 2 : ℝ) = epsP (rhoN N) ^ 2 * rhoN N ^ (49 / 100 : ℝ) := by
    rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ]
    norm_num
  have h2 := hu.2
  rw [h1] at h2
  refine h2.trans ?_
  calc (epsP (rhoN N))⁻¹ * (epsP (rhoN N) ^ 2 * rhoN N ^ (49 / 100 : ℝ))
      ≤ (epsP (rhoN N))⁻¹ * (epsP (rhoN N) ^ 2 * (1 / 2)) := by gcongr
    _ = epsP (rhoN N) / 2 := by field_simp

/-- `⌈m_c⌉ ≤ 2 m_c` for `0 < ρ ≤ 1`. -/
private lemma UpperL_ceil_le {ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) :
    (⌈mc ρ⌉₊ : ℝ) ≤ 2 * mc ρ := by
  have hm : 1 ≤ mc ρ := by
    unfold mc
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ h1 (by norm_num)
  have := Nat.ceil_lt_add_one (by linarith : 0 ≤ mc ρ)
  linarith

/-- `|Ψ|²` vanishes off `M`. -/
private lemma UpperL_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  rw [FIdentities_trialState, ite_eq_right hc, norm_zero]
  norm_num

/-- A single occupation number is at most the particle number. -/
private lemma UpperL_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]; exact Nat.zero_le _

/-- `α ↦ α(u) |Ψ(α)|²` is summable. -/
private lemma UpperL_summable_occ (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    Summable fun α : Occ => (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by
  have hΨ := Normalization_isNState V w kc hN
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_)
    (hΨ.1.summable.mul_left (N : ℝ))
  by_cases hz : trialState V w kc N α = 0
  · simp [hz]
  · have hnum := hΨ.2 α hz
    have h1 : (α u : ℝ) ≤ N := by
      rw [← hnum]
      exact_mod_cast UpperL_occ_le_num α u
    exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-! ### The lattice sum `Σ_p |λ_p λ_{u-p}|` -/

/-- `p_{u-p} = p_u - p_p`. -/
private lemma UpperL_mom_sub (L : ℝ) (u p : Idx) : mom L (u - p) = mom L u - mom L p := by
  ext i
  simp [mom]
  ring

/-- For `u ∈ P_L`, `L_N^{-3} Σ_p [p, u-p ∈ P_{H,c}] |λ_p λ_{u-p}| ≤ K/ε` with `K` independent of
`N ≥ 84`, `k_c` and `u`; the decay `|λ_n| ≤ ‖g‖₁ |p_n|^{-2}` is used off `P_L`, and
`|p_{u-p}| ≥ |p_p|/2` since `|p_u| ≤ ε/2 < |p_p|/2`. -/
private lemma UpperL_T_bound (V w : R3 → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 84 ≤ N → ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      (∑' p : Idx, if inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (u - p) then
          |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (u - p)| else 0) ≤
        LN N ^ 3 * (K / epsP (rhoN N)) := by
  obtain ⟨K₀, hK₀, hK⟩ := sum_norm_rpow_gt (s := 4) (by norm_num)
  set G : ℝ := ∫ x, |gfun V w x| with hG
  have hG0 : 0 ≤ G := integral_nonneg fun x => abs_nonneg _
  refine ⟨4 * G ^ 2 * K₀, by positivity, fun N hN kc u hu => ?_⟩
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN (by omega : 1 ≤ N)
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  obtain ⟨hsum, hle⟩ := hK (LN N) (epsP (rhoN N)) hε (UpperL_two_pi_le hN)
  set F : Idx → ℝ := fun n => if epsP (rhoN N) < ‖mom (LN N) n‖ then
    ‖mom (LN N) n‖ ^ (-(4 : ℝ)) else 0 with hF
  have hF0 : ∀ n, 0 ≤ F n := fun n => by
    simp only [hF]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hpt : ∀ p : Idx, (if inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (u - p) then
      |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (u - p)| else 0) ≤ 4 * G ^ 2 * F p := by
    intro p
    by_cases hc : inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (u - p)
    · rw [ite_eq_left hc]
      obtain ⟨⟨hp1, -⟩, ⟨hp2, -⟩⟩ := hc
      have hpH : epsP (rhoN N) < ‖mom (LN N) p‖ := hp1
      have hqH : epsP (rhoN N) < ‖mom (LN N) (u - p)‖ := hp2
      have hF1 : F p = ‖mom (LN N) p‖ ^ (-(4 : ℝ)) := by simp only [hF, ite_eq_left hpH]
      have hl1 := Particles_lam_abs_le V w (rhoN N) (LN N) p
        (fun h => Regions_PL_PH hρ h hp1)
      have hl2 := Particles_lam_abs_le V w (rhoN N) (LN N) (u - p)
        (fun h => Regions_PL_PH hρ h hp2)
      set a := ‖mom (LN N) p‖ with ha
      set b := ‖mom (LN N) (u - p)‖ with hb
      have ha0 : 0 < a := hε.trans hpH
      have hb0 : 0 < b := hε.trans hqH
      have hup := UpperL_mom_le hN hu
      have hab : a / 2 ≤ b := by
        have e : mom (LN N) p = mom (LN N) u - mom (LN N) (u - p) := by
          rw [UpperL_mom_sub, sub_sub_cancel]
        have h1 : a ≤ ‖mom (LN N) u‖ + b := by
          rw [ha, e]
          exact norm_sub_le _ _
        linarith
      have hab2 : a ^ 2 / 4 ≤ b ^ 2 := by
        have := pow_le_pow_left₀ (by positivity : 0 ≤ a / 2) hab 2
        nlinarith
      rw [abs_mul, hF1]
      calc |lam V w (rhoN N) (LN N) p| * |lam V w (rhoN N) (LN N) (u - p)|
          ≤ (G / a ^ 2) * (G / b ^ 2) :=
            mul_le_mul hl1 hl2 (abs_nonneg _) (by positivity)
        _ = G ^ 2 / (a ^ 2 * b ^ 2) := by field_simp
        _ ≤ G ^ 2 / (a ^ 2 * (a ^ 2 / 4)) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hab2 (by positivity))
        _ = 4 * G ^ 2 * a ^ (-(4 : ℝ)) := by
            rw [show (-(4 : ℝ)) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg ha0.le,
              Real.rpow_natCast]
            field_simp
    · rw [ite_eq_right hc]
      exact mul_nonneg (by positivity) (hF0 p)
  have hTs : Summable fun p : Idx => if inPHc (rhoN N) (LN N) kc p ∧
      inPHc (rhoN N) (LN N) kc (u - p) then
        |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (u - p)| else 0 :=
    Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity) hpt
      (hsum.mul_left (4 * G ^ 2))
  have hsum' : (∑' p : Idx, F p) ≤ LN N ^ 3 * (K₀ * epsP (rhoN N) ^ (3 - 4 : ℝ)) := by
    have := (inv_mul_le_iff₀ (by positivity : 0 < LN N ^ 3)).1 hle
    simpa only [hF] using this
  calc (∑' p : Idx, if inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (u - p) then
          |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (u - p)| else 0)
      ≤ ∑' p : Idx, 4 * G ^ 2 * F p := hTs.tsum_le_tsum hpt (hsum.mul_left (4 * G ^ 2))
    _ = 4 * G ^ 2 * ∑' p : Idx, F p := tsum_mul_left
    _ ≤ 4 * G ^ 2 * (LN N ^ 3 * (K₀ * epsP (rhoN N) ^ (3 - 4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum' (by positivity)
    _ = LN N ^ 3 * (4 * G ^ 2 * K₀ / epsP (rhoN N)) := by
        rw [show (3 : ℝ) - 4 = -1 by norm_num, Real.rpow_neg_one]
        field_simp

/-- The soft creation bound (5.22) [ubpsiuroughPL1] for an admissible event, with a constant
independent of `N ≥ 84`, `k_c`, `u ∈ P_L`, `m` and `E`. -/
private lemma UpperL_soft (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 84 ≤ N → ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      ∀ E : Occ → Prop,
      (∀ α β : Occ, (∀ n, n ≠ 0 → n ≠ u → n ≠ -u → ¬ inPH (rhoN N) (LN N) n → α n = β n) →
        (E α ↔ E β)) → ∀ m : ℕ,
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m ∧ E α then
          ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C * rhoN N * m / epsP (rhoN N) *
          (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m ∧ E β then
            ‖trialState V w kc N β‖ ^ 2 else 0) := by
  obtain ⟨K, hK, hT⟩ := UpperL_T_bound V w
  refine ⟨8 * K, by positivity, fun N hN kc u hu E hE m => ?_⟩
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN (by omega : 1 ≤ N)
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have h1 := Particles_softCreation V w kc (by omega : 1 ≤ N) hu E hE m
  have hS0 : 0 ≤ ∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m ∧ E β then
      ‖trialState V w kc N β‖ ^ 2 else 0 := tsum_nonneg fun β => by split_ifs <;> positivity
  refine h1.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ hS0
  calc 8 * rhoN N * m / LN N ^ 3 * _
      ≤ 8 * rhoN N * m / LN N ^ 3 * (LN N ^ 3 * (K / epsP (rhoN N))) :=
        mul_le_mul_of_nonneg_left (hT N hN kc u hu) (by positivity)
    _ = 8 * K * rhoN N * m / epsP (rhoN N) := by field_simp

/-! ### Sums over the occupation of `u` -/

/-- If the fibres satisfy `A_m ≤ c m S_m` for `m ≤ M`, then the weighted and the plain sums
satisfy the same bound with `m` replaced by `M`. -/
private lemma UpperL_sum_bounds {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (Pa Ps : Occ → Prop) [DecidablePred Pa] [DecidablePred Ps] (ka ks : Occ → ℕ) (M : ℕ)
    (hka : ∀ α, Pa α → ka α ≤ M)
    (hks : ∀ α, Ps α → ks α ≤ M) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ m : ℕ, (∑' α, if Pa α ∧ ka α = m then ψ α else 0) ≤
      c * m * ∑' β, if Ps β ∧ ks β = m then ψ β else 0) :
    ((∑' α, if Pa α then (ka α : ℝ) * ψ α else 0) ≤
        c * M * (∑' β, if Ps β then (ks β : ℝ) * ψ β else 0)) ∧
    ((∑' α, if Pa α then ψ α else 0) ≤ c * M * (∑' β, if Ps β then ψ β else 0)) := by
  have hS0 : ∀ m, 0 ≤ ∑' β, if Ps β ∧ ks β = m then ψ β else 0 :=
    fun m => tsum_nonneg fun β => by split_ifs <;> simp [hψ β]
  have hfa := UpperL_fibre hs hψ Pa ka M hka (fun m => (m : ℝ))
  have hfs := UpperL_fibre hs hψ Ps ks M hks (fun m => (m : ℝ))
  have hfa1 := UpperL_fibre hs hψ Pa ka M hka (fun _ => 1)
  have hfs1 := UpperL_fibre hs hψ Ps ks M hks (fun _ => 1)
  simp only [one_mul] at hfa1 hfs1
  constructor
  · rw [hfa, hfs, Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have h1 := mul_le_mul_of_nonneg_left (h m) (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have h2 := mul_nonneg (mul_nonneg (mul_nonneg hc (Nat.cast_nonneg m : (0 : ℝ) ≤ m))
      (hS0 m)) (sub_nonneg.2 hmM)
    nlinarith
  · rw [hfa1, hfs1, Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have h2 := mul_nonneg (mul_nonneg hc (hS0 m)) (sub_nonneg.2 hmM)
    nlinarith [h m]

/-- A nonnegative sequence with `s_{m+1} ≤ x s_m` and `Σ_{m ≤ M} s_m ≤ 1` has
`Σ_{m ≤ M} m s_m ≤ x/(1 − x)` for `0 ≤ x < 1`. -/
private lemma UpperL_W_bound {s : ℕ → ℝ} {x : ℝ} {M : ℕ} (hs0 : ∀ m, 0 ≤ s m) (hx0 : 0 ≤ x)
    (hx1 : x < 1) (hstep : ∀ m, s (m + 1) ≤ x * s m)
    (hZ : ∑ m ∈ Finset.range (M + 1), s m ≤ 1) :
    ∑ m ∈ Finset.range (M + 1), (m : ℝ) * s m ≤ x / (1 - x) := by
  have h1 : ∑ m ∈ Finset.range (M + 1), (m : ℝ) * s m =
      ∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) * s (i + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have h2 : ∑ i ∈ Finset.range M, ((i + 1 : ℕ) : ℝ) * s (i + 1) ≤
      ∑ i ∈ Finset.range M, x * (((i + 1 : ℕ) : ℝ) * s i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have hi : (0 : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left (hstep i) hi]
  have h3 : ∑ i ∈ Finset.range M, x * (((i + 1 : ℕ) : ℝ) * s i) ≤
      x * ((∑ m ∈ Finset.range (M + 1), (m : ℝ) * s m) + ∑ m ∈ Finset.range (M + 1), s m) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hx0
    have e : (∑ m ∈ Finset.range (M + 1), (m : ℝ) * s m) + ∑ m ∈ Finset.range (M + 1), s m =
        ∑ i ∈ Finset.range (M + 1), ((i + 1 : ℕ) : ℝ) * s i := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring
    rw [e, Finset.sum_range_succ]
    have : 0 ≤ ((M + 1 : ℕ) : ℝ) * s M := mul_nonneg (Nat.cast_nonneg _) (hs0 M)
    linarith
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hZ hx0]

/-! ### (5.22), (5.23), (5.24) with explicit thresholds -/

/-- (5.22) [ubpsiuroughPL1] for `N ≥ 84`. -/
private lemma UpperL_core22 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 84 ≤ N → ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      ∀ m : ℕ,
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m then
          ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C * rhoN N * m / epsP (rhoN N) *
          (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m then
            ‖trialState V w kc N β‖ ^ 2 else 0) := by
  obtain ⟨C, hC, h⟩ := UpperL_soft V w
  refine ⟨C, hC, fun N hN kc u hu m => ?_⟩
  have := h N hN kc u hu (fun _ => True) (fun _ _ _ => Iff.rfl) m
  simpa only [and_true] using this

/-- (5.22) [ubpsiuroughPL1] weighted by `α*(u)` and summed over `m`, for `N ≥ 84`. -/
private lemma UpperL_core22w (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 84 ≤ N → ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
          (alphaStar α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C * rhoN N * mc (rhoN N) / epsP (rhoN N) *
          (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β then
            (β u : ℝ) * ‖trialState V w kc N β‖ ^ 2 else 0) := by
  obtain ⟨C, hC, h⟩ := UpperL_core22 V w
  refine ⟨2 * C, by positivity, fun N hN kc u hu => ?_⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hmc : 0 < mc (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN1).1.summable
  have hψ : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun α => by positivity
  have key := (UpperL_sum_bounds hs hψ (InMuA (rhoN N) (LN N) kc N u)
    (InMuS (rhoN N) (LN N) kc N u) (fun α => alphaStar α u) (fun β => β u) ⌈mc (rhoN N)⌉₊
    (fun α hα => MStar_PL_ceil hρ hα.1 hu)
    (fun β hβ => (le_max_left (β u) (β (-u))).trans (MStar_PL_ceil hρ hβ.1 hu))
    (c := C * rhoN N / epsP (rhoN N)) (by positivity)
    (fun m => (h N hN kc u hu m).trans_eq (by ring))).1
  have hW : 0 ≤ ∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β then
      (β u : ℝ) * ‖trialState V w kc N β‖ ^ 2 else 0 :=
    tsum_nonneg fun β => by split_ifs <;> positivity
  have hceil := UpperL_ceil_le hρ hρ1
  refine key.trans ?_
  calc C * rhoN N / epsP (rhoN N) * (⌈mc (rhoN N)⌉₊ : ℝ) * _
      ≤ C * rhoN N / epsP (rhoN N) * (2 * mc (rhoN N)) * _ := by gcongr
    _ = 2 * C * rhoN N * mc (rhoN N) / epsP (rhoN N) * _ := by ring

/-- (5.23) [boundMa] for `N ≥ 84`. -/
private lemma UpperL_core23 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 84 ≤ N → ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
          ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C * rhoN N * mc (rhoN N) / epsP (rhoN N) := by
  obtain ⟨C, hC, h⟩ := UpperL_core22 V w
  refine ⟨2 * C, by positivity, fun N hN kc u hu => ?_⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hmc : 0 < mc (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hΨ := Normalization_isNState V w kc hN1
  have hs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun α => by positivity
  have key := (UpperL_sum_bounds hs hψ (InMuA (rhoN N) (LN N) kc N u)
    (InMuS (rhoN N) (LN N) kc N u) (fun α => alphaStar α u) (fun β => β u) ⌈mc (rhoN N)⌉₊
    (fun α hα => MStar_PL_ceil hρ hα.1 hu)
    (fun β hβ => (le_max_left (β u) (β (-u))).trans (MStar_PL_ceil hρ hβ.1 hu))
    (c := C * rhoN N / epsP (rhoN N)) (by positivity)
    (fun m => (h N hN kc u hu m).trans_eq (by ring))).2
  have hZ := UpperL_tsum_le_one hs hψ hΨ.1.tsum_eq (InMuS (rhoN N) (LN N) kc N u)
  have hceil := UpperL_ceil_le hρ hρ1
  refine key.trans ?_
  calc C * rhoN N / epsP (rhoN N) * (⌈mc (rhoN N)⌉₊ : ℝ) * _
      ≤ C * rhoN N / epsP (rhoN N) * (2 * mc (rhoN N)) * 1 := by gcongr
    _ = 2 * C * rhoN N * mc (rhoN N) / epsP (rhoN N) := by ring

/-- (5.24) [boundMaMa], for `N ≥ 84`. -/
private lemma UpperL_core24 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 84 ≤ N → ∀ kc : ℝ, ∀ u v : Idx,
      inPL (rhoN N) (LN N) u → inPL (rhoN N) (LN N) v → u ≠ v → u + v ≠ 0 →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ InMuA (rhoN N) (LN N) kc N v α then
          ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        (C * rhoN N * mc (rhoN N) / epsP (rhoN N)) ^ 2 := by
  obtain ⟨C₁, hC₁, hsoft⟩ := UpperL_soft V w
  obtain ⟨C₃, hC₃, h23⟩ := UpperL_core23 V w
  refine ⟨max (2 * C₁) C₃, le_max_of_le_right hC₃, fun N hN kc u v hu hv huv huv' => ?_⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hmc : 0 < mc (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hΨ := Normalization_isNState V w kc hN1
  have hs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun α => by positivity
  have hv0 : v ≠ 0 := Regions_PL_ne_zero hρ hv
  have hvn : inPL (rhoN N) (LN N) (-v) := Regions_PL_neg.2 hv
  -- the event `α(v) ≠ α(-v)`, which depends only on occupations outside `{0, ±u} ∪ P_H`
  obtain ⟨E, hEdef⟩ : ∃ E : Occ → Prop, E = fun α => α v ≠ α (-v) := ⟨_, rfl⟩
  have hE : ∀ α β : Occ,
      (∀ n, n ≠ 0 → n ≠ u → n ≠ -u → ¬ inPH (rhoN N) (LN N) n → α n = β n) →
      (E α ↔ E β) := by
    intro α β h
    have h1 : α v = β v := h v hv0 (fun e => huv e.symm) (fun e => huv' (by rw [e]; simp))
      (Regions_PL_PH hρ hv)
    have h2 : α (-v) = β (-v) := h (-v) (neg_ne_zero.2 hv0)
      (fun e => huv' (by rw [← e]; simp)) (fun e => huv (neg_injective e).symm)
      (Regions_PL_PH hρ hvn)
    rw [hEdef]
    simp only [h1, h2]
  have hc : 0 ≤ C₁ * rhoN N / epsP (rhoN N) := by positivity
  have key := (UpperL_sum_bounds hs hψ
    (fun α => InMuA (rhoN N) (LN N) kc N u α ∧ E α)
    (fun β => InMuS (rhoN N) (LN N) kc N u β ∧ E β)
    (fun α => alphaStar α u) (fun β => β u) ⌈mc (rhoN N)⌉₊
    (fun α hα => MStar_PL_ceil hρ hα.1.1 hu)
    (fun β hβ => (le_max_left (β u) (β (-u))).trans (MStar_PL_ceil hρ hβ.1.1 hu))
    hc (fun m => ?_)).2
  · have hmono : (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ E β then
        ‖trialState V w kc N β‖ ^ 2 else 0) ≤
        ∑' β : Occ, if InMuA (rhoN N) (LN N) kc N v β then
          ‖trialState V w kc N β‖ ^ 2 else 0 :=
      UpperL_tsum_mono hs hψ (fun β hβ => ⟨hβ.1.1, by rw [hEdef] at hβ; exact hβ.2⟩)
    have hZ : (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ E β then
        ‖trialState V w kc N β‖ ^ 2 else 0) ≤ C₃ * rhoN N * mc (rhoN N) / epsP (rhoN N) :=
      hmono.trans (h23 N hN kc v hv)
    have hZ0 : 0 ≤ ∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ E β then
        ‖trialState V w kc N β‖ ^ 2 else 0 :=
      tsum_nonneg fun β => by split_ifs <;> positivity
    have hr : 0 ≤ rhoN N * mc (rhoN N) / epsP (rhoN N) := by positivity
    have hceil := UpperL_ceil_le hρ hρ1
    have hcM : C₁ * rhoN N / epsP (rhoN N) * (⌈mc (rhoN N)⌉₊ : ℝ) ≤
        2 * C₁ * (rhoN N * mc (rhoN N) / epsP (rhoN N)) :=
      calc C₁ * rhoN N / epsP (rhoN N) * (⌈mc (rhoN N)⌉₊ : ℝ)
          ≤ C₁ * rhoN N / epsP (rhoN N) * (2 * mc (rhoN N)) := by gcongr
        _ = 2 * C₁ * (rhoN N * mc (rhoN N) / epsP (rhoN N)) := by ring
    have e0 : (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ InMuA (rhoN N) (LN N) kc N v α
        then ‖trialState V w kc N α‖ ^ 2 else 0) =
        ∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ E α then
          ‖trialState V w kc N α‖ ^ 2 else 0 :=
      UpperL_tsum_iff (fun α => by simp only [hEdef, InMuA]; tauto)
    rw [e0]
    calc _ ≤ C₁ * rhoN N / epsP (rhoN N) * (⌈mc (rhoN N)⌉₊ : ℝ) * _ := key
      _ ≤ (2 * C₁ * (rhoN N * mc (rhoN N) / epsP (rhoN N))) *
            (C₃ * (rhoN N * mc (rhoN N) / epsP (rhoN N))) :=
          mul_le_mul hcM (hZ.trans_eq (by ring)) hZ0 (by positivity)
      _ ≤ (max (2 * C₁) C₃ * (rhoN N * mc (rhoN N) / epsP (rhoN N))) *
            (max (2 * C₁) C₃ * (rhoN N * mc (rhoN N) / epsP (rhoN N))) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (le_max_left _ _) hr)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hr) (by positivity) (by positivity)
      _ = (max (2 * C₁) C₃ * rhoN N * mc (rhoN N) / epsP (rhoN N)) ^ 2 := by ring
  · have h := hsoft N hN kc u hu E hE m
    have e1 : (∑' α : Occ, if (InMuA (rhoN N) (LN N) kc N u α ∧ E α) ∧
        alphaStar α u = m then ‖trialState V w kc N α‖ ^ 2 else 0) =
        ∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m ∧ E α then
          ‖trialState V w kc N α‖ ^ 2 else 0 :=
      UpperL_tsum_iff (fun α => by tauto)
    have e2 : (∑' β : Occ, if (InMuS (rhoN N) (LN N) kc N u β ∧ E β) ∧ β u = m then
        ‖trialState V w kc N β‖ ^ 2 else 0) =
        ∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m ∧ E β then
          ‖trialState V w kc N β‖ ^ 2 else 0 :=
      UpperL_tsum_iff (fun β => by tauto)
    rw [e1, e2]
    refine h.trans_eq ?_
    ring

/-- (5.14) [ubpsiuroughPL] of Lemma 5.4 [lem1], for `N ≥ 84`. -/
private lemma UpperL_core54 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 84 ≤ N → ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      Expect.Q (trialState V w kc N) [u] ≤
        (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) *
          (1 + C * rhoN N * mc (rhoN N) / epsP (rhoN N)) := by
  obtain ⟨C, hC, h22w⟩ := UpperL_core22w V w
  refine ⟨C, hC, fun N hN kc u hu => ?_⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hmc : 0 < mc (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hΨ := Normalization_isNState V w kc hN1
  have hs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun α => by positivity
  obtain ⟨hneg, hge⟩ := Particles_rho_lam_PL hg hρ hρ1 hu
  have hpos : 0 < epsP (rhoN N) / (1 + Real.sqrt (g0 V w)) := by positivity
  have hx1 : (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 < 1 := by nlinarith
  have hx0 : 0 ≤ (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 := sq_nonneg _
  have hs1 : Summable fun α : Occ => if InMuS (rhoN N) (LN N) kc N u α then
      (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => by split_ifs <;> first | exact le_rfl | positivity)
      (UpperL_summable_occ V w kc hN1 u)
  have hs2 : Summable fun α : Occ => if InMuA (rhoN N) (LN N) kc N u α then
      (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => by split_ifs <;> first | exact le_rfl | positivity)
      (UpperL_summable_occ V w kc hN1 u)
  have hQ : Expect.Q (trialState V w kc N) [u] =
      (∑' α : Occ, if InMuS (rhoN N) (LN N) kc N u α then
        (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) +
      ∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
        (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
    have e : Expect.Q (trialState V w kc N) [u] =
        ∑' α : Occ, (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by simp [Expect.Q]
    rw [e, ← Summable.tsum_add hs1 hs2]
    refine tsum_congr fun α => ?_
    by_cases hM : InM (rhoN N) (LN N) kc N α
    · by_cases hsym : α u = α (-u) <;> simp [InMuS, InMuA, hM, hsym]
    · have h0 : ‖trialState V w kc N α‖ ^ 2 = 0 := by
        by_contra h
        exact hM (UpperL_inM h)
      simp [InMuS, InMuA, hM, h0]
  -- the symmetric part
  have hks : ∀ β : Occ, InMuS (rhoN N) (LN N) kc N u β → β u ≤ ⌈mc (rhoN N)⌉₊ :=
    fun β hβ => (le_max_left (β u) (β (-u))).trans (MStar_PL_ceil hρ hβ.1 hu)
  have hZ : ∑ m ∈ Finset.range (⌈mc (rhoN N)⌉₊ + 1),
      (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m then
        ‖trialState V w kc N β‖ ^ 2 else 0) ≤ 1 := by
    have h1 := UpperL_fibre hs hψ (InMuS (rhoN N) (LN N) kc N u) (fun β => β u)
      ⌈mc (rhoN N)⌉₊ hks (fun _ => 1)
    simp only [one_mul] at h1
    rw [← h1]
    exact UpperL_tsum_le_one hs hψ hΨ.1.tsum_eq _
  have hWb : (∑' α : Occ, if InMuS (rhoN N) (LN N) kc N u α then
        (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
        (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) := by
    have h1 := UpperL_fibre hs hψ (InMuS (rhoN N) (LN N) kc N u) (fun β => β u)
      ⌈mc (rhoN N)⌉₊ hks (fun m => (m : ℝ))
    rw [h1]
    exact UpperL_W_bound
      (s := fun m => ∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m then
        ‖trialState V w kc N β‖ ^ 2 else 0)
      (fun m => tsum_nonneg fun β => by split_ifs <;> positivity) hx0 hx1
      (fun m => Eq5_26 V w kc hN1 hu m) hZ
  have hW0 : 0 ≤ ∑' α : Occ, if InMuS (rhoN N) (LN N) kc N u α then
      (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 :=
    tsum_nonneg fun α => by split_ifs <;> positivity
  -- the asymmetric part
  have hs3 : Summable fun α : Occ => if InMuA (rhoN N) (LN N) kc N u α then
      (alphaStar α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
    refine Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => ?_) (hs.mul_left (⌈mc (rhoN N)⌉₊ : ℝ))
    split_ifs with hA
    · have : (alphaStar α u : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := by
        exact_mod_cast MStar_PL_ceil hρ hA.1 hu
      exact mul_le_mul_of_nonneg_right this (hψ α)
    · exact mul_nonneg (Nat.cast_nonneg _) (hψ α)
  have hAb : (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
        (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      C * rhoN N * mc (rhoN N) / epsP (rhoN N) *
        (∑' α : Occ, if InMuS (rhoN N) (LN N) kc N u α then
          (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) := by
    refine le_trans (hs2.tsum_le_tsum (fun α => ?_) hs3) (h22w N hN kc u hu)
    split_ifs
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left (α u) (α (-u))) (hψ α)
    · exact le_rfl
  rw [hQ]
  calc _ ≤ (∑' α : Occ, if InMuS (rhoN N) (LN N) kc N u α then
          (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) *
        (1 + C * rhoN N * mc (rhoN N) / epsP (rhoN N)) := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hWb (by positivity)

/-! ### The pinned statements -/

/-- (5.22) [ubpsiuroughPL1]. -/
theorem Eq5_22 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      ∀ m : ℕ,
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m then
          ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C * rhoN N * m / epsP (rhoN N) *
          (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m then
            ‖trialState V w kc N β‖ ^ 2 else 0) := by
  obtain ⟨C, hC, h⟩ := UpperL_core22 V w
  exact ⟨C, hC, 84, h⟩

/-- (5.22) [ubpsiuroughPL1] weighted by `α*(u)` and summed over `m`, the form used for (7.57) [8.2]. -/
theorem Eq5_22_weighted (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
          (alphaStar α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C * rhoN N * mc (rhoN N) / epsP (rhoN N) *
          (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β then
            (β u : ℝ) * ‖trialState V w kc N β‖ ^ 2 else 0) := by
  obtain ⟨C, hC, h⟩ := UpperL_core22w V w
  exact ⟨C, hC, 84, h⟩

/-- (5.23) [boundMa]. -/
theorem Eq5_23 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
          ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C * rhoN N * mc (rhoN N) / epsP (rhoN N) := by
  obtain ⟨C, hC, h⟩ := UpperL_core23 V w
  exact ⟨C, hC, 84, h⟩

/-- (5.24) [boundMaMa], for `u ≠ ±v`. -/
theorem Eq5_24 (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u v : Idx,
      inPL (rhoN N) (LN N) u → inPL (rhoN N) (LN N) v → u ≠ v → u + v ≠ 0 →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ InMuA (rhoN N) (LN N) kc N v α then
          ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        (C * rhoN N * mc (rhoN N) / epsP (rhoN N)) ^ 2 := by
  obtain ⟨C, hC, h⟩ := UpperL_core24 V w
  exact ⟨C, hC, 84, h⟩

/-- (5.14) [ubpsiuroughPL] of Lemma 5.4 [lem1]. -/
theorem Lemma5_4_PL {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      Expect.Q (trialState V w kc N) [u] ≤
        (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) *
          (1 + C * rhoN N * mc (rhoN N) / epsP (rhoN N)) := by
  obtain ⟨C, hC, h⟩ := UpperL_core54 hg
  exact ⟨C, hC, 84, h⟩

end LHYUpper
