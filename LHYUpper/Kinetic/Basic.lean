module

public import LHYUpper.Particles.Basic
public import LHYUpper.Riemann.Cells
public import LHYUpper.Scattering.Lambda

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Auxiliary facts -/

/-- `mom L` is additive in the lattice index. -/
private lemma Kinetic_mom_sub (L : ℝ) (a b : Idx) : mom L (a - b) = mom L a - mom L b := by
  ext i
  simp [mom, mul_sub]

/-- `mom L 0 = 0`. -/
private lemma Kinetic_mom_zero (L : ℝ) : mom L 0 = 0 := by
  ext i
  simp [mom]

/-- Interchange of the two sums of a nonnegative double family whose fibres over `k` are
summable with summable totals. -/
private theorem Kinetic_hasSum_swap {ι κ : Type*} (a : ι → κ → ℝ) (s : κ → ℝ)
    (ha : ∀ i k, 0 ≤ a i k) (hfib : ∀ k, HasSum (fun i => a i k) (s k)) (hs : Summable s) :
    HasSum (fun i => ∑' k, a i k) (∑' k, s k) := by
  have hF : Summable (fun x : κ × ι => a x.2 x.1) := by
    rw [summable_prod_of_nonneg (fun x => ha _ _)]
    refine ⟨fun k => (hfib k).summable, ?_⟩
    simpa [(hfib _).tsum_eq] using hs
  have h1 : Summable (Function.uncurry a) := hF.prod_symm
  have h2 : HasSum (fun i => ∑' k, a i k) (∑' i, ∑' k, a i k) := h1.prod.hasSum
  have h3 : ∑' k, ∑' i, a i k = ∑' i, ∑' k, a i k := Summable.tsum_comm h1
  rw [← h3] at h2
  have h4 : ∑' k, ∑' i, a i k = ∑' k, s k := tsum_congr fun k => (hfib k).tsum_eq
  rwa [h4] at h2

/-- On the support of an `N`-particle state, every occupation number is at most `N`. -/
private theorem Kinetic_occ_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) {α : Occ}
    (hz : Ψ α ≠ 0) (u : Idx) : (α u : ℝ) ≤ N := by
  have h : α u ≤ α.num := by
    by_cases hn : u ∈ α.support
    · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
    · rw [Finsupp.notMem_support_iff.mp hn]; exact Nat.zero_le _
  have h2 := h.trans (hΨ.2 α hz).le
  exact_mod_cast h2

/-- The summand `|Ψ(α)|² |n|² α(n)` of the kinetic series. -/
private def Kinetic_F (L : ℝ) (Ψ : Occ → ℂ) (α : Occ) (n : Idx) : ℝ :=
  ‖Ψ α‖ ^ 2 * (‖mom L n‖ ^ 2 * (α n : ℝ))

private lemma Kinetic_F_nonneg (L : ℝ) (Ψ : Occ → ℂ) (α : Occ) (n : Idx) :
    0 ≤ Kinetic_F L Ψ α n := by
  unfold Kinetic_F
  positivity

/-- For fixed `α`, the sum over `n` of `Kinetic_F` is `kinTerm`. -/
private lemma Kinetic_hasSum_fibre (L : ℝ) (Ψ : Occ → ℂ) (α : Occ) :
    HasSum (fun n => Kinetic_F L Ψ α n) (kinTerm L Ψ α) := by
  have h : HasSum (fun n : Idx => Kinetic_F L Ψ α n)
      (∑ n ∈ α.support, Kinetic_F L Ψ α n) :=
    hasSum_sum_of_ne_finset_zero (fun b hb => by
      simp [Kinetic_F, Finsupp.notMem_support_iff.mp hb])
  have h2 : (∑ n ∈ α.support, Kinetic_F L Ψ α n) = kinTerm L Ψ α := by
    unfold kinTerm Kinetic_F
    rw [Finset.mul_sum]
  rwa [h2] at h

/-- `Σ_α Kinetic_F = |n|² Q_Ψ(n)`. -/
private lemma Kinetic_tsum_alpha (L : ℝ) (Ψ : Occ → ℂ) (n : Idx) :
    ∑' α : Occ, Kinetic_F L Ψ α n = ‖mom L n‖ ^ 2 * Expect.Q Ψ [n] := by
  have h : Expect.Q Ψ [n] = ∑' α : Occ, (α n : ℝ) * ‖Ψ α‖ ^ 2 := by
    simp [Expect.Q]
  rw [h, ← tsum_mul_left]
  refine tsum_congr fun α => ?_
  unfold Kinetic_F
  ring

/-- For an `N`-particle state, the fibre over `n` of `Kinetic_F` is summable. -/
private lemma Kinetic_summable_alpha {N : ℕ} {L : ℝ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ)
    (n : Idx) : Summable fun α : Occ => Kinetic_F L Ψ α n := by
  have hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  refine Summable.of_nonneg_of_le (fun α => Kinetic_F_nonneg L Ψ α n) (fun α => ?_)
    (hs.mul_left (‖mom L n‖ ^ 2 * N))
  by_cases hz : Ψ α = 0
  · simp [Kinetic_F, hz]
  · unfold Kinetic_F
    have h1 := Kinetic_occ_le hΨ hz n
    have h2 : 0 ≤ ‖Ψ α‖ ^ 2 := by positivity
    have h3 : ‖mom L n‖ ^ 2 * (α n : ℝ) ≤ ‖mom L n‖ ^ 2 * N :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ‖Ψ α‖ ^ 2 * (‖mom L n‖ ^ 2 * (α n : ℝ)) ≤ ‖Ψ α‖ ^ 2 * (‖mom L n‖ ^ 2 * N) :=
          mul_le_mul_of_nonneg_left h3 h2
      _ = ‖mom L n‖ ^ 2 * N * ‖Ψ α‖ ^ 2 := by ring

/-- The kinetic energy of the trial state (3.18) [deffal] in momentum form, as in Lemma 4.1
[lemkinetic]: `Σ_α |Ψ(α)|² Σ_k |k|² α(k)` and `Σ_u |u|² Q_Ψ(u)` converge together, to the same
value. -/
theorem Kinetic_hasSum_iff (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (E : ℝ) :
    HasSum (kinTerm (LN N) (trialState V w kc N)) E ↔
      HasSum (fun n : Idx => ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n]) E := by
  have hΨ := Normalization_isNState V w kc hN
  set L := LN N with hL
  set Ψ := trialState V w kc N with hΨdef
  constructor
  · intro h
    have key := Kinetic_hasSum_swap (fun (n : Idx) (α : Occ) => Kinetic_F L Ψ α n)
      (kinTerm L Ψ) (fun n α => Kinetic_F_nonneg L Ψ α n)
      (fun α => Kinetic_hasSum_fibre L Ψ α) h.summable
    rw [h.tsum_eq] at key
    refine key.congr_fun ?_
    intro n
    exact (Kinetic_tsum_alpha L Ψ n).symm
  · intro h
    have key := Kinetic_hasSum_swap (fun (α : Occ) (n : Idx) => Kinetic_F L Ψ α n)
      (fun n : Idx => ‖mom L n‖ ^ 2 * Expect.Q Ψ [n]) (fun α n => Kinetic_F_nonneg L Ψ α n)
      (fun n => by
        have h1 := (Kinetic_summable_alpha (L := L) hΨ n).hasSum
        rw [Kinetic_tsum_alpha] at h1
        exact h1)
      h.summable
    rw [h.tsum_eq] at key
    refine key.congr_fun ?_
    intro α
    exact (Kinetic_hasSum_fibre L Ψ α).tsum_eq.symm

/-- `|u|² Q_Ψ(u)` vanishes outside `P_L ∪ P_I ∪ P_H` (at `u = 0` and on the gap
`0 < |u| < ε_L ρ^{1/2}` of Definition 3.1 [def1]), and the three regions are disjoint. -/
theorem Kinetic_split (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (fun n : Idx => ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n]) =
      fun n : Idx =>
        (if inPL (rhoN N) (LN N) n then
          ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n] else 0) +
        (if inPI (rhoN N) (LN N) n then
          ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n] else 0) +
        (if inPH (rhoN N) (LN N) n then
          ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n] else 0) := by
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  funext n
  by_cases hPL : inPL (rhoN N) (LN N) n
  · have h1 : ¬ inPI (rhoN N) (LN N) n := Regions_PL_PI hPL
    have h2 : ¬ inPH (rhoN N) (LN N) n := Regions_PL_PH hρ hPL
    simp [hPL, h1, h2]
  by_cases hPI : inPI (rhoN N) (LN N) n
  · have h2 : ¬ inPH (rhoN N) (LN N) n := Regions_PI_PH hPI
    simp [hPL, hPI, h2]
  by_cases hPH : inPH (rhoN N) (LN N) n
  · simp [hPL, hPI, hPH]
  -- `n` lies in no region
  simp only [hPL, hPI, hPH, ite_false, add_zero]
  by_cases h0 : n = 0
  · subst h0
    simp [Kinetic_mom_zero]
  · have hQ : Expect.Q (trialState V w kc N) [n] = 0 := by
      have h : Expect.Q (trialState V w kc N) [n] =
          ∑' α : Occ, (α n : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by
        simp [Expect.Q]
      rw [h]
      refine (tsum_congr fun α => ?_).trans tsum_zero
      by_cases hz : trialState V w kc N α = 0
      · simp [hz]
      · have hM : InM (rhoN N) (LN N) kc N α := by
          by_contra hM
          rw [FIdentities_trialState] at hz
          exact hz (by simp [hM])
        by_cases ha : α n = 0
        · simp [ha]
        · rcases MBasic_support hM n ha with h | h | h | h
          · exact absurd h h0
          · exact absurd h hPL
          · exact absurd h hPI
          · exact absurd h hPH
    simp [hQ]

/-- The decay threshold: `ρ_N^{49/100} ≤ 1/2` for all large `N`. -/
private lemma Kinetic_eventually_small :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ rhoN N ^ (49 / 100 : ℝ) ≤ 1 / 2 := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (Real.continuousAt_rpow_const (0 : ℝ) (49 / 100 : ℝ) (Or.inr (by norm_num))).tendsto
  rw [Real.zero_rpow (by norm_num)] at h
  have h2 : ∀ᶠ N : ℕ in atTop, rhoN N ^ (49 / 100 : ℝ) ≤ 1 / 2 :=
    (h.comp hT).eventually (ge_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop 1, h2] with N hN hq
  exact ⟨hN, hq⟩

/-- For `0 < ρ` with `ρ^{49/100} ≤ 1/2`: `ε_L^{-1} ρ^{1/2} ≤ ε_L / 2`. -/
private lemma Kinetic_threshold {ρ : ℝ} (hρ : 0 < ρ) (hq : ρ ^ (49 / 100 : ℝ) ≤ 1 / 2) :
    (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) ≤ epsP ρ / 2 := by
  have hε0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have e1 : epsP ρ ^ 2 = ρ ^ (1 / 100 : ℝ) := by
    rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have e2 : ρ ^ (1 / 2 : ℝ) = ρ ^ (49 / 100 : ℝ) * ρ ^ (1 / 100 : ℝ) := by
    rw [← Real.rpow_add hρ]
    norm_num
  have hpos : 0 < ρ ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hρ _
  have h1 : ρ ^ (1 / 2 : ℝ) ≤ epsP ρ ^ 2 / 2 := by
    rw [e1, e2]
    nlinarith
  rw [inv_mul_le_iff₀ hε0]
  nlinarith

/-- The mean value step (6.13)–(6.14) in uniform form: for `u ∈ P_H` and `v ∈ P_L`,
`|λ_{v−u} − λ_u| ≤ C ε_H^{-3} (1 + |u|)^{-4} |v|`. -/
theorem Kinetic_lam_pair {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ u v : Idx,
      inPH (rhoN N) (LN N) u → inPL (rhoN N) (LN N) v →
      |lam V w (rhoN N) (LN N) (v - u) - lam V w (rhoN N) (LN N) u| ≤
        C / epsP (rhoN N) ^ 3 * ((1 + ‖mom (LN N) u‖) ^ 4)⁻¹ * ‖mom (LN N) v‖ := by
  obtain ⟨C₄, hC₄⟩ := scat_wmom_lipschitz hV hw 4
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp Kinetic_eventually_small
  refine ⟨max C₄ 0, le_max_right _ _, N₀, fun N hN u v hu hv => ?_⟩
  obtain ⟨hN1, hq⟩ := hN₀ N hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  have hε0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hth := Kinetic_threshold hρ hq
  have hvε : ‖mom L v‖ ≤ epsP ρ / 2 := hv.2.trans hth
  have huε : epsP ρ < ‖mom L u‖ := hu
  -- `v - u ∉ P_L` and `u ∉ P_L`
  have hvu : ¬ inPL ρ L (v - u) := by
    intro h
    have h1 : ‖mom L u‖ - ‖mom L v‖ ≤ ‖mom L (v - u)‖ := by
      rw [Kinetic_mom_sub, norm_sub_rev]
      exact norm_sub_norm_le _ _
    have h2 := h.2
    linarith
  have huL : ¬ inPL ρ L u := fun h => Regions_PL_PH hρ h hu
  rw [scat_lam_of_not_PL ρ L _ hvu, scat_lam_of_not_PL ρ L _ huL, Kinetic_mom_sub]
  have hq0 : wmom V w (mom L v - mom L u) = wmom V w (mom L u - mom L v) := by
    rw [← scat_wmom_neg hV hw (mom L v - mom L u), neg_sub]
  have hqp : ‖(mom L u - mom L v) - mom L u‖ = ‖mom L v‖ := by
    rw [sub_sub_cancel_left, norm_neg]
  have hb := hC₄ (epsP ρ) hε0 hε1 (mom L u) (mom L u - mom L v) huε.le
    (by rw [hqp]; exact hvε)
  rw [hqp] at hb
  rw [hq0, show -wmom V w (mom L u - mom L v) - -wmom V w (mom L u) =
    -(wmom V w (mom L u - mom L v) - wmom V w (mom L u)) by ring, abs_neg]
  refine hb.trans ?_
  have hD : (0 : ℝ) ≤ ((1 + ‖mom L u‖) ^ 4)⁻¹ := by positivity
  have hE : 0 < epsP ρ ^ 3 := by positivity
  gcongr
  exact le_max_left _ _

/-- The decay summand is the lattice-sum summand (for `A = ℝ³`) plus the term at `n = 0`. -/
private lemma Kinetic_decay_term (L : ℝ) (A : Set R3) (hA : ∀ p, p ∈ A) (n : Idx) :
    ((1 + ‖mom L n‖) ^ 4)⁻¹ =
      (if n ≠ 0 ∧ mom L n ∈ A then |((1 + ‖mom L n‖) ^ 4)⁻¹| else 0) +
        (if n = 0 then (1 : ℝ) else 0) := by
  by_cases hn : n = 0
  · subst hn
    simp [Kinetic_mom_zero]
  · simp [hn, hA, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((1 + ‖mom L n‖) ^ 4)⁻¹)]

/-- `|Λ|⁻¹ Σ_u (1 + |u|)^{-4}` is bounded uniformly in `L ≥ 2π`: the finiteness of
`Σ_{u ∈ P_H} G(u)/|Λ|` in the proof of (6.4), with `G(u)` replaced by `(1 + |u|)^{-4}`. -/
theorem Kinetic_sum_decay :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, 2 * π ≤ L →
      Summable (fun n : Idx => ((1 + ‖mom L n‖) ^ 4)⁻¹) ∧
      (L ^ 3)⁻¹ * (∑' n : Idx, ((1 + ‖mom L n‖) ^ 4)⁻¹) ≤ K := by
  obtain ⟨K₀, hK₀, hK⟩ := latSum_abs_le (a := 0) (b := 4) le_rfl (by norm_num) (by norm_num)
  refine ⟨K₀ + ((2 * π) ^ 3)⁻¹, by positivity, fun L hL => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨hsum, hbd⟩ := hK 1 (fun p => ((1 + ‖p‖) ^ 4)⁻¹) L zero_le_one hL (fun p hp => by
    have hp0 : 0 < ‖p‖ := norm_pos_iff.mpr hp
    rw [abs_of_nonneg (by positivity), one_mul]
    refine le_min ?_ ?_
    · simp only [neg_zero, Real.rpow_zero]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith))
    · rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hp0.le, Real.rpow_natCast]
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hp0.le (by linarith) 4))
  have hS2 : HasSum (fun n : Idx => if n = 0 then (1 : ℝ) else 0) 1 := by
    simpa using hasSum_ite_eq (0 : Idx) (1 : ℝ)
  have hadd := hsum.hasSum.add hS2
  have hh : HasSum (fun n : Idx => ((1 + ‖mom L n‖) ^ 4)⁻¹)
      (latSum L Set.univ (fun p => |((1 + ‖p‖) ^ 4)⁻¹|) + 1) := by
    refine hadd.congr_fun ?_
    intro n
    exact Kinetic_decay_term L Set.univ (fun p => Set.mem_univ p) n
  refine ⟨hh.summable, ?_⟩
  have htsum : ∑' n : Idx, ((1 + ‖mom L n‖) ^ 4)⁻¹ =
      latSum L Set.univ (fun p => |((1 + ‖p‖) ^ 4)⁻¹|) + 1 := hh.tsum_eq
  rw [htsum, mul_add]
  have h1 : (L ^ 3)⁻¹ * latSum L Set.univ (fun p => |((1 + ‖p‖) ^ 4)⁻¹|) ≤ K₀ := by
    simpa using hbd
  have h2 : (L ^ 3)⁻¹ * 1 ≤ ((2 * π) ^ 3)⁻¹ := by
    rw [mul_one]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hL 3)
  linarith

end LHYUpper
