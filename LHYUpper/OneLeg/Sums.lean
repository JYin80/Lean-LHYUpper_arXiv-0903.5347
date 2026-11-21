module

public import LHYUpper.Assembly.Section4
public import LHYUpper.OneLeg.FirstPair
public import LHYUpper.OneLeg.Ratio
public import LHYUpper.Particles.Totals
public import LHYUpper.Riemann.Bridge
public import LHYUpper.Scattering.Identities
public import LHYUpper.Particles.Lower
public import LHYUpper.Particles.Lemma55

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! Sums over `Idx × Idx × Occ` for Lemma 8.3 [0resultfirstcase]: the shell sum (8.27), the
identity (8.29) [sum0PL], and the three cases (8.14)–(8.16) with the per-pair exponents of
(8.31)–(8.34). -/

/-! ### The scales `ρ_N`, `L_N` -/

/-- `|Λ| = L_N³ = ρ_N^{-25/8}`. -/
private lemma Sums_Lcube {N : ℕ} (hN : 1 ≤ N) : LN N ^ 3 = rhoN N ^ (-(25/8 : ℝ)) := by
  have hρ := (Particles_rhoN_LN hN).2.1
  rw [LN, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  norm_num

/-- `N = ρ_N^{-17/8}`. -/
private lemma Sums_N_eq {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) = rhoN N ^ (-(17/8 : ℝ)) := by
  have hρ := (Particles_rhoN_LN hN).2.1
  have h1 : rhoN N ^ (-(17/8 : ℝ)) = rhoN N ^ (1 : ℝ) * rhoN N ^ (-(25/8 : ℝ)) := by
    rw [← Real.rpow_add hρ]
    norm_num
  rw [h1, Real.rpow_one, ← Sums_Lcube hN, (Particles_rhoN_LN hN).1]

/-- `ρ_N^a → ∞` for `a < 0`. -/
private lemma Sums_rho_tendsto_atTop {a : ℝ} (ha : a < 0) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop atTop := by
  have h : ∀ N : ℕ, rhoN N ^ a = (N : ℝ) ^ (8 / 17 * (-a)) := fun N => by
    rw [rhoN, ← Real.rpow_mul (Nat.cast_nonneg N)]
    ring_nf
  simp_rw [h]
  exact (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop

/-- `c ≤ ρ_N^a` eventually, for `a < 0`. -/
private lemma Sums_ev_rho_ge {a : ℝ} (ha : a < 0) (c : ℝ) :
    ∀ᶠ N : ℕ in atTop, c ≤ rhoN N ^ a :=
  (Sums_rho_tendsto_atTop ha).eventually_ge_atTop c

/-- `2π ≤ L_N` eventually. -/
private lemma Sums_ev_L : ∀ᶠ N : ℕ in atTop, 2 * π ≤ LN N := by
  filter_upwards [Sums_ev_rho_ge (a := -(25/24 : ℝ)) (by norm_num) (2 * π)] with N hN
  exact hN

private lemma Sums_eps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _

/-- `ρ^b ≤ ρ^a` for `0 < ρ ≤ 1` and `a ≤ b`. -/
private lemma Sums_rpow_mono {ρ a b : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) (hab : a ≤ b) :
    ρ ^ b ≤ ρ ^ a := Real.rpow_le_rpow_of_exponent_ge hρ h1 hab

/-! ### Counting lattice points -/

/-- The lattice points with `‖p_n‖ ≤ R` form a finite set. -/
private lemma Sums_finite_ball {L R : ℝ} (hL : 0 < L) : {n : Idx | ‖mom L n‖ ≤ R}.Finite := by
  set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
  refine (Set.finite_Icc (fun _ : Fin 3 => -B) (fun _ => B)).subset ?_
  intro n hn
  have hi : ∀ i : Fin 3, |(n i : ℝ)| ≤ B := by
    intro i
    have h1 : |(mom L n).ofLp i| ≤ R := by
      have := PiLp.norm_apply_le (mom L n) i
      rw [Real.norm_eq_abs] at this
      exact this.trans hn
    rw [Cells_mom_apply, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
    have h2 : |(n i : ℝ)| ≤ L * R / (2 * π) := by
      rw [le_div_iff₀ (by positivity)]
      have := h1
      rw [div_mul_eq_mul_div, div_le_iff₀ hL] at this
      nlinarith
    exact h2.trans (Int.le_ceil _)
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.1 (hi i)).1
    exact_mod_cast this
  · have := (abs_le.1 (hi i)).2
    exact_mod_cast this

/-- `#{n ≠ 0 : ‖p_n‖ ≤ R} ≤ K L³ R³` for `2π ≤ L R`. -/
private lemma Sums_card : ∃ K : ℝ, 0 ≤ K ∧ ∀ L R : ℝ, 0 < R → 2 * π ≤ L * R →
    ∃ F : Finset Idx, (∀ n : Idx, n ≠ 0 → ‖mom L n‖ ≤ R → n ∈ F) ∧
      (F.card : ℝ) ≤ K * (L ^ 3 * R ^ 3) := by
  obtain ⟨K, hK, h⟩ := sum_norm_rpow_le (s := 0) (by norm_num)
  refine ⟨K, hK, fun L R hR hLR => ?_⟩
  have hL : 0 < L := by
    by_contra hL
    push Not at hL
    have : L * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hL hR.le
    linarith [Real.pi_pos]
  have hfin : {n : Idx | n ≠ 0 ∧ ‖mom L n‖ ≤ R}.Finite :=
    (Sums_finite_ball (R := R) hL).subset fun n hn => hn.2
  refine ⟨hfin.toFinset, fun n hn hR' => hfin.mem_toFinset.2 ⟨hn, hR'⟩, ?_⟩
  have hsum : (∑' n : Idx, (if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-(0 : ℝ)) else 0)) =
      (hfin.toFinset.card : ℝ) := by
    rw [tsum_eq_sum (s := hfin.toFinset)]
    · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have := hfin.mem_toFinset.1 hn
      simp [this.1, this.2]
    · intro n hn
      have : ¬ (n ≠ 0 ∧ ‖mom L n‖ ≤ R) := fun h' => hn (hfin.mem_toFinset.2 h')
      simp [this]
  have h1 := h L R hR hLR
  rw [hsum, sub_zero, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h1
  have hL3 : 0 < L ^ 3 := by positivity
  calc (hfin.toFinset.card : ℝ) = L ^ 3 * ((L ^ 3)⁻¹ * hfin.toFinset.card) := by
        field_simp
    _ ≤ L ^ 3 * (K * R ^ 3) := mul_le_mul_of_nonneg_left h1 hL3.le
    _ = K * (L ^ 3 * R ^ 3) := by ring

/-- `P_L` lies in a finite set of at most `K ρ^{3/2 - 3/200} |Λ|` lattice points. -/
private lemma Sums_cardPL : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ F : Finset Idx,
    (∀ n : Idx, inPL (rhoN N) (LN N) n → n ∈ F) ∧
      (F.card : ℝ) ≤ K * rhoN N ^ (3/2 - 3/200 : ℝ) * LN N ^ 3 := by
  obtain ⟨K, hK, h⟩ := Sums_card
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    ((eventually_ge_atTop 1).and
      (Sums_ev_rho_ge (a := -(25/24 : ℝ) + (1/2 - 1/200)) (by norm_num) (2 * π)))
  refine ⟨K, hK, N₁, fun N hN => ?_⟩
  obtain ⟨hN1, hlr⟩ := hN₁ N hN
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hR : (epsP (rhoN N))⁻¹ * rhoN N ^ (1/2 : ℝ) = rhoN N ^ (1/2 - 1/200 : ℝ) := by
    rw [epsP, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
    ring_nf
  have hLR : LN N * rhoN N ^ (1/2 - 1/200 : ℝ) = rhoN N ^ (-(25/24 : ℝ) + (1/2 - 1/200)) := by
    rw [LN, ← Real.rpow_add hρ]
  obtain ⟨F, hF, hcard⟩ := h (LN N) ((epsP (rhoN N))⁻¹ * rhoN N ^ (1/2 : ℝ))
    (by rw [hR]; positivity) (by rw [hR, hLR]; exact hlr)
  refine ⟨F, fun n hn => hF n (Regions_PL_ne_zero hρ hn) hn.2, ?_⟩
  refine hcard.trans (le_of_eq ?_)
  have hR3 : (rhoN N ^ (1/2 - 1/200 : ℝ)) ^ 3 = rhoN N ^ (3/2 - 3/200 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  rw [hR, hR3]
  ring

/-! ### Iterated sums over `Idx × Idx × Occ` -/

/-- Fubini on `Idx × Idx × Occ` for a summable family. -/
private lemma Sums_fubini {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : Idx × Idx × Occ → E) (hf : Summable f) :
    ∑' i, f i = ∑' v₁ : Idx, ∑' v₂ : Idx, ∑' β : Occ, f (v₁, v₂, β) ∧
    (∀ v₁ : Idx, Summable fun v₂ : Idx => ∑' β : Occ, f (v₁, v₂, β)) ∧
    (Summable fun v₁ : Idx => ∑' v₂ : Idx, ∑' β : Occ, f (v₁, v₂, β)) ∧
    (∀ v₁ v₂ : Idx, Summable fun β : Occ => f (v₁, v₂, β)) := by
  refine ⟨?_, fun v₁ => (hf.prod_factor v₁).prod, ?_, fun v₁ v₂ => (hf.prod_factor v₁).prod_factor v₂⟩
  · rw [hf.tsum_prod]
    exact tsum_congr fun v₁ => (hf.prod_factor v₁).tsum_prod
  · have h := hf.prod
    refine h.congr fun v₁ => ?_
    exact (hf.prod_factor v₁).tsum_prod

/-! ### The sums `Σ_u Q_Ψ(0, u)` over `P_L` -/

/-- `Ψ α ≠ 0` forces `α ∈ M`. -/
private lemma Sums_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hM
  exact h (by simp [trialState, hM])

/-- `Σ_n α(n) = α.num`. -/
private lemma Sums_hasSum_occ (α : Occ) : HasSum (fun n : Idx => (α n : ℝ)) (α.num : ℝ) := by
  have h : HasSum (fun n : Idx => (α n : ℝ)) (∑ n ∈ α.support, (α n : ℝ)) :=
    hasSum_sum_of_ne_finset_zero (fun b hb => by simp [Finsupp.notMem_support_iff.mp hb])
  simpa [Occ.num, Finsupp.sum, Nat.cast_sum] using h

/-- On the support of an `N`-particle state, `α(u) ≤ N`. -/
private lemma Sums_occ_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) {α : Occ}
    (hz : Ψ α ≠ 0) (u : Idx) : (α u : ℝ) ≤ N := by
  have h := le_hasSum (Sums_hasSum_occ α) u (fun _ _ => by positivity)
  rwa [hΨ.2 α hz] at h

/-- `α.num · |Ψ(α)|² = N |Ψ(α)|²` for an `N`-particle state. -/
private lemma Sums_num_mul {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (α : Occ) :
    (α.num : ℝ) * ‖Ψ α‖ ^ 2 = N * ‖Ψ α‖ ^ 2 := by
  by_cases hz : Ψ α = 0
  · simp [hz]
  · rw [hΨ.2 α hz]

/-- A bounded weight against `|Ψ|²` is summable. -/
private lemma Sums_summable_weight {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (h : Occ → ℝ)
    (C : ℝ) (hh : ∀ α, Ψ α ≠ 0 → |h α| ≤ C) : Summable fun α : Occ => h α * ‖Ψ α‖ ^ 2 := by
  refine Summable.of_norm_bounded (hΨ.1.summable.mul_left C) (fun α => ?_)
  rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
  by_cases hz : Ψ α = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hh α hz) (by positivity)

/-- Interchange of a sum over `Idx` and a sum over `Occ` for nonnegative terms. -/
private lemma Sums_hasSum_swap (a : Idx → Occ → ℝ) (s : Occ → ℝ) (ha : ∀ u α, 0 ≤ a u α)
    (hfib : ∀ α, HasSum (fun u => a u α) (s α)) (hs : Summable s) :
    HasSum (fun u => ∑' α, a u α) (∑' α, s α) := by
  have hF : Summable (fun x : Occ × Idx => a x.2 x.1) := by
    rw [summable_prod_of_nonneg (fun x => ha _ _)]
    refine ⟨fun α => (hfib α).summable, ?_⟩
    simpa [(hfib _).tsum_eq] using hs
  have h1 : Summable (Function.uncurry a) := hF.prod_symm
  have h2 : HasSum (fun u => ∑' α, a u α) (∑' u, ∑' α, a u α) := h1.prod.hasSum
  have h3 : ∑' α, ∑' u, a u α = ∑' u, ∑' α, a u α := Summable.tsum_comm h1
  rw [← h3] at h2
  have h4 : ∑' α, ∑' u, a u α = ∑' α, s α := tsum_congr fun α => (hfib α).tsum_eq
  rwa [h4] at h2

private lemma Sums_Q_single (Φ : Occ → ℂ) (u : Idx) :
    Expect.Q Φ [u] = ∑' α : Occ, (α u : ℝ) * ‖Φ α‖ ^ 2 := by
  simp [Expect.Q]

private lemma Sums_Q_pair (Φ : Occ → ℂ) (u v : Idx) :
    Expect.Q Φ [u, v] = ∑' α : Occ, (α u : ℝ) * (α v : ℝ) * ‖Φ α‖ ^ 2 := by
  simp [Expect.Q, mul_assoc]

private lemma Sums_Q_pair_nonneg (Φ : Occ → ℂ) (u v : Idx) : 0 ≤ Expect.Q Φ [u, v] := by
  rw [Sums_Q_pair]
  exact tsum_nonneg fun α => by positivity

private lemma Sums_Q_single_nonneg (Φ : Occ → ℂ) (u : Idx) : 0 ≤ Expect.Q Φ [u] := by
  rw [Sums_Q_single]
  exact tsum_nonneg fun α => by positivity

/-- `Σ_u Q_Ψ(0, u) = N Q_Ψ(0)`. -/
private lemma Sums_hasSum_Q0 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun u : Idx => Expect.Q (trialState V w kc N) [0, u])
      ((N : ℝ) * Expect.Q (trialState V w kc N) [0]) := by
  have hΨ := Normalization_isNState V w kc hN
  set Ψ := trialState V w kc N
  have hA : Summable fun α : Occ => (α 0 : ℝ) * ‖Ψ α‖ ^ 2 :=
    Sums_summable_weight hΨ (fun α => (α 0 : ℝ)) N
      (fun α hz => by rw [abs_of_nonneg (by positivity)]; exact Sums_occ_le hΨ hz 0)
  have key := Sums_hasSum_swap (fun u α => (α 0 : ℝ) * (α u : ℝ) * ‖Ψ α‖ ^ 2)
    (fun α => (N : ℝ) * ((α 0 : ℝ) * ‖Ψ α‖ ^ 2)) (fun u α => by positivity)
    (fun α => by
      have h := (Sums_hasSum_occ α).mul_left ((α 0 : ℝ) * ‖Ψ α‖ ^ 2)
      have e : (α 0 : ℝ) * ‖Ψ α‖ ^ 2 * α.num = (N : ℝ) * ((α 0 : ℝ) * ‖Ψ α‖ ^ 2) := by
        linear_combination (α 0 : ℝ) * Sums_num_mul hΨ α
      rw [e] at h
      refine h.congr_fun ?_
      intro u
      ring)
    (hA.mul_left (N : ℝ))
  simp only [← Sums_Q_pair] at key
  rw [tsum_mul_left, ← Sums_Q_single] at key
  exact key

/-- `Q_Ψ(0, u) ≤ N Q_Ψ(u)` for an `N`-particle state. -/
private lemma Sums_Q0_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (u : Idx) :
    Expect.Q Ψ [0, u] ≤ (N : ℝ) * Expect.Q Ψ [u] := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Sums_Q_single, ← tsum_mul_left, Sums_Q_pair]
  have hs : Summable fun α : Occ => (α u : ℝ) * ‖Ψ α‖ ^ 2 :=
    Sums_summable_weight hΨ (fun α => (α u : ℝ)) N
      (fun α hz => by rw [abs_of_nonneg (by positivity)]; exact Sums_occ_le hΨ hz u)
  refine Summable.tsum_le_tsum (fun α => ?_) ?_ (hs.mul_left _)
  · by_cases hα : Ψ α = 0
    · simp [hα]
    have c0 := Sums_occ_le hΨ hα 0
    calc (α 0 : ℝ) * α u * ‖Ψ α‖ ^ 2 ≤ (N : ℝ) * α u * ‖Ψ α‖ ^ 2 := by gcongr
      _ = (N : ℝ) * ((α u : ℝ) * ‖Ψ α‖ ^ 2) := by ring
  · exact Sums_summable_weight hΨ (fun α => (α 0 : ℝ) * (α u : ℝ)) ((N : ℝ) * N)
      (fun α hα => by
        rw [abs_of_nonneg (by positivity)]
        exact mul_le_mul (Sums_occ_le hΨ hα _) (Sums_occ_le hΨ hα _) (by positivity) hN0) |>.congr
      (fun α => by ring)

/-- For `u ≠ 0` outside `P_L ∪ P_I ∪ P_H`, `Q_Ψ(0, u) = 0`. -/
private lemma Sums_Q0_eq_zero (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {u : Idx} (hu0 : u ≠ 0)
    (hL : ¬ inPL (rhoN N) (LN N) u) (hI : ¬ inPI (rhoN N) (LN N) u)
    (hH : ¬ inPH (rhoN N) (LN N) u) : Expect.Q (trialState V w kc N) [0, u] = 0 := by
  rw [Sums_Q_pair]
  refine (tsum_congr fun α => ?_).trans tsum_zero
  by_cases hz : trialState V w kc N α = 0
  · simp [hz]
  · have hα := Sums_inM hz
    have : α u = 0 := by
      by_contra h
      rcases MBasic_support hα u h with h0 | h0 | h0 | h0
      · exact hu0 h0
      · exact hL h0
      · exact hI h0
      · exact hH h0
    rw [this]
    simp

/-- `Σ_{u ∈ P_L} Q_Ψ(0, u) = N Q_Ψ(0) - Q_Ψ(0, 0) - Σ_{u ∈ P_I ∪ P_H} Q_Ψ(0, u)`. -/
private lemma Sums_PL_split (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' v₁ : Idx, (if inPL (rhoN N) (LN N) v₁ then
          Expect.Q (trialState V w kc N) [0, v₁] else 0)) =
      (N : ℝ) * Expect.Q (trialState V w kc N) [0] - Expect.Q (trialState V w kc N) [0, 0] -
        ∑' v : Idx, (if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
          Expect.Q (trialState V w kc N) [0, v] else 0) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  set q : Idx → ℝ := fun u => Expect.Q (trialState V w kc N) [0, u] with hq
  have hq0 : ∀ u, 0 ≤ q u := fun u => Sums_Q_pair_nonneg _ _ _
  have hqs : Summable q := (Sums_hasSum_Q0 V w kc hN).summable
  have hsum : ∀ (P : Idx → Prop) [DecidablePred P], Summable fun u => if P u then q u else 0 :=
    fun P _ =>
    Summable.of_nonneg_of_le (fun u => by split_ifs <;> simp [hq0 u])
      (fun u => by split_ifs <;> simp [hq0 u]) hqs
  have hpt : ∀ u : Idx, q u = (if u = 0 then q 0 else 0) +
      ((if inPL (rhoN N) (LN N) u then q u else 0) +
        (if inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u then q u else 0)) := by
    intro u
    by_cases hu : u = 0
    · subst hu
      have h1 : ¬ inPL (rhoN N) (LN N) 0 := fun h => Regions_PL_ne_zero hρ h rfl
      have h2 : ¬ inPI (rhoN N) (LN N) 0 := fun h => Regions_PI_ne_zero hρ h rfl
      have h3 : ¬ inPH (rhoN N) (LN N) 0 := fun h => Regions_PH_ne_zero hρ h rfl
      simp [h1, h2, h3]
    · by_cases hL : inPL (rhoN N) (LN N) u
      · have hI := Regions_PL_PI hL
        have hH := Regions_PL_PH hρ hL
        simp [hu, hL, hI, hH]
      · by_cases hIH : inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u
        · simp [hu, hL, hIH]
        · push Not at hIH
          have := Sums_Q0_eq_zero V w kc N hu hL hIH.1 hIH.2
          simp [hu, hL, hIH.1, hIH.2, hq, this]
  have hall : (N : ℝ) * Expect.Q (trialState V w kc N) [0] = ∑' u, q u :=
    (Sums_hasSum_Q0 V w kc hN).tsum_eq.symm
  have h0 : Summable fun u : Idx => if u = 0 then q 0 else 0 :=
    (hasSum_ite_eq (0 : Idx) (q 0)).summable
  have h0v : (∑' u : Idx, if u = 0 then q 0 else 0) = q 0 := tsum_ite_eq (0 : Idx) (fun _ => q 0)
  have hB := hsum (fun u => inPL (rhoN N) (LN N) u)
  have hC := hsum (fun u => inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u)
  have e : (∑' u, q u) = q 0 + ((∑' u : Idx, (if inPL (rhoN N) (LN N) u then q u else 0)) +
      ∑' u : Idx, (if inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u then q u else 0)) := by
    calc ∑' u, q u = ∑' u : Idx, ((if u = 0 then q 0 else 0) +
          ((if inPL (rhoN N) (LN N) u then q u else 0) +
            (if inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u then q u else 0))) :=
          tsum_congr hpt
      _ = (∑' u : Idx, if u = 0 then q 0 else 0) +
            ((∑' u : Idx, if inPL (rhoN N) (LN N) u then q u else 0) +
              ∑' u : Idx, if inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u then q u else 0) :=
          (h0.tsum_add (hB.add hC)).trans (by rw [hB.tsum_add hC])
      _ = _ := by rw [h0v]
  have h00 : q 0 = Expect.Q (trialState V w kc N) [0, 0] := rfl
  rw [hall, e, h00]
  ring

/-- `0 ≤ Σ_{u ∈ P_I ∪ P_H} Q_Ψ(0, u) ≤ N Σ_{u ∈ P_I ∪ P_H} Q_Ψ(u)`. -/
private lemma Sums_IH_le (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' v : Idx, (if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
          Expect.Q (trialState V w kc N) [0, v] else 0)) ≤
      (N : ℝ) * ∑' v : Idx, (if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
          Expect.Q (trialState V w kc N) [v] else 0) := by
  have hΨ := Normalization_isNState V w kc hN
  have hs1 : Summable fun v : Idx => if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
      Expect.Q (trialState V w kc N) [0, v] else 0 :=
    Summable.of_nonneg_of_le (fun v => by split_ifs <;> simp [Sums_Q_pair_nonneg])
      (fun v => by split_ifs <;> simp [Sums_Q_pair_nonneg])
      (Sums_hasSum_Q0 V w kc hN).summable
  have hs2 : Summable fun v : Idx => if inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v then
      Expect.Q (trialState V w kc N) [v] else 0 :=
    Summable.of_nonneg_of_le (fun v => by split_ifs <;> simp [Sums_Q_single_nonneg])
      (fun v => by split_ifs <;> simp [Sums_Q_single_nonneg])
      (Particles_hasSum_Q V w kc hN).summable
  rw [← tsum_mul_left]
  refine hs1.tsum_le_tsum (fun v => ?_) (hs2.mul_left _)
  split_ifs
  · exact Sums_Q0_le hΨ v
  · simp

/-- (8.28)–(8.29) [sum0PL]: `|Λ|⁻² Σ_{v₁ ∈ P_L} Q_Ψ(0, v₁) = ρ₀(ρ - ρ₀)` up to
`Cρ^{5/2+1/400}`. -/
theorem Eq8_29 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      |((LN N ^ 3) ^ 2)⁻¹ * (∑' v₁ : Idx, (if inPL (rhoN N) (LN N) v₁ then
          Expect.Q (trialState V w kc N) [0, v₁] else 0)) -
        rho0 (g0 V w) (rhoN N) * (rhoN N - rho0 (g0 V w) (rhoN N))| ≤
        C * rhoN N ^ (5/2 + 1/400 : ℝ) := by
  obtain ⟨C3, hC3, N3, h3⟩ := Lemma5_3 hg
  obtain ⟨C6, hC6, N6, h6⟩ := Lemma5_6 hg
  obtain ⟨C1, hC1, N1, h1⟩ := Thm5_1 hg
  refine ⟨C3 + C6 + C1, by positivity, max (max N3 N6) (max N1 1), fun N hN kc => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN3, hN6⟩, hN1, hN1'⟩ := hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1'
  have hΛ : 0 < LN N ^ 3 := by positivity
  set ρ := rhoN N with hρdef
  set Λ := LN N ^ 3 with hΛdef
  set Ψ := trialState V w kc N with hΨdef
  set S := ∑' v : Idx, (if inPI ρ (LN N) v ∨ inPH ρ (LN N) v then
          Expect.Q Ψ [0, v] else 0) with hS
  set T := ∑' v : Idx, (if inPI ρ (LN N) v ∨ inPH ρ (LN N) v then Expect.Q Ψ [v] else 0) with hT
  have hsplit := Sums_PL_split V w kc hN1'
  have hSle : S ≤ (N : ℝ) * T := Sums_IH_le V w kc hN1'
  have hS0 : 0 ≤ S := tsum_nonneg fun v => by split_ifs <;> simp [Sums_Q_pair_nonneg]
  have hT0 : 0 ≤ T := tsum_nonneg fun v => by split_ifs <;> simp [Sums_Q_single_nonneg]
  have hNρ : (N : ℝ) = ρ * Λ := hNL.symm
  -- the three error terms
  have hA := h3 N hN3 kc
  have hB := h6 N hN6 kc
  have hI := (h1 N hN1 kc).1
  have hT' : Λ⁻¹ * T ≤ ρ ^ (3/2 : ℝ) * (C1 * ρ ^ (1/200 : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hI (Real.rpow_nonneg hρ.le (3/2 : ℝ))
    have e : ρ ^ (3/2 : ℝ) * (ρ ^ (-(3/2 : ℝ)) * Λ⁻¹ * T) = Λ⁻¹ * T := by
      rw [← mul_assoc, ← mul_assoc, ← Real.rpow_add hρ]
      norm_num
    rwa [e] at h
  have hSΛ : (Λ ^ 2)⁻¹ * S ≤ C1 * ρ ^ (5/2 + 1/200 : ℝ) := by
    calc (Λ ^ 2)⁻¹ * S ≤ (Λ ^ 2)⁻¹ * ((N : ℝ) * T) :=
          mul_le_mul_of_nonneg_left hSle (by positivity)
      _ = ρ * (Λ⁻¹ * T) := by rw [hNρ]; field_simp
      _ ≤ ρ * (ρ ^ (3/2 : ℝ) * (C1 * ρ ^ (1/200 : ℝ))) :=
          mul_le_mul_of_nonneg_left hT' hρ.le
      _ = C1 * ρ ^ (5/2 + 1/200 : ℝ) := by
          rw [show (5/2 + 1/200 : ℝ) = 1 + 3/2 + 1/200 by norm_num,
            Real.rpow_add hρ (1 + 3/2) (1/200), Real.rpow_add hρ 1 (3/2), Real.rpow_one]
          ring
  have hSΛ0 : 0 ≤ (Λ ^ 2)⁻¹ * S := by positivity
  have hρA : |ρ * (Expect.Q Ψ [0] / Λ - rho0 (g0 V w) ρ)| ≤ C3 * ρ ^ (5/2 + 1/400 : ℝ) := by
    rw [abs_mul, abs_of_pos hρ]
    calc ρ * |Expect.Q Ψ [0] / Λ - rho0 (g0 V w) ρ| ≤ ρ * (C3 * ρ ^ (3/2 + 1/400 : ℝ)) :=
          mul_le_mul_of_nonneg_left hA hρ.le
      _ = C3 * ρ ^ (5/2 + 1/400 : ℝ) := by
          rw [show (5/2 + 1/400 : ℝ) = 1 + (3/2 + 1/400) by norm_num,
            Real.rpow_add hρ 1 (3/2 + 1/400), Real.rpow_one]
          ring
  have key : (Λ ^ 2)⁻¹ * (∑' v₁ : Idx, (if inPL ρ (LN N) v₁ then Expect.Q Ψ [0, v₁] else 0)) -
      rho0 (g0 V w) ρ * (ρ - rho0 (g0 V w) ρ) =
      ρ * (Expect.Q Ψ [0] / Λ - rho0 (g0 V w) ρ) -
        (Expect.Q Ψ [0, 0] / Λ ^ 2 - rho0 (g0 V w) ρ ^ 2) - (Λ ^ 2)⁻¹ * S := by
    rw [hsplit, hNρ]
    field_simp
    ring
  rw [key]
  have hexp : ρ ^ (5/2 + 1/200 : ℝ) ≤ ρ ^ (5/2 + 1/400 : ℝ) :=
    Sums_rpow_mono hρ hρ1 (by norm_num)
  have hc1 : C1 * ρ ^ (5/2 + 1/200 : ℝ) ≤ C1 * ρ ^ (5/2 + 1/400 : ℝ) :=
    mul_le_mul_of_nonneg_left hexp hC1
  calc _ ≤ |ρ * (Expect.Q Ψ [0] / Λ - rho0 (g0 V w) ρ)| +
        |Expect.Q Ψ [0, 0] / Λ ^ 2 - rho0 (g0 V w) ρ ^ 2| + |(Λ ^ 2)⁻¹ * S| := by
        refine (abs_sub _ _).trans ?_
        exact add_le_add_left (abs_sub _ _) _
    _ ≤ C3 * ρ ^ (5/2 + 1/400 : ℝ) + C6 * ρ ^ (5/2 + 1/400 : ℝ) +
        C1 * ρ ^ (5/2 + 1/400 : ℝ) := by
        rw [abs_of_nonneg hSΛ0]
        exact add_le_add (add_le_add hρA hB) (hSΛ.trans hc1)
    _ = _ := by ring

/-! ### The shell sum of (8.27) -/

/-- `p_{a - b} = p_a - p_b`. -/
private lemma Sums_mom_sub (L : ℝ) (a b : Idx) : mom L (a - b) = mom L a - mom L b := by
  ext i
  simp only [mom, WithLp.equiv_symm_apply, PiLp.sub_apply, Pi.sub_apply, Int.cast_sub]
  ring

/-- The summation domain of the inner sum of (8.27) for `v₁`. -/
private def Sums_A (ρ kc : ℝ) (p₁ : R3) : Set R3 :=
  {p | (epsP ρ < ‖p‖ ∧ ‖p‖ ≤ kc) ∧ (epsP ρ < ‖p - p₁‖ ∧ ‖p - p₁‖ ≤ kc)}

private lemma Sums_A_meas (ρ kc : ℝ) (p₁ : R3) : MeasurableSet (Sums_A ρ kc p₁) := by
  have h1 : Measurable fun p : R3 => ‖p‖ := measurable_norm
  have h2 : Measurable fun p : R3 => ‖p - p₁‖ := (measurable_id.sub_const p₁).norm
  exact ((measurableSet_lt measurable_const h1).inter (measurableSet_le h1 measurable_const)).inter
    ((measurableSet_lt measurable_const h2).inter (measurableSet_le h2 measurable_const))

private lemma Sums_A_shell (ρ kc : ℝ) (p₁ : R3) :
    IsShell (epsP ρ) (ENNReal.ofReal kc) ‖p₁‖ (Sums_A ρ kc p₁) := by
  refine ⟨fun p h1 h2 => ?_, fun p hp => ⟨hp.1.1.le, ENNReal.ofReal_le_ofReal hp.1.2⟩⟩
  have h2' : ‖p‖ + ‖p₁‖ < kc := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 h2
  have hs := norm_nonneg p₁
  have a1 : ‖p‖ - ‖p₁‖ ≤ ‖p - p₁‖ := norm_sub_norm_le p p₁
  have a2 : ‖p - p₁‖ ≤ ‖p‖ + ‖p₁‖ := norm_sub_le p p₁
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The membership `p_{v₂} ∈ A` is the pair of conditions `v₂, v₁ - v₂ ∈ P_{H,c}`. -/
private lemma Sums_A_iff {ρ L kc : ℝ} (hρ : 0 < ρ) (v₁ v₂ : Idx) :
    (inPHc ρ L kc v₂ ∧ inPHc ρ L kc (v₁ - v₂)) ↔
      (v₂ ≠ 0 ∧ mom L v₂ ∈ Sums_A ρ kc (mom L v₁)) := by
  unfold inPHc inPH Sums_A
  rw [Sums_mom_sub, norm_sub_rev (mom L v₁) (mom L v₂)]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨Regions_PH_ne_zero hρ h1, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  · rintro ⟨-, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- `δ (1 + log δ⁻¹) ≤ 52 π ρ^{1/200}` for `δ = 2π/L_N`. -/
private lemma Sums_rate_le {ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) :
    riemannRate 2 (2 * π / ρ ^ (-(25/24 : ℝ))) ≤ 52 * π * ρ ^ (1/200 : ℝ) := by
  set δ : ℝ := 2 * π / ρ ^ (-(25/24 : ℝ)) with hδ
  have hLpos : 0 < ρ ^ (-(25/24 : ℝ)) := Real.rpow_pos_of_pos hρ _
  have hδ0 : 0 < δ := by positivity
  have hδρ : δ = 2 * π * ρ ^ (25/24 : ℝ) := by
    rw [hδ, Real.rpow_neg hρ.le, div_inv_eq_mul]
  have hrate : riemannRate 2 δ = δ * (1 + Real.log δ⁻¹) := by
    simp [riemannRate]
  have hlog : Real.log δ⁻¹ ≤ 25 * ρ ^ (-(1/24 : ℝ)) := by
    have hinv : δ⁻¹ = ρ ^ (-(25/24 : ℝ)) / (2 * π) := by
      rw [hδ, inv_div]
    have hπ : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
    have h2 : δ⁻¹ ≤ ρ ^ (-(25/24 : ℝ)) := by
      rw [hinv]
      exact div_le_self hLpos.le hπ
    have h3 : Real.log δ⁻¹ ≤ Real.log (ρ ^ (-(25/24 : ℝ))) :=
      Real.log_le_log (inv_pos.2 hδ0) h2
    rw [Real.log_rpow hρ] at h3
    have h4 : Real.log (ρ⁻¹) ≤ (ρ⁻¹) ^ (1/24 : ℝ) / (1/24) :=
      Real.log_le_rpow_div (inv_nonneg.2 hρ.le) (by norm_num)
    rw [Real.log_inv, Real.inv_rpow hρ.le, ← Real.rpow_neg hρ.le] at h4
    have h5 : -Real.log ρ ≤ 24 * ρ ^ (-(1/24 : ℝ)) := by
      have := h4
      field_simp at this
      linarith
    nlinarith
  rw [hrate]
  have hρ1' : ρ ^ (25/24 : ℝ) ≤ ρ ^ (1/200 : ℝ) := Sums_rpow_mono hρ h1 (by norm_num)
  have hρ2 : ρ ≤ ρ ^ (1/200 : ℝ) := by
    simpa using Sums_rpow_mono hρ h1 (a := 1/200) (b := 1) (by norm_num)
  calc δ * (1 + Real.log δ⁻¹) ≤ δ * (1 + 25 * ρ ^ (-(1/24 : ℝ))) := by
        gcongr
    _ = 2 * π * ρ ^ (25/24 : ℝ) + 50 * π * ρ := by
        rw [hδρ]
        have e : ρ ^ (25/24 : ℝ) * ρ ^ (-(1/24 : ℝ)) = ρ := by
          rw [← Real.rpow_add hρ]
          norm_num
        calc 2 * π * ρ ^ (25/24 : ℝ) * (1 + 25 * ρ ^ (-(1/24 : ℝ))) =
            2 * π * ρ ^ (25/24 : ℝ) + 50 * π * (ρ ^ (25/24 : ℝ) * ρ ^ (-(1/24 : ℝ))) := by ring
          _ = _ := by rw [e]
    _ ≤ 2 * π * ρ ^ (1/200 : ℝ) + 50 * π * ρ ^ (1/200 : ℝ) := by
        gcongr
    _ = 52 * π * ρ ^ (1/200 : ℝ) := by ring

/-- The inner sum of (8.27): `|Λ|⁻¹ Σ_{v₂, v₁ - v₂ ∈ P_{H,c}} V_{v₂} λ_{v₂} = -‖Vw‖₁` up to
`C(ρ^{1/200} + k_c⁻¹)`, uniformly in `v₁ ∈ P_L`. -/
theorem OneLeg_shell {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc → ∀ v₁ : Idx,
      inPL (rhoN N) (LN N) v₁ →
      |(LN N ^ 3)⁻¹ * (∑' v₂ : Idx, (if inPHc (rhoN N) (LN N) kc v₂ ∧
          inPHc (rhoN N) (LN N) kc (v₁ - v₂) then
            (ft V (mom (LN N) v₂)).re * lam V w (rhoN N) (LN N) v₂ else 0)) + normVw V w| ≤
        C * (rhoN N ^ (1/200 : ℝ) + kc⁻¹) := by
  obtain ⟨Cm, hCV, hCg⟩ := Bridge_momDecay hV hw 4
  obtain ⟨K, hK, hsum⟩ := sum_Vw (M := 4) le_rfl hCV hCg
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 ((eventually_ge_atTop 1).and Sums_ev_L)
  refine ⟨K * (2 + 52 * π), by positivity, N₁, fun N hN kc hkc v₁ hv₁ => ?_⟩
  obtain ⟨hN1, hL2⟩ := hN₁ N hN
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  have hkc0 : 0 < kc := by linarith
  have hε : 0 < epsP ρ := Sums_eps_pos hρ
  have hs0 : 0 ≤ ‖mom L v₁‖ := norm_nonneg _
  -- the summand is minus the lattice summand
  have hpt : ∀ v₂ : Idx, (if inPHc ρ L kc v₂ ∧ inPHc ρ L kc (v₁ - v₂) then
        (ft V (mom L v₂)).re * lam V w ρ L v₂ else 0) =
      -(if v₂ ≠ 0 ∧ mom L v₂ ∈ Sums_A ρ kc (mom L v₁) then
        (fun p => (ft V p).re) (mom L v₂) *
          ((fun p => (ft (gfun V w) p).re) (mom L v₂) / ‖mom L v₂‖ ^ 2) else 0) := by
    intro v₂
    by_cases h : inPHc ρ L kc v₂ ∧ inPHc ρ L kc (v₁ - v₂)
    · have h' := (Sums_A_iff hρ v₁ v₂).1 h
      have hnL : ¬ inPL ρ L v₂ := fun hl => Regions_PL_PH hρ hl h.1.1
      rw [ite_eq_left h, ite_eq_left h', scat_lam_of_not_PL ρ L v₂ hnL]
      unfold wmom
      ring
    · have h' : ¬ (v₂ ≠ 0 ∧ mom L v₂ ∈ Sums_A ρ kc (mom L v₁)) := fun h'' =>
        h ((Sums_A_iff hρ v₁ v₂).2 h'')
      rw [ite_eq_right h, ite_eq_right h']
      simp
  rw [tsum_congr hpt, tsum_neg]
  obtain ⟨-, hb⟩ := hsum L (epsP ρ) ‖mom L v₁‖ (ENNReal.ofReal kc) (Sums_A ρ kc (mom L v₁))
    hL2 hε.le hs0 (by simpa using hkc0) (Sums_A_meas _ _ _) (Sums_A_shell _ _ _)
  unfold latSum at hb
  have hVw : ((2 * π) ^ 3)⁻¹ * ∫ p : R3, (fun p => (ft V p).re) p *
      ((fun p => (ft (gfun V w) p).re) p / ‖p‖ ^ 2) = normVw V w := by
    have h1 := scat_Vw_eq hV hw
    have h2 : normVw V w = ∫ x, V x * w x := by
      unfold normVw
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      rw [abs_of_nonneg (mul_nonneg (hV.nonneg x) (hw.nonneg x))]
    rw [h2, h1, inv_pow]
    rfl
  rw [hVw] at hb
  have hinv : (ENNReal.ofReal kc)⁻¹.toReal = kc⁻¹ := by
    rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hkc0.le]
  rw [hinv] at hb
  have hs : ‖mom L v₁‖ ≤ epsP ρ := by
    have h1 := hv₁.2
    have h2 : ρ ^ (1/2 : ℝ) ≤ epsP ρ * epsP ρ := by
      have : epsP ρ * epsP ρ = ρ ^ (1/100 : ℝ) := by
        unfold epsP
        rw [← Real.rpow_add hρ]
        norm_num
      rw [this]
      exact Sums_rpow_mono hρ hρ1 (by norm_num)
    refine h1.trans ?_
    rw [inv_mul_le_iff₀ hε]
    exact h2
  have hrate : riemannRate 2 (2 * π / L) ≤ 52 * π * epsP ρ := by
    have := Sums_rate_le hρ hρ1
    rwa [show L = ρ ^ (-(25/24 : ℝ)) from rfl]
  have hkc : 0 ≤ kc⁻¹ := inv_nonneg.2 hkc0.le
  have hε0 : 0 ≤ epsP ρ := hε.le
  have hfin : K * (epsP ρ + ‖mom L v₁‖ + kc⁻¹ + riemannRate 2 (2 * π / L)) ≤
      K * (2 + 52 * π) * (ρ ^ (1/200 : ℝ) + kc⁻¹) := by
    have hπ : 0 < π := Real.pi_pos
    calc K * (epsP ρ + ‖mom L v₁‖ + kc⁻¹ + riemannRate 2 (2 * π / L))
        ≤ K * (epsP ρ + epsP ρ + kc⁻¹ + 52 * π * epsP ρ) := by gcongr
      _ ≤ K * ((2 + 52 * π) * (epsP ρ + kc⁻¹)) := by
          gcongr
          nlinarith [mul_nonneg hπ.le hkc]
      _ = K * (2 + 52 * π) * (ρ ^ (1/200 : ℝ) + kc⁻¹) := by
          rw [mul_assoc]
          rfl
  have hmain : |(L ^ 3)⁻¹ * -(∑' v₂ : Idx, if v₂ ≠ 0 ∧ mom L v₂ ∈ Sums_A ρ kc (mom L v₁) then
        (fun p => (ft V p).re) (mom L v₂) *
          ((fun p => (ft (gfun V w) p).re) (mom L v₂) / ‖mom L v₂‖ ^ 2) else 0) + normVw V w| =
      |(L ^ 3)⁻¹ * (∑' v₂ : Idx, if v₂ ≠ 0 ∧ mom L v₂ ∈ Sums_A ρ kc (mom L v₁) then
        (fun p => (ft V p).re) (mom L v₂) *
          ((fun p => (ft (gfun V w) p).re) (mom L v₂) / ‖mom L v₂‖ ^ 2) else 0) - normVw V w| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [hmain]
  exact hb.trans hfin

/-! ### The sums over the cases (8.3) and (8.4) -/

/-- The summands of `OneLeg_term` at nonzero legs factor as `V_{v₂}` times an `a4` term. -/
private lemma Sums_term_eq (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) {v₁ v₂ : Idx} (h₁ : v₁ ≠ 0)
    (h₂ : v₂ ≠ 0) (h₃ : v₁ - v₂ ≠ 0) (β : Occ) :
    OneLeg_term L V Ψ (v₁, v₂, β) =
      ft V (mom L v₂) * (conj (Ψ (a4 0 v₁ v₂ (v₁ - v₂) β).2) *
        ((a4 0 v₁ v₂ (v₁ - v₂) β).1 : ℂ) * Ψ β) := by
  unfold OneLeg_term
  rw [ite_eq_left ⟨h₁, h₂, h₃⟩]
  ring

/-- `Σ_β ‖term(v₁, v₂, β)‖ = |V_{v₂}| · absA` at nonzero legs. -/
private lemma Sums_sum_norm_term (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) {v₁ v₂ : Idx} (h₁ : v₁ ≠ 0)
    (h₂ : v₂ ≠ 0) (h₃ : v₁ - v₂ ≠ 0) :
    ∑' β : Occ, ‖OneLeg_term L V Ψ (v₁, v₂, β)‖ =
      ‖ft V (mom L v₂)‖ * OneLeg_absA Ψ v₁ v₂ (v₁ - v₂) := by
  unfold OneLeg_absA
  rw [← tsum_mul_left]
  refine tsum_congr fun β => ?_
  rw [Sums_term_eq L V Ψ h₁ h₂ h₃, norm_mul, norm_mul, norm_mul, RCLike.norm_conj,
    Complex.norm_real, Real.norm_of_nonneg (a4_fst_nonneg _ _ _ _ _), mul_assoc]

/-- The three legs of the cases (8.2)–(8.4) are nonzero. -/
private lemma Sums_case2_ne {ρ L kc : ℝ} (hρ : 0 < ρ) {v₁ v₂ : Idx}
    (h : OneLeg_case2 ρ L kc v₁ v₂) : v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ - v₂ ≠ 0 := by
  rcases h with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  · exact ⟨Regions_PH_ne_zero hρ h₁.1, Regions_PL_ne_zero hρ h₂, Regions_PH_ne_zero hρ h₃.1⟩
  · exact ⟨Regions_PH_ne_zero hρ h₁.1, Regions_PH_ne_zero hρ h₂.1, Regions_PL_ne_zero hρ h₃⟩

private lemma Sums_case3_ne {ρ L : ℝ} (hρ : 0 < ρ) {v₁ v₂ : Idx}
    (h : OneLeg_case3 ρ L v₁ v₂) : v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ - v₂ ≠ 0 :=
  ⟨Regions_PL_ne_zero hρ h.1, Regions_PL_ne_zero hρ h.2.1, Regions_PL_ne_zero hρ h.2.2⟩

private lemma Sums_case1_ne {ρ L kc : ℝ} (hρ : 0 < ρ) {v₁ v₂ : Idx}
    (h : OneLeg_case1 ρ L kc v₁ v₂) : v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ - v₂ ≠ 0 :=
  ⟨Regions_PL_ne_zero hρ h.1, Regions_PH_ne_zero hρ h.2.1.1, Regions_PH_ne_zero hρ h.2.2.1⟩

/-- (8.15) [0resultsecondcase] of Lemma 8.3 with a rate uniform in `k_c`. -/
theorem Lemma8_3_second {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ *
          (∑' i : Idx × Idx × Occ, (if OneLeg_case2 (rhoN N) (LN N) kc i.1 i.2.1 then
            ‖OneLeg_term (LN N) V (trialState V w kc N) i‖ else 0)) ≤
        C * rhoN N ^ (1/2 : ℝ) := by
  obtain ⟨C31, hC31, N31, h31⟩ := Eq8_31 hV hw
  obtain ⟨K', hK', N', hcard⟩ := Sums_cardPL
  obtain ⟨Kg, hKg, hgt⟩ := sum_norm_rpow_gt (s := 4) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 ((eventually_ge_atTop 1).and
    (Sums_ev_L.and (Sums_ev_rho_ge (a := -(25/24 : ℝ) + 1/200) (by norm_num) (2 * π))))
  set V₀ : ℝ := ∫ x, V x with hV₀
  have hV₀0 : 0 ≤ V₀ := integral_nonneg hV.nonneg
  refine ⟨2 * K' * V₀ * C31 * Kg, by positivity, max (max N31 N') N₁, fun N hN kc => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN31, hN'⟩, hN₁'⟩ := hN
  obtain ⟨hN1, hL2, hLε⟩ := hN₁ N hN₁'
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨F, hF, hFcard⟩ := hcard N hN'
  have hΨ := Normalization_isNState V w kc hN1
  have hε : 0 < epsP (rhoN N) := Sums_eps_pos hρ
  set Ψ := trialState V w kc N with hΨdef
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  have hΛ : 0 < L ^ 3 := by positivity
  have hterm := OneLeg_summable L V N Ψ (OneLeg_summable_V hV hL2) hΨ
  set g : Idx × Idx × Occ → ℝ := fun i =>
    if OneLeg_case2 ρ L kc i.1 i.2.1 then ‖OneLeg_term L V Ψ i‖ else 0 with hg
  have hgs : Summable g := Summable.of_nonneg_of_le (fun i => by simp only [hg]; split_ifs <;> simp)
    (fun i => by simp only [hg]; split_ifs <;> simp) hterm
  obtain ⟨e1, -, hsum1, -⟩ := Sums_fubini g hgs
  change ρ ^ (-(5/2 : ℝ)) * ((L ^ 3) ^ 2)⁻¹ * (∑' i, g i) ≤ _
  rw [e1]
  -- the per-pair bound
  set B : Idx → ℝ := fun v₁ => (V₀ * C31 * ρ ^ (2 - 1/10 : ℝ)) *
    (if epsP ρ < ‖mom L v₁‖ then ‖mom L v₁‖ ^ (-(4 : ℝ)) else 0) with hB
  have hpair : ∀ v₁ v₂ : Idx, (0 ≤ ∑' β, g (v₁, v₂, β)) ∧
      (¬ OneLeg_case2 ρ L kc v₁ v₂ → ∑' β, g (v₁, v₂, β) = 0) ∧
      (OneLeg_case2 ρ L kc v₁ v₂ → ∑' β, g (v₁, v₂, β) ≤ B v₁) := by
    intro v₁ v₂
    refine ⟨tsum_nonneg fun β => by simp only [hg]; split_ifs <;> simp, fun hc => ?_, fun hc => ?_⟩
    · simp only [hg, hc, ite_false]
      exact tsum_zero
    · obtain ⟨h₁, h₂, h₃⟩ := Sums_case2_ne hρ hc
      have e : ∑' β, g (v₁, v₂, β) = ∑' β : Occ, ‖OneLeg_term L V Ψ (v₁, v₂, β)‖ := by
        simp only [hg, hc, ite_true]
      rw [e, Sums_sum_norm_term L V Ψ h₁ h₂ h₃]
      have hvε : epsP ρ < ‖mom L v₁‖ := by
        rcases hc with ⟨a, -, -⟩ | ⟨a, -, -⟩ <;> exact a.1
      have hv₁ : 0 < ‖mom L v₁‖ := hε.trans hvε
      have habs := h31 N hN31 kc v₁ v₂ hc
      have hft : ‖ft V (mom L v₂)‖ ≤ V₀ := scat_ft_V_norm_le hV _
      have hneg : ‖mom L v₁‖ ^ (-(4 : ℝ)) = 1 / ‖mom L v₁‖ ^ 4 := by
        rw [Real.rpow_neg hv₁.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
      simp only [hB, hvε, ite_true, hneg]
      calc ‖ft V (mom L v₂)‖ * OneLeg_absA Ψ v₁ v₂ (v₁ - v₂)
          ≤ V₀ * (C31 * ρ ^ (2 - 1/10 : ℝ) / ‖mom L v₁‖ ^ 4) := by
            have h0 : 0 ≤ OneLeg_absA Ψ v₁ v₂ (v₁ - v₂) := by
              unfold OneLeg_absA
              exact tsum_nonneg fun β => by
                have := a4_fst_nonneg 0 v₁ v₂ (v₁ - v₂) β
                positivity
            exact mul_le_mul hft habs h0 hV₀0
        _ = _ := by ring
  -- the sum over `v₂` for fixed `v₁`
  have hinner : ∀ v₁ : Idx, ∑' v₂, ∑' β, g (v₁, v₂, β) ≤ (2 * F.card) * B v₁ := by
    intro v₁
    have hB0 : 0 ≤ B v₁ := by
      simp only [hB]
      split_ifs <;> positivity
    by_cases hvε : epsP ρ < ‖mom L v₁‖
    · set S : Finset Idx := F ∪ F.image (fun x => v₁ - x) with hS
      have hzero : ∀ v₂ ∉ S, ∑' β, g (v₁, v₂, β) = 0 := by
        intro v₂ hv₂
        refine (hpair v₁ v₂).2.1 fun hc => hv₂ ?_
        rcases hc with ⟨-, h2, -⟩ | ⟨-, -, h3⟩
        · exact Finset.mem_union_left _ (hF _ h2)
        · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨v₁ - v₂, hF _ h3, ?_⟩)
          simp
      rw [tsum_eq_sum hzero]
      have hSc : (S.card : ℝ) ≤ 2 * F.card := by
        have h1 : S.card ≤ F.card + (F.image (fun x => v₁ - x)).card := Finset.card_union_le _ _
        have h2 : (F.image (fun x => v₁ - x)).card ≤ F.card := Finset.card_image_le
        have : S.card ≤ 2 * F.card := by omega
        exact_mod_cast this
      calc ∑ v₂ ∈ S, ∑' β, g (v₁, v₂, β) ≤ S.card • B v₁ := by
            refine Finset.sum_le_card_nsmul _ _ _ fun v₂ _ => ?_
            by_cases hc : OneLeg_case2 ρ L kc v₁ v₂
            · exact (hpair v₁ v₂).2.2 hc
            · rw [(hpair v₁ v₂).2.1 hc]
              exact hB0
        _ = (S.card : ℝ) * B v₁ := by rw [nsmul_eq_mul]
        _ ≤ (2 * F.card) * B v₁ := mul_le_mul_of_nonneg_right hSc hB0
    · have hz : ∀ v₂, ∑' β, g (v₁, v₂, β) = 0 := by
        intro v₂
        refine (hpair v₁ v₂).2.1 fun hc => hvε ?_
        rcases hc with ⟨a, -, -⟩ | ⟨a, -, -⟩ <;> exact a.1
      simp only [hz, tsum_zero]
      positivity
  -- the sum over `v₁`
  obtain ⟨hgts, hgtb⟩ := hgt (L) (epsP ρ) hε (by
    have e : L * epsP ρ = ρ ^ (-(25/24 : ℝ) + 1/200) := by
      rw [hLdef, LN, epsP, ← Real.rpow_add hρ]
    rw [e]
    exact hLε)
  have hBs : Summable B := by
    have := hgts.mul_left (V₀ * C31 * ρ ^ (2 - 1/10 : ℝ))
    exact this
  have hS2 : ∑' v₁, ∑' v₂, ∑' β, g (v₁, v₂, β) ≤
      (2 * F.card) * ((V₀ * C31 * ρ ^ (2 - 1/10 : ℝ)) *
        (Kg * epsP ρ ^ (3 - 4 : ℝ) * L ^ 3)) := by
    calc ∑' v₁, ∑' v₂, ∑' β, g (v₁, v₂, β) ≤ ∑' v₁, (2 * F.card) * B v₁ :=
          hsum1.tsum_le_tsum hinner (hBs.mul_left _)
      _ = (2 * F.card) * ∑' v₁, B v₁ := tsum_mul_left
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          simp only [hB]
          rw [tsum_mul_left]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h := hgtb
          rw [inv_mul_le_iff₀ hΛ] at h
          have e : ∑' n : Idx, (if epsP ρ < ‖mom L n‖ then ‖mom L n‖ ^ (-(4 : ℝ)) else 0) ≤
              Kg * epsP ρ ^ (3 - 4 : ℝ) * L ^ 3 := by linarith [h]
          exact e
  -- the final arithmetic
  have hFc : (F.card : ℝ) ≤ K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3 := hFcard
  have hexp : (epsP ρ) ^ (3 - 4 : ℝ) = ρ ^ (-(1/200 : ℝ)) := by
    rw [epsP, ← Real.rpow_mul hρ.le]
    norm_num
  have hpow : ρ ^ (-(5/2 : ℝ)) * (ρ ^ (3/2 - 3/200 : ℝ) * (ρ ^ (2 - 1/10 : ℝ) *
      ρ ^ (-(1/200 : ℝ)))) = ρ ^ (22/25 : ℝ) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  have hρ' : ρ ^ (22/25 : ℝ) ≤ ρ ^ (1/2 : ℝ) := Sums_rpow_mono hρ hρ1 (by norm_num)
  have hC0 : 0 ≤ 2 * K' * V₀ * C31 * Kg := by positivity
  calc ρ ^ (-(5/2 : ℝ)) * ((L ^ 3) ^ 2)⁻¹ * ∑' v₁, ∑' v₂, ∑' β, g (v₁, v₂, β)
      ≤ ρ ^ (-(5/2 : ℝ)) * ((L ^ 3) ^ 2)⁻¹ * ((2 * (K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3)) *
        ((V₀ * C31 * ρ ^ (2 - 1/10 : ℝ)) * (Kg * ρ ^ (-(1/200 : ℝ)) * L ^ 3))) := by
        rw [← hexp]
        refine mul_le_mul_of_nonneg_left (hS2.trans ?_) (by positivity)
        gcongr
    _ = (2 * K' * V₀ * C31 * Kg) * (ρ ^ (-(5/2 : ℝ)) * (ρ ^ (3/2 - 3/200 : ℝ) *
        (ρ ^ (2 - 1/10 : ℝ) * ρ ^ (-(1/200 : ℝ))))) := by
        field_simp
    _ = (2 * K' * V₀ * C31 * Kg) * ρ ^ (22/25 : ℝ) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hρ' hC0

/-- In case (8.4), a coincidence `v_i = ±v_j` is one of `v₂ = -v₁`, `v₂ = 2 v₁`, `v₁ = 2 v₂`:
the others force a zero leg. -/
private lemma Sums_special {v₁ v₂ : Idx} (h₁ : v₁ ≠ 0) (h₂ : v₂ ≠ 0) (h₃ : v₁ - v₂ ≠ 0)
    (h : ¬ (Legs_pm v₁ v₂ ∧ Legs_pm v₁ (v₁ - v₂) ∧ Legs_pm v₂ (v₁ - v₂))) :
    v₂ = -v₁ ∨ v₂ = v₁ + v₁ ∨ v₁ = v₂ + v₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3⟩ := hcon
  apply h
  unfold Legs_pm
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro e
    apply h₃
    rw [e, sub_self]
  · intro e
    apply c1
    rw [e, neg_neg]
  · intro e
    exact h₂ (sub_eq_self.1 e.symm)
  · intro e
    apply c2
    linear_combination -e
  · intro e
    apply c3
    linear_combination -e
  · intro e
    apply h₁
    linear_combination e

/-- (8.16) [0resultthirdcase] of Lemma 8.3, with the cases (8.32), with a rate uniform in
`k_c`. -/
theorem Lemma8_3_third {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ *
          (∑' i : Idx × Idx × Occ, (if OneLeg_case3 (rhoN N) (LN N) i.1 i.2.1 then
            ‖OneLeg_term (LN N) V (trialState V w kc N) i‖ else 0)) ≤
        C * rhoN N ^ (1/2 : ℝ) := by
  obtain ⟨C34, hC34, N34, h34⟩ := Eq8_34 hV hw
  obtain ⟨K', hK', N', hcard⟩ := Sums_cardPL
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 ((eventually_ge_atTop 1).and Sums_ev_L)
  set V₀ : ℝ := ∫ x, V x with hV₀
  have hV₀0 : 0 ≤ V₀ := integral_nonneg hV.nonneg
  refine ⟨K' ^ 2 * V₀ * C34 + 12 * K' * V₀, by positivity, max (max N34 N') N₁, fun N hN kc => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN34, hN'⟩, hN₁'⟩ := hN
  obtain ⟨hN1, hL2⟩ := hN₁ N hN₁'
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨F, hF, hFcard⟩ := hcard N hN'
  have hΨ := Normalization_isNState V w kc hN1
  have hΛeq := Sums_Lcube hN1
  have hNeq := Sums_N_eq hN1
  set Ψ := trialState V w kc N with hΨdef
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  have hΛ : 0 < L ^ 3 := by positivity
  have hterm := OneLeg_summable L V N Ψ (OneLeg_summable_V hV hL2) hΨ
  set g : Idx × Idx × Occ → ℝ := fun i =>
    if OneLeg_case3 ρ L i.1 i.2.1 then ‖OneLeg_term L V Ψ i‖ else 0 with hg
  have hgs : Summable g := Summable.of_nonneg_of_le (fun i => by simp only [hg]; split_ifs <;> simp)
    (fun i => by simp only [hg]; split_ifs <;> simp) hterm
  obtain ⟨e1, -, hsum1, -⟩ := Sums_fubini g hgs
  change ρ ^ (-(5/2 : ℝ)) * ((L ^ 3) ^ 2)⁻¹ * (∑' i, g i) ≤ _
  rw [e1]
  set b₁ : ℝ := V₀ * (C34 * ρ ^ (1 - 1/10 : ℝ)) with hb₁
  set b₂ : ℝ := V₀ * (Real.sqrt N * (mc ρ + 1) ^ (3/2 : ℝ)) with hb₂
  have hb₁0 : 0 ≤ b₁ := by positivity
  have hb₂0 : 0 ≤ b₂ := by
    have : 0 ≤ mc ρ + 1 := by unfold mc; positivity
    positivity
  set T3 : Finset (Idx × Idx) := F.image (fun x => (x, -x)) ∪ F.image (fun x => (x, x + x)) ∪
    F.image (fun x => (x + x, x)) with hT3
  have hpair : ∀ v₁ v₂ : Idx, (0 ≤ ∑' β, g (v₁, v₂, β)) ∧
      (¬ OneLeg_case3 ρ L v₁ v₂ → ∑' β, g (v₁, v₂, β) = 0) ∧
      (OneLeg_case3 ρ L v₁ v₂ →
        ∑' β, g (v₁, v₂, β) ≤ b₁ + (if (v₁, v₂) ∈ T3 then b₂ else 0)) := by
    intro v₁ v₂
    refine ⟨tsum_nonneg fun β => by simp only [hg]; split_ifs <;> simp, fun hc => ?_, fun hc => ?_⟩
    · simp only [hg, hc, ite_false]
      exact tsum_zero
    · obtain ⟨h₁, h₂, h₃⟩ := Sums_case3_ne hρ hc
      have e : ∑' β, g (v₁, v₂, β) = ∑' β : Occ, ‖OneLeg_term L V Ψ (v₁, v₂, β)‖ := by
        simp only [hg, hc, ite_true]
      rw [e, Sums_sum_norm_term L V Ψ h₁ h₂ h₃]
      have hft : ‖ft V (mom L v₂)‖ ≤ V₀ := scat_ft_V_norm_le hV _
      have h0 : 0 ≤ OneLeg_absA Ψ v₁ v₂ (v₁ - v₂) := by
        unfold OneLeg_absA
        exact tsum_nonneg fun β => by
          have := a4_fst_nonneg 0 v₁ v₂ (v₁ - v₂) β
          positivity
      have hge : ‖ft V (mom L v₂)‖ * OneLeg_absA Ψ v₁ v₂ (v₁ - v₂) ≤
          V₀ * OneLeg_absA Ψ v₁ v₂ (v₁ - v₂) := mul_le_mul_of_nonneg_right hft h0
      by_cases hgen : Legs_pm v₁ v₂ ∧ Legs_pm v₁ (v₁ - v₂) ∧ Legs_pm v₂ (v₁ - v₂)
      · have hab := h34 N hN34 kc v₁ v₂ hc hgen.1 hgen.2.1 hgen.2.2
        have : ‖ft V (mom L v₂)‖ * OneLeg_absA Ψ v₁ v₂ (v₁ - v₂) ≤ b₁ :=
          hge.trans (mul_le_mul_of_nonneg_left hab hV₀0)
        refine this.trans ?_
        split_ifs <;> linarith
      · have hab := Eq8_32 V w kc hN1 hc.1 hc.2.1 hc.2.2
        have h1 : ‖ft V (mom L v₂)‖ * OneLeg_absA Ψ v₁ v₂ (v₁ - v₂) ≤ b₂ :=
          hge.trans (mul_le_mul_of_nonneg_left hab hV₀0)
        have hmem : (v₁, v₂) ∈ T3 := by
          rcases Sums_special h₁ h₂ h₃ hgen with e | e | e
          · refine Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_image.2 ⟨v₁, hF _ hc.1, ?_⟩))
            rw [e]
          · refine Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_image.2 ⟨v₁, hF _ hc.1, ?_⟩))
            rw [e]
          · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨v₂, hF _ hc.2.1, ?_⟩)
            rw [e]
        rw [ite_eq_left hmem]
        linarith
  -- the double sum is a finite sum over `F × F`
  have hinner0 : ∀ v₁ : Idx, v₁ ∉ F → ∑' v₂, ∑' β, g (v₁, v₂, β) = 0 := by
    intro v₁ hv₁
    have : ∀ v₂, ∑' β, g (v₁, v₂, β) = 0 := fun v₂ =>
      (hpair v₁ v₂).2.1 fun hc => hv₁ (hF _ hc.1)
    simp only [this, tsum_zero]
  have hinner : ∀ v₁ : Idx, ∑' v₂, ∑' β, g (v₁, v₂, β) = ∑ v₂ ∈ F, ∑' β, g (v₁, v₂, β) := by
    intro v₁
    refine tsum_eq_sum fun v₂ hv₂ => (hpair v₁ v₂).2.1 fun hc => hv₂ (hF _ hc.2.1)
  have hdouble : ∑' v₁, ∑' v₂, ∑' β, g (v₁, v₂, β) =
      ∑ p ∈ F ×ˢ F, ∑' β, g (p.1, p.2, β) := by
    rw [Finset.sum_product]
    rw [tsum_eq_sum (s := F) (fun v₁ hv₁ => hinner0 v₁ hv₁)]
    exact Finset.sum_congr rfl fun v₁ _ => hinner v₁
  have hsumF : ∑ p ∈ F ×ˢ F, ∑' β, g (p.1, p.2, β) ≤
      (F.card : ℝ) ^ 2 * b₁ + (T3.card : ℝ) * b₂ := by
    calc ∑ p ∈ F ×ˢ F, ∑' β, g (p.1, p.2, β)
        ≤ ∑ p ∈ F ×ˢ F, (b₁ + (if p ∈ T3 then b₂ else 0)) := by
          refine Finset.sum_le_sum fun p hp => ?_
          by_cases hc : OneLeg_case3 ρ L p.1 p.2
          · exact (hpair p.1 p.2).2.2 hc
          · rw [(hpair p.1 p.2).2.1 hc]
            split_ifs <;> linarith
      _ = (F.card : ℝ) ^ 2 * b₁ + ∑ p ∈ F ×ˢ F, (if p ∈ T3 then b₂ else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_product, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ (F.card : ℝ) ^ 2 * b₁ + (T3.card : ℝ) * b₂ := by
          refine add_le_add le_rfl ?_
          rw [Finset.sum_ite_mem]
          calc ∑ p ∈ F ×ˢ F ∩ T3, b₂ ≤ ∑ p ∈ T3, b₂ :=
                Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
                  (fun _ _ _ => hb₂0)
            _ = (T3.card : ℝ) * b₂ := by rw [Finset.sum_const, nsmul_eq_mul]
  have hT3c : (T3.card : ℝ) ≤ 3 * F.card := by
    have h1 : T3.card ≤ F.card + F.card + F.card := by
      calc T3.card ≤ (F.image (fun x => (x, -x)) ∪ F.image (fun x => (x, x + x))).card +
            (F.image (fun x => (x + x, x))).card := Finset.card_union_le _ _
        _ ≤ ((F.image (fun x => (x, -x))).card + (F.image (fun x => (x, x + x))).card) +
            (F.image (fun x => (x + x, x))).card := by
            gcongr
            exact Finset.card_union_le _ _
        _ ≤ F.card + F.card + F.card := by
            gcongr <;> exact Finset.card_image_le
    have : (T3.card : ℝ) ≤ ((F.card + F.card + F.card : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    linarith
  rw [hdouble]
  -- the final arithmetic
  have hFc : (F.card : ℝ) ≤ K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3 := hFcard
  have hF0 : (0 : ℝ) ≤ F.card := Nat.cast_nonneg _
  have hFq : (F.card : ℝ) ^ 2 ≤ K' ^ 2 * ρ ^ (3 - 3/100 : ℝ) * (L ^ 3) ^ 2 := by
    have := pow_le_pow_left₀ hF0 hFc 2
    refine this.trans (le_of_eq ?_)
    have e : (ρ ^ (3/2 - 3/200 : ℝ)) ^ 2 = ρ ^ (3 - 3/100 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
      norm_num
    calc (K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3) ^ 2 =
        K' ^ 2 * (ρ ^ (3/2 - 3/200 : ℝ)) ^ 2 * (L ^ 3) ^ 2 := by ring
      _ = _ := by rw [e]
  -- the exponents of `b₂`
  have hmc : mc ρ ^ (3/2 : ℝ) = ρ ^ (-(3/400 : ℝ)) := by
    rw [mc, ← Real.rpow_mul hρ.le]
    norm_num
  have hmc1 : 1 ≤ mc ρ := by
    unfold mc
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  have hsq : Real.sqrt N = ρ ^ (-(17/16 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, hNeq, ← Real.rpow_mul hρ.le]
    norm_num
  have h232 : (2 : ℝ) ^ (3/2 : ℝ) ≤ 4 := by
    calc (2 : ℝ) ^ (3/2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have hb₂le : b₂ ≤ 4 * V₀ * ρ ^ (-(17/16 : ℝ) - 3/400) := by
    have h1 : (mc ρ + 1) ^ (3/2 : ℝ) ≤ 4 * ρ ^ (-(3/400 : ℝ)) := by
      calc (mc ρ + 1) ^ (3/2 : ℝ) ≤ (2 * mc ρ) ^ (3/2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
        _ = 2 ^ (3/2 : ℝ) * mc ρ ^ (3/2 : ℝ) := Real.mul_rpow (by norm_num) (by linarith)
        _ ≤ 4 * ρ ^ (-(3/400 : ℝ)) := by
            rw [hmc]
            gcongr
    have e : ρ ^ (-(17/16 : ℝ) - 3/400) = ρ ^ (-(17/16 : ℝ)) * ρ ^ (-(3/400 : ℝ)) := by
      rw [← Real.rpow_add hρ]
      ring_nf
    rw [e]
    simp only [hb₂, hsq]
    calc V₀ * (ρ ^ (-(17/16 : ℝ)) * (mc ρ + 1) ^ (3/2 : ℝ))
        ≤ V₀ * (ρ ^ (-(17/16 : ℝ)) * (4 * ρ ^ (-(3/400 : ℝ)))) := by gcongr
      _ = _ := by ring
  have hΛinv : (L ^ 3)⁻¹ = ρ ^ (25/8 : ℝ) := by
    rw [hΛeq, ← Real.rpow_neg hρ.le]
    norm_num
  have hΛ2 : ((L ^ 3) ^ 2)⁻¹ * (L ^ 3) ^ 2 = 1 := inv_mul_cancel₀ (by positivity)
  have hρ137 : ρ ^ (-(5/2 : ℝ)) * ρ ^ (3 - 3/100 : ℝ) * ρ ^ (1 - 1/10 : ℝ) = ρ ^ (137/100 : ℝ) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  have hρ104 : ρ ^ (-(5/2 : ℝ)) * (ρ ^ (3/2 - 3/200 : ℝ) * ρ ^ (-(17/16 : ℝ) - 3/400) *
      ρ ^ (25/8 : ℝ)) = ρ ^ (26/25 : ℝ) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  have h1' : ρ ^ (137/100 : ℝ) ≤ ρ ^ (1/2 : ℝ) := Sums_rpow_mono hρ hρ1 (by norm_num)
  have h2' : ρ ^ (26/25 : ℝ) ≤ ρ ^ (1/2 : ℝ) := Sums_rpow_mono hρ hρ1 (by norm_num)
  have hpow0 : ∀ a : ℝ, 0 ≤ ρ ^ a := fun a => Real.rpow_nonneg hρ.le a
  calc ρ ^ (-(5/2 : ℝ)) * ((L ^ 3) ^ 2)⁻¹ * ∑ p ∈ F ×ˢ F, ∑' β, g (p.1, p.2, β)
      ≤ ρ ^ (-(5/2 : ℝ)) * ((L ^ 3) ^ 2)⁻¹ *
        ((K' ^ 2 * ρ ^ (3 - 3/100 : ℝ) * (L ^ 3) ^ 2) * b₁ +
          (3 * (K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3)) * (4 * V₀ * ρ ^ (-(17/16 : ℝ) - 3/400))) := by
        refine mul_le_mul_of_nonneg_left (hsumF.trans ?_) (by positivity)
        refine add_le_add (mul_le_mul_of_nonneg_right hFq hb₁0) ?_
        calc (T3.card : ℝ) * b₂ ≤ (3 * F.card) * b₂ := mul_le_mul_of_nonneg_right hT3c hb₂0
          _ ≤ (3 * (K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3)) * b₂ := by gcongr
          _ ≤ _ := mul_le_mul_of_nonneg_left hb₂le (by positivity)
    _ = (K' ^ 2 * V₀ * C34) * (ρ ^ (-(5/2 : ℝ)) * ρ ^ (3 - 3/100 : ℝ) * ρ ^ (1 - 1/10 : ℝ)) +
        (12 * K' * V₀) * (ρ ^ (-(5/2 : ℝ)) * (ρ ^ (3/2 - 3/200 : ℝ) *
          ρ ^ (-(17/16 : ℝ) - 3/400) * ρ ^ (25/8 : ℝ))) := by
        rw [← hΛinv]
        have hΛ3 : ((L ^ 3) ^ 2)⁻¹ = (L ^ 3)⁻¹ * (L ^ 3)⁻¹ := by rw [sq, mul_inv]
        simp only [hb₁, hΛ3]
        field_simp
        ring
    _ = (K' ^ 2 * V₀ * C34) * ρ ^ (137/100 : ℝ) + (12 * K' * V₀) * ρ ^ (26/25 : ℝ) := by
        rw [hρ137, hρ104]
    _ ≤ (K' ^ 2 * V₀ * C34) * ρ ^ (1/2 : ℝ) + (12 * K' * V₀) * ρ ^ (1/2 : ℝ) := by
        gcongr
    _ = _ := by ring

/-! ### The sum over the case (8.2) -/

/-- A family on `Idx` supported on a lattice ball is summable. -/
private lemma Sums_summable_fin {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {L kc : ℝ}
    (hL : 0 < L) (G : Idx → E) (hG : ∀ v : Idx, G v ≠ 0 → ‖mom L v‖ ≤ kc) : Summable G := by
  have hfin := Sums_finite_ball (L := L) (R := kc) hL
  exact summable_of_ne_finset_zero (s := hfin.toFinset) fun v hv => by
    by_contra h
    exact hv (hfin.mem_toFinset.2 (hG v h))

/-- The sum over the case (8.2) of Lemma 8.1 is the main term `Σ_{v₁ ∈ P_L} 2 Q_Ψ(0, v₁)` times
the inner sum of (8.27), plus an error controlled by the per-pair bound `Eb`. -/
private lemma Sums_first_decomp {V w : R3 → ℝ} (hV : PotentialHyp V) (kc : ℝ) {N : ℕ}
    (hN : 1 ≤ N) (hL2 : 2 * π ≤ LN N) (F : Finset Idx)
    (hF : ∀ n : Idx, inPL (rhoN N) (LN N) n → n ∈ F) (Eb : Idx → ℝ) (hEb0 : ∀ v, 0 ≤ Eb v)
    (hEb : ∀ v₁ v₂ : Idx, OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂ →
      ‖OneLeg_expA (trialState V w kc N) v₁ v₂ (v₁ - v₂) -
        ((2 * lam V w (rhoN N) (LN N) v₂ * Expect.Q (trialState V w kc N) [0, v₁] /
          LN N ^ 3 : ℝ) : ℂ)‖ ≤ Eb v₁) :
    ∃ m : Idx → ℝ, ∃ d : Idx → ℂ,
      (∑' i : Idx × Idx × Occ, (if OneLeg_case1 (rhoN N) (LN N) kc i.1 i.2.1 then
            OneLeg_term (LN N) V (trialState V w kc N) i else 0)) =
        ((∑' v₁, m v₁ : ℝ) : ℂ) + ∑' v₁, d v₁ ∧
      (∀ v₁, v₁ ∉ F → m v₁ = 0) ∧ (∀ v₁, v₁ ∉ F → d v₁ = 0) ∧
      (∀ v₁, m v₁ = if inPL (rhoN N) (LN N) v₁ then
          2 * Expect.Q (trialState V w kc N) [0, v₁] * ((LN N ^ 3)⁻¹ *
            ∑' v₂ : Idx, (if inPHc (rhoN N) (LN N) kc v₂ ∧ inPHc (rhoN N) (LN N) kc (v₁ - v₂)
              then (ft V (mom (LN N) v₂)).re * lam V w (rhoN N) (LN N) v₂ else 0)) else 0) ∧
      (∀ v₁, ‖d v₁‖ ≤ (if inPL (rhoN N) (LN N) v₁ then Eb v₁ else 0) *
        ∑' v₂ : Idx, ‖ft V (mom (LN N) v₂)‖) := by
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  set Ψ := trialState V w kc N with hΨdef
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  have hsV := OneLeg_summable_V hV hL2
  have hterm := OneLeg_summable L V N Ψ hsV hΨ
  set f : Idx × Idx × Occ → ℂ := fun i =>
    if OneLeg_case1 ρ L kc i.1 i.2.1 then OneLeg_term L V Ψ i else 0 with hf
  have hfs : Summable f := Summable.of_norm (Summable.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun i => by simp only [hf]; split_ifs <;> simp) hterm)
  obtain ⟨e1, -, -, -⟩ := Sums_fubini f hfs
  set P : Idx → Idx → ℂ := fun v₁ v₂ =>
    if OneLeg_case1 ρ L kc v₁ v₂ then ft V (mom L v₂) * OneLeg_expA Ψ v₁ v₂ (v₁ - v₂) else 0
    with hP
  have hPfib : ∀ v₁ v₂, ∑' β, f (v₁, v₂, β) = P v₁ v₂ := by
    intro v₁ v₂
    by_cases hc : OneLeg_case1 ρ L kc v₁ v₂
    · obtain ⟨h₁, h₂, h₃⟩ := Sums_case1_ne hρ hc
      simp only [hf, hP, hc, ite_true]
      rw [tsum_congr (Sums_term_eq L V Ψ h₁ h₂ h₃), tsum_mul_left]
      rfl
    · simp only [hf, hP, hc, ite_false, tsum_zero]
  have hS1 : ∑' i, f i = ∑' v₁, ∑' v₂, P v₁ v₂ := by
    rw [e1]
    exact tsum_congr fun v₁ => tsum_congr fun v₂ => hPfib v₁ v₂
  -- the main part and the remainder
  set Mn : Idx → Idx → ℂ := fun v₁ v₂ =>
    if OneLeg_case1 ρ L kc v₁ v₂ then ft V (mom L v₂) *
      ((2 * lam V w ρ L v₂ * Expect.Q Ψ [0, v₁] / L ^ 3 : ℝ) : ℂ) else 0 with hMn
  set D : Idx → Idx → ℂ := fun v₁ v₂ => P v₁ v₂ - Mn v₁ v₂ with hD
  have hsupp : ∀ v₁ v₂, ¬ OneLeg_case1 ρ L kc v₁ v₂ → P v₁ v₂ = 0 ∧ Mn v₁ v₂ = 0 := by
    intro v₁ v₂ hc
    exact ⟨by simp [hP, hc], by simp [hMn, hc]⟩
  have hball : ∀ v₁ v₂, OneLeg_case1 ρ L kc v₁ v₂ → ‖mom L v₂‖ ≤ kc := fun v₁ v₂ hc => hc.2.1.2
  have hPs : ∀ v₁, Summable (P v₁) := fun v₁ => Sums_summable_fin hL _ fun v₂ h => by
    by_contra h'
    exact h (hsupp v₁ v₂ fun hc => h' (hball v₁ v₂ hc)).1
  have hMs : ∀ v₁, Summable (Mn v₁) := fun v₁ => Sums_summable_fin hL _ fun v₂ h => by
    by_contra h'
    exact h (hsupp v₁ v₂ fun hc => h' (hball v₁ v₂ hc)).2
  have hDs : ∀ v₁, Summable (D v₁) := fun v₁ => (hPs v₁).sub (hMs v₁)
  have hsplit : ∀ v₁, ∑' v₂, P v₁ v₂ = (∑' v₂, Mn v₁ v₂) + ∑' v₂, D v₁ v₂ := by
    intro v₁
    rw [← (hMs v₁).tsum_add (hDs v₁)]
    exact tsum_congr fun v₂ => by simp [hD]
  have hnoF : ∀ v₁, v₁ ∉ F → ∀ v₂, ¬ OneLeg_case1 ρ L kc v₁ v₂ := fun v₁ hv₁ v₂ hc => hv₁ (hF _ hc.1)
  have hm'0 : ∀ v₁, v₁ ∉ F → ∑' v₂, Mn v₁ v₂ = 0 := fun v₁ hv₁ => by
    simp only [fun v₂ => (hsupp v₁ v₂ (hnoF v₁ hv₁ v₂)).2, tsum_zero]
  have hd0 : ∀ v₁, v₁ ∉ F → ∑' v₂, D v₁ v₂ = 0 := fun v₁ hv₁ => by
    simp only [hD, fun v₂ => (hsupp v₁ v₂ (hnoF v₁ hv₁ v₂)).1,
      fun v₂ => (hsupp v₁ v₂ (hnoF v₁ hv₁ v₂)).2, sub_zero, tsum_zero]
  have hm's : Summable fun v₁ => ∑' v₂, Mn v₁ v₂ :=
    summable_of_ne_finset_zero (s := F) fun v₁ hv₁ => hm'0 v₁ hv₁
  have hds : Summable fun v₁ => ∑' v₂, D v₁ v₂ :=
    summable_of_ne_finset_zero (s := F) fun v₁ hv₁ => hd0 v₁ hv₁
  -- the real main term
  set G : Idx → Idx → ℝ := fun v₁ v₂ =>
    if inPHc ρ L kc v₂ ∧ inPHc ρ L kc (v₁ - v₂) then (ft V (mom L v₂)).re * lam V w ρ L v₂
    else 0 with hG
  set m : Idx → ℝ := fun v₁ => if inPL ρ L v₁ then
    2 * Expect.Q Ψ [0, v₁] * ((L ^ 3)⁻¹ * ∑' v₂, G v₁ v₂) else 0 with hm
  have hmeq : ∀ v₁, ∑' v₂, Mn v₁ v₂ = ((m v₁ : ℝ) : ℂ) := by
    intro v₁
    by_cases hPL : inPL ρ L v₁
    · have hpt : ∀ v₂, Mn v₁ v₂ = (((2 * Expect.Q Ψ [0, v₁] / L ^ 3) * G v₁ v₂ : ℝ) : ℂ) := by
        intro v₂
        by_cases hcond : inPHc ρ L kc v₂ ∧ inPHc ρ L kc (v₁ - v₂)
        · have hc : OneLeg_case1 ρ L kc v₁ v₂ := ⟨hPL, hcond⟩
          have hGv : G v₁ v₂ = (ft V (mom L v₂)).re * lam V w ρ L v₂ := by
            simp only [hG]
            exact ite_eq_left hcond
          have hMv : Mn v₁ v₂ = (((ft V (mom L v₂)).re : ℝ) : ℂ) *
              ((2 * lam V w ρ L v₂ * Expect.Q Ψ [0, v₁] / L ^ 3 : ℝ) : ℂ) := by
            simp only [hMn]
            rw [ite_eq_left hc]
            exact congrArg (· * _) (scat_ft_V_real hV _)
          rw [hMv, hGv]
          push_cast
          ring
        · have hc : ¬ OneLeg_case1 ρ L kc v₁ v₂ := fun h => hcond ⟨h.2.1, h.2.2⟩
          simp [hMn, hG, hc, hcond]
      simp only [hpt]
      rw [← Complex.ofReal_tsum, tsum_mul_left]
      simp only [hm, hPL, ite_true]
      congr 1
      ring
    · have : ∀ v₂, Mn v₁ v₂ = 0 := fun v₂ => (hsupp v₁ v₂ fun h => hPL h.1).2
      simp [this, hm, hPL]
  refine ⟨m, fun v₁ => ∑' v₂, D v₁ v₂, ?_, ?_, hd0, fun v₁ => rfl, ?_⟩
  · show ∑' i, f i = _
    rw [hS1, tsum_congr hsplit, (hm's.tsum_add hds), tsum_congr hmeq, Complex.ofReal_tsum]
  · intro v₁ hv₁
    have h := hm'0 v₁ hv₁
    rw [hmeq] at h
    exact_mod_cast h
  · intro v₁
    have hsn : Summable fun v₂ => ‖D v₁ v₂‖ := Sums_summable_fin hL _ fun v₂ h => by
      by_contra h'
      have := (hsupp v₁ v₂ fun hc => h' (hball v₁ v₂ hc))
      apply h
      simp [hD, this.1, this.2]
    have hterm' : ∀ v₂, ‖D v₁ v₂‖ ≤ (if inPL ρ L v₁ then Eb v₁ else 0) * ‖ft V (mom L v₂)‖ := by
      intro v₂
      by_cases hc : OneLeg_case1 ρ L kc v₁ v₂
      · have hDe : D v₁ v₂ = ft V (mom L v₂) * (OneLeg_expA Ψ v₁ v₂ (v₁ - v₂) -
            ((2 * lam V w ρ L v₂ * Expect.Q Ψ [0, v₁] / L ^ 3 : ℝ) : ℂ)) := by
          simp only [hD, hP, hMn, hc, ite_true]
          ring
        rw [hDe, norm_mul, ite_eq_left hc.1, mul_comm]
        exact mul_le_mul_of_nonneg_right (hEb v₁ v₂ hc) (norm_nonneg _)
      · have := hsupp v₁ v₂ hc
        simp only [hD, this.1, this.2, sub_zero, norm_zero]
        split_ifs <;> exact mul_nonneg (by first | exact hEb0 _ | exact le_rfl) (norm_nonneg _)
    calc ‖∑' v₂, D v₁ v₂‖ ≤ ∑' v₂, ‖D v₁ v₂‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' v₂, (if inPL ρ L v₁ then Eb v₁ else 0) * ‖ft V (mom L v₂)‖ :=
          hsn.tsum_le_tsum hterm' (hsV.mul_left _)
      _ = _ := tsum_mul_left

/-- The normalized total `ρ^{-5/2} |Λ|⁻² Σ_{P_L} Q_Ψ(0, v₁)` is `g₀^{3/2}/(3π²)` up to
`κ² ρ^{1/2} + C ρ^{1/400}`, from (8.29) and `ρ₀(ρ - ρ₀) = κ ρ^{5/2} - κ² ρ³`. -/
private lemma Sums_cT {ρ g X C : ℝ} (hρ : 0 < ρ)
    (hX : |X - rho0 g ρ * (ρ - rho0 g ρ)| ≤ C * ρ ^ (5/2 + 1/400 : ℝ)) :
    |ρ ^ (-(5/2 : ℝ)) * X - g ^ (3/2 : ℝ) / (3 * π ^ 2)| ≤
      (g ^ (3/2 : ℝ) / (3 * π ^ 2)) ^ 2 * ρ ^ (1/2 : ℝ) + C * ρ ^ (1/400 : ℝ) := by
  set κ : ℝ := g ^ (3/2 : ℝ) / (3 * π ^ 2) with hκ
  have hρ52 : 0 < ρ ^ (5/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have h1 : ρ ^ (-(5/2 : ℝ)) * ρ ^ (5/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hρ]
    norm_num
  have h2 : ρ ^ (5/2 : ℝ) = ρ * ρ ^ (3/2 : ℝ) := by
    rw [show (5/2 : ℝ) = 1 + 3/2 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have h3 : ρ ^ (3/2 : ℝ) * ρ ^ (3/2 : ℝ) = ρ ^ (5/2 : ℝ) * ρ ^ (1/2 : ℝ) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  have h4 : ρ ^ (5/2 + 1/400 : ℝ) = ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ) :=
    Real.rpow_add hρ _ _
  have hρ0 : rho0 g ρ = ρ - κ * ρ ^ (3/2 : ℝ) := by
    unfold rho0
    rw [hκ]
    ring
  have hmain : ρ ^ (-(5/2 : ℝ)) * (rho0 g ρ * (ρ - rho0 g ρ)) = κ - κ ^ 2 * ρ ^ (1/2 : ℝ) := by
    rw [hρ0]
    have e : (ρ - κ * ρ ^ (3/2 : ℝ)) * (ρ - (ρ - κ * ρ ^ (3/2 : ℝ))) =
        κ * (ρ * ρ ^ (3/2 : ℝ)) - κ ^ 2 * (ρ ^ (3/2 : ℝ) * ρ ^ (3/2 : ℝ)) := by ring
    rw [e, ← h2, h3]
    linear_combination (κ - κ ^ 2 * ρ ^ (1/2 : ℝ)) * h1
  have e : ρ ^ (-(5/2 : ℝ)) * X - κ =
      ρ ^ (-(5/2 : ℝ)) * (X - rho0 g ρ * (ρ - rho0 g ρ)) - κ ^ 2 * ρ ^ (1/2 : ℝ) := by
    have := hmain
    linear_combination this
  rw [e]
  calc |ρ ^ (-(5/2 : ℝ)) * (X - rho0 g ρ * (ρ - rho0 g ρ)) - κ ^ 2 * ρ ^ (1/2 : ℝ)|
      ≤ |ρ ^ (-(5/2 : ℝ)) * (X - rho0 g ρ * (ρ - rho0 g ρ))| + |κ ^ 2 * ρ ^ (1/2 : ℝ)| :=
        abs_sub _ _
    _ ≤ C * ρ ^ (1/400 : ℝ) + κ ^ 2 * ρ ^ (1/2 : ℝ) := by
        have hr : 0 ≤ ρ ^ (1/2 : ℝ) := Real.rpow_nonneg hρ.le _
        rw [abs_of_nonneg (by positivity : 0 ≤ κ ^ 2 * ρ ^ (1/2 : ℝ))]
        refine add_le_add ?_ le_rfl
        rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hρ.le _)]
        calc ρ ^ (-(5/2 : ℝ)) * |X - rho0 g ρ * (ρ - rho0 g ρ)|
            ≤ ρ ^ (-(5/2 : ℝ)) * (C * ρ ^ (5/2 + 1/400 : ℝ)) :=
              mul_le_mul_of_nonneg_left hX (Real.rpow_nonneg hρ.le _)
          _ = C * ρ ^ (1/400 : ℝ) := by
              rw [h4]
              linear_combination (C * ρ ^ (1/400 : ℝ)) * h1
    _ = _ := by ring

/-- The exponent bookkeeping for the error of (8.26) summed over the pairs (8.2). -/
private lemma Sums_err_arith {ρ Λ cV cp K κ C₅ : ℝ} (hρ : 0 < ρ) (hΛ : 0 < Λ) :
    ρ ^ (-(5/2 : ℝ)) * (Λ ^ 2)⁻¹ * (cV * Λ * (cp * ρ ^ (2 - 1/40 : ℝ) *
        (K * ρ ^ (3/2 - 3/200 : ℝ) * Λ) + 4 * ρ ^ (4/3 : ℝ) *
          (Λ * ((κ + C₅) * ρ ^ (3/2 : ℝ))))) =
      cV * cp * K * ρ ^ (24/25 : ℝ) + 4 * cV * (κ + C₅) * ρ ^ (1/3 : ℝ) := by
  have h1 : ρ ^ (-(5/2 : ℝ)) * (ρ ^ (2 - 1/40 : ℝ) * ρ ^ (3/2 - 3/200 : ℝ)) =
      ρ ^ (24/25 : ℝ) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  have h2 : ρ ^ (-(5/2 : ℝ)) * (ρ ^ (4/3 : ℝ) * ρ ^ (3/2 : ℝ)) = ρ ^ (1/3 : ℝ) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  have e : ρ ^ (-(5/2 : ℝ)) * (Λ ^ 2)⁻¹ * (cV * Λ * (cp * ρ ^ (2 - 1/40 : ℝ) *
        (K * ρ ^ (3/2 - 3/200 : ℝ) * Λ) + 4 * ρ ^ (4/3 : ℝ) *
          (Λ * ((κ + C₅) * ρ ^ (3/2 : ℝ))))) =
      cV * cp * K * (ρ ^ (-(5/2 : ℝ)) * (ρ ^ (2 - 1/40 : ℝ) * ρ ^ (3/2 - 3/200 : ℝ))) +
        4 * cV * (κ + C₅) * (ρ ^ (-(5/2 : ℝ)) * (ρ ^ (4/3 : ℝ) * ρ ^ (3/2 : ℝ))) := by
    field_simp
  rw [e, h1, h2]

/-- `|Σ m + a Σ q| ≤ B Σ q` when `|m + a q| ≤ B q` pointwise and `m`, `q ≥ 0` are supported in
`F`. -/
private lemma Sums_main_bound {m q : Idx → ℝ} (F : Finset Idx) (hm0 : ∀ v, v ∉ F → m v = 0)
    (hq0 : ∀ v, v ∉ F → q v = 0) (a B : ℝ) (hpt : ∀ v, |m v + a * q v| ≤ B * q v) :
    |(∑' v, m v) + a * ∑' v, q v| ≤ B * ∑' v, q v := by
  have hms : Summable m := summable_of_ne_finset_zero (s := F) hm0
  have hqs : Summable q := summable_of_ne_finset_zero (s := F) hq0
  have hmq : (∑' v, m v) + a * ∑' v, q v = ∑' v, (m v + a * q v) := by
    rw [hms.tsum_add (hqs.mul_left _), tsum_mul_left]
  have hsn : Summable fun v => |m v + a * q v| :=
    summable_of_ne_finset_zero (s := F) (fun v hv => by simp [hm0 v hv, hq0 v hv])
  rw [hmq]
  calc |∑' v, (m v + a * q v)| ≤ ∑' v, |m v + a * q v| := by
        simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm
          (f := fun v => m v + a * q v) (by simpa only [Real.norm_eq_abs] using hsn)
    _ ≤ ∑' v, B * q v := hsn.tsum_le_tsum hpt (hqs.mul_left _)
    _ = B * ∑' v, q v := tsum_mul_left

/-- The bound for `Σ_v ‖d v‖` from a pointwise bound supported in `F`. -/
private lemma Sums_err_bound {d : Idx → ℂ} {E : Idx → ℝ} {P : Idx → Prop} (F : Finset Idx)
    (hd0 : ∀ v, v ∉ F → d v = 0) (hP : ∀ v, P v → v ∈ F) (hE0 : ∀ v, 0 ≤ E v) (J B : ℝ)
    (hJ0 : 0 ≤ J) (hdb : ∀ v, ‖d v‖ ≤ (if P v then E v else 0) * J) (hJ : J ≤ B) :
    ‖∑' v, d v‖ ≤ B * ∑' v, (if P v then E v else 0) := by
  have hdsn : Summable fun v => ‖d v‖ :=
    summable_of_ne_finset_zero (s := F) (fun v hv => by simp [hd0 v hv])
  have hEs : Summable fun v => (if P v then E v else 0) :=
    summable_of_ne_finset_zero (s := F) (fun v hv => by rw [ite_eq_right (fun h => hv (hP _ h))])
  have hB0 : 0 ≤ B := hJ0.trans hJ
  calc ‖∑' v, d v‖ ≤ ∑' v, ‖d v‖ := norm_tsum_le_tsum_norm hdsn
    _ ≤ ∑' v, B * (if P v then E v else 0) := by
        refine hdsn.tsum_le_tsum (fun v => ?_) (hEs.mul_left _)
        refine (hdb v).trans ?_
        have hE : 0 ≤ (if P v then E v else 0) := by
          split_ifs
          · exact hE0 _
          · exact le_rfl
        calc (if P v then E v else 0) * J ≤ (if P v then E v else 0) * B :=
              mul_le_mul_of_nonneg_left hJ hE
          _ = _ := by ring
    _ = _ := tsum_mul_left

/-- `Σ_{v ∈ P} (c₀ + c₁ Q v) ≤ |F| c₀ + c₁ Σ_{v ∈ P} Q v` for `P ⊆ F`. -/
private lemma Sums_Eb_sum {P : Idx → Prop} (F : Finset Idx) (hP : ∀ v, P v → v ∈ F)
    (c₀ c₁ : ℝ) (hc₀ : 0 ≤ c₀) (Q : Idx → ℝ) :
    ∑' v, (if P v then c₀ + c₁ * Q v else 0) ≤
      F.card * c₀ + c₁ * ∑' v, (if P v then Q v else 0) := by
  have hs : ∀ f : Idx → ℝ, Summable fun v => (if P v then f v else 0) := fun f =>
    summable_of_ne_finset_zero (s := F) (fun v hv => by rw [ite_eq_right (fun h => hv (hP _ h))])
  have hpt : ∀ v, (if P v then c₀ + c₁ * Q v else 0) =
      (if P v then c₀ else 0) + c₁ * (if P v then Q v else 0) := by
    intro v
    by_cases h : P v <;> simp [h]
  have hcs : ∑' v : Idx, (if P v then c₀ else 0) ≤ F.card * c₀ := by
    rw [tsum_eq_sum (s := F) (fun v hv => by rw [ite_eq_right (fun h => hv (hP _ h))])]
    calc ∑ v ∈ F, (if P v then c₀ else 0) ≤ F.card • c₀ :=
          Finset.sum_le_card_nsmul _ _ _ fun v _ => by split_ifs <;> first | exact le_rfl | exact hc₀
      _ = _ := by rw [nsmul_eq_mul]
  rw [tsum_congr hpt, (hs fun _ => c₀).tsum_add ((hs Q).mul_left _), tsum_mul_left]
  exact add_le_add hcs le_rfl

/-- (8.14) [0resultfirstcase] of Lemma 8.3 with a rate uniform in `k_c ≥ 1`. -/
theorem Lemma8_3_first {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc →
      ‖((rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ : ℝ) : ℂ) *
          (∑' i : Idx × Idx × Occ, (if OneLeg_case1 (rhoN N) (LN N) kc i.1 i.2.1 then
            OneLeg_term (LN N) V (trialState V w kc N) i else 0)) -
        ((-2 * normVw V w * (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2)) : ℝ) : ℂ)‖ ≤
        C * (rhoN N ^ (1/400 : ℝ) + kc⁻¹) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C₂₉, hC₂₉, N₂₉, h₂₉⟩ := Eq8_29 hg
  obtain ⟨Cs, hCs, Ns, hs⟩ := OneLeg_shell hV hw
  obtain ⟨Cp, hCp, Np, hp⟩ := OneLeg_pair_first hV hw
  obtain ⟨C₅, hC₅, N₅, h₅⟩ := Prop5_4_PL hg
  obtain ⟨K', hK', N', hcard⟩ := Sums_cardPL
  obtain ⟨CV, hCV⟩ := scat_lattice_V hV
  have hCV0 : 0 ≤ CV := by
    obtain ⟨-, h⟩ := hCV 1 le_rfl
    have : 0 ≤ ∑' n : Idx, ‖ft V (mom 1 n)‖ := tsum_nonneg fun _ => norm_nonneg _
    simp only [one_pow, inv_one, one_mul] at h
    linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 ((eventually_ge_atTop 1).and Sums_ev_L)
  set κ : ℝ := g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) with hκ
  set Vw : ℝ := normVw V w with hVw
  have hκ0 : 0 ≤ κ := by
    have := scat_g0_pos hV hw
    positivity
  have hVw0 : 0 ≤ Vw := integral_nonneg fun x => abs_nonneg _
  set W : ℝ := κ + κ ^ 2 + C₂₉ with hW
  refine ⟨2 * Vw * κ ^ 2 + 2 * Vw * C₂₉ + 2 * Cs * W + CV * Cp * K' + 4 * CV * (κ + C₅),
    by positivity, max (max (max N₂₉ Ns) (max Np N₅)) (max N' N₁), fun N hN kc hkc => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hN₂₉, hNs⟩, ⟨hNp, hN₅⟩⟩, ⟨hN', hN₁'⟩⟩ := hN
  obtain ⟨hN1, hL2⟩ := hN₁ N hN₁'
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨F, hF, hFcard⟩ := hcard N hN'
  have hL1 : 1 ≤ LN N := by linarith [Real.pi_gt_three]
  have hAm := h₂₉ N hN₂₉ kc
  have hA5 := h₅ N hN₅ kc
  set Ψ := trialState V w kc N with hΨdef
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  have hΛ : 0 < L ^ 3 := by positivity
  -- the per-pair error bound
  set Eb : Idx → ℝ := fun v₁ => Cp * ρ ^ (2 - 1/40 : ℝ) + 4 * ρ ^ (4/3 : ℝ) * Expect.Q Ψ [v₁]
    with hEb
  have hEb0 : ∀ v, 0 ≤ Eb v := fun v => by
    have := Sums_Q_single_nonneg Ψ v
    simp only [hEb]
    positivity
  obtain ⟨m, d, hS, hm0, hd0, hmdef, hdb⟩ :=
    Sums_first_decomp hV kc hN1 hL2 F hF Eb hEb0 (fun v₁ v₂ hc => hp N hNp kc v₁ v₂ hc)
  rw [hS]
  -- the weights `Q_Ψ(0, v₁)` on `P_L`
  set q : Idx → ℝ := fun v₁ => if inPL ρ L v₁ then Expect.Q Ψ [0, v₁] else 0 with hq
  have hq0 : ∀ v, 0 ≤ q v := fun v => by
    simp only [hq]
    split_ifs
    · exact Sums_Q_pair_nonneg _ _ _
    · exact le_rfl
  have hqF : ∀ v, v ∉ F → q v = 0 := fun v hv => by
    simp only [hq]
    rw [ite_eq_right (fun h => hv (hF _ h))]
  set T : ℝ := ∑' v₁, q v₁ with hT
  have hT0 : 0 ≤ T := tsum_nonneg hq0
  -- the main term against `-2 ‖Vw‖₁ T`
  have hB2 : |(∑' v₁, m v₁) + 2 * Vw * T| ≤ 2 * Cs * (ρ ^ (1/200 : ℝ) + kc⁻¹) * T := by
    refine Sums_main_bound F hm0 hqF (2 * Vw) _ (fun v₁ => ?_)
    by_cases hPL : inPL ρ L v₁
    · have hq1 : q v₁ = Expect.Q Ψ [0, v₁] := by simp only [hq, hPL, ite_true]
      rw [hmdef v₁, ite_eq_left hPL, hq1]
      have hsh := hs N hNs kc hkc v₁ hPL
      have hQ0 := Sums_Q_pair_nonneg Ψ 0 v₁
      set I := ∑' v₂ : Idx, (if inPHc ρ L kc v₂ ∧ inPHc ρ L kc (v₁ - v₂) then
        (ft V (mom L v₂)).re * lam V w ρ L v₂ else 0) with hI
      have e : 2 * Expect.Q Ψ [0, v₁] * ((L ^ 3)⁻¹ * I) + 2 * Vw * Expect.Q Ψ [0, v₁] =
          2 * Expect.Q Ψ [0, v₁] * ((L ^ 3)⁻¹ * I + Vw) := by ring
      rw [e, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Expect.Q Ψ [0, v₁])]
      calc 2 * Expect.Q Ψ [0, v₁] * |(L ^ 3)⁻¹ * I + Vw|
          ≤ 2 * Expect.Q Ψ [0, v₁] * (Cs * (ρ ^ (1/200 : ℝ) + kc⁻¹)) :=
            mul_le_mul_of_nonneg_left hsh (by positivity)
        _ = _ := by ring
    · have hq1 : q v₁ = 0 := by simp only [hq, hPL, ite_false]
      rw [hmdef v₁, ite_eq_right hPL, hq1]
      simp
  -- the error term
  set T₁ : ℝ := ∑' v₁, (if inPL ρ L v₁ then Expect.Q Ψ [v₁] else 0) with hT₁
  have hJ : ∑' v₂ : Idx, ‖ft V (mom L v₂)‖ ≤ CV * L ^ 3 := by
    have h := (hCV L hL1).2
    rw [inv_mul_le_iff₀ hΛ] at h
    linarith
  have hCp' : 0 ≤ Cp * ρ ^ (2 - 1/40 : ℝ) := by positivity
  have hEbsum := Sums_Eb_sum (P := fun v => inPL ρ L v) F hF (Cp * ρ ^ (2 - 1/40 : ℝ))
    (4 * ρ ^ (4/3 : ℝ)) hCp' (fun v => Expect.Q Ψ [v])
  have hErr : ‖∑' v₁, d v₁‖ ≤ (CV * L ^ 3) *
      (F.card * (Cp * ρ ^ (2 - 1/40 : ℝ)) + 4 * ρ ^ (4/3 : ℝ) * T₁) :=
    (Sums_err_bound (P := fun v => inPL ρ L v) F hd0 hF hEb0 _ (CV * L ^ 3)
      (tsum_nonneg fun _ => norm_nonneg _) hdb hJ).trans
      (mul_le_mul_of_nonneg_left hEbsum (by positivity))
  -- the bound on `T₁` and on `|F|`
  have hT₁le : T₁ ≤ L ^ 3 * ((κ + C₅) * ρ ^ (3/2 : ℝ)) := by
    have h := hA5
    rw [inv_mul_le_iff₀ hΛ] at h
    have hρe : ρ ^ (1/200 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
    have h3 : C₅ * ρ ^ (1/200 : ℝ) ≤ C₅ := by
      calc C₅ * ρ ^ (1/200 : ℝ) ≤ C₅ * 1 := mul_le_mul_of_nonneg_left hρe hC₅
        _ = C₅ := mul_one _
    have : (κ + C₅ * ρ ^ (1/200 : ℝ)) * ρ ^ (3/2 : ℝ) ≤ (κ + C₅) * ρ ^ (3/2 : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hρ.le _)
    exact h.trans (mul_le_mul_of_nonneg_left this hΛ.le)
  have hFc : (F.card : ℝ) ≤ K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3 := hFcard
  have hErr2 : ‖∑' v₁, d v₁‖ ≤ ρ ^ (5/2 : ℝ) * (L ^ 3) ^ 2 *
      (CV * Cp * K' * ρ ^ (24/25 : ℝ) + 4 * CV * (κ + C₅) * ρ ^ (1/3 : ℝ)) := by
    refine hErr.trans ?_
    have h1 : (CV * L ^ 3) * (F.card * (Cp * ρ ^ (2 - 1/40 : ℝ)) + 4 * ρ ^ (4/3 : ℝ) * T₁) ≤
        (CV * L ^ 3) * (Cp * ρ ^ (2 - 1/40 : ℝ) * (K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3) +
          4 * ρ ^ (4/3 : ℝ) * (L ^ 3 * ((κ + C₅) * ρ ^ (3/2 : ℝ)))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine add_le_add ?_ (mul_le_mul_of_nonneg_left hT₁le (by positivity))
      calc (F.card : ℝ) * (Cp * ρ ^ (2 - 1/40 : ℝ)) ≤
          (K' * ρ ^ (3/2 - 3/200 : ℝ) * L ^ 3) * (Cp * ρ ^ (2 - 1/40 : ℝ)) :=
            mul_le_mul_of_nonneg_right hFc hCp'
        _ = _ := by ring
    refine h1.trans (le_of_eq ?_)
    have hcalc := Sums_err_arith (ρ := ρ) (Λ := L ^ 3) (cV := CV) (cp := Cp) (K := K') (κ := κ)
      (C₅ := C₅) hρ hΛ
    have hρ52 : 0 < ρ ^ (5/2 : ℝ) := Real.rpow_pos_of_pos hρ _
    have hneg : ρ ^ (-(5/2 : ℝ)) = (ρ ^ (5/2 : ℝ))⁻¹ := Real.rpow_neg hρ.le _
    rw [hneg] at hcalc
    rw [← hcalc]
    field_simp
  -- the arithmetic
  have hcT := Sums_cT (ρ := ρ) (g := g0 V w) (X := ((L ^ 3) ^ 2)⁻¹ * T) (C := C₂₉) hρ hAm
  have hρ12 : ρ ^ (1/2 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hρ400 : ρ ^ (1/400 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hρ0 : ∀ a : ℝ, 0 ≤ ρ ^ a := fun a => Real.rpow_nonneg hρ.le a
  have hmono : ∀ a : ℝ, 1/400 ≤ a → ρ ^ a ≤ ρ ^ (1/400 : ℝ) := fun a ha =>
    Sums_rpow_mono hρ hρ1 ha
  have hcT0 : 0 ≤ ρ ^ (-(5/2 : ℝ)) * (((L ^ 3) ^ 2)⁻¹ * T) := by positivity
  have hcTle : ρ ^ (-(5/2 : ℝ)) * (((L ^ 3) ^ 2)⁻¹ * T) ≤ W := by
    have h := (abs_le.1 hcT).2
    have : κ ^ 2 * ρ ^ (1/2 : ℝ) ≤ κ ^ 2 := by
      calc κ ^ 2 * ρ ^ (1/2 : ℝ) ≤ κ ^ 2 * 1 := by gcongr
        _ = κ ^ 2 := mul_one _
    have h2 : C₂₉ * ρ ^ (1/400 : ℝ) ≤ C₂₉ := by
      calc C₂₉ * ρ ^ (1/400 : ℝ) ≤ C₂₉ * 1 := by gcongr
        _ = C₂₉ := mul_one _
    simp only [hW]
    linarith
  -- assemble
  set c : ℝ := ρ ^ (-(5/2 : ℝ)) * ((L ^ 3) ^ 2)⁻¹ with hc
  have hc0 : 0 ≤ c := by positivity
  set Mm : ℝ := ∑' v₁, m v₁ with hMm
  set Err : ℂ := ∑' v₁, d v₁ with hErrdef
  have hsplit : (c : ℂ) * ((Mm : ℂ) + Err) - ((-2 * Vw * κ : ℝ) : ℂ) =
      (((c * Mm - (-2 * Vw * κ) : ℝ)) : ℂ) + (c : ℂ) * Err := by
    push_cast
    ring
  rw [hsplit]
  have hcMm : |c * Mm - (-2 * Vw * κ)| ≤ 2 * Cs * (ρ ^ (1/200 : ℝ) + kc⁻¹) * W +
      2 * Vw * (κ ^ 2 * ρ ^ (1/2 : ℝ) + C₂₉ * ρ ^ (1/400 : ℝ)) := by
    have e : c * Mm - (-2 * Vw * κ) =
        c * (Mm + 2 * Vw * T) - 2 * Vw * (ρ ^ (-(5/2 : ℝ)) * (((L ^ 3) ^ 2)⁻¹ * T) - κ) := by
      simp only [hc]
      ring
    rw [e]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg hc0]
      calc c * |Mm + 2 * Vw * T| ≤ c * (2 * Cs * (ρ ^ (1/200 : ℝ) + kc⁻¹) * T) :=
            mul_le_mul_of_nonneg_left hB2 hc0
        _ = 2 * Cs * (ρ ^ (1/200 : ℝ) + kc⁻¹) * (ρ ^ (-(5/2 : ℝ)) * (((L ^ 3) ^ 2)⁻¹ * T)) := by
            simp only [hc]
            ring
        _ ≤ 2 * Cs * (ρ ^ (1/200 : ℝ) + kc⁻¹) * W :=
            mul_le_mul_of_nonneg_left hcTle (by positivity)
    · rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Vw)]
      exact mul_le_mul_of_nonneg_left hcT (by positivity)
  have hcErr : c * ‖Err‖ ≤ CV * Cp * K' * ρ ^ (24/25 : ℝ) +
      4 * CV * (κ + C₅) * ρ ^ (1/3 : ℝ) := by
    calc c * ‖Err‖ ≤ c * (ρ ^ (5/2 : ℝ) * (L ^ 3) ^ 2 *
          (CV * Cp * K' * ρ ^ (24/25 : ℝ) + 4 * CV * (κ + C₅) * ρ ^ (1/3 : ℝ))) :=
          mul_le_mul_of_nonneg_left hErr2 hc0
      _ = _ := by
          have h1 : ρ ^ (-(5/2 : ℝ)) * ρ ^ (5/2 : ℝ) = 1 := by
            rw [← Real.rpow_add hρ]
            norm_num
          simp only [hc]
          field_simp
          linear_combination (CV * Cp * K' * ρ ^ (24/25 : ℝ) + 4 * CV * (κ + C₅) * ρ ^ (1/3 : ℝ))
            * h1
  calc ‖(((c * Mm - (-2 * Vw * κ) : ℝ)) : ℂ) + (c : ℂ) * Err‖
      ≤ ‖(((c * Mm - (-2 * Vw * κ) : ℝ)) : ℂ)‖ + ‖(c : ℂ) * Err‖ := norm_add_le _ _
    _ = |c * Mm - (-2 * Vw * κ)| + c * ‖Err‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hc0]
    _ ≤ (2 * Cs * (ρ ^ (1/200 : ℝ) + kc⁻¹) * W +
          2 * Vw * (κ ^ 2 * ρ ^ (1/2 : ℝ) + C₂₉ * ρ ^ (1/400 : ℝ))) +
        (CV * Cp * K' * ρ ^ (24/25 : ℝ) + 4 * CV * (κ + C₅) * ρ ^ (1/3 : ℝ)) :=
        add_le_add hcMm hcErr
    _ ≤ _ := by
        have h12 := hmono (1/2) (by norm_num)
        have h200 := hmono (1/200) (by norm_num)
        have h2425 := hmono (24/25) (by norm_num)
        have h13 := hmono (1/3) (by norm_num)
        have hkc0 : 0 ≤ kc⁻¹ := inv_nonneg.2 (by linarith)
        have hW0 : 0 ≤ W := by simp only [hW]; positivity
        set X : ℝ := ρ ^ (1/400 : ℝ) with hX
        set Y : ℝ := kc⁻¹ with hY
        have hX0 : 0 ≤ X := hρ0 _
        have t1 : 2 * Cs * (ρ ^ (1/200 : ℝ) + Y) * W ≤ 2 * Cs * (X + Y) * W := by gcongr
        have t2 : 2 * Vw * (κ ^ 2 * ρ ^ (1/2 : ℝ) + C₂₉ * X) ≤ 2 * Vw * (κ ^ 2 * X + C₂₉ * X) := by
          gcongr
        have t3 : CV * Cp * K' * ρ ^ (24/25 : ℝ) + 4 * CV * (κ + C₅) * ρ ^ (1/3 : ℝ) ≤
            CV * Cp * K' * X + 4 * CV * (κ + C₅) * X := by gcongr
        have t4 : 0 ≤ (2 * Vw * κ ^ 2 + 2 * Vw * C₂₉ + CV * Cp * K' + 4 * CV * (κ + C₅)) * Y := by
          positivity
        linarith [t1, t2, t3, t4]

end LHYUpper
