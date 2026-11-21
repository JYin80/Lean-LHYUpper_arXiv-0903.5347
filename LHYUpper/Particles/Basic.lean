module

public import LHYUpper.Fock.Expect
public import LHYUpper.TrialState.Normalization
public import LHYUpper.Scattering.Solution

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # Basic particle-number identities and bounds for the trial state

Collects the elementary facts behind §5 for the trial state: `ρ_N L_N³ = N`, the bounds on `λ_k` of
(5.9) [ublambda] and (5.10) off and on `P_L`, sums of occupation numbers over `Idx` against `|Ψ|²`,
the identity `Σ_u Q_Ψ(u) = N` behind (5.32) [resultlbpsi0], the first identity of (5.18) [4], the
event form of Proposition 5.5 [prop6], and the identity (5.62) [temp6.56] for `Q_Ψ(0, 0)`. -/

/-- `ρ_N L_N³ = N`, `0 < ρ_N ≤ 1` and `0 < L_N` for `N ≥ 1`. -/
theorem Particles_rhoN_LN {N : ℕ} (hN : 1 ≤ N) :
    rhoN N * LN N ^ 3 = N ∧ 0 < rhoN N ∧ rhoN N ≤ 1 ∧ 0 < LN N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hρ : 0 < rhoN N := Real.rpow_pos_of_pos hNpos _
  have hL : LN N = (N : ℝ) ^ (25 / 51 : ℝ) := by
    rw [LN, rhoN, ← Real.rpow_mul hNpos.le]
    norm_num
  refine ⟨?_, hρ, ?_, ?_⟩
  · rw [hL, rhoN, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    norm_num
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  · rw [hL]
    exact Real.rpow_pos_of_pos hNpos _

/-- `|Re ĝ(p)| ≤ ∫ |g|` for every `V`, `w`. -/
private theorem Particles_abs_re_ft_le (V w : R3 → ℝ) (p : R3) :
    |(ft (gfun V w) p).re| ≤ ∫ x, |gfun V w x| := by
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold ft
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- Off `P_L`, `|λ_k| ≤ ‖g‖₁ |k|⁻²` for every `V`, `w`, (5.9) [ublambda] with `‖g‖₁`. -/
theorem Particles_lam_abs_le (V w : R3 → ℝ) (ρ L : ℝ) (n : Idx) (h : ¬ inPL ρ L n) :
    |lam V w ρ L n| ≤ (∫ x, |gfun V w x|) / ‖mom L n‖ ^ 2 := by
  have h0 := Particles_abs_re_ft_le V w (mom L n)
  simp only [lam, h, ↓reduceIte]
  rw [abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ ‖mom L n‖ ^ 2)]
  exact div_le_div_of_nonneg_right h0 (by positivity)

/-- On `P_L`, `-1 < ρλ_k < 0` with `1 + ρλ_k ≥ ε_L / (1 + √g₀)`, (5.9) [ublambda], (5.10). -/
theorem Particles_rho_lam_PL {V w : R3 → ℝ} (hg : 0 < g0 V w) {ρ L : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {n : Idx} (hn : inPL ρ L n) :
    ρ * lam V w ρ L n < 0 ∧ epsP ρ / (1 + Real.sqrt (g0 V w)) ≤ 1 + ρ * lam V w ρ L n := by
  have hε0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hs0 : 0 < ρ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hsq : ρ ^ (1 / 2 : ℝ) * ρ ^ (1 / 2 : ℝ) = ρ := by
    rw [← Real.rpow_add hρ]
    norm_num
  have hlow : epsP ρ * ρ ^ (1 / 2 : ℝ) ≤ ‖mom L n‖ := hn.1
  have hu0 : 0 < ‖mom L n‖ := lt_of_lt_of_le (mul_pos hε0 hs0) hlow
  have hu2 : (epsP ρ) ^ 2 * ρ ≤ ‖mom L n‖ ^ 2 := by
    calc (epsP ρ) ^ 2 * ρ = (epsP ρ * ρ ^ (1 / 2 : ℝ)) ^ 2 := by
          rw [mul_pow, sq (ρ ^ (1 / 2 : ℝ)), hsq]
      _ ≤ ‖mom L n‖ ^ 2 := pow_le_pow_left₀ (by positivity) hlow 2
  have hq0 : 0 < 4 * ρ * g0 V w / ‖mom L n‖ ^ 2 := by positivity
  have hq : 4 * ρ * g0 V w / ‖mom L n‖ ^ 2 ≤ (2 * Real.sqrt (g0 V w) / epsP ρ) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hg.le]
    calc 4 * ρ * g0 V w / ‖mom L n‖ ^ 2 ≤ 4 * ρ * g0 V w / ((epsP ρ) ^ 2 * ρ) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hu2
      _ = 2 ^ 2 * g0 V w / epsP ρ ^ 2 := by
          field_simp
          norm_num
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (1 + 4 * ρ * g0 V w / ‖mom L n‖ ^ 2) := ⟨_, rfl⟩
  have hs1 : 1 < s := by
    rw [hs, Real.lt_sqrt (by norm_num)]
    linarith
  have hs2 : s ≤ 1 + 2 * Real.sqrt (g0 V w) / epsP ρ := by
    rw [hs, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : 0 ≤ 2 * Real.sqrt (g0 V w) / epsP ρ := by positivity
    nlinarith
  have hlam : ρ * lam V w ρ L n = (1 - s) / (1 + s) := by
    simp only [lam, hn, ↓reduceIte]
    rw [← hs]
    field_simp
  have hsp : 0 < 1 + s := by linarith
  refine ⟨?_, ?_⟩
  · rw [hlam]
    exact div_neg_of_neg_of_pos (by linarith) hsp
  · have h1 : 1 + ρ * lam V w ρ L n = 2 / (1 + s) := by
      rw [hlam]
      field_simp
      ring
    rw [h1, div_le_div_iff₀ (by positivity) hsp]
    have h2 : epsP ρ * s ≤ epsP ρ + 2 * Real.sqrt (g0 V w) := by
      have := mul_le_mul_of_nonneg_left hs2 hε0.le
      calc epsP ρ * s ≤ epsP ρ * (1 + 2 * Real.sqrt (g0 V w) / epsP ρ) := this
        _ = epsP ρ + 2 * Real.sqrt (g0 V w) := by field_simp
    nlinarith


section Sums

variable {N : ℕ} {Ψ : Occ → ℂ}

/-- `Σ_n α(n) = α.num`. -/
private theorem Particles_hasSum_occ (α : Occ) : HasSum (fun n : Idx => (α n : ℝ)) (α.num : ℝ) := by
  have h : HasSum (fun n : Idx => (α n : ℝ)) (∑ n ∈ α.support, (α n : ℝ)) :=
    hasSum_sum_of_ne_finset_zero (fun b hb => by simp [Finsupp.notMem_support_iff.mp hb])
  simpa [Occ.num, Finsupp.sum, Nat.cast_sum] using h

/-- `Σ_{n ≠ 0} α(n) = α.num − α(0)`. -/
private theorem Particles_hasSum_occ_ne (α : Occ) :
    HasSum (fun n : Idx => if n ≠ 0 then (α n : ℝ) else 0) ((α.num : ℝ) - α 0) := by
  have h := (Particles_hasSum_occ α).sub (hasSum_ite_eq (0 : Idx) (α 0 : ℝ))
  refine h.congr_fun ?_
  intro n
  by_cases hn : n = 0
  · subst hn
    simp
  · simp [hn]

/-- A bounded weight against `|Ψ|²` is summable. -/
private theorem Particles_summable_weight (hΨ : IsNState N Ψ) (h : Occ → ℝ) (C : ℝ)
    (hh : ∀ α, Ψ α ≠ 0 → |h α| ≤ C) : Summable fun α : Occ => h α * ‖Ψ α‖ ^ 2 := by
  refine Summable.of_norm_bounded (hΨ.1.summable.mul_left C) (fun α => ?_)
  rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
  by_cases hz : Ψ α = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hh α hz) (by positivity)

/-- Interchange of a sum over `Idx` and a sum over `Occ` for nonnegative terms. -/
private theorem Particles_hasSum_swap (a : Idx → Occ → ℝ) (s : Occ → ℝ) (ha : ∀ u α, 0 ≤ a u α)
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


/-- `α.num · |Ψ(α)|² = N |Ψ(α)|²` on an `N`-particle state. -/
private theorem Particles_num_mul (hΨ : IsNState N Ψ) (α : Occ) :
    (α.num : ℝ) * ‖Ψ α‖ ^ 2 = N * ‖Ψ α‖ ^ 2 := by
  by_cases hz : Ψ α = 0
  · simp [hz]
  · rw [hΨ.2 α hz]

/-- On the support of an `N`-particle state, every occupation number is at most `N`. -/
private theorem Particles_occ_le (hΨ : IsNState N Ψ) {α : Occ} (hz : Ψ α ≠ 0) (u : Idx) :
    (α u : ℝ) ≤ N := by
  have h := le_hasSum (Particles_hasSum_occ α) u (fun _ _ => by positivity)
  rwa [hΨ.2 α hz] at h

private theorem Particles_Q_single (Φ : Occ → ℂ) (u : Idx) :
    Expect.Q Φ [u] = ∑' α : Occ, (α u : ℝ) * ‖Φ α‖ ^ 2 := by
  simp [Expect.Q]

private theorem Particles_Q_pair (Φ : Occ → ℂ) (u v : Idx) :
    Expect.Q Φ [u, v] = ∑' α : Occ, (α u : ℝ) * (α v : ℝ) * ‖Φ α‖ ^ 2 := by
  simp [Expect.Q, mul_assoc]

private theorem Particles_hasSum_Q_aux (hΨ : IsNState N Ψ) :
    HasSum (fun n : Idx => Expect.Q Ψ [n]) N := by
  have key := Particles_hasSum_swap (fun u α => (α u : ℝ) * ‖Ψ α‖ ^ 2)
    (fun α => (N : ℝ) * ‖Ψ α‖ ^ 2) (fun u α => by positivity)
    (fun α => by
      have := (Particles_hasSum_occ α).mul_right (‖Ψ α‖ ^ 2)
      rwa [Particles_num_mul hΨ α] at this)
    (hΨ.1.summable.mul_left (N : ℝ))
  simpa [Particles_Q_single, tsum_mul_left, hΨ.1.tsum_eq] using key

private theorem Particles_Q_eq_tsum_aux (hΨ : IsNState N Ψ) (u : Idx) :
    Expect.Q Ψ [u] = ∑' m : ℕ, (m : ℝ) * Expect.Qm Ψ [(u, m)] := by
  have hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have hA : Summable fun α : Occ => (α u : ℝ) * ‖Ψ α‖ ^ 2 :=
    Particles_summable_weight hΨ (fun α => (α u : ℝ)) N
      (fun α hz => by rw [abs_of_nonneg (by positivity)]; exact Particles_occ_le hΨ hz u)
  let e : (Σ m : ℕ, {α : Occ // α u = m}) ≃ Occ := Equiv.sigmaFiberEquiv fun α : Occ => α u
  have hev : ∀ (m : ℕ) (α : Occ), Expect.Ev [(u, m)] α ↔ α u = m := by
    intro m α
    simp [Expect.Ev]
  have hfib : ∀ m : ℕ, HasSum (fun c : {α : Occ // α u = m} => ‖Ψ c.1‖ ^ 2)
      (Expect.Qm Ψ [(u, m)]) := by
    intro m
    have h1 : Summable (Set.indicator {α : Occ | α u = m} fun α : Occ => ‖Ψ α‖ ^ 2) :=
      hs.indicator _
    have h2 : HasSum (Set.indicator {α : Occ | α u = m} fun α : Occ => ‖Ψ α‖ ^ 2)
        (Expect.Qm Ψ [(u, m)]) := by
      have : Expect.Qm Ψ [(u, m)] =
          ∑' α, Set.indicator {α : Occ | α u = m} (fun α : Occ => ‖Ψ α‖ ^ 2) α := by
        unfold Expect.Qm
        refine tsum_congr fun α => ?_
        by_cases h : α u = m <;> simp [Set.indicator, hev, h]
      rw [this]
      exact h1.hasSum
    exact (hasSum_subtype_iff_indicator (f := fun α : Occ => ‖Ψ α‖ ^ 2)
      (s := {α : Occ | α u = m})).mpr h2
  have hall : HasSum (fun m : ℕ => (m : ℝ) * Expect.Qm Ψ [(u, m)]) (Expect.Q Ψ [u]) := by
    rw [Particles_Q_single]
    refine HasSum.sigma (f := fun x : (Σ m : ℕ, {α : Occ // α u = m}) =>
      (e x u : ℝ) * ‖Ψ (e x)‖ ^ 2) (e.hasSum_iff.mpr hA.hasSum) ?_
    intro m
    refine ((hfib m).mul_left (m : ℝ)).congr_fun ?_
    intro c
    have hc : c.1 u = m := c.2
    simp [e, hc]
  exact hall.tsum_eq.symm

private theorem Particles_event_aux (hΨ : IsNState N Ψ) (E : Occ → Prop) :
    (N : ℝ) * (∑' α : Occ, if E α then ‖Ψ α‖ ^ 2 else 0)
        - ((N : ℝ) - Expect.Q Ψ [0])
      ≤ ∑' α : Occ, if E α then (α 0 : ℝ) * ‖Ψ α‖ ^ 2 else 0 := by
  have hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have hA : Summable fun α : Occ => (α 0 : ℝ) * ‖Ψ α‖ ^ 2 :=
    Particles_summable_weight hΨ (fun α => (α 0 : ℝ)) N
      (fun α hz => by rw [abs_of_nonneg (by positivity)]; exact Particles_occ_le hΨ hz 0)
  have hsE : Summable fun α : Occ => if E α then ‖Ψ α‖ ^ 2 else 0 :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => by split_ifs <;> simp) hs
  have hsE' : Summable fun α : Occ => if E α then 0 else ‖Ψ α‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => by split_ifs <;> simp) hs
  have hAE : Summable fun α : Occ => if E α then (α 0 : ℝ) * ‖Ψ α‖ ^ 2 else 0 :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => by split_ifs <;> first | exact le_rfl | positivity) hA
  have hAE' : Summable fun α : Occ => if E α then 0 else (α 0 : ℝ) * ‖Ψ α‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => by split_ifs <;> first | exact le_rfl | positivity) hA
  have hP : (∑' α : Occ, if E α then ‖Ψ α‖ ^ 2 else 0) +
      (∑' α : Occ, if E α then 0 else ‖Ψ α‖ ^ 2) = 1 := by
    rw [← hsE.tsum_add hsE', ← hΨ.1.tsum_eq]
    exact tsum_congr fun α => by split_ifs <;> simp
  have hQ : (∑' α : Occ, if E α then (α 0 : ℝ) * ‖Ψ α‖ ^ 2 else 0) +
      (∑' α : Occ, if E α then 0 else (α 0 : ℝ) * ‖Ψ α‖ ^ 2) = Expect.Q Ψ [0] := by
    rw [← hAE.tsum_add hAE', Particles_Q_single]
    exact tsum_congr fun α => by split_ifs <;> simp
  have hB : (∑' α : Occ, if E α then 0 else (α 0 : ℝ) * ‖Ψ α‖ ^ 2) ≤
      N * (∑' α : Occ, if E α then 0 else ‖Ψ α‖ ^ 2) := by
    rw [← tsum_mul_left]
    refine hAE'.tsum_le_tsum (fun α => ?_) (hsE'.mul_left _)
    by_cases hE : E α
    · simp [hE]
    · by_cases hz : Ψ α = 0
      · simp [hE, hz]
      · simp only [hE, ↓reduceIte]
        exact mul_le_mul_of_nonneg_right (Particles_occ_le hΨ hz 0) (by positivity)
  have hN' : (N : ℝ) * (∑' α : Occ, if E α then 0 else ‖Ψ α‖ ^ 2) =
      N - N * (∑' α : Occ, if E α then ‖Ψ α‖ ^ 2 else 0) := by
    rw [show (∑' α : Occ, if E α then 0 else ‖Ψ α‖ ^ 2) =
      1 - ∑' α : Occ, if E α then ‖Ψ α‖ ^ 2 else 0 by linarith]
    ring
  linarith


private theorem Particles_hasSum_moments (hΨ : IsNState N Ψ) :
    HasSum (fun α : Occ => (α 0 : ℝ) * ‖Ψ α‖ ^ 2) (Expect.Q Ψ [0]) ∧
    HasSum (fun α : Occ => (α 0 : ℝ) * (α 0 : ℝ) * ‖Ψ α‖ ^ 2) (Expect.Q Ψ [0, 0]) := by
  refine ⟨?_, ?_⟩
  · rw [Particles_Q_single]
    exact (Particles_summable_weight hΨ (fun α => (α 0 : ℝ)) N
      (fun α hz => by rw [abs_of_nonneg (by positivity)]; exact Particles_occ_le hΨ hz 0)).hasSum
  · rw [Particles_Q_pair]
    refine (Particles_summable_weight hΨ (fun α => (α 0 : ℝ) * (α 0 : ℝ)) ((N : ℝ) * N)
      (fun α hz => ?_)).hasSum
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (Particles_occ_le hΨ hz 0) (Particles_occ_le hΨ hz 0) (by positivity)
      (by positivity)

private theorem Particles_Q00_ge_aux (hΨ : IsNState N Ψ) :
    Expect.Q Ψ [0] ^ 2 ≤ Expect.Q Ψ [0, 0] := by
  obtain ⟨h0, h00⟩ := Particles_hasSum_moments hΨ
  have h := (h00.sub (h0.mul_left (2 * Expect.Q Ψ [0]))).add
    (hΨ.1.mul_left (Expect.Q Ψ [0] ^ 2))
  have hnn := h.nonneg (fun α => by
    have e : (α 0 : ℝ) * (α 0 : ℝ) * ‖Ψ α‖ ^ 2 - 2 * Expect.Q Ψ [0] * ((α 0 : ℝ) * ‖Ψ α‖ ^ 2) +
        Expect.Q Ψ [0] ^ 2 * ‖Ψ α‖ ^ 2 = ((α 0 : ℝ) - Expect.Q Ψ [0]) ^ 2 * ‖Ψ α‖ ^ 2 := by ring
    rw [e]
    positivity)
  nlinarith [hnn]

private theorem Particles_Q00_eq_aux (hΨ : IsNState N Ψ) :
    (∑' u : Idx, ∑' v : Idx, (if u ≠ 0 ∧ v ≠ 0 then Expect.Q Ψ [u, v] else 0)) =
      (∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖Ψ α‖ ^ 2) ∧
    Expect.Q Ψ [0, 0] = Expect.Q Ψ [0] ^ 2 - ((N : ℝ) - Expect.Q Ψ [0]) ^ 2
        + (∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖Ψ α‖ ^ 2) := by
  have hnn : ∀ α : Occ, Ψ α ≠ 0 → 0 ≤ (N : ℝ) - α 0 := fun α hz =>
    sub_nonneg.mpr (Particles_occ_le hΨ hz 0)
  have hle : ∀ α : Occ, Ψ α ≠ 0 → (N : ℝ) - α 0 ≤ N := fun α _ => by
    have : (0 : ℝ) ≤ α 0 := by positivity
    linarith
  have hnn2 : ∀ α : Occ, 0 ≤ ((N : ℝ) - α 0) * ‖Ψ α‖ ^ 2 := fun α => by
    by_cases hz : Ψ α = 0
    · simp [hz]
    · exact mul_nonneg (hnn α hz) (by positivity)
  have hX : Summable fun α : Occ => ((N : ℝ) - α 0) ^ 2 * ‖Ψ α‖ ^ 2 :=
    Particles_summable_weight hΨ (fun α => ((N : ℝ) - α 0) ^ 2) ((N : ℝ) ^ 2) (fun α hz => by
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (hnn α hz) (hle α hz) 2)
  have hY : ∀ u : Idx, Summable fun α : Occ =>
      (α u : ℝ) * (((N : ℝ) - α 0) * ‖Ψ α‖ ^ 2) := fun u =>
    (Particles_summable_weight hΨ (fun α => (α u : ℝ) * ((N : ℝ) - α 0)) ((N : ℝ) * N)
      (fun α hz => by
        rw [abs_of_nonneg (mul_nonneg (by positivity) (hnn α hz))]
        exact mul_le_mul (Particles_occ_le hΨ hz u) (hle α hz) (hnn α hz) (by positivity))).congr
      (fun α => by ring)
  -- the inner sum, for a fixed `u`
  have hinner : ∀ u : Idx, (∑' v : Idx, (if u ≠ 0 ∧ v ≠ 0 then Expect.Q Ψ [u, v] else 0)) =
      ∑' α : Occ, (if u ≠ 0 then (α u : ℝ) * (((N : ℝ) - α 0) * ‖Ψ α‖ ^ 2) else 0) := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · have key := Particles_hasSum_swap
        (fun v α => if v ≠ 0 then (α u : ℝ) * (α v : ℝ) * ‖Ψ α‖ ^ 2 else 0)
        (fun α => (α u : ℝ) * (((N : ℝ) - α 0) * ‖Ψ α‖ ^ 2))
        (fun v α => by split_ifs <;> positivity)
        (fun α => by
          have hval : (α u : ℝ) * ‖Ψ α‖ ^ 2 * ((α.num : ℝ) - α 0) =
              (α u : ℝ) * (((N : ℝ) - α 0) * ‖Ψ α‖ ^ 2) := by
            linear_combination (α u : ℝ) * Particles_num_mul hΨ α
          rw [← hval]
          refine ((Particles_hasSum_occ_ne α).mul_left ((α u : ℝ) * ‖Ψ α‖ ^ 2)).congr_fun ?_
          intro v
          split_ifs <;> ring)
        (hY u)
      have hv : ∀ v : Idx, (if u ≠ 0 ∧ v ≠ 0 then Expect.Q Ψ [u, v] else 0) =
          ∑' α : Occ, (if v ≠ 0 then (α u : ℝ) * (α v : ℝ) * ‖Ψ α‖ ^ 2 else 0) := by
        intro v
        by_cases hv0 : v = 0
        · simp [hv0]
        · simp [hu, hv0, Particles_Q_pair]
      rw [tsum_congr hv, key.tsum_eq]
      simp [hu]
  have step : HasSum (fun u : Idx => ∑' α : Occ,
      (if u ≠ 0 then (α u : ℝ) * (((N : ℝ) - α 0) * ‖Ψ α‖ ^ 2) else 0))
      (∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖Ψ α‖ ^ 2) := by
    refine Particles_hasSum_swap _ _ (fun u α => ?_) (fun α => ?_) hX
    · split_ifs
      · exact mul_nonneg (by positivity) (hnn2 α)
      · exact le_rfl
    · have hval : (((N : ℝ) - α 0) * ‖Ψ α‖ ^ 2) * ((α.num : ℝ) - α 0) =
          ((N : ℝ) - α 0) ^ 2 * ‖Ψ α‖ ^ 2 := by
        linear_combination ((N : ℝ) - α 0) * Particles_num_mul hΨ α
      rw [← hval]
      refine ((Particles_hasSum_occ_ne α).mul_left (((N : ℝ) - α 0) * ‖Ψ α‖ ^ 2)).congr_fun ?_
      intro u
      split_ifs <;> ring
  have hfirst : (∑' u : Idx, ∑' v : Idx, (if u ≠ 0 ∧ v ≠ 0 then Expect.Q Ψ [u, v] else 0)) =
      ∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖Ψ α‖ ^ 2 := by
    rw [tsum_congr hinner]
    exact step.tsum_eq
  refine ⟨hfirst, ?_⟩
  obtain ⟨h0, h00⟩ := Particles_hasSum_moments hΨ
  have hexp := ((hΨ.1.mul_left ((N : ℝ) ^ 2)).sub (h0.mul_left (2 * (N : ℝ)))).add h00
  have hXeq : (∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖Ψ α‖ ^ 2) =
      (N : ℝ) ^ 2 * 1 - 2 * N * Expect.Q Ψ [0] + Expect.Q Ψ [0, 0] := by
    refine HasSum.tsum_eq ?_
    refine hexp.congr_fun ?_
    intro α
    ring
  rw [hXeq]
  ring

end Sums

/-- `Σ_u Q_Ψ(u) = N`, the identity behind (5.32) [resultlbpsi0]. -/
theorem Particles_hasSum_Q (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun n : Idx => Expect.Q (trialState V w kc N) [n]) N := by
  exact Particles_hasSum_Q_aux (Normalization_isNState V w kc hN)

/-- `Q_Ψ(u) = Σ_m m Q_Ψ({u, m})`, the first identity of (5.18) [4]. -/
theorem Particles_Q_eq_tsum (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    Expect.Q (trialState V w kc N) [u] =
      ∑' m : ℕ, (m : ℝ) * Expect.Qm (trialState V w kc N) [(u, m)] := by
  exact Particles_Q_eq_tsum_aux (Normalization_isNState V w kc hN) u

/-- Event form of Proposition 5.5 [prop6]: `Σ_{α ∈ E} α(0)|Ψ(α)|² ≥ N P(E) − (N − Q_Ψ(0))`. -/
theorem Prop5_5_event (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (E : Occ → Prop) :
    (N : ℝ) * (∑' α : Occ, if E α then ‖trialState V w kc N α‖ ^ 2 else 0)
        - ((N : ℝ) - Expect.Q (trialState V w kc N) [0])
      ≤ ∑' α : Occ, if E α then (α 0 : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
  exact Particles_event_aux (Normalization_isNState V w kc hN) E

/-- `Q_Ψ(0)² ≤ Q_Ψ(0, 0)`, the lower bound in the proof of Lemma 5.6 [boundspsi02]. -/
theorem Particles_Q00_ge (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    Expect.Q (trialState V w kc N) [0] ^ 2 ≤ Expect.Q (trialState V w kc N) [0, 0] := by
  exact Particles_Q00_ge_aux (Normalization_isNState V w kc hN)

/-- `Q_Ψ(0, 0) = Q_Ψ(0)² − (N − Q_Ψ(0))² + Σ_{u,v≠0} Q_Ψ(u, v)`, (5.62) [temp6.56], and
`Σ_{u,v≠0} Q_Ψ(u, v) = Σ_α (N − α(0))² |Ψ(α)|²`. -/
theorem Particles_Q00_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' u : Idx, ∑' v : Idx,
        (if u ≠ 0 ∧ v ≠ 0 then Expect.Q (trialState V w kc N) [u, v] else 0)) =
      (∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖trialState V w kc N α‖ ^ 2) ∧
    Expect.Q (trialState V w kc N) [0, 0] =
      Expect.Q (trialState V w kc N) [0] ^ 2 - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) ^ 2
        + (∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖trialState V w kc N α‖ ^ 2) := by
  exact Particles_Q00_eq_aux (Normalization_isNState V w kc hN)

end LHYUpper
