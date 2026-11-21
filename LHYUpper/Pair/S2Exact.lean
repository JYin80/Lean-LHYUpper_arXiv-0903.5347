module

public import LHYUpper.Particles.Basic
public import LHYUpper.Pair.Identities

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! # The pair terms `a†_u a†_{-u} a_0 a_0` of Lemma 7.1

Evaluates the summand of (7.4) [resultid4a] for `a†_u a†_{-u} a_0 a_0` on the trial state: the
arithmetic of the cases of (7.13)–(7.15) [temp8.23], and the estimates (7.9) [prle81], (7.10)
[temp8.15], (7.11) [temp8.16]–(7.12) and (7.16) [temp8.24]–(7.17) [temp8.25] as `Eq7_10`, `Eq7_12`,
`Eq7_15` and `Eq7_17`. The proofs use the expectations `Q_Ψ(u)` of Definition 5.1 [1]. -/

/-- `-u ≠ u` for a nonzero lattice point `u`. -/
private lemma S2Exact_neg_ne_self {u : Idx} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

/-- The occupation produced by `a†_u a†_{−u} a_0 a_0` on `|α⟩` is the strict pair creation
`𝓐^u α` of Definition 3.3 (item 1). -/
private lemma S2Exact_a4_snd (α : Occ) (u : Idx) :
    (a4 u (-u) 0 0 α).2 = strictPair u α := by
  unfold a4 strictPair
  simp only
  ext n
  simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
  split_ifs <;> omega

/-- The coefficient of `a†_u a†_{−u} a_0 a_0` on `|α⟩` is
`√(α(0)(α(0) − 1)) √((α(u)+1)(α(−u)+1))` for `u ≠ 0`, (7.4) [resultid4a]. -/
private lemma S2Exact_a4_fst {u : Idx} (hu : u ≠ 0) (α : Occ) :
    (a4 u (-u) 0 0 α).1 =
      Real.sqrt ((α 0 : ℝ) * ((α 0 : ℝ) - 1)) *
        Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) := by
  have hn := S2Exact_neg_ne_self hu
  have h1 : (-u : Idx) ≠ 0 := neg_ne_zero.mpr hu
  have key : (a4 u (-u) 0 0 α).1 =
      Real.sqrt (α 0 : ℝ) * Real.sqrt ((α 0 - 1 : ℕ) : ℝ) *
        Real.sqrt ((α (-u) : ℝ) + 1) * Real.sqrt ((α u : ℝ) + 1) := by
    unfold a4
    simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    simp [hn, hu.symm, h1.symm]
  rw [key]
  rcases Nat.eq_zero_or_pos (α 0) with h0 | h0
  · simp [h0]
  · have hc : ((α 0 - 1 : ℕ) : ℝ) = (α 0 : ℝ) - 1 := by
      rw [Nat.cast_sub h0]
      simp
    rw [hc, Real.sqrt_mul (by positivity) ((α 0 : ℝ) - 1),
      Real.sqrt_mul (by positivity) ((α (-u) : ℝ) + 1)]
    ring

/-- If `α` and `𝓐^u α` lie in `M` and `f(𝓐^u α) = r f(α)` with `r` real, the summand
`conj Ψ(𝓐^u α) c Ψ(α)` of (7.4) [resultid4a] equals `r c |Ψ(α)|²`, a real number. -/
private lemma S2Exact_term_main {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α β : Occ}
    (hα : InM (rhoN N) (LN N) kc N α)
    (hβ : InM (rhoN N) (LN N) kc N β) {r : ℝ}
    (hr : f0 V w (rhoN N) (LN N) β = (r : ℂ) * f0 V w (rhoN N) (LN N) α) (c : ℝ) :
    conj (trialState V w kc N β) * (c : ℂ) * trialState V w kc N α =
      ((r * c * ‖trialState V w kc N α‖ ^ 2 : ℝ) : ℂ) := by
  have hΨα : trialState V w kc N α = (CN V w kc N : ℂ) * f0 V w (rhoN N) (LN N) α := by
    rw [FIdentities_trialState]
    simp [hα]
  have hΨβ : trialState V w kc N β =
      (CN V w kc N : ℂ) * ((r : ℂ) * f0 V w (rhoN N) (LN N) α) := by
    rw [FIdentities_trialState]
    simp [hβ, hr]
  rw [hΨβ]
  have h2 : ((‖trialState V w kc N α‖ ^ 2 : ℝ) : ℂ) =
      conj (trialState V w kc N α) * trialState V w kc N α := by
    rw [Complex.conj_mul']
    norm_cast
  rw [Complex.ofReal_mul, Complex.ofReal_mul, h2, hΨα]
  simp only [map_mul, Complex.conj_ofReal]
  ring

/-- `√(a/L)√((a-1)/L) λ (√(a(a-1)) s) = (λ/L) a (a-1) s` for `a ≥ 1`, `L > 0`. -/
private lemma S2Exact_arith {L3 a lam s : ℝ} (hL : 0 < L3) (ha : 1 ≤ a) :
    Real.sqrt (a / L3) * Real.sqrt ((a - 1) / L3) * lam * (Real.sqrt (a * (a - 1)) * s) =
      lam / L3 * (a * (a - 1) * s) := by
  have h0 : 0 ≤ a * (a - 1) := mul_nonneg (by linarith) (by linarith)
  have e : Real.sqrt (a / L3) * Real.sqrt ((a - 1) / L3) = Real.sqrt (a * (a - 1)) / L3 := by
    rw [← Real.sqrt_mul (div_nonneg (by linarith) hL.le),
      show a / L3 * ((a - 1) / L3) = a * (a - 1) / L3 ^ 2 by field_simp,
      Real.sqrt_div' _ (by positivity), Real.sqrt_sq hL.le]
  rw [e]
  have hx := Real.mul_self_sqrt h0
  generalize Real.sqrt (a * (a - 1)) = x at hx ⊢
  rw [← hx]
  ring

/-- The summand of (7.4) [resultid4a] for `a†_u a†_{−u} a_0 a_0` with `u ∈ P_I ∪ P_H`,
(7.9) [prle81] and (7.10) [temp8.15]. -/
private lemma S2Exact_term_IH {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u) (α : Occ) :
    conj (trialState V w kc N (a4 u (-u) 0 0 α).2) * ((a4 u (-u) 0 0 α).1 : ℂ) *
        trialState V w kc N α =
      ((lam V w (rhoN N) (LN N) u / LN N ^ 3 *
        ((α 0 : ℝ) * ((α 0 : ℝ) - 1) *
          Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 2) : ℝ) :
        ℂ) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hu0 : u ≠ 0 := by
    rcases hu with h | h
    · exact Regions_PI_ne_zero hρ h
    · exact Regions_PH_ne_zero hρ h
  rw [S2Exact_a4_snd, S2Exact_a4_fst hu0]
  by_cases hα : InM (rhoN N) (LN N) kc N α
  · by_cases h2 : 2 ≤ α 0
    · have hβ := InM.strictIH hα hu h2
      have hf := Lemma5_1_properf1 (V := V) (w := w) hρ hL hu hα hβ
      rw [S2Exact_term_main hα hβ hf]
      congr 1
      have h2' : (1 : ℝ) ≤ (α 0 : ℝ) := by exact_mod_cast (by omega : 1 ≤ α 0)
      have := S2Exact_arith (lam := lam V w (rhoN N) (LN N) u)
        (s := Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 2)
        (pow_pos hL 3) h2'
      linear_combination this
    · have h0 : (α 0 : ℝ) * ((α 0 : ℝ) - 1) = 0 := by
        rcases (by omega : α 0 = 0 ∨ α 0 = 1) with h | h <;> simp [h]
      simp [h0]
  · have hz : trialState V w kc N α = 0 := by
      rw [FIdentities_trialState]
      simp [hα]
    simp [hz]

/-- The arithmetic of the case `α(u) ≠ α(−u)` in (7.13)–(7.14) [temp8.23], with `s = α*(u)`:
`√((s+1)/s) √(s(s+1)) = s + 1`. -/
private lemma S2Exact_arith_asym {L3 a lam s : ℝ} (hL : 0 < L3) (ha : 1 ≤ a) (hs : 0 < s) :
    Real.sqrt (a / L3) * Real.sqrt ((a - 1) / L3) * Real.sqrt ((s + 1) / s) * lam *
        (Real.sqrt (a * (a - 1)) * Real.sqrt (s * (s + 1))) =
      lam / L3 * (a * (a - 1) * (s + 1)) := by
  have hq : Real.sqrt ((s + 1) / s) * Real.sqrt (s * (s + 1)) = s + 1 := by
    rw [← Real.sqrt_mul (div_nonneg (by linarith) hs.le),
      show (s + 1) / s * (s * (s + 1)) = (s + 1) ^ 2 by field_simp,
      Real.sqrt_sq (by linarith)]
  have := S2Exact_arith (lam := lam) (s := s + 1) hL ha
  calc _ = Real.sqrt (a / L3) * Real.sqrt ((a - 1) / L3) * lam *
        (Real.sqrt (a * (a - 1)) * (Real.sqrt ((s + 1) / s) * Real.sqrt (s * (s + 1)))) := by ring
    _ = _ := by rw [hq]; exact this

/-- The summand of (7.4) [resultid4a] for `a†_u a†_{−u} a_0 a_0` with `u ∈ P_L`, (7.13)–(7.15)
[temp8.23]. -/
private lemma S2Exact_term_L {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) (α : Occ) :
    conj (trialState V w kc N (a4 u (-u) 0 0 α).2) * ((a4 u (-u) 0 0 α).1 : ℂ) *
        trialState V w kc N α =
      ((lam V w (rhoN N) (LN N) u / LN N ^ 3 *
        (if (alphaStar α u : ℝ) < mc (rhoN N) then
          (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ((alphaStar α u : ℝ) + 1) * ‖trialState V w kc N α‖ ^ 2
          else 0) : ℝ) : ℂ) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hu0 := Regions_PL_ne_zero hρ hu
  have hn := S2Exact_neg_ne_self hu0
  have h1 : (-u : Idx) ≠ 0 := neg_ne_zero.mpr hu0
  rw [S2Exact_a4_snd, S2Exact_a4_fst hu0]
  by_cases hα : InM (rhoN N) (LN N) kc N α
  · by_cases h2 : 2 ≤ α 0
    · have h2' : (1 : ℝ) ≤ (α 0 : ℝ) := by exact_mod_cast (by omega : 1 ≤ α 0)
      by_cases hlt : (alphaStar α u : ℝ) < mc (rhoN N)
      · have hβ := InM.strictL hα hu hlt h2
        simp only [hlt, ite_true]
        by_cases hsym : α u = α (-u)
        · have hf := Lemma5_1_properf2 (V := V) (w := w) hρ hL hu ⟨hα, hsym⟩ hβ
          rw [S2Exact_term_main hα hβ hf]
          congr 1
          have hstar : alphaStar α u = α u := by
            unfold alphaStar
            rw [← hsym]
            simp
          rw [← hsym, hstar, Real.sqrt_mul_self (by positivity)]
          have := S2Exact_arith (lam := lam V w (rhoN N) (LN N) u)
            (s := ((α u : ℝ) + 1) * ‖trialState V w kc N α‖ ^ 2) (pow_pos hL 3) h2'
          linear_combination this
        · have hf := Lemma5_1_properf3 (V := V) (w := w) hρ hL hu ⟨hα, hsym⟩ hβ
          rw [S2Exact_term_main hα hβ hf]
          congr 1
          have s0 := MStar_PL_star hρ hα hu
          have s1 := MStar_PL_star hρ hα (Regions_PL_neg.2 hu)
          unfold alphaStar at s0 s1
          simp only [neg_neg] at s1
          have hlin : (α (-u) = α u + 1 ∧ alphaStar α u = α u + 1) ∨
              (α u = α (-u) + 1 ∧ alphaStar α u = α u) := by
            unfold alphaStar
            omega
          have e : ((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1) =
              (alphaStar α u : ℝ) * ((alphaStar α u : ℝ) + 1) := by
            rcases hlin with ⟨e1, e2⟩ | ⟨e1, e2⟩
            · rw [e2]
              have : (α (-u) : ℝ) = α u + 1 := by exact_mod_cast e1
              rw [this]
              push_cast
              ring
            · rw [e2]
              have : (α u : ℝ) = α (-u) + 1 := by exact_mod_cast e1
              rw [e2] at *
              rw [this]
              ring
          have hs : 0 < (alphaStar α u : ℝ) := by
            have : 1 ≤ alphaStar α u := by
              unfold alphaStar
              omega
            exact_mod_cast this
          rw [e]
          have := S2Exact_arith_asym (lam := lam V w (rhoN N) (LN N) u)
            (pow_pos hL 3) h2' hs
          linear_combination ‖trialState V w kc N α‖ ^ 2 * this
      · have hβ : ¬ InM (rhoN N) (LN N) kc N (strictPair u α) := by
          intro hβ
          have h3 := MStar_PL_mc hρ hβ hu
          have e : alphaStar (strictPair u α) u = alphaStar α u + 1 := by
            unfold alphaStar
            rw [MBasic_strictPair_apply, MBasic_strictPair_apply]
            simp [hu0, hn, h1, hn.symm]
          rw [e] at h3
          push_cast at h3
          linarith
        have hz : trialState V w kc N (strictPair u α) = 0 := by
          rw [FIdentities_trialState]
          simp [hβ]
        simp [hz, hlt]
    · have h0 : (α 0 : ℝ) * ((α 0 : ℝ) - 1) = 0 := by
        rcases (by omega : α 0 = 0 ∨ α 0 = 1) with h | h <;> simp [h]
      simp [h0]
  · have hz : trialState V w kc N α = 0 := by
      rw [FIdentities_trialState]
      simp [hα]
    simp [hz]

section S2ExactSums

variable {N : ℕ} {Ψ : Occ → ℂ}

/-- An occupation number is at most the particle number. -/
private lemma S2Exact_apply_le (α : Occ) (u : Idx) : α u ≤ α.num := by
  by_cases hu : u ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hu
  · rw [Finsupp.notMem_support_iff.mp hu]
    exact Nat.zero_le _

/-- On the support of an `N`-particle state, every occupation number is at most `N`. -/
private lemma S2Exact_occ_le (hΨ : IsNState N Ψ) {α : Occ} (hz : Ψ α ≠ 0) (u : Idx) :
    (α u : ℝ) ≤ N := by
  have h := S2Exact_apply_le α u
  rw [hΨ.2 α hz] at h
  exact_mod_cast h

/-- A weight bounded on the support, against `|Ψ|²`, is summable. -/
private lemma S2Exact_summable_weight (hΨ : IsNState N Ψ) (h : Occ → ℝ) (C : ℝ)
    (hh : ∀ α, Ψ α ≠ 0 → |h α| ≤ C) : Summable fun α : Occ => h α * ‖Ψ α‖ ^ 2 := by
  refine Summable.of_norm_bounded (hΨ.1.summable.mul_left C) (fun α => ?_)
  rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
  by_cases hz : Ψ α = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hh α hz) (by positivity)

/-- `Q_Ψ(u) = Σ_α α(u)|Ψ(α)|²`, Definition 5.1 [1]. -/
private lemma S2Exact_Q_single (Φ : Occ → ℂ) (u : Idx) :
    Expect.Q Φ [u] = ∑' α : Occ, (α u : ℝ) * ‖Φ α‖ ^ 2 := by
  simp [Expect.Q]

/-- `Q_Ψ(u, v) = Σ_α α(u)α(v)|Ψ(α)|²`, Definition 5.1 [1]. -/
private lemma S2Exact_Q_pair (Φ : Occ → ℂ) (u v : Idx) :
    Expect.Q Φ [u, v] = ∑' α : Occ, (α u : ℝ) * (α v : ℝ) * ‖Φ α‖ ^ 2 := by
  simp [Expect.Q, mul_assoc]

/-- `0 ≤ α(0)(α(0) − 1) ≤ N²` on the support of an `N`-particle state. -/
private lemma S2Exact_wt_bounds (hΨ : IsNState N Ψ) {α : Occ} (hz : Ψ α ≠ 0) :
    0 ≤ (α 0 : ℝ) * ((α 0 : ℝ) - 1) ∧ (α 0 : ℝ) * ((α 0 : ℝ) - 1) ≤ (N : ℝ) ^ 2 := by
  have h := S2Exact_occ_le hΨ hz 0
  have h0 : (0 : ℝ) ≤ α 0 := by positivity
  refine ⟨?_, by nlinarith⟩
  rcases Nat.eq_zero_or_pos (α 0) with h1 | h1
  · simp [h1]
  · have : (1 : ℝ) ≤ α 0 := by exact_mod_cast h1
    nlinarith

/-- `Q_Ψ(0, 0) − Q_Ψ(0) = Σ_α α(0)(α(0) − 1)|Ψ(α)|²`, with a summable series. -/
private lemma S2Exact_D (hΨ : IsNState N Ψ) :
    Summable (fun α : Occ => (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖Ψ α‖ ^ 2) ∧
      Expect.Q Ψ [0, 0] - Expect.Q Ψ [0] =
        ∑' α : Occ, (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖Ψ α‖ ^ 2 := by
  have h1 : Summable fun α : Occ => (α 0 : ℝ) * ‖Ψ α‖ ^ 2 :=
    S2Exact_summable_weight hΨ (fun α => (α 0 : ℝ)) N
      (fun α hz => by rw [abs_of_nonneg (by positivity)]; exact S2Exact_occ_le hΨ hz 0)
  have h2 : Summable fun α : Occ => (α 0 : ℝ) * (α 0 : ℝ) * ‖Ψ α‖ ^ 2 :=
    S2Exact_summable_weight hΨ (fun α => (α 0 : ℝ) * (α 0 : ℝ)) ((N : ℝ) ^ 2) (fun α hz => by
      rw [abs_of_nonneg (by positivity), sq]
      exact mul_le_mul (S2Exact_occ_le hΨ hz 0) (S2Exact_occ_le hΨ hz 0) (by positivity)
        (by positivity))
  refine ⟨S2Exact_summable_weight hΨ (fun α => (α 0 : ℝ) * ((α 0 : ℝ) - 1)) ((N : ℝ) ^ 2)
    (fun α hz => ?_), ?_⟩
  · obtain ⟨a, b⟩ := S2Exact_wt_bounds hΨ hz
    rw [abs_of_nonneg a]
    exact b
  · rw [S2Exact_Q_pair, S2Exact_Q_single, ← h2.tsum_sub h1]
    exact tsum_congr fun α => by ring

/-- `√((a+1)(b+1)) − 1 ≤ (a + b)/2` for `a, b ≥ 0`, used for (7.11) [temp8.16]. -/
private lemma S2Exact_sqrt_sub_one (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt ((a + 1) * (b + 1)) - 1 ≤ (a + b) / 2 := by
  have h : Real.sqrt ((a + 1) * (b + 1)) ≤ (a + b) / 2 + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (a - b)]⟩
  linarith

/-- `1 ≤ √((a+1)(b+1))` for `a, b ≥ 0`. -/
private lemma S2Exact_one_le_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    1 ≤ Real.sqrt ((a + 1) * (b + 1)) := by
  rw [Real.one_le_sqrt]
  nlinarith [mul_nonneg ha hb]

/-- `0 ≤ Σ_α α(0)(α(0) − 1)√((α(u)+1)(α(−u)+1))|Ψ(α)|² − (Q_Ψ(0, 0) − Q_Ψ(0)) ≤ N² Q_Ψ(u)`,
given `Q_Ψ(−u) = Q_Ψ(u)`. -/
private lemma S2Exact_S_sub_D (hΨ : IsNState N Ψ) (u : Idx)
    (hneg : Expect.Q Ψ [-u] = Expect.Q Ψ [u]) :
    0 ≤ (∑' α : Occ, (α 0 : ℝ) * ((α 0 : ℝ) - 1) *
          Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) * ‖Ψ α‖ ^ 2) -
        (Expect.Q Ψ [0, 0] - Expect.Q Ψ [0]) ∧
      (∑' α : Occ, (α 0 : ℝ) * ((α 0 : ℝ) - 1) *
          Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) * ‖Ψ α‖ ^ 2) -
        (Expect.Q Ψ [0, 0] - Expect.Q Ψ [0]) ≤ (N : ℝ) ^ 2 * Expect.Q Ψ [u] := by
  obtain ⟨hDs, hDeq⟩ := S2Exact_D hΨ
  have hsu : Summable fun α : Occ => (α u : ℝ) * ‖Ψ α‖ ^ 2 :=
    S2Exact_summable_weight hΨ (fun α => (α u : ℝ)) N
      (fun α hz => by rw [abs_of_nonneg (by positivity)]; exact S2Exact_occ_le hΨ hz u)
  have hsv : Summable fun α : Occ => (α (-u) : ℝ) * ‖Ψ α‖ ^ 2 :=
    S2Exact_summable_weight hΨ (fun α => (α (-u) : ℝ)) N
      (fun α hz => by rw [abs_of_nonneg (by positivity)]; exact S2Exact_occ_le hΨ hz (-u))
  have hT2s : Summable fun α : Occ => (N : ℝ) ^ 2 *
      (((α u : ℝ) * ‖Ψ α‖ ^ 2 + (α (-u) : ℝ) * ‖Ψ α‖ ^ 2) / 2) :=
    ((hsu.add hsv).div_const 2).mul_left _
  have hpt : ∀ α : Occ, 0 ≤ (α 0 : ℝ) * ((α 0 : ℝ) - 1) *
        (Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) - 1) * ‖Ψ α‖ ^ 2 ∧
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) *
        (Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) - 1) * ‖Ψ α‖ ^ 2 ≤
      (N : ℝ) ^ 2 * (((α u : ℝ) * ‖Ψ α‖ ^ 2 + (α (-u) : ℝ) * ‖Ψ α‖ ^ 2) / 2) := by
    intro α
    by_cases hz : Ψ α = 0
    · simp [hz]
    · obtain ⟨hw0, hw1⟩ := S2Exact_wt_bounds hΨ hz
      have hx : 0 ≤ ‖Ψ α‖ ^ 2 := by positivity
      have hu0 : (0 : ℝ) ≤ α u := by positivity
      have hv0 : (0 : ℝ) ≤ α (-u) := by positivity
      have hs0 := S2Exact_one_le_sqrt (α u : ℝ) (α (-u) : ℝ) hu0 hv0
      have hs1 := S2Exact_sqrt_sub_one (α u : ℝ) (α (-u) : ℝ) hu0 hv0
      refine ⟨mul_nonneg (mul_nonneg hw0 (by linarith)) hx, ?_⟩
      have := mul_le_mul hw1 hs1 (by linarith) (by positivity)
      have h2 := mul_le_mul_of_nonneg_right this hx
      calc _ ≤ (N : ℝ) ^ 2 * (((α u : ℝ) + (α (-u) : ℝ)) / 2) * ‖Ψ α‖ ^ 2 := h2
        _ = _ := by ring
  have hT1s : Summable fun α : Occ => (α 0 : ℝ) * ((α 0 : ℝ) - 1) *
        (Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) - 1) * ‖Ψ α‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun α => (hpt α).1) (fun α => (hpt α).2) hT2s
  have hsplit : (∑' α : Occ, (α 0 : ℝ) * ((α 0 : ℝ) - 1) *
          Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) * ‖Ψ α‖ ^ 2) =
      (∑' α : Occ, (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖Ψ α‖ ^ 2) +
        ∑' α : Occ, (α 0 : ℝ) * ((α 0 : ℝ) - 1) *
          (Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) - 1) * ‖Ψ α‖ ^ 2 := by
    rw [← hDs.tsum_add hT1s]
    exact tsum_congr fun α => by ring
  have hT1le := hT1s.tsum_le_tsum (fun α => (hpt α).2) hT2s
  have hT2eq : (∑' α : Occ, (N : ℝ) ^ 2 *
      (((α u : ℝ) * ‖Ψ α‖ ^ 2 + (α (-u) : ℝ) * ‖Ψ α‖ ^ 2) / 2)) = (N : ℝ) ^ 2 * Expect.Q Ψ [u] := by
    rw [tsum_mul_left, tsum_div_const, hsu.tsum_add hsv, ← S2Exact_Q_single, ← S2Exact_Q_single,
      hneg]
    ring
  rw [hsplit, hDeq]
  constructor
  · rw [add_sub_cancel_left]
    exact tsum_nonneg (fun α => (hpt α).1)
  · rw [add_sub_cancel_left]
    linarith

end S2ExactSums

/-- The final estimate of (7.11) [temp8.16]–(7.12) in real form: with `ρ|Λ| = N`,
`0 ≤ S − D ≤ N² Q` gives `|λ|Λ|⁻¹ S|Λ|⁻¹ − λ|Λ|⁻² D| ≤ |λ| ρ² Q`. -/
private lemma S2Exact_final {lam L3 ρ N S D Q : ℝ} (hL3 : 0 < L3) (hN : ρ * L3 = N)
    (h0 : 0 ≤ S - D) (h1 : S - D ≤ N ^ 2 * Q) :
    |lam / L3 * S / L3 - lam / L3 ^ 2 * D| ≤ |lam| * ρ ^ 2 * Q := by
  have e : lam / L3 * S / L3 - lam / L3 ^ 2 * D = lam / L3 ^ 2 * (S - D) := by
    field_simp
  rw [e, abs_mul, abs_div, abs_of_pos (pow_pos hL3 2), abs_of_nonneg h0]
  calc |lam| / L3 ^ 2 * (S - D) ≤ |lam| / L3 ^ 2 * (N ^ 2 * Q) := by gcongr
    _ = |lam| * ρ ^ 2 * Q := by
      rw [← hN]
      field_simp

section S2ExactL

variable {N : ℕ} {Ψ : Occ → ℂ}

/-- The regrouping `Σ_{m : t ≤ m+2} Q_Ψ({u, m}) = Σ_α 1[t ≤ α(u)+2] |Ψ(α)|²`. -/
private lemma S2Exact_tail (hΨ : IsNState N Ψ) (u : Idx) (t : ℝ) :
    (∑' m : ℕ, if t ≤ (m : ℝ) + 2 then Expect.Qm Ψ [(u, m)] else 0) =
      ∑' α : Occ, if t ≤ (α u : ℝ) + 2 then ‖Ψ α‖ ^ 2 else 0 := by
  have hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have hsc : Summable fun α : Occ => if t ≤ (α u : ℝ) + 2 then ‖Ψ α‖ ^ 2 else 0 :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => by split_ifs <;> simp) hs
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
  have hall : HasSum (fun m : ℕ => if t ≤ (m : ℝ) + 2 then Expect.Qm Ψ [(u, m)] else 0)
      (∑' α : Occ, if t ≤ (α u : ℝ) + 2 then ‖Ψ α‖ ^ 2 else 0) := by
    refine HasSum.sigma (f := fun x : (Σ m : ℕ, {α : Occ // α u = m}) =>
      if t ≤ ((e x) u : ℝ) + 2 then ‖Ψ (e x)‖ ^ 2 else 0) (e.hasSum_iff.mpr hsc.hasSum) ?_
    intro m
    by_cases hm : t ≤ (m : ℝ) + 2
    · simp only [hm, ite_true]
      refine (hfib m).congr_fun ?_
      intro c
      have hc : c.1 u = m := c.2
      simp [e, hc, hm]
    · simp only [hm, ite_false]
      refine hasSum_zero.congr_fun ?_
      intro c
      have hc : c.1 u = m := c.2
      simp [e, hc, hm]
  exact hall.tsum_eq

/-- The termwise inequality behind (7.16) [temp8.24]–(7.17) [temp8.25], for `α ∈ M`. -/
private lemma S2Exact_L_pt (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) (α : Occ) :
    (if (α u : ℝ) + 2 ≤ mc (rhoN N) then
        (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) +
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2 -
      (N : ℝ) ^ 2 * (if mc (rhoN N) ≤ (α u : ℝ) + 2 then ‖trialState V w kc N α‖ ^ 2 else 0) ≤
    if (alphaStar α u : ℝ) < mc (rhoN N) then
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ((alphaStar α u : ℝ) + 1) * ‖trialState V w kc N α‖ ^ 2
      else 0 := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  by_cases hz : trialState V w kc N α = 0
  · simp [hz]
  · have hα : InM (rhoN N) (LN N) kc N α := by
      by_contra h
      apply hz
      rw [FIdentities_trialState]
      simp [h]
    obtain ⟨hw0, hw1⟩ := S2Exact_wt_bounds hΨ hz
    have hx : 0 ≤ ‖trialState V w kc N α‖ ^ 2 := by positivity
    have hu0 : (0 : ℝ) ≤ α u := by positivity
    have hge : (α u : ℝ) ≤ alphaStar α u := by
      unfold alphaStar
      exact_mod_cast le_max_left _ _
    have hle1 : (alphaStar α u : ℝ) ≤ (α u : ℝ) + 1 := by
      rcases MStar_PL_star hρ hα hu with h | h <;> rw [h] <;> push_cast <;> linarith
    by_cases h1 : (α u : ℝ) + 2 ≤ mc (rhoN N)
    · have h2 : (alphaStar α u : ℝ) < mc (rhoN N) := by linarith
      have h3 : 0 ≤ (N : ℝ) ^ 2 *
          (if mc (rhoN N) ≤ (α u : ℝ) + 2 then ‖trialState V w kc N α‖ ^ 2 else 0) := by
        split_ifs <;> positivity
      simp only [h1, h2, ite_true]
      nlinarith [mul_nonneg hw0 hx, mul_nonneg (mul_nonneg hw0 hx) (sub_nonneg.mpr hge)]
    · have h3 : mc (rhoN N) ≤ (α u : ℝ) + 2 := by linarith [not_le.mp h1]
      have hT : 0 ≤ (if (alphaStar α u : ℝ) < mc (rhoN N) then
          (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ((alphaStar α u : ℝ) + 1) *
            ‖trialState V w kc N α‖ ^ 2 else 0) := by
        split_ifs
        · have : (0 : ℝ) ≤ alphaStar α u := by positivity
          positivity
        · exact le_rfl
      simp only [h1, h3, ite_false, ite_true]
      nlinarith [mul_nonneg (sub_nonneg.mpr hw1) hx]

/-- For `u ∈ P_L`, the right side of (7.17) [temp8.25] without the factor `λ_u|Λ|⁻¹` is at most
`Σ_{α*(u) < m_c} α(0)(α(0) − 1)(α*(u) + 1)|Ψ(α)|²`, (7.15) [temp8.23]. -/
private lemma S2Exact_L_key (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) :
    (∑' α : Occ, if (α u : ℝ) + 2 ≤ mc (rhoN N) then
        (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) +
      (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) -
      (N : ℝ) ^ 2 * (∑' m : ℕ, if mc (rhoN N) ≤ (m : ℝ) + 2 then
        Expect.Qm (trialState V w kc N) [(u, m)] else 0) ≤
    ∑' α : Occ, if (alphaStar α u : ℝ) < mc (rhoN N) then
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ((alphaStar α u : ℝ) + 1) * ‖trialState V w kc N α‖ ^ 2
      else 0 := by
  have hΨ := Normalization_isNState V w kc hN
  obtain ⟨hDs, hDeq⟩ := S2Exact_D hΨ
  have hA : Summable fun α : Occ => if (α u : ℝ) + 2 ≤ mc (rhoN N) then
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
    refine (S2Exact_summable_weight hΨ (fun α => if (α u : ℝ) + 2 ≤ mc (rhoN N) then
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) else 0) ((N : ℝ) ^ 2 * N)
      (fun α hz => ?_)).congr (fun α => ?_)
    · obtain ⟨hw0, hw1⟩ := S2Exact_wt_bounds hΨ hz
      have hu1 := S2Exact_occ_le hΨ hz u
      have hu0 : (0 : ℝ) ≤ α u := by positivity
      split_ifs
      · rw [abs_of_nonneg (mul_nonneg hw0 hu0)]
        exact mul_le_mul hw1 hu1 hu0 (by positivity)
      · simp only [abs_zero]
        positivity
    · split_ifs <;> simp
  have hR : Summable fun α : Occ => (N : ℝ) ^ 2 *
      (if mc (rhoN N) ≤ (α u : ℝ) + 2 then ‖trialState V w kc N α‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le (fun α => by split_ifs <;> positivity)
      (fun α => by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        split_ifs <;> simp)
      (hΨ.1.summable.mul_left ((N : ℝ) ^ 2))
  have hT : Summable fun α : Occ => if (alphaStar α u : ℝ) < mc (rhoN N) then
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ((alphaStar α u : ℝ) + 1) *
        ‖trialState V w kc N α‖ ^ 2 else 0 := by
    refine (S2Exact_summable_weight hΨ (fun α => if (alphaStar α u : ℝ) < mc (rhoN N) then
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ((alphaStar α u : ℝ) + 1) else 0)
      ((N : ℝ) ^ 2 * ((N : ℝ) + 1)) (fun α hz => ?_)).congr (fun α => ?_)
    · obtain ⟨hw0, hw1⟩ := S2Exact_wt_bounds hΨ hz
      have hs1 : (alphaStar α u : ℝ) ≤ N := by
        unfold alphaStar
        rw [Nat.cast_max]
        exact max_le (S2Exact_occ_le hΨ hz u) (S2Exact_occ_le hΨ hz (-u))
      have hs0 : (0 : ℝ) ≤ (alphaStar α u : ℝ) + 1 := by positivity
      split_ifs
      · rw [abs_of_nonneg (mul_nonneg hw0 hs0)]
        exact mul_le_mul hw1 (by linarith) hs0 (by positivity)
      · simp only [abs_zero]
        positivity
    · split_ifs <;> simp
  rw [S2Exact_tail hΨ u (mc (rhoN N)), hDeq, ← tsum_mul_left, ← hA.tsum_add hDs,
    ← (hA.add hDs).tsum_sub hR]
  exact ((hA.add hDs).sub hR).tsum_le_tsum (fun α => S2Exact_L_pt V w kc hN hu α) hT

end S2ExactL

/-- (7.9) [prle81] and (7.10) [temp8.15] with the complex conjugate of Lemma 7.1 [id4a]: for
`u ∈ P_I ∪ P_H`, `⟨a†_u a†_{−u} a_0 a_0⟩_Ψ = λ_u|Λ|⁻¹ Σ_α α(0)(α(0) − 1)√((α(u)+1)(α(−u)+1))|Ψ(α)|²`. -/
theorem Eq7_10 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u) :
    Expect.E4 (trialState V w kc N) u (-u) 0 0 =
      ((lam V w (rhoN N) (LN N) u / LN N ^ 3 *
        (∑' α : Occ, (α 0 : ℝ) * ((α 0 : ℝ) - 1) *
          Real.sqrt (((α u : ℝ) + 1) * ((α (-u) : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 2) :
        ℝ) : ℂ) := by
  unfold Expect.E4
  rw [tsum_congr (S2Exact_term_IH hN hu), ← Complex.ofReal_tsum, tsum_mul_left]

/-- (7.11) [temp8.16]–(7.12): for `u ∈ P_I ∪ P_H`,
`||Λ|⁻¹⟨a†_u a†_{−u} a_0 a_0⟩_Ψ − λ_u|Λ|⁻²(Q_Ψ(0, 0) − Q_Ψ(0))| ≤ |λ_u| ρ² Q_Ψ(u)`. -/
theorem Eq7_12 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u) :
    ‖Expect.E4 (trialState V w kc N) u (-u) 0 0 / (LN N ^ 3 : ℝ) -
        ((lam V w (rhoN N) (LN N) u / (LN N ^ 3) ^ 2 *
          (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) : ℝ) : ℂ)‖ ≤
      |lam V w (rhoN N) (LN N) u| * rhoN N ^ 2 * Expect.Q (trialState V w kc N) [u] := by
  obtain ⟨hNρ, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  obtain ⟨h0, h1⟩ := S2Exact_S_sub_D hΨ u (Pair_Q_neg V w kc N [u])
  rw [Eq7_10 V w kc hN hu, ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  exact S2Exact_final (pow_pos hL 3) hNρ h0 h1

/-- (7.13)–(7.15) [temp8.23] with the complex conjugate of Lemma 7.1 [id4a]: for `u ∈ P_L`,
`⟨a†_u a†_{−u} a_0 a_0⟩_Ψ = λ_u|Λ|⁻¹ Σ_{α*(u) < m_c} α(0)(α(0) − 1)(α*(u) + 1)|Ψ(α)|²`. -/
theorem Eq7_15 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) :
    Expect.E4 (trialState V w kc N) u (-u) 0 0 =
      ((lam V w (rhoN N) (LN N) u / LN N ^ 3 *
        (∑' α : Occ, if (alphaStar α u : ℝ) < mc (rhoN N) then
          (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ((alphaStar α u : ℝ) + 1) * ‖trialState V w kc N α‖ ^ 2
          else 0) : ℝ) : ℂ) := by
  unfold Expect.E4
  rw [tsum_congr (S2Exact_term_L hN hu), ← Complex.ofReal_tsum, tsum_mul_left]

/-- (7.16) [temp8.24]–(7.17) [temp8.25]: for `u ∈ P_L` and `g₀ > 0`, `⟨a†_u a†_{−u} a_0 a_0⟩_Ψ` is at
most `λ_u|Λ|⁻¹` times `Σ_{α(u)+2 ≤ m_c} α(0)(α(0) − 1)α(u)|Ψ(α)|² + Q_Ψ(0, 0) − Q_Ψ(0)
− N² Σ_{m_c ≤ m+2} Q_Ψ({u, m})`. -/
theorem Eq7_17 {V w : R3 → ℝ} (hg : 0 < g0 V w) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) :
    (Expect.E4 (trialState V w kc N) u (-u) 0 0).re ≤
      lam V w (rhoN N) (LN N) u / LN N ^ 3 *
        ((∑' α : Occ, if (α u : ℝ) + 2 ≤ mc (rhoN N) then
            (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) +
          (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) -
          (N : ℝ) ^ 2 * (∑' m : ℕ, if mc (rhoN N) ≤ (m : ℝ) + 2 then
            Expect.Qm (trialState V w kc N) [(u, m)] else 0)) := by
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN
  have hlam : lam V w (rhoN N) (LN N) u < 0 := by
    by_contra hcon
    have h := (Particles_rho_lam_PL hg hρ hρ1 hu).1
    have := mul_nonneg hρ.le (not_lt.mp hcon)
    linarith
  rw [Eq7_15 V w kc hN hu, Complex.ofReal_re]
  exact mul_le_mul_of_nonpos_left (S2Exact_L_key V w kc hN hu)
    (div_nonpos_of_nonpos_of_nonneg hlam.le (pow_pos hL 3).le)

end LHYUpper
