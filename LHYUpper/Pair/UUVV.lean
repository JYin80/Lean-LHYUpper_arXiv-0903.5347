import LHYUpper.Particles.UpperL
import LHYUpper.Pair.Identities
import LHYUpper.Pair.Id4a2
import LHYUpper.Particles.Lemma55

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Auxiliary facts on `Ψ` and on its series -/

/-- `Ψ(α) ≠ 0` forces `α ∈ M`. -/
private lemma UUVV_inM_of_ne {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  simp [trialState, hc]

/-- `Ψ` vanishes off `M`. -/
private lemma UUVV_psi_zero {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : ¬ InM (rhoN N) (LN N) kc N α) : trialState V w kc N α = 0 := by
  simp [trialState, h]

/-- On the support of `Ψ`, every occupation number is at most `N`. -/
private lemma UUVV_occ_le {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {α : Occ}
    (h : trialState V w kc N α ≠ 0) (n : Idx) : (α n : ℝ) ≤ N := by
  have hρ := (Particles_rhoN_LN hN).2.1
  have h1 : α n ≤ α.num := by
    by_cases hn : n ∈ α.support
    · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
    · rw [Finsupp.notMem_support_iff.mp hn]
      exact Nat.zero_le _
  have h2 := MBasic_num hρ (UUVV_inM_of_ne h)
  rw [h2] at h1
  exact_mod_cast h1

/-- A family `f(α)|Ψ(α)|²` with `|f| ≤ K` on the support of `Ψ` is summable. -/
private lemma UUVV_summable (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (f : Occ → ℝ) (K : ℝ)
    (hf : ∀ α, trialState V w kc N α ≠ 0 → |f α| ≤ K) :
    Summable fun α => f α * ‖trialState V w kc N α‖ ^ 2 := by
  have hs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  refine Summable.of_norm_bounded (hs.mul_left K) (fun α => ?_)
  by_cases h : trialState V w kc N α = 0
  · simp [h]
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖trialState V w kc N α‖ ^ 2)]
    exact mul_le_mul_of_nonneg_right (hf α h) (by positivity)

/-- `Σ_α α(a) |Ψ(α)|² = Q_Ψ(a)` as a `HasSum`. -/
private lemma UUVV_hasSum_Q1 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (a : Idx) :
    HasSum (fun α : Occ => (α a : ℝ) * ‖trialState V w kc N α‖ ^ 2)
      (Expect.Q (trialState V w kc N) [a]) := by
  have e : Expect.Q (trialState V w kc N) [a] =
      ∑' α : Occ, (α a : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by simp [Expect.Q]
  rw [e]
  exact (UUVV_summable V w kc hN (fun α => (α a : ℝ)) N (fun α h => by
    rw [abs_of_nonneg (by positivity)]
    exact UUVV_occ_le hN h a)).hasSum

/-- `Σ_α α(a) α(b) |Ψ(α)|² = Q_Ψ(a, b)` as a `HasSum`. -/
private lemma UUVV_hasSum_Q2 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (a b : Idx) :
    HasSum (fun α : Occ => (α a : ℝ) * (α b : ℝ) * ‖trialState V w kc N α‖ ^ 2)
      (Expect.Q (trialState V w kc N) [a, b]) := by
  have e : Expect.Q (trialState V w kc N) [a, b] =
      ∑' α : Occ, (α a : ℝ) * (α b : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by simp [Expect.Q]
  rw [e]
  exact (UUVV_summable V w kc hN (fun α => (α a : ℝ) * (α b : ℝ)) ((N : ℝ) * N) (fun α h => by
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (UUVV_occ_le hN h a) (UUVV_occ_le hN h b) (by positivity) (by positivity))).hasSum

/-- `Q_Ψ(0, 0) − Q_Ψ(0) = Σ_α α(0)(α(0) − 1)|Ψ(α)|²`. -/
private lemma UUVV_hasSum_Q00 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun α : Occ => (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2)
      (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) := by
  refine ((UUVV_hasSum_Q2 V w kc hN 0 0).sub (UUVV_hasSum_Q1 V w kc hN 0)).congr_fun ?_
  intro α
  ring

/-- `α(0)(α(0) − 1) ≥ 0`. -/
private lemma UUVV_nat_mul_pred (a : ℕ) : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos a with rfl | h
  · simp
  · have : (1 : ℝ) ≤ a := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)

/-- `0 ≤ γ(0)(γ(0) − 1)/|Λ|⁶ ≤ ρ²` when `γ(0) ≤ N`. -/
private lemma UUVV_W_bounds {N : ℕ} (hN : 1 ≤ N) {γ : Occ} (h0 : (γ 0 : ℝ) ≤ N) :
    0 ≤ (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 ∧
      (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 ≤ rhoN N ^ 2 := by
  obtain ⟨hNL, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hL3 : 0 < (LN N ^ 3) ^ 2 := by positivity
  refine ⟨div_nonneg (UUVV_nat_mul_pred _) hL3.le, ?_⟩
  rw [div_le_iff₀ hL3]
  have hg : (0 : ℝ) ≤ γ 0 := Nat.cast_nonneg _
  calc (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) ≤ (N : ℝ) * N := by nlinarith
    _ = rhoN N ^ 2 * (LN N ^ 3) ^ 2 := by rw [← hNL]; ring


/-! ### The amplitudes `Ψ(𝓐^k γ)` -/

/-- The weight of `𝓐^k` in `P(u, v)`: `γ*(k) + 1` on `P_L`, and `√((γ(k)+1)(γ(−k)+1))` off `P_L`. -/
private def UUVV_Wk (ρ L : ℝ) (k : Idx) (γ : Occ) : ℝ :=
  if inPL ρ L k then (alphaStar γ k : ℝ) + 1
  else Real.sqrt (((γ k : ℝ) + 1) * ((γ (-k) : ℝ) + 1))

/-- On `M`, a multiplicative relation between `f` at two points passes to `Ψ`. -/
private lemma UUVV_psi_mul {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {γ β : Occ}
    (hγ : InM (rhoN N) (LN N) kc N γ) (hβ : InM (rhoN N) (LN N) kc N β) {c : ℝ}
    (h : f0 V w (rhoN N) (LN N) β = (c : ℂ) * f0 V w (rhoN N) (LN N) γ) :
    trialState V w kc N β = (c : ℂ) * trialState V w kc N γ := by
  rw [FIdentities_trialState, FIdentities_trialState, ite_eq_left hβ, ite_eq_left hγ, h]
  ring

/-- For `k ∈ P_L` and `γ(k) ≠ γ(−k)` in `M`: `(γ(k)+1)(γ(−k)+1) = γ*(k)(γ*(k)+1)`. -/
private lemma UUVV_star_asym {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {γ : Occ}
    (hγ : InM ρ L kc N γ) {k : Idx} (hk : inPL ρ L k) (hs : γ k ≠ γ (-k)) :
    ((γ k : ℝ) + 1) * ((γ (-k) : ℝ) + 1) =
      (alphaStar γ k : ℝ) * ((alphaStar γ k : ℝ) + 1) := by
  have s0 := MStar_PL_star hρ hγ hk
  have s1 := MStar_PL_star hρ hγ (Regions_PL_neg.2 hk)
  unfold alphaStar at s0 s1 ⊢
  simp only [neg_neg] at s1
  have key : (max (γ k) (γ (-k)) = γ k ∧ γ (-k) + 1 = γ k) ∨
      (max (γ k) (γ (-k)) = γ (-k) ∧ γ k + 1 = γ (-k)) := by omega
  rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
    have : (γ k : ℝ) = γ (-k) + 1 := by exact_mod_cast h2.symm
    linear_combination (-(γ k : ℝ) - 1) * this
  · rw [h1]
    have : (γ (-k) : ℝ) = γ k + 1 := by exact_mod_cast h2.symm
    linear_combination (-(γ (-k) : ℝ) - 1) * this

/-- `γ*(k) ≥ 1` when `γ(k) ≠ γ(−k)`. -/
private lemma UUVV_star_pos {γ : Occ} {k : Idx} (hs : γ k ≠ γ (-k)) : 1 ≤ alphaStar γ k := by
  unfold alphaStar
  omega

/-- `Ψ(𝓐^k γ) √((γ(k)+1)(γ(−k)+1)) = √(γ(0)/|Λ|³) √((γ(0)−1)/|Λ|³) λ_k W_k Ψ(γ)` when `γ` and
`𝓐^k γ` lie in `M`, by (5.4) [properf1], (5.5) [properf2] and (5.6) [properf3]. -/
private lemma UUVV_amp (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {k : Idx}
    (hk : inPL (rhoN N) (LN N) k ∨ inPI (rhoN N) (LN N) k ∨ inPH (rhoN N) (LN N) k)
    {γ : Occ} (hγ : InM (rhoN N) (LN N) kc N γ)
    (hβ : InM (rhoN N) (LN N) kc N (strictPair k γ)) :
    trialState V w kc N (strictPair k γ) *
        ((Real.sqrt (((γ k : ℝ) + 1) * ((γ (-k) : ℝ) + 1)) : ℝ) : ℂ) =
      ((Real.sqrt ((γ 0 : ℝ) / LN N ^ 3) * Real.sqrt (((γ 0 : ℝ) - 1) / LN N ^ 3) *
        lam V w (rhoN N) (LN N) k * UUVV_Wk (rhoN N) (LN N) k γ : ℝ) : ℂ) *
        trialState V w kc N γ := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  by_cases hPL : inPL (rhoN N) (LN N) k
  · by_cases hs : γ k = γ (-k)
    · have h := Lemma5_1_properf2 (V := V) (w := w) hρ hL hPL ⟨hγ, hs⟩ hβ
      rw [UUVV_psi_mul hγ hβ h]
      have hS : Real.sqrt (((γ k : ℝ) + 1) * ((γ (-k) : ℝ) + 1)) = (alphaStar γ k : ℝ) + 1 := by
        have : alphaStar γ k = γ k := by
          unfold alphaStar
          rw [← hs]
          exact max_self _
        rw [this, ← hs]
        exact Real.sqrt_mul_self (by positivity)
      rw [hS, UUVV_Wk, ite_eq_left hPL]
      push_cast
      ring
    · have h := Lemma5_1_properf3 (V := V) (w := w) hρ hL hPL ⟨hγ, hs⟩ hβ
      rw [UUVV_psi_mul hγ hβ h]
      have hpos : (0 : ℝ) < alphaStar γ k := by exact_mod_cast UUVV_star_pos hs
      have hS : Real.sqrt ((alphaStar γ k + 1 : ℝ) / alphaStar γ k) *
          Real.sqrt (((γ k : ℝ) + 1) * ((γ (-k) : ℝ) + 1)) = (alphaStar γ k : ℝ) + 1 := by
        rw [UUVV_star_asym hρ hγ hPL hs, ← Real.sqrt_mul (by positivity)]
        have : ((alphaStar γ k : ℝ) + 1) / alphaStar γ k *
            ((alphaStar γ k : ℝ) * ((alphaStar γ k : ℝ) + 1)) =
            ((alphaStar γ k : ℝ) + 1) ^ 2 := by
          field_simp
        rw [this]
        exact Real.sqrt_sq (by positivity)
      rw [UUVV_Wk, ite_eq_left hPL]
      generalize hA : Real.sqrt ((γ 0 : ℝ) / LN N ^ 3) * Real.sqrt (((γ 0 : ℝ) - 1) / LN N ^ 3) = A
      generalize hr : Real.sqrt (((alphaStar γ k : ℝ) + 1) / (alphaStar γ k : ℝ)) = r at hS ⊢
      generalize hSS : Real.sqrt (((γ k : ℝ) + 1) * ((γ (-k) : ℝ) + 1)) = S' at hS ⊢
      have e : A * r * lam V w (rhoN N) (LN N) k * S' =
          A * lam V w (rhoN N) (LN N) k * ((alphaStar γ k : ℝ) + 1) := by
        rw [← hS]
        ring
      push_cast
      calc _ = ((A * r * lam V w (rhoN N) (LN N) k * S' : ℝ) : ℂ) * trialState V w kc N γ := by
            push_cast
            ring
        _ = _ := by rw [e]; push_cast; ring
  · have hIH : inPI (rhoN N) (LN N) k ∨ inPH (rhoN N) (LN N) k := by tauto
    have h := Lemma5_1_properf1 (V := V) (w := w) hρ hL hIH hγ hβ
    rw [UUVV_psi_mul hγ hβ h, UUVV_Wk, ite_eq_right hPL]
    push_cast
    ring


/-! ### The series `P(u, v)` of (7.25) [defPuv] as a real series -/

/-- The factor of `P(u, v)` from `𝓐^u γ` and `𝓐^v γ`: `W_u(γ) W_v(γ)` when both lie in `M`, and
`0` otherwise. -/
private def UUVV_Y (kc : ℝ) (N : ℕ) (u v : Idx) (γ : Occ) : ℝ :=
  if InM (rhoN N) (LN N) kc N (strictPair u γ) ∧ InM (rhoN N) (LN N) kc N (strictPair v γ) then
    UUVV_Wk (rhoN N) (LN N) u γ * UUVV_Wk (rhoN N) (LN N) v γ
  else 0

/-- `0 ≤ W_k(γ) ≤ N + 1` on the support of `Ψ`. -/
private lemma UUVV_Wk_bounds (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {γ : Occ}
    (hγ : trialState V w kc N γ ≠ 0) (k : Idx) :
    0 ≤ UUVV_Wk (rhoN N) (LN N) k γ ∧ UUVV_Wk (rhoN N) (LN N) k γ ≤ (N : ℝ) + 1 := by
  have h1 := UUVV_occ_le hN hγ k
  have h2 := UUVV_occ_le hN hγ (-k)
  unfold UUVV_Wk
  split_ifs
  · refine ⟨by positivity, ?_⟩
    have : (alphaStar γ k : ℝ) ≤ N := by
      unfold alphaStar
      rcases le_total (γ k) (γ (-k)) with h | h
      · rw [max_eq_right h]
        exact h2
      · rw [max_eq_left h]
        exact h1
    linarith
  · refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩⟩
    have := Nat.cast_nonneg (α := ℝ) (γ k)
    have := Nat.cast_nonneg (α := ℝ) (γ (-k))
    nlinarith

/-- The summand of (7.25) [defPuv] at `γ ∈ M` with `γ(0) ≥ 2`, for `u, v ∈ P_L ∪ P_I ∪ P_H`. -/
private lemma UUVV_term (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : inPL (rhoN N) (LN N) u ∨ inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u)
    (hv : inPL (rhoN N) (LN N) v ∨ inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v)
    {γ : Occ} (hγ : InM (rhoN N) (LN N) kc N γ) (h2 : 2 ≤ γ 0) :
    conj (trialState V w kc N (strictPair u γ)) * trialState V w kc N (strictPair v γ) *
        (Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) * ((γ v : ℝ) + 1) *
          ((γ (-v) : ℝ) + 1)) : ℂ) =
      (((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
        (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v) * UUVV_Y kc N u v γ *
        ‖trialState V w kc N γ‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  by_cases hb : InM (rhoN N) (LN N) kc N (strictPair u γ) ∧
      InM (rhoN N) (LN N) kc N (strictPair v γ)
  · have au := UUVV_amp V w kc hN hu hγ hb.1
    have av := UUVV_amp V w kc hN hv hγ hb.2
    have e4 : ((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) * ((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1) =
        (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1)) * (((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1)) := by
      ring
    rw [e4, Real.sqrt_mul (by positivity)]
    have e5 : conj (trialState V w kc N (strictPair u γ)) * trialState V w kc N (strictPair v γ) *
        (((Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1)) *
          Real.sqrt (((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1)) : ℝ)) : ℂ) =
        conj (trialState V w kc N (strictPair u γ) *
          ((Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1)) : ℝ) : ℂ)) *
        (trialState V w kc N (strictPair v γ) *
          ((Real.sqrt (((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1)) : ℝ) : ℂ)) := by
      rw [map_mul, Complex.conj_ofReal]
      push_cast
      ring
    rw [e5, au, av, map_mul, Complex.conj_ofReal]
    have hab : Real.sqrt ((γ 0 : ℝ) / LN N ^ 3) * Real.sqrt (((γ 0 : ℝ) - 1) / LN N ^ 3) *
        (Real.sqrt ((γ 0 : ℝ) / LN N ^ 3) * Real.sqrt (((γ 0 : ℝ) - 1) / LN N ^ 3)) =
        (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (γ 0 : ℝ) / LN N ^ 3 := by positivity
      have h1' : (1 : ℝ) ≤ (γ 0 : ℝ) := by exact_mod_cast (by omega : 1 ≤ γ 0)
      have h2' : (0 : ℝ) ≤ ((γ 0 : ℝ) - 1) / LN N ^ 3 :=
        div_nonneg (by linarith) (by positivity)
      rw [← Real.sqrt_mul h1, Real.mul_self_sqrt (mul_nonneg h1 h2'), div_mul_div_comm, ← sq]
    have hcc : conj (trialState V w kc N γ) * trialState V w kc N γ =
        ((‖trialState V w kc N γ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.conj_mul']
      push_cast
      ring
    unfold UUVV_Y
    rw [ite_eq_left hb]
    calc _ = (((Real.sqrt ((γ 0 : ℝ) / LN N ^ 3) * Real.sqrt (((γ 0 : ℝ) - 1) / LN N ^ 3) *
          (Real.sqrt ((γ 0 : ℝ) / LN N ^ 3) * Real.sqrt (((γ 0 : ℝ) - 1) / LN N ^ 3)) : ℝ) : ℂ) *
        ((lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
          (UUVV_Wk (rhoN N) (LN N) u γ * UUVV_Wk (rhoN N) (LN N) v γ) : ℝ) : ℂ)) *
        (conj (trialState V w kc N γ) * trialState V w kc N γ) := by
          push_cast
          ring
      _ = _ := by
        rw [hcc, hab]
        push_cast
        ring
  · unfold UUVV_Y
    rw [ite_eq_right hb]
    rcases not_and_or.mp hb with h | h
    · rw [UUVV_psi_zero h]
      simp
    · rw [UUVV_psi_zero h]
      simp

/-- The series `P(u, v)` of (7.25) [defPuv] is the real series
`Σ_γ γ(0)(γ(0)−1)|Λ|⁻⁶ λ_u λ_v W_u(γ) W_v(γ) |Ψ(γ)|²`. -/
private lemma UUVV_Puv_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : inPL (rhoN N) (LN N) u ∨ inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u)
    (hv : inPL (rhoN N) (LN N) v ∨ inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v) :
    Puv V w kc N u v =
      ((∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
        (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v) * UUVV_Y kc N u v γ *
        ‖trialState V w kc N γ‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  unfold Puv
  refine tsum_congr fun γ => ?_
  by_cases h : InM (rhoN N) (LN N) kc N γ ∧ 2 ≤ γ 0
  · rw [ite_eq_left h]
    exact UUVV_term V w kc hN hu hv h.1 h.2
  · rw [ite_eq_right h]
    by_cases hM : InM (rhoN N) (LN N) kc N γ
    · have h0 : γ 0 ≤ 1 := by
        by_contra hc
        exact h ⟨hM, by omega⟩
      have : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) = 0 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h' | h' <;> simp [h']
      rw [this]
      simp
    · rw [UUVV_psi_zero hM]
      simp

/-- The series of (7.25) [defPuv] is summable. -/
private lemma UUVV_summable_t (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u v : Idx) :
    Summable fun γ : Occ => (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
        (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v) * UUVV_Y kc N u v γ *
        ‖trialState V w kc N γ‖ ^ 2 := by
  refine (UUVV_summable V w kc hN (fun γ => (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
        (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v) * UUVV_Y kc N u v γ)
      (rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| *
        (((N : ℝ) + 1) * ((N : ℝ) + 1))) (fun γ hγ => ?_))
  obtain ⟨hW0, hW1⟩ := UUVV_W_bounds hN (UUVV_occ_le hN hγ 0)
  have hY : |UUVV_Y kc N u v γ| ≤ ((N : ℝ) + 1) * ((N : ℝ) + 1) := by
    unfold UUVV_Y
    split_ifs
    · obtain ⟨a0, a1⟩ := UUVV_Wk_bounds V w kc hN hγ u
      obtain ⟨b0, b1⟩ := UUVV_Wk_bounds V w kc hN hγ v
      rw [abs_of_nonneg (mul_nonneg a0 b0)]
      exact mul_le_mul a1 b1 b0 (by positivity)
    · rw [abs_zero]
      positivity
  rw [abs_mul, abs_mul, abs_of_nonneg hW0]
  exact mul_le_mul (mul_le_mul hW1 le_rfl (abs_nonneg _) (by positivity)) hY (abs_nonneg _)
    (by positivity)


/-! ### Comparison of series -/

/-- If `|t − m| ≤ B` termwise and the three series converge, `|Σt − Σm| ≤ ΣB`. -/
private lemma UUVV_diff_abs {t m B : Occ → ℝ} {T M S : ℝ} (ht : HasSum t T) (hm : HasSum m M)
    (hB : HasSum B S) (h : ∀ γ, |t γ - m γ| ≤ B γ) : |T - M| ≤ S := by
  have := tsum_of_norm_bounded hB (f := fun γ => t γ - m γ)
    (fun γ => by simpa [Real.norm_eq_abs] using h γ)
  rw [(ht.sub hm).tsum_eq] at this
  simpa [Real.norm_eq_abs] using this

/-- If `t − m ≤ B` termwise and the three series converge, `Σt − Σm ≤ ΣB`. -/
private lemma UUVV_diff_le {t m B : Occ → ℝ} {T M S : ℝ} (ht : HasSum t T) (hm : HasSum m M)
    (hB : HasSum B S) (h : ∀ γ, t γ - m γ ≤ B γ) : T - M ≤ S :=
  hasSum_le h (ht.sub hm) hB

/-- (7.50) [u-uv-vPMHproof3.5]: `√((a+1)(b+1)(c+1)(d+1)) ≤ ((a+b)/2 + 1)((c+d)/2 + 1)`. -/
private lemma UUVV_sqrt4 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt ((a + 1) * (b + 1) * (c + 1) * (d + 1)) ≤ ((a + b) / 2 + 1) * ((c + d) / 2 + 1) := by
  rw [show (a + 1) * (b + 1) * (c + 1) * (d + 1) = ((a + 1) * (b + 1)) * ((c + 1) * (d + 1)) by
    ring, Real.sqrt_mul (by positivity)]
  have h1 : Real.sqrt ((a + 1) * (b + 1)) ≤ (a + b) / 2 + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (a - b)]⟩
  have h2 : Real.sqrt ((c + 1) * (d + 1)) ≤ (c + d) / 2 + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (c - d)]⟩
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)

/-- (7.11) [temp8.16]: `√((a+1)(b+1)) − 1 ≤ (a+b)/2`. -/
private lemma UUVV_sqrt_sub_one (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt ((a + 1) * (b + 1)) - 1 ≤ (a + b) / 2 := by
  have h : Real.sqrt ((a + 1) * (b + 1)) ≤ (a + b) / 2 + 1 :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [sq_nonneg (a - b)]⟩
  linarith

/-- `Q_Ψ(−u, −v) = Q_Ψ(u, v)` and `Q_Ψ(−u, v) = Q_Ψ(u, −v)`. -/
private lemma UUVV_Q_neg2 (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (u v : Idx) :
    Expect.Q (trialState V w kc N) [-u, -v] = Expect.Q (trialState V w kc N) [u, v] ∧
      Expect.Q (trialState V w kc N) [-u, v] = Expect.Q (trialState V w kc N) [u, -v] := by
  refine ⟨Pair_Q_neg V w kc N [u, v], ?_⟩
  have := Pair_Q_neg V w kc N [u, -v]
  simpa only [List.map_cons, List.map_nil, neg_neg] using this

/-- `Q_Ψ(−u) = Q_Ψ(u)`. -/
private lemma UUVV_Q_neg1 (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (u : Idx) :
    Expect.Q (trialState V w kc N) [-u] = Expect.Q (trialState V w kc N) [u] :=
  Pair_Q_neg V w kc N [u]

/-- The series `Σ_γ (ab + a + b)|Ψ(γ)|²`, `a = (γ(u)+γ(−u))/2`, `b = (γ(v)+γ(−v))/2`, of (7.50)
[u-uv-vPMHproof3.5]. -/
private lemma UUVV_hasSum_ab (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u v : Idx) :
    HasSum (fun γ : Occ => (((γ u : ℝ) + γ (-u)) / 2 * (((γ v : ℝ) + γ (-v)) / 2) +
        ((γ u : ℝ) + γ (-u)) / 2 + ((γ v : ℝ) + γ (-v)) / 2) *
        ‖trialState V w kc N γ‖ ^ 2)
      ((Expect.Q (trialState V w kc N) [u, v] + Expect.Q (trialState V w kc N) [u, -v]) / 2 +
        Expect.Q (trialState V w kc N) [u] + Expect.Q (trialState V w kc N) [v]) := by
  have h1 := UUVV_hasSum_Q2 V w kc hN u v
  have h2 := UUVV_hasSum_Q2 V w kc hN u (-v)
  have h3 := UUVV_hasSum_Q2 V w kc hN (-u) v
  have h4 := UUVV_hasSum_Q2 V w kc hN (-u) (-v)
  have q1 := UUVV_hasSum_Q1 V w kc hN u
  have q2 := UUVV_hasSum_Q1 V w kc hN (-u)
  have q3 := UUVV_hasSum_Q1 V w kc hN v
  have q4 := UUVV_hasSum_Q1 V w kc hN (-v)
  obtain ⟨e1, e2⟩ := UUVV_Q_neg2 V w kc N u v
  have e3 := UUVV_Q_neg1 V w kc N u
  have e4 := UUVV_Q_neg1 V w kc N v
  have hq := (((h1.add h2).add h3).add h4).mul_left (1 / 4 : ℝ) |>.add
    (((q1.add q2).mul_left (1 / 2 : ℝ)).add ((q3.add q4).mul_left (1 / 2 : ℝ)))
  convert hq using 1
  · funext γ
    ring
  · rw [e1, e2, e3, e4]
    ring


/-- Termwise bound behind (7.44) [u-uv-vPMH]: for `u, v ∈ P_I ∪ P_H`,
`|γ(0)(γ(0)−1)|Λ|⁻⁶ λ_u λ_v (W_uW_v − 1)|Ψ(γ)|²| ≤ |λ_u λ_v| ρ² (ab + a + b)|Ψ(γ)|²`. -/
private lemma UUVV_term44 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u)
    (hv : inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v) (γ : Occ) :
    |(γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
        (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v) * UUVV_Y kc N u v γ *
        ‖trialState V w kc N γ‖ ^ 2 -
      lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v / (LN N ^ 3) ^ 2 *
        ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * ‖trialState V w kc N γ‖ ^ 2)| ≤
      |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
        ((((γ u : ℝ) + γ (-u)) / 2 * (((γ v : ℝ) + γ (-v)) / 2) +
          ((γ u : ℝ) + γ (-u)) / 2 + ((γ v : ℝ) + γ (-v)) / 2) *
          ‖trialState V w kc N γ‖ ^ 2) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  set lu := lam V w (rhoN N) (LN N) u
  set lv := lam V w (rhoN N) (LN N) v
  have hp0 : 0 ≤ ‖trialState V w kc N γ‖ ^ 2 := by positivity
  have hγu := Nat.cast_nonneg (α := ℝ) (γ u)
  have hγu' := Nat.cast_nonneg (α := ℝ) (γ (-u))
  have hγv := Nat.cast_nonneg (α := ℝ) (γ v)
  have hγv' := Nat.cast_nonneg (α := ℝ) (γ (-v))
  have hRHS : 0 ≤ |lu * lv| * rhoN N ^ 2 *
      ((((γ u : ℝ) + γ (-u)) / 2 * (((γ v : ℝ) + γ (-v)) / 2) +
        ((γ u : ℝ) + γ (-u)) / 2 + ((γ v : ℝ) + γ (-v)) / 2) *
        ‖trialState V w kc N γ‖ ^ 2) := by positivity
  by_cases hΨ : trialState V w kc N γ = 0
  · simp only [hΨ, norm_zero]
    simp
  have hγ := UUVV_inM_of_ne hΨ
  obtain ⟨hW0, hW1⟩ := UUVV_W_bounds hN (UUVV_occ_le hN hΨ 0)
  by_cases h2 : 2 ≤ γ 0
  · have hAu := InM.strictIH hγ hu h2
    have hAv := InM.strictIH hγ hv h2
    have hnu : ¬ inPL (rhoN N) (LN N) u := by
      rcases hu with h | h
      · exact fun h' => Regions_PL_PI h' h
      · exact fun h' => Regions_PL_PH hρ h' h
    have hnv : ¬ inPL (rhoN N) (LN N) v := by
      rcases hv with h | h
      · exact fun h' => Regions_PL_PI h' h
      · exact fun h' => Regions_PL_PH hρ h' h
    have hY : UUVV_Y kc N u v γ = Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) *
        (((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1))) := by
      unfold UUVV_Y UUVV_Wk
      rw [ite_eq_left ⟨hAu, hAv⟩, ite_eq_right hnu, ite_eq_right hnv,
        ← Real.sqrt_mul (by positivity)]
    have hY4 : UUVV_Y kc N u v γ =
        Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) * ((γ v : ℝ) + 1) *
          ((γ (-v) : ℝ) + 1)) := by
      rw [hY]
      congr 1
      ring
    have hY1 : 1 ≤ UUVV_Y kc N u v γ := by
      rw [hY4, Real.one_le_sqrt]
      have h1 : (1 : ℝ) ≤ (γ u : ℝ) + 1 := by linarith
      have h2 : (1 : ℝ) ≤ (γ (-u) : ℝ) + 1 := by linarith
      have h3 : (1 : ℝ) ≤ (γ v : ℝ) + 1 := by linarith
      have h4 : (1 : ℝ) ≤ (γ (-v) : ℝ) + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 * 1 := by norm_num
        _ ≤ _ := by gcongr
    have hY2 : UUVV_Y kc N u v γ ≤
        (((γ u : ℝ) + γ (-u)) / 2 + 1) * (((γ v : ℝ) + γ (-v)) / 2 + 1) := by
      rw [hY4]
      exact UUVV_sqrt4 _ _ _ _ hγu hγu' hγv hγv'
    have e : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (lu * lv) * UUVV_Y kc N u v γ *
          ‖trialState V w kc N γ‖ ^ 2 -
        lu * lv / (LN N ^ 3) ^ 2 * ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * ‖trialState V w kc N γ‖ ^ 2) =
        ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2) * (lu * lv) *
          ((UUVV_Y kc N u v γ - 1) * ‖trialState V w kc N γ‖ ^ 2) := by
      ring
    have hX : 0 ≤ (UUVV_Y kc N u v γ - 1) * ‖trialState V w kc N γ‖ ^ 2 :=
      mul_nonneg (by linarith) hp0
    rw [e, abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_nonneg hX]
    have hb : UUVV_Y kc N u v γ - 1 ≤ ((γ u : ℝ) + γ (-u)) / 2 * (((γ v : ℝ) + γ (-v)) / 2) +
        ((γ u : ℝ) + γ (-u)) / 2 + ((γ v : ℝ) + γ (-v)) / 2 := by
      nlinarith
    calc _ ≤ rhoN N ^ 2 * |lu * lv| * ((((γ u : ℝ) + γ (-u)) / 2 * (((γ v : ℝ) + γ (-v)) / 2) +
        ((γ u : ℝ) + γ (-u)) / 2 + ((γ v : ℝ) + γ (-v)) / 2) *
        ‖trialState V w kc N γ‖ ^ 2) := by
          gcongr
      _ = _ := by ring
  · have h0 : γ 0 ≤ 1 := by omega
    have : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h' | h' <;> simp [h']
    rw [this]
    simpa using hRHS

/-- (7.44) [u-uv-vPMH] of Lemma 7.4 [u-uv-vPsi], for `u, v ∈ P_I ∪ P_H` with `u ≠ ±v`, with the
constant of (7.27) [resultid4a2o] equal to `1`. -/
theorem Eq7_44 (V w : R3 → ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u v : Idx,
      (inPI (rhoN N) (LN N) u ∨ inPH (rhoN N) (LN N) u) →
      (inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v) → u ≠ v → u + v ≠ 0 →
      ‖Expect.E4 (trialState V w kc N) u (-u) v (-v) -
          ((lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
            (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
              (LN N ^ 3) ^ 2 : ℝ) : ℂ)‖ ≤
        |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
          ((Expect.Q (trialState V w kc N) [u, v] + Expect.Q (trialState V w kc N) [u, -v]) / 2 +
            Expect.Q (trialState V w kc N) [u] + Expect.Q (trialState V w kc N) [v] +
            rhoN N ^ 2) := by
  obtain ⟨N₁, h73⟩ := Lemma7_3_PH V w
  refine ⟨max N₁ 1, fun N hN kc u v hu hv huv huv' => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN2 : N₁ ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  have hu0 : u ≠ 0 := by
    rcases hu with h | h
    · exact Regions_PI_ne_zero hρ h
    · exact Regions_PH_ne_zero hρ h
  have hv0 : v ≠ 0 := by
    rcases hv with h | h
    · exact Regions_PI_ne_zero hρ h
    · exact Regions_PH_ne_zero hρ h
  have hE : ‖Expect.E4 (trialState V w kc N) u (-u) v (-v) - Puv V w kc N u v‖ ≤
      rhoN N ^ 4 * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| := by
    rcases hu with huI | huH
    · rw [Lemma7_3 V w kc hN1 hu0 hv0 huv huv' (Or.inr (Or.inl huI)), sub_self, norm_zero]
      positivity
    · rcases hv with hvI | hvH
      · rw [Lemma7_3 V w kc hN1 hu0 hv0 huv huv' (Or.inr (Or.inr (Or.inr hvI))), sub_self,
          norm_zero]
        positivity
      · exact h73 N hN2 kc u v huH hvH huv huv'
  have hP := UUVV_Puv_eq V w kc hN1 (Or.inr hu) (Or.inr hv)
  have ht := (UUVV_summable_t V w kc hN1 u v).hasSum
  have hm : HasSum (fun γ : Occ => lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v /
      (LN N ^ 3) ^ 2 * ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * ‖trialState V w kc N γ‖ ^ 2))
      (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
        (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
          (LN N ^ 3) ^ 2) := by
    have := (UUVV_hasSum_Q00 V w kc hN1).mul_left
      (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v / (LN N ^ 3) ^ 2)
    convert this using 1
    ring
  have hB := (UUVV_hasSum_ab V w kc hN1 u v).mul_left
    (|lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2)
  have hbound := UUVV_diff_abs ht hm hB (fun γ => UUVV_term44 V w kc hN1 hu hv γ)
  have h1 : ‖Expect.E4 (trialState V w kc N) u (-u) v (-v) -
      ((lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
        (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
          (LN N ^ 3) ^ 2 : ℝ) : ℂ)‖ ≤
      ‖Expect.E4 (trialState V w kc N) u (-u) v (-v) - Puv V w kc N u v‖ +
        ‖Puv V w kc N u v - ((lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
        (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
          (LN N ^ 3) ^ 2 : ℝ) : ℂ)‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  rw [hP, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
  rw [← hP] at h1
  calc _ ≤ _ := h1
    _ ≤ rhoN N ^ 4 * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| +
        |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
          ((Expect.Q (trialState V w kc N) [u, v] + Expect.Q (trialState V w kc N) [u, -v]) / 2 +
            Expect.Q (trialState V w kc N) [u] + Expect.Q (trialState V w kc N) [v]) := by
        refine add_le_add hE ?_
        exact hbound
    _ = _ := by ring

/-! ### The weighted sums of (7.57) [8.2] -/

/-- `α*(u)` is at most `N` on the support of `Ψ`. -/
private lemma UUVV_star_le {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {γ : Occ}
    (hγ : trialState V w kc N γ ≠ 0) (u : Idx) : (alphaStar γ u : ℝ) ≤ N := by
  have h1 := UUVV_occ_le hN hγ u
  have h2 := UUVV_occ_le hN hγ (-u)
  unfold alphaStar
  rcases le_total (γ u) (γ (-u)) with h | h
  · rw [max_eq_right h]
    exact h2
  · rw [max_eq_left h]
    exact h1

/-- `α*(u) |Ψ|²` is summable. -/
private lemma UUVV_summable_star (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    Summable fun γ : Occ => (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 :=
  UUVV_summable V w kc hN (fun γ => (alphaStar γ u : ℝ)) N (fun γ h => by
    rw [abs_of_nonneg (by positivity)]
    exact UUVV_star_le hN h u)

/-- `γ(0)(γ(0) − 1) α*(u) |Ψ|²` is summable. -/
private lemma UUVV_summable_W_star (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    Summable fun γ : Occ => (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
      ‖trialState V w kc N γ‖ ^ 2 :=
  UUVV_summable V w kc hN (fun γ => (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ))
    ((N : ℝ) * N * N) (fun γ h => by
      rw [abs_of_nonneg (mul_nonneg (UUVV_nat_mul_pred _) (by positivity))]
      have h0 := UUVV_occ_le hN h 0
      have hs := UUVV_star_le hN h u
      have hg : (0 : ℝ) ≤ γ 0 := Nat.cast_nonneg _
      have hs0 : (0 : ℝ) ≤ alphaStar γ u := Nat.cast_nonneg _
      calc (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) ≤ (N : ℝ) * N * N := by
            have : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) ≤ (N : ℝ) * N := by nlinarith
            exact mul_le_mul this hs hs0 (by positivity))

/-- `α*(u) |Ψ|² = 1_{M_u^s} α(u)|Ψ|² + 1_{M_u^a} α*(u)|Ψ|²`. -/
private lemma UUVV_star_split (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (u : Idx) (γ : Occ) :
    (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 =
      (if InMuS (rhoN N) (LN N) kc N u γ then (γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0) +
      (if InMuA (rhoN N) (LN N) kc N u γ then
        (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0) := by
  by_cases hM : InM (rhoN N) (LN N) kc N γ
  · by_cases hs : γ u = γ (-u)
    · have hS : InMuS (rhoN N) (LN N) kc N u γ := ⟨hM, hs⟩
      have hA : ¬ InMuA (rhoN N) (LN N) kc N u γ := fun h => h.2 hs
      have : alphaStar γ u = γ u := by
        unfold alphaStar
        rw [← hs]
        exact max_self _
      rw [ite_eq_left hS, ite_eq_right hA, this]
      ring
    · have hS : ¬ InMuS (rhoN N) (LN N) kc N u γ := fun h => hs h.2
      have hA : InMuA (rhoN N) (LN N) kc N u γ := ⟨hM, hs⟩
      rw [ite_eq_right hS, ite_eq_left hA]
      ring
  · have hS : ¬ InMuS (rhoN N) (LN N) kc N u γ := fun h => hM h.1
    have hA : ¬ InMuA (rhoN N) (LN N) kc N u γ := fun h => hM h.1
    rw [ite_eq_right hS, ite_eq_right hA, UUVV_psi_zero hM]
    simp

/-- The two parts of `Σ_γ α*(u)|Ψ|²` are summable. -/
private lemma UUVV_summable_parts (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    Summable (fun γ : Occ => if InMuS (rhoN N) (LN N) kc N u γ then
        (γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0) ∧
    Summable (fun γ : Occ => if InMuA (rhoN N) (LN N) kc N u γ then
        (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0) := by
  have hs : Summable fun γ : Occ => ‖trialState V w kc N γ‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  constructor
  · refine Summable.of_nonneg_of_le (fun γ => by split_ifs <;> positivity) (fun γ => ?_)
      (hs.mul_left (N : ℝ))
    split_ifs
    · by_cases h : trialState V w kc N γ = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (UUVV_occ_le hN h u) (by positivity)
    · positivity
  · refine Summable.of_nonneg_of_le (fun γ => by split_ifs <;> positivity) (fun γ => ?_)
      (hs.mul_left (N : ℝ))
    split_ifs
    · by_cases h : trialState V w kc N γ = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (UUVV_star_le hN h u) (by positivity)
    · positivity

/-- Upper bound: `|Λ|⁻⁶ Σ_γ γ(0)(γ(0)−1) α*(u)|Ψ|² ≤ ρ² Σ_γ α*(u)|Ψ|²`. -/
private lemma UUVV_S_le (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    ((LN N ^ 3) ^ 2)⁻¹ * (∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
        ‖trialState V w kc N γ‖ ^ 2) ≤
      rhoN N ^ 2 * (∑' γ : Occ, (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2) := by
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine (UUVV_summable_W_star V w kc hN u).mul_left _ |>.tsum_le_tsum (fun γ => ?_)
    ((UUVV_summable_star V w kc hN u).mul_left _)
  by_cases h : trialState V w kc N γ = 0
  · simp [h]
  · obtain ⟨hW0, hW1⟩ := UUVV_W_bounds hN (UUVV_occ_le hN h 0)
    have hx : 0 ≤ (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 := by positivity
    calc ((LN N ^ 3) ^ 2)⁻¹ * ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
          ‖trialState V w kc N γ‖ ^ 2) =
        ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2) *
          ((alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2) := by ring
      _ ≤ rhoN N ^ 2 * ((alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hW1 hx

/-- Lower bound: restricting to `α(u) + 2 ≤ m_c` and using `α(u) ≤ α*(u)` decreases the sum. -/
private lemma UUVV_S_ge (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    (∑' γ : Occ, (if (γ u : ℝ) + 2 ≤ mc (rhoN N) then
        (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0)) ≤
      ∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
        ‖trialState V w kc N γ‖ ^ 2 := by
  have hs : Summable fun γ : Occ => ‖trialState V w kc N γ‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  refine Summable.tsum_le_tsum (fun γ => ?_) ?_ (UUVV_summable_W_star V w kc hN u)
  · split_ifs
    · have h1 : (γ u : ℝ) ≤ alphaStar γ u := by
        exact_mod_cast le_max_left (γ u) (γ (-u))
      have h2 := UUVV_nat_mul_pred (γ 0)
      have h3 : (0 : ℝ) ≤ ‖trialState V w kc N γ‖ ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
    · exact mul_nonneg (mul_nonneg (UUVV_nat_mul_pred _) (by positivity)) (by positivity)
  · refine Summable.of_nonneg_of_le (fun γ => ?_) (fun γ => ?_)
      ((UUVV_summable_W_star V w kc hN u))
    · split_ifs
      · exact mul_nonneg (mul_nonneg (UUVV_nat_mul_pred _) (by positivity)) (by positivity)
      · exact le_rfl
    · split_ifs
      · have h1 : (γ u : ℝ) ≤ alphaStar γ u := by
          exact_mod_cast le_max_left (γ u) (γ (-u))
        have h2 := UUVV_nat_mul_pred (γ 0)
        have h3 : (0 : ℝ) ≤ ‖trialState V w kc N γ‖ ^ 2 := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h2) h3
      · exact mul_nonneg (mul_nonneg (UUVV_nat_mul_pred _) (by positivity)) (by positivity)

/-- `ρ_N · m_c / ε = ρ_N^{99/100}`. -/
private lemma UUVV_r {ρ : ℝ} (hρ : 0 < ρ) : ρ * mc ρ / epsP ρ = ρ ^ (99 / 100 : ℝ) := by
  rw [mc, epsP, div_eq_iff (Real.rpow_pos_of_pos hρ _).ne', ← Real.rpow_add hρ]
  have : ρ * ρ ^ (-(1 / 200 : ℝ)) = ρ ^ ((1 : ℝ) + -(1 / 200)) := by
    rw [Real.rpow_add hρ, Real.rpow_one]
  rw [this]
  norm_num

/-- `ρ^a → 0` as `N → ∞`, for `a > 0`. -/
private lemma UUVV_rho_pow_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.comp hT

/-- On `P_L`: `0 < (ρλ_u)² < 1`. -/
private lemma UUVV_x_bounds {V w : R3 → ℝ} (hg : 0 < g0 V w) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) :
    0 < (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 ∧
      (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 < 1 := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  obtain ⟨hl0, hl1⟩ := Particles_rho_lam_PL hg hρ hρ1 hu
  refine ⟨by rw [sq]; exact mul_pos_of_neg_of_neg hl0 hl0, ?_⟩
  have h1 : 0 < epsP (rhoN N) / (1 + Real.sqrt (g0 V w)) := by
    have := Real.sqrt_nonneg (g0 V w)
    unfold epsP
    positivity
  have h2 : 0 < -(rhoN N * lam V w (rhoN N) (LN N) u) := by linarith
  have h3 : -(rhoN N * lam V w (rhoN N) (LN N) u) < 1 := by linarith
  calc (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2
      = (-(rhoN N * lam V w (rhoN N) (LN N) u)) * (-(rhoN N * lam V w (rhoN N) (LN N) u)) := by
        ring
    _ < 1 * 1 := mul_lt_mul'' h3 h3 h2.le h2.le
    _ = 1 := one_mul 1

/-- (7.57) [8.2]: for `u ∈ P_L`, `|Λ|⁻² Σ_γ γ(0)(γ(0) − 1)γ*(u)|Ψ(γ)|² = ρ²x_u/(1 − x_u)
(1 + O(ρ^{η/2}) + O(|ρλ_u|^{2√m_c}))`, `x_u = (ρλ_u)²`. -/
theorem Eq7_57 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      |((LN N ^ 3) ^ 2)⁻¹ * (∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
            ‖trialState V w kc N γ‖ ^ 2) -
          rhoN N ^ 2 * ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
            (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2))| ≤
        rhoN N ^ 2 * ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
            (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2)) *
          (C * rhoN N ^ (1/400 : ℝ) +
            |rhoN N * lam V w (rhoN N) (LN N) u| ^ (2 * Real.sqrt (mc (rhoN N)))) := by
  obtain ⟨C₅₈, hC₅₈, N₅₈, h58⟩ := Eq5_58 hg
  obtain ⟨C₅₄, hC₅₄, N₅₄, h54⟩ := Lemma5_4_PL hg
  obtain ⟨C₂₂, hC₂₂, N₂₂, h22⟩ := Eq5_22_weighted V w
  refine ⟨max C₅₈ (C₅₄ + C₂₂ + C₅₄ * C₂₂), le_trans hC₅₈ (le_max_left _ _),
    max (max N₅₈ N₅₄) (max N₂₂ 1), fun N hN kc u hu => ?_⟩
  have hN58 : N₅₈ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN54 : N₅₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN22 : N₂₂ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨hx0, hx1⟩ := UUVV_x_bounds hg hN1 hu
  have hT0 : 0 ≤ (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
      (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) := div_nonneg hx0.le (by linarith)
  set T := (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
      (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) with hT
  set e := |rhoN N * lam V w (rhoN N) (LN N) u| ^ (2 * Real.sqrt (mc (rhoN N))) with he
  have he0 : 0 ≤ e := Real.rpow_nonneg (abs_nonneg _) _
  have hp0 : 0 ≤ rhoN N ^ (1 / 400 : ℝ) := Real.rpow_nonneg hρ.le _
  have hr : rhoN N * mc (rhoN N) / epsP (rhoN N) = rhoN N ^ (99 / 100 : ℝ) := UUVV_r hρ
  have hr0 : 0 ≤ rhoN N ^ (99 / 100 : ℝ) := Real.rpow_nonneg hρ.le _
  have hr1 : rhoN N ^ (99 / 100 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hr2 : rhoN N ^ (99 / 100 : ℝ) ≤ rhoN N ^ (1 / 400 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hτ : 0 ≤ rhoN N ^ 2 * T := by positivity
  have hN2 : (N : ℝ) ^ 2 = rhoN N ^ 2 * (LN N ^ 3) ^ 2 := by
    rw [← hNL]
    ring
  -- lower bound, from (5.58) [lbpsiuPL0]
  have hlow : rhoN N ^ 2 * T * (1 - C₅₈ * rhoN N ^ (1 / 400 : ℝ) - e) ≤
      ((LN N ^ 3) ^ 2)⁻¹ * (∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
        ‖trialState V w kc N γ‖ ^ 2) := by
    have h1 := (h58 N hN58 kc u hu).trans (UUVV_S_ge V w kc hN1 u)
    rw [← hT, ← he] at h1
    have h2 := mul_le_mul_of_nonneg_left h1
      (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ (LN N ^ 3) ^ 2))
    refine le_trans (le_of_eq ?_) h2
    rw [hN2]
    have hL0 : LN N ≠ 0 := hL.ne'
    field_simp
  -- upper bound, from (5.14) [ubpsiuroughPL] and (5.22) [ubpsiuroughPL1]
  obtain ⟨hs1, hs2⟩ := UUVV_summable_parts V w kc hN1 u
  have hsplit : (∑' γ : Occ, (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2) =
      (∑' γ : Occ, if InMuS (rhoN N) (LN N) kc N u γ then
        (γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0) +
      ∑' γ : Occ, if InMuA (rhoN N) (LN N) kc N u γ then
        (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0 := by
    rw [← hs1.tsum_add hs2]
    exact tsum_congr (UUVV_star_split V w kc N u)
  have hAs0 : 0 ≤ ∑' γ : Occ, if InMuS (rhoN N) (LN N) kc N u γ then
      (γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0 :=
    tsum_nonneg fun γ => by split_ifs <;> positivity
  have hAa := h22 N hN22 kc u hu
  have hAsQ : (∑' γ : Occ, if InMuS (rhoN N) (LN N) kc N u γ then
      (γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0) ≤ Expect.Q (trialState V w kc N) [u] := by
    rw [← (UUVV_hasSum_Q1 V w kc hN1 u).tsum_eq]
    refine hs1.tsum_le_tsum (fun γ => ?_) (UUVV_hasSum_Q1 V w kc hN1 u).summable
    split_ifs
    · exact le_rfl
    · positivity
  have hQ := h54 N hN54 kc u hu
  have hcc : ∀ C : ℝ, C * rhoN N * mc (rhoN N) / epsP (rhoN N) = C * rhoN N ^ (99 / 100 : ℝ) := by
    intro C
    rw [← hr]
    ring
  rw [hcc] at hAa hQ
  have hup : ((LN N ^ 3) ^ 2)⁻¹ * (∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
        ‖trialState V w kc N γ‖ ^ 2) ≤
      rhoN N ^ 2 * T * (1 + (C₅₄ + C₂₂ + C₅₄ * C₂₂) * rhoN N ^ (99 / 100 : ℝ)) := by
    refine (UUVV_S_le V w kc hN1 u).trans ?_
    rw [hsplit]
    set As := ∑' γ : Occ, if InMuS (rhoN N) (LN N) kc N u γ then
      (γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0
    set Aa := ∑' γ : Occ, if InMuA (rhoN N) (LN N) kc N u γ then
      (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2 else 0
    set r := rhoN N ^ (99 / 100 : ℝ)
    set Q := Expect.Q (trialState V w kc N) [u]
    have h1 : As + Aa ≤ Q * (1 + C₂₂ * r) := by
      nlinarith [mul_nonneg (mul_nonneg hC₂₂ hr0) (sub_nonneg.2 hAsQ), hAa, hAsQ]
    have h2 : Q * (1 + C₂₂ * r) ≤ T * (1 + C₅₄ * r) * (1 + C₂₂ * r) :=
      mul_le_mul_of_nonneg_right hQ (by positivity)
    have h3 : (1 + C₅₄ * r) * (1 + C₂₂ * r) ≤ 1 + (C₅₄ + C₂₂ + C₅₄ * C₂₂) * r := by
      have : 0 ≤ C₅₄ * C₂₂ * (r * (1 - r)) := mul_nonneg (mul_nonneg hC₅₄ hC₂₂)
        (mul_nonneg hr0 (by linarith))
      nlinarith
    calc rhoN N ^ 2 * (As + Aa) ≤ rhoN N ^ 2 * (T * ((1 + C₅₄ * r) * (1 + C₂₂ * r))) := by
          gcongr
          nlinarith
      _ ≤ rhoN N ^ 2 * (T * (1 + (C₅₄ + C₂₂ + C₅₄ * C₂₂) * r)) := by gcongr
      _ = _ := by ring
  set C := max C₅₈ (C₅₄ + C₂₂ + C₅₄ * C₂₂) with hC
  have hC1 : C₅₈ ≤ C := le_max_left _ _
  have hC2 : C₅₄ + C₂₂ + C₅₄ * C₂₂ ≤ C := le_max_right _ _
  rw [abs_le]
  constructor
  · have : 0 ≤ rhoN N ^ 2 * T * ((C - C₅₈) * rhoN N ^ (1 / 400 : ℝ)) :=
      mul_nonneg hτ (mul_nonneg (by linarith) hp0)
    linarith
  · have h1 : (C₅₄ + C₂₂ + C₅₄ * C₂₂) * rhoN N ^ (99 / 100 : ℝ) ≤ C * rhoN N ^ (1 / 400 : ℝ) :=
      mul_le_mul hC2 hr2 hr0 (le_trans (by positivity : 0 ≤ C₅₄ + C₂₂ + C₅₄ * C₂₂) hC2)
    have : 0 ≤ rhoN N ^ 2 * T * (C * rhoN N ^ (1 / 400 : ℝ) -
        (C₅₄ + C₂₂ + C₅₄ * C₂₂) * rhoN N ^ (99 / 100 : ℝ) + e) := mul_nonneg hτ (by linarith)
    linarith

/-! ### The pair series for `u ∈ P_L` and `v ∈ P_I ∪ P_H`: (7.45) [u-uv-vPLMH] -/

/-- A series `Σ_γ g(γ(u)) |Ψ(γ)|²` regrouped by the value `m = γ(u)`:
`Σ_m g(m) Q_Ψ({u, m})`. -/
private lemma UUVV_fibre (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) (g : ℕ → ℝ)
    (hg : ∀ α : Occ, trialState V w kc N α ≠ 0 → |g (α u)| ≤ N) :
    HasSum (fun m : ℕ => g m * Expect.Qm (trialState V w kc N) [(u, m)])
      (∑' α : Occ, g (α u) * ‖trialState V w kc N α‖ ^ 2) := by
  have hs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  have hA : Summable fun α : Occ => g (α u) * ‖trialState V w kc N α‖ ^ 2 :=
    UUVV_summable V w kc hN (fun α => g (α u)) N hg
  let e : (Σ m : ℕ, {α : Occ // α u = m}) ≃ Occ := Equiv.sigmaFiberEquiv fun α : Occ => α u
  have hev : ∀ (m : ℕ) (α : Occ), Expect.Ev [(u, m)] α ↔ α u = m := by
    intro m α
    simp [Expect.Ev]
  have hfib : ∀ m : ℕ, HasSum (fun c : {α : Occ // α u = m} => ‖trialState V w kc N c.1‖ ^ 2)
      (Expect.Qm (trialState V w kc N) [(u, m)]) := by
    intro m
    have h1 : Summable (Set.indicator {α : Occ | α u = m}
        fun α : Occ => ‖trialState V w kc N α‖ ^ 2) := hs.indicator _
    have h2 : HasSum (Set.indicator {α : Occ | α u = m}
        fun α : Occ => ‖trialState V w kc N α‖ ^ 2) (Expect.Qm (trialState V w kc N) [(u, m)]) := by
      have : Expect.Qm (trialState V w kc N) [(u, m)] =
          ∑' α, Set.indicator {α : Occ | α u = m}
            (fun α : Occ => ‖trialState V w kc N α‖ ^ 2) α := by
        unfold Expect.Qm
        refine tsum_congr fun α => ?_
        by_cases h : α u = m <;> simp [Set.indicator, hev, h]
      rw [this]
      exact h1.hasSum
    exact (hasSum_subtype_iff_indicator (f := fun α : Occ => ‖trialState V w kc N α‖ ^ 2)
      (s := {α : Occ | α u = m})).mpr h2
  refine HasSum.sigma (f := fun x : (Σ m : ℕ, {α : Occ // α u = m}) =>
    g (e x u) * ‖trialState V w kc N (e x)‖ ^ 2) (e.hasSum_iff.mpr hA.hasSum) ?_
  intro m
  refine ((hfib m).mul_left (g m)).congr_fun ?_
  intro c
  have hc : c.1 u = m := c.2
  simp [e, hc]

/-- `Σ_γ 1_{m_c ≤ γ(u)+2} γ(u)|Ψ(γ)|²`, as a `HasSum`, and its value is the series of (5.57)
[ubpsiuPLmc]. -/
private lemma UUVV_hasSum_tail (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    HasSum (fun γ : Occ => (if mc (rhoN N) ≤ (γ u : ℝ) + 2 then (γ u : ℝ) else 0) *
        ‖trialState V w kc N γ‖ ^ 2)
      (∑' m : ℕ, (if mc (rhoN N) ≤ (m : ℝ) + 2 then
          (m : ℝ) * Expect.Qm (trialState V w kc N) [(u, m)] else 0)) := by
  have h := UUVV_fibre V w kc hN u (fun m : ℕ => if mc (rhoN N) ≤ (m : ℝ) + 2 then (m : ℝ) else 0)
    (fun α hα => by
      have := UUVV_occ_le hN hα u
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
        exact this
      · simp)
  have e : (fun m : ℕ => (if mc (rhoN N) ≤ (m : ℝ) + 2 then (m : ℝ) else 0) *
      Expect.Qm (trialState V w kc N) [(u, m)]) = fun m : ℕ => (if mc (rhoN N) ≤ (m : ℝ) + 2 then
        (m : ℝ) * Expect.Qm (trialState V w kc N) [(u, m)] else 0) := by
    funext m
    split_ifs <;> simp
  rw [e] at h
  rw [h.tsum_eq]
  exact (UUVV_summable V w kc hN (fun α => if mc (rhoN N) ≤ (α u : ℝ) + 2 then (α u : ℝ) else 0)
    N (fun α hα => by
      have := UUVV_occ_le hN hα u
      split_ifs
      · rw [abs_of_nonneg (by positivity)]
        exact this
      · simp)).hasSum

/-- Termwise bound behind (7.45) [u-uv-vPLMHproof1]–(8.2): for `u ∈ P_L`, `v ∈ P_I ∪ P_H` and
`m_c ≥ 3`. -/
private lemma UUVV_term45 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (hmc : 3 ≤ mc (rhoN N)) {u v : Idx} (hu : inPL (rhoN N) (LN N) u)
    (hv : inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v) (γ : Occ) :
    |(γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
        (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v) * UUVV_Y kc N u v γ *
        ‖trialState V w kc N γ‖ ^ 2 -
      lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
        ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (1 + (alphaStar γ u : ℝ)) *
          ‖trialState V w kc N γ‖ ^ 2)| ≤
      |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
        (((((γ u : ℝ) + 2) * (((γ v : ℝ) + γ (-v)) / 2)) +
          2 * (if mc (rhoN N) ≤ (γ u : ℝ) + 2 then (γ u : ℝ) else 0)) *
          ‖trialState V w kc N γ‖ ^ 2) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  set lu := lam V w (rhoN N) (LN N) u
  set lv := lam V w (rhoN N) (LN N) v
  have hp0 : 0 ≤ ‖trialState V w kc N γ‖ ^ 2 := by positivity
  have hγu := Nat.cast_nonneg (α := ℝ) (γ u)
  have hγv := Nat.cast_nonneg (α := ℝ) (γ v)
  have hγv' := Nat.cast_nonneg (α := ℝ) (γ (-v))
  have hg0 : 0 ≤ (if mc (rhoN N) ≤ (γ u : ℝ) + 2 then (γ u : ℝ) else 0) := by
    split_ifs <;> positivity
  have hRHS : 0 ≤ |lu * lv| * rhoN N ^ 2 *
      (((((γ u : ℝ) + 2) * (((γ v : ℝ) + γ (-v)) / 2)) +
        2 * (if mc (rhoN N) ≤ (γ u : ℝ) + 2 then (γ u : ℝ) else 0)) *
        ‖trialState V w kc N γ‖ ^ 2) := by positivity
  by_cases hΨ : trialState V w kc N γ = 0
  · simp only [hΨ, norm_zero]
    simp
  have hγ := UUVV_inM_of_ne hΨ
  obtain ⟨hW0, hW1⟩ := UUVV_W_bounds hN (UUVV_occ_le hN hΨ 0)
  by_cases h2 : 2 ≤ γ 0
  · have hAv := InM.strictIH hγ hv h2
    have hnv : ¬ inPL (rhoN N) (LN N) v := by
      rcases hv with h | h
      · exact fun h' => Regions_PL_PI h' h
      · exact fun h' => Regions_PL_PH hρ h' h
    have hst := MStar_PL_star hρ hγ hu
    have hst1 : (alphaStar γ u : ℝ) ≤ (γ u : ℝ) + 1 := by
      rcases hst with h | h
      · rw [h]
        linarith
      · rw [h]
        push_cast
        linarith
    have hst0 : (0 : ℝ) ≤ alphaStar γ u := Nat.cast_nonneg _
    by_cases hAu : InM (rhoN N) (LN N) kc N (strictPair u γ)
    · -- the case `𝓐^u γ ∈ M`
      have hY : UUVV_Y kc N u v γ = ((alphaStar γ u : ℝ) + 1) *
          Real.sqrt (((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1)) := by
        unfold UUVV_Y UUVV_Wk
        rw [ite_eq_left ⟨hAu, hAv⟩, ite_eq_left hu, ite_eq_right hnv]
      have hS1 : 1 ≤ Real.sqrt (((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1)) := by
        rw [Real.one_le_sqrt]
        have h1 : (1 : ℝ) ≤ (γ v : ℝ) + 1 := by linarith
        have h2 : (1 : ℝ) ≤ (γ (-v) : ℝ) + 1 := by linarith
        calc (1 : ℝ) = 1 * 1 := by norm_num
          _ ≤ _ := by gcongr
      have hS2 := UUVV_sqrt_sub_one (γ v : ℝ) (γ (-v) : ℝ) hγv hγv'
      set Sv := Real.sqrt (((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1))
      have e : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (lu * lv) * UUVV_Y kc N u v γ *
            ‖trialState V w kc N γ‖ ^ 2 -
          lu * lv * ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (1 + (alphaStar γ u : ℝ)) *
            ‖trialState V w kc N γ‖ ^ 2) =
          ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2) * (lu * lv) *
            (((alphaStar γ u : ℝ) + 1) * (Sv - 1) * ‖trialState V w kc N γ‖ ^ 2) := by
        rw [hY]
        ring
      have hX : 0 ≤ ((alphaStar γ u : ℝ) + 1) * (Sv - 1) * ‖trialState V w kc N γ‖ ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) hp0
      rw [e, abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_nonneg hX]
      have hb : ((alphaStar γ u : ℝ) + 1) * (Sv - 1) ≤
          ((γ u : ℝ) + 2) * (((γ v : ℝ) + γ (-v)) / 2) :=
        mul_le_mul (by linarith) hS2 (by linarith) (by positivity)
      have hgp : 0 ≤ 2 * (if mc (rhoN N) ≤ (γ u : ℝ) + 2 then (γ u : ℝ) else 0) *
          ‖trialState V w kc N γ‖ ^ 2 := by positivity
      calc _ ≤ rhoN N ^ 2 * |lu * lv| * (((γ u : ℝ) + 2) * (((γ v : ℝ) + γ (-v)) / 2) *
          ‖trialState V w kc N γ‖ ^ 2) := by
            gcongr
        _ ≤ _ := by
            have : 0 ≤ rhoN N ^ 2 * |lu * lv| := by positivity
            nlinarith [mul_nonneg this hgp]
    · -- the case `𝓐^u γ ∉ M`
      have hY : UUVV_Y kc N u v γ = 0 := by
        unfold UUVV_Y
        rw [ite_eq_right (fun h => hAu h.1)]
      have hge : mc (rhoN N) ≤ (alphaStar γ u : ℝ) := by
        by_contra hlt
        exact hAu (InM.strictL hγ hu (not_le.mp hlt) h2)
      have hstar3 : (3 : ℝ) ≤ alphaStar γ u := le_trans hmc hge
      have hgu : (2 : ℝ) ≤ γ u := by linarith
      have hind : mc (rhoN N) ≤ (γ u : ℝ) + 2 := by linarith
      rw [ite_eq_left hind] at hRHS ⊢
      have e : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (lu * lv) * UUVV_Y kc N u v γ *
            ‖trialState V w kc N γ‖ ^ 2 -
          lu * lv * ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (1 + (alphaStar γ u : ℝ)) *
            ‖trialState V w kc N γ‖ ^ 2) =
          -(((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2) * (lu * lv) *
            ((1 + (alphaStar γ u : ℝ)) * ‖trialState V w kc N γ‖ ^ 2)) := by
        rw [hY]
        ring
      have hX : 0 ≤ (1 + (alphaStar γ u : ℝ)) * ‖trialState V w kc N γ‖ ^ 2 := by positivity
      rw [e, abs_neg, abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_nonneg hX]
      have hb : 1 + (alphaStar γ u : ℝ) ≤ 2 * (γ u : ℝ) := by linarith
      have hgp : 0 ≤ ((γ u : ℝ) + 2) * (((γ v : ℝ) + γ (-v)) / 2) *
          ‖trialState V w kc N γ‖ ^ 2 := by positivity
      calc _ ≤ rhoN N ^ 2 * |lu * lv| * (2 * (γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2) := by
            gcongr
        _ ≤ _ := by
            have : 0 ≤ rhoN N ^ 2 * |lu * lv| := by positivity
            nlinarith [mul_nonneg this hgp]
  · have h0 : γ 0 ≤ 1 := by omega
    have : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h' | h' <;> simp [h']
    rw [this]
    simpa using hRHS

/-- `N ≥ 1` and `m_c ≥ 3` for all large `N`. -/
private lemma UUVV_mc_ev : ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N ∧ (3 : ℝ) ≤ mc (rhoN N) := by
  have h := (UUVV_rho_pow_tendsto (a := 1 / 200) (by norm_num)).eventually
    (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 h
  refine ⟨max N₁ 1, fun N hN => ⟨le_trans (le_max_right _ _) hN, ?_⟩⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN)
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN1
  have h0 : 0 < rhoN N ^ (1 / 200 : ℝ) := Real.rpow_pos_of_pos hρ _
  rw [mc, Real.rpow_neg hρ.le]
  rw [le_inv_comm₀ (by norm_num) h0]
  simpa using h1

/-- (7.45) [u-uv-vPLMH] of Lemma 7.4 [u-uv-vPsi], for `u ∈ P_L` and `v ∈ P_I ∪ P_H`, with `C` in
place of the constant `4`. -/
theorem Eq7_45 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u v : Idx, inPL (rhoN N) (LN N) u →
      (inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v) →
      ‖Expect.E4 (trialState V w kc N) u (-u) v (-v) -
          ((lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
            ((Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
                (LN N ^ 3) ^ 2 +
              rhoN N ^ 2 * ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
                (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2))) : ℝ) : ℂ)‖ ≤
        |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
          ((Expect.Q (trialState V w kc N) [u, v] + Expect.Q (trialState V w kc N) [u, -v]) / 2 +
            2 * Expect.Q (trialState V w kc N) [v] +
            (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
                (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) *
              (C * rhoN N ^ (1/400 : ℝ) +
                |rhoN N * lam V w (rhoN N) (LN N) u| ^ (2 * Real.sqrt (mc (rhoN N))))) := by
  obtain ⟨C₅₇, hC₅₇, N₅₇, h57⟩ := Eq7_57 hg
  obtain ⟨N₅, h557⟩ := Eq5_57 hg
  obtain ⟨N₃, hN₃⟩ := UUVV_mc_ev
  refine ⟨C₅₇ + 2, by positivity, max (max N₅₇ N₅) N₃, fun N hN kc u v hu hv => ?_⟩
  have hN57 : N₅₇ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN5 : N₅ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hN1, hmc⟩ := hN₃ N (le_trans (le_max_right _ _) hN)
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hnvL : ¬ inPL (rhoN N) (LN N) v := by
    rcases hv with h | h
    · exact fun h' => Regions_PL_PI h' h
    · exact fun h' => Regions_PL_PH hρ h' h
  have hu0 : u ≠ 0 := Regions_PL_ne_zero hρ hu
  have hv0 : v ≠ 0 := by
    rcases hv with h | h
    · exact Regions_PI_ne_zero hρ h
    · exact Regions_PH_ne_zero hρ h
  have huv : u ≠ v := fun h => hnvL (h ▸ hu)
  have huv' : u + v ≠ 0 := by
    intro h
    have : u = -v := add_eq_zero_iff_eq_neg.mp h
    exact hnvL (Regions_PL_neg.1 (this ▸ hu))
  have hE := Lemma7_3 V w kc hN1 hu0 hv0 huv huv' (Or.inl hu)
  have hP := UUVV_Puv_eq V w kc hN1 (Or.inl hu) (Or.inr hv)
  obtain ⟨hx0, hx1⟩ := UUVV_x_bounds hg hN1 hu
  have hT0 : 0 ≤ (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
      (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) := div_nonneg hx0.le (by linarith)
  set T := (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
      (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) with hT
  set e := |rhoN N * lam V w (rhoN N) (LN N) u| ^ (2 * Real.sqrt (mc (rhoN N))) with he
  set lu := lam V w (rhoN N) (LN N) u with hlu
  set lv := lam V w (rhoN N) (LN N) v with hlv
  have hp0 : 0 ≤ rhoN N ^ (1 / 400 : ℝ) := Real.rpow_nonneg hρ.le _
  have hF := UUVV_hasSum_tail V w kc hN1 u
  have hFle := h557 N hN5 kc u hu
  rw [← hT] at hFle
  have h57' := h57 N hN57 kc u hu
  rw [← hT, ← he] at h57'
  -- the three series
  have ht := (UUVV_summable_t V w kc hN1 u v).hasSum
  have hWp : HasSum (fun γ : Occ => (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
      ‖trialState V w kc N γ‖ ^ 2)
      ((Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
        (LN N ^ 3) ^ 2) := by
    refine ((UUVV_hasSum_Q00 V w kc hN1).div_const ((LN N ^ 3) ^ 2)).congr_fun ?_
    intro γ
    ring
  have hWs : HasSum (fun γ : Occ => (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
      (alphaStar γ u : ℝ) * ‖trialState V w kc N γ‖ ^ 2)
      (((LN N ^ 3) ^ 2)⁻¹ * (∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
        ‖trialState V w kc N γ‖ ^ 2)) := by
    refine ((UUVV_summable_W_star V w kc hN1 u).hasSum.mul_left (((LN N ^ 3) ^ 2)⁻¹)).congr_fun ?_
    intro γ
    ring
  have hm := ((hWp.add hWs).mul_left (lu * lv)).congr_fun (g := fun γ : Occ =>
    lu * lv * ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (1 + (alphaStar γ u : ℝ)) *
      ‖trialState V w kc N γ‖ ^ 2)) (fun γ => by ring)
  have h1 := UUVV_hasSum_Q2 V w kc hN1 u v
  have h2 := UUVV_hasSum_Q2 V w kc hN1 u (-v)
  have q3 := UUVV_hasSum_Q1 V w kc hN1 v
  have q4 := UUVV_hasSum_Q1 V w kc hN1 (-v)
  have e4 := UUVV_Q_neg1 V w kc N v
  have hB0 := ((((h1.add h2).mul_left (1 / 2 : ℝ)).add (q3.add q4)).add (hF.mul_left 2)).congr_fun
    (g := fun γ : Occ => ((((γ u : ℝ) + 2) * (((γ v : ℝ) + γ (-v)) / 2)) +
      2 * (if mc (rhoN N) ≤ (γ u : ℝ) + 2 then (γ u : ℝ) else 0)) *
      ‖trialState V w kc N γ‖ ^ 2) (fun γ => by ring)
  have hB := hB0.mul_left (|lu * lv| * rhoN N ^ 2)
  have hbound := UUVV_diff_abs ht hm hB (fun γ => UUVV_term45 V w kc hN1 hmc hu hv γ)
  rw [hE, hP, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set S57 := ((LN N ^ 3) ^ 2)⁻¹ * (∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * (alphaStar γ u : ℝ) *
    ‖trialState V w kc N γ‖ ^ 2) with hS57
  set Tt := ∑' γ : Occ, (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
    (lu * lv) * UUVV_Y kc N u v γ * ‖trialState V w kc N γ‖ ^ 2 with hTt
  set Q00 := (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
    (LN N ^ 3) ^ 2 with hQ00
  set F := ∑' m : ℕ, (if mc (rhoN N) ≤ (m : ℝ) + 2 then
    (m : ℝ) * Expect.Qm (trialState V w kc N) [(u, m)] else 0) with hFdef
  have hmain : |lu * lv * (Q00 + S57) - lu * lv * (Q00 + rhoN N ^ 2 * T)| ≤
      |lu * lv| * (rhoN N ^ 2 * T * ((C₅₇ * rhoN N ^ (1 / 400 : ℝ)) + e)) := by
    rw [← mul_sub, abs_mul, add_sub_add_left_eq_sub]
    exact mul_le_mul_of_nonneg_left (by simpa [mul_comm] using h57') (abs_nonneg _)
  calc |Tt - lu * lv * (Q00 + rhoN N ^ 2 * T)|
      ≤ |Tt - lu * lv * (Q00 + S57)| + |lu * lv * (Q00 + S57) - lu * lv * (Q00 + rhoN N ^ 2 * T)| :=
        abs_sub_le _ _ _
    _ ≤ |lu * lv| * rhoN N ^ 2 * (1 / 2 * (Expect.Q (trialState V w kc N) [u, v] +
          Expect.Q (trialState V w kc N) [u, -v]) + (Expect.Q (trialState V w kc N) [v] +
          Expect.Q (trialState V w kc N) [-v]) + 2 * F) +
        |lu * lv| * (rhoN N ^ 2 * T * ((C₅₇ * rhoN N ^ (1 / 400 : ℝ)) + e)) :=
        add_le_add hbound hmain
    _ ≤ _ := by
        rw [e4]
        have hK : 0 ≤ |lu * lv| * rhoN N ^ 2 := by positivity
        have hKF := mul_le_mul_of_nonneg_left hFle hK
        nlinarith [hKF]

/-! ### The pair series for `u, v ∈ P_L`: (7.46) [u-uv-vPL] -/

/-- Termwise bound behind (7.46) [u-uv-vPLproof1]: for `u, v ∈ P_L` with `λ_u λ_v ≥ 0`. -/
private lemma UUVV_term46 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : inPL (rhoN N) (LN N) u) (hv : inPL (rhoN N) (LN N) v)
    (hlam : 0 ≤ lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v) (γ : Occ) :
    (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 *
        (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v) * UUVV_Y kc N u v γ *
        ‖trialState V w kc N γ‖ ^ 2 -
      lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v / (LN N ^ 3) ^ 2 *
        ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * ‖trialState V w kc N γ‖ ^ 2) ≤
      |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
        (((γ u : ℝ) * (γ v : ℝ) + 2 * (γ u : ℝ) + 2 * (γ v : ℝ) + 3) *
          ‖trialState V w kc N γ‖ ^ 2) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  set lu := lam V w (rhoN N) (LN N) u
  set lv := lam V w (rhoN N) (LN N) v
  have hp0 : 0 ≤ ‖trialState V w kc N γ‖ ^ 2 := by positivity
  have hγu := Nat.cast_nonneg (α := ℝ) (γ u)
  have hγv := Nat.cast_nonneg (α := ℝ) (γ v)
  have hRHS : 0 ≤ |lu * lv| * rhoN N ^ 2 *
      (((γ u : ℝ) * (γ v : ℝ) + 2 * (γ u : ℝ) + 2 * (γ v : ℝ) + 3) *
        ‖trialState V w kc N γ‖ ^ 2) := by positivity
  by_cases hΨ : trialState V w kc N γ = 0
  · simp only [hΨ, norm_zero]
    simp
  have hγ := UUVV_inM_of_ne hΨ
  obtain ⟨hW0, hW1⟩ := UUVV_W_bounds hN (UUVV_occ_le hN hΨ 0)
  by_cases h2 : 2 ≤ γ 0
  · have hsu := MStar_PL_star hρ hγ hu
    have hsv := MStar_PL_star hρ hγ hv
    have hsu1 : (alphaStar γ u : ℝ) ≤ (γ u : ℝ) + 1 := by
      rcases hsu with h | h
      · rw [h]
        linarith
      · rw [h]
        push_cast
        linarith
    have hsv1 : (alphaStar γ v : ℝ) ≤ (γ v : ℝ) + 1 := by
      rcases hsv with h | h
      · rw [h]
        linarith
      · rw [h]
        push_cast
        linarith
    have hsu0 : (0 : ℝ) ≤ alphaStar γ u := Nat.cast_nonneg _
    have hsv0 : (0 : ℝ) ≤ alphaStar γ v := Nat.cast_nonneg _
    have hY : UUVV_Y kc N u v γ ≤ ((alphaStar γ u : ℝ) + 1) * ((alphaStar γ v : ℝ) + 1) := by
      unfold UUVV_Y UUVV_Wk
      split_ifs
      · exact le_rfl
      · positivity
    have hX : ((alphaStar γ u : ℝ) + 1) * ((alphaStar γ v : ℝ) + 1) - 1 ≤
        (γ u : ℝ) * (γ v : ℝ) + 2 * (γ u : ℝ) + 2 * (γ v : ℝ) + 3 := by
      nlinarith [mul_le_mul hsu1 hsv1 hsv0 (by linarith)]
    have e : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (lu * lv) * UUVV_Y kc N u v γ *
          ‖trialState V w kc N γ‖ ^ 2 -
        lu * lv / (LN N ^ 3) ^ 2 * ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * ‖trialState V w kc N γ‖ ^ 2) =
        ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (lu * lv) *
          ‖trialState V w kc N γ‖ ^ 2) * (UUVV_Y kc N u v γ - 1) := by
      ring
    rw [e, abs_of_nonneg hlam]
    have hc : 0 ≤ (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (lu * lv) *
        ‖trialState V w kc N γ‖ ^ 2 := by positivity
    calc _ ≤ ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 * (lu * lv) *
          ‖trialState V w kc N γ‖ ^ 2) *
          ((γ u : ℝ) * (γ v : ℝ) + 2 * (γ u : ℝ) + 2 * (γ v : ℝ) + 3) :=
          mul_le_mul_of_nonneg_left (by linarith) hc
      _ ≤ (rhoN N ^ 2 * (lu * lv) * ‖trialState V w kc N γ‖ ^ 2) *
          ((γ u : ℝ) * (γ v : ℝ) + 2 * (γ u : ℝ) + 2 * (γ v : ℝ) + 3) := by
          gcongr
      _ = _ := by ring
  · have h0 : γ 0 ≤ 1 := by omega
    have : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with h' | h' <;> simp [h']
    rw [this]
    simpa using hRHS

/-- (7.46) [u-uv-vPL] of Lemma 7.4 [u-uv-vPsi], for `u, v ∈ P_L` with `u ≠ ±v` (one-sided). -/
theorem Eq7_46 {V w : R3 → ℝ} (hg : 0 < g0 V w) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : inPL (rhoN N) (LN N) u) (hv : inPL (rhoN N) (LN N) v) (huv : u ≠ v)
    (huv' : u + v ≠ 0) :
    (Expect.E4 (trialState V w kc N) u (-u) v (-v)).re -
        lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
          (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
            (LN N ^ 3) ^ 2 ≤
      |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
        (Expect.Q (trialState V w kc N) [u, v] + 2 * Expect.Q (trialState V w kc N) [u] +
          2 * Expect.Q (trialState V w kc N) [v] + 3) := by
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN
  have hu0 : u ≠ 0 := Regions_PL_ne_zero hρ hu
  have hv0 : v ≠ 0 := Regions_PL_ne_zero hρ hv
  have hE := Lemma7_3 V w kc hN hu0 hv0 huv huv' (Or.inl hu)
  have hP := UUVV_Puv_eq V w kc hN (Or.inl hu) (Or.inl hv)
  have hlam : 0 ≤ lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v := by
    have h1 := (Particles_rho_lam_PL hg hρ hρ1 hu).1
    have h2 := (Particles_rho_lam_PL hg hρ hρ1 hv).1
    have h1' : lam V w (rhoN N) (LN N) u < 0 := by
      by_contra h
      push Not at h
      linarith [mul_nonneg hρ.le h]
    have h2' : lam V w (rhoN N) (LN N) v < 0 := by
      by_contra h
      push Not at h
      linarith [mul_nonneg hρ.le h]
    exact (mul_pos_of_neg_of_neg h1' h2').le
  have ht := (UUVV_summable_t V w kc hN u v).hasSum
  have hm : HasSum (fun γ : Occ => lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v /
      (LN N ^ 3) ^ 2 * ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) * ‖trialState V w kc N γ‖ ^ 2))
      (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
        (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
          (LN N ^ 3) ^ 2) := by
    have := (UUVV_hasSum_Q00 V w kc hN).mul_left
      (lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v / (LN N ^ 3) ^ 2)
    convert this using 1
    ring
  have h1 := UUVV_hasSum_Q2 V w kc hN u v
  have q1 := UUVV_hasSum_Q1 V w kc hN u
  have q2 := UUVV_hasSum_Q1 V w kc hN v
  have hΨ := (Normalization_isNState V w kc hN).1
  have hB0 := (h1.add ((q1.mul_left 2).add ((q2.mul_left 2).add (hΨ.mul_left 3)))).congr_fun
    (g := fun γ : Occ => ((γ u : ℝ) * (γ v : ℝ) + 2 * (γ u : ℝ) + 2 * (γ v : ℝ) + 3) *
      ‖trialState V w kc N γ‖ ^ 2) (fun γ => by ring)
  have hB := hB0.mul_left (|lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2)
  have hbound := UUVV_diff_le ht hm hB (fun γ => UUVV_term46 V w kc hN hu hv hlam γ)
  rw [hE, hP, Complex.ofReal_re]
  convert hbound using 2
  ring

/-- (7.45) [u-uv-vPLMH] of Lemma 7.4 [u-uv-vPsi] under the hypotheses of the paper: the
conclusion of `Eq7_45`, with `0 < g₀` from `scat_g0_pos`. -/
theorem Eq7_45_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u v : Idx, inPL (rhoN N) (LN N) u →
      (inPI (rhoN N) (LN N) v ∨ inPH (rhoN N) (LN N) v) →
      ‖Expect.E4 (trialState V w kc N) u (-u) v (-v) -
          ((lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
            ((Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
                (LN N ^ 3) ^ 2 +
              rhoN N ^ 2 * ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
                (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2))) : ℝ) : ℂ)‖ ≤
        |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
          ((Expect.Q (trialState V w kc N) [u, v] + Expect.Q (trialState V w kc N) [u, -v]) / 2 +
            2 * Expect.Q (trialState V w kc N) [v] +
            (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
                (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) *
              (C * rhoN N ^ (1/400 : ℝ) +
                |rhoN N * lam V w (rhoN N) (LN N) u| ^ (2 * Real.sqrt (mc (rhoN N))))) :=
  Eq7_45 (scat_g0_pos hV hw)

/-- (7.46) [u-uv-vPL] of Lemma 7.4 [u-uv-vPsi] under the hypotheses of the paper: the
conclusion of `Eq7_46`, with `0 < g₀` from `scat_g0_pos`. -/
theorem Eq7_46_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx} (hu : inPL (rhoN N) (LN N) u)
    (hv : inPL (rhoN N) (LN N) v) (huv : u ≠ v) (huv' : u + v ≠ 0) :
    (Expect.E4 (trialState V w kc N) u (-u) v (-v)).re -
        lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v *
          (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
            (LN N ^ 3) ^ 2 ≤
      |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 2 *
        (Expect.Q (trialState V w kc N) [u, v] + 2 * Expect.Q (trialState V w kc N) [u] +
          2 * Expect.Q (trialState V w kc N) [v] + 3) :=
  Eq7_46 (scat_g0_pos hV hw) kc hN hu hv huv huv'

end LHYUpper
