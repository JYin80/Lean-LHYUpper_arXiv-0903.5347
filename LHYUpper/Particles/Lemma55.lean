import LHYUpper.Particles.Totals
import LHYUpper.Particles.Prop55
import LHYUpper.Particles.Lower

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Elementary facts -/

/-- `|Ψ|²` vanishes off `M`. -/
private lemma Lemma55_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  rw [FIdentities_trialState, ite_eq_right hc, norm_zero]
  norm_num

/-- A restriction of a nonnegative summable family is summable. -/
private lemma Lemma55_summable_ite {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (p : Occ → Prop) [DecidablePred p] : Summable fun α => if p α then ψ α else 0 :=
  Summable.of_nonneg_of_le (fun α => by split_ifs <;> simp [hψ α])
    (fun α => by split_ifs <;> simp [hψ α]) hs

/-- A restricted family `G ψ` with `0 ≤ G ≤ B` on the support of `ψ` is summable. -/
private lemma Lemma55_summable_bdd {ψ G : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (E : Occ → Prop) [DecidablePred E] (B : ℝ) (hG0 : ∀ α, 0 ≤ G α)
    (hGB : ∀ α, ψ α ≠ 0 → G α ≤ B) : Summable fun α => if E α then G α * ψ α else 0 := by
  have hle : ∀ α, G α * ψ α ≤ B * ψ α := fun α => by
    by_cases hz : ψ α = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right (hGB α hz) (hψ α)
  refine Summable.of_nonneg_of_le (fun α => ?_) (fun α => ?_) (hs.mul_left B)
  · split_ifs
    · exact mul_nonneg (hG0 α) (hψ α)
    · exact le_rfl
  · split_ifs
    · exact hle α
    · exact (mul_nonneg (hG0 α) (hψ α)).trans (hle α)

/-- A single occupation number is at most the particle number. -/
private lemma Lemma55_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]
    exact Nat.zero_le _

/-- On the support of `Ψ`, every occupation number is at most `N`. -/
private lemma Lemma55_occ_le_N {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) (n : Idx) : (α n : ℝ) ≤ N := by
  have hρ := (Particles_rhoN_LN hN).2.1
  have := MBasic_num hρ (Lemma55_inM h)
  have h1 := Lemma55_occ_le_num α n
  rw [this] at h1
  exact_mod_cast h1

/-- `Q_Ψ({u, m})` as a restricted sum. -/
private lemma Lemma55_Qm_single (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) :
    Expect.Qm Ψ [(u, m)] = ∑' α : Occ, if α u = m then ‖Ψ α‖ ^ 2 else 0 := by
  simp [Expect.Qm, Expect.Ev]

/-- `Q_Ψ({u, m}) ≥ 0`. -/
private lemma Lemma55_Qm_nonneg (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) :
    0 ≤ Expect.Qm Ψ [(u, m)] := by
  rw [Lemma55_Qm_single]
  exact tsum_nonneg fun α => by split_ifs <;> positivity

/-- `Q_Ψ({u, m}) = 0` for `m > ⌈m_c⌉` and `u ∈ P_L`, by `α*(u) ≤ ⌈m_c⌉`, (3.8) [defmc]. -/
private lemma Lemma55_Qm_zero (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) {m : ℕ} (hm : ⌈mc (rhoN N)⌉₊ < m) :
    Expect.Qm (trialState V w kc N) [(u, m)] = 0 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  rw [Lemma55_Qm_single]
  refine (tsum_congr fun α => ?_).trans tsum_zero
  by_cases h : α u = m
  · by_cases hz : ‖trialState V w kc N α‖ ^ 2 = 0
    · rw [hz]
      simp
    · exfalso
      have h1 := MStar_PL_ceil hρ (Lemma55_inM hz) hu
      have h2 : α u ≤ alphaStar α u := le_max_left _ _
      omega
  · simp [h]

/-- `ρ_N^a → 0` for `a > 0`. -/
private lemma Lemma55_rho_pow_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.comp hT

/-- `(ρ^{1/400})^k = ρ^a` when `400 a = k`. -/
private lemma Lemma55_pow {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) (a : ℝ) (ha : a * 400 = k) :
    (ρ ^ (1 / 400 : ℝ)) ^ k = ρ ^ a := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le, ← ha]
  ring_nf

/-- On `P_L`: `0 < (ρλ_u)² < 1`. -/
private lemma Lemma55_x_bounds {V w : R3 → ℝ} (hg : 0 < g0 V w) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
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

/-- `Σ_{i < n} i = n (n − 1) / 2`. -/
private lemma Lemma55_sum_id (n : ℕ) : (∑ i ∈ Finset.range n, (i : ℝ)) = n * (n - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring


/-! ### Iterated strict pair creation -/

/-- `u ≠ -u` for `u ≠ 0`. -/
private lemma Lemma55_ne_neg {u : Idx} (hu : u ≠ 0) : u ≠ -u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
  omega

/-- For `u ≠ 0`: `(𝓐^u β)(0) = β(0) − 2`, `(𝓐^u β)(±u) = β(±u) + 1`. -/
private lemma Lemma55_apply {u : Idx} (hu : u ≠ 0) (β : Occ) :
    strictPair u β 0 = β 0 - 2 ∧ strictPair u β u = β u + 1 ∧
      strictPair u β (-u) = β (-u) + 1 := by
  have h1 : (0 : Idx) ≠ u := fun h => hu h.symm
  have h2 : (0 : Idx) ≠ -u := fun h => hu (neg_eq_zero.1 h.symm)
  have h3 : u ≠ -u := Lemma55_ne_neg hu
  have h4 : -u ≠ (0 : Idx) := fun h => hu (neg_eq_zero.1 h)
  refine ⟨?_, ?_, ?_⟩
  · rw [MBasic_strictPair_apply]
    simp [h1, h2]
  · rw [MBasic_strictPair_apply]
    simp [hu, h3]
  · rw [MBasic_strictPair_apply]
    simp [h4, h3.symm]

/-- For `u ≠ 0`: `((𝓐^u)^j β)(0) = β(0) − 2j` and `((𝓐^u)^j β)(u) = β(u) + j`. -/
private lemma Lemma55_iterate_apply {u : Idx} (hu : u ≠ 0) (β : Occ) (j : ℕ) :
    ((strictPair u)^[j] β) 0 = β 0 - 2 * j ∧ ((strictPair u)^[j] β) u = β u + j ∧
      ((strictPair u)^[j] β) (-u) = β (-u) + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨h0, hu', hn⟩ := ih
    obtain ⟨e0, eu, en⟩ := Lemma55_apply hu ((strictPair u)^[j] β)
    rw [Function.iterate_succ_apply']
    exact ⟨by rw [e0, h0]; omega, by rw [eu, hu']; omega, by rw [en, hn]; omega⟩

/-! ### Restricted sums of `|Ψ|²` -/

/-- Monotonicity of restricted sums in the event, on the support of `ψ`. -/
private lemma Lemma55_tsum_mono {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    {P Q : Occ → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ α, P α → ψ α ≠ 0 → Q α) :
    (∑' α, if P α then ψ α else 0) ≤ ∑' α, if Q α then ψ α else 0 :=
  (Lemma55_summable_ite hs hψ P).tsum_le_tsum
    (fun α => by
      by_cases hp : P α
      · by_cases hz : ψ α = 0
        · simp only [hp, ite_true, hz]
          split_ifs <;> simp
        · simp [hp, h α hp hz]
      · simp only [hp, ite_false]
        split_ifs <;> simp [hψ α])
    (Lemma55_summable_ite hs hψ Q)

/-- `Σ_{i ≤ k} Σ_α [α(u) = i] f(α) = Σ_α [α(u) ≤ k] f(α)` for a summable family `f`. -/
private lemma Lemma55_fibre_sum {f : Occ → ℝ} (hs : Summable f) (hf : ∀ α, 0 ≤ f α) (u : Idx)
    (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (∑' α : Occ, if α u = i then f α else 0) =
      ∑' α : Occ, if α u ≤ k then f α else 0 := by
  rw [← Summable.tsum_finsetSum (fun i _ => Lemma55_summable_ite hs hf (fun α => α u = i))]
  refine tsum_congr fun α => ?_
  have : (∑ i ∈ Finset.range (k + 1), if α u = i then f α else 0) =
      if α u ∈ Finset.range (k + 1) then f α else 0 :=
    Finset.sum_ite_eq (Finset.range (k + 1)) (α u) (fun _ => f α)
  rw [this]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- `N − Q_Ψ(0) ≤ K N ρ^{1/2}` with `K = (3π²)⁻¹ g₀^{3/2} + C`, from (5.32) [resultlbpsi0]. -/
private lemma Lemma55_Q0 {V w : R3 → ℝ} {kc C : ℝ} {N : ℕ} (hN : 1 ≤ N) (hC : 0 ≤ C)
    (h : rho0 (g0 V w) (rhoN N) - C * rhoN N ^ (3 / 2 + 1 / 200 : ℝ) ≤
      Expect.Q (trialState V w kc N) [0] / LN N ^ 3) :
    (N : ℝ) - Expect.Q (trialState V w kc N) [0] ≤
      ((3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) + C) * N * rhoN N ^ (1 / 2 : ℝ) := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN
  rw [le_div_iff₀ (by positivity : 0 < LN N ^ 3)] at h
  have h1 : rhoN N ^ (3 / 2 : ℝ) = rhoN N * rhoN N ^ (1 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have h2 : rhoN N ^ (3 / 2 + 1 / 200 : ℝ) = rhoN N * rhoN N ^ (1 / 2 + 1 / 200 : ℝ) := by
    rw [show (3 / 2 + 1 / 200 : ℝ) = 1 + (1 / 2 + 1 / 200) by norm_num, Real.rpow_add hρ,
      Real.rpow_one]
  have h3 : rhoN N ^ (1 / 2 + 1 / 200 : ℝ) ≤ rhoN N ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hA : (rho0 (g0 V w) (rhoN N) - C * rhoN N ^ (3 / 2 + 1 / 200 : ℝ)) * LN N ^ 3 =
      (N : ℝ) - (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) * rhoN N ^ (1 / 2 : ℝ) * N -
        C * rhoN N ^ (1 / 2 + 1 / 200 : ℝ) * N := by
    rw [rho0, h1, h2]
    linear_combination (1 - (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) * rhoN N ^ (1 / 2 : ℝ) -
      C * rhoN N ^ (1 / 2 + 1 / 200 : ℝ)) * hNL
  rw [hA] at h
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C * (N : ℝ))
  nlinarith

/-! ### Jensen's inequality for `t ↦ t^k` in tangent form -/

/-- If `c > 0` is at most the `ψ`-mean of `z ≥ 0` over `E`, then `c^k Σ_E ψ ≤ Σ_E z^k ψ`; this is
the Jensen step of (5.48) [lastlb2.1], from the tangent line of `t ↦ t^k` at `c`. -/
private lemma Lemma55_tangent {ψ z : Occ → ℝ} (E : Occ → Prop) [DecidablePred E]
    (hψ0 : ∀ β, 0 ≤ ψ β) (hz0 : ∀ β, 0 ≤ z β)
    (hs1 : Summable fun β => if E β then ψ β else 0)
    (hs2 : Summable fun β => if E β then z β * ψ β else 0) (k : ℕ)
    (hs3 : Summable fun β => if E β then z β ^ k * ψ β else 0) {c : ℝ} (hc : 0 < c)
    (hmean : c * (∑' β, if E β then ψ β else 0) ≤ ∑' β, if E β then z β * ψ β else 0) :
    c ^ k * (∑' β, if E β then ψ β else 0) ≤ ∑' β, if E β then z β ^ k * ψ β else 0 := by
  set a : ℝ := c ^ k * (1 - k) with ha
  set b : ℝ := k * c ^ k / c with hb
  have hb0 : 0 ≤ b := by positivity
  have hpt : ∀ β, a * (if E β then ψ β else 0) + b * (if E β then z β * ψ β else 0) ≤
      if E β then z β ^ k * ψ β else 0 := by
    intro β
    split_ifs
    · have h1 := one_add_mul_le_pow (a := z β / c - 1)
        (by have := div_nonneg (hz0 β) hc.le; linarith) k
      have e : 1 + (z β / c - 1) = z β / c := by ring
      rw [e, div_pow, le_div_iff₀ (pow_pos hc k)] at h1
      have h2 := mul_le_mul_of_nonneg_right h1 (hψ0 β)
      have e2 : (1 + (k : ℝ) * (z β / c - 1)) * c ^ k * ψ β = a * ψ β + b * (z β * ψ β) := by
        rw [ha, hb]
        field_simp
        ring
      linarith
    · simp
  have hL : Summable fun β => a * (if E β then ψ β else 0) +
      b * (if E β then z β * ψ β else 0) := (hs1.mul_left a).add (hs2.mul_left b)
  have h1 := hL.tsum_le_tsum hpt hs3
  rw [(hs1.mul_left a).tsum_add (hs2.mul_left b), tsum_mul_left, tsum_mul_left] at h1
  have h2 := mul_le_mul_of_nonneg_left hmean hb0
  have e : a * (∑' β, if E β then ψ β else 0) + b * (c * ∑' β, if E β then ψ β else 0) =
      c ^ k * ∑' β, if E β then ψ β else 0 := by
    rw [ha, hb]
    field_simp
    ring
  linarith

/-! ### The estimates behind (5.58) [lbpsiuPL0] -/

/-- `a (a − 1) ≥ 0` for a natural number `a`. -/
private lemma Lemma55_nat_mul_pred (a : ℕ) : 0 ≤ (a : ℝ) * ((a : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos a with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ a := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)

/-- `(d − 1)₊^{2m+2} ≤ d (d − 1) d^{2m}` for a natural number `d`. -/
private lemma Lemma55_pow_le (m d : ℕ) :
    max ((d : ℝ) - 1) 0 ^ (2 * m + 2) ≤ (d : ℝ) * ((d : ℝ) - 1) * (d : ℝ) ^ (2 * m) := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h
    simp
  · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast h
    rw [max_eq_left (by linarith)]
    have e : ((d : ℝ) - 1) ^ (2 * m + 2) = ((d : ℝ) - 1) ^ 2 * ((d : ℝ) - 1) ^ (2 * m) := by
      ring
    rw [e]
    have h2 : ((d : ℝ) - 1) ^ 2 ≤ (d : ℝ) * ((d : ℝ) - 1) := by nlinarith
    have h3 : ((d : ℝ) - 1) ^ (2 * m) ≤ (d : ℝ) ^ (2 * m) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    exact mul_le_mul h2 h3 (by positivity) (by nlinarith)

/-- (5.46) [mcmlbum1] on the event `β*(u) + m + 2 ≤ ⌊m_c⌋` used for (5.58) [lbpsiuPL0]: on `P_L`,
for `m + 3 ≤ ⌊m_c⌋`, `(⌊m_c⌋ − m − 2)/(⌈m_c⌉ + 1) ≤ Σ_{β*(u) + m + 2 ≤ ⌊m_c⌋} |Ψ(β)|²`. -/
private lemma Lemma55_PE {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u → ∀ m : ℕ,
      m + 3 ≤ ⌊mc (rhoN N)⌋₊ →
      ((⌊mc (rhoN N)⌋₊ : ℝ) - m - 2) / ((⌈mc (rhoN N)⌉₊ : ℝ) + 1) ≤
        ∑' β : Occ, if alphaStar β u + m + 2 ≤ ⌊mc (rhoN N)⌋₊ then
          ‖trialState V w kc N β‖ ^ 2 else 0 := by
  obtain ⟨N₄, h46⟩ := Eq5_46 hg
  refine ⟨max N₄ 1, fun N hN kc u hu m hm => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₄ : N₄ ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  have hψs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ0 : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  have hmc0 : 0 ≤ mc (rhoN N) := Real.rpow_nonneg hρ.le _
  set M := ⌈mc (rhoN N)⌉₊ with hM
  set Kf := ⌊mc (rhoN N)⌋₊ with hKf
  have hKM : Kf ≤ M := Nat.floor_le_ceil _
  set k := Kf - m - 3 with hk
  have hkM : k ≤ M := by omega
  have h1 := h46 N hN₄ kc u hu k hkM
  simp_rw [Lemma55_Qm_single] at h1
  rw [Lemma55_fibre_sum hψs hψ0 u k] at h1
  have hkr : (k : ℝ) + 1 = (Kf : ℝ) - m - 2 := by
    have : k + m + 3 = Kf := by omega
    have h' : ((k + m + 3 : ℕ) : ℝ) = (Kf : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  rw [hkr] at h1
  refine h1.trans (Lemma55_tsum_mono hψs hψ0 fun α hα hz => ?_)
  rcases MStar_PL_star hρ (Lemma55_inM hz) hu with h | h <;> omega

/-- (5.48)–(5.49) summed, with the weight `α(0)(α(0) − 1)`: on `P_L`, for `1 ≤ m`,
`(λ_u²/|Λ|²)^m Σ_{β*(u) + m + 2 ≤ ⌊m_c⌋} (β(0) − 2m − 1)₊^{2m+2} |Ψ(β)|² ≤
Σ_{m ≤ α(u), α(u) + 2 ≤ ⌊m_c⌋} α(0)(α(0) − 1) |Ψ(α)|²`, by injectivity of `(𝓐^u)^m`. -/
private lemma Lemma55_inj_bound (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) {m : ℕ} (hm : 1 ≤ m) :
    (lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2) ^ m *
        (∑' β : Occ, if alphaStar β u + m + 2 ≤ ⌊mc (rhoN N)⌋₊ then
          max ((β 0 : ℝ) - (2 * m + 1)) 0 ^ (2 * m + 2) * ‖trialState V w kc N β‖ ^ 2
            else 0) ≤
      ∑' α : Occ, if m ≤ α u ∧ α u + 2 ≤ ⌊mc (rhoN N)⌋₊ then
        (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hu0 : u ≠ 0 := Regions_PL_ne_zero hρ hu
  have hΨ := Normalization_isNState V w kc hN
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψ
  have hψs : Summable ψ := hΨ.1.summable
  have hψ0 : ∀ α, 0 ≤ ψ α := fun _ => by positivity
  set A := lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set E : Occ → Prop := fun β => alphaStar β u + m + 2 ≤ ⌊mc (rhoN N)⌋₊ with hE
  set z : Occ → ℝ := fun β => max ((β 0 : ℝ) - (2 * m + 1)) 0 with hz
  set F : Occ → ℝ := fun β => if E β then A ^ m * (z β ^ (2 * m + 2) * ψ β) else 0 with hF
  have hzN : ∀ β, ψ β ≠ 0 → z β ^ (2 * m + 2) ≤ (N : ℝ) ^ (2 * m + 2) := fun β hβ => by
    refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ (Nat.cast_nonneg N)) _
    have := Lemma55_occ_le_N hN hβ 0
    have : (0 : ℝ) ≤ 2 * m + 1 := by positivity
    linarith
  have hFs : Summable F := by
    have := (Lemma55_summable_bdd hψs hψ0 E _ (fun β => by positivity) hzN).mul_left (A ^ m)
    refine this.congr fun β => ?_
    simp only [hF, mul_ite, mul_zero]
  have hgs := Lemma55_summable_bdd hψs hψ0 (fun α => m ≤ α u ∧ α u + 2 ≤ ⌊mc (rhoN N)⌋₊)
    ((N : ℝ) ^ 2) (G := fun α => (α 0 : ℝ) * ((α 0 : ℝ) - 1))
    (fun α => Lemma55_nat_mul_pred _) (fun α hα => by
      have h0 := Lemma55_occ_le_N hN hα 0
      have h1 : (0 : ℝ) ≤ α 0 := Nat.cast_nonneg _
      nlinarith)
  -- the summands of `F` vanish off `S`
  set S : Set Occ := {β | InM (rhoN N) (LN N) kc N β ∧ E β ∧ 2 * m ≤ β 0} with hS
  have hFS : ∀ β, F β = S.indicator F β := by
    intro β
    by_cases hβ : β ∈ S
    · rw [Set.indicator_of_mem hβ]
    · rw [Set.indicator_of_notMem hβ]
      simp only [hS, Set.mem_ofPred_eq, not_and_or] at hβ
      simp only [hF]
      split_ifs with hE'
      · rcases hβ with h | h | h
        · by_cases hz0 : ψ β = 0
          · rw [hz0]; ring
          · exact absurd (Lemma55_inM hz0) h
        · exact absurd hE' h
        · have : z β = 0 := by
            simp only [hz]
            refine max_eq_right ?_
            have : (β 0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast not_le.1 h
            push_cast at this
            linarith
          rw [this, zero_pow (by omega)]
          ring
      · rfl
  have hsum : (∑' β, F β) = ∑' x : S, F x := by
    rw [tsum_subtype S F]
    exact tsum_congr hFS
  have hLHS : A ^ m * (∑' β : Occ, if E β then z β ^ (2 * m + 2) * ψ β else 0) = ∑' β, F β := by
    rw [← tsum_mul_left]
    refine tsum_congr fun β => ?_
    simp only [hF, mul_ite, mul_zero]
  change A ^ m * (∑' β : Occ, if E β then z β ^ (2 * m + 2) * ψ β else 0) ≤ _
  rw [hLHS, hsum]
  refine Summable.tsum_le_tsum_of_inj (fun x : S => (strictPair u)^[m] x.1) ?_
    (fun _ _ => by split_ifs <;> first | exact mul_nonneg (Lemma55_nat_mul_pred _) (hψ0 _) | simp)
    (fun x => ?_) (hFs.subtype (· ∈ S)) hgs
  · intro x y hxy
    exact Subtype.ext (Particles_iterate_injOn u m x.2.2.2 y.2.2.2 hxy)
  · obtain ⟨hxM, hxE, hx0⟩ := x.2
    obtain ⟨hγ0, hxu, -⟩ := Lemma55_iterate_apply hu0 x.1 m
    have hxle : x.1 u ≤ alphaStar x.1 u := le_max_left _ _
    have hKM : ⌊mc (rhoN N)⌋₊ ≤ ⌈mc (rhoN N)⌉₊ := Nat.floor_le_ceil _
    have hxE' : alphaStar x.1 u + m ≤ ⌈mc (rhoN N)⌉₊ := by
      simp only [hE] at hxE
      omega
    have hcond : m ≤ ((strictPair u)^[m] x.1) u ∧
        ((strictPair u)^[m] x.1) u + 2 ≤ ⌊mc (rhoN N)⌋₊ := by
      simp only [hE] at hxE
      omega
    have hit := (Particles_iterate V w kc hN hu m hxM hxE' hx0).2
    have hd : (((strictPair u)^[m] x.1) 0 : ℝ) = (x.1 0 : ℝ) - 2 * m := by
      rw [hγ0, Nat.cast_sub hx0]
      push_cast
      ring
    set d : ℕ := ((strictPair u)^[m] x.1) 0 with hdd
    have hzx : z x.1 = max ((d : ℝ) - 1) 0 := by
      simp only [hz]
      rw [hd]
      congr 1
      ring
    have hdn := Lemma55_nat_mul_pred d
    have hpl := Lemma55_pow_le m d
    simp only [hF, hxE, ite_true, hcond, and_self, hzx]
    have hdn' : 0 ≤ ((x.1 0 : ℝ) - 2 * m) * (((x.1 0 : ℝ) - 2 * m) - 1) := by
      rw [← hd]
      exact hdn
    have hit' : A ^ m * ((x.1 0 : ℝ) - 2 * m) ^ (2 * m) * ψ x.1 ≤
        ‖trialState V w kc N ((strictPair u)^[m] x.1)‖ ^ 2 := by
      simpa only [hψ] using hit
    have hAψ : 0 ≤ A ^ m * ψ x.1 := by have := hψ0 x.1; positivity
    calc A ^ m * (max ((d : ℝ) - 1) 0 ^ (2 * m + 2) * ψ x.1)
        = max ((d : ℝ) - 1) 0 ^ (2 * m + 2) * (A ^ m * ψ x.1) := by ring
      _ ≤ ((d : ℝ) * ((d : ℝ) - 1) * (d : ℝ) ^ (2 * m)) * (A ^ m * ψ x.1) :=
          mul_le_mul_of_nonneg_right hpl hAψ
      _ = ((x.1 0 : ℝ) - 2 * m) * (((x.1 0 : ℝ) - 2 * m) - 1) *
            (A ^ m * ((x.1 0 : ℝ) - 2 * m) ^ (2 * m) * ψ x.1) := by rw [hd]; ring
      _ ≤ ((x.1 0 : ℝ) - 2 * m) * (((x.1 0 : ℝ) - 2 * m) - 1) *
            ‖trialState V w kc N ((strictPair u)^[m] x.1)‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hit' hdn'
      _ = _ := by rw [hd]

/-- (5.48)–(5.54) [lastlb4] for one `m`, with the weight of (5.58) [lbpsiuPL0]: on `P_L`, for
`1 ≤ m ≤ n`, with `θ = 1 − (2n + 1)/N − 2Kρ^{1/2} > 0`, `N − Q_Ψ(0) ≤ KNρ^{1/2}` ((5.32)
[resultlbpsi0]) and `Σ_{β*(u) + m + 2 ≤ ⌊m_c⌋} |Ψ|² ≥ 1/2`:
`((ρλ_u)² θ²)^m (Nθ)² Σ_{β*(u) + m + 2 ≤ ⌊m_c⌋} |Ψ|² ≤
Σ_{m ≤ α(u), α(u) + 2 ≤ ⌊m_c⌋} α(0)(α(0) − 1) |Ψ|²`. -/
private lemma Lemma55_Tm (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN1 : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) {K θ : ℝ} (hK0 : 0 ≤ K)
    (hQ0 : (N : ℝ) - Expect.Q (trialState V w kc N) [0] ≤ K * N * rhoN N ^ (1 / 2 : ℝ))
    {m n : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hθ : θ = 1 - (2 * n + 1) / N - 2 * K * rhoN N ^ (1 / 2 : ℝ)) (hθ0 : 0 < θ)
    (hPhalf : 1 / 2 ≤ ∑' β : Occ, if alphaStar β u + m + 2 ≤ ⌊mc (rhoN N)⌋₊ then
      ‖trialState V w kc N β‖ ^ 2 else 0) :
    ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 * θ ^ 2) ^ m * ((N : ℝ) * θ) ^ 2 *
        (∑' β : Occ, if alphaStar β u + m + 2 ≤ ⌊mc (rhoN N)⌋₊ then
          ‖trialState V w kc N β‖ ^ 2 else 0) ≤
      ∑' α : Occ, if m ≤ α u ∧ α u + 2 ≤ ⌊mc (rhoN N)⌋₊ then
        (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψ
  have hψs : Summable ψ := hΨ.1.summable
  have hψ0 : ∀ α, 0 ≤ ψ α := fun _ => by positivity
  set ρ := rhoN N with hρdef
  set c : ℝ := N * θ with hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := by positivity
  set x : ℝ := (ρ * lam V w ρ (LN N) u) ^ 2 with hx
  set A := lam V w ρ (LN N) u ^ 2 / (LN N ^ 3) ^ 2 with hA
  have hAc : A * c ^ 2 = x * θ ^ 2 := by
    rw [hA, hc, hx, ← hNL]
    field_simp
  set E : Occ → Prop := fun β => alphaStar β u + m + 2 ≤ ⌊mc ρ⌋₊ with hE
  set P := ∑' β : Occ, if E β then ψ β else 0 with hP
  have hev := Prop5_5_event V w kc hN1 E
  set z : Occ → ℝ := fun β => max ((β 0 : ℝ) - (2 * m + 1)) 0 with hz
  have hzN : ∀ β, ψ β ≠ 0 → z β ≤ N := fun β hβ => by
    refine max_le ?_ (Nat.cast_nonneg N)
    have := Lemma55_occ_le_N hN1 hβ 0
    have : (0 : ℝ) ≤ 2 * m + 1 := by positivity
    linarith
  have hz0 : ∀ β, 0 ≤ z β := fun β => le_max_right _ _
  have hs1 := Lemma55_summable_ite hψs hψ0 E
  have hs2 := Lemma55_summable_bdd hψs hψ0 E N hz0 hzN
  have hs0 := Lemma55_summable_bdd hψs hψ0 E N (G := fun β => (β 0 : ℝ))
    (fun _ => by positivity) (fun β hβ => Lemma55_occ_le_N hN1 hβ 0)
  have hs3 := Lemma55_summable_bdd hψs hψ0 E ((N : ℝ) ^ (2 * m + 2))
    (G := fun β => z β ^ (2 * m + 2))
    (fun β => by positivity) (fun β hβ => pow_le_pow_left₀ (hz0 β) (hzN β hβ) _)
  have hmean : c * P ≤ ∑' β, if E β then z β * ψ β else 0 := by
    have h1 : (∑' β, if E β then ((β 0 : ℝ) - (2 * m + 1)) * ψ β else 0) ≤
        ∑' β, if E β then z β * ψ β else 0 := by
      have hs4 : Summable fun β => if E β then ((β 0 : ℝ) - (2 * m + 1)) * ψ β else 0 := by
        refine (hs0.sub (hs1.mul_left (2 * (m : ℝ) + 1))).congr fun β => ?_
        split_ifs <;> ring
      refine hs4.tsum_le_tsum (fun β => ?_) hs2
      split_ifs
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hψ0 β)
      · exact le_rfl
    have h2 : (∑' β, if E β then ((β 0 : ℝ) - (2 * m + 1)) * ψ β else 0) =
        (∑' β, if E β then (β 0 : ℝ) * ψ β else 0) - (2 * m + 1) * P := by
      rw [hP, ← tsum_mul_left, ← hs0.tsum_sub (hs1.mul_left _)]
      refine tsum_congr fun β => ?_
      split_ifs <;> ring
    have h3 : (N : ℝ) * P - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) ≤
        ∑' β, if E β then (β 0 : ℝ) * ψ β else 0 := by
      convert hev
    have h4 : c * P ≤ (N : ℝ) * P - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) -
        (2 * m + 1) * P := by
      have e : (N : ℝ) * P - (2 * m + 1) * P - c * P = (2 * n - 2 * m) * P +
          2 * K * N * ρ ^ (1 / 2 : ℝ) * P := by
        rw [hc, hθ]
        field_simp
        ring
      have h5 : 0 ≤ (2 * (n : ℝ) - 2 * m) * P := by
        have : (m : ℝ) ≤ n := by exact_mod_cast hmn
        exact mul_nonneg (by linarith) (by linarith)
      have h6 : K * N * ρ ^ (1 / 2 : ℝ) ≤ 2 * K * N * ρ ^ (1 / 2 : ℝ) * P := by
        have h0 : 0 ≤ K * N * ρ ^ (1 / 2 : ℝ) := by positivity
        have := mul_le_mul_of_nonneg_left hPhalf h0
        linarith
      linarith
    linarith
  have htan := Lemma55_tangent E hψ0 hz0 hs1 hs2 (2 * m + 2) hs3 hc0 hmean
  have hinj := Lemma55_inj_bound V w kc hN1 hu hm1
  have e : (x * θ ^ 2) ^ m * (N * θ) ^ 2 = A ^ m * c ^ (2 * m + 2) := by
    rw [← hAc, mul_pow, ← pow_mul, ← hc]
    ring
  calc (x * θ ^ 2) ^ m * (N * θ) ^ 2 * P = A ^ m * (c ^ (2 * m + 2) * P) := by rw [e]; ring
    _ ≤ A ^ m * (∑' β, if E β then z β ^ (2 * m + 2) * ψ β else 0) :=
        mul_le_mul_of_nonneg_left htan (by positivity)
    _ ≤ _ := hinj

/-- `Σ_{j < n} Σ_α [j + 1 ≤ α(u), α(u) + 2 ≤ m_c] α(0)(α(0) − 1) |Ψ(α)|² ≤
Σ_α [α(u) + 2 ≤ m_c] α(0)(α(0) − 1) α(u) |Ψ(α)|²`, from `Σ_{j < n} [j + 1 ≤ k] ≤ k`. -/
private lemma Lemma55_sum_ge (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) (n : ℕ) :
    ∑ j ∈ Finset.range n, (∑' α : Occ, if j + 1 ≤ α u ∧ α u + 2 ≤ ⌊mc (rhoN N)⌋₊ then
        (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      ∑' α : Occ, if (α u : ℝ) + 2 ≤ mc (rhoN N) then
        (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  have hψs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ0 : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  have hmc0 : 0 ≤ mc (rhoN N) := Real.rpow_nonneg hρ.le _
  have hiff : ∀ α : Occ, ((α u : ℝ) + 2 ≤ mc (rhoN N)) ↔ α u + 2 ≤ ⌊mc (rhoN N)⌋₊ := by
    intro α
    rw [Nat.le_floor_iff hmc0]
    push_cast
    rfl
  have hsj : ∀ j : ℕ, Summable fun α : Occ => if j + 1 ≤ α u ∧ α u + 2 ≤ ⌊mc (rhoN N)⌋₊ then
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2 else 0 := fun j =>
    Lemma55_summable_bdd hψs hψ0 (fun α => j + 1 ≤ α u ∧ α u + 2 ≤ ⌊mc (rhoN N)⌋₊)
      ((N : ℝ) ^ 2) (G := fun α => (α 0 : ℝ) * ((α 0 : ℝ) - 1))
      (fun α => Lemma55_nat_mul_pred _) (fun α hα => by
        have h0 := Lemma55_occ_le_N hN hα 0
        have h1 : (0 : ℝ) ≤ α 0 := Nat.cast_nonneg _
        nlinarith)
  have hS : Summable fun α : Occ => if (α u : ℝ) + 2 ≤ mc (rhoN N) then
      (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 :=
    Lemma55_summable_bdd hψs hψ0 (fun α => (α u : ℝ) + 2 ≤ mc (rhoN N))
      ((N : ℝ) ^ 2 * N) (G := fun α => (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ))
      (fun α => mul_nonneg (Lemma55_nat_mul_pred _) (Nat.cast_nonneg _)) (fun α hα => by
        have h0 := Lemma55_occ_le_N hN hα 0
        have h1 := Lemma55_occ_le_N hN hα u
        have h2 : (0 : ℝ) ≤ α 0 := Nat.cast_nonneg _
        have h3 : (0 : ℝ) ≤ α u := Nat.cast_nonneg _
        have h4 : (α 0 : ℝ) * ((α 0 : ℝ) - 1) ≤ (N : ℝ) ^ 2 := by nlinarith
        exact mul_le_mul h4 h1 h3 (by positivity))
  rw [← Summable.tsum_finsetSum (fun j _ => hsj j)]
  refine (summable_sum fun j _ => hsj j).tsum_le_tsum (fun α => ?_) hS
  by_cases hc : α u + 2 ≤ ⌊mc (rhoN N)⌋₊
  · have hc' : (α u : ℝ) + 2 ≤ mc (rhoN N) := (hiff α).2 hc
    simp only [hc, hc', and_true, ite_true]
    set g : ℝ := (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2 with hg
    have hg0 : 0 ≤ g := mul_nonneg (Lemma55_nat_mul_pred _) (hψ0 α)
    have e : (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 =
        (α u : ℝ) * g := by
      rw [hg]; ring
    rw [e, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hg0
    have : ((Finset.range n).filter fun j => j + 1 ≤ α u) ⊆ Finset.range (α u) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      omega
    have h2 := Finset.card_le_card this
    rw [Finset.card_range] at h2
    exact_mod_cast h2
  · have hc' : ¬ ((α u : ℝ) + 2 ≤ mc (rhoN N)) := fun h => hc ((hiff α).1 h)
    simp [hc, hc']

/-- The final inequality of the tail estimate: `S ≤ 3 M a`, `a j (j + 1)/2 ≤ Q`,
`Q ≤ X (1 + C r^{396})`, `M = j + 2`, `M r² ≥ 1` and `r ≤ 1/13` give `S ≤ X r`. -/
private lemma Lemma55_tail_alg {S Q a X C r M j : ℝ} (hS0 : 0 ≤ S) (hS3 : S ≤ 3 * (M * a))
    (hQlow : a * ((j + 1) * j) / 2 ≤ Q) (hQ : Q ≤ X * (1 + C * r ^ 396))
    (hX0 : 0 ≤ X) (hMr : M = j + 2) (hj : 167 ≤ j) (hMr2 : 1 ≤ M * r ^ 2) (hr0 : 0 < r)
    (hr13 : r ≤ 1 / 13) (hCr : C * r ^ 396 ≤ 1 / 12) : S ≤ X * r := by
  have hMpos : 0 < M := by rw [hMr]; linarith
  have h1 : S * (j * (j + 1)) ≤ 3 * (M * a) * (j * (j + 1)) :=
    mul_le_mul_of_nonneg_right hS3 (by positivity)
  have h2 : a * ((j + 1) * j) ≤ 2 * Q := by linarith
  have h3 : 3 * (M * a) * (j * (j + 1)) ≤ 6 * M * Q := by
    have e : 3 * (M * a) * (j * (j + 1)) = 3 * M * (a * ((j + 1) * j)) := by ring
    rw [e]
    nlinarith
  have h4 : M ^ 2 ≤ 2 * (j * (j + 1)) := by
    rw [hMr]
    nlinarith
  have h5 : S * M ^ 2 ≤ 2 * (S * (j * (j + 1))) := by
    have := mul_le_mul_of_nonneg_left h4 hS0
    linarith
  have h6 : M * (S * M) ≤ M * (12 * Q) := by nlinarith
  have hSM : S * M ≤ 12 * Q := le_of_mul_le_mul_left h6 hMpos
  have hQ' : Q ≤ X * (13 / 12) := by
    have := mul_le_mul_of_nonneg_left hCr hX0
    nlinarith
  calc S ≤ S * (M * r ^ 2) := by
        have := mul_le_mul_of_nonneg_left hMr2 hS0
        linarith
    _ = (S * M) * r ^ 2 := by ring
    _ ≤ (12 * Q) * r ^ 2 := mul_le_mul_of_nonneg_right hSM (sq_nonneg r)
    _ ≤ (12 * (X * (13 / 12))) * r ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg r)
    _ ≤ X * r := by
        have h13 : 13 * r ≤ 1 := by linarith
        have : X * r * (1 - 13 * r) ≥ 0 := mul_nonneg (mul_nonneg hX0 hr0.le) (by linarith)
        nlinarith

/-- (5.57) [ubpsiuPLmc], over the occupations `m` with `m_c ≤ m + 2`. -/
theorem Eq5_57 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      ∑' m : ℕ, (if mc (rhoN N) ≤ (m : ℝ) + 2 then
          (m : ℝ) * Expect.Qm (trialState V w kc N) [(u, m)] else 0) ≤
        (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) * rhoN N ^ (1/400 : ℝ) := by
  obtain ⟨C, hC, N₁, h54⟩ := Lemma5_4_PL hg
  obtain ⟨C₂, -, N₂, h45⟩ := Eq5_45 hg
  have hev1 : ∀ᶠ N : ℕ in atTop, rhoN N ^ (1 / 400 : ℝ) ≤ 1 / 13 :=
    (Lemma55_rho_pow_tendsto (by norm_num)).eventually (ge_mem_nhds (by norm_num))
  have hev2 : ∀ᶠ N : ℕ in atTop, C * rhoN N ^ (99 / 100 : ℝ) ≤ 1 / 12 := by
    have h := (Lemma55_rho_pow_tendsto (a := 99 / 100) (by norm_num)).const_mul C
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨max (max (max N₁ N₂) N₃) 1, fun N hN kc u hu => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₁ : N₁ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₂ : N₂ ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₃' : N₃ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hr13, hCr⟩ := hN₃ N hN₃'
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨hx0, hx1⟩ := Lemma55_x_bounds hg hN1 hu
  have hQ54 := h54 N hN₁ kc u hu
  have hanti : Antitone fun m : ℕ => Expect.Qm (trialState V w kc N) [(u, m)] :=
    antitone_nat_of_succ_le fun i => (h45 N hN₂ kc u hu i).2
  have ha0 : ∀ m : ℕ, 0 ≤ Expect.Qm (trialState V w kc N) [(u, m)] := fun m =>
    Lemma55_Qm_nonneg _ u m
  have haM : ∀ m : ℕ, ⌈mc (rhoN N)⌉₊ < m → Expect.Qm (trialState V w kc N) [(u, m)] = 0 :=
    fun m hm => Lemma55_Qm_zero V w kc hN1 hu hm
  have hQeq := Particles_Q_eq_tsum V w kc hN1 u
  set ρ := rhoN N with hρdef
  set r : ℝ := ρ ^ (1 / 400 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ _
  have hpow : ∀ (k : ℕ) (a : ℝ), a * 400 = k → r ^ k = ρ ^ a := fun k a ha =>
    Lemma55_pow hρ k a ha
  have hmc : mc ρ = (r ^ 2)⁻¹ := by
    rw [mc, Real.rpow_neg hρ.le, hpow 2 (1 / 200) (by norm_num)]
  have hε : epsP ρ = r ^ 2 := (hpow 2 (1 / 200) (by norm_num)).symm
  have hr400 : r ^ 400 = ρ := by rw [hpow 400 1 (by norm_num), Real.rpow_one]
  have hCr' : C * r ^ 396 ≤ 1 / 12 := by
    rw [hpow 396 (99 / 100) (by norm_num)]
    exact hCr
  set x : ℝ := (ρ * lam V w ρ (LN N) u) ^ 2 with hx
  set X : ℝ := x / (1 - x) with hX
  have hX0 : 0 ≤ X := div_nonneg hx0.le (by linarith)
  have hQ : Expect.Q (trialState V w kc N) [u] ≤ X * (1 + C * r ^ 396) := by
    refine hQ54.trans (le_of_eq ?_)
    have e : C * ρ * mc ρ / epsP ρ = C * r ^ 396 := by
      rw [hmc, hε, ← hr400]
      field_simp
    rw [e]
  set M := ⌈mc ρ⌉₊ with hM
  have hM1 : (r ^ 2)⁻¹ ≤ M := by rw [← hmc]; exact Nat.le_ceil _
  have hr2 : r ^ 2 ≤ 1 / 169 := by
    have := pow_le_pow_left₀ hr0.le hr13 2
    norm_num at this ⊢
    linarith
  have hM169 : 169 ≤ M := by
    have h1 : (169 : ℝ) ≤ (r ^ 2)⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) (by positivity)]
      linarith
    exact_mod_cast h1.trans hM1
  obtain ⟨j, hj⟩ : ∃ j, M = j + 2 := ⟨M - 2, by omega⟩
  set a : ℕ → ℝ := fun m => Expect.Qm (trialState V w kc N) [(u, m)] with ha
  set f : ℕ → ℝ := fun m => if mc ρ ≤ (m : ℝ) + 2 then (m : ℝ) * a m else 0 with hf
  have hfM : ∀ m ∉ Finset.range (M + 1), f m = 0 := by
    intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    have h0 : a m = 0 := haM m (by omega)
    simp only [hf]
    rw [h0]
    simp
  have hlow : ∀ m, m < j → f m = 0 := by
    intro m hm
    simp only [hf]
    split_ifs with h
    · exfalso
      have : M ≤ m + 2 := Nat.ceil_le.2 (by push_cast; exact h)
      omega
    · rfl
  have hsum3 : ∑ m ∈ Finset.range (M + 1), f m = f j + f (j + 1) + f (j + 2) := by
    rw [hj, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun m hm => hlow m (Finset.mem_range.1 hm))]
    ring
  have hfb : ∀ m, j ≤ m → m ≤ M → f m ≤ (M : ℝ) * a j := by
    intro m hjm hmM
    simp only [hf]
    split_ifs
    · exact mul_le_mul (by exact_mod_cast hmM) (hanti hjm) (ha0 m) (by positivity)
    · exact mul_nonneg (by positivity) (ha0 j)
  have hS3 : ∑' m, f m ≤ 3 * ((M : ℝ) * a j) := by
    rw [tsum_eq_sum hfM, hsum3]
    have h1 := hfb j le_rfl (by omega)
    have h2 := hfb (j + 1) (by omega) (by omega)
    have h3 := hfb (j + 2) (by omega) (by omega)
    linarith
  have hS0 : 0 ≤ ∑' m, f m := tsum_nonneg fun m => by
    simp only [hf]
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg m) (ha0 m)
    · exact le_rfl
  have hQsum : Expect.Q (trialState V w kc N) [u] = ∑ m ∈ Finset.range (M + 1), (m : ℝ) * a m := by
    rw [hQeq]
    exact tsum_eq_sum fun m hm => by
      simp only [Finset.mem_range, not_lt] at hm
      simp [haM m (by omega)]
  have hQlow : a j * (((j : ℝ) + 1) * j) / 2 ≤ Expect.Q (trialState V w kc N) [u] := by
    rw [hQsum]
    have h1 : ∑ m ∈ Finset.range (j + 1), (m : ℝ) * a m ≤
        ∑ m ∈ Finset.range (M + 1), (m : ℝ) * a m :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
        (fun m _ _ => mul_nonneg (Nat.cast_nonneg m) (ha0 m))
    have h2 : ∑ m ∈ Finset.range (j + 1), (m : ℝ) * a j ≤
        ∑ m ∈ Finset.range (j + 1), (m : ℝ) * a m :=
      Finset.sum_le_sum fun m hm =>
        mul_le_mul_of_nonneg_left (hanti (by simpa [Nat.lt_succ_iff] using hm)) (Nat.cast_nonneg m)
    rw [← Finset.sum_mul, Lemma55_sum_id] at h2
    push_cast at h2
    have e : a j * (((j : ℝ) + 1) * j) / 2 = ((j : ℝ) + 1) * ((j : ℝ) + 1 - 1) / 2 * a j := by
      ring
    rw [e]
    exact h2.trans h1
  have hMr : (M : ℝ) = (j : ℝ) + 2 := by rw [hj]; push_cast; ring
  have hj167 : (167 : ℝ) ≤ j := by
    have : (169 : ℝ) ≤ M := by exact_mod_cast hM169
    linarith
  have hMr2 : 1 ≤ (M : ℝ) * r ^ 2 := by
    have := mul_le_mul_of_nonneg_right hM1 (sq_nonneg r)
    rwa [inv_mul_cancel₀ (by positivity)] at this
  exact Lemma55_tail_alg hS0 hS3 hQlow hQ hX0 hMr hj167 hMr2 hr0 hr13 hCr'

/-- The loss `2(n + 1)(1 − θ) ≤ r` of (5.58) [lbpsiuPL0], with `1 − θ = (2n + 1)/N + 2Kρ^{1/2}`,
`1/N ≤ ρ = r^{400}`, `ρ^{1/2} = r^{200}`, `n r ≤ 2` and `(48 + 16K) r^{198} ≤ 1`. -/
private lemma Lemma55_loss {n r K Ni sh : ℝ} (hn1 : 1 ≤ n) (hnr : n * r ≤ 2) (hr0 : 0 < r)
    (hr5 : r ≤ 1 / 5) (hK0 : 0 ≤ K) (hrK : (48 + 16 * K) * r ^ 198 ≤ 1) (hNi0 : 0 ≤ Ni)
    (hNi : Ni ≤ r ^ 400) (hs0 : 0 ≤ sh) (hs : sh = r ^ 200) :
    2 * (n + 1) * ((2 * n + 1) * Ni + 2 * K * sh) ≤ r := by
  have e : 2 * (n + 1) * ((2 * n + 1) * Ni + 2 * K * sh) =
      2 * (n + 1) * (2 * n + 1) * Ni + 4 * K * ((n + 1) * sh) := by ring
  have h1 : 2 * (n + 1) * (2 * n + 1) * Ni ≤ 48 * r ^ 398 := by
    have h2 : 2 * (n + 1) * (2 * n + 1) ≤ 12 * n ^ 2 := by nlinarith
    calc 2 * (n + 1) * (2 * n + 1) * Ni ≤ 12 * n ^ 2 * Ni :=
          mul_le_mul_of_nonneg_right h2 hNi0
      _ ≤ 12 * n ^ 2 * r ^ 400 := mul_le_mul_of_nonneg_left hNi (by positivity)
      _ = 12 * (n * r) ^ 2 * r ^ 398 := by ring
      _ ≤ 12 * 2 ^ 2 * r ^ 398 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (by norm_num))
            (by positivity)
          exact pow_le_pow_left₀ (by positivity) hnr 2
      _ = 48 * r ^ 398 := by norm_num
  have h2 : (n + 1) * sh ≤ 4 * r ^ 199 := by
    calc (n + 1) * sh ≤ (2 * n) * sh := mul_le_mul_of_nonneg_right (by linarith) hs0
      _ = 2 * (n * r) * r ^ 199 := by rw [hs]; ring
      _ ≤ 2 * 2 * r ^ 199 := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnr (by norm_num))
            (by positivity)
      _ = 4 * r ^ 199 := by norm_num
  have h3 : r ^ 398 ≤ r ^ 199 := pow_le_pow_of_le_one hr0.le (by linarith) (by norm_num)
  have h4 : (48 + 16 * K) * r ^ 199 ≤ r := by
    have : (48 + 16 * K) * r ^ 199 = r * ((48 + 16 * K) * r ^ 198) := by ring
    rw [this]
    calc r * ((48 + 16 * K) * r ^ 198) ≤ r * 1 := mul_le_mul_of_nonneg_left hrK hr0.le
      _ = r := mul_one r
  have h5 : 4 * K * ((n + 1) * sh) ≤ 4 * K * (4 * r ^ 199) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [e]
  nlinarith

/-- The `j`-th term of the geometric sum of (5.58) [lbpsiuPL0]. -/
private lemma Lemma55_term_eq (N x θ b : ℝ) (j : ℕ) :
    N ^ 2 * x ^ (j + 1) * ((θ ^ 2) ^ (j + 2) * (1 - b)) =
      (x * θ ^ 2) ^ (j + 1) * (N * θ) ^ 2 * (1 - b) := by ring

/-- `|y|^{2n} = (y²)^n`, the tail factor of (5.58) [lbpsiuPL0]. -/
private lemma Lemma55_tail_exp (y : ℝ) (n : ℕ) : |y| ^ ((2 * n : ℕ) : ℝ) = (y ^ 2) ^ n := by
  rw [Real.rpow_natCast, pow_mul, sq_abs]

/-- The closing estimate of (5.58) [lbpsiuPL0]: from the geometric sum with loss
`q = (θ²)^{n+1}(1 − b)`, the losses `2(n + 1)(1 − θ) + b ≤ 3r` and `x^n ≤ T`. -/
private lemma Lemma55_close {x θ b r T Ssum N : ℝ} {n : ℕ} (hx0 : 0 < x) (hx1 : x < 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hr : 2 * ((n : ℝ) + 1) * (1 - θ) + b ≤ 3 * r) (hxT : x ^ n ≤ T)
    (hS : N ^ 2 * ((θ ^ 2) ^ (n + 1) * (1 - b)) * (x * (1 - x ^ n) / (1 - x)) ≤ Ssum) :
    N ^ 2 * (x / (1 - x)) * (1 - 3 * r - T) ≤ Ssum := by
  have hθ2 : 0 ≤ θ ^ 2 := sq_nonneg θ
  have hθ21 : θ ^ 2 ≤ 1 := pow_le_one₀ hθ0.le hθ1
  set t : ℝ := (θ ^ 2) ^ (n + 1) with ht
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := pow_le_one₀ hθ2 hθ21
  have hB := one_add_mul_le_pow (a := θ ^ 2 - 1) (by linarith [hθ2]) (n + 1)
  rw [show 1 + (θ ^ 2 - 1) = θ ^ 2 by ring] at hB
  have h5 : 1 - θ ^ 2 ≤ 2 * (1 - θ) :=
    calc 1 - θ ^ 2 = (1 - θ) * (1 + θ) := by ring
      _ ≤ (1 - θ) * 2 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = 2 * (1 - θ) := by ring
  have hn1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have h6 := mul_le_mul_of_nonneg_left h5 hn1
  have hts : 1 - 2 * ((n : ℝ) + 1) * (1 - θ) ≤ t := by
    push_cast at hB
    nlinarith
  set s : ℝ := 2 * ((n : ℝ) + 1) * (1 - θ) with hs
  have hs0 : 0 ≤ s := by
    have : 0 ≤ 1 - θ := by linarith
    positivity
  have hq : 1 - b - s ≤ t * (1 - b) := by
    have h1 := mul_le_mul_of_nonneg_right hts (by linarith : 0 ≤ 1 - b)
    nlinarith [mul_nonneg hs0 hb0]
  have hq1 : t * (1 - b) ≤ 1 := by nlinarith
  have hxn : 0 ≤ x ^ n := by positivity
  have hfin : 1 - 3 * r - T ≤ (t * (1 - b)) * (1 - x ^ n) := by
    have h1 : (t * (1 - b)) * x ^ n ≤ x ^ n := by
      have := mul_le_mul_of_nonneg_right hq1 hxn
      linarith
    nlinarith
  have hX0 : 0 ≤ x / (1 - x) := div_nonneg hx0.le (by linarith)
  calc N ^ 2 * (x / (1 - x)) * (1 - 3 * r - T)
      ≤ N ^ 2 * (x / (1 - x)) * ((t * (1 - b)) * (1 - x ^ n)) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = N ^ 2 * (t * (1 - b)) * (x * (1 - x ^ n) / (1 - x)) := by ring
    _ ≤ Ssum := hS

/-- (5.58) [lbpsiuPL0], with the weight `α(0)(α(0) − 1)` and the range `α(u) + 2 ≤ m_c`. -/
theorem Eq5_58 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      (N : ℝ) ^ 2 * ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2)) *
          (1 - C * rhoN N ^ (1/400 : ℝ) -
            |rhoN N * lam V w (rhoN N) (LN N) u| ^ (2 * Real.sqrt (mc (rhoN N)))) ≤
        ∑' α : Occ, (if (α u : ℝ) + 2 ≤ mc (rhoN N) then
          (α 0 : ℝ) * ((α 0 : ℝ) - 1) * (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) := by
  obtain ⟨C₃, hC₃, N₃, h32⟩ := Eq5_32 hg
  obtain ⟨N₄, hPE⟩ := Lemma55_PE hg
  set K : ℝ := (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) + C₃ with hK
  have hK0 : 0 ≤ K := by positivity
  have hev1 : ∀ᶠ N : ℕ in atTop, rhoN N ^ (1 / 400 : ℝ) ≤ 1 / 5 :=
    (Lemma55_rho_pow_tendsto (by norm_num)).eventually (ge_mem_nhds (by norm_num))
  have hev2 : ∀ᶠ N : ℕ in atTop, (48 + 16 * K) * rhoN N ^ (99 / 200 : ℝ) ≤ 1 := by
    have h := (Lemma55_rho_pow_tendsto (a := 99 / 200) (by norm_num)).const_mul (48 + 16 * K)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨3, by norm_num, max (max (max N₃ N₄) N₅) 1, fun N hN kc u hu => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₃ : N₃ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₄ : N₄ ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₅' : N₅ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hr5', hrK'⟩ := hN₅ N hN₅'
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  obtain ⟨hx0, hx1⟩ := Lemma55_x_bounds hg hN1 hu
  have hQ0 := Lemma55_Q0 hN1 hC₃ (h32 N hN₃ kc)
  rw [← hK] at hQ0
  have hPEN := hPE N hN₄ kc u hu
  have hTm := fun {m n : ℕ} {θ : ℝ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
      (hθ : θ = 1 - (2 * n + 1) / N - 2 * K * rhoN N ^ (1 / 2 : ℝ)) (hθ0 : 0 < θ)
      (hPhalf : 1 / 2 ≤ ∑' β : Occ, if alphaStar β u + m + 2 ≤ ⌊mc (rhoN N)⌋₊ then
        ‖trialState V w kc N β‖ ^ 2 else 0) =>
    Lemma55_Tm V w kc hN1 hu hK0 hQ0 hm1 hmn hθ hθ0 hPhalf
  have hsumge := Lemma55_sum_ge V w kc hN1 u
  have hmcN : ((⌊mc (rhoN N)⌋₊ : ℕ) : ℝ) ≤ mc (rhoN N) := Nat.floor_le (Real.rpow_nonneg hρ.le _)
  have hmcN' : mc (rhoN N) < ((⌊mc (rhoN N)⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hmcM : ((⌈mc (rhoN N)⌉₊ : ℕ) : ℝ) < mc (rhoN N) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hρ.le _)
  have hrlam := Particles_rho_lam_PL hg hρ hρ1 hu
  have hNinv : (N : ℝ)⁻¹ ≤ rhoN N := by
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    rw [rhoN, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  set ρ := rhoN N with hρdef
  set r : ℝ := ρ ^ (1 / 400 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ _
  have hr5 : r ≤ 1 / 5 := hr5'
  have hpow : ∀ (k : ℕ) (a : ℝ), a * 400 = k → r ^ k = ρ ^ a := fun k a ha =>
    Lemma55_pow hρ k a ha
  have hrK : (48 + 16 * K) * r ^ 198 ≤ 1 := by
    rw [hpow 198 (99 / 200) (by norm_num)]
    exact hrK'
  have hr400 : r ^ 400 = ρ := by rw [hpow 400 1 (by norm_num), Real.rpow_one]
  have hr200 : r ^ 200 = ρ ^ (1 / 2 : ℝ) := hpow 200 (1 / 2) (by norm_num)
  have hmc : mc ρ = (r ^ 2)⁻¹ := by
    rw [mc, Real.rpow_neg hρ.le, hpow 2 (1 / 200) (by norm_num)]
  have hsqrt : Real.sqrt (mc ρ) = r⁻¹ := by
    rw [hmc, Real.sqrt_inv, Real.sqrt_sq hr0.le]
  set M := ⌈mc ρ⌉₊ with hM
  set Kf := ⌊mc ρ⌋₊ with hKf
  set n := ⌈Real.sqrt (mc ρ)⌉₊ with hn
  have hn1 : r⁻¹ ≤ n := by rw [← hsqrt]; exact Nat.le_ceil _
  have hn2 : (n : ℝ) < r⁻¹ + 1 := by
    rw [← hsqrt]; exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  have hM1 : (r ^ 2)⁻¹ ≤ M := by rw [← hmc]; exact Nat.le_ceil _
  have hrinv : r * r⁻¹ = 1 := mul_inv_cancel₀ hr0.ne'
  have hr5inv : 5 ≤ r⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hr0]
    linarith
  have hnr : (n : ℝ) * r ≤ 2 := by
    have h1 : (n : ℝ) * r ≤ (r⁻¹ + 1) * r := mul_le_mul_of_nonneg_right hn2.le hr0.le
    have e : (r⁻¹ + 1) * r = 1 + r := by rw [add_mul, inv_mul_cancel₀ hr0.ne', one_mul]
    linarith
  have hnr1 : 1 ≤ (n : ℝ) * r := by
    have := mul_le_mul_of_nonneg_right hn1 hr0.le
    rw [inv_mul_cancel₀ hr0.ne'] at this
    exact this
  have hn1' : 1 ≤ n := by
    have : (1 : ℝ) ≤ n := le_trans (by linarith) hn1
    exact_mod_cast this
  -- `M ≤ ⌊m_c⌋ + 1`
  have hMKf : M ≤ Kf + 1 := by
    have : (M : ℝ) < (Kf : ℝ) + 2 := by linarith
    have : M < Kf + 2 := by exact_mod_cast this
    omega
  -- the loss `b = (n + 4)/(⌈m_c⌉ + 1) ≤ r + 5r²`
  set b : ℝ := ((n : ℝ) + 4) / ((M : ℝ) + 1) with hb
  have hb0 : 0 ≤ b := by positivity
  have hbr : b ≤ r + 5 * r ^ 2 := by
    rw [hb, div_le_iff₀ (by positivity)]
    have h1 : (r + 5 * r ^ 2) * (r ^ 2)⁻¹ = r⁻¹ + 5 := by
      field_simp
    have h2 : (r + 5 * r ^ 2) * (r ^ 2)⁻¹ ≤ (r + 5 * r ^ 2) * ((M : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hr2 : r ^ 2 ≤ 1 / 5 * r := by
    rw [sq]
    calc r * r ≤ r * (1 / 5) := mul_le_mul_of_nonneg_left hr5 hr0.le
      _ = 1 / 5 * r := by ring
  have hb1 : b ≤ 2 * r := by linarith
  have hb1' : b < 1 := by linarith
  have hnM : n + 4 ≤ M := by
    rw [hb, div_lt_one (by positivity)] at hb1'
    have : ((n + 4 : ℕ) : ℝ) < ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega
  -- `θ = 1 − (2n + 1)/N − 2Kρ^{1/2}` and the loss `2(n + 1)(1 − θ) ≤ r`
  set θ : ℝ := 1 - (2 * n + 1) / N - 2 * K * ρ ^ (1 / 2 : ℝ) with hθ
  have hθ1 : θ ≤ 1 := by
    have : 0 ≤ (2 * (n : ℝ) + 1) / N := by positivity
    have : 0 ≤ 2 * K * ρ ^ (1 / 2 : ℝ) := by positivity
    linarith
  have hloss : 2 * ((n : ℝ) + 1) * (1 - θ) ≤ r := by
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
    have e : 1 - θ = (2 * (n : ℝ) + 1) * (N : ℝ)⁻¹ + 2 * K * ρ ^ (1 / 2 : ℝ) := by
      rw [hθ]
      field_simp
      ring
    rw [e]
    exact Lemma55_loss hn1r hnr hr0 hr5 hK0 hrK (by positivity) (by rw [hr400]; exact hNinv)
      (Real.rpow_nonneg hρ.le _) hr200.symm
  have hθ0 : 0 < θ := by
    by_contra h
    have h1 : 1 ≤ 1 - θ := by linarith [not_lt.1 h]
    have h2 : 2 * ((n : ℝ) + 1) * 1 ≤ 2 * ((n : ℝ) + 1) * (1 - θ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
    linarith
  -- the bound on `Σ_{α(u) ≥ m, α(u) + 2 ≤ m_c} α(0)(α(0) − 1)|Ψ|²` for `1 ≤ m ≤ n`
  set x : ℝ := (ρ * lam V w ρ (LN N) u) ^ 2 with hx
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψ
  have hPb : ∀ m : ℕ, 1 ≤ m → m ≤ n → 1 - b ≤
      ∑' β : Occ, if alphaStar β u + m + 2 ≤ Kf then ψ β else 0 := by
    intro m hm1 hmn
    have h3 : m + 3 ≤ Kf := by omega
    have hP := hPEN m h3
    refine le_trans ?_ hP
    have e : 1 - b = ((M : ℝ) - n - 3) / ((M : ℝ) + 1) := by
      rw [hb]
      field_simp
      ring
    rw [e]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have h4 : (M : ℝ) ≤ (Kf : ℝ) + 1 := by exact_mod_cast hMKf
    have h5 : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hT : ∀ m : ℕ, 1 ≤ m → m ≤ n → (x * θ ^ 2) ^ m * ((N : ℝ) * θ) ^ 2 * (1 - b) ≤
      ∑' α : Occ, if m ≤ α u ∧ α u + 2 ≤ Kf then
        (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
    intro m hm1 hmn
    have hPn := hPb m hm1 hmn
    have hPhalf : 1 / 2 ≤ ∑' β : Occ, if alphaStar β u + m + 2 ≤ Kf then ψ β else 0 := by
      linarith
    exact (mul_le_mul_of_nonneg_left hPn (by positivity)).trans
      (hTm hm1 hmn hθ hθ0 hPhalf)
  -- summing over `m = 1, …, n`
  have hgeom : ∑ j ∈ Finset.range n, x ^ (j + 1) = x * (1 - x ^ n) / (1 - x) := by
    have h1 : ∑ j ∈ Finset.range n, x ^ (j + 1) = x * ∑ j ∈ Finset.range n, x ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1, geom_sum_eq hx1.ne]
    have : x - 1 ≠ 0 := by linarith
    have : 1 - x ≠ 0 := by linarith
    field_simp
    ring
  have hθ2 : 0 ≤ θ ^ 2 := sq_nonneg θ
  have hθ21 : θ ^ 2 ≤ 1 := pow_le_one₀ hθ0.le hθ1
  set q : ℝ := (θ ^ 2) ^ (n + 1) * (1 - b) with hq
  have hb1'' : 0 ≤ 1 - b := by linarith
  have hterm : ∀ j ∈ Finset.range n, (N : ℝ) ^ 2 * q * x ^ (j + 1) ≤
      ∑' α : Occ, if j + 1 ≤ α u ∧ α u + 2 ≤ Kf then
        (α 0 : ℝ) * ((α 0 : ℝ) - 1) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
    intro j hj
    have hj' : j + 1 ≤ n := Finset.mem_range.1 hj
    have h1 := hT (j + 1) (by omega) hj'
    have h2 : (θ ^ 2) ^ (n + 1) ≤ (θ ^ 2) ^ (j + 2) := pow_le_pow_of_le_one hθ2 hθ21 (by omega)
    calc (N : ℝ) ^ 2 * q * x ^ (j + 1)
        = (N : ℝ) ^ 2 * x ^ (j + 1) * ((θ ^ 2) ^ (n + 1) * (1 - b)) := by rw [hq]; ring
      _ ≤ (N : ℝ) ^ 2 * x ^ (j + 1) * ((θ ^ 2) ^ (j + 2) * (1 - b)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hb1'') (by positivity)
      _ = (x * θ ^ 2) ^ (j + 1) * ((N : ℝ) * θ) ^ 2 * (1 - b) := Lemma55_term_eq _ _ _ _ _
      _ ≤ _ := h1
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, hgeom] at hsum
  -- the tail factor `x^n ≤ |ρλ_u|^{2√m_c}`
  have hy0 : 0 < |ρ * lam V w ρ (LN N) u| := abs_pos.2 hrlam.1.ne
  have hy1 : |ρ * lam V w ρ (LN N) u| ≤ 1 := (sq_le_one_iff_abs_le_one _).1 hx1.le
  have hxT : x ^ n ≤ |ρ * lam V w ρ (LN N) u| ^ (2 * Real.sqrt (mc ρ)) := by
    rw [← Lemma55_tail_exp]
    refine Real.rpow_le_rpow_of_exponent_ge hy0 hy1 ?_
    push_cast
    rw [hsqrt]
    linarith
  have hsumge' := hsumge n
  exact Lemma55_close hx0 hx1 hθ0 hθ1 hb0 hb1'.le (by linarith) hxT (hsum.trans hsumge')

/-! ### Particle numbers in `P_I ∪ P_H` and the support bound for `Σ_{u,v ≠ 0} Q_Ψ(u, v)` -/

/-- For all large `N`: `N ≥ 1` and `2π ≤ L_N ρ_N^{1/2}`. -/
private lemma Lemma55_eventually :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ 2 * π ≤ LN N * rhoN N ^ (1 / 2 : ℝ) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hP : ∀ {a : ℝ}, 0 < a → Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
    intro a ha
    have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at h
    exact h.comp hT
  have h2 : ∀ᶠ N : ℕ in atTop, 2 * π * rhoN N ^ (13 / 24 : ℝ) ≤ 1 := by
    have h := (hP (by norm_num : (0 : ℝ) < 13 / 24)).const_mul (2 * π)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop 1, h2] with N hN hΔ
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  refine ⟨hN, ?_⟩
  have hq : 0 < rhoN N ^ (13 / 24 : ℝ) := Real.rpow_pos_of_pos hρ _
  have e : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) = 1 := by
    rw [LN, mul_assoc, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  by_contra h
  have h' : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) <
      2 * π * rhoN N ^ (13 / 24 : ℝ) := mul_lt_mul_of_pos_right (not_le.1 h) hq
  linarith

/-- The lattice points with `‖p_n‖ ≤ R` form a finite set. -/
private lemma Lemma55_finite_ball {L R : ℝ} (hL : 0 < L) : {n : Idx | ‖mom L n‖ ≤ R}.Finite := by
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

/-- `#{n ≠ 0 : ‖p_n‖ ≤ R} ≤ K L³ R³` for `2π ≤ L R`: `Σ_{0 < |u| ≤ R} |u|⁰` of the lattice sum
estimate. -/
private lemma Lemma55_card : ∃ K : ℝ, 0 ≤ K ∧ ∀ L R : ℝ, 0 < R → 2 * π ≤ L * R →
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
    (Lemma55_finite_ball (R := R) hL).subset fun n hn => hn.2
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

/-- `Q_Ψ(n) ≥ 0`. -/
private lemma Lemma55_Q_nonneg (Ψ : Occ → ℂ) (n : Idx) : 0 ≤ Expect.Q Ψ [n] := by
  unfold Expect.Q
  refine tsum_nonneg fun α => ?_
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  positivity

/-- For `n ≠ 0` outside `P_L ∪ P_I ∪ P_H`, `Q_Ψ(n) = 0` (Definition 3.4 [M], supports in `P`). -/
private lemma Lemma55_Q_eq_zero (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {n : Idx} (hn0 : n ≠ 0)
    (hL : ¬ inPL (rhoN N) (LN N) n) (hI : ¬ inPI (rhoN N) (LN N) n)
    (hH : ¬ inPH (rhoN N) (LN N) n) : Expect.Q (trialState V w kc N) [n] = 0 := by
  unfold Expect.Q
  refine (tsum_congr fun α => ?_).trans tsum_zero
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  by_cases hz : ‖trialState V w kc N α‖ ^ 2 = 0
  · rw [hz, mul_zero]
  · have hα := Lemma55_inM hz
    have : α n = 0 := by
      by_contra h
      rcases MBasic_support hα n h with h0 | h0 | h0 | h0
      · exact hn0 h0
      · exact hL h0
      · exact hI h0
      · exact hH h0
    rw [this]
    simp

/-- `N − Q_Ψ(0) = Σ_{P_I} Q_Ψ + Σ_{P_H} Q_Ψ + Σ_{P_L} Q_Ψ`, by `Σ_n Q_Ψ(n) = N`. -/
private lemma Lemma55_split (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) - Expect.Q (trialState V w kc N) [0] =
      (∑' n : Idx, (if inPI (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) +
      (∑' n : Idx, (if inPH (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) +
      (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
          Expect.Q (trialState V w kc N) [n] else 0)) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  set Q : Idx → ℝ := fun n => Expect.Q (trialState V w kc N) [n] with hQ
  have hs : HasSum Q N := Particles_hasSum_Q V w kc hN
  have hQs : Summable Q := hs.summable
  have hQnn : ∀ n, 0 ≤ Q n := fun n => Lemma55_Q_nonneg _ n
  have hsub := hs.sub (hasSum_ite_eq (0 : Idx) (Q 0))
  have hsum : ∀ P : Idx → Prop, Summable fun n => if P n then Q n else 0 := fun P =>
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> simp [hQnn n])
      (fun n => by split_ifs <;> simp [hQnn n]) hQs
  have hfun : (fun n : Idx => Q n - if n = 0 then Q 0 else 0) =
      fun n => ((if inPI (rhoN N) (LN N) n then Q n else 0) +
        (if inPH (rhoN N) (LN N) n then Q n else 0)) +
        (if inPL (rhoN N) (LN N) n then Q n else 0) := by
    funext n
    by_cases hn : n = 0
    · subst hn
      have h1 : ¬ inPI (rhoN N) (LN N) 0 := fun h => Regions_PI_ne_zero hρ h rfl
      have h2 : ¬ inPH (rhoN N) (LN N) 0 := fun h => Regions_PH_ne_zero hρ h rfl
      have h3 : ¬ inPL (rhoN N) (LN N) 0 := fun h => Regions_PL_ne_zero hρ h rfl
      simp [h1, h2, h3]
    · by_cases hI : inPI (rhoN N) (LN N) n
      · have h2 : ¬ inPH (rhoN N) (LN N) n := Regions_PI_PH hI
        have h3 : ¬ inPL (rhoN N) (LN N) n := fun h => Regions_PL_PI h hI
        simp [hn, hI, h2, h3]
      · by_cases hH : inPH (rhoN N) (LN N) n
        · have h3 : ¬ inPL (rhoN N) (LN N) n := fun h => Regions_PL_PH hρ h hH
          simp [hn, hI, hH, h3]
        · by_cases hL : inPL (rhoN N) (LN N) n
          · simp [hn, hI, hH, hL]
          · have := Lemma55_Q_eq_zero V w kc N hn hL hI hH
            simp [hn, hI, hH, hL, hQ, this]
  rw [hfun] at hsub
  have hall := ((hsum (inPI (rhoN N) (LN N))).hasSum.add (hsum (inPH (rhoN N) (LN N))).hasSum).add
    (hsum (inPL (rhoN N) (LN N))).hasSum
  exact hsub.unique hall

/-- A finite sum of occupation numbers is at most the particle number. -/
private lemma Lemma55_finset_sum_le (α : Occ) (T : Finset Idx) : ∑ n ∈ T, α n ≤ α.num := by
  calc ∑ n ∈ T, α n = ∑ n ∈ T.filter (fun n => α n ≠ 0), α n :=
        (Finset.sum_filter_ne_zero (f := fun n => α n) T).symm
    _ ≤ ∑ n ∈ α.support, α n := Finset.sum_le_sum_of_subset (fun n hn => by
        simp only [Finset.mem_filter] at hn
        exact Finsupp.mem_support_iff.2 hn.2)
    _ = α.num := rfl

/-- A weight bounded on the support of `ψ` against `ψ` is summable. -/
private lemma Lemma55_summable_w {ψ G : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α) (B : ℝ)
    (hGB : ∀ α, ψ α ≠ 0 → |G α| ≤ B) : Summable fun α => G α * ψ α := by
  refine Summable.of_norm_bounded (hs.mul_left B) (fun α => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hψ α)]
  by_cases hz : ψ α = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hGB α hz) (hψ α)

/-- The support bound behind (5.62) [temp6.56] and (5.64) [temp6.58]: if `F` is the finite set of
the points of `P_L`, then `Σ_α (N − α(0))² |Ψ(α)|² ≤ ⌈m_c⌉ #F (N − Q_Ψ(0)) +
N (Σ_{P_I} Q_Ψ + Σ_{P_H} Q_Ψ)`, from `(N − α(0))² ≤ ⌈m_c⌉ #F (N − α(0)) +
N Σ_{n ∈ P_I ∪ P_H} α(n)`. -/
private lemma Lemma55_support (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (F : Finset Idx)
    (hF : ∀ n : Idx, inPL (rhoN N) (LN N) n ↔ n ∈ F) :
    (∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖trialState V w kc N α‖ ^ 2) ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) * F.card * ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) +
        N * ((∑' n : Idx, (if inPI (rhoN N) (LN N) n then
            Expect.Q (trialState V w kc N) [n] else 0)) +
          (∑' n : Idx, (if inPH (rhoN N) (LN N) n then
            Expect.Q (trialState V w kc N) [n] else 0))) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψ
  have hψs : Summable ψ := hΨ.1.summable
  have hψ0 : ∀ α, 0 ≤ ψ α := fun _ => by positivity
  have hψ1 : ∑' α, ψ α = 1 := hΨ.1.tsum_eq
  set M := ⌈mc (rhoN N)⌉₊ with hM
  set SL : Occ → ℝ := fun α => ∑ n ∈ F, (α n : ℝ) with hSL
  have h0F : (0 : Idx) ∉ F := fun h => Regions_PL_ne_zero hρ ((hF 0).2 h) rfl
  -- pointwise facts on the support of `ψ`
  have hpt : ∀ α, ψ α ≠ 0 → 0 ≤ SL α ∧ SL α ≤ (N : ℝ) - α 0 ∧ (α 0 : ℝ) ≤ N ∧
      SL α ≤ F.card * M := by
    intro α hz
    have hα := Lemma55_inM hz
    have hnum : α.num = N := MBasic_num hρ hα
    have h1 := Lemma55_finset_sum_le α (insert 0 F)
    rw [Finset.sum_insert h0F, hnum] at h1
    have h1' : (α 0 : ℝ) + SL α ≤ N := by
      have : ((α 0 + ∑ n ∈ F, α n : ℕ) : ℝ) ≤ N := by exact_mod_cast h1
      simpa [hSL] using this
    have hSLM : SL α ≤ F.card * M := by
      have := Finset.sum_le_card_nsmul F (fun n => (α n : ℝ)) (M : ℝ) (fun n hn => by
        have h2 : α n ≤ alphaStar α n := le_max_left _ _
        have h3 := MStar_PL_ceil hρ hα ((hF n).2 hn)
        exact_mod_cast h2.trans h3)
      simpa [hSL, nsmul_eq_mul] using this
    refine ⟨Finset.sum_nonneg fun n _ => Nat.cast_nonneg _, by linarith, ?_, hSLM⟩
    have : (0 : ℝ) ≤ SL α := Finset.sum_nonneg fun n _ => Nat.cast_nonneg _
    linarith
  -- the pointwise inequality
  have hineq : ∀ α, ((N : ℝ) - α 0) ^ 2 * ψ α ≤
      (M * F.card) * (((N : ℝ) - α 0) * ψ α) + N * (((N : ℝ) - α 0 - SL α) * ψ α) := by
    intro α
    by_cases hz : ψ α = 0
    · simp [hz]
    · obtain ⟨hS0, hS1, hα0, hS2⟩ := hpt α hz
      have hA0 : 0 ≤ (N : ℝ) - α 0 := le_trans hS0 hS1
      have hA1 : (N : ℝ) - α 0 ≤ N := by
        have : (0 : ℝ) ≤ α 0 := Nat.cast_nonneg _
        linarith
      have h1 : ((N : ℝ) - α 0) ^ 2 ≤
          (M * F.card) * ((N : ℝ) - α 0) + N * ((N : ℝ) - α 0 - SL α) := by
        have h2 : ((N : ℝ) - α 0) * SL α ≤ ((N : ℝ) - α 0) * (F.card * M) :=
          mul_le_mul_of_nonneg_left hS2 hA0
        have h3 : ((N : ℝ) - α 0) * ((N : ℝ) - α 0 - SL α) ≤ N * ((N : ℝ) - α 0 - SL α) :=
          mul_le_mul_of_nonneg_right hA1 (by linarith)
        nlinarith
      have := mul_le_mul_of_nonneg_right h1 (hψ0 α)
      linarith
  -- summability
  have hsA2 : Summable fun α => ((N : ℝ) - α 0) ^ 2 * ψ α :=
    Lemma55_summable_w hψs hψ0 ((N : ℝ) ^ 2) (fun α hz => by
      obtain ⟨hS0, hS1, hα0, -⟩ := hpt α hz
      have hA0 : 0 ≤ (N : ℝ) - α 0 := le_trans hS0 hS1
      have hA1 : (N : ℝ) - α 0 ≤ N := by
        have : (0 : ℝ) ≤ α 0 := Nat.cast_nonneg _
        linarith
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ hA0 hA1 2)
  have hsA : Summable fun α => ((N : ℝ) - α 0) * ψ α :=
    Lemma55_summable_w hψs hψ0 (N : ℝ) (fun α hz => by
      obtain ⟨hS0, hS1, hα0, -⟩ := hpt α hz
      have hA0 : 0 ≤ (N : ℝ) - α 0 := le_trans hS0 hS1
      have : (0 : ℝ) ≤ α 0 := Nat.cast_nonneg _
      rw [abs_of_nonneg hA0]
      linarith)
  have hsAS : Summable fun α => ((N : ℝ) - α 0 - SL α) * ψ α :=
    Lemma55_summable_w hψs hψ0 (N : ℝ) (fun α hz => by
      obtain ⟨hS0, hS1, hα0, -⟩ := hpt α hz
      have : (0 : ℝ) ≤ α 0 := Nat.cast_nonneg _
      rw [abs_of_nonneg (by linarith)]
      linarith)
  have hsocc : ∀ n : Idx, Summable fun α : Occ => (α n : ℝ) * ψ α := fun n =>
    Lemma55_summable_w hψs hψ0 (N : ℝ) (fun α hz => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact Lemma55_occ_le_N hN hz n)
  have hQn : ∀ n : Idx, Expect.Q (trialState V w kc N) [n] = ∑' α : Occ, (α n : ℝ) * ψ α := by
    intro n
    simp [Expect.Q, hψ]
  -- the sums
  have hsumA : (∑' α : Occ, ((N : ℝ) - α 0) * ψ α) =
      (N : ℝ) - Expect.Q (trialState V w kc N) [0] := by
    rw [hQn 0]
    have : (fun α : Occ => ((N : ℝ) - α 0) * ψ α) = fun α => (N : ℝ) * ψ α - (α 0 : ℝ) * ψ α := by
      funext α
      ring
    rw [this, (hψs.mul_left (N : ℝ)).tsum_sub (hsocc 0), tsum_mul_left, hψ1, mul_one]
  have hsumSL : (∑' α : Occ, SL α * ψ α) =
      ∑ n ∈ F, Expect.Q (trialState V w kc N) [n] := by
    have : (fun α : Occ => SL α * ψ α) = fun α => ∑ n ∈ F, (α n : ℝ) * ψ α := by
      funext α
      simp only [hSL, Finset.sum_mul]
    rw [this, Summable.tsum_finsetSum (fun n _ => hsocc n)]
    exact Finset.sum_congr rfl fun n _ => (hQn n).symm
  have hsSL : Summable fun α : Occ => SL α * ψ α := by
    have : (fun α : Occ => SL α * ψ α) = fun α => ∑ n ∈ F, (α n : ℝ) * ψ α := by
      funext α
      simp only [hSL, Finset.sum_mul]
    rw [this]
    exact summable_sum fun n _ => hsocc n
  have hsumAS : (∑' α : Occ, ((N : ℝ) - α 0 - SL α) * ψ α) =
      (N : ℝ) - Expect.Q (trialState V w kc N) [0] -
        ∑ n ∈ F, Expect.Q (trialState V w kc N) [n] := by
    have : (fun α : Occ => ((N : ℝ) - α 0 - SL α) * ψ α) =
        fun α => ((N : ℝ) - α 0) * ψ α - SL α * ψ α := by
      funext α
      ring
    rw [this, hsA.tsum_sub hsSL, hsumA, hsumSL]
  -- `Σ_{P_L} Q_Ψ = Σ_{n ∈ F} Q_Ψ(n)` and the split
  have hPL : (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
      Expect.Q (trialState V w kc N) [n] else 0)) =
        ∑ n ∈ F, Expect.Q (trialState V w kc N) [n] := by
    rw [tsum_eq_sum (s := F)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      simp [(hF n).2 hn]
    · intro n hn
      have : ¬ inPL (rhoN N) (LN N) n := fun h => hn ((hF n).1 h)
      simp [this]
  have hsplit := Lemma55_split V w kc hN
  rw [hPL] at hsplit
  calc (∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖trialState V w kc N α‖ ^ 2)
      ≤ ∑' α : Occ, ((M * F.card) * (((N : ℝ) - α 0) * ψ α) +
          N * (((N : ℝ) - α 0 - SL α) * ψ α)) :=
        hsA2.tsum_le_tsum hineq ((hsA.mul_left _).add (hsAS.mul_left _))
    _ = (M * F.card) * ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) +
          N * ((N : ℝ) - Expect.Q (trialState V w kc N) [0] -
            ∑ n ∈ F, Expect.Q (trialState V w kc N) [n]) := by
        rw [(hsA.mul_left _).tsum_add (hsAS.mul_left _), tsum_mul_left, tsum_mul_left, hsumA,
          hsumAS]
    _ = _ := by
        rw [hsplit]
        ring

/-- The closing estimate of (5.64) [temp6.58]: all quantities are powers of `r = ρ^{1/400}`. -/
private lemma Lemma55_close61 {Ks K C₁ C₂ L3 R3 r card Mr NQ SI SH X : ℝ} (hr0 : 0 < r)
    (hr1 : r ≤ 1) (hL3 : 0 < L3) (hKs : 0 ≤ Ks) (hK : 0 ≤ K) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hcard0 : 0 ≤ card) (hcard : card ≤ Ks * (L3 * R3)) (hR3 : R3 = r ^ 594) (hM0 : 0 ≤ Mr)
    (hM : Mr ≤ 2 * (r ^ 2)⁻¹) (hNQ0 : 0 ≤ NQ) (hNQ : NQ ≤ K * (r ^ 400 * L3) * r ^ 200)
    (hSI0 : 0 ≤ SI) (hSI : SI ≤ L3 * (C₁ * r ^ 602)) (hSH0 : 0 ≤ SH)
    (hSH : SH ≤ L3 * (C₂ * r ^ 798))
    (hX : X ≤ Mr * card * NQ + r ^ 400 * L3 * (SI + SH)) :
    (r ^ 1000)⁻¹ * (L3 ^ 2)⁻¹ * X ≤ (2 * Ks * K + C₁ + C₂) * r ^ 2 := by
  rw [hR3] at hcard
  have h1 : Mr * card * NQ ≤ (2 * (r ^ 2)⁻¹) * (Ks * (L3 * r ^ 594)) *
      (K * (r ^ 400 * L3) * r ^ 200) :=
    mul_le_mul (mul_le_mul hM hcard hcard0 (by positivity)) hNQ hNQ0 (by positivity)
  have h2 : (2 * (r ^ 2)⁻¹) * (Ks * (L3 * r ^ 594)) * (K * (r ^ 400 * L3) * r ^ 200) =
      2 * Ks * K * L3 ^ 2 * r ^ 1192 := by
    field_simp
  have h3 : r ^ 400 * L3 * (SI + SH) ≤ r ^ 400 * L3 * (L3 * (C₁ * r ^ 602) + L3 * (C₂ * r ^ 798)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have h4 : r ^ 400 * L3 * (L3 * (C₁ * r ^ 602) + L3 * (C₂ * r ^ 798)) =
      L3 ^ 2 * (C₁ * r ^ 1002 + C₂ * r ^ 1198) := by ring
  have h5 : r ^ 1192 ≤ r ^ 1002 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
  have h6 : r ^ 1198 ≤ r ^ 1002 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
  have hXb : X ≤ L3 ^ 2 * r ^ 1002 * (2 * Ks * K + C₁ + C₂) := by
    have h7 : 2 * Ks * K * L3 ^ 2 * r ^ 1192 ≤ 2 * Ks * K * L3 ^ 2 * r ^ 1002 :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    have h8 : C₁ * r ^ 1002 + C₂ * r ^ 1198 ≤ C₁ * r ^ 1002 + C₂ * r ^ 1002 := by
      have := mul_le_mul_of_nonneg_left h6 hC₂
      linarith
    have h9 := mul_le_mul_of_nonneg_left h8 (sq_nonneg L3)
    nlinarith
  calc (r ^ 1000)⁻¹ * (L3 ^ 2)⁻¹ * X
      ≤ (r ^ 1000)⁻¹ * (L3 ^ 2)⁻¹ * (L3 ^ 2 * r ^ 1002 * (2 * Ks * K + C₁ + C₂)) :=
        mul_le_mul_of_nonneg_left hXb (by positivity)
    _ = (2 * Ks * K + C₁ + C₂) * r ^ 2 := by field_simp

/-- (5.64) [temp6.58] and (5.65) [temp6.59]: the bound (6.1) [boundspsiuvtotal] with a rate. -/
theorem Eq6_1 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ *
          (∑' u : Idx, ∑' v : Idx,
            (if u ≠ 0 ∧ v ≠ 0 then Expect.Q (trialState V w kc N) [u, v] else 0)) ≤
        C * rhoN N ^ (1/200 : ℝ) := by
  obtain ⟨Ks, hKs, hcard⟩ := Lemma55_card
  obtain ⟨C₃, hC₃, N₃, h32⟩ := Eq5_32 hg
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Prop5_4_PI V w
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := Prop5_4_PH V w
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.1 Lemma55_eventually
  set K : ℝ := (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) + C₃ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * Ks * K + C₁ + C₂, by positivity, max (max (max (max N₁ N₂) N₃) N₅) 1,
    fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₁ : N₁ ≤ N :=
    le_trans (le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) hN
  have hN₂ : N₂ ≤ N :=
    le_trans (le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _))
      (le_max_left _ _)) hN
  have hN₃ : N₃ ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₅' : N₅ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨-, hL2π⟩ := hN₅ N hN₅'
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  have hQ0 := Lemma55_Q0 hN1 hC₃ (h32 N hN₃ kc)
  rw [← hK] at hQ0
  have hSI := h₁ N hN₁ kc
  have hSH := h₂ N hN₂ kc
  have hQ0N : Expect.Q (trialState V w kc N) [0] ≤ N := Expect.Q_single_le N _ hΨ 0
  have hQnn := fun n : Idx => Lemma55_Q_nonneg (trialState V w kc N) n
  have hsplit := Lemma55_split V w kc hN1
  have hmcge : 1 ≤ mc (rhoN N) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  have hmcM : ((⌈mc (rhoN N)⌉₊ : ℕ) : ℝ) < mc (rhoN N) + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg hρ.le _)
  have hε0 : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP (rhoN N) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hsqrtρ : 0 < rhoN N ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  -- the radius `R = ε⁻¹ ρ^{1/2}` of `P_L`
  have hR0 : 0 < (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ) := by positivity
  have h2πR : 2 * π ≤ LN N * ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) := by
    refine hL2π.trans ?_
    have h1 : 1 ≤ (epsP (rhoN N))⁻¹ := (one_le_inv₀ hε0).2 hε1
    calc LN N * rhoN N ^ (1 / 2 : ℝ) = LN N * (1 * rhoN N ^ (1 / 2 : ℝ)) := by rw [one_mul]
      _ ≤ LN N * ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hsqrtρ.le) hL.le
  obtain ⟨F', hF'1, hF'2⟩ := hcard (LN N) _ hR0 h2πR
  classical
  set F : Finset Idx := F'.filter (fun n => inPL (rhoN N) (LN N) n) with hFdef
  have hF : ∀ n : Idx, inPL (rhoN N) (LN N) n ↔ n ∈ F := by
    intro n
    constructor
    · intro hn
      exact Finset.mem_filter.2 ⟨hF'1 n (Regions_PL_ne_zero hρ hn) hn.2, hn⟩
    · intro hn
      exact (Finset.mem_filter.1 hn).2
  have hFcard : (F.card : ℝ) ≤ Ks * (LN N ^ 3 *
      ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) ^ 3) :=
    (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans hF'2
  have hsupp := Lemma55_support V w kc hN1 F hF
  rw [(Particles_Q00_eq V w kc hN1).1]
  set ρ := rhoN N with hρdef
  set r : ℝ := ρ ^ (1 / 400 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ _
  have hr1 : r ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hpow : ∀ (k : ℕ) (a : ℝ), a * 400 = k → r ^ k = ρ ^ a := fun k a ha =>
    Lemma55_pow hρ k a ha
  have hr400 : r ^ 400 = ρ := by rw [hpow 400 1 (by norm_num), Real.rpow_one]
  have hr200 : r ^ 200 = ρ ^ (1 / 2 : ℝ) := hpow 200 (1 / 2) (by norm_num)
  have hε : epsP ρ = r ^ 2 := (hpow 2 (1 / 200) (by norm_num)).symm
  have hmc : mc ρ = (r ^ 2)⁻¹ := by
    rw [mc, Real.rpow_neg hρ.le, hpow 2 (1 / 200) (by norm_num)]
  have hR3 : ((epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ)) ^ 3 = r ^ 594 := by
    rw [hε, ← hr200]
    field_simp
  have hL3 : 0 < LN N ^ 3 := by positivity
  have hNr : (N : ℝ) = r ^ 400 * LN N ^ 3 := by rw [hr400]; exact hNL.symm
  have hSI' : (∑' n : Idx, (if inPI ρ (LN N) n then Expect.Q (trialState V w kc N) [n] else 0)) ≤
      LN N ^ 3 * (C₁ * r ^ 602) := by
    rw [hpow 602 (3 / 2 + 1 / 200) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hSI hL3.le
    rwa [mul_inv_cancel_left₀ hL3.ne'] at this
  have hSH' : (∑' n : Idx, (if inPH ρ (LN N) n then Expect.Q (trialState V w kc N) [n] else 0)) ≤
      LN N ^ 3 * (C₂ * r ^ 798) := by
    rw [hpow 798 (2 - 1 / 200) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hSH hL3.le
    rwa [mul_inv_cancel_left₀ hL3.ne'] at this
  have hSI0 : 0 ≤ ∑' n : Idx, (if inPI ρ (LN N) n then Expect.Q (trialState V w kc N) [n] else 0) :=
    tsum_nonneg fun n => by split_ifs <;> simp [hQnn n]
  have hSH0 : 0 ≤ ∑' n : Idx, (if inPH ρ (LN N) n then Expect.Q (trialState V w kc N) [n] else 0) :=
    tsum_nonneg fun n => by split_ifs <;> simp [hQnn n]
  have hNQ0 : 0 ≤ (N : ℝ) - Expect.Q (trialState V w kc N) [0] := by linarith
  have hNQ : (N : ℝ) - Expect.Q (trialState V w kc N) [0] ≤ K * (r ^ 400 * LN N ^ 3) * r ^ 200 := by
    rw [← hNr, hr200]
    exact hQ0
  have hM : ((⌈mc ρ⌉₊ : ℕ) : ℝ) ≤ 2 * (r ^ 2)⁻¹ := by
    calc ((⌈mc ρ⌉₊ : ℕ) : ℝ) ≤ mc ρ + 1 := hmcM.le
      _ ≤ mc ρ + mc ρ := by linarith
      _ = 2 * (r ^ 2)⁻¹ := by rw [hmc]; ring
  have hrpow5 : ρ ^ (-(5 / 2 : ℝ)) = (r ^ 1000)⁻¹ := by
    rw [Real.rpow_neg hρ.le, hpow 1000 (5 / 2) (by norm_num)]
  have hr200' : ρ ^ (1 / 200 : ℝ) = r ^ 2 := (hpow 2 (1 / 200) (by norm_num)).symm
  rw [hrpow5, hr200']
  rw [hR3] at hFcard
  exact Lemma55_close61 hr0 hr1 hL3 hKs hK0 hC₁ hC₂ (Nat.cast_nonneg _) hFcard rfl
    (Nat.cast_nonneg _) hM hNQ0 hNQ hSI0 hSI' hSH0 hSH' (by rw [← hNr]; exact hsupp)

/-- The closing estimate of Lemma 5.6 [boundspsi02]: all quantities are powers of
`r = ρ^{1/400}`. -/
private lemma Lemma55_close56 {Q0 Q00 Xa L3 ρ₀ r κ C₃ C₆ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hL3 : 0 < L3) (hC₃ : 0 ≤ C₃) (hC₆ : 0 ≤ C₆) (hκ : 0 ≤ κ)
    (h53 : |Q0 / L3 - ρ₀| ≤ C₃ * r ^ 601) (hρ₀ : |ρ₀| ≤ (1 + κ) * r ^ 400)
    (hge : Q0 ^ 2 ≤ Q00) (hle : Q00 ≤ Q0 ^ 2 + Xa)
    (h61 : (r ^ 1000)⁻¹ * (L3 ^ 2)⁻¹ * Xa ≤ C₆ * r ^ 2) :
    |Q00 / L3 ^ 2 - ρ₀ ^ 2| ≤ (C₃ ^ 2 + 2 * C₃ * (1 + κ) + C₆) * r ^ 1001 := by
  set q := Q0 / L3 with hq
  have hQ0 : Q0 ^ 2 / L3 ^ 2 = q ^ 2 := by rw [hq]; field_simp
  have hXa : Xa / L3 ^ 2 ≤ C₆ * r ^ 1001 := by
    have h1 := mul_le_mul_of_nonneg_left h61 (pow_nonneg hr0.le 1000)
    have e1 : r ^ 1000 * ((r ^ 1000)⁻¹ * (L3 ^ 2)⁻¹ * Xa) = Xa / L3 ^ 2 := by field_simp
    have e2 : r ^ 1000 * (C₆ * r ^ 2) = C₆ * r ^ 1002 := by ring
    have h2 : r ^ 1002 ≤ r ^ 1001 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left h2 hC₆
    linarith
  have hdd : |q ^ 2 - ρ₀ ^ 2| ≤ (C₃ ^ 2 + 2 * C₃ * (1 + κ)) * r ^ 1001 := by
    have e : q ^ 2 - ρ₀ ^ 2 = (q - ρ₀) * ((q - ρ₀) + 2 * ρ₀) := by ring
    rw [e, abs_mul]
    have h1 : |(q - ρ₀) + 2 * ρ₀| ≤ C₃ * r ^ 601 + 2 * ((1 + κ) * r ^ 400) := by
      calc |(q - ρ₀) + 2 * ρ₀| ≤ |q - ρ₀| + |2 * ρ₀| := abs_add_le _ _
        _ = |q - ρ₀| + 2 * |ρ₀| := by rw [abs_mul]; norm_num
        _ ≤ _ := by linarith
    calc |q - ρ₀| * |(q - ρ₀) + 2 * ρ₀|
        ≤ (C₃ * r ^ 601) * (C₃ * r ^ 601 + 2 * ((1 + κ) * r ^ 400)) :=
          mul_le_mul h53 h1 (abs_nonneg _) (by positivity)
      _ = C₃ ^ 2 * r ^ 1202 + 2 * C₃ * (1 + κ) * r ^ 1001 := by ring
      _ ≤ (C₃ ^ 2 + 2 * C₃ * (1 + κ)) * r ^ 1001 := by
          have h2 : r ^ 1202 ≤ r ^ 1001 := pow_le_pow_of_le_one hr0.le hr1 (by norm_num)
          have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg C₃)
          nlinarith
  have hup : Q00 / L3 ^ 2 ≤ q ^ 2 + Xa / L3 ^ 2 := by
    rw [← hQ0, ← add_div]
    exact div_le_div_of_nonneg_right hle (by positivity)
  have hlo : q ^ 2 ≤ Q00 / L3 ^ 2 := by
    rw [← hQ0]
    exact div_le_div_of_nonneg_right hge (by positivity)
  rw [abs_le] at hdd ⊢
  constructor <;> nlinarith [hdd.1, hdd.2]

/-- Lemma 5.6 [boundspsi02] with a rate. -/
theorem Lemma5_6 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      |Expect.Q (trialState V w kc N) [0, 0] / (LN N ^ 3) ^ 2 - rho0 (g0 V w) (rhoN N) ^ 2| ≤
        C * rhoN N ^ (5/2 + 1/400 : ℝ) := by
  obtain ⟨C₃, hC₃, N₃, h53⟩ := Lemma5_3 hg
  obtain ⟨C₆, hC₆, N₆, h61⟩ := Eq6_1 hg
  set κ : ℝ := (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  refine ⟨C₃ ^ 2 + 2 * C₃ * (1 + κ) + C₆, by positivity, max (max N₃ N₆) 1, fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₃ : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₆ : N₆ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have h53' := h53 N hN₃ kc
  have h61' := h61 N hN₆ kc
  have hge := Particles_Q00_ge V w kc hN1
  obtain ⟨hX1, hX2⟩ := Particles_Q00_eq V w kc hN1
  rw [hX1] at h61'
  have hXa0 : 0 ≤ ∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖trialState V w kc N α‖ ^ 2 :=
    tsum_nonneg fun α => by positivity
  have hle : Expect.Q (trialState V w kc N) [0, 0] ≤
      Expect.Q (trialState V w kc N) [0] ^ 2 +
        ∑' α : Occ, ((N : ℝ) - α 0) ^ 2 * ‖trialState V w kc N α‖ ^ 2 := by
    rw [hX2]
    nlinarith [sq_nonneg ((N : ℝ) - Expect.Q (trialState V w kc N) [0])]
  have hρ32 : rhoN N ^ (3 / 2 : ℝ) ≤ rhoN N := by
    have := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num : (1 : ℝ) ≤ 3 / 2)
    rwa [Real.rpow_one] at this
  have hρ₀ : |rho0 (g0 V w) (rhoN N)| ≤ (1 + κ) * rhoN N := by
    have h1 : 0 ≤ κ * rhoN N ^ (3 / 2 : ℝ) := by positivity
    have h2 : κ * rhoN N ^ (3 / 2 : ℝ) ≤ κ * rhoN N := mul_le_mul_of_nonneg_left hρ32 hκ0
    have e : rho0 (g0 V w) (rhoN N) = rhoN N - κ * rhoN N ^ (3 / 2 : ℝ) := by
      rw [rho0, hκ, mul_assoc]
    rw [e, abs_le]
    constructor <;> nlinarith
  set ρ := rhoN N with hρdef
  set r : ℝ := ρ ^ (1 / 400 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ _
  have hr1 : r ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hpow : ∀ (k : ℕ) (a : ℝ), a * 400 = k → r ^ k = ρ ^ a := fun k a ha =>
    Lemma55_pow hρ k a ha
  have hr400 : r ^ 400 = ρ := by rw [hpow 400 1 (by norm_num), Real.rpow_one]
  have hL3 : 0 < LN N ^ 3 := by positivity
  have hrpow5 : ρ ^ (-(5 / 2 : ℝ)) = (r ^ 1000)⁻¹ := by
    rw [Real.rpow_neg hρ.le, hpow 1000 (5 / 2) (by norm_num)]
  have hr200' : ρ ^ (1 / 200 : ℝ) = r ^ 2 := (hpow 2 (1 / 200) (by norm_num)).symm
  rw [hrpow5, hr200'] at h61'
  rw [← hpow 601 (3 / 2 + 1 / 400) (by norm_num)] at h53'
  have hρ₀' : |rho0 (g0 V w) ρ| ≤ (1 + κ) * r ^ 400 := by
    rw [hr400]
    exact hρ₀
  rw [← hpow 1001 (5 / 2 + 1 / 400) (by norm_num)]
  exact Lemma55_close56 hr0 hr1 hL3 hC₃ hC₆ hκ0 h53' hρ₀' hge hle h61'

end LHYUpper
