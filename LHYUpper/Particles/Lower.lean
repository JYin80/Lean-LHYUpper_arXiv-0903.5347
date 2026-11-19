import LHYUpper.Particles.Totals
import LHYUpper.Particles.Prop55

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Pointwise values of the iterated strict pair creation -/

/-- `u ≠ -u` for `u ≠ 0`. -/
private lemma Lower_ne_neg {u : Idx} (hu : u ≠ 0) : u ≠ -u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
  omega

/-- For `u ≠ 0`: `(𝓐^u β)(0) = β(0) − 2`, `(𝓐^u β)(±u) = β(±u) + 1`. -/
private lemma Lower_apply {u : Idx} (hu : u ≠ 0) (β : Occ) :
    strictPair u β 0 = β 0 - 2 ∧ strictPair u β u = β u + 1 ∧
      strictPair u β (-u) = β (-u) + 1 := by
  have h1 : (0 : Idx) ≠ u := fun h => hu h.symm
  have h2 : (0 : Idx) ≠ -u := fun h => hu (neg_eq_zero.1 h.symm)
  have h3 : u ≠ -u := Lower_ne_neg hu
  have h4 : -u ≠ (0 : Idx) := fun h => hu (neg_eq_zero.1 h)
  refine ⟨?_, ?_, ?_⟩
  · rw [MBasic_strictPair_apply]
    simp [h1, h2]
  · rw [MBasic_strictPair_apply]
    simp [hu, h3]
  · rw [MBasic_strictPair_apply]
    simp [h4, h3.symm]

/-- For `u ≠ 0`: `((𝓐^u)^j β)(0) = β(0) − 2j`, `((𝓐^u)^j β)(±u) = β(±u) + j`, and
`α*((𝓐^u)^j β, u) = α*(β, u) + j`. -/
private lemma Lower_iterate_apply {u : Idx} (hu : u ≠ 0) (β : Occ) (j : ℕ) :
    ((strictPair u)^[j] β) 0 = β 0 - 2 * j ∧ ((strictPair u)^[j] β) u = β u + j ∧
      ((strictPair u)^[j] β) (-u) = β (-u) + j ∧
      alphaStar ((strictPair u)^[j] β) u = alphaStar β u + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨h0, hu', hn, -⟩ := ih
    obtain ⟨e0, eu, en⟩ := Lower_apply hu ((strictPair u)^[j] β)
    rw [Function.iterate_succ_apply']
    refine ⟨by rw [e0, h0]; omega, by rw [eu, hu']; omega, by rw [en, hn]; omega, ?_⟩
    unfold alphaStar
    rw [eu, en, hu', hn]
    omega

/-! ### One step of rule 3 -/

/-- One application of `𝓐^u` with `u ∈ P_L`, (5.48) [lastlb2.1] for `m = 1`: if `α ∈ M`,
`𝓐^u α ∈ M`, `2 ≤ α(0)`, `0 ≤ d` and `d + 1 ≤ α(0)`, then
`(λ_u²/|Λ|²) d² |Ψ(α)|² ≤ |Ψ(𝓐^u α)|²` (Lemma 5.1, (5.5) [properf2] and (5.6) [properf3]). -/
private lemma Lower_step (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) {α : Occ} (hα : InM (rhoN N) (LN N) kc N α)
    (hα' : InM (rhoN N) (LN N) kc N (strictPair u α)) (h2 : 2 ≤ α 0) {d : ℝ} (hd : 0 ≤ d)
    (hda : d + 1 ≤ (α 0 : ℝ)) :
    lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2 * d ^ 2 * ‖trialState V w kc N α‖ ^ 2 ≤
      ‖trialState V w kc N (strictPair u α)‖ ^ 2 := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hL3 : 0 < LN N ^ 3 := by positivity
  set a : ℝ := (α 0 : ℝ) with ha
  have ha1 : 1 ≤ a - 1 := by
    have : (2 : ℝ) ≤ a := by rw [ha]; exact_mod_cast h2
    linarith
  set l := lam V w (rhoN N) (LN N) u with hl
  have hsq1 : Real.sqrt (a / LN N ^ 3) ^ 2 = a / LN N ^ 3 :=
    Real.sq_sqrt (by positivity)
  have hsq2 : Real.sqrt ((a - 1) / LN N ^ 3) ^ 2 = (a - 1) / LN N ^ 3 :=
    Real.sq_sqrt (div_nonneg (by linarith) hL3.le)
  have hbase : l ^ 2 / (LN N ^ 3) ^ 2 * d ^ 2 ≤
      (Real.sqrt (a / LN N ^ 3) * Real.sqrt ((a - 1) / LN N ^ 3) * l) ^ 2 := by
    rw [mul_pow, mul_pow, hsq1, hsq2]
    have hdd : d * d ≤ a * (a - 1) := mul_le_mul (by linarith) (by linarith) hd (by linarith)
    have e : a / LN N ^ 3 * ((a - 1) / LN N ^ 3) * l ^ 2 =
        l ^ 2 / (LN N ^ 3) ^ 2 * (a * (a - 1)) := by
      field_simp
    rw [e, sq d]
    exact mul_le_mul_of_nonneg_left hdd (by positivity)
  -- the weight ratio `c` of Lemma 5.1
  obtain ⟨c, hc, hf⟩ : ∃ c : ℝ, l ^ 2 / (LN N ^ 3) ^ 2 * d ^ 2 ≤ c ^ 2 ∧
      f0 V w (rhoN N) (LN N) (strictPair u α) = (c : ℂ) * f0 V w (rhoN N) (LN N) α := by
    by_cases hs : α u = α (-u)
    · exact ⟨_, hbase, Lemma5_1_properf2 hρ hL hu ⟨hα, hs⟩ hα'⟩
    · refine ⟨_, ?_, Lemma5_1_properf3 hρ hL hu ⟨hα, hs⟩ hα'⟩
      have hs1 : 1 ≤ alphaStar α u := by
        unfold alphaStar
        omega
      have hs3 : 1 ≤ Real.sqrt (((alphaStar α u : ℝ) + 1) / (alphaStar α u : ℝ)) ^ 2 := by
        have h1 : (1 : ℝ) ≤ (alphaStar α u : ℝ) := by exact_mod_cast hs1
        rw [Real.sq_sqrt (by positivity), le_div_iff₀ (by linarith)]
        linarith
      calc l ^ 2 / (LN N ^ 3) ^ 2 * d ^ 2
          ≤ (Real.sqrt (a / LN N ^ 3) * Real.sqrt ((a - 1) / LN N ^ 3) * l) ^ 2 := hbase
        _ = (Real.sqrt (a / LN N ^ 3) * Real.sqrt ((a - 1) / LN N ^ 3) * l) ^ 2 * 1 := by ring
        _ ≤ (Real.sqrt (a / LN N ^ 3) * Real.sqrt ((a - 1) / LN N ^ 3) * l) ^ 2 *
              Real.sqrt (((alphaStar α u : ℝ) + 1) / (alphaStar α u : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_left hs3 (by positivity)
        _ = _ := by ring
  rw [FIdentities_trialState, FIdentities_trialState, ite_eq_left hα, ite_eq_left hα', hf]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have h0 : 0 ≤ CN V w kc N ^ 2 * ‖f0 V w (rhoN N) (LN N) α‖ ^ 2 := by positivity
  calc l ^ 2 / (LN N ^ 3) ^ 2 * d ^ 2 * (CN V w kc N ^ 2 * ‖f0 V w (rhoN N) (LN N) α‖ ^ 2)
      ≤ c ^ 2 * (CN V w kc N ^ 2 * ‖f0 V w (rhoN N) (LN N) α‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hc h0
    _ = _ := by ring

/-! ### The pinned statements -/

/-- `(𝓐^u)^m` is one to one on `{β : 2m ≤ β(0)}` (Lemma 5.2 [lem-l] iterated, as used in (5.48) [lastlb2.1]). -/
theorem Particles_iterate_injOn (u : Idx) (m : ℕ) :
    Set.InjOn ((strictPair u)^[m]) {β : Occ | 2 * m ≤ β 0} := by
  induction m with
  | zero => exact fun a _ b _ h => h
  | succ m ih =>
    rw [Function.iterate_succ]
    refine ih.comp ((Reorder_strictPair_injOn u).mono fun β hβ => ?_) fun β hβ => ?_
    · simp only [Set.mem_ofPred_eq] at hβ ⊢
      omega
    · simp only [Set.mem_ofPred_eq] at hβ ⊢
      rw [MBasic_strictPair_apply]
      split_ifs <;> omega

/-- (5.48)–(5.49) and (5.54) [lastlb4] pointwise: on `P_L`, if `β*(u) + m ≤ ⌈m_c⌉` and
`2m ≤ β(0)`, then `(𝓐^u)^m β ∈ M` and `|Ψ((𝓐^u)^m β)|² ≥ (λ_u²/|Λ|²)^m (β(0) − 2m)^{2m} |Ψ(β)|²`. -/
theorem Particles_iterate (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) (m : ℕ) {β : Occ} (hβ : InM (rhoN N) (LN N) kc N β)
    (hm : alphaStar β u + m ≤ ⌈mc (rhoN N)⌉₊) (h0 : 2 * m ≤ β 0) :
    InM (rhoN N) (LN N) kc N ((strictPair u)^[m] β) ∧
      (lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2) ^ m * ((β 0 : ℝ) - 2 * m) ^ (2 * m) *
          ‖trialState V w kc N β‖ ^ 2 ≤
        ‖trialState V w kc N ((strictPair u)^[m] β)‖ ^ 2 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hu0 : u ≠ 0 := Regions_PL_ne_zero hρ hu
  have hmc0 : 0 ≤ mc (rhoN N) := Real.rpow_nonneg hρ.le _
  set A := lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2 with hA
  set d : ℝ := (β 0 : ℝ) - 2 * m with hd
  have hd0 : 0 ≤ d := by
    have : ((2 * m : ℕ) : ℝ) ≤ (β 0 : ℝ) := by exact_mod_cast h0
    push_cast at this
    linarith
  have key : ∀ j, j ≤ m → InM (rhoN N) (LN N) kc N ((strictPair u)^[j] β) ∧
      (A * d ^ 2) ^ j * ‖trialState V w kc N β‖ ^ 2 ≤
        ‖trialState V w kc N ((strictPair u)^[j] β)‖ ^ 2 := by
    intro j
    induction j with
    | zero => intro _; simp [hβ]
    | succ j ih =>
      intro hj
      obtain ⟨hM, hW⟩ := ih (by omega)
      obtain ⟨h0j, -, -, hstar⟩ := Lower_iterate_apply hu0 β j
      have h2 : 2 ≤ ((strictPair u)^[j] β) 0 := by omega
      have hlt : ((alphaStar ((strictPair u)^[j] β) u : ℕ) : ℝ) < mc (rhoN N) := by
        have h1 := Nat.ceil_lt_add_one hmc0
        have h' : ((alphaStar β u + j + 1 : ℕ) : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := by
          exact_mod_cast (by omega : alphaStar β u + j + 1 ≤ ⌈mc (rhoN N)⌉₊)
        rw [hstar]
        push_cast at h' ⊢
        linarith
      have hM' := InM.strictL hM hu hlt h2
      have hda : d + 1 ≤ ((((strictPair u)^[j] β) 0 : ℕ) : ℝ) := by
        rw [h0j]
        have : ((β 0 - 2 * j : ℕ) : ℝ) = (β 0 : ℝ) - 2 * j := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [this, hd]
        have : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
        linarith
      have hstep := Lower_step V w kc hN hu hM hM' h2 hd0 hda
      rw [Function.iterate_succ_apply']
      refine ⟨hM', ?_⟩
      have hAd : 0 ≤ A * d ^ 2 := by positivity
      calc (A * d ^ 2) ^ (j + 1) * ‖trialState V w kc N β‖ ^ 2
          = A * d ^ 2 * ((A * d ^ 2) ^ j * ‖trialState V w kc N β‖ ^ 2) := by ring
        _ ≤ A * d ^ 2 * ‖trialState V w kc N ((strictPair u)^[j] β)‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hW hAd
        _ ≤ _ := hstep
  obtain ⟨h1, h2⟩ := key m le_rfl
  refine ⟨h1, ?_⟩
  calc A ^ m * d ^ (2 * m) * ‖trialState V w kc N β‖ ^ 2
      = (A * d ^ 2) ^ m * ‖trialState V w kc N β‖ ^ 2 := by rw [mul_pow, pow_mul]
    _ ≤ _ := h2

/-! ### Elementary facts on restricted sums of `|Ψ|²` -/

/-- `|Ψ|²` vanishes off `M`. -/
private lemma Lower_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  rw [FIdentities_trialState, ite_eq_right hc, norm_zero]
  norm_num

/-- A restriction of a nonnegative summable family is summable. -/
private lemma Lower_summable_ite {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (p : Occ → Prop) [DecidablePred p] : Summable fun α => if p α then ψ α else 0 :=
  Summable.of_nonneg_of_le (fun α => by split_ifs <;> simp [hψ α])
    (fun α => by split_ifs <;> simp [hψ α]) hs

/-- A restricted family `G ψ` with `0 ≤ G ≤ B` on the support of `ψ` is summable. -/
private lemma Lower_summable_bdd {ψ G : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
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

/-- Monotonicity of restricted sums in the event, on the support of `ψ`. -/
private lemma Lower_tsum_mono {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    {P Q : Occ → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ α, P α → ψ α ≠ 0 → Q α) :
    (∑' α, if P α then ψ α else 0) ≤ ∑' α, if Q α then ψ α else 0 :=
  (Lower_summable_ite hs hψ P).tsum_le_tsum
    (fun α => by
      by_cases hp : P α
      · by_cases hz : ψ α = 0
        · simp only [hp, ite_true, hz]
          split_ifs <;> simp
        · simp [hp, h α hp hz]
      · simp only [hp, ite_false]
        split_ifs <;> simp [hψ α])
    (Lower_summable_ite hs hψ Q)

/-- A single occupation number is at most the particle number. -/
private lemma Lower_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]
    exact Nat.zero_le _

/-- On the support of `Ψ`, every occupation number is at most `N`. -/
private lemma Lower_occ_le_N {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) (n : Idx) : (α n : ℝ) ≤ N := by
  have hρ := (Particles_rhoN_LN hN).2.1
  have := MBasic_num hρ (Lower_inM h)
  have h1 := Lower_occ_le_num α n
  rw [this] at h1
  exact_mod_cast h1

/-- `Q_Ψ({u, m})` as a restricted sum. -/
private lemma Lower_Qm_single (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) :
    Expect.Qm Ψ [(u, m)] = ∑' α : Occ, if α u = m then ‖Ψ α‖ ^ 2 else 0 := by
  simp [Expect.Qm, Expect.Ev]

/-- `Σ_{i ≤ k} Σ_α [α(u) = i] f(α) = Σ_α [α(u) ≤ k] f(α)` for a summable family `f`. -/
private lemma Lower_fibre_sum {f : Occ → ℝ} (hs : Summable f) (hf : ∀ α, 0 ≤ f α) (u : Idx)
    (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (∑' α : Occ, if α u = i then f α else 0) =
      ∑' α : Occ, if α u ≤ k then f α else 0 := by
  rw [← Summable.tsum_finsetSum (fun i _ => Lower_summable_ite hs hf (fun α => α u = i))]
  refine tsum_congr fun α => ?_
  have : (∑ i ∈ Finset.range (k + 1), if α u = i then f α else 0) =
      if α u ∈ Finset.range (k + 1) then f α else 0 :=
    Finset.sum_ite_eq (Finset.range (k + 1)) (α u) (fun _ => f α)
  rw [this]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- `ρ_N^a → 0` for `a > 0`. -/
private lemma Lower_rho_pow_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.comp hT

/-! ### Jensen's inequality for `t ↦ t^k` in tangent form -/

/-- If `c > 0` is at most the `ψ`-mean of `z ≥ 0` over `E`, then `c^k Σ_E ψ ≤ Σ_E z^k ψ`; this is
the Jensen step of (5.48) [lastlb2.1], from the tangent line of `t ↦ t^k` at `c`. -/
private lemma Lower_tangent {ψ z : Occ → ℝ} (E : Occ → Prop) [DecidablePred E]
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

/-! ### The three estimates behind (5.56) [ubpsiuPL] -/

/-- (5.48)–(5.49) summed: on `P_L`, for `1 ≤ m`, `(λ_u²/|Λ|²)^m Σ_{β*(u) + m ≤ ⌈m_c⌉}
(β(0) − 2m)₊^{2m} |Ψ(β)|² ≤ Σ_{α(u) ≥ m} |Ψ(α)|²`, by injectivity of `(𝓐^u)^m`. -/
private lemma Lower_inj_bound (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) {m : ℕ} (hm : 1 ≤ m) :
    (lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2) ^ m *
        (∑' β : Occ, if alphaStar β u + m ≤ ⌈mc (rhoN N)⌉₊ then
          max ((β 0 : ℝ) - 2 * m) 0 ^ (2 * m) * ‖trialState V w kc N β‖ ^ 2 else 0) ≤
      ∑' α : Occ, if m ≤ α u then ‖trialState V w kc N α‖ ^ 2 else 0 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hu0 : u ≠ 0 := Regions_PL_ne_zero hρ hu
  have hΨ := Normalization_isNState V w kc hN
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψ
  have hψs : Summable ψ := hΨ.1.summable
  have hψ0 : ∀ α, 0 ≤ ψ α := fun _ => by positivity
  set A := lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  set E : Occ → Prop := fun β => alphaStar β u + m ≤ ⌈mc (rhoN N)⌉₊ with hE
  set z : Occ → ℝ := fun β => max ((β 0 : ℝ) - 2 * m) 0 with hz
  set F : Occ → ℝ := fun β => if E β then A ^ m * (z β ^ (2 * m) * ψ β) else 0 with hF
  have hzN : ∀ β, ψ β ≠ 0 → z β ^ (2 * m) ≤ (N : ℝ) ^ (2 * m) := fun β hβ => by
    refine pow_le_pow_left₀ (le_max_right _ _) (max_le ?_ (Nat.cast_nonneg N)) _
    have := Lower_occ_le_N hN hβ 0
    linarith
  have hFs : Summable F := by
    have := (Lower_summable_bdd hψs hψ0 E _ (fun β => by positivity) hzN).mul_left (A ^ m)
    refine this.congr fun β => ?_
    simp only [hF, mul_ite, mul_zero]
  have hgs := Lower_summable_ite hψs hψ0 (fun α => m ≤ α u)
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
          · exact absurd (Lower_inM hz0) h
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
  have hLHS : A ^ m * (∑' β : Occ, if E β then z β ^ (2 * m) * ψ β else 0) = ∑' β, F β := by
    rw [← tsum_mul_left]
    refine tsum_congr fun β => ?_
    simp only [hF, mul_ite, mul_zero]
  change A ^ m * (∑' β : Occ, if E β then z β ^ (2 * m) * ψ β else 0) ≤ _
  rw [hLHS, hsum]
  refine Summable.tsum_le_tsum_of_inj (fun x : S => (strictPair u)^[m] x.1) ?_
    (fun _ _ => by split_ifs <;> simp) (fun x => ?_) (hFs.subtype (· ∈ S)) hgs
  · intro x y hxy
    exact Subtype.ext (Particles_iterate_injOn u m x.2.2.2 y.2.2.2 hxy)
  · obtain ⟨hxM, hxE, hx0⟩ := x.2
    obtain ⟨-, hxu, -, -⟩ := Lower_iterate_apply hu0 x.1 m
    have hmu : m ≤ ((strictPair u)^[m] x.1) u := by omega
    have hzx : z x.1 = (x.1 0 : ℝ) - 2 * m := by
      simp only [hz]
      refine max_eq_left ?_
      have : ((2 * m : ℕ) : ℝ) ≤ (x.1 0 : ℝ) := by exact_mod_cast hx0
      push_cast at this
      linarith
    have hit := (Particles_iterate V w kc hN hu m hxM hxE hx0).2
    simp only [hF, hxE, ite_true, hmu, hzx]
    calc A ^ m * (((x.1 0 : ℝ) - 2 * m) ^ (2 * m) * ψ x.1)
        = A ^ m * ((x.1 0 : ℝ) - 2 * m) ^ (2 * m) * ‖trialState V w kc N x.1‖ ^ 2 := by
          simp only [hψ]; ring
      _ ≤ _ := hit

/-- (5.46) [mcmlbum1] on the event of (5.48): on `P_L`, for `m + 1 ≤ ⌈m_c⌉`,
`(⌈m_c⌉ − m)/(⌈m_c⌉ + 1) ≤ Σ_{β*(u) + m ≤ ⌈m_c⌉} |Ψ(β)|²`. -/
private lemma Lower_PE {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u → ∀ m : ℕ,
      m + 1 ≤ ⌈mc (rhoN N)⌉₊ →
      ((⌈mc (rhoN N)⌉₊ : ℝ) - m) / ((⌈mc (rhoN N)⌉₊ : ℝ) + 1) ≤
        ∑' β : Occ, if alphaStar β u + m ≤ ⌈mc (rhoN N)⌉₊ then
          ‖trialState V w kc N β‖ ^ 2 else 0 := by
  obtain ⟨N₄, h46⟩ := Eq5_46 hg
  refine ⟨max N₄ 1, fun N hN kc u hu m hm => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₄ : N₄ ≤ N := le_trans (le_max_left _ _) hN
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  have hψs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ0 : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  set M := ⌈mc (rhoN N)⌉₊ with hM
  set k := M - m - 1 with hk
  have hkM : k ≤ M := by omega
  have h1 := h46 N hN₄ kc u hu k hkM
  simp_rw [Lower_Qm_single] at h1
  rw [Lower_fibre_sum hψs hψ0 u k] at h1
  have hkr : (k : ℝ) + 1 = (M : ℝ) - m := by
    have : k + m + 1 = M := by omega
    have h' : ((k + m + 1 : ℕ) : ℝ) = (M : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  rw [hkr] at h1
  refine h1.trans (Lower_tsum_mono hψs hψ0 fun α hα hz => ?_)
  rcases MStar_PL_star hρ (Lower_inM hz) hu with h | h <;> omega

/-- `Σ_{j < n} Σ_α [α(u) ≥ j + 1] |Ψ(α)|² ≤ Q_Ψ(u)`, from `Q_Ψ(u) = Σ_α α(u)|Ψ(α)|²`. -/
private lemma Lower_Q_ge (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) (n : ℕ) :
    ∑ j ∈ Finset.range n, (∑' α : Occ, if j + 1 ≤ α u then ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      Expect.Q (trialState V w kc N) [u] := by
  have hΨ := Normalization_isNState V w kc hN
  have hψs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ0 : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  have hocc : Summable fun α : Occ => (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by
    have := Lower_summable_bdd hψs hψ0 (fun _ => True) N (G := fun α => (α u : ℝ))
      (fun _ => by positivity) (fun α hα => Lower_occ_le_N hN hα u)
    simpa using this
  unfold Expect.Q
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  rw [← Summable.tsum_finsetSum
    (fun j _ => Lower_summable_ite hψs hψ0 (fun α => j + 1 ≤ α u))]
  refine (summable_sum fun j _ => Lower_summable_ite hψs hψ0 (fun α => j + 1 ≤ α u)).tsum_le_tsum
    (fun α => ?_) hocc
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hψ0 α)
  have : ((Finset.range n).filter fun j => j + 1 ≤ α u) ⊆ Finset.range (α u) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  have h2 := Finset.card_le_card this
  rw [Finset.card_range] at h2
  exact_mod_cast h2

/-- `N − Q_Ψ(0) ≤ K N ρ^{1/2}` with `K = (3π²)⁻¹ g₀^{3/2} + C`, from (5.32) [resultlbpsi0]. -/
private lemma Lower_Q0 {V w : R3 → ℝ} {kc C : ℝ} {N : ℕ} (hN : 1 ≤ N) (hC : 0 ≤ C)
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

/-- (5.48)–(5.54) [lastlb4] for one `m`: on `P_L`, for `1 ≤ m ≤ n`, with
`θ = 1 − 2n/N − 2Kρ^{1/2} > 0`, `N − Q_Ψ(0) ≤ KNρ^{1/2}` ((5.32) [resultlbpsi0]) and
`Σ_{β*(u) + m ≤ ⌈m_c⌉} |Ψ|² ≥ 1/2`: `((ρλ_u)² θ²)^m Σ_{β*(u) + m ≤ ⌈m_c⌉} |Ψ|² ≤
Σ_{α(u) ≥ m} |Ψ|²`. -/
private lemma Lower_Tm (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN1 : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) {K : ℝ} (hK0 : 0 ≤ K)
    (hQ0 : (N : ℝ) - Expect.Q (trialState V w kc N) [0] ≤ K * N * rhoN N ^ (1 / 2 : ℝ))
    {m n : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (hθ0 : 0 < 1 - 2 * n / N - 2 * K * rhoN N ^ (1 / 2 : ℝ))
    (hPhalf : 1 / 2 ≤ ∑' β : Occ, if alphaStar β u + m ≤ ⌈mc (rhoN N)⌉₊ then
      ‖trialState V w kc N β‖ ^ 2 else 0) :
    ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
        (1 - 2 * n / N - 2 * K * rhoN N ^ (1 / 2 : ℝ)) ^ 2) ^ m *
        (∑' β : Occ, if alphaStar β u + m ≤ ⌈mc (rhoN N)⌉₊ then
          ‖trialState V w kc N β‖ ^ 2 else 0) ≤
      ∑' α : Occ, if m ≤ α u then ‖trialState V w kc N α‖ ^ 2 else 0 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψ
  have hψs : Summable ψ := hΨ.1.summable
  have hψ0 : ∀ α, 0 ≤ ψ α := fun _ => by positivity
  set ρ := rhoN N with hρdef
  set θ : ℝ := 1 - 2 * n / N - 2 * K * ρ ^ (1 / 2 : ℝ) with hθ
  set c : ℝ := N * θ with hc
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c := by positivity
  set x : ℝ := (ρ * lam V w ρ (LN N) u) ^ 2 with hx
  set A := lam V w ρ (LN N) u ^ 2 / (LN N ^ 3) ^ 2 with hA
  have hAc : A * c ^ 2 = x * θ ^ 2 := by
    rw [hA, hc, hx, ← hNL]
    field_simp
  set M := ⌈mc ρ⌉₊ with hM
  set E : Occ → Prop := fun β => alphaStar β u + m ≤ M with hE
  set P := ∑' β : Occ, if E β then ψ β else 0 with hP
  -- Proposition 5.5 [prop6] on `E` and the mean of `(β(0) − 2m)₊`
  have hev := Prop5_5_event V w kc hN1 E
  set z : Occ → ℝ := fun β => max ((β 0 : ℝ) - 2 * m) 0 with hz
  have hzN : ∀ β, ψ β ≠ 0 → z β ≤ N := fun β hβ => by
    refine max_le ?_ (Nat.cast_nonneg N)
    have := Lower_occ_le_N hN1 hβ 0
    linarith
  have hz0 : ∀ β, 0 ≤ z β := fun β => le_max_right _ _
  have hs1 := Lower_summable_ite hψs hψ0 E
  have hs2 := Lower_summable_bdd hψs hψ0 E N hz0 hzN
  have hs0 := Lower_summable_bdd hψs hψ0 E N (G := fun β => (β 0 : ℝ))
    (fun _ => by positivity) (fun β hβ => Lower_occ_le_N hN1 hβ 0)
  have hs3 := Lower_summable_bdd hψs hψ0 E ((N : ℝ) ^ (2 * m)) (G := fun β => z β ^ (2 * m))
    (fun β => by positivity) (fun β hβ => pow_le_pow_left₀ (hz0 β) (hzN β hβ) _)
  have hmean : c * P ≤ ∑' β, if E β then z β * ψ β else 0 := by
    have h1 : (∑' β, if E β then ((β 0 : ℝ) - 2 * m) * ψ β else 0) ≤
        ∑' β, if E β then z β * ψ β else 0 := by
      have hs4 : Summable fun β => if E β then ((β 0 : ℝ) - 2 * m) * ψ β else 0 := by
        refine (hs0.sub (hs1.mul_left (2 * (m : ℝ)))).congr fun β => ?_
        split_ifs <;> ring
      refine hs4.tsum_le_tsum (fun β => ?_) hs2
      split_ifs
      · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hψ0 β)
      · exact le_rfl
    have h2 : (∑' β, if E β then ((β 0 : ℝ) - 2 * m) * ψ β else 0) =
        (∑' β, if E β then (β 0 : ℝ) * ψ β else 0) - 2 * m * P := by
      rw [hP, ← tsum_mul_left, ← hs0.tsum_sub (hs1.mul_left _)]
      refine tsum_congr fun β => ?_
      split_ifs <;> ring
    have h3 : (N : ℝ) * P - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) ≤
        ∑' β, if E β then (β 0 : ℝ) * ψ β else 0 := by
      convert hev
    have h4 : c * P ≤ (N : ℝ) * P - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) -
        2 * m * P := by
      have e : (N : ℝ) * P - 2 * m * P - c * P = (2 * n - 2 * m) * P +
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
  have htan := Lower_tangent E hψ0 hz0 hs1 hs2 (2 * m) hs3 hc0 hmean
  have hinj := Lower_inj_bound V w kc hN1 hu hm1
  have e : (x * θ ^ 2) ^ m = A ^ m * c ^ (2 * m) := by
    rw [← hAc, mul_pow, pow_mul]
  calc (x * θ ^ 2) ^ m * P = A ^ m * (c ^ (2 * m) * P) := by rw [e]; ring
    _ ≤ A ^ m * (∑' β, if E β then z β ^ (2 * m) * ψ β else 0) :=
        mul_le_mul_of_nonneg_left htan (by positivity)
    _ ≤ _ := hinj

/-- (5.56) [ubpsiuPL], with `n = ⌈√m_c⌉` and the loss `3ρ^{η/2}`. -/
theorem Eq5_56 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      (1 - 3 * rhoN N ^ (1/400 : ℝ)) *
          ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
            (1 - ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) ^ ⌈Real.sqrt (mc (rhoN N))⌉₊) /
            (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2)) ≤
        Expect.Q (trialState V w kc N) [u] := by
  obtain ⟨C₃, hC₃, N₃, h32⟩ := Eq5_32 hg
  obtain ⟨N₄, hPE⟩ := Lower_PE hg
  set K : ℝ := (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) + C₃ with hK
  have hK0 : 0 ≤ K := by positivity
  have hev1 : ∀ᶠ N : ℕ in atTop, rhoN N ^ (1 / 400 : ℝ) ≤ 1 / 5 :=
    (Lower_rho_pow_tendsto (by norm_num)).eventually (ge_mem_nhds (by norm_num))
  have hev2 : ∀ᶠ N : ℕ in atTop, (10 + 5 * K) * rhoN N ^ (99 / 200 : ℝ) ≤ 1 := by
    have h := (Lower_rho_pow_tendsto (a := 99 / 200) (by norm_num)).const_mul (10 + 5 * K)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.1 (hev1.and hev2)
  refine ⟨max (max (max N₃ N₄) N₅) 1, fun N hN kc u hu => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₃ : N₃ ≤ N :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₄ : N₄ ≤ N :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₅' : N₅ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hr5', hrK'⟩ := hN₅ N hN₅'
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψ
  have hψs : Summable ψ := hΨ.1.summable
  have hψ0 : ∀ α, 0 ≤ ψ α := fun _ => by positivity
  have hQ0 := Lower_Q0 hN1 hC₃ (h32 N hN₃ kc)
  rw [← hK] at hQ0
  -- the parameters `r = ρ^{1/400}`, `m_c = r^{-2}`, `√m_c = r^{-1}`
  set ρ := rhoN N with hρdef
  set r : ℝ := ρ ^ (1 / 400 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ _
  have hr5 : r ≤ 1 / 5 := hr5'
  have hpow : ∀ (k : ℕ) (a : ℝ), a * 400 = k → r ^ k = ρ ^ a := by
    intro k a ha
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le, ← ha]
    ring_nf
  have hrK : (10 + 5 * K) * r ^ 198 ≤ 1 := by
    rw [hpow 198 (99 / 200) (by norm_num)]
    exact hrK'
  have hr400 : r ^ 400 = ρ := by rw [hpow 400 1 (by norm_num), Real.rpow_one]
  have hr200 : r ^ 200 = ρ ^ (1 / 2 : ℝ) := hpow 200 (1 / 2) (by norm_num)
  have hmc : mc ρ = (r ^ 2)⁻¹ := by
    rw [mc, Real.rpow_neg hρ.le, hpow 2 (1 / 200) (by norm_num)]
  have hsqrt : Real.sqrt (mc ρ) = r⁻¹ := by
    rw [hmc, Real.sqrt_inv, Real.sqrt_sq hr0.le]
  set M := ⌈mc ρ⌉₊ with hM
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
  have hNinv : (N : ℝ)⁻¹ ≤ ρ := by
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    rw [hρdef, rhoN, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1' (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  -- the loss `b = (n + 1)/(⌈m_c⌉ + 1) ≤ r + 2r²`
  set b : ℝ := ((n : ℝ) + 1) / ((M : ℝ) + 1) with hb
  have hb0 : 0 ≤ b := by positivity
  have hbr : b ≤ r + 2 * r ^ 2 := by
    rw [hb, div_le_iff₀ (by positivity)]
    have h1 : (r + 2 * r ^ 2) * (r ^ 2)⁻¹ = r⁻¹ + 2 := by
      field_simp
    have h2 : (r + 2 * r ^ 2) * (r ^ 2)⁻¹ ≤ (r + 2 * r ^ 2) * ((M : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hr2 : r ^ 2 ≤ 1 / 5 * r := by
    rw [sq]
    calc r * r ≤ r * (1 / 5) := mul_le_mul_of_nonneg_left hr5 hr0.le
      _ = 1 / 5 * r := by ring
  have hb1 : b ≤ 7 / 5 * r := by linarith
  have hnM : n + 1 ≤ M := by
    have : b < 1 := by linarith
    rw [hb, div_lt_one (by positivity)] at this
    have : ((n + 1 : ℕ) : ℝ) < ((M + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := Nat.cast_lt.1 this
    omega
  -- `θ = 1 − 2n/N − 2Kρ^{1/2}` and the loss `2n(1 − θ) ≤ (8/5) r`
  set θ : ℝ := 1 - 2 * n / N - 2 * K * ρ ^ (1 / 2 : ℝ) with hθ
  have hθ1 : θ ≤ 1 := by
    have : 0 ≤ 2 * (n : ℝ) / N := by positivity
    have : 0 ≤ 2 * K * ρ ^ (1 / 2 : ℝ) := by positivity
    linarith
  have hloss : 2 * n * (1 - θ) ≤ 8 / 5 * r := by
    have e : 2 * n * (1 - θ) = 4 * ((n : ℝ) ^ 2 * (N : ℝ)⁻¹) + 4 * K * (n * ρ ^ (1 / 2 : ℝ)) := by
      rw [hθ]
      field_simp
      ring
    have h1 : (n : ℝ) ^ 2 * (N : ℝ)⁻¹ ≤ 4 * r ^ 398 := by
      calc (n : ℝ) ^ 2 * (N : ℝ)⁻¹ ≤ (n : ℝ) ^ 2 * ρ :=
            mul_le_mul_of_nonneg_left hNinv (by positivity)
        _ = ((n : ℝ) * r) ^ 2 * r ^ 398 := by rw [← hr400]; ring
        _ ≤ 2 ^ 2 * r ^ 398 :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnr 2) (by positivity)
        _ = 4 * r ^ 398 := by norm_num
    have h2 : (n : ℝ) * ρ ^ (1 / 2 : ℝ) ≤ 2 * r ^ 199 := by
      calc (n : ℝ) * ρ ^ (1 / 2 : ℝ) = ((n : ℝ) * r) * r ^ 199 := by rw [← hr200]; ring
        _ ≤ 2 * r ^ 199 := mul_le_mul_of_nonneg_right hnr (by positivity)
    have h3 : r ^ 398 ≤ r ^ 199 := pow_le_pow_of_le_one hr0.le (by linarith) (by norm_num)
    have h4 : (16 + 8 * K) * r ^ 199 ≤ 8 / 5 * r := by
      have : (16 + 8 * K) * r ^ 199 = 8 / 5 * r * ((10 + 5 * K) * r ^ 198) := by ring
      rw [this]
      calc 8 / 5 * r * ((10 + 5 * K) * r ^ 198) ≤ 8 / 5 * r * 1 :=
            mul_le_mul_of_nonneg_left hrK (by positivity)
        _ = _ := by ring
    have h5 : 4 * K * ((n : ℝ) * ρ ^ (1 / 2 : ℝ)) ≤ 4 * K * (2 * r ^ 199) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [e]
    linarith
  have hθ0 : 0 < θ := by
    have h0 : (1 : ℝ) ≤ n := by exact_mod_cast hn1'
    have h1 : 0 ≤ 1 - θ := by linarith
    have h2 : 1 - θ ≤ n * (1 - θ) := le_mul_of_one_le_left h1 h0
    linarith
  set c : ℝ := N * θ with hc
  have hc0 : 0 < c := by positivity
  -- `x_u = (ρλ_u)² ∈ (0, 1)`
  set x : ℝ := (ρ * lam V w ρ (LN N) u) ^ 2 with hx
  obtain ⟨hl0, hl1⟩ := Particles_rho_lam_PL hg hρ hρ1 hu
  have hx0 : 0 < x := by rw [hx, sq]; exact mul_pos_of_neg_of_neg hl0 hl0
  have hx1 : x < 1 := by
    have h1 : 0 < epsP ρ / (1 + Real.sqrt (g0 V w)) := by
      have := Real.sqrt_nonneg (g0 V w)
      unfold epsP
      positivity
    have h2 : 0 < -(ρ * lam V w ρ (LN N) u) := by linarith
    have h3 : -(ρ * lam V w ρ (LN N) u) < 1 := by linarith
    calc x = (-(ρ * lam V w ρ (LN N) u)) * (-(ρ * lam V w ρ (LN N) u)) := by rw [hx]; ring
      _ < 1 * 1 := mul_lt_mul'' h3 h3 h2.le h2.le
      _ = 1 := one_mul 1
  set A := lam V w ρ (LN N) u ^ 2 / (LN N ^ 3) ^ 2 with hA
  have hAc : A * c ^ 2 = x * θ ^ 2 := by
    rw [hA, hc, hx, ← hNL]
    field_simp
  -- the bound on `Σ_{α(u) ≥ m} |Ψ|²` for `1 ≤ m ≤ n`
  have hT : ∀ m : ℕ, 1 ≤ m → m ≤ n →
      (x * θ ^ 2) ^ m * (((M : ℝ) - n) / ((M : ℝ) + 1)) ≤
        ∑' α : Occ, if m ≤ α u then ψ α else 0 := by
    intro m hm1 hmn
    have hPge := hPE N hN₄ kc u hu m (le_trans (by omega : m + 1 ≤ n + 1) hnM)
    have hPn : ((M : ℝ) - n) / ((M : ℝ) + 1) ≤
        ∑' β : Occ, if alphaStar β u + m ≤ M then ψ β else 0 := by
      refine le_trans ?_ hPge
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have hPb : ((M : ℝ) - n) / ((M : ℝ) + 1) = 1 - b := by
      rw [hb]
      field_simp
      ring
    have hPhalf : 1 / 2 ≤ ∑' β : Occ, if alphaStar β u + m ≤ M then ψ β else 0 := by
      rw [hPb] at hPn
      linarith
    have h1 := Lower_Tm V w kc hN1 hu hK0 hQ0 hm1 hmn hθ0 hPhalf
    exact (mul_le_mul_of_nonneg_left hPn (by positivity)).trans h1
  -- summing over `m = 1, …, n`
  have hsumT := Lower_Q_ge V w kc hN1 u n
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
  set q : ℝ := (θ ^ 2) ^ n * (1 - b) with hq
  have hterm : ∀ j ∈ Finset.range n, q * x ^ (j + 1) ≤
      ∑' α : Occ, if j + 1 ≤ α u then ψ α else 0 := by
    intro j hj
    have hj' : j + 1 ≤ n := Finset.mem_range.1 hj
    have h1 := hT (j + 1) (by omega) hj'
    have hPb : ((M : ℝ) - n) / ((M : ℝ) + 1) = 1 - b := by
      rw [hb]
      field_simp
      ring
    rw [hPb] at h1
    have h2 : (θ ^ 2) ^ n ≤ (θ ^ 2) ^ (j + 1) := pow_le_pow_of_le_one hθ2 hθ21 hj'
    have h3 : 0 ≤ 1 - b := by linarith
    calc q * x ^ (j + 1) = x ^ (j + 1) * (θ ^ 2) ^ n * (1 - b) := by rw [hq]; ring
      _ ≤ x ^ (j + 1) * (θ ^ 2) ^ (j + 1) * (1 - b) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by positivity)) h3
      _ = (x * θ ^ 2) ^ (j + 1) * (1 - b) := by rw [mul_pow]
      _ ≤ _ := h1
  have hsum := Finset.sum_le_sum hterm
  rw [← Finset.mul_sum, hgeom] at hsum
  -- the coefficient `q ≥ 1 − 3r`
  have hq3 : 1 - 3 * r ≤ q := by
    have h1 := one_add_mul_le_pow (a := θ ^ 2 - 1) (by linarith [hθ2]) n
    rw [show 1 + (θ ^ 2 - 1) = θ ^ 2 by ring] at h1
    have h2 : 1 - 8 / 5 * r ≤ (θ ^ 2) ^ n := by
      have : (n : ℝ) * (θ ^ 2 - 1) ≥ -(2 * n * (1 - θ)) := by
        have h5 : 1 - θ ^ 2 ≤ 2 * (1 - θ) :=
          calc 1 - θ ^ 2 = (1 - θ) * (1 + θ) := by ring
            _ ≤ (1 - θ) * 2 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
            _ = 2 * (1 - θ) := by ring
        have h6 := mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
        have e1 : (n : ℝ) * (θ ^ 2 - 1) = -((n : ℝ) * (1 - θ ^ 2)) := by ring
        have e2 : 2 * (n : ℝ) * (1 - θ) = (n : ℝ) * (2 * (1 - θ)) := by ring
        rw [e1, e2]
        linarith
      linarith
    have h3 : 0 ≤ 1 - 8 / 5 * r := by linarith
    have h4 : 1 - 7 / 5 * r ≤ 1 - b := by linarith
    have e3 : (1 - 8 / 5 * r) * (1 - 7 / 5 * r) = 1 - 3 * r + 56 / 25 * r ^ 2 := by ring
    have h5 := sq_nonneg r
    calc 1 - 3 * r ≤ (1 - 8 / 5 * r) * (1 - 7 / 5 * r) := by rw [e3]; linarith
      _ ≤ (θ ^ 2) ^ n * (1 - b) := mul_le_mul h2 h4 (by linarith) (by positivity)
  have hS0 : 0 ≤ x * (1 - x ^ n) / (1 - x) := by
    have : x ^ n ≤ 1 := pow_le_one₀ hx0.le hx1.le
    exact div_nonneg (mul_nonneg hx0.le (sub_nonneg.2 this)) (sub_pos.2 hx1).le
  calc (1 - 3 * r) * (x * (1 - x ^ n) / (1 - x)) ≤ q * (x * (1 - x ^ n) / (1 - x)) :=
        mul_le_mul_of_nonneg_right hq3 hS0
    _ ≤ _ := hsum.trans hsumT

/-! ### Sums over `P_L` -/

/-- For all large `N`: `N ≥ 1`, `ρ_N^{1/400} ≤ 1/5` and `2π ≤ L_N ρ_N^{1/2}`. -/
private lemma Lower_eventually :
    ∀ᶠ N : ℕ in atTop, 1 ≤ N ∧ rhoN N ^ (1 / 400 : ℝ) ≤ 1 / 5 ∧
      2 * π ≤ LN N * rhoN N ^ (1 / 2 : ℝ) := by
  have h1 : ∀ᶠ N : ℕ in atTop, rhoN N ^ (1 / 400 : ℝ) ≤ 1 / 5 :=
    (Lower_rho_pow_tendsto (by norm_num)).eventually (ge_mem_nhds (by norm_num))
  have h2 : ∀ᶠ N : ℕ in atTop, 2 * π * rhoN N ^ (13 / 24 : ℝ) ≤ 1 := by
    have h := (Lower_rho_pow_tendsto (a := 13 / 24) (by norm_num)).const_mul (2 * π)
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop 1, h1, h2] with N hN hr hΔ
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  refine ⟨hN, hr, ?_⟩
  have hq : 0 < rhoN N ^ (13 / 24 : ℝ) := Real.rpow_pos_of_pos hρ _
  have e : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) = 1 := by
    rw [LN, mul_assoc, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
    norm_num
  by_contra h
  have h' : LN N * rhoN N ^ (1 / 2 : ℝ) * rhoN N ^ (13 / 24 : ℝ) <
      2 * π * rhoN N ^ (13 / 24 : ℝ) := mul_lt_mul_of_pos_right (not_le.1 h) hq
  linarith

/-- `L ρ^{1/2} = ρ^{-13/24}` at `L = L_N`, `ρ = ρ_N`. -/
private lemma Lower_L_sqrt {N : ℕ} (hρ : 0 < rhoN N) :
    LN N * rhoN N ^ (1 / 2 : ℝ) = (rhoN N ^ (13 / 24 : ℝ))⁻¹ := by
  rw [LN, ← Real.rpow_add hρ, ← Real.rpow_neg hρ.le]
  norm_num

/-- `√m_c = ρ^{-1/400}`, (3.8) [defmc]. -/
private lemma Lower_sqrt_mc {ρ : ℝ} (hρ : 0 < ρ) : Real.sqrt (mc ρ) = (ρ ^ (1 / 400 : ℝ))⁻¹ := by
  have e : mc ρ = ((ρ ^ (1 / 400 : ℝ)) ^ 2)⁻¹ := by
    rw [mc, Real.rpow_neg hρ.le, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  rw [e, Real.sqrt_inv, Real.sqrt_sq (Real.rpow_nonneg hρ.le _)]

/-- A function on `Idx` supported in `{‖p_n‖ ≤ R}` is summable. -/
private lemma Lower_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
    (hf : ∀ n, f n ≠ 0 → ‖mom L n‖ ≤ R) : Summable f := by
  have hfin : {n : Idx | ‖mom L n‖ ≤ R}.Finite := by
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
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  by_contra h
  exact hn (hfin.mem_toFinset.2 (hf n h))

/-- A family restricted to `P_L` is summable. -/
private lemma Lower_summable_PL {N : ℕ} (hN : 1 ≤ N) (f : Idx → ℝ) :
    Summable fun n => if inPL (rhoN N) (LN N) n then f n else 0 :=
  Lower_summable_ball (R := (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ))
    (Particles_rhoN_LN hN).2.2.2 _ (fun n hn => by
      by_contra h
      exact hn (by simp [show ¬ inPL (rhoN N) (LN N) n from fun h' => h h'.2]))

/-- `Q_Ψ(n) ≥ 0`. -/
private lemma Lower_Q_nonneg (Ψ : Occ → ℂ) (n : Idx) : 0 ≤ Expect.Q Ψ [n] := by
  unfold Expect.Q
  refine tsum_nonneg fun α => ?_
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  positivity

/-- The tail of (5.56) is the summand of the tail sum at `t = 2n`: `|y|^{2n} = (y²)^n`. -/
private lemma Lower_tail_exp (y : ℝ) (n : ℕ) : |y| ^ ((2 * n : ℕ) : ℝ) = (y ^ 2) ^ n := by
  rw [Real.rpow_natCast, pow_mul, sq_abs]

/-- (5.43) [upt01] with a rate. -/
theorem Eq5_43 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) - C * rhoN N ^ (1/400 : ℝ) ≤
        rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
          (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
            Expect.Q (trialState V w kc N) [n] else 0)) := by
  obtain ⟨N₅, h56⟩ := Eq5_56 hg
  obtain ⟨K₁, hK₁, hocc⟩ := sum_PL_occ hg
  obtain ⟨K₂, hK₂, htail⟩ := sum_PL_tail hg
  obtain ⟨N₂, h₂⟩ := eventually_atTop.1 Lower_eventually
  set G := g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) with hGdef
  have hG0 : 0 ≤ G := by positivity
  refine ⟨3 * G + (K₁ + K₂) * (1 + 2 * π), by positivity, max N₅ N₂, fun N hN kc => ?_⟩
  obtain ⟨hN1, hr5, hL2π⟩ := h₂ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set r : ℝ := ρ ^ (1 / 400 : ℝ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ _
  set n := ⌈Real.sqrt (mc ρ)⌉₊ with hn
  have hn1 : r⁻¹ ≤ n := by rw [← Lower_sqrt_mc hρ]; exact Nat.le_ceil _
  set lp : Idx → ℝ := fun k => ρ * lamPL (g0 V w) ρ (mom L k) with hlp
  set fm : Idx → ℝ := fun k => lp k ^ 2 / (1 - lp k ^ 2) with hfm
  set ft : Idx → ℝ := fun k => |lp k| ^ ((2 * n : ℕ) : ℝ) * fm k with hft
  set Q : Idx → ℝ := fun k => Expect.Q (trialState V w kc N) [k] with hQ
  have hQs : Summable Q := (Particles_hasSum_Q V w kc hN1).summable
  have hsQ : Summable fun k => if inPL ρ L k then Q k else 0 :=
    Summable.of_nonneg_of_le (fun k => by split_ifs; exacts [Lower_Q_nonneg _ _, le_rfl])
      (fun k => by split_ifs; exacts [le_rfl, Lower_Q_nonneg _ _]) hQs
  have hsm := Lower_summable_PL hN1 fm
  have hst := Lower_summable_PL hN1 ft
  -- (5.56) [ubpsiuPL] summed over `P_L`
  have hpt : ∀ k, (if inPL ρ L k then (1 - 3 * r) * (fm k - ft k) else 0) ≤
      if inPL ρ L k then Q k else 0 := by
    intro k
    split_ifs with hk
    · have h1 := h56 N (le_of_max_le_left hN) kc k hk
      rw [lam_of_inPL hk] at h1
      have e : (1 - 3 * r) * (fm k - ft k) = (1 - 3 * ρ ^ (1 / 400 : ℝ)) *
          ((ρ * lamPL (g0 V w) ρ (mom L k)) ^ 2 *
            (1 - ((ρ * lamPL (g0 V w) ρ (mom L k)) ^ 2) ^ n) /
            (1 - (ρ * lamPL (g0 V w) ρ (mom L k)) ^ 2)) := by
        simp only [hfm, hft, hlp, Lower_tail_exp]
        ring
      rw [e]
      exact h1
    · exact le_rfl
  have hsum1 : (1 - 3 * r) * ((∑' k, if inPL ρ L k then fm k else 0) -
      ∑' k, if inPL ρ L k then ft k else 0) ≤ ∑' k, if inPL ρ L k then Q k else 0 := by
    have e : (1 - 3 * r) * ((∑' k, if inPL ρ L k then fm k else 0) -
        ∑' k, if inPL ρ L k then ft k else 0) =
        ∑' k, if inPL ρ L k then (1 - 3 * r) * (fm k - ft k) else 0 := by
      rw [← hsm.tsum_sub hst, ← tsum_mul_left]
      exact tsum_congr fun k => by split_ifs <;> ring
    rw [e]
    exact (Lower_summable_PL hN1 _).tsum_le_tsum hpt hsQ
  -- the scaled main term and the scaled tail
  have hΔ : 2 * π / (L * ρ ^ (1 / 2 : ℝ)) ≤ 2 * π * r := by
    rw [hLdef, hρdef, Lower_L_sqrt hρ, div_inv_eq_mul]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)) (by positivity)
  have hr2 : ρ ^ (1 / 200 : ℝ) = r ^ 2 := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  have hr1 : r ≤ 1 := by linarith
  have hrr : r ^ 2 ≤ r := by
    rw [sq]
    exact mul_le_of_le_one_left hr0.le hr1
  set Φ : ℝ := ρ ^ (-(3/2 : ℝ)) * (L ^ 3)⁻¹ with hΦ
  have hmain : G - K₁ * (1 + 2 * π) * r ≤ Φ * ∑' k, if inPL ρ L k then fm k else 0 := by
    have h1 := (abs_le.1 (hocc ρ L hρ hρ1 hL2π)).1
    have h2 : K₁ * (ρ ^ (1 / 200 : ℝ) + 2 * π / (L * ρ ^ (1 / 2 : ℝ))) ≤ K₁ * (1 + 2 * π) * r := by
      rw [hr2]
      calc K₁ * (r ^ 2 + 2 * π / (L * ρ ^ (1 / 2 : ℝ))) ≤ K₁ * (r + 2 * π * r) :=
            mul_le_mul_of_nonneg_left (add_le_add hrr hΔ) hK₁
        _ = _ := by ring
    have e : Φ * (∑' k, if inPL ρ L k then fm k else 0) =
        (L ^ 3)⁻¹ * ρ ^ (-(3 / 2 : ℝ)) * ∑' k, if inPL ρ L k then
          (ρ * lamPL (g0 V w) ρ (mom L k)) ^ 2 / (1 - (ρ * lamPL (g0 V w) ρ (mom L k)) ^ 2)
          else 0 := by
      rw [hΦ]
      ring
    rw [e]
    linarith
  have htl : Φ * (∑' k, if inPL ρ L k then ft k else 0) ≤ K₂ * (1 + 2 * π) * r := by
    have h1 := htail ((2 * n : ℕ) : ℝ) ρ L (Nat.cast_nonneg _) hρ hL2π
    have ht : (1 + ((2 * n : ℕ) : ℝ)) ^ (-2 : ℝ) ≤ r ^ 2 := by
      have hpos : 0 < 1 + ((2 * n : ℕ) : ℝ) := by positivity
      rw [Real.rpow_neg hpos.le, Real.rpow_two]
      have h3 : r⁻¹ ≤ 1 + ((2 * n : ℕ) : ℝ) := by
        push_cast
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith
      have h4 : (r⁻¹) ^ 2 ≤ (1 + ((2 * n : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (inv_nonneg.2 hr0.le) h3 2
      calc ((1 + ((2 * n : ℕ) : ℝ)) ^ 2)⁻¹ ≤ ((r⁻¹) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) h4
        _ = r ^ 2 := by rw [inv_pow, inv_inv]
    have h2 : K₂ * ((1 + ((2 * n : ℕ) : ℝ)) ^ (-2 : ℝ) + 2 * π / (L * ρ ^ (1 / 2 : ℝ))) ≤
        K₂ * (1 + 2 * π) * r :=
      calc _ ≤ K₂ * (r + 2 * π * r) :=
            mul_le_mul_of_nonneg_left (add_le_add (ht.trans hrr) hΔ) hK₂
        _ = _ := by ring
    have e : Φ * (∑' k, if inPL ρ L k then ft k else 0) =
        (L ^ 3)⁻¹ * ρ ^ (-(3 / 2 : ℝ)) * ∑' k, if inPL ρ L k then
          |ρ * lamPL (g0 V w) ρ (mom L k)| ^ ((2 * n : ℕ) : ℝ) *
            ((ρ * lamPL (g0 V w) ρ (mom L k)) ^ 2 / (1 - (ρ * lamPL (g0 V w) ρ (mom L k)) ^ 2))
          else 0 := by
      rw [hΦ]
      ring
    rw [e]
    linarith
  have hΦ0 : 0 ≤ Φ := by positivity
  have h3r : 0 ≤ 1 - 3 * r := by linarith
  have hE : 0 ≤ (K₁ + K₂) * (1 + 2 * π) * r := by positivity
  have hfin : G - (K₁ + K₂) * (1 + 2 * π) * r ≤
      Φ * (∑' k, if inPL ρ L k then fm k else 0) - Φ * ∑' k, if inPL ρ L k then ft k else 0 := by
    linarith
  calc G - (3 * G + (K₁ + K₂) * (1 + 2 * π)) * r
      ≤ (1 - 3 * r) * (G - (K₁ + K₂) * (1 + 2 * π) * r) := by
        have : 0 ≤ 3 * r * ((K₁ + K₂) * (1 + 2 * π) * r) := by positivity
        nlinarith
    _ ≤ (1 - 3 * r) * (Φ * (∑' k, if inPL ρ L k then fm k else 0) -
          Φ * ∑' k, if inPL ρ L k then ft k else 0) := mul_le_mul_of_nonneg_left hfin h3r
    _ = Φ * ((1 - 3 * r) * ((∑' k, if inPL ρ L k then fm k else 0) -
          ∑' k, if inPL ρ L k then ft k else 0)) := by ring
    _ ≤ Φ * ∑' k, if inPL ρ L k then Q k else 0 := mul_le_mul_of_nonneg_left hsum1 hΦ0

/-- Lemma 5.3 [boundspsi0], (5.12) [boundspsi01], with a rate. -/
theorem Lemma5_3 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      |Expect.Q (trialState V w kc N) [0] / LN N ^ 3 - rho0 (g0 V w) (rhoN N)| ≤
        C * rhoN N ^ (3/2 + 1/400 : ℝ) := by
  obtain ⟨C₃, hC₃, N₃, h32⟩ := Eq5_32 hg
  obtain ⟨C₄, hC₄, N₄, h43⟩ := Eq5_43 hg
  refine ⟨C₃ + C₄, by positivity, max (max N₃ N₄) 1, fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN₃ : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₄ : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set Q : Idx → ℝ := fun k => Expect.Q (trialState V w kc N) [k] with hQ
  have hs : HasSum Q N := Particles_hasSum_Q V w kc hN1
  have hQ0 : ∀ k, 0 ≤ Q k := fun k => Lower_Q_nonneg _ k
  have hsL : Summable fun k => if inPL (rhoN N) (LN N) k then Q k else 0 :=
    Summable.of_nonneg_of_le (fun k => by split_ifs; exacts [hQ0 k, le_rfl])
      (fun k => by split_ifs; exacts [le_rfl, hQ0 k]) hs.summable
  set SL := ∑' k, if inPL (rhoN N) (LN N) k then Q k else 0 with hSL
  -- `Q_Ψ(0) + Σ_{P_L} Q_Ψ ≤ N`, since `0 ∉ P_L`
  have hsum : Q 0 + SL ≤ N := by
    refine hasSum_le (fun k => ?_) ((hasSum_ite_eq (0 : Idx) (Q 0)).add hsL.hasSum) hs
    by_cases hk : k = 0
    · subst hk
      have : ¬ inPL (rhoN N) (LN N) 0 := fun h => Regions_PL_ne_zero hρ h rfl
      simp [this]
    · simp only [hk, ite_false, zero_add]
      split_ifs
      · exact le_rfl
      · exact hQ0 k
  have hL3 : 0 < LN N ^ 3 := by positivity
  have e1 : rhoN N ^ (3 / 2 : ℝ) * rhoN N ^ (-(3 / 2 : ℝ)) = 1 := by
    rw [← Real.rpow_add hρ]
    norm_num
  have e2 : rhoN N ^ (3 / 2 : ℝ) * rhoN N ^ (1 / 400 : ℝ) = rhoN N ^ (3 / 2 + 1 / 400 : ℝ) := by
    rw [← Real.rpow_add hρ]
  have h3 : rhoN N ^ (3 / 2 + 1 / 200 : ℝ) ≤ rhoN N ^ (3 / 2 + 1 / 400 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hp0 : 0 ≤ rhoN N ^ (3 / 2 + 1 / 400 : ℝ) := Real.rpow_nonneg hρ.le _
  have hp1 : 0 ≤ rhoN N ^ (3 / 2 : ℝ) := Real.rpow_nonneg hρ.le _
  set G := g0 V w ^ (3 / 2 : ℝ) / (3 * π ^ 2) with hG
  have hrho0 : rho0 (g0 V w) (rhoN N) = rhoN N - G * rhoN N ^ (3 / 2 : ℝ) := by
    rw [rho0, hG]
    ring
  -- the upper side, from (5.43) [upt01]
  have hup : Expect.Q (trialState V w kc N) [0] / LN N ^ 3 - rho0 (g0 V w) (rhoN N) ≤
      C₄ * rhoN N ^ (3 / 2 + 1 / 400 : ℝ) := by
    have h1 := h43 N hN₄ kc
    have h2 : (LN N ^ 3)⁻¹ * SL = rhoN N ^ (3 / 2 : ℝ) *
        (rhoN N ^ (-(3 / 2 : ℝ)) * (LN N ^ 3)⁻¹ * SL) := by
      rw [← mul_assoc, ← mul_assoc, e1, one_mul]
    have h4 : rhoN N ^ (3 / 2 : ℝ) * (G - C₄ * rhoN N ^ (1 / 400 : ℝ)) ≤ (LN N ^ 3)⁻¹ * SL := by
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 hp1
    have h5 : Expect.Q (trialState V w kc N) [0] / LN N ^ 3 ≤ rhoN N - (LN N ^ 3)⁻¹ * SL := by
      rw [div_le_iff₀ hL3]
      have : (rhoN N - (LN N ^ 3)⁻¹ * SL) * LN N ^ 3 = N - SL := by
        rw [← hNL]
        field_simp
      rw [this]
      have : Expect.Q (trialState V w kc N) [0] = Q 0 := rfl
      linarith
    rw [hrho0, ← e2]
    have : rhoN N ^ (3 / 2 : ℝ) * (G - C₄ * rhoN N ^ (1 / 400 : ℝ)) =
        G * rhoN N ^ (3 / 2 : ℝ) - C₄ * (rhoN N ^ (3 / 2 : ℝ) * rhoN N ^ (1 / 400 : ℝ)) := by ring
    linarith
  -- the lower side, from (5.32) [resultlbpsi0]
  have hlo : -(C₃ * rhoN N ^ (3 / 2 + 1 / 400 : ℝ)) ≤
      Expect.Q (trialState V w kc N) [0] / LN N ^ 3 - rho0 (g0 V w) (rhoN N) := by
    have h1 := h32 N hN₃ kc
    have := mul_le_mul_of_nonneg_left h3 hC₃
    linarith
  rw [abs_le]
  constructor
  · have : 0 ≤ C₄ * rhoN N ^ (3 / 2 + 1 / 400 : ℝ) := mul_nonneg hC₄ hp0
    linarith
  · have : 0 ≤ C₃ * rhoN N ^ (3 / 2 + 1 / 400 : ℝ) := mul_nonneg hC₃ hp0
    linarith

/-- Theorem 5.1 [thmA], (5.2) [boundspsiuPMPHtotal] and (5.3) [boundspsiuPLtotal], with rates
uniform in `k_c`. -/
theorem Thm5_1 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
          (∑' n : Idx, (if inPI (rhoN N) (LN N) n ∨ inPH (rhoN N) (LN N) n then
            Expect.Q (trialState V w kc N) [n] else 0)) ≤ C * rhoN N ^ (1/200 : ℝ) ∧
      |rhoN N ^ (-(3/2 : ℝ)) * (LN N ^ 3)⁻¹ *
          (∑' n : Idx, (if inPL (rhoN N) (LN N) n then
            Expect.Q (trialState V w kc N) [n] else 0))
        - g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2)| ≤ C * rhoN N ^ (1/400 : ℝ) := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Prop5_4_PI V w
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := Prop5_4_PH V w
  obtain ⟨C₅, hC₅, N₅, h₅⟩ := Prop5_4_PL hg
  obtain ⟨C₄, hC₄, N₄, h₄⟩ := Eq5_43 hg
  refine ⟨C₁ + C₂ + C₄ + C₅, by positivity,
    max (max (max (max N₁ N₂) N₄) N₅) 1, fun N hN kc => ⟨?_, ?_⟩⟩
  all_goals
    have hN1 : 1 ≤ N := le_of_max_le_right hN
    have hN' : max (max (max N₁ N₂) N₄) N₅ ≤ N := le_of_max_le_left hN
    have hN₁ : N₁ ≤ N := by omega
    have hN₂ : N₂ ≤ N := by omega
    have hN₄ : N₄ ≤ N := by omega
    have hN₅ : N₅ ≤ N := by omega
    obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
    have hm0 : 0 ≤ rhoN N ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hρ.le _
    have hp200 : 0 ≤ rhoN N ^ (1 / 200 : ℝ) := Real.rpow_nonneg hρ.le _
    have hp400 : 0 ≤ rhoN N ^ (1 / 400 : ℝ) := Real.rpow_nonneg hρ.le _
    have h200 : rhoN N ^ (1 / 200 : ℝ) ≤ rhoN N ^ (1 / 400 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  · -- (5.2) [boundspsiuPMPHtotal]
    set Q : Idx → ℝ := fun k => Expect.Q (trialState V w kc N) [k] with hQ
    have hQs : Summable Q := (Particles_hasSum_Q V w kc hN1).summable
    have hQ0 : ∀ k, 0 ≤ Q k := fun k => Lower_Q_nonneg _ k
    have hsP : ∀ P : Idx → Prop, Summable fun k => if P k then Q k else 0 := fun P =>
      Summable.of_nonneg_of_le (fun k => by split_ifs; exacts [hQ0 k, le_rfl])
        (fun k => by split_ifs; exacts [le_rfl, hQ0 k]) hQs
    have hsplit : (∑' k, if inPI (rhoN N) (LN N) k ∨ inPH (rhoN N) (LN N) k then Q k else 0) =
        (∑' k, if inPI (rhoN N) (LN N) k then Q k else 0) +
          ∑' k, if inPH (rhoN N) (LN N) k then Q k else 0 := by
      rw [← (hsP _).tsum_add (hsP _)]
      refine tsum_congr fun k => ?_
      by_cases hI : inPI (rhoN N) (LN N) k
      · have hH : ¬ inPH (rhoN N) (LN N) k := Regions_PI_PH hI
        simp [hI, hH]
      · by_cases hH : inPH (rhoN N) (LN N) k
        · simp [hI, hH]
        · simp [hI, hH]
    change rhoN N ^ (-(3 / 2 : ℝ)) * (LN N ^ 3)⁻¹ *
      (∑' k, if inPI (rhoN N) (LN N) k ∨ inPH (rhoN N) (LN N) k then Q k else 0) ≤ _
    rw [hsplit]
    have hI := h₁ N hN₁ kc
    have hH := h₂ N hN₂ kc
    have e1 : rhoN N ^ (-(3 / 2 : ℝ)) * rhoN N ^ (3 / 2 + 1 / 200 : ℝ) =
        rhoN N ^ (1 / 200 : ℝ) := by
      rw [← Real.rpow_add hρ]
      norm_num
    have e2 : rhoN N ^ (-(3 / 2 : ℝ)) * rhoN N ^ (2 - 1 / 200 : ℝ) =
        rhoN N ^ (1 / 2 - 1 / 200 : ℝ) := by
      rw [← Real.rpow_add hρ]
      norm_num
    have h3 : rhoN N ^ (1 / 2 - 1 / 200 : ℝ) ≤ rhoN N ^ (1 / 200 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
    have hI' := mul_le_mul_of_nonneg_left hI hm0
    have hH' := mul_le_mul_of_nonneg_left hH hm0
    have hC2 := mul_le_mul_of_nonneg_left h3 hC₂
    have e3 : rhoN N ^ (-(3 / 2 : ℝ)) * (LN N ^ 3)⁻¹ *
        ((∑' k, if inPI (rhoN N) (LN N) k then Q k else 0) +
          ∑' k, if inPH (rhoN N) (LN N) k then Q k else 0) =
        rhoN N ^ (-(3 / 2 : ℝ)) * ((LN N ^ 3)⁻¹ *
          ∑' k, if inPI (rhoN N) (LN N) k then Q k else 0) +
        rhoN N ^ (-(3 / 2 : ℝ)) * ((LN N ^ 3)⁻¹ *
          ∑' k, if inPH (rhoN N) (LN N) k then Q k else 0) := by ring
    have e4 : rhoN N ^ (-(3 / 2 : ℝ)) * (C₁ * rhoN N ^ (3 / 2 + 1 / 200 : ℝ)) =
        C₁ * rhoN N ^ (1 / 200 : ℝ) := by rw [← e1]; ring
    have e5 : rhoN N ^ (-(3 / 2 : ℝ)) * (C₂ * rhoN N ^ (2 - 1 / 200 : ℝ)) =
        C₂ * rhoN N ^ (1 / 2 - 1 / 200 : ℝ) := by rw [← e2]; ring
    have h6 : 0 ≤ (C₄ + C₅) * rhoN N ^ (1 / 200 : ℝ) := by positivity
    rw [e3]
    rw [e4] at hI'
    rw [e5] at hH'
    nlinarith
  · -- (5.3) [boundspsiuPLtotal]
    have hlo := h₄ N hN₄ kc
    have hhi := mul_le_mul_of_nonneg_left (h₅ N hN₅ kc) hm0
    have e1 : rhoN N ^ (-(3 / 2 : ℝ)) * rhoN N ^ (3 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hρ]
      norm_num
    have e2 : rhoN N ^ (-(3 / 2 : ℝ)) * ((g0 V w ^ (3 / 2 : ℝ) / (3 * π ^ 2) +
        C₅ * rhoN N ^ (1 / 200 : ℝ)) * rhoN N ^ (3 / 2 : ℝ)) =
        g0 V w ^ (3 / 2 : ℝ) / (3 * π ^ 2) + C₅ * rhoN N ^ (1 / 200 : ℝ) := by
      calc _ = (g0 V w ^ (3 / 2 : ℝ) / (3 * π ^ 2) + C₅ * rhoN N ^ (1 / 200 : ℝ)) *
            (rhoN N ^ (-(3 / 2 : ℝ)) * rhoN N ^ (3 / 2 : ℝ)) := by ring
        _ = _ := by rw [e1, mul_one]
    rw [e2, ← mul_assoc] at hhi
    have hC5 := mul_le_mul_of_nonneg_left h200 hC₅
    rw [abs_le]
    constructor
    · have : 0 ≤ (C₁ + C₂ + C₅) * rhoN N ^ (1 / 400 : ℝ) := by positivity
      nlinarith
    · have : 0 ≤ (C₁ + C₂ + C₄) * rhoN N ^ (1 / 400 : ℝ) := by positivity
      nlinarith

end LHYUpper
