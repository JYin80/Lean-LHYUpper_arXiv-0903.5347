import LHYUpper.Particles.Totals

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Elementary facts on nonnegative series, on `Ψ` and on the parameters -/

/-- A restriction of a nonnegative summable family is summable. -/
private lemma Prop55_summable_ite {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (p : Occ → Prop) [DecidablePred p] : Summable fun α => if p α then ψ α else 0 :=
  Summable.of_nonneg_of_le (fun α => by split_ifs <;> simp [hψ α])
    (fun α => by split_ifs <;> simp [hψ α]) hs

/-- Union bound for restricted sums: if every `α` with `ψ α ≠ 0` in the event `P` lies in one of
`P₁`, `P₂`, `P₃`, then the `P`-sum is at most the sum of the three restricted sums. -/
private lemma Prop55_union {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (P P₁ P₂ P₃ : Occ → Prop) [DecidablePred P] [DecidablePred P₁] [DecidablePred P₂]
    [DecidablePred P₃] (h : ∀ α, P α → ψ α ≠ 0 → P₁ α ∨ P₂ α ∨ P₃ α) :
    (∑' α, if P α then ψ α else 0) ≤
      (∑' α, if P₁ α then ψ α else 0) + (∑' α, if P₂ α then ψ α else 0) +
        ∑' α, if P₃ α then ψ α else 0 := by
  have h1 := Prop55_summable_ite hs hψ P₁
  have h2 := Prop55_summable_ite hs hψ P₂
  have h3 := Prop55_summable_ite hs hψ P₃
  rw [← h1.tsum_add h2, ← (h1.add h2).tsum_add h3]
  refine (Prop55_summable_ite hs hψ P).tsum_le_tsum (fun α => ?_) ((h1.add h2).add h3)
  have a1 : 0 ≤ (if P₁ α then ψ α else 0) := by split_ifs <;> simp [hψ α]
  have a2 : 0 ≤ (if P₂ α then ψ α else 0) := by split_ifs <;> simp [hψ α]
  have a3 : 0 ≤ (if P₃ α then ψ α else 0) := by split_ifs <;> simp [hψ α]
  by_cases hP : P α
  · rw [ite_eq_left hP]
    by_cases hz : ψ α = 0
    · rw [hz]
      simp
    · rcases h α hP hz with h' | h' | h'
      · rw [ite_eq_left h']
        linarith
      · rw [ite_eq_left h']
        linarith
      · rw [ite_eq_left h']
        linarith
  · rw [ite_eq_right hP]
    linarith

/-- Monotonicity of restricted sums in the restricting event. -/
private lemma Prop55_tsum_mono {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    {P Q : Occ → Prop} [DecidablePred P] [DecidablePred Q] (h : ∀ α, P α → Q α) :
    (∑' α, if P α then ψ α else 0) ≤ ∑' α, if Q α then ψ α else 0 :=
  (Prop55_summable_ite hs hψ P).tsum_le_tsum
    (fun α => by
      by_cases hp : P α
      · simp [hp, h α hp]
      · simp only [hp, ite_false]
        split_ifs <;> simp [hψ α])
    (Prop55_summable_ite hs hψ Q)

/-- `|Ψ|²` vanishes off `M`. -/
private lemma Prop55_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  rw [FIdentities_trialState, ite_eq_right hc, norm_zero]
  norm_num

/-- `Q_Ψ({u, m})` as a restricted sum. -/
private lemma Prop55_Qm_single (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) :
    Expect.Qm Ψ [(u, m)] = ∑' α : Occ, if α u = m then ‖Ψ α‖ ^ 2 else 0 := by
  simp [Expect.Qm, Expect.Ev]

/-- `Q_Ψ({u, m}) ≥ 0`. -/
private lemma Prop55_Qm_nonneg (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) : 0 ≤ Expect.Qm Ψ [(u, m)] := by
  rw [Prop55_Qm_single]
  exact tsum_nonneg fun α => by split_ifs <;> positivity

/-- `Q_Ψ({u, m}) = 0` for `m > ⌈m_c⌉` and `u ∈ P_L`, by `α*(u) ≤ ⌈m_c⌉`, (3.8) [defmc]. -/
private lemma Prop55_Qm_zero (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) {m : ℕ} (hm : ⌈mc (rhoN N)⌉₊ < m) :
    Expect.Qm (trialState V w kc N) [(u, m)] = 0 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  rw [Prop55_Qm_single]
  refine (tsum_congr fun α => ?_).trans tsum_zero
  by_cases h : α u = m
  · by_cases hz : ‖trialState V w kc N α‖ ^ 2 = 0
    · rw [hz]
      simp
    · exfalso
      have h1 := MStar_PL_ceil hρ (Prop55_inM hz) hu
      have h2 : α u ≤ alphaStar α u := le_max_left _ _
      omega
  · simp [h]

/-- A single occupation number is at most the particle number. -/
private lemma Prop55_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]
    exact Nat.zero_le _

/-- `α ↦ α(u) |Ψ(α)|²` is summable. -/
private lemma Prop55_summable_occ (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    Summable fun α : Occ => (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by
  have hΨ := Normalization_isNState V w kc hN
  refine Summable.of_nonneg_of_le (fun α => by positivity) (fun α => ?_)
    (hΨ.1.summable.mul_left (N : ℝ))
  by_cases hz : trialState V w kc N α = 0
  · simp [hz]
  · have hnum := hΨ.2 α hz
    have h1 : (α u : ℝ) ≤ N := by
      rw [← hnum]
      exact_mod_cast Prop55_occ_le_num α u
    exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- `ρ_N^a → 0` for `a > 0`. -/
private lemma Prop55_rho_pow_tendsto {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have hT : Tendsto rhoN atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := 8 / 17) (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h := (Real.continuousAt_rpow_const (0 : ℝ) a (Or.inr ha.le)).tendsto
  rw [Real.zero_rpow ha.ne'] at h
  exact h.comp hT

/-- `ρ m_c / ε_H = ρ^{99/100}` for `m_c = ρ^{-1/200}`, `ε_H = ρ^{1/200}`. -/
private lemma Prop55_rho_mc_eps {ρ : ℝ} (hρ : 0 < ρ) :
    ρ * mc ρ / epsP ρ = ρ ^ (99 / 100 : ℝ) := by
  unfold mc epsP
  rw [div_eq_iff (Real.rpow_pos_of_pos hρ _).ne']
  have e1 : ρ * ρ ^ (-(1 / 200 : ℝ)) = ρ ^ (199 / 200 : ℝ) := by
    calc ρ * ρ ^ (-(1 / 200 : ℝ)) = ρ ^ (1 : ℝ) * ρ ^ (-(1 / 200 : ℝ)) := by
          rw [Real.rpow_one]
      _ = ρ ^ ((1 : ℝ) + -(1 / 200 : ℝ)) := (Real.rpow_add hρ _ _).symm
      _ = ρ ^ (199 / 200 : ℝ) := by norm_num
  rw [e1, ← Real.rpow_add hρ]
  norm_num

/-- `ρ^{1 + a} = ρ · ρ^a`. -/
private lemma Prop55_rpow_one_add {ρ : ℝ} (hρ : 0 < ρ) (a : ℝ) : ρ ^ (1 + a) = ρ * ρ ^ a := by
  rw [Real.rpow_add hρ, Real.rpow_one]

/-- Finite antitone averages: for antitone `a` and `k ≤ M`,
`(k + 1) Σ_{i ≤ M} a_i ≤ (M + 1) Σ_{i ≤ k} a_i`. -/
private lemma Prop55_antitone_avg {a : ℕ → ℝ} (ha : Antitone a) {k M : ℕ} (hk : k ≤ M) :
    ((k : ℝ) + 1) * ∑ i ∈ Finset.range (M + 1), a i ≤
      ((M : ℝ) + 1) * ∑ i ∈ Finset.range (k + 1), a i := by
  induction M, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ M hkM ih =>
    have h1 : ((k : ℝ) + 1) * a k ≤ ∑ i ∈ Finset.range (k + 1), a i := by
      have := Finset.sum_le_sum (s := Finset.range (k + 1)) (f := fun _ => a k) (g := a)
        (fun i hi => ha (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))
      simpa using this
    have h2 : a (M + 1) ≤ a k := ha (by omega)
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
    rw [Finset.sum_range_succ _ (M + 1)]
    push_cast
    nlinarith

/-- `Σ_{i ≤ k} Σ_α [α(u) = i] f(α) = Σ_α [α(u) ≤ k] f(α)` for a summable family `f`. -/
private lemma Prop55_fibre_sum {f : Occ → ℝ} (hs : Summable f) (hf : ∀ α, 0 ≤ f α) (u : Idx)
    (k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), (∑' α : Occ, if α u = i then f α else 0) =
      ∑' α : Occ, if α u ≤ k then f α else 0 := by
  rw [← Summable.tsum_finsetSum (fun i _ => Prop55_summable_ite hs hf (fun α => α u = i))]
  refine tsum_congr fun α => ?_
  have : (∑ i ∈ Finset.range (k + 1), if α u = i then f α else 0) =
      if α u ∈ Finset.range (k + 1) then f α else 0 :=
    Finset.sum_ite_eq (Finset.range (k + 1)) (α u) (fun _ => f α)
  rw [this]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- `Q_Ψ(0 | {u, i}) Q_Ψ({u, i}) = Σ_{α(u) = i} α(0) |Ψ(α)|²`, also when `Q_Ψ({u, i}) = 0`. -/
private lemma Prop55_Qc_mul_Qm (Ψ : Occ → ℂ) (hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2) (u : Idx)
    (i : ℕ) :
    Expect.Qc Ψ [0] [(u, i)] * Expect.Qm Ψ [(u, i)] =
      ∑' α : Occ, if α u = i then (α 0 : ℝ) * ‖Ψ α‖ ^ 2 else 0 := by
  have hQ : Expect.Qc Ψ [0] [(u, i)] * Expect.Qm Ψ [(u, i)] =
      (∑' α : Occ, if α u = i then (α 0 : ℝ) * ‖Ψ α‖ ^ 2 else 0) / Expect.Qm Ψ [(u, i)] *
        Expect.Qm Ψ [(u, i)] := by
    simp [Expect.Qc, Expect.Ev]
  rw [hQ]
  by_cases h0 : Expect.Qm Ψ [(u, i)] = 0
  · rw [h0, mul_zero]
    symm
    rw [Prop55_Qm_single] at h0
    have hsm := Prop55_summable_ite hs (fun α => by positivity) (fun α => α u = i)
    have hz := congrFun ((hasSum_zero_iff_of_nonneg
      (fun α => by split_ifs <;> positivity)).1 (h0 ▸ hsm.hasSum)) 
    refine (tsum_congr fun α => ?_).trans tsum_zero
    have := hz α
    by_cases hα : α u = i
    · simp only [hα, ite_true, Pi.zero_apply] at this ⊢
      rw [this, mul_zero]
    · simp [hα]
  · exact div_mul_cancel₀ _ h0

/-! ### The pinned statements -/

/-- (5.45) [mcmlbum0]: on `P_L`, `Q_Ψ({u, m + 1}) ≤ (ρλ_u)²(1 + Cρm_c/ε_H) Q_Ψ({u, m})
≤ Q_Ψ({u, m})`. -/
theorem Eq5_45 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      ∀ m : ℕ,
      Expect.Qm (trialState V w kc N) [(u, m + 1)] ≤
          (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
            (1 + C * rhoN N * mc (rhoN N) / epsP (rhoN N)) *
            Expect.Qm (trialState V w kc N) [(u, m)] ∧
        Expect.Qm (trialState V w kc N) [(u, m + 1)] ≤
          Expect.Qm (trialState V w kc N) [(u, m)] := by
  obtain ⟨C₂, hC₂, N₁, h22⟩ := Eq5_22 V w
  have hs0 : 0 < 1 + Real.sqrt (g0 V w) := by
    have := Real.sqrt_nonneg (g0 V w)
    linarith
  have hev : ∀ᶠ N : ℕ in atTop,
      (5 * C₂ * (1 + Real.sqrt (g0 V w))) * rhoN N ^ (197 / 200 : ℝ) ≤ 1 := by
    have h := (Prop55_rho_pow_tendsto (a := 197 / 200) (by norm_num)).const_mul
      (5 * C₂ * (1 + Real.sqrt (g0 V w)))
    rw [mul_zero] at h
    exact h.eventually (ge_mem_nhds (by norm_num))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hev
  refine ⟨5 * C₂, by linarith, max (max N₁ N₂) 1, fun N hN kc u hu m => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂' : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  have hψs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ0 : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  obtain ⟨hlam0, hlam1⟩ := Particles_rho_lam_PL hg hρ hρ1 hu
  have hε0 : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP (rhoN N) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hmc0 : 0 < mc (rhoN N) := Real.rpow_pos_of_pos hρ _
  have hmc1 : 1 ≤ mc (rhoN N) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  -- the factor `t = Cρm_c/ε_H = C ρ^{99/100}` is below `ε_H/(1 + √g₀)`
  have ht : 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N) = 5 * C₂ * rhoN N ^ (99 / 100 : ℝ) := by
    rw [mul_assoc (5 * C₂), mul_div_assoc, Prop55_rho_mc_eps hρ]
  have ht0 : 0 ≤ 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N) := by positivity
  have hte : 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N) ≤
      epsP (rhoN N) / (1 + Real.sqrt (g0 V w)) := by
    rw [le_div_iff₀ hs0, ht]
    have h1 := hN₂ N hN₂'
    have h2 : rhoN N ^ (99 / 100 : ℝ) = rhoN N ^ (197 / 200 : ℝ) * rhoN N ^ (1 / 200 : ℝ) := by
      rw [← Real.rpow_add hρ]
      norm_num
    have h3 : 0 ≤ rhoN N ^ (1 / 200 : ℝ) := Real.rpow_nonneg hρ.le _
    have h4 := mul_le_mul_of_nonneg_right h1 h3
    unfold epsP
    rw [h2]
    nlinarith
  -- monotonicity `x_u (1 + t) ≤ 1`
  have he0 : 0 < epsP (rhoN N) / (1 + Real.sqrt (g0 V w)) := by positivity
  have he1 : epsP (rhoN N) / (1 + Real.sqrt (g0 V w)) ≤ 1 :=
    (div_le_self hε0.le (by linarith [Real.sqrt_nonneg (g0 V w)])).trans hε1
  have hx2 : (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 ≤
      (1 - epsP (rhoN N) / (1 + Real.sqrt (g0 V w))) ^ 2 := by
    have h1 : -(rhoN N * lam V w (rhoN N) (LN N) u) ≤
        1 - epsP (rhoN N) / (1 + Real.sqrt (g0 V w)) := by linarith
    calc (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 = (-(rhoN N * lam V w (rhoN N) (LN N) u)) ^ 2 :=
          (neg_sq _).symm
      _ ≤ _ := pow_le_pow_left₀ (by linarith) h1 2
  have hx : (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
      (1 + 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N)) ≤ 1 := by
    set e := epsP (rhoN N) / (1 + Real.sqrt (g0 V w)) with he
    set t := 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N) with ht'
    calc (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 * (1 + t) ≤ (1 - e) ^ 2 * (1 + t) :=
          mul_le_mul_of_nonneg_right hx2 (by linarith)
      _ ≤ (1 - e) * (1 + t) :=
          mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (sub_nonneg.2 he1) he0.le])
            (by linarith)
      _ ≤ 1 := by nlinarith [mul_nonneg he0.le ht0]
  have hx0 : 0 ≤ (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 := sq_nonneg _
  have hx1 : (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx0 ht0]
  -- the two conjuncts
  have hQ0 : ∀ j : ℕ, 0 ≤ Expect.Qm (trialState V w kc N) [(u, j)] :=
    fun j => Prop55_Qm_nonneg _ u j
  have key : Expect.Qm (trialState V w kc N) [(u, m + 1)] ≤
      (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
        (1 + 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N)) *
        Expect.Qm (trialState V w kc N) [(u, m)] := by
    by_cases hm : m + 1 ≤ ⌈mc (rhoN N)⌉₊
    · -- `Q_Ψ({u, m + 1}) = S_{m+1} + A_{m+1}` with `A_{m+1}` bounded by (5.22)
      have hmlt : (m : ℝ) < mc (rhoN N) := by
        have h1 : ((m + 1 : ℕ) : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := by exact_mod_cast hm
        have h2 := Nat.ceil_lt_add_one hmc0.le
        push_cast at h1
        linarith
      set S : ℕ → ℝ := fun j => ∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = j then
          ‖trialState V w kc N β‖ ^ 2 else 0 with hS
      have hS0 : ∀ j, 0 ≤ S j := fun j => tsum_nonneg fun β => by split_ifs <;> positivity
      have hunion := Prop55_union hψs hψ0 (fun α => α u = m + 1)
        (fun α => InMuS (rhoN N) (LN N) kc N u α ∧ α u = m + 1)
        (fun α => InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m + 1)
        (fun α => InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m + 1 + 1)
        (fun α hα hz => by
          have hM := Prop55_inM hz
          by_cases hs : α u = α (-u)
          · exact Or.inl ⟨⟨hM, hs⟩, hα⟩
          · rcases MStar_PL_star hρ hM hu with h | h
            · exact Or.inr (Or.inl ⟨⟨hM, hs⟩, by omega⟩)
            · exact Or.inr (Or.inr ⟨⟨hM, hs⟩, by omega⟩))
      have hA1 := h22 N hN₁ kc u hu (m + 1)
      have hA2 := h22 N hN₁ kc u hu (m + 1 + 1)
      have hSS : S (m + 1 + 1) ≤ (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 * S (m + 1) :=
        Eq5_26 V w kc hN1 hu (m + 1)
      have hSm : S (m + 1) ≤ (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 * S m :=
        Eq5_26 V w kc hN1 hu m
      have hSQ : S m ≤ Expect.Qm (trialState V w kc N) [(u, m)] := by
        rw [Prop55_Qm_single]
        exact Prop55_tsum_mono hψs hψ0 (fun α hα => hα.2)
      rw [Prop55_Qm_single (trialState V w kc N) u (m + 1)]
      have hmain : (∑' α : Occ, if α u = m + 1 then ‖trialState V w kc N α‖ ^ 2 else 0) ≤
          S (m + 1) + 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N) * S (m + 1) := by
        refine hunion.trans ?_
        set a := C₂ * rhoN N / epsP (rhoN N) with ha
        have ha0 : 0 ≤ a := by positivity
        have e1 : C₂ * rhoN N * ((m + 1 : ℕ) : ℝ) / epsP (rhoN N) = a * ((m : ℝ) + 1) := by
          push_cast
          ring
        have e2 : C₂ * rhoN N * ((m + 1 + 1 : ℕ) : ℝ) / epsP (rhoN N) = a * ((m : ℝ) + 2) := by
          push_cast
          ring
        have e3 : 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N) = 5 * a * mc (rhoN N) := by
          ring
        rw [e1] at hA1
        rw [e2] at hA2
        rw [e3]
        have hS1 := hS0 (m + 1)
        have h5 : a * ((m : ℝ) + 2) * S (m + 1 + 1) ≤ a * ((m : ℝ) + 2) * S (m + 1) := by
          refine mul_le_mul_of_nonneg_left (hSS.trans ?_) (by positivity)
          nlinarith
        have h6 : (2 * (m : ℝ) + 3) ≤ 5 * mc (rhoN N) := by linarith
        have h7 := mul_le_mul_of_nonneg_left h6 (mul_nonneg ha0 hS1)
        nlinarith
      calc _ ≤ S (m + 1) + 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N) * S (m + 1) := hmain
        _ = (1 + 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N)) * S (m + 1) := by ring
        _ ≤ (1 + 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N)) *
              ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 * S m) :=
            mul_le_mul_of_nonneg_left hSm (by linarith)
        _ ≤ (1 + 5 * C₂ * rhoN N * mc (rhoN N) / epsP (rhoN N)) *
              ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
                Expect.Qm (trialState V w kc N) [(u, m)]) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSQ hx0) (by linarith)
        _ = _ := by ring
    · rw [Prop55_Qm_zero V w kc hN1 hu (by omega : ⌈mc (rhoN N)⌉₊ < m + 1)]
      exact mul_nonneg (mul_nonneg hx0 (by linarith)) (hQ0 m)
  refine ⟨key, key.trans ?_⟩
  calc _ ≤ 1 * Expect.Qm (trialState V w kc N) [(u, m)] :=
        mul_le_mul_of_nonneg_right hx (hQ0 m)
    _ = _ := one_mul _

/-- (5.46) [mcmlbum1], with `⌈m_c⌉` in place of `m_c`. -/
theorem Eq5_46 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      ∀ k : ℕ, k ≤ ⌈mc (rhoN N)⌉₊ →
      ((k : ℝ) + 1) / ((⌈mc (rhoN N)⌉₊ : ℝ) + 1) ≤
        ∑ i ∈ Finset.range (k + 1), Expect.Qm (trialState V w kc N) [(u, i)] := by
  obtain ⟨C, -, N₁, h45⟩ := Eq5_45 hg
  refine ⟨max N₁ 1, fun N hN kc u hu k hk => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hΨ := Normalization_isNState V w kc hN1
  set M := ⌈mc (rhoN N)⌉₊ with hM
  have hanti : Antitone fun i : ℕ => Expect.Qm (trialState V w kc N) [(u, i)] :=
    antitone_nat_of_succ_le fun i => (h45 N hN₁ kc u hu i).2
  have hsum : ∑ i ∈ Finset.range (M + 1), Expect.Qm (trialState V w kc N) [(u, i)] = 1 := by
    rw [← Expect.tsum_Qm_single N _ hΨ u]
    exact (tsum_eq_sum (s := Finset.range (M + 1)) fun i hi =>
      Prop55_Qm_zero V w kc hN1 hu (by simpa using hi)).symm
  have key := Prop55_antitone_avg hanti hk
  rw [hsum] at key
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- Proposition 5.5 [prop6], (5.44) [temp6.42], for `u ∈ P_L` and `0 ≤ k ≤ ⌈m_c⌉`. -/
theorem Prop5_5 {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPL (rhoN N) (LN N) u →
      ∀ k : ℕ, k ≤ ⌈mc (rhoN N)⌉₊ →
      (N : ℝ) - C * N * rhoN N ^ (1/2 : ℝ) * mc (rhoN N) ≤
        (∑ i ∈ Finset.range (k + 1), Expect.Qc (trialState V w kc N) [0] [(u, i)] *
            Expect.Qm (trialState V w kc N) [(u, i)]) /
          ∑ i ∈ Finset.range (k + 1), Expect.Qm (trialState V w kc N) [(u, i)] := by
  obtain ⟨C₃, hC₃, N₃, h32⟩ := Eq5_32 hg
  obtain ⟨N₄, h46⟩ := Eq5_46 hg
  set K : ℝ := (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) + C₃ with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨3 * K, by positivity, max (max N₃ N₄) 1, fun N hN kc u hu k hk => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₃ : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₄ : N₄ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  have hψs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hψ0 : ∀ α : Occ, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  have hmc1 : 1 ≤ mc (rhoN N) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hr0 : 0 < rhoN N ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  -- the numerator and the denominator as sums over the event `α(u) ≤ k`
  have hnum : ∑ i ∈ Finset.range (k + 1), Expect.Qc (trialState V w kc N) [0] [(u, i)] *
        Expect.Qm (trialState V w kc N) [(u, i)] =
      ∑' α : Occ, if α u ≤ k then (α 0 : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0 := by
    simp_rw [Prop55_Qc_mul_Qm _ hψs]
    exact Prop55_fibre_sum (Prop55_summable_occ V w kc hN1 0) (fun α => by positivity) u k
  have hden : ∑ i ∈ Finset.range (k + 1), Expect.Qm (trialState V w kc N) [(u, i)] =
      ∑' α : Occ, if α u ≤ k then ‖trialState V w kc N α‖ ^ 2 else 0 := by
    simp_rw [Prop55_Qm_single]
    exact Prop55_fibre_sum hψs hψ0 u k
  rw [hnum, hden]
  set D := ∑' α : Occ, if α u ≤ k then ‖trialState V w kc N α‖ ^ 2 else 0 with hD
  set Num := ∑' α : Occ, if α u ≤ k then (α 0 : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0
    with hNum
  have hDge : ((k : ℝ) + 1) / ((⌈mc (rhoN N)⌉₊ : ℝ) + 1) ≤ D := by
    have := h46 N hN₄ kc u hu k hk
    rwa [hden] at this
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hDge
  -- Proposition 5.5 [prop6] in event form
  have hev : (N : ℝ) * D - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) ≤ Num := by
    have := Prop5_5_event V w kc hN1 (fun α => α u ≤ k)
    convert this using 4
    funext α
    congr
  -- `N - Q_Ψ(0) ≤ K N ρ^{1/2}` by (5.32) [resultlbpsi0]
  have hQ0 : (N : ℝ) - Expect.Q (trialState V w kc N) [0] ≤ K * N * rhoN N ^ (1 / 2 : ℝ) := by
    have h := h32 N hN₃ kc
    rw [le_div_iff₀ (by positivity : 0 < LN N ^ 3)] at h
    have h1 : rhoN N ^ (3 / 2 : ℝ) = rhoN N * rhoN N ^ (1 / 2 : ℝ) := by
      rw [← Prop55_rpow_one_add hρ]
      norm_num
    have h2 : rhoN N ^ (3 / 2 + 1 / 200 : ℝ) = rhoN N * rhoN N ^ (1 / 2 + 1 / 200 : ℝ) := by
      rw [← Prop55_rpow_one_add hρ]
      norm_num
    have h3 : rhoN N ^ (1 / 2 + 1 / 200 : ℝ) ≤ rhoN N ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
    have hA : (rho0 (g0 V w) (rhoN N) - C₃ * rhoN N ^ (3 / 2 + 1 / 200 : ℝ)) * LN N ^ 3 =
        (N : ℝ) - (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) * rhoN N ^ (1 / 2 : ℝ) * N -
          C₃ * rhoN N ^ (1 / 2 + 1 / 200 : ℝ) * N := by
      rw [rho0, h1, h2]
      linear_combination (1 - (3 * π ^ 2)⁻¹ * g0 V w ^ (3 / 2 : ℝ) * rhoN N ^ (1 / 2 : ℝ) -
        C₃ * rhoN N ^ (1 / 2 + 1 / 200 : ℝ)) * hNL
    rw [hA] at h
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C₃ * (N : ℝ))
    rw [hK]
    nlinarith
  -- the average over `α(u) ≤ k`
  have hceil : (⌈mc (rhoN N)⌉₊ : ℝ) + 1 ≤ 3 * mc (rhoN N) := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ mc (rhoN N))
    linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hM1 : (0 : ℝ) < (⌈mc (rhoN N)⌉₊ : ℝ) + 1 := by positivity
  have hq : ((⌈mc (rhoN N)⌉₊ : ℝ) + 1) / ((k : ℝ) + 1) ≤ 3 * mc (rhoN N) :=
    (div_le_self hM1.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).trans hceil
  have hb1 : (N : ℝ) - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) / D ≤ Num / D := by
    rw [le_div_iff₀ hDpos]
    have : ((N : ℝ) - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) / D) * D =
        (N : ℝ) * D - ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) := by
      field_simp
    linarith
  have hb2 : ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) / D ≤
      K * N * rhoN N ^ (1 / 2 : ℝ) * (3 * mc (rhoN N)) := by
    calc ((N : ℝ) - Expect.Q (trialState V w kc N) [0]) / D
        ≤ K * N * rhoN N ^ (1 / 2 : ℝ) / D := div_le_div_of_nonneg_right hQ0 hDpos.le
      _ ≤ K * N * rhoN N ^ (1 / 2 : ℝ) /
            (((k : ℝ) + 1) / ((⌈mc (rhoN N)⌉₊ : ℝ) + 1)) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hDge
      _ = K * N * rhoN N ^ (1 / 2 : ℝ) *
            (((⌈mc (rhoN N)⌉₊ : ℝ) + 1) / ((k : ℝ) + 1)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
  have : 3 * K * (N : ℝ) * rhoN N ^ (1 / 2 : ℝ) * mc (rhoN N) =
      K * N * rhoN N ^ (1 / 2 : ℝ) * (3 * mc (rhoN N)) := by ring
  linarith

end LHYUpper
