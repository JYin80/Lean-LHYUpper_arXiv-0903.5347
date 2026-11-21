module

public import LHYUpper.TrialState.Reorder

@[expose] public section

/-!
# Proposition 11.1 [propchi]

Every `χ ∈ M` (Definition 3.4 [M]) is a symmetric `α ∈ M` that vanishes on `P_{H,c}`
((8.1) [defPHc]), followed by strict pair creations in `P_{H,c}` and soft pair creations at
pairwise non-opposite momenta of `P_L`: a product of the operations `𝓐_{q,q'}` of (11.5)
[elementform2].
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

section Chi
variable {ρ L kc : ℝ} {N : ℕ}

/-- `𝓐_{q,q'}` of (11.5) [elementform2]: `a†_q a†_{q'} a_{q+q'} a_0`. -/
def Chi_pairOp (q q' : Idx) (β : Occ) : Occ :=
  if q + q' = 0 then strictPair q β else softPair (q + q') q q' β

/-- A product of operations `𝓐_{q,q'}`, the last one of the list applied first. -/
def Chi_ops (ops : List (Idx × Idx)) (α : Occ) : Occ :=
  ops.foldr (fun o β => Chi_pairOp o.1 o.2 β) α

private lemma Chi_ops_cons (o : Idx × Idx) (ops : List (Idx × Idx)) (α : Occ) :
    Chi_ops (o :: ops) α = Chi_pairOp o.1 o.2 (Chi_ops ops α) := rfl

private lemma Chi_norm_mom_neg (L : ℝ) (n : Idx) : ‖mom L (-n)‖ = ‖mom L n‖ := by
  have : mom L (-n) = -mom L n := by
    ext i
    simp [mom]
  rw [this, norm_neg]

private lemma Chi_PHc_neg {n : Idx} : inPHc ρ L kc (-n) ↔ inPHc ρ L kc n := by
  unfold inPHc
  rw [Regions_PH_neg, Chi_norm_mom_neg]

/-- The number of particles that `𝓐_{o.1,o.2}` removes at `n`. -/
private def Chi_d (o : Idx × Idx) (n : Idx) : ℕ :=
  if o.1 + o.2 = 0 then (if n = 0 then 2 else 0)
  else (if n = 0 then 1 else 0) + (if n = o.1 + o.2 then 1 else 0)

/-- The number of particles that the product `Chi_ops ops` removes at `n`. -/
private def Chi_D (ops : List (Idx × Idx)) (n : Idx) : ℕ := (ops.map (fun o => Chi_d o n)).sum

/-- The number of zero-momentum particles that the product `Chi_ops ops` removes. -/
private def Chi_W (ops : List (Idx × Idx)) : ℕ :=
  (ops.map (fun o => if o.1 + o.2 = 0 then 2 else 1)).sum

/-- The nonzero total momenta `q + q'` of the factors. -/
private def Chi_S (ops : List (Idx × Idx)) : List Idx :=
  (ops.map (fun o => o.1 + o.2)).filter (· ≠ 0)

private lemma Chi_D_cons (o : Idx × Idx) (ops : List (Idx × Idx)) (n : Idx) :
    Chi_D (o :: ops) n = Chi_d o n + Chi_D ops n := by
  simp [Chi_D]

private lemma Chi_W_cons (o : Idx × Idx) (ops : List (Idx × Idx)) :
    Chi_W (o :: ops) = (if o.1 + o.2 = 0 then 2 else 1) + Chi_W ops := by
  simp [Chi_W]

private lemma Chi_S_cons (o : Idx × Idx) (ops : List (Idx × Idx)) :
    Chi_S (o :: ops) = if o.1 + o.2 = 0 then Chi_S ops else (o.1 + o.2) :: Chi_S ops := by
  by_cases h : o.1 + o.2 = 0 <;> simp [Chi_S, h]

private lemma Chi_D_zero (ops : List (Idx × Idx)) : Chi_D ops 0 = Chi_W ops := by
  induction ops with
  | nil => simp [Chi_D, Chi_W]
  | cons o ops ih =>
    rw [Chi_D_cons, Chi_W_cons, ih]
    unfold Chi_d
    by_cases h : o.1 + o.2 = 0
    · simp [h]
    · simp [h, Ne.symm h]

private lemma Chi_D_not_mem {n : Idx} (hn : n ≠ 0) :
    ∀ ops : List (Idx × Idx), n ∉ Chi_S ops → Chi_D ops n = 0
  | [], _ => by simp [Chi_D]
  | o :: ops, h => by
    rw [Chi_S_cons] at h
    rw [Chi_D_cons]
    unfold Chi_d
    by_cases hs : o.1 + o.2 = 0
    · simp only [hs, ↓reduceIte] at h
      simp [hs, hn, Chi_D_not_mem hn ops h]
    · simp only [hs, ↓reduceIte, List.mem_cons, not_or] at h
      simp [hs, hn, h.1, Chi_D_not_mem hn ops h.2]

private lemma Chi_D_mem {n : Idx} : ∀ ops : List (Idx × Idx), n ∈ Chi_S ops → 1 ≤ Chi_D ops n
  | [], h => by simp [Chi_S] at h
  | o :: ops, h => by
    rw [Chi_S_cons] at h
    rw [Chi_D_cons]
    by_cases hs : o.1 + o.2 = 0
    · simp only [hs, ↓reduceIte] at h
      have := Chi_D_mem ops h
      omega
    · simp only [hs, ↓reduceIte, List.mem_cons] at h
      rcases h with h | h
      · have : Chi_d o n = (if n = 0 then 1 else 0) + 1 := by
          simp [Chi_d, hs, h]
        omega
      · have := Chi_D_mem ops h
        omega

private lemma Chi_S_pairwise_tail {o : Idx × Idx} {ops : List (Idx × Idx)}
    (h : (Chi_S (o :: ops)).Pairwise Legs_pm) : (Chi_S ops).Pairwise Legs_pm := by
  rw [Chi_S_cons] at h
  by_cases hs : o.1 + o.2 = 0
  · simpa only [hs, ↓reduceIte] using h
  · simp only [hs, ↓reduceIte] at h
    exact (List.pairwise_cons.1 h).2

private lemma Chi_S_not_mem_head {o : Idx × Idx} {ops : List (Idx × Idx)} (hs : o.1 + o.2 ≠ 0)
    (h : (Chi_S (o :: ops)).Pairwise Legs_pm) :
    o.1 + o.2 ∉ Chi_S ops ∧ -(o.1 + o.2) ∉ Chi_S ops := by
  simp only [Chi_S_cons, hs, ↓reduceIte, List.pairwise_cons] at h
  refine ⟨fun hm => (h.1 _ hm).1 rfl, fun hm => (h.1 _ hm).2 (neg_neg _).symm⟩

private lemma Chi_D_le_one {n : Idx} (hn : n ≠ 0) :
    ∀ ops : List (Idx × Idx), (Chi_S ops).Pairwise Legs_pm → Chi_D ops n ≤ 1
  | [], _ => by simp [Chi_D]
  | o :: ops, h => by
    rw [Chi_D_cons]
    have ih := Chi_D_le_one hn ops (Chi_S_pairwise_tail h)
    by_cases hs : o.1 + o.2 = 0
    · simp [Chi_d, hs, hn, ih]
    · by_cases he : n = o.1 + o.2
      · have h0 := Chi_D_not_mem hn ops (he ▸ (Chi_S_not_mem_head hs h).1)
        rw [h0]
        simp [Chi_d, hs, he]
      · simp [Chi_d, hs, hn, he, ih]

private lemma Chi_D_pm {k : Idx} (hk : k ≠ 0) :
    ∀ ops : List (Idx × Idx), (Chi_S ops).Pairwise Legs_pm →
      Chi_D ops k = 0 ∨ Chi_D ops (-k) = 0
  | [], _ => by simp [Chi_D]
  | o :: ops, h => by
    have hk' : -k ≠ 0 := neg_ne_zero.mpr hk
    have hkk : k ≠ -k := fun e => hk (by
      have : k + k = 0 := by nth_rewrite 2 [e]; exact add_neg_cancel k
      funext i
      have := congrFun this i
      simp only [Pi.add_apply, Pi.zero_apply] at this
      simp only [Pi.zero_apply]
      omega)
    rw [Chi_D_cons, Chi_D_cons]
    have ih := Chi_D_pm hk ops (Chi_S_pairwise_tail h)
    by_cases hs : o.1 + o.2 = 0
    · simp only [Chi_d, hs, ↓reduceIte, hk, hk', zero_add]
      exact ih
    · obtain ⟨h1, h2⟩ := Chi_S_not_mem_head hs h
      by_cases e1 : k = o.1 + o.2
      · right
        have : -k ∉ Chi_S ops := by rw [e1]; exact h2
        rw [Chi_D_not_mem hk' ops this]
        have : -k ≠ o.1 + o.2 := fun e => hkk (e1.trans e.symm)
        simp [Chi_d, hs, hk', this]
      · by_cases e2 : -k = o.1 + o.2
        · left
          have : k ∉ Chi_S ops := by
            intro hm
            apply h2
            rw [← e2, neg_neg]
            exact hm
          rw [Chi_D_not_mem hk ops this]
          simp [Chi_d, hs, hk, e1]
        · simp only [Chi_d, hs, ↓reduceIte, hk, hk', e1, e2, add_zero, zero_add]
          exact ih

private lemma Chi_pairOp_apply {q q' n : Idx} (β : Occ) (h1 : n ≠ q) (h2 : n ≠ q')
    (h3 : n ≠ -q) : Chi_pairOp q q' β n = β n - Chi_d (q, q') n := by
  unfold Chi_pairOp Chi_d
  by_cases hs : q + q' = 0
  · simp only [hs, ↓reduceIte, MBasic_strictPair_apply, h1, h3, add_zero]
  · simp only [hs, ↓reduceIte, MBasic_softPair_apply, h1, h2, add_zero]
    omega

/-- Away from the created momenta, the product `Chi_ops ops` only removes particles. -/
private lemma Chi_ops_apply {n : Idx} (α : Occ) :
    ∀ ops : List (Idx × Idx), (∀ o ∈ ops, n ≠ o.1 ∧ n ≠ o.2 ∧ n ≠ -o.1) →
      Chi_ops ops α n = α n - Chi_D ops n
  | [], _ => by simp [Chi_ops, Chi_D]
  | (q, q') :: ops, h => by
    obtain ⟨h1, h2, h3⟩ := h (q, q') List.mem_cons_self
    change Chi_pairOp q q' (Chi_ops ops α) n = _
    rw [Chi_pairOp_apply (q := q) (q' := q') _ h1 h2 h3,
      Chi_ops_apply α ops (fun o ho => h o (List.mem_cons_of_mem _ ho)), Chi_D_cons]
    omega

private lemma Chi_avoid {ops : List (Idx × Idx)}
    (hops : ∀ o ∈ ops, inPHc ρ L kc o.1 ∧ inPHc ρ L kc o.2) {n : Idx}
    (hn : ¬ inPHc ρ L kc n) : ∀ o ∈ ops, n ≠ o.1 ∧ n ≠ o.2 ∧ n ≠ -o.1 := by
  intro o ho
  obtain ⟨h1, h2⟩ := hops o ho
  refine ⟨fun e => hn (e ▸ h1), fun e => hn (e ▸ h2), fun e => hn ?_⟩
  rw [e]
  exact Chi_PHc_neg.2 h1

private lemma Chi_not_PHc_zero (hρ : 0 < ρ) : ¬ inPHc ρ L kc 0 :=
  fun h => Regions_PH_ne_zero hρ h.1 rfl

private lemma Chi_not_PHc_PL (hρ : 0 < ρ) {n : Idx} (hn : inPL ρ L n) : ¬ inPHc ρ L kc n :=
  fun h => Regions_PL_PH hρ hn h.1

/-- The legs of the factors: momenta in `P_{H,c}`, total momentum `0` or in `P_L`. -/
private def Chi_Legs (ρ L kc : ℝ) (α : Occ) (ops : List (Idx × Idx)) : Prop :=
  ∀ o ∈ ops, inPHc ρ L kc o.1 ∧ inPHc ρ L kc o.2 ∧
    (o.1 + o.2 = 0 ∨ (inPL ρ L (o.1 + o.2) ∧ 1 ≤ α (o.1 + o.2)))

private lemma Chi_Legs_PHc {α : Occ} {ops : List (Idx × Idx)} (h : Chi_Legs ρ L kc α ops) :
    ∀ o ∈ ops, inPHc ρ L kc o.1 ∧ inPHc ρ L kc o.2 :=
  fun o ho => ⟨(h o ho).1, (h o ho).2.1⟩

private lemma Chi_ops_zero (hρ : 0 < ρ) {α : Occ} {ops : List (Idx × Idx)}
    (h : Chi_Legs ρ L kc α ops) : Chi_ops ops α 0 = α 0 - Chi_W ops := by
  rw [Chi_ops_apply α ops (Chi_avoid (Chi_Legs_PHc h) (Chi_not_PHc_zero hρ)), Chi_D_zero]

/-- A strict pair creation commutes with the product `Chi_ops ops` when nothing truncates. -/
private lemma Chi_strict_comm (hρ : 0 < ρ) (k : Idx) (α : Occ) :
    ∀ ops : List (Idx × Idx), Chi_Legs ρ L kc α ops → (Chi_S ops).Pairwise Legs_pm →
      Chi_W ops + 2 ≤ α 0 → strictPair k (Chi_ops ops α) = Chi_ops ops (strictPair k α)
  | [], _, _, _ => rfl
  | (q, q') :: ops, h4, h5, h6 => by
    have h4' : Chi_Legs ρ L kc α ops := fun o ho => h4 o (List.mem_cons_of_mem _ ho)
    have h5' := Chi_S_pairwise_tail h5
    rw [Chi_W_cons] at h6
    rw [Chi_ops_cons, Chi_ops_cons, ← Chi_strict_comm hρ k α ops h4' h5' (by omega)]
    dsimp only
    have h0 := Chi_ops_zero hρ h4'
    set β := Chi_ops ops α with hβ
    unfold Chi_pairOp
    by_cases hs : q + q' = 0
    · simp only [hs, ↓reduceIte] at h6 ⊢
      have h4β : 4 ≤ β 0 := by omega
      exact Reorder_strict_strict h4β
    · simp only [hs, ↓reduceIte] at h6 ⊢
      have hor : q + q' = 0 ∨ (inPL ρ L (q + q') ∧ 1 ≤ α (q + q')) :=
        (h4 (q, q') List.mem_cons_self).2.2
      obtain ⟨hPL, hα1⟩ := hor.resolve_left hs
      have hnm := (Chi_S_not_mem_head (o := (q, q')) hs h5).1
      have hu : β (q + q') = α (q + q') := by
        rw [hβ, Chi_ops_apply α ops (Chi_avoid (Chi_Legs_PHc h4') (Chi_not_PHc_PL hρ hPL)),
          Chi_D_not_mem hs ops hnm]
        simp
      have h3β : 3 ≤ β 0 := by omega
      have h1β : 1 ≤ β (q + q') := by omega
      exact (Reorder_soft_strict hs h3β h1β).symm

private lemma Chi_strict_symm (k : Idx) {α : Occ} (hs : ∀ n, α n = α (-n)) (n : Idx) :
    strictPair k α n = strictPair k α (-n) := by
  rw [MBasic_strictPair_apply, MBasic_strictPair_apply, hs n]
  have e0 : (-n = 0) ↔ (n = 0) := neg_eq_zero
  have e1 : (-n = k) ↔ (n = -k) := neg_eq_iff_eq_neg
  have e2 : (-n = -k) ↔ (n = k) := neg_inj
  simp only [e0, e1, e2]
  split_ifs <;> omega

private lemma Chi_strict_ge (k : Idx) (α : Occ) {n : Idx} (hn : n ≠ 0) :
    α n ≤ strictPair k α n := by
  rw [MBasic_strictPair_apply]
  simp only [hn, ↓reduceIte]
  omega

/-- A strict pair creation at `k ∉ P_{H,c}` moves into `α`. -/
private lemma Chi_strict_out (hρ : 0 < ρ) {χ α : Occ} {ops : List (Idx × Idx)} {k : Idx}
    (hk0 : k ≠ 0) (hkc : ¬ inPHc ρ L kc k) (h2 : 2 ≤ χ 0)
    (hs : ∀ n, α n = α (-n)) (hz : ∀ n, inPHc ρ L kc n → α n = 0)
    (h4 : Chi_Legs ρ L kc α ops) (h5 : (Chi_S ops).Pairwise Legs_pm) (h6 : Chi_W ops ≤ α 0)
    (h7 : χ = Chi_ops ops α) :
    2 ≤ α 0 ∧ (∀ n, strictPair k α n = strictPair k α (-n)) ∧
      (∀ n, inPHc ρ L kc n → strictPair k α n = 0) ∧ Chi_Legs ρ L kc (strictPair k α) ops ∧
      Chi_W ops ≤ strictPair k α 0 ∧ strictPair k χ = Chi_ops ops (strictPair k α) := by
  have h0 := Chi_ops_zero hρ h4
  rw [← h7] at h0
  have hW : Chi_W ops + 2 ≤ α 0 := by omega
  refine ⟨by omega, Chi_strict_symm k hs, ?_, ?_, ?_, ?_⟩
  · intro n hn
    have hn0 : n ≠ 0 := fun e => Chi_not_PHc_zero hρ (e ▸ hn)
    have hnk : n ≠ k := fun e => hkc (e ▸ hn)
    have hnk' : n ≠ -k := by
      intro e
      apply hkc
      rw [← neg_neg k, ← e]
      exact Chi_PHc_neg.2 hn
    rw [MBasic_strictPair_apply]
    simp [hn0, hnk, hnk', hz n hn]
  · intro o ho
    obtain ⟨h1, h2, h3⟩ := h4 o ho
    refine ⟨h1, h2, h3.imp_right fun h => ⟨h.1, ?_⟩⟩
    exact h.2.trans (Chi_strict_ge k α (Regions_PL_ne_zero hρ h.1))
  · rw [MBasic_strictPair_apply]
    have : (0 : Idx) ≠ -k := fun e => hk0 (neg_eq_zero.mp e.symm)
    simp only [Ne.symm hk0, this, ↓reduceIte, add_zero]
    omega
  · rw [h7]
    exact Chi_strict_comm hρ k α ops h4 h5 hW

/-- Proposition 11.1 [propchi]. -/
theorem Prop11_1 (hρ : 0 < ρ) {χ : Occ} (hχ : InM ρ L kc N χ) :
    ∃ (α : Occ) (ops : List (Idx × Idx)),
      InM ρ L kc N α ∧ (∀ n, α n = α (-n)) ∧ (∀ n, inPHc ρ L kc n → α n = 0) ∧
      (∀ o ∈ ops, inPHc ρ L kc o.1 ∧ inPHc ρ L kc o.2 ∧
        (o.1 + o.2 = 0 ∨ (inPL ρ L (o.1 + o.2) ∧ 1 ≤ α (o.1 + o.2)))) ∧
      ((ops.map (fun o => o.1 + o.2)).filter (· ≠ 0)).Pairwise Legs_pm ∧
      (ops.map (fun o => if o.1 + o.2 = 0 then 2 else 1)).sum ≤ α 0 ∧
      χ = Chi_ops ops α := by
  suffices H : ∃ (α : Occ) (ops : List (Idx × Idx)),
      InM ρ L kc N α ∧ (∀ n, α n = α (-n)) ∧ (∀ n, inPHc ρ L kc n → α n = 0) ∧
      Chi_Legs ρ L kc α ops ∧ (Chi_S ops).Pairwise Legs_pm ∧ Chi_W ops ≤ α 0 ∧
      χ = Chi_ops ops α from H
  induction hχ with
  | free =>
    refine ⟨Finsupp.single 0 N, [], InM.free, ?_, ?_, by simp [Chi_Legs], by simp [Chi_S],
      by simp [Chi_W], rfl⟩
    · intro n
      have e : ((0 : Idx) = -n) ↔ ((0 : Idx) = n) := by
        rw [eq_comm, neg_eq_zero, eq_comm]
      simp only [Finsupp.single_apply, e]
    · intro n hn
      have hn0 : (0 : Idx) ≠ n := fun e => Chi_not_PHc_zero hρ (e ▸ hn)
      simp only [Finsupp.single_apply, hn0, ↓reduceIte]
  | @strictIH χ k _ hk h2 ih =>
    obtain ⟨α, ops, hα, hs, hz, h4, h5, h6, h7⟩ := ih
    have hk0 : k ≠ 0 := hk.elim (Regions_PI_ne_zero hρ) (Regions_PH_ne_zero hρ)
    by_cases hkc : inPHc ρ L kc k
    · have h0 := Chi_ops_zero hρ h4
      rw [← h7] at h0
      refine ⟨α, (k, -k) :: ops, hα, hs, hz, ?_, ?_, ?_, ?_⟩
      · intro o ho
        rcases List.mem_cons.1 ho with rfl | ho
        · exact ⟨hkc, Chi_PHc_neg.2 hkc, Or.inl (add_neg_cancel k)⟩
        · exact h4 o ho
      · simpa only [Chi_S_cons, add_neg_cancel, ↓reduceIte] using h5
      · simp only [Chi_W_cons, add_neg_cancel, ↓reduceIte]
        omega
      · rw [Chi_ops_cons, ← h7]
        simp only [Chi_pairOp, add_neg_cancel, ↓reduceIte]
    · obtain ⟨h2α, hs', hz', h4', h6', h7'⟩ :=
        Chi_strict_out hρ hk0 hkc h2 hs hz h4 h5 h6 h7
      exact ⟨strictPair k α, ops, InM.strictIH hα hk h2α, hs', hz', h4', h5, h6', h7'⟩
  | @strictL χ k _ hk hmc h2 ih =>
    obtain ⟨α, ops, hα, hs, hz, h4, h5, h6, h7⟩ := ih
    have hk0 : k ≠ 0 := Regions_PL_ne_zero hρ hk
    have hk0' : -k ≠ 0 := neg_ne_zero.mpr hk0
    have hkc : ¬ inPHc ρ L kc k := Chi_not_PHc_PL hρ hk
    obtain ⟨h2α, hs', hz', h4', h6', h7'⟩ := Chi_strict_out hρ hk0 hkc h2 hs hz h4 h5 h6 h7
    have hχk : χ k = α k - Chi_D ops k := by
      rw [h7]
      exact Chi_ops_apply α ops (Chi_avoid (Chi_Legs_PHc h4) hkc)
    have hχk' : χ (-k) = α (-k) - Chi_D ops (-k) := by
      rw [h7]
      exact Chi_ops_apply α ops
        (Chi_avoid (Chi_Legs_PHc h4) (Chi_not_PHc_PL hρ (Regions_PL_neg.2 hk)))
    have hpm := Chi_D_pm hk0 ops h5
    have hsk := hs k
    have hstar : alphaStar α k ≤ alphaStar χ k := by
      unfold alphaStar
      omega
    have hmc' : ((alphaStar α k : ℕ) : ℝ) < mc ρ :=
      lt_of_le_of_lt (by exact_mod_cast hstar) hmc
    exact ⟨strictPair k α, ops, InM.strictL hα hk hmc' h2α, hs', hz', h4', h5, h6', h7'⟩
  | @soft χ u p₁ p₂ _ hu hsym hp hp₁ hp₂ hk₁ hk₂ h0 h1 ih =>
    obtain ⟨α, ops, hα, hs, hz, h4, h5, h6, h7⟩ := ih
    have hu0 : u ≠ 0 := Regions_PL_ne_zero hρ hu
    have hu0' : -u ≠ 0 := neg_ne_zero.mpr hu0
    have hc1 : inPHc ρ L kc p₁ := ⟨hp₁, hk₁⟩
    have hc2 : inPHc ρ L kc p₂ := ⟨hp₂, hk₂⟩
    have hχ0 := Chi_ops_zero hρ h4
    rw [← h7] at hχ0
    have hχu : χ u = α u - Chi_D ops u := by
      rw [h7]
      exact Chi_ops_apply α ops (Chi_avoid (Chi_Legs_PHc h4) (Chi_not_PHc_PL hρ hu))
    have hχu' : χ (-u) = α (-u) - Chi_D ops (-u) := by
      rw [h7]
      exact Chi_ops_apply α ops
        (Chi_avoid (Chi_Legs_PHc h4) (Chi_not_PHc_PL hρ (Regions_PL_neg.2 hu)))
    have hl1 := Chi_D_le_one hu0 ops h5
    have hl2 := Chi_D_le_one hu0' ops h5
    have hpm := Chi_D_pm hu0 ops h5
    have hsu := hs u
    have hnot : u ∉ Chi_S ops := fun hm => by
      have := Chi_D_mem ops hm
      omega
    have hnot' : -u ∉ Chi_S ops := fun hm => by
      have := Chi_D_mem ops hm
      omega
    have hps : (p₁, p₂).1 + (p₁, p₂).2 = u := hp
    refine ⟨α, (p₁, p₂) :: ops, hα, hs, hz, ?_, ?_, ?_, ?_⟩
    · intro o ho
      rcases List.mem_cons.1 ho with rfl | ho
      · refine ⟨hc1, hc2, Or.inr ⟨hps ▸ hu, ?_⟩⟩
        rw [hps]
        omega
      · exact h4 o ho
    · simp only [Chi_S_cons, hps, hu0, ↓reduceIte]
      refine List.Pairwise.cons (fun v hv => ⟨fun e => hnot (e ▸ hv), fun e => hnot' ?_⟩) h5
      rw [e, neg_neg]
      exact hv
    · simp only [Chi_W_cons, hps, hu0, ↓reduceIte]
      omega
    · rw [Chi_ops_cons, ← h7]
      simp only [Chi_pairOp, hps, hu0, ↓reduceIte]

end Chi

end LHYUpper
