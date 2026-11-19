import LHYUpper.Scattering.Solution
import LHYUpper.TrialState.Chi
import LHYUpper.TrialState.FRatio
import LHYUpper.Scattering.Lambda

/-!
# The products (11.5) [elementform2] over a common base

In the proof of Lemma 11.2 [thehardestlemma] the states are products `∏ 𝓐_{q_i, q'_i} α` of
(11.5) [elementform2]. Their factors commute and every sub-product stays in `M` (Definition 3.4
[M]); the base `α` and the total momenta are determined by the product off `P_{H,c}` ((8.1)
[defPHc]); and (11.13) bounds `|Ψ(β)|²` with the exponent `2s + 2t`, the factor `4^t` and
`⌈m_c⌉`.
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

namespace HardRep

/-- `β = ∏ 𝓐_{q_i, q'_i} α` is a product (11.5) [elementform2] on `α ∈ M`: the momenta
`q_i, q'_i` lie in `P_{H,c}` ((8.1) [defPHc]), each total momentum `q_i + q'_i` is `0` or lies
in `P_L` with `α(q_i + q'_i) = α(-(q_i + q'_i)) ≥ 1`, the nonzero totals are pairwise `≠ ±`,
and `α(0)` is at least `2s + t` (`s` pairs of total momentum `0`, `t` others). -/
def Rep (ρ L kc : ℝ) (N : ℕ) (α : Occ) (ops : List (Idx × Idx)) : Prop :=
  InM ρ L kc N α ∧
    (∀ o ∈ ops, inPHc ρ L kc o.1 ∧ inPHc ρ L kc o.2 ∧
      (o.1 + o.2 = 0 ∨ (inPL ρ L (o.1 + o.2) ∧ 1 ≤ α (o.1 + o.2) ∧
        α (o.1 + o.2) = α (-(o.1 + o.2))))) ∧
    ((ops.map (fun o => o.1 + o.2)).filter (· ≠ 0)).Pairwise Legs_pm ∧
    (ops.map (fun o => if o.1 + o.2 = 0 then 2 else 1)).sum ≤ α 0

/-- The multiset of the total momenta `u_i = q_i + q'_i` of the factors of (11.5)
[elementform2]: `s` zeros and `v_1, …, v_t`. -/
def sums (ops : List (Idx × Idx)) : Multiset Idx := ↑(ops.map fun o => o.1 + o.2)

/-- The weight `ρ^{2s+t} (g₀ ε_H^{-2})^{2s+2t} (4 ⌈m_c⌉ / |Λ|)^t` of (11.13), at `ρ = ρ_N`,
`L = L_N`. -/
def wt (V w : R3 → ℝ) (N s t : ℕ) : ℝ :=
  rhoN N ^ (2 * s + t) * (g0 V w / epsP (rhoN N) ^ 2) ^ (2 * s + 2 * t) *
    (4 * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3) ^ t

end HardRep

section HardRepAux
variable {ρ L kc : ℝ} {N : ℕ}

private lemma HR_norm_mom_neg (L : ℝ) (n : Idx) : ‖mom L (-n)‖ = ‖mom L n‖ := by
  have : mom L (-n) = -mom L n := by
    ext i
    simp [mom]
  rw [this, norm_neg]

private lemma HR_PHc_neg {n : Idx} : inPHc ρ L kc (-n) ↔ inPHc ρ L kc n := by
  unfold inPHc
  rw [Regions_PH_neg, HR_norm_mom_neg]

private lemma HR_ne_neg {n : Idx} (hn : n ≠ 0) : n ≠ -n := fun e => hn (by
  have : n + n = 0 := by nth_rewrite 2 [e]; exact add_neg_cancel n
  funext i
  have := congrFun this i
  simp only [Pi.add_apply, Pi.zero_apply] at this
  simp only [Pi.zero_apply]
  omega)

private lemma HR_pm_symm {a b : Idx} (h : Legs_pm a b) : Legs_pm b a :=
  ⟨fun e => h.1 e.symm, fun e => h.2 (by rw [e, neg_neg])⟩

private lemma HR_not_PHc_zero (hρ : 0 < ρ) : ¬ inPHc ρ L kc 0 :=
  fun h => Regions_PH_ne_zero hρ h.1 rfl

private lemma HR_not_PHc_PL (hρ : 0 < ρ) {n : Idx} (hn : inPL ρ L n) : ¬ inPHc ρ L kc n :=
  fun h => Regions_PL_PH hρ hn h.1

/-- The number of particles that `𝓐_{o.1,o.2}` removes at `n`. -/
private def HR_d (o : Idx × Idx) (n : Idx) : ℕ :=
  if o.1 + o.2 = 0 then (if n = 0 then 2 else 0)
  else (if n = 0 then 1 else 0) + (if n = o.1 + o.2 then 1 else 0)

/-- The number of particles that `𝓐_{o.1,o.2}` creates at `n`. -/
private def HR_g (o : Idx × Idx) (n : Idx) : ℕ :=
  (if n = o.1 then 1 else 0) + (if n = o.2 then 1 else 0)

private def HR_D (ops : List (Idx × Idx)) (n : Idx) : ℕ := (ops.map (fun o => HR_d o n)).sum

private def HR_G (ops : List (Idx × Idx)) (n : Idx) : ℕ := (ops.map (fun o => HR_g o n)).sum

private def HR_W (ops : List (Idx × Idx)) : ℕ :=
  (ops.map (fun o => if o.1 + o.2 = 0 then 2 else 1)).sum

private def HR_S (ops : List (Idx × Idx)) : List Idx :=
  (ops.map (fun o => o.1 + o.2)).filter (· ≠ 0)

/-- The condition of `HardRep.Rep` on one factor. -/
private def HR_C (ρ L kc : ℝ) (α : Occ) (o : Idx × Idx) : Prop :=
  inPHc ρ L kc o.1 ∧ inPHc ρ L kc o.2 ∧
    (o.1 + o.2 = 0 ∨ (inPL ρ L (o.1 + o.2) ∧ 1 ≤ α (o.1 + o.2) ∧
      α (o.1 + o.2) = α (-(o.1 + o.2))))

/-- Legs in `P_{H,c}`, total momentum `0` or in `P_L`. -/
private def HR_Legs (ρ L kc : ℝ) (ops : List (Idx × Idx)) : Prop :=
  ∀ o ∈ ops, inPHc ρ L kc o.1 ∧ inPHc ρ L kc o.2 ∧ (o.1 + o.2 = 0 ∨ inPL ρ L (o.1 + o.2))

private lemma HR_Legs_of_C {α : Occ} {ops : List (Idx × Idx)}
    (h : ∀ o ∈ ops, HR_C ρ L kc α o) : HR_Legs ρ L kc ops :=
  fun o ho => ⟨(h o ho).1, (h o ho).2.1, (h o ho).2.2.imp_right fun h => h.1⟩

private lemma HR_D_cons (o : Idx × Idx) (ops : List (Idx × Idx)) (n : Idx) :
    HR_D (o :: ops) n = HR_d o n + HR_D ops n := by
  simp [HR_D]

private lemma HR_G_cons (o : Idx × Idx) (ops : List (Idx × Idx)) (n : Idx) :
    HR_G (o :: ops) n = HR_g o n + HR_G ops n := by
  simp [HR_G]

private lemma HR_W_cons (o : Idx × Idx) (ops : List (Idx × Idx)) :
    HR_W (o :: ops) = (if o.1 + o.2 = 0 then 2 else 1) + HR_W ops := by
  simp [HR_W]

private lemma HR_S_cons (o : Idx × Idx) (ops : List (Idx × Idx)) :
    HR_S (o :: ops) = if o.1 + o.2 = 0 then HR_S ops else (o.1 + o.2) :: HR_S ops := by
  by_cases h : o.1 + o.2 = 0 <;> simp [HR_S, h]

private lemma HR_W_append (D C : List (Idx × Idx)) : HR_W (D ++ C) = HR_W D + HR_W C := by
  simp [HR_W]

private lemma HR_S_append (D C : List (Idx × Idx)) : HR_S (D ++ C) = HR_S D ++ HR_S C := by
  simp [HR_S]

private lemma HR_D_perm {l l' : List (Idx × Idx)} (hp : l.Perm l') (n : Idx) :
    HR_D l n = HR_D l' n :=
  (hp.map _).sum_eq

private lemma HR_G_perm {l l' : List (Idx × Idx)} (hp : l.Perm l') (n : Idx) :
    HR_G l n = HR_G l' n :=
  (hp.map _).sum_eq

private lemma HR_W_perm {l l' : List (Idx × Idx)} (hp : l.Perm l') : HR_W l = HR_W l' :=
  (hp.map _).sum_eq

private lemma HR_S_perm {l l' : List (Idx × Idx)} (hp : l.Perm l') :
    (HR_S l).Perm (HR_S l') :=
  (hp.map _).filter _

private lemma HR_pairOp_apply (q q' : Idx) (β : Occ) (n : Idx) :
    Chi_pairOp q q' β n = β n - HR_d (q, q') n + HR_g (q, q') n := by
  unfold Chi_pairOp HR_d HR_g
  by_cases hs : q + q' = 0
  · have hq' : q' = -q := eq_neg_of_add_eq_zero_right hs
    subst hq'
    simp only [hs, ↓reduceIte, MBasic_strictPair_apply]
    omega
  · simp only [hs, ↓reduceIte, MBasic_softPair_apply]
    omega

private lemma HR_ops_append (D C : List (Idx × Idx)) (α : Occ) :
    Chi_ops D (Chi_ops C α) = Chi_ops (D ++ C) α := by
  simp [Chi_ops, List.foldr_append]

/-- Where no factor creates, the product only removes. -/
private lemma HR_ops_out {n : Idx} (α : Occ) :
    ∀ ops : List (Idx × Idx), (∀ o ∈ ops, HR_g o n = 0) → Chi_ops ops α n = α n - HR_D ops n
  | [], _ => by simp [Chi_ops, HR_D]
  | (q, q') :: ops, h => by
    change Chi_pairOp q q' (Chi_ops ops α) n = _
    rw [HR_pairOp_apply, HR_ops_out α ops (fun o ho => h o (List.mem_cons_of_mem _ ho)),
      h (q, q') List.mem_cons_self, HR_D_cons]
    omega

/-- Where no factor removes, the product only creates. -/
private lemma HR_ops_in {n : Idx} (α : Occ) :
    ∀ ops : List (Idx × Idx), (∀ o ∈ ops, HR_d o n = 0) → Chi_ops ops α n = α n + HR_G ops n
  | [], _ => by simp [Chi_ops, HR_G]
  | (q, q') :: ops, h => by
    change Chi_pairOp q q' (Chi_ops ops α) n = _
    rw [HR_pairOp_apply, HR_ops_in α ops (fun o ho => h o (List.mem_cons_of_mem _ ho)),
      h (q, q') List.mem_cons_self, HR_G_cons]
    omega

private lemma HR_g_out {ops : List (Idx × Idx)} (h : HR_Legs ρ L kc ops) {n : Idx}
    (hn : ¬ inPHc ρ L kc n) : ∀ o ∈ ops, HR_g o n = 0 := by
  intro o ho
  obtain ⟨h1, h2, -⟩ := h o ho
  have e1 : n ≠ o.1 := fun e => hn (e ▸ h1)
  have e2 : n ≠ o.2 := fun e => hn (e ▸ h2)
  simp [HR_g, e1, e2]

private lemma HR_d_in (hρ : 0 < ρ) {ops : List (Idx × Idx)} (h : HR_Legs ρ L kc ops) {n : Idx}
    (hn : inPHc ρ L kc n) : ∀ o ∈ ops, HR_d o n = 0 := by
  intro o ho
  have h0 : n ≠ 0 := Regions_PH_ne_zero hρ hn.1
  by_cases hs : o.1 + o.2 = 0
  · simp [HR_d, hs, h0]
  · have hPL := (h o ho).2.2.resolve_left hs
    have hu : n ≠ o.1 + o.2 := fun e => Regions_PL_PH hρ hPL (e ▸ hn.1)
    simp [HR_d, hs, h0, hu]

/-- The product depends only on the multiset of its factors. -/
private lemma HR_ops_perm (hρ : 0 < ρ) {l l' : List (Idx × Idx)} (h : HR_Legs ρ L kc l')
    (hp : l.Perm l') (α : Occ) : Chi_ops l α = Chi_ops l' α := by
  have hl : HR_Legs ρ L kc l := fun o ho => h o (hp.subset ho)
  ext n
  by_cases hn : inPHc ρ L kc n
  · rw [HR_ops_in α l (HR_d_in hρ hl hn), HR_ops_in α l' (HR_d_in hρ h hn), HR_G_perm hp]
  · rw [HR_ops_out α l (HR_g_out hl hn), HR_ops_out α l' (HR_g_out h hn), HR_D_perm hp]

private lemma HR_D_zero (ops : List (Idx × Idx)) : HR_D ops 0 = HR_W ops := by
  induction ops with
  | nil => simp [HR_D, HR_W]
  | cons o ops ih =>
    rw [HR_D_cons, HR_W_cons, ih]
    unfold HR_d
    by_cases h : o.1 + o.2 = 0
    · simp [h]
    · simp [h, Ne.symm h]

private lemma HR_ops_zero (hρ : 0 < ρ) {ops : List (Idx × Idx)} (h : HR_Legs ρ L kc ops)
    (α : Occ) : Chi_ops ops α 0 = α 0 - HR_W ops := by
  rw [HR_ops_out α ops (HR_g_out h (HR_not_PHc_zero hρ)), HR_D_zero]

private lemma HR_D_not_mem {n : Idx} (hn : n ≠ 0) :
    ∀ ops : List (Idx × Idx), n ∉ HR_S ops → HR_D ops n = 0
  | [], _ => by simp [HR_D]
  | o :: ops, h => by
    rw [HR_S_cons] at h
    rw [HR_D_cons]
    unfold HR_d
    by_cases hs : o.1 + o.2 = 0
    · simp only [hs, ↓reduceIte] at h
      simp [hs, hn, HR_D_not_mem hn ops h]
    · simp only [hs, ↓reduceIte, List.mem_cons, not_or] at h
      simp [hs, hn, h.1, HR_D_not_mem hn ops h.2]

private lemma HR_D_mem {n : Idx} : ∀ ops : List (Idx × Idx), n ∈ HR_S ops → 1 ≤ HR_D ops n
  | [], h => by simp [HR_S] at h
  | o :: ops, h => by
    rw [HR_S_cons] at h
    rw [HR_D_cons]
    by_cases hs : o.1 + o.2 = 0
    · simp only [hs, ↓reduceIte] at h
      have := HR_D_mem ops h
      omega
    · simp only [hs, ↓reduceIte, List.mem_cons] at h
      rcases h with h | h
      · have : HR_d o n = (if n = 0 then 1 else 0) + 1 := by
          simp [HR_d, hs, h]
        omega
      · have := HR_D_mem ops h
        omega

private lemma HR_S_pairwise_tail {o : Idx × Idx} {ops : List (Idx × Idx)}
    (h : (HR_S (o :: ops)).Pairwise Legs_pm) : (HR_S ops).Pairwise Legs_pm := by
  rw [HR_S_cons] at h
  by_cases hs : o.1 + o.2 = 0
  · simpa only [hs, ↓reduceIte] using h
  · simp only [hs, ↓reduceIte] at h
    exact (List.pairwise_cons.1 h).2

private lemma HR_S_not_mem_head {o : Idx × Idx} {ops : List (Idx × Idx)} (hs : o.1 + o.2 ≠ 0)
    (h : (HR_S (o :: ops)).Pairwise Legs_pm) :
    o.1 + o.2 ∉ HR_S ops ∧ -(o.1 + o.2) ∉ HR_S ops := by
  simp only [HR_S_cons, hs, ↓reduceIte, List.pairwise_cons] at h
  refine ⟨fun hm => (h.1 _ hm).1 rfl, fun hm => (h.1 _ hm).2 (neg_neg _).symm⟩

private lemma HR_D_le_one {n : Idx} (hn : n ≠ 0) :
    ∀ ops : List (Idx × Idx), (HR_S ops).Pairwise Legs_pm → HR_D ops n ≤ 1
  | [], _ => by simp [HR_D]
  | o :: ops, h => by
    rw [HR_D_cons]
    have ih := HR_D_le_one hn ops (HR_S_pairwise_tail h)
    by_cases hs : o.1 + o.2 = 0
    · simp [HR_d, hs, hn, ih]
    · by_cases he : n = o.1 + o.2
      · have h0 := HR_D_not_mem hn ops (he ▸ (HR_S_not_mem_head hs h).1)
        rw [h0]
        simp [HR_d, hs, he]
      · simp [HR_d, hs, hn, he, ih]

private lemma HR_S_mem {α : Occ} {ops : List (Idx × Idx)} (h1 : ∀ o ∈ ops, HR_C ρ L kc α o)
    {n : Idx} (hn : n ∈ HR_S ops) :
    n ≠ 0 ∧ inPL ρ L n ∧ 1 ≤ α n ∧ α n = α (-n) := by
  obtain ⟨hm, hn0⟩ := List.mem_filter.1 hn
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hm
  have hs : o.1 + o.2 ≠ 0 := by simpa using hn0
  exact ⟨hs, (h1 o ho).2.2.resolve_left hs⟩

private lemma HR_S_neg {ops : List (Idx × Idx)} (h : (HR_S ops).Pairwise Legs_pm) {n : Idx}
    (hn : n ∈ HR_S ops) : -n ∉ HR_S ops := by
  intro hm
  have h0 : n ≠ 0 := by simpa using (List.mem_filter.1 hn).2
  have : Std.Symm Legs_pm := ⟨fun _ _ h => HR_pm_symm h⟩
  exact (h.forall hn hm (HR_ne_neg h0)).2 (neg_neg n).symm

private lemma HR_S_nodup {ops : List (Idx × Idx)} (h : (HR_S ops).Pairwise Legs_pm) :
    (HR_S ops).Nodup :=
  h.imp fun h => h.1

/-- Off `P_{H,c} ∪ {0}` the product removes one particle at each nonzero total. -/
private lemma HR_val {α : Occ} {ops : List (Idx × Idx)}
    (h1 : ∀ o ∈ ops, HR_C ρ L kc α o) (h2 : (HR_S ops).Pairwise Legs_pm) {n : Idx}
    (hn : n ≠ 0) (hnc : ¬ inPHc ρ L kc n) :
    Chi_ops ops α n = α n - (if n ∈ HR_S ops then 1 else 0) := by
  rw [HR_ops_out α ops (HR_g_out (HR_Legs_of_C h1) hnc)]
  congr 1
  by_cases hm : n ∈ HR_S ops
  · have := HR_D_le_one hn ops h2
    have := HR_D_mem ops hm
    simp only [hm, ↓reduceIte]
    omega
  · simp [hm, HR_D_not_mem hn ops hm]

/-- Off `P_{H,c} ∪ {0}`, the nonzero totals are where the product is smaller than at `-n`. -/
private lemma HR_char {α : Occ} {ops : List (Idx × Idx)}
    (hs : ∀ n, α n = α (-n)) (h1 : ∀ o ∈ ops, HR_C ρ L kc α o)
    (h2 : (HR_S ops).Pairwise Legs_pm) {n : Idx} (hn : n ≠ 0) (hnc : ¬ inPHc ρ L kc n) :
    n ∈ HR_S ops ↔ Chi_ops ops α n < Chi_ops ops α (-n) := by
  have v1 := HR_val h1 h2 hn hnc
  have v2 := HR_val h1 h2 (neg_ne_zero.2 hn) (HR_PHc_neg.not.2 hnc)
  have hsn := hs n
  by_cases hm : n ∈ HR_S ops
  · have hm' := HR_S_neg h2 hm
    have h1n := (HR_S_mem h1 hm).2.2.1
    simp only [hm, hm', ↓reduceIte] at v1 v2
    simp only [hm, true_iff]
    omega
  · simp only [hm, ↓reduceIte] at v1
    simp only [hm, false_iff, not_lt]
    split_ifs at v2 <;> omega

private lemma HR_W_eq : ∀ ops : List (Idx × Idx),
    HR_W ops = 2 * (ops.map (fun o => o.1 + o.2)).count 0 + (HR_S ops).length
  | [] => by simp [HR_W, HR_S]
  | o :: ops => by
    rw [HR_W_cons, HR_S_cons, HR_W_eq ops]
    by_cases h : o.1 + o.2 = 0
    · simp [h]
      omega
    · simp [h]
      omega

private lemma HR_num_split (α : Occ) : α.num = α 0 + Occ.num (Finsupp.erase 0 α) := by
  conv_lhs => rw [← Finsupp.single_add_erase 0 α]
  unfold Occ.num
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]

/-- Every sub-product stays in `M`. -/
private lemma HR_inM (hρ : 0 < ρ) {α : Occ} (hα : InM ρ L kc N α) :
    ∀ C : List (Idx × Idx), (∀ o ∈ C, HR_C ρ L kc α o) → (HR_S C).Pairwise Legs_pm →
      HR_W C ≤ α 0 → InM ρ L kc N (Chi_ops C α)
  | [], _, _, _ => hα
  | (q, q') :: C, h1, h2, h3 => by
    have h1' : ∀ o ∈ C, HR_C ρ L kc α o := fun o ho => h1 o (List.mem_cons_of_mem _ ho)
    have h2' := HR_S_pairwise_tail h2
    rw [HR_W_cons] at h3
    have ih := HR_inM hρ hα C h1' h2' (by split_ifs at h3 <;> omega)
    have h0 := HR_ops_zero hρ (HR_Legs_of_C h1') α
    obtain ⟨hq, hq', hor⟩ := h1 (q, q') List.mem_cons_self
    change InM ρ L kc N (Chi_pairOp q q' (Chi_ops C α))
    unfold Chi_pairOp
    by_cases hs : q + q' = 0
    · simp only [hs, ↓reduceIte] at h3 ⊢
      exact InM.strictIH ih (Or.inr hq.1) (by omega)
    · simp only [hs, ↓reduceIte] at h3 ⊢
      obtain ⟨hPL, hu1, husym⟩ := hor.resolve_left hs
      obtain ⟨hn1, hn2⟩ := HR_S_not_mem_head (o := (q, q')) hs h2
      have hu0 : -(q + q') ≠ 0 := neg_ne_zero.mpr hs
      have e1 : Chi_ops C α (q + q') = α (q + q') := by
        rw [HR_ops_out α C (HR_g_out (HR_Legs_of_C h1') (HR_not_PHc_PL hρ hPL)),
          HR_D_not_mem hs C hn1]
        simp
      have e2 : Chi_ops C α (-(q + q')) = α (-(q + q')) := by
        rw [HR_ops_out α C (HR_g_out (HR_Legs_of_C h1')
          (HR_not_PHc_PL hρ (Regions_PL_neg.2 hPL))), HR_D_not_mem hu0 C hn2]
        simp
      exact InM.soft ih hPL (by rw [e1, e2]; exact husym) rfl hq.1 hq'.1 hq.2 hq'.2
        (by omega) (by rw [e1]; exact hu1)

private lemma HR_count_cons (o : Idx × Idx) (ops : List (Idx × Idx)) :
    (HardRep.sums (o :: ops)).count 0 =
      (HardRep.sums ops).count 0 + (if o.1 + o.2 = 0 then 1 else 0) := by
  unfold HardRep.sums
  rw [Multiset.coe_count, Multiset.coe_count, List.map_cons, List.count_cons]
  simp

private lemma HR_count_le (ops : List (Idx × Idx)) : (HardRep.sums ops).count 0 ≤ ops.length := by
  have := Multiset.count_le_card 0 (HardRep.sums ops)
  simpa [HardRep.sums] using this

end HardRepAux

/-! ### The squared weights `|f(α)|²` of (3.18) [deffal] -/

section HardRepWeight
variable {V w : R3 → ℝ} {ρ L kc : ℝ} {N : ℕ}

private lemma HR_norm_csqrt_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h, abs_of_nonneg h]
  · have h' : 0 ≤ -x := by linarith [not_le.1 h]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt h', abs_of_neg (not_le.1 h)]

/-- The factor of `|f(α)|²` at the index `n`, with `a = α(n)`, `b = α(-n)`. -/
private def HR_phi (V w : R3 → ℝ) (ρ L : ℝ) (n : Idx) (a b : ℕ) : ℝ :=
  (if n ≠ 0 then |lam V w ρ L n| ^ a else 1) *
    (if inPL ρ L n ∧ max a b = a + 1 then
      |4 * ((max a b : ℕ) : ℝ) * lam V w ρ L n / L ^ 3| else 1)

private lemma HR_phi_zero (hρ : 0 < ρ) (a b : ℕ) : HR_phi V w ρ L 0 a b = 1 := by
  have : ¬ inPL ρ L 0 := fun h => Regions_PL_ne_zero hρ h rfl
  simp [HR_phi, this]

private lemma HR_phi_notPL {n : Idx} (hn : n ≠ 0) (h : ¬ inPL ρ L n) (a b : ℕ) :
    HR_phi V w ρ L n a b = |lam V w ρ L n| ^ a := by
  simp [HR_phi, hn, h]

private lemma HR_f0_sq (hL : 0 < L) (γ : Occ) (F : Finset Idx)
    (hF : ∀ n, γ n ≠ 0 → n ∈ F) (hF' : ∀ n, γ (-n) ≠ 0 → n ∈ F) :
    ‖f0 V w ρ L γ‖ ^ 2 = (L ^ 3) ^ (γ 0) / (Nat.factorial (γ 0)) *
      ∏ n ∈ F, HR_phi V w ρ L n (γ n) (γ (-n)) := by
  rw [FRatio_f0, norm_mul, norm_mul, mul_pow, mul_pow]
  have hA : ‖((Real.sqrt ((L ^ 3) ^ (γ 0) / (Nat.factorial (γ 0))) : ℝ) : ℂ)‖ ^ 2 =
      (L ^ 3) ^ (γ 0) / (Nat.factorial (γ 0)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity)]
  have hB : ‖∏ n ∈ γ.support.filter (· ≠ 0), csqrt (lam V w ρ L n) ^ (γ n)‖ ^ 2 =
      ∏ n ∈ F, (if n ≠ 0 then |lam V w ρ L n| ^ (γ n) else 1) := by
    have e1 : ∀ n, ‖csqrt (lam V w ρ L n) ^ (γ n)‖ ^ 2 = |lam V w ρ L n| ^ (γ n) := by
      intro n
      rw [norm_pow, ← pow_mul, mul_comm, pow_mul, HR_norm_csqrt_sq]
    rw [norm_prod, ← Finset.prod_pow, Finset.prod_congr rfl (fun n _ => e1 n),
      Finset.prod_filter]
    refine Finset.prod_subset (fun n hn => hF n (Finsupp.mem_support_iff.1 hn)) ?_
    intro n _ hn
    rw [Finsupp.notMem_support_iff.1 hn]
    simp
  have hC : ‖FRatio_asym V w ρ L γ‖ ^ 2 =
      ∏ n ∈ F, (if inPL ρ L n ∧ max (γ n) (γ (-n)) = γ n + 1 then
        |4 * ((max (γ n) (γ (-n)) : ℕ) : ℝ) * lam V w ρ L n / L ^ 3| else 1) := by
    unfold FRatio_asym alphaStar
    rw [norm_prod, ← Finset.prod_pow, Finset.prod_congr rfl (fun n _ => HR_norm_csqrt_sq _),
      Finset.prod_filter]
    refine Finset.prod_subset ?_ ?_
    · intro u hu
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hu
      exact hF' _ (by rw [neg_neg]; exact Finsupp.mem_support_iff.1 ha)
    · intro u _ hu
      have h0 : γ (-u) = 0 := by
        by_contra hc
        exact hu (Finset.mem_image.2 ⟨-u, Finsupp.mem_support_iff.2 hc, neg_neg u⟩)
      simp [h0]
  rw [hA, hB, hC, mul_assoc, ← Finset.prod_mul_distrib]
  rfl

private lemma HR_F_mem (T : Finset Idx) {n : Idx} (h : n ∈ T ∨ -n ∈ T) :
    n ∈ T ∪ T.image Neg.neg := by
  rcases h with h | h
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨-n, h, neg_neg n⟩)

private lemma HR_pow_leg (x : ℝ) (a : ℕ) (p p' : Prop) [Decidable p] [Decidable p'] :
    x ^ (a + (if p then 1 else 0) + (if p' then 1 else 0)) =
      x ^ a * ((if p then x else 1) * (if p' then x else 1)) := by
  split_ifs <;> ring

/-- `|f(𝓐^q γ)|² = |f(γ)|² γ(0)(γ(0)-1)|Λ|^{-2}|λ_q||λ_{-q}|` for `q ∈ P_{H,c}`. -/
private lemma HR_strict_step (hρ : 0 < ρ) (hL : 0 < L) {γ : Occ} {q : Idx}
    (hq : inPHc ρ L kc q) (h2 : 2 ≤ γ 0) :
    ‖f0 V w ρ L (strictPair q γ)‖ ^ 2 = ‖f0 V w ρ L γ‖ ^ 2 *
      ((γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (L ^ 3) ^ 2 *
        (|lam V w ρ L q| * |lam V w ρ L (-q)|)) := by
  have hq0 : q ≠ 0 := Regions_PH_ne_zero hρ hq.1
  have hq' : inPHc ρ L kc (-q) := HR_PHc_neg.2 hq
  have hqq : q ≠ -q := HR_ne_neg hq0
  set β := strictPair q γ with hβ
  have hval : ∀ n, β n = γ n - (if n = 0 then 2 else 0) + (if n = q then 1 else 0) +
      (if n = -q then 1 else 0) := fun n => MBasic_strictPair_apply q γ n
  set T : Finset Idx := γ.support ∪ {q, -q} with hT
  have hTm : ∀ n, (γ n ≠ 0 ∨ n = q ∨ n = -q) → n ∈ T := by
    intro n h
    rcases h with h | h | h
    · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.2 h)
    · simp [hT, h]
    · simp [hT, h]
  have hβT : ∀ n, β n ≠ 0 → n ∈ T := by
    intro n hn
    refine hTm n ?_
    by_contra hc
    push Not at hc
    apply hn
    rw [hval n]
    simp [hc.1, hc.2.1, hc.2.2]
  have hγT : ∀ n, γ n ≠ 0 → n ∈ T := fun n h => hTm n (Or.inl h)
  set F := T ∪ T.image Neg.neg with hF
  rw [HR_f0_sq hL β F (fun n h => HR_F_mem T (Or.inl (hβT n h)))
      (fun n h => HR_F_mem T (Or.inr (hβT _ h))),
    HR_f0_sq hL γ F (fun n h => HR_F_mem T (Or.inl (hγT n h)))
      (fun n h => HR_F_mem T (Or.inr (hγT _ h)))]
  set ψ : Idx → ℝ := fun n =>
    (if n = q then |lam V w ρ L n| else 1) * (if n = -q then |lam V w ρ L n| else 1) with hψ
  have hidx : ∀ n ∈ F, HR_phi V w ρ L n (β n) (β (-n)) =
      HR_phi V w ρ L n (γ n) (γ (-n)) * ψ n := by
    intro n _
    by_cases hn0 : n = 0
    · subst hn0
      have e1 : (0 : Idx) ≠ q := fun e => hq0 e.symm
      have e2 : (0 : Idx) ≠ -q := fun e => hq0 (neg_eq_zero.1 e.symm)
      simp only [HR_phi_zero hρ, hψ, e1, e2, ↓reduceIte, mul_one]
    by_cases hnc : inPHc ρ L kc n
    · have hnPL : ¬ inPL ρ L n := fun h => HR_not_PHc_PL hρ h hnc
      rw [HR_phi_notPL hn0 hnPL, HR_phi_notPL hn0 hnPL, hval n]
      simp only [hn0, ↓reduceIte, Nat.sub_zero, hψ]
      exact HR_pow_leg _ _ _ _
    · have e1 : n ≠ q := fun e => hnc (e ▸ hq)
      have e2 : n ≠ -q := fun e => hnc (e ▸ hq')
      have e3 : -n ≠ q := fun e => hnc (by rw [← neg_neg n, e]; exact hq')
      have e4 : -n ≠ -q := fun e => e1 (neg_injective e)
      have e5 : -n ≠ 0 := neg_ne_zero.2 hn0
      have b1 : β n = γ n := by rw [hval n]; simp [hn0, e1, e2]
      have b2 : β (-n) = γ (-n) := by rw [hval (-n)]; simp [e3, e4, e5]
      rw [b1, b2]
      simp [hψ, e1, e2]
  have hprod : ∏ n ∈ F, ψ n = |lam V w ρ L q| * |lam V w ρ L (-q)| := by
    have m1 : q ∈ F := HR_F_mem T (Or.inl (hTm q (Or.inr (Or.inl rfl))))
    have m2 : -q ∈ F := HR_F_mem T (Or.inl (hTm (-q) (Or.inr (Or.inr rfl))))
    rw [hψ, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp [m1, m2]
  rw [Finset.prod_congr rfl hidx, Finset.prod_mul_distrib, hprod]
  obtain ⟨m, hm⟩ : ∃ m, γ 0 = m + 2 := ⟨γ 0 - 2, by omega⟩
  have hβ0 : β 0 = m := by
    rw [hval 0]
    have e1 : (0 : Idx) ≠ q := fun e => hq0 e.symm
    have e2 : (0 : Idx) ≠ -q := fun e => hq0 (neg_eq_zero.1 e.symm)
    simp [e1, e2, hm]
  rw [hβ0, hm, Nat.factorial_succ, Nat.factorial_succ]
  have hL3 : (L ^ 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- `|f(𝓐^{u}_{q,q'} γ)|² = |f(γ)|² γ(0)|Λ|^{-1}|λ_q||λ_{q'}| · 4γ(u)/|Λ|` for `q, q' ∈ P_{H,c}`,
`u ∈ P_L`, `γ(u) = γ(-u) ≥ 1`. -/
private lemma HR_soft_step (hρ : 0 < ρ) (hL : 0 < L) {γ : Occ} {u q q' : Idx}
    (hq : inPHc ρ L kc q) (hq' : inPHc ρ L kc q') (hu : inPL ρ L u) (h0 : 1 ≤ γ 0)
    (h1 : 1 ≤ γ u) (hsym : γ u = γ (-u)) :
    ‖f0 V w ρ L (softPair u q q' γ)‖ ^ 2 = ‖f0 V w ρ L γ‖ ^ 2 *
      ((γ 0 : ℝ) / L ^ 3 * (|lam V w ρ L q| * |lam V w ρ L q'|) *
        (4 * (γ u : ℝ) / L ^ 3)) := by
  have hq0 : q ≠ 0 := Regions_PH_ne_zero hρ hq.1
  have hq0' : q' ≠ 0 := Regions_PH_ne_zero hρ hq'.1
  have hu0 : u ≠ 0 := Regions_PL_ne_zero hρ hu
  have huc : ¬ inPHc ρ L kc u := HR_not_PHc_PL hρ hu
  have huc' : ¬ inPHc ρ L kc (-u) := HR_not_PHc_PL hρ (Regions_PL_neg.2 hu)
  have hqu : q ≠ u := fun e => huc (e ▸ hq)
  have hqu' : q' ≠ u := fun e => huc (e ▸ hq')
  have hqnu : q ≠ -u := fun e => huc' (e ▸ hq)
  have hqnu' : q' ≠ -u := fun e => huc' (e ▸ hq')
  have huu : u ≠ -u := HR_ne_neg hu0
  set β := softPair u q q' γ with hβ
  have hval : ∀ n, β n = γ n - (if n = 0 then 1 else 0) - (if n = u then 1 else 0) +
      (if n = q then 1 else 0) + (if n = q' then 1 else 0) :=
    fun n => MBasic_softPair_apply u q q' γ n
  set T : Finset Idx := γ.support ∪ {q, q'} with hT
  have hTm : ∀ n, (γ n ≠ 0 ∨ n = q ∨ n = q') → n ∈ T := by
    intro n h
    rcases h with h | h | h
    · exact Finset.mem_union_left _ (Finsupp.mem_support_iff.2 h)
    · simp [hT, h]
    · simp [hT, h]
  have hβT : ∀ n, β n ≠ 0 → n ∈ T := by
    intro n hn
    refine hTm n ?_
    by_contra hc
    push Not at hc
    apply hn
    rw [hval n]
    simp [hc.1, hc.2.1, hc.2.2]
  have hγT : ∀ n, γ n ≠ 0 → n ∈ T := fun n h => hTm n (Or.inl h)
  set F := T ∪ T.image Neg.neg with hF
  rw [HR_f0_sq hL β F (fun n h => HR_F_mem T (Or.inl (hβT n h)))
      (fun n h => HR_F_mem T (Or.inr (hβT _ h))),
    HR_f0_sq hL γ F (fun n h => HR_F_mem T (Or.inl (hγT n h)))
      (fun n h => HR_F_mem T (Or.inr (hγT _ h)))]
  set ψ : Idx → ℝ := fun n =>
    (if n = q then |lam V w ρ L n| else 1) * (if n = q' then |lam V w ρ L n| else 1) *
      (if n = u then 4 * (γ u : ℝ) / L ^ 3 else 1) with hψ
  have hidx : ∀ n ∈ F, HR_phi V w ρ L n (β n) (β (-n)) =
      HR_phi V w ρ L n (γ n) (γ (-n)) * ψ n := by
    intro n _
    by_cases hn0 : n = 0
    · subst hn0
      have e1 : (0 : Idx) ≠ q := fun e => hq0 e.symm
      have e2 : (0 : Idx) ≠ q' := fun e => hq0' e.symm
      have e3 : (0 : Idx) ≠ u := fun e => hu0 e.symm
      simp only [HR_phi_zero hρ, hψ, e1, e2, e3, ↓reduceIte, mul_one]
    by_cases hnc : inPHc ρ L kc n
    · have hnPL : ¬ inPL ρ L n := fun h => HR_not_PHc_PL hρ h hnc
      have hnu : n ≠ u := fun e => huc (e ▸ hnc)
      rw [HR_phi_notPL hn0 hnPL, HR_phi_notPL hn0 hnPL, hval n]
      simp only [hn0, hnu, ↓reduceIte, Nat.sub_zero, hψ, mul_one]
      exact HR_pow_leg _ _ _ _
    by_cases hnu : n = u
    · subst hnu
      have b1 : β n = γ n - 1 := by rw [hval n]; simp [hn0, hqu.symm, hqu'.symm]
      have b2 : β (-n) = γ (-n) := by
        rw [hval (-n)]
        simp [neg_ne_zero.2 hn0, huu.symm, hqnu.symm, hqnu'.symm]
      rw [b1, b2]
      obtain ⟨k, hk⟩ : ∃ k, γ n = k + 1 := ⟨γ n - 1, by omega⟩
      have m1 : max (γ n - 1) (γ (-n)) = γ n - 1 + 1 := by omega
      have m2 : ¬ max (γ n) (γ (-n)) = γ n + 1 := by omega
      simp only [HR_phi, hn0, hu, m1, m2, ne_eq, not_false_eq_true, ↓reduceIte, and_self,
        and_false, mul_one, hψ, hqu.symm, hqu'.symm, one_mul]
      rw [hk, Nat.add_sub_cancel]
      rw [abs_div, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < L ^ 3)]
      push_cast
      rw [abs_of_pos (by positivity : (0 : ℝ) < 4), abs_of_pos (by positivity : (0 : ℝ) < k + 1)]
      ring
    by_cases hnu' : n = -u
    · subst hnu'
      have b1 : β (-u) = γ (-u) := by
        rw [hval (-u)]
        simp [neg_ne_zero.2 hu0, huu.symm, hqnu.symm, hqnu'.symm]
      have b2 : β (-(-u)) = γ u - 1 := by
        rw [neg_neg, hval u]
        simp [hu0, hqu.symm, hqu'.symm]
      rw [b1, b2, neg_neg]
      have m1 : ¬ max (γ (-u)) (γ u - 1) = γ (-u) + 1 := by omega
      have m2 : ¬ max (γ (-u)) (γ u) = γ (-u) + 1 := by omega
      simp only [HR_phi, m1, m2, and_false, ↓reduceIte, hψ, hqnu.symm, hqnu'.symm, huu.symm,
        mul_one]
    · have e1 : n ≠ q := fun e => hnc (e ▸ hq)
      have e2 : n ≠ q' := fun e => hnc (e ▸ hq')
      have hnc' : ¬ inPHc ρ L kc (-n) := HR_PHc_neg.not.2 hnc
      have e3 : -n ≠ q := fun e => hnc' (e ▸ hq)
      have e4 : -n ≠ q' := fun e => hnc' (e ▸ hq')
      have e5 : -n ≠ 0 := neg_ne_zero.2 hn0
      have e6 : -n ≠ u := fun e => hnu' (by rw [← e, neg_neg])
      have b1 : β n = γ n := by rw [hval n]; simp [hn0, hnu, e1, e2]
      have b2 : β (-n) = γ (-n) := by rw [hval (-n)]; simp [e3, e4, e5, e6]
      rw [b1, b2]
      simp [hψ, e1, e2, hnu]
  have hprod : ∏ n ∈ F, ψ n =
      |lam V w ρ L q| * |lam V w ρ L q'| * (4 * (γ u : ℝ) / L ^ 3) := by
    have m1 : q ∈ F := HR_F_mem T (Or.inl (hTm q (Or.inr (Or.inl rfl))))
    have m2 : q' ∈ F := HR_F_mem T (Or.inl (hTm q' (Or.inr (Or.inr rfl))))
    have m3 : u ∈ F := HR_F_mem T (Or.inl (hTm u (Or.inl (by omega))))
    rw [hψ, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_ite_eq',
      Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp [m1, m2, m3]
  rw [Finset.prod_congr rfl hidx, Finset.prod_mul_distrib, hprod]
  obtain ⟨m, hm⟩ : ∃ m, γ 0 = m + 1 := ⟨γ 0 - 1, by omega⟩
  have hβ0 : β 0 = m := by
    rw [hval 0]
    have e1 : (0 : Idx) ≠ q := fun e => hq0 e.symm
    have e2 : (0 : Idx) ≠ q' := fun e => hq0' e.symm
    have e3 : (0 : Idx) ≠ u := fun e => hu0 e.symm
    simp [e1, e2, e3, hm]
  rw [hβ0, hm, Nat.factorial_succ]
  have hL3 : (L ^ 3) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- Both states in `M`: a bound on `|f|²` is a bound on `|Ψ|²`. -/
private lemma HR_psi_le {β γ : Occ} (hβ : InM (rhoN N) (LN N) kc N β)
    (hγ : InM (rhoN N) (LN N) kc N γ) {c : ℝ}
    (h : ‖f0 V w (rhoN N) (LN N) β‖ ^ 2 ≤ ‖f0 V w (rhoN N) (LN N) γ‖ ^ 2 * c) :
    ‖trialState V w kc N β‖ ^ 2 ≤ ‖trialState V w kc N γ‖ ^ 2 * c := by
  unfold trialState
  simp only [hβ, hγ, ↓reduceIte]
  rw [norm_mul, norm_mul, mul_pow, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (by positivity)

private lemma HR_rhoN_LN (hN : 1 ≤ N) : rhoN N * LN N ^ 3 = N ∧ 0 < rhoN N ∧ 0 < LN N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 < rhoN N := Real.rpow_pos_of_pos hNpos _
  have hL : LN N = (N : ℝ) ^ (25 / 51 : ℝ) := by
    rw [LN, rhoN, ← Real.rpow_mul hNpos.le]
    norm_num
  refine ⟨?_, hρ, ?_⟩
  · rw [hL, rhoN, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    norm_num
  · rw [hL]
    exact Real.rpow_pos_of_pos hNpos _

private lemma HR_le_num {α : Occ} (hρ : 0 < ρ) (h : InM ρ L kc N α) : α 0 ≤ N := by
  have := MBasic_num hρ h
  rw [HR_num_split] at this
  omega

private lemma HR_ops_tot (hρ : 0 < ρ) {α : Occ} {ops : List (Idx × Idx)}
    (h : HR_Legs ρ L kc ops) {u : Idx} (hu : inPL ρ L u) (hm : u ∉ HR_S ops) :
    Chi_ops ops α u = α u := by
  rw [HR_ops_out α ops (HR_g_out h (HR_not_PHc_PL hρ hu)),
    HR_D_not_mem (Regions_PL_ne_zero hρ hu) ops hm]
  simp

/-- (11.13) by induction on the number of factors. -/
private lemma HR_weight_ind (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (kc : ℝ)
    (hN : 1 ≤ N) {α : Occ} (hα : InM (rhoN N) (LN N) kc N α) :
    ∀ (ops : List (Idx × Idx)) (s t : ℕ), (∀ o ∈ ops, HR_C (rhoN N) (LN N) kc α o) →
      (HR_S ops).Pairwise Legs_pm → HR_W ops ≤ α 0 → (HardRep.sums ops).count 0 = s →
      ops.length = s + t →
      ‖trialState V w kc N (Chi_ops ops α)‖ ^ 2 ≤
        ‖trialState V w kc N α‖ ^ 2 * HardRep.wt V w N s t
  | [], s, t, _, _, _, hs, ht => by
    simp only [HardRep.sums, List.map_nil, Multiset.coe_count, List.count_nil] at hs
    simp only [List.length_nil] at ht
    subst hs
    obtain rfl : t = 0 := by omega
    simp [HardRep.wt, Chi_ops]
  | (q, q') :: ops, s, t, h1, h2, h3, hs, ht => by
    obtain ⟨hNρ, hρ, hL⟩ := HR_rhoN_LN hN
    have hg := scat_g0_pos hV hw
    have hG : 0 ≤ g0 V w / epsP (rhoN N) ^ 2 := by positivity
    have hlam : ∀ n, inPHc (rhoN N) (LN N) kc n →
        |lam V w (rhoN N) (LN N) n| ≤ g0 V w / epsP (rhoN N) ^ 2 :=
      fun n hn => scat_lam_PH hV hw _ hρ _ n hn.1
    have h1' : ∀ o ∈ ops, HR_C (rhoN N) (LN N) kc α o :=
      fun o ho => h1 o (List.mem_cons_of_mem _ ho)
    have h2' := HR_S_pairwise_tail h2
    have h3c := h3
    rw [HR_W_cons] at h3c
    have hW' : HR_W ops ≤ α 0 := by split_ifs at h3c <;> omega
    have hγ : InM (rhoN N) (LN N) kc N (Chi_ops ops α) := HR_inM hρ hα ops h1' h2' hW'
    have hβ : InM (rhoN N) (LN N) kc N (Chi_ops ((q, q') :: ops) α) := HR_inM hρ hα _ h1 h2 h3
    have hγ0 := HR_ops_zero hρ (HR_Legs_of_C h1') α
    have hγN := HR_le_num hρ hγ
    have hcnt := HR_count_cons (q, q') ops
    have hcle := HR_count_le ops
    simp only [List.length_cons] at ht
    obtain ⟨hq, hq', hor⟩ := h1 (q, q') List.mem_cons_self
    change InM (rhoN N) (LN N) kc N (Chi_pairOp q q' (Chi_ops ops α)) at hβ
    change ‖trialState V w kc N (Chi_pairOp q q' (Chi_ops ops α))‖ ^ 2 ≤ _
    unfold Chi_pairOp at hβ ⊢
    set γ := Chi_ops ops α with hγdef
    have hNN : ((γ 0 : ℕ) : ℝ) ≤ N := by exact_mod_cast hγN
    by_cases hs0 : q + q' = 0
    · simp only [hs0, ↓reduceIte] at h3c hcnt hβ ⊢
      have hq'eq : q' = -q := eq_neg_of_add_eq_zero_right hs0
      have ih := HR_weight_ind hV hw kc hN hα ops ((HardRep.sums ops).count 0) t h1' h2' hW' rfl
        (by omega)
      have h2γ : 2 ≤ γ 0 := by omega
      have h2γR : (2 : ℝ) ≤ γ 0 := by exact_mod_cast h2γ
      have hfac : (γ 0 : ℝ) * ((γ 0 : ℝ) - 1) / (LN N ^ 3) ^ 2 ≤ rhoN N ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have e : rhoN N ^ 2 * (LN N ^ 3) ^ 2 = (N : ℝ) ^ 2 := by rw [← hNρ]; ring
        nlinarith
      have hstep := HR_psi_le (V := V) (w := w) hβ hγ (c := rhoN N ^ 2 *
          (g0 V w / epsP (rhoN N) ^ 2) ^ 2) (by
        rw [HR_strict_step hρ hL hq h2γ]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [sq (g0 V w / epsP (rhoN N) ^ 2)]
        refine mul_le_mul hfac (mul_le_mul (hlam q hq) (hlam (-q) (HR_PHc_neg.2 hq))
          (abs_nonneg _) hG) (by positivity) (sq_nonneg _))
      calc _ ≤ _ := hstep
        _ ≤ ‖trialState V w kc N α‖ ^ 2 * HardRep.wt V w N ((HardRep.sums ops).count 0) t *
            (rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) ^ 2) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ = _ := by
          rw [← hs, hcnt]
          unfold HardRep.wt
          ring
    · simp only [hs0, ↓reduceIte] at h3c hcnt hβ ⊢
      obtain ⟨hPL, hu1, husym⟩ := hor.resolve_left hs0
      obtain ⟨hn1, hn2⟩ := HR_S_not_mem_head (o := (q, q')) hs0 h2
      have e1 : γ (q + q') = α (q + q') := HR_ops_tot hρ (HR_Legs_of_C h1') hPL hn1
      have e2 : γ (-(q + q')) = α (-(q + q')) :=
        HR_ops_tot hρ (HR_Legs_of_C h1') (Regions_PL_neg.2 hPL) hn2
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have ih := HR_weight_ind hV hw kc hN hα ops s t' h1' h2' hW' (by omega) (by omega)
      have h1γ : 1 ≤ γ 0 := by omega
      have hu1γ : 1 ≤ γ (q + q') := by rw [e1]; exact hu1
      have hsymγ : γ (q + q') = γ (-(q + q')) := by rw [e1, e2]; exact husym
      have hmcγ : (γ (q + q') : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := by
        have := MStar_PL_ceil hρ hγ hPL
        unfold alphaStar at this
        exact_mod_cast (le_max_left _ _).trans this
      have hfac : (γ 0 : ℝ) / LN N ^ 3 ≤ rhoN N := by
        rw [div_le_iff₀ (by positivity), hNρ]
        exact hNN
      have hfac2 : 4 * (γ (q + q') : ℝ) / LN N ^ 3 ≤ 4 * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3 := by
        gcongr
      have hstep := HR_psi_le (V := V) (w := w) hβ hγ (c := rhoN N *
          (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * (4 * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3)) (by
        rw [HR_soft_step hρ hL hq hq' hPL h1γ hu1γ hsymγ]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [sq (g0 V w / epsP (rhoN N) ^ 2)]
        refine mul_le_mul (mul_le_mul hfac (mul_le_mul (hlam q hq) (hlam q' hq')
          (abs_nonneg _) hG) (by positivity) hρ.le) hfac2 (by positivity) (by positivity))
      calc _ ≤ _ := hstep
        _ ≤ ‖trialState V w kc N α‖ ^ 2 * HardRep.wt V w N s t' *
            (rhoN N * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 *
              (4 * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3)) :=
          mul_le_mul_of_nonneg_right ih (by positivity)
        _ = _ := by
          unfold HardRep.wt
          ring

end HardRepWeight

/-- The factors of (11.5) [elementform2] commute and every sub-product stays in `M`: if
`D ++ C` is a reordering of `ops`, then `C` applied to `α` is again a base for `D`, and
`D` applied after `C` gives the product over `ops`. -/
theorem HardRep_split {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {α : Occ}
    {ops C D : List (Idx × Idx)} (h : HardRep.Rep ρ L kc N α ops) (hp : (D ++ C).Perm ops) :
    HardRep.Rep ρ L kc N (Chi_ops C α) D ∧ Chi_ops D (Chi_ops C α) = Chi_ops ops α := by
  obtain ⟨hα, h1, h2, h3⟩ := h
  change ∀ o ∈ ops, HR_C ρ L kc α o at h1
  change (HR_S ops).Pairwise Legs_pm at h2
  change HR_W ops ≤ α 0 at h3
  have hsub : ∀ o ∈ D ++ C, o ∈ ops := fun o ho => hp.subset ho
  have h2' : (HR_S (D ++ C)).Pairwise Legs_pm :=
    ((HR_S_perm hp).pairwise_iff HR_pm_symm).2 h2
  rw [HR_S_append, List.pairwise_append] at h2'
  obtain ⟨hD, hC, hDC⟩ := h2'
  have hW : HR_W D + HR_W C ≤ α 0 := by rw [← HR_W_append, HR_W_perm hp]; exact h3
  have hC1 : ∀ o ∈ C, HR_C ρ L kc α o := fun o ho => h1 o (hsub o (List.mem_append_right _ ho))
  have hD1 : ∀ o ∈ D, HR_C ρ L kc α o := fun o ho => h1 o (hsub o (List.mem_append_left _ ho))
  have h0 := HR_ops_zero hρ (HR_Legs_of_C hC1) α
  refine ⟨⟨HR_inM hρ hα C hC1 hC (by omega), ?_, hD, ?_⟩, ?_⟩
  · intro o ho
    obtain ⟨ho1, ho2, hor⟩ := hD1 o ho
    refine ⟨ho1, ho2, hor.imp_right fun ⟨hPL, hu1, husym⟩ => ?_⟩
    have hs : o.1 + o.2 ≠ 0 := Regions_PL_ne_zero hρ hPL
    have hmem : o.1 + o.2 ∈ HR_S D :=
      List.mem_filter.2 ⟨List.mem_map.2 ⟨o, ho, rfl⟩, by simpa using hs⟩
    have hn1 : o.1 + o.2 ∉ HR_S C := fun hm => (hDC _ hmem _ hm).1 rfl
    have hn2 : -(o.1 + o.2) ∉ HR_S C := fun hm => (hDC _ hmem _ hm).2 (neg_neg _).symm
    have e1 : Chi_ops C α (o.1 + o.2) = α (o.1 + o.2) := by
      rw [HR_ops_out α C (HR_g_out (HR_Legs_of_C hC1) (HR_not_PHc_PL hρ hPL)),
        HR_D_not_mem hs C hn1]
      simp
    have e2 : Chi_ops C α (-(o.1 + o.2)) = α (-(o.1 + o.2)) := by
      rw [HR_ops_out α C (HR_g_out (HR_Legs_of_C hC1)
        (HR_not_PHc_PL hρ (Regions_PL_neg.2 hPL))), HR_D_not_mem (neg_ne_zero.2 hs) C hn2]
      simp
    exact ⟨hPL, by rw [e1]; exact hu1, by rw [e1, e2]; exact husym⟩
  · change HR_W D ≤ Chi_ops C α 0
    rw [h0]
    omega
  · rw [HR_ops_append, HR_ops_perm hρ (HR_Legs_of_C h1) hp]

/-- The base `α` of Proposition 11.1 [propchi] is determined by `χ` off `P_{H,c}`: two
products (11.5) [elementform2] on symmetric bases vanishing on `P_{H,c}` that agree off
`P_{H,c}` have the same base and the same total momenta (Lemma 11.2 [thehardestlemma], the
same `α`, `s`, `{v_1, …, v_t}` for `β` and `γ`). -/
theorem HardRep_same {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {α α' : Occ}
    {ops ops' : List (Idx × Idx)} (h : HardRep.Rep ρ L kc N α ops)
    (h' : HardRep.Rep ρ L kc N α' ops') (hs : ∀ n, α n = α (-n)) (hs' : ∀ n, α' n = α' (-n))
    (hz : ∀ n, inPHc ρ L kc n → α n = 0) (hz' : ∀ n, inPHc ρ L kc n → α' n = 0)
    (hoff : ∀ n, ¬ inPHc ρ L kc n → Chi_ops ops α n = Chi_ops ops' α' n) :
    α = α' ∧ HardRep.sums ops = HardRep.sums ops' := by
  obtain ⟨hα, h1, h2, h3⟩ := h
  obtain ⟨hα', h1', h2', h3'⟩ := h'
  change ∀ o ∈ ops, HR_C ρ L kc α o at h1
  change (HR_S ops).Pairwise Legs_pm at h2
  change HR_W ops ≤ α 0 at h3
  change ∀ o ∈ ops', HR_C ρ L kc α' o at h1'
  change (HR_S ops').Pairwise Legs_pm at h2'
  change HR_W ops' ≤ α' 0 at h3'
  have hS : ∀ n, n ∈ HR_S ops ↔ n ∈ HR_S ops' := by
    intro n
    by_cases hn : n = 0
    · exact iff_of_false (fun hm => (HR_S_mem h1 hm).1 hn) (fun hm => (HR_S_mem h1' hm).1 hn)
    by_cases hnc : inPHc ρ L kc n
    · exact iff_of_false (fun hm => HR_not_PHc_PL hρ (HR_S_mem h1 hm).2.1 hnc)
        (fun hm => HR_not_PHc_PL hρ (HR_S_mem h1' hm).2.1 hnc)
    · rw [HR_char hs h1 h2 hn hnc, HR_char hs' h1' h2' hn hnc, hoff n hnc,
        hoff (-n) (HR_PHc_neg.not.2 hnc)]
  have hne : ∀ n, n ≠ 0 → α n = α' n := by
    intro n hn
    by_cases hnc : inPHc ρ L kc n
    · rw [hz n hnc, hz' n hnc]
    · have v1 := HR_val h1 h2 hn hnc
      have v2 := HR_val h1' h2' hn hnc
      have e := hoff n hnc
      by_cases hm : n ∈ HR_S ops
      · have hm' := (hS n).1 hm
        have a1 := (HR_S_mem h1 hm).2.2.1
        have a2 := (HR_S_mem h1' hm').2.2.1
        simp only [hm, hm', ↓reduceIte] at v1 v2
        omega
      · have hm' : n ∉ HR_S ops' := fun x => hm ((hS n).2 x)
        simp only [hm, hm', ↓reduceIte] at v1 v2
        omega
  have h0 : α 0 = α' 0 := by
    have e1 := MBasic_num hρ hα
    have e2 := MBasic_num hρ hα'
    rw [HR_num_split] at e1 e2
    have : α.erase 0 = α'.erase 0 := by
      ext n
      by_cases hn : n = 0
      · subst hn
        simp
      · rw [Finsupp.erase_ne hn, Finsupp.erase_ne hn, hne n hn]
    rw [this] at e1
    omega
  have hαα : α = α' := Finsupp.ext fun n => if hn : n = 0 then hn ▸ h0 else hne n hn
  refine ⟨hαα, ?_⟩
  subst hαα
  have hW : HR_W ops = HR_W ops' := by
    have e := hoff 0 (HR_not_PHc_zero hρ)
    rw [HR_ops_zero hρ (HR_Legs_of_C h1), HR_ops_zero hρ (HR_Legs_of_C h1')] at e
    omega
  have hperm : (HR_S ops).Perm (HR_S ops') :=
    (List.perm_ext_iff_of_nodup (HR_S_nodup h2) (HR_S_nodup h2')).2 hS
  have hc : (ops.map (fun o => o.1 + o.2)).count 0 = (ops'.map (fun o => o.1 + o.2)).count 0 := by
    have a := HR_W_eq ops
    have b := HR_W_eq ops'
    have c := hperm.length_eq
    omega
  unfold HardRep.sums
  rw [Multiset.coe_eq_coe, List.perm_iff_count]
  intro n
  by_cases hn : n = 0
  · subst hn
    exact hc
  · have := hperm.count_eq n
    unfold HR_S at this
    rwa [List.count_filter (by simpa using hn), List.count_filter (by simpa using hn)] at this

/-- (11.13) with the exponent `2s + 2t` of `max |λ_k|`: for a product (11.5)
[elementform2] with `s` pairs of total momentum `0` and `t` others,
`|Ψ(β)|² ≤ |Ψ(α)|² ρ^{2s+t} (g₀ ε_H^{-2})^{2s+2t} (4 ⌈m_c⌉ / |Λ|)^t`. -/
theorem HardRep_weight {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {α : Occ} {ops : List (Idx × Idx)}
    (h : HardRep.Rep (rhoN N) (LN N) kc N α ops) {s t : ℕ}
    (hs : (HardRep.sums ops).count 0 = s) (ht : ops.length = s + t) :
    ‖trialState V w kc N (Chi_ops ops α)‖ ^ 2 ≤
      ‖trialState V w kc N α‖ ^ 2 * HardRep.wt V w N s t := by
  obtain ⟨hα, h1, h2, h3⟩ := h
  exact HR_weight_ind hV hw kc hN hα ops s t h1 h2 h3 hs ht

end LHYUpper
