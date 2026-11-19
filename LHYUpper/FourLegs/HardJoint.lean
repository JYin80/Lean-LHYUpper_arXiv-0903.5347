import LHYUpper.FourLegs.Defs
import LHYUpper.Riemann.Defs
import LHYUpper.TrialState.Chi
import LHYUpper.FourLegs.HardRep
import LHYUpper.FourLegs.HardGraph
import LHYUpper.FourLegs.HardBounds

/-!
# The joint representation of `β` and `γ` in Lemma 11.2 [thehardestlemma]

For the summands (11.3) [defnastk1234] of (11.2) [resulthardest], `β` and `γ` are products
(11.5) [elementform2] on one base `α` with the same total momenta and no common pair
((11.20) [112], (11.10) [stst] in a local form); the legs of `β` and `γ` form the graph of
(11.24) [temp4.178] with the exclusions of (11.26) [uboundl]; and the number
`N(α, s, {v_1, …, v_t})` of Lemma 11.2 obeys Lemma 11.3 [lem11.1], in a local form and in the
form (11.19) [0.025].
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

namespace HardJoint

/-- The unordered pairs `{q_i, q'_i}` of the factors of (11.5) [elementform2]. -/
def pairs (ops : List (Idx × Idx)) : Multiset (Sym2 Idx) := ↑(ops.map fun o => s(o.1, o.2))

/-- `N(α, s, {v_1, …, v_t})` of Lemma 11.2 [thehardestlemma], over the indices
`(k₁, k₂, k₁ - k₃, γ)` of (11.2) [resulthardest]: legs in `P_{H,c}` with (10.7)
[conditionk2], `β ∉ M(k₁, k₂)`, (11.3) [defnastk1234] with `β, γ ∈ M`, and `β`, `γ` products
(11.5) [elementform2] on `α` without a common pair, with total momenta `S`. -/
def NSet (ρ L kc : ℝ) (N : ℕ) (α : Occ) (S : Multiset Idx) : Set (Idx × Idx × Idx × Occ) :=
  {i | FourLegs.Cls.mem ρ L kc N .fourRest i ∧
    (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).1 ≠ 0 ∧
    InM ρ L kc N (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2 ∧
    InM ρ L kc N i.2.2.2 ∧
    ∃ B G : List (Idx × Idx), HardRep.Rep ρ L kc N α B ∧ HardRep.Rep ρ L kc N α G ∧
      (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2 = Chi_ops B α ∧
      i.2.2.2 = Chi_ops G α ∧ HardRep.sums B = S ∧ HardRep.sums G = S ∧
      ∀ p ∈ pairs B, p ∉ pairs G}

end HardJoint

section HardJointAux
variable {ρ L kc : ℝ} {N : ℕ}

/-- The number of particles that `𝓐_{o.1,o.2}` removes at `n`. -/
private def HJ_d (o : Idx × Idx) (n : Idx) : ℕ :=
  if o.1 + o.2 = 0 then (if n = 0 then 2 else 0)
  else (if n = 0 then 1 else 0) + (if n = o.1 + o.2 then 1 else 0)

/-- The number of particles that `𝓐_{o.1,o.2}` creates at `n`. -/
private def HJ_g (o : Idx × Idx) (n : Idx) : ℕ :=
  (if n = o.1 then 1 else 0) + (if n = o.2 then 1 else 0)

private def HJ_D (ops : List (Idx × Idx)) (n : Idx) : ℕ := (ops.map (fun o => HJ_d o n)).sum

private def HJ_G (ops : List (Idx × Idx)) (n : Idx) : ℕ := (ops.map (fun o => HJ_g o n)).sum

/-- Legs in `P_{H,c}`, total momentum `0` or in `P_L`. -/
private def HJ_Legs (ρ L kc : ℝ) (ops : List (Idx × Idx)) : Prop :=
  ∀ o ∈ ops, inPHc ρ L kc o.1 ∧ inPHc ρ L kc o.2 ∧ (o.1 + o.2 = 0 ∨ inPL ρ L (o.1 + o.2))

private lemma HJ_legs_of_rep {α : Occ} {ops : List (Idx × Idx)}
    (h : HardRep.Rep ρ L kc N α ops) : HJ_Legs ρ L kc ops :=
  fun o ho => ⟨(h.2.1 o ho).1, (h.2.1 o ho).2.1, (h.2.1 o ho).2.2.imp_right fun h => h.1⟩

private lemma HJ_D_cons (o : Idx × Idx) (ops : List (Idx × Idx)) (n : Idx) :
    HJ_D (o :: ops) n = HJ_d o n + HJ_D ops n := by
  simp [HJ_D]

private lemma HJ_G_cons (o : Idx × Idx) (ops : List (Idx × Idx)) (n : Idx) :
    HJ_G (o :: ops) n = HJ_g o n + HJ_G ops n := by
  simp [HJ_G]

private lemma HJ_pairOp_apply (q q' : Idx) (β : Occ) (n : Idx) :
    Chi_pairOp q q' β n = β n - HJ_d (q, q') n + HJ_g (q, q') n := by
  unfold Chi_pairOp HJ_d HJ_g
  by_cases hs : q + q' = 0
  · have hq' : q' = -q := eq_neg_of_add_eq_zero_right hs
    subst hq'
    simp only [hs, ↓reduceIte, MBasic_strictPair_apply]
    omega
  · simp only [hs, ↓reduceIte, MBasic_softPair_apply]
    omega

/-- Where no factor creates, the product only removes. -/
private lemma HJ_ops_out {n : Idx} (α : Occ) :
    ∀ ops : List (Idx × Idx), (∀ o ∈ ops, HJ_g o n = 0) → Chi_ops ops α n = α n - HJ_D ops n
  | [], _ => by simp [Chi_ops, HJ_D]
  | (q, q') :: ops, h => by
    change Chi_pairOp q q' (Chi_ops ops α) n = _
    rw [HJ_pairOp_apply, HJ_ops_out α ops (fun o ho => h o (List.mem_cons_of_mem _ ho)),
      h (q, q') List.mem_cons_self, HJ_D_cons]
    omega

/-- Where no factor removes, the product only creates. -/
private lemma HJ_ops_in {n : Idx} (α : Occ) :
    ∀ ops : List (Idx × Idx), (∀ o ∈ ops, HJ_d o n = 0) → Chi_ops ops α n = α n + HJ_G ops n
  | [], _ => by simp [Chi_ops, HJ_G]
  | (q, q') :: ops, h => by
    change Chi_pairOp q q' (Chi_ops ops α) n = _
    rw [HJ_pairOp_apply, HJ_ops_in α ops (fun o ho => h o (List.mem_cons_of_mem _ ho)),
      h (q, q') List.mem_cons_self, HJ_G_cons]
    omega

private lemma HJ_g_out {ops : List (Idx × Idx)} (h : HJ_Legs ρ L kc ops) {n : Idx}
    (hn : ¬ inPHc ρ L kc n) : ∀ o ∈ ops, HJ_g o n = 0 := by
  intro o ho
  obtain ⟨h1, h2, -⟩ := h o ho
  have e1 : n ≠ o.1 := fun e => hn (e ▸ h1)
  have e2 : n ≠ o.2 := fun e => hn (e ▸ h2)
  simp [HJ_g, e1, e2]

private lemma HJ_d_in (hρ : 0 < ρ) {ops : List (Idx × Idx)} (h : HJ_Legs ρ L kc ops) {n : Idx}
    (hn : inPHc ρ L kc n) : ∀ o ∈ ops, HJ_d o n = 0 := by
  intro o ho
  have h0 : n ≠ 0 := Regions_PH_ne_zero hρ hn.1
  by_cases hs : o.1 + o.2 = 0
  · simp [HJ_d, hs, h0]
  · have hPL := (h o ho).2.2.resolve_left hs
    have hu : n ≠ o.1 + o.2 := fun e => Regions_PL_PH hρ hPL (e ▸ hn.1)
    simp [HJ_d, hs, h0, hu]

/-- `HJ_d` as a function of the unordered pair. -/
private def HJ_ds (n : Idx) (p : Sym2 Idx) : ℕ :=
  if HardGraph.tot p = 0 then (if n = 0 then 2 else 0)
  else (if n = 0 then 1 else 0) + (if n = HardGraph.tot p then 1 else 0)

/-- `HJ_g` as a function of the unordered pair. -/
private def HJ_gs (n : Idx) : Sym2 Idx → ℕ :=
  Sym2.lift ⟨fun a b => (if n = a then 1 else 0) + (if n = b then 1 else 0),
    fun _ _ => add_comm _ _⟩

private lemma HJ_D_pairs (ops : List (Idx × Idx)) (n : Idx) :
    HJ_D ops n = ((HardJoint.pairs ops).map (HJ_ds n)).sum := by
  unfold HJ_D HardJoint.pairs
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_map]
  rfl

private lemma HJ_G_pairs (ops : List (Idx × Idx)) (n : Idx) :
    HJ_G ops n = ((HardJoint.pairs ops).map (HJ_gs n)).sum := by
  unfold HJ_G HardJoint.pairs
  rw [Multiset.map_coe, Multiset.sum_coe, List.map_map]
  rfl

private lemma HJ_legs_of_pairs {G G' : List (Idx × Idx)} (h : HJ_Legs ρ L kc G)
    (he : HardJoint.pairs G = HardJoint.pairs G') : HJ_Legs ρ L kc G' := by
  intro o ho
  have hm : s(o.1, o.2) ∈ HardJoint.pairs G := by
    rw [he]
    exact Multiset.mem_coe.2 (List.mem_map.2 ⟨o, ho, rfl⟩)
  obtain ⟨o', ho', he'⟩ := List.mem_map.1 (Multiset.mem_coe.1 hm)
  obtain ⟨h1, h2, h3⟩ := h o' ho'
  rcases Sym2.eq_iff.1 he' with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [← e1, ← e2]
    exact ⟨h1, h2, h3⟩
  · rw [← e1, ← e2, add_comm]
    exact ⟨h2, h1, h3⟩

/-- The product depends only on the multiset of unordered pairs of its factors. -/
private lemma HJ_ops_pairs (hρ : 0 < ρ) {G G' : List (Idx × Idx)} (h : HJ_Legs ρ L kc G)
    (he : HardJoint.pairs G = HardJoint.pairs G') (α : Occ) : Chi_ops G α = Chi_ops G' α := by
  have h' := HJ_legs_of_pairs h he
  ext n
  by_cases hn : inPHc ρ L kc n
  · rw [HJ_ops_in α G (HJ_d_in hρ h hn), HJ_ops_in α G' (HJ_d_in hρ h' hn), HJ_G_pairs,
      HJ_G_pairs, he]
  · rw [HJ_ops_out α G (HJ_g_out h hn), HJ_ops_out α G' (HJ_g_out h' hn), HJ_D_pairs,
      HJ_D_pairs, he]

private lemma HJ_pairOp_swap (a b : Idx) (β : Occ) : Chi_pairOp a b β = Chi_pairOp b a β := by
  unfold Chi_pairOp
  rw [add_comm b a]
  split_ifs with h
  · have hb : b = -a := eq_neg_of_add_eq_zero_right h
    subst hb
    unfold strictPair
    rw [neg_neg, add_right_comm]
  · unfold softPair
    rw [add_right_comm]

/-- A nonzero coefficient of `a†_p a†_q a_r a_s` on `|β⟩` means that nothing is truncated:
`α + δ_s + δ_r = β + δ_q + δ_p` pointwise for the resulting state `α`. -/
private lemma HJ_a4_id {p q r s : Idx} {β : Occ} (hne : (a4 p q r s β).1 ≠ 0) (n : Idx) :
    (a4 p q r s β).2 n + (if n = s then 1 else 0) + (if n = r then 1 else 0) =
      β n + (if n = q then 1 else 0) + (if n = p then 1 else 0) := by
  have hpos : 1 ≤ β s ∧ 1 ≤ ((β - Finsupp.single s 1 : Occ) r) := by
    simp only [a4] at hne
    rw [mul_ne_zero_iff, mul_ne_zero_iff, mul_ne_zero_iff] at hne
    obtain ⟨⟨⟨h1, h2⟩, -⟩, -⟩ := hne
    rw [Ne, Real.sqrt_eq_zero', not_le] at h1 h2
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  obtain ⟨h1, h2⟩ := hpos
  simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply] at h2
  simp only [a4, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
    Finsupp.single_apply, @eq_comm _ n]
  by_cases hs : s = n <;> by_cases hr : r = n <;> subst_vars <;> simp_all <;> omega

/-- Away from the four legs, `a†_p a†_q a_r a_s` does not change the occupation. -/
private lemma HJ_a4_off {p q r s n : Idx} (β : Occ) (hp : p ≠ n) (hq : q ≠ n) (hr : r ≠ n)
    (hs : s ≠ n) : (a4 p q r s β).2 n = β n := by
  simp [a4, Finsupp.single_apply, hp, hq, hr, hs]

private lemma HJ_count_pair (n a b : Idx) :
    Multiset.count n ({a, b} : Multiset Idx) =
      (if n = a then 1 else 0) + (if n = b then 1 else 0) := by
  rw [Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton]
  omega

private lemma HJ_count_legs (n : Idx) : ∀ B : List (Idx × Idx),
    (HardGraph.legs (HardJoint.pairs B)).count n = HJ_G B n
  | [] => by simp [HardGraph.legs, HardJoint.pairs, HJ_G]
  | o :: B => by
    have e : HardGraph.legs (HardJoint.pairs (o :: B)) =
        {o.1, o.2} + HardGraph.legs (HardJoint.pairs B) := by
      unfold HardGraph.legs HardJoint.pairs
      rw [List.map_cons, ← Multiset.cons_coe, Multiset.cons_bind]
      simp
    rw [e, Multiset.count_add, HJ_count_pair, HJ_count_legs n B, HJ_G_cons]
    rfl

private lemma HJ_G_out {ops : List (Idx × Idx)} (h : HJ_Legs ρ L kc ops) {n : Idx}
    (hn : ¬ inPHc ρ L kc n) : HJ_G ops n = 0 := by
  unfold HJ_G
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
    exact HJ_g_out h hn o ho

/-- The list of the representatives of a multiset of unordered pairs has these pairs. -/
private lemma HJ_pairs_out (P : Multiset (Sym2 Idx)) :
    HardJoint.pairs (P.toList.map fun p : Sym2 Idx => (Quot.out p : Idx × Idx)) = P := by
  unfold HardJoint.pairs
  rw [List.map_map]
  conv_rhs => rw [← Multiset.coe_toList P]
  congr 1
  conv_rhs => rw [← List.map_id P.toList]
  refine List.map_congr_left fun p _ => ?_
  exact Quot.out_eq p

/-- A product (11.5) [elementform2] lies in `M`. -/
private lemma HJ_inM (hρ : 0 < ρ) {α : Occ} {B : List (Idx × Idx)}
    (h : HardRep.Rep ρ L kc N α B) : InM ρ L kc N (Chi_ops B α) :=
  (HardRep_split hρ h (C := B) (D := []) (by simp)).1.1

/-- A pair `{a, b}` with `a + b ≠ 0` of a product (11.5) [elementform2] can be applied last:
the product is `𝓐^{a+b}_{a,b} β'` with `β' ∈ M^s_{a+b}`. -/
private lemma HJ_soft (hρ : 0 < ρ) {α : Occ} {B : List (Idx × Idx)}
    (h : HardRep.Rep ρ L kc N α B) {a b : Idx} (hab : a + b ≠ 0)
    (hm : s(a, b) ∈ HardJoint.pairs B) :
    inPL ρ L (a + b) ∧
      ∃ β', InMuS ρ L kc N (a + b) β' ∧ softPair (a + b) a b β' = Chi_ops B α := by
  obtain ⟨o, ho, he⟩ := List.mem_map.1 (Multiset.mem_coe.1 hm)
  obtain ⟨hr, hc⟩ := HardRep_split hρ h (C := B.erase o) (D := [o])
    (List.perm_cons_erase ho).symm
  have hsum : o.1 + o.2 = a + b ∧ Chi_pairOp o.1 o.2 = Chi_pairOp a b := by
    rcases Sym2.eq_iff.1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]
      exact ⟨rfl, rfl⟩
    · rw [e1, e2, add_comm]
      exact ⟨rfl, funext fun β => HJ_pairOp_swap b a β⟩
  obtain ⟨hInM, h1, -, -⟩ := hr
  obtain ⟨-, -, hor⟩ := h1 o List.mem_cons_self
  rw [hsum.1] at hor
  obtain ⟨hPL, -, hsym⟩ := hor.resolve_left hab
  refine ⟨hPL, Chi_ops (B.erase o) α, ⟨hInM, hsym⟩, ?_⟩
  rw [← hc]
  change _ = Chi_pairOp o.1 o.2 _
  rw [hsum.2]
  unfold Chi_pairOp
  simp [hab]

/-- Removal of the common pairs of two products on one base, one pair at a time. -/
private lemma HJ_reduce (hρ : 0 < ρ) : ∀ (n : ℕ) (α : Occ) (B G : List (Idx × Idx)),
    B.length ≤ n → HardRep.Rep ρ L kc N α B → HardRep.Rep ρ L kc N α G →
    HardRep.sums B = HardRep.sums G →
    ∃ (α' : Occ) (B' G' : List (Idx × Idx)),
      HardRep.Rep ρ L kc N α' B' ∧ HardRep.Rep ρ L kc N α' G' ∧
      Chi_ops B α = Chi_ops B' α' ∧ Chi_ops G α = Chi_ops G' α' ∧
      HardRep.sums B' = HardRep.sums G' ∧ ∀ p ∈ HardJoint.pairs B', p ∉ HardJoint.pairs G'
  | n, α, B, G, hn, hB, hG, hs => by
    by_cases hc : ∃ p ∈ HardJoint.pairs B, p ∈ HardJoint.pairs G
    · obtain ⟨p, hpB, hpG⟩ := hc
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 (Multiset.mem_coe.1 hpB)
      obtain ⟨o', ho', he⟩ := List.mem_map.1 (Multiset.mem_coe.1 hpG)
      have hlen : B.length ≠ 0 := List.length_pos_of_mem ho |>.ne'
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      obtain ⟨hB', hcB⟩ := HardRep_split hρ hB (C := [o]) (D := B.erase o)
        ((List.perm_append_singleton o _).trans (List.perm_cons_erase ho).symm)
      obtain ⟨hG', hcG⟩ := HardRep_split hρ hG (C := [o']) (D := G.erase o')
        ((List.perm_append_singleton o' _).trans (List.perm_cons_erase ho').symm)
      have hsum : o'.1 + o'.2 = o.1 + o.2 ∧ Chi_ops [o'] α = Chi_ops [o] α := by
        change o'.1 + o'.2 = o.1 + o.2 ∧ Chi_pairOp o'.1 o'.2 α = Chi_pairOp o.1 o.2 α
        rcases Sym2.eq_iff.1 he with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]
          exact ⟨rfl, rfl⟩
        · rw [e1, e2, add_comm]
          exact ⟨rfl, HJ_pairOp_swap _ _ α⟩
      rw [hsum.2] at hG' hcG
      have hs' : HardRep.sums (B.erase o) = HardRep.sums (G.erase o') := by
        have eB : HardRep.sums B = (o.1 + o.2) ::ₘ HardRep.sums (B.erase o) := by
          unfold HardRep.sums
          rw [Multiset.cons_coe, Multiset.coe_eq_coe]
          exact (List.perm_cons_erase ho).map _
        have eG : HardRep.sums G = (o'.1 + o'.2) ::ₘ HardRep.sums (G.erase o') := by
          unfold HardRep.sums
          rw [Multiset.cons_coe, Multiset.coe_eq_coe]
          exact (List.perm_cons_erase ho').map _
        rw [eB, eG, hsum.1] at hs
        exact (Multiset.cons_inj_right _).1 hs
      have hlen' : (B.erase o).length ≤ m := by
        rw [List.length_erase_of_mem ho]
        omega
      obtain ⟨α', B', G', h1, h2, h3, h4, h5, h6⟩ :=
        HJ_reduce hρ m (Chi_ops [o] α) (B.erase o) (G.erase o') hlen' hB' hG' hs'
      exact ⟨α', B', G', h1, h2, by rw [← hcB, h3], by rw [← hcG, h4], h5, h6⟩
    · push Not at hc
      exact ⟨α, B, G, hB, hG, rfl, rfl, hs, hc⟩

end HardJointAux

/-- Lemma 11.2 [thehardestlemma], (11.20) [112]: for (11.3) [defnastk1234] with legs in
`P_{H,c}`, `β` and `γ` are products (11.5) [elementform2] on one `α` with the same total
momenta and no common pair ((11.10) [stst] in the local form). -/
theorem HardJoint_rep {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {k₁ k₂ k₃ k₄ : Idx} {γ : Occ}
    (hk : inPHc ρ L kc k₁ ∧ inPHc ρ L kc k₂ ∧ inPHc ρ L kc k₃ ∧ inPHc ρ L kc k₄)
    (hne : (a4 k₁ k₂ k₃ k₄ γ).1 ≠ 0)
    (hβ : InM ρ L kc N (a4 k₁ k₂ k₃ k₄ γ).2) (hγ : InM ρ L kc N γ) :
    ∃ (α : Occ) (B G : List (Idx × Idx)),
      HardRep.Rep ρ L kc N α B ∧ HardRep.Rep ρ L kc N α G ∧
      (a4 k₁ k₂ k₃ k₄ γ).2 = Chi_ops B α ∧ γ = Chi_ops G α ∧
      HardRep.sums B = HardRep.sums G ∧ ∀ p ∈ HardJoint.pairs B, p ∉ HardJoint.pairs G := by
  obtain ⟨α₁, B₁, hα₁, hs₁, hz₁, hl₁, hp₁, hw₁, he₁⟩ := Prop11_1 hρ hβ
  obtain ⟨α₂, G₁, hα₂, hs₂, hz₂, hl₂, hp₂, hw₂, he₂⟩ := Prop11_1 hρ hγ
  have hR₁ : HardRep.Rep ρ L kc N α₁ B₁ :=
    ⟨hα₁, fun o ho => ⟨(hl₁ o ho).1, (hl₁ o ho).2.1,
      (hl₁ o ho).2.2.imp_right fun h => ⟨h.1, h.2, hs₁ _⟩⟩, hp₁, hw₁⟩
  have hR₂ : HardRep.Rep ρ L kc N α₂ G₁ :=
    ⟨hα₂, fun o ho => ⟨(hl₂ o ho).1, (hl₂ o ho).2.1,
      (hl₂ o ho).2.2.imp_right fun h => ⟨h.1, h.2, hs₂ _⟩⟩, hp₂, hw₂⟩
  have hoff : ∀ n, ¬ inPHc ρ L kc n → Chi_ops B₁ α₁ n = Chi_ops G₁ α₂ n := by
    intro n hn
    rw [← he₁, ← he₂]
    obtain ⟨h1, h2, h3, h4⟩ := hk
    exact HJ_a4_off γ (fun e => hn (e ▸ h1)) (fun e => hn (e ▸ h2)) (fun e => hn (e ▸ h3))
      (fun e => hn (e ▸ h4))
  obtain ⟨rfl, hsum⟩ := HardRep_same hρ hR₁ hR₂ hs₁ hs₂ hz₁ hz₂ hoff
  obtain ⟨α, B, G, hB, hG, h3, h4, h5, h6⟩ := HJ_reduce hρ _ α₁ B₁ G₁ le_rfl hR₁ hR₂ hsum
  exact ⟨α, B, G, hB, hG, by rw [he₁, h3], by rw [he₂, h4], h5, h6⟩

/-- The graph of (11.24) [temp4.178]: the legs of `β` and `γ` are `{k₁, k₂} + P` and
`{k₃, k₄} + P`, and for `β ∉ M(k₁, k₂)` neither `{k₁, k₂}` is a pair of `β` nor `{k₃, k₄}` a
pair of `γ` ((11.26) [uboundl]). -/
theorem HardJoint_graph {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {k₁ k₂ k₃ k₄ : Idx} {α γ : Occ}
    {B G : List (Idx × Idx)}
    (hk : inPHc ρ L kc k₁ ∧ inPHc ρ L kc k₂ ∧ inPHc ρ L kc k₃ ∧ inPHc ρ L kc k₄)
    (hg : FourLegs.Gen ![k₁, k₂, k₃, k₄]) (hne : (a4 k₁ k₂ k₃ k₄ γ).1 ≠ 0)
    (hB : HardRep.Rep ρ L kc N α B) (hG : HardRep.Rep ρ L kc N α G)
    (hβ : (a4 k₁ k₂ k₃ k₄ γ).2 = Chi_ops B α) (hγ : γ = Chi_ops G α)
    (hrest : ¬ FourLegs.InMk ρ L kc N k₁ k₂ (a4 k₁ k₂ k₃ k₄ γ).2) :
    HardGraph.legs (HardJoint.pairs B) + {k₃, k₄} =
        HardGraph.legs (HardJoint.pairs G) + {k₁, k₂} ∧
      s(k₁, k₂) ∉ HardJoint.pairs B ∧ s(k₃, k₄) ∉ HardJoint.pairs G := by
  obtain ⟨hk₁, hk₂, hk₃, hk₄⟩ := hk
  have hlB := HJ_legs_of_rep hB
  have hlG := HJ_legs_of_rep hG
  have h12 : k₁ + k₂ ≠ 0 := fun e => (hg 0 1 (by decide)).2 (eq_neg_of_add_eq_zero_left e)
  have h34 : k₃ + k₄ ≠ 0 := fun e => (hg 2 3 (by decide)).2 (eq_neg_of_add_eq_zero_left e)
  have hβM : InM ρ L kc N (a4 k₁ k₂ k₃ k₄ γ).2 := hβ ▸ HJ_inM hρ hB
  have hγM : InM ρ L kc N γ := hγ ▸ HJ_inM hρ hG
  refine ⟨?_, ?_, ?_⟩
  · ext n
    rw [Multiset.count_add, Multiset.count_add, HJ_count_legs, HJ_count_legs, HJ_count_pair,
      HJ_count_pair]
    have hid := HJ_a4_id hne n
    by_cases hn : inPHc ρ L kc n
    · rw [hβ, HJ_ops_in α B (HJ_d_in hρ hlB hn)] at hid
      rw [hγ, HJ_ops_in α G (HJ_d_in hρ hlG hn)] at hid
      omega
    · have e1 : n ≠ k₁ := fun e => hn (e ▸ hk₁)
      have e2 : n ≠ k₂ := fun e => hn (e ▸ hk₂)
      have e3 : n ≠ k₃ := fun e => hn (e ▸ hk₃)
      have e4 : n ≠ k₄ := fun e => hn (e ▸ hk₄)
      simp [HJ_G_out hlB hn, HJ_G_out hlG hn, e1, e2, e3, e4]
  · intro hm
    obtain ⟨hPL, β', hβ', hsβ⟩ := HJ_soft hρ hB h12 hm
    exact hrest ⟨hβM, hPL, β', hβ', hsβ.trans hβ.symm⟩
  · intro hm
    obtain ⟨hPL, γ', hγ', hsγ⟩ := HJ_soft hρ hG h34 hm
    obtain ⟨hsum, hiff⟩ := Eq10_9 hρ hγ'.1 hβM hγM hne rfl
    refine hrest ⟨hβM, hsum ▸ hPL, γ', hsum ▸ hγ', hiff.2 (hsγ.trans hγ.symm)⟩

/-- Lemma 11.3 [lem11.1] for `N(α, s, {v_1, …, v_t})`: for `K ≥ #P_{H,c}, t, 1` it is
empty if `s + t ≤ 1` ((11.11) [stgeq2]) and has at most
`2 · 16^{s+t} t! t^{t/2+1} K^{(s+t)/2+1}` elements. -/
theorem HardJoint_count {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) (hL : 0 < L) (α : Occ) (s : ℕ)
    (vs : Finset Idx) (h0 : (0 : Idx) ∉ vs) {K : ℝ}
    (hH : ({n | inPHc ρ L kc n}.ncard : ℝ) ≤ K) (ht : (vs.card : ℝ) ≤ K) (hK : 1 ≤ K) :
    (HardJoint.NSet ρ L kc N α (Multiset.replicate s 0 + vs.val)).Finite ∧
      (s + vs.card ≤ 1 → HardJoint.NSet ρ L kc N α (Multiset.replicate s 0 + vs.val) = ∅) ∧
      ((HardJoint.NSet ρ L kc N α (Multiset.replicate s 0 + vs.val)).ncard : ℝ) ≤
        2 * 16 ^ (s + vs.card) * (vs.card.factorial : ℝ) *
          (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) * K ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) := by
  have hRL : π ≤ max kc (π / L) * L :=
    calc π = π / L * L := (div_mul_cancel₀ π hL.ne').symm
      _ ≤ max kc (π / L) * L := mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le
  have hHfin : {n | inPHc ρ L kc n}.Finite :=
    (HardBounds_card_ball hL hRL).1.subset fun n hn => hn.2.trans (le_max_left _ _)
  have hHK : (hHfin.toFinset.card : ℝ) ≤ K := by
    rw [← Set.ncard_eq_toFinset_card _ hHfin]
    exact hH
  obtain ⟨hAfin, hAempty, hAcard⟩ := HardGraph_count hHfin.toFinset s vs h0 hHK ht hK
  let g : (Fin 4 → Idx) × Multiset (Sym2 Idx) × Multiset (Sym2 Idx) → Idx × Idx × Idx × Occ :=
    fun x => (x.1 0, x.1 1, x.1 0 - x.1 2,
      Chi_ops (x.2.2.toList.map fun p : Sym2 Idx => (Quot.out p : Idx × Idx)) α)
  have hsub : HardJoint.NSet ρ L kc N α (Multiset.replicate s 0 + vs.val) ⊆
      g '' {x | HardGraph.Adm hHfin.toFinset (Multiset.replicate s 0 + vs.val) x} := by
    rintro ⟨k₁, k₂, u, γ⟩ ⟨hcls, hne, -, -, B, G, hB, hG, hBe, hGe, hsB, hsG, hnc⟩
    obtain ⟨hk, hgen, hrest⟩ := hcls
    obtain ⟨hlegs, hnB, hnG⟩ :=
      HardJoint_graph hρ ⟨hk 0, hk 1, hk 2, hk 3⟩ hgen hne hB hG hBe hGe hrest
    have hlB := HJ_legs_of_rep hB
    have hlG := HJ_legs_of_rep hG
    have hin : ∀ {P : List (Idx × Idx)}, HJ_Legs ρ L kc P →
        ∀ q ∈ HardGraph.legs (HardJoint.pairs P), q ∈ hHfin.toFinset := by
      intro P hP q hq
      rw [Set.Finite.mem_toFinset]
      by_contra hn
      have := Multiset.count_pos.2 hq
      rw [HJ_count_legs, HJ_G_out hP hn] at this
      omega
    have htot : ∀ P : List (Idx × Idx),
        (HardJoint.pairs P).map HardGraph.tot = HardRep.sums P := by
      intro P
      unfold HardJoint.pairs HardRep.sums
      rw [Multiset.map_coe, List.map_map]
      rfl
    refine ⟨(FourLegs.legs k₁ k₂ u, HardJoint.pairs B, HardJoint.pairs G),
      ⟨hgen, hin hlB, hin hlG, (htot B).trans hsB, (htot G).trans hsG, hnc, hlegs, hnB, hnG⟩,
      ?_⟩
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext (sub_sub_cancel k₁ u) ?_))
    exact (HJ_ops_pairs hρ hlG (HJ_pairs_out _).symm α).symm.trans hGe.symm
  refine ⟨(hAfin.image g).subset hsub, fun h => ?_, ?_⟩
  · rw [hAempty h, Set.image_empty] at hsub
    exact Set.subset_empty_iff.1 hsub
  · refine le_trans ?_ hAcard
    exact_mod_cast (Set.ncard_le_ncard hsub (hAfin.image g)).trans (Set.ncard_image_le hAfin)

/-- Lemma 11.3 [lem11.1], (11.19) [0.025] with `t^{t/2+1}`: for every `k_c`, eventually in
`N`, for every `α`, `s` and `{v_1, …, v_t} ⊂ P_L` with `t ≥ 1`, `s + t ≥ 2`, the set
`N(α, s, {v_1, …, v_t})` has at most `t! t^{t/2+1} |Λ|^{(s+t)/2+1} (ρ^{-5η})^{s+t}`
elements. -/
theorem Lemma11_3_paper :
    ∀ kc : ℝ, ∀ᶠ N in atTop, ∀ (α : Occ) (s : ℕ) (vs : Finset Idx),
      (∀ v ∈ vs, inPL (rhoN N) (LN N) v) → 1 ≤ vs.card → 2 ≤ s + vs.card →
      (HardJoint.NSet (rhoN N) (LN N) kc N α (Multiset.replicate s 0 + vs.val)).Finite ∧
      ((HardJoint.NSet (rhoN N) (LN N) kc N α (Multiset.replicate s 0 + vs.val)).ncard : ℝ) ≤
        (vs.card.factorial : ℝ) * (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) *
          (LN N ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) *
          (rhoN N ^ (-(1/40 : ℝ))) ^ (s + vs.card) := by
  intro kc
  have hk1 : (1 : ℝ) ≤ max kc 1 := le_max_right _ _
  have hLt : Tendsto (fun N : ℕ => LN N) atTop atTop := by
    refine ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 25 / 51)).comp
      tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp, LN, rhoN]
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hρt : Tendsto (fun N : ℕ => rhoN N ^ (-(1/40 : ℝ))) atTop atTop := by
    refine ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 85)).comp
      tendsto_natCast_atTop_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp, rhoN]
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  filter_upwards [eventually_ge_atTop 1, hLt.eventually_ge_atTop π,
    hρt.eventually_ge_atTop (32 * max kc 1 ^ 3)] with N hN hLπ hρk
  intro α s vs hvs ht1 hst
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 < rhoN N := Real.rpow_pos_of_pos hNpos _
  have hρ1 : rhoN N ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hN) (by norm_num)
  have hL : 0 < LN N := lt_of_lt_of_le Real.pi_pos hLπ
  have hL1 : 1 ≤ LN N := le_trans (by linarith [Real.pi_gt_three]) hLπ
  have hkL : π ≤ max kc 1 * LN N := le_trans hLπ (le_mul_of_one_le_left hL.le hk1)
  obtain ⟨hbf, hbc⟩ := HardBounds_card_ball hL hkL
  have hbK : ({n : Idx | ‖mom (LN N) n‖ ≤ max kc 1}.ncard : ℝ) ≤ max kc 1 ^ 3 * LN N ^ 3 := by
    refine hbc.trans ?_
    have hπ3 : 8 / π ^ 3 ≤ 1 := by
      rw [div_le_one (by positivity)]
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ π ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) 3
    calc 8 / π ^ 3 * (max kc 1 * LN N) ^ 3 ≤ 1 * (max kc 1 * LN N) ^ 3 :=
          mul_le_mul_of_nonneg_right hπ3 (by positivity)
      _ = max kc 1 ^ 3 * LN N ^ 3 := by ring
  have hHb : {n | inPHc (rhoN N) (LN N) kc n}.ncard ≤
      {n : Idx | ‖mom (LN N) n‖ ≤ max kc 1}.ncard :=
    Set.ncard_le_ncard (fun n (hn : inPHc (rhoN N) (LN N) kc n) =>
      hn.2.trans (le_max_left _ _)) hbf
  have hH : ({n | inPHc (rhoN N) (LN N) kc n}.ncard : ℝ) ≤ max kc 1 ^ 3 * LN N ^ 3 :=
    le_trans (by exact_mod_cast hHb) hbK
  have hPLb : ∀ v, inPL (rhoN N) (LN N) v → ‖mom (LN N) v‖ ≤ max kc 1 := by
    intro v hv
    refine hv.2.trans (le_trans ?_ hk1)
    have hε : 0 < epsP (rhoN N) := Real.rpow_pos_of_pos hρ _
    rw [inv_mul_le_iff₀ hε, mul_one]
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have ht : (vs.card : ℝ) ≤ max kc 1 ^ 3 * LN N ^ 3 := by
    have hvb : (vs : Set Idx).ncard ≤ {n : Idx | ‖mom (LN N) n‖ ≤ max kc 1}.ncard :=
      Set.ncard_le_ncard (fun v hv => hPLb v (hvs v (Finset.mem_coe.1 hv))) hbf
    rw [← Set.ncard_coe_finset]
    exact le_trans (by exact_mod_cast hvb) hbK
  have hK : 1 ≤ max kc 1 ^ 3 * LN N ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk1) (one_le_pow₀ hL1)
  have h0 : (0 : Idx) ∉ vs := fun h => Regions_PL_ne_zero hρ (hvs 0 h) rfl
  obtain ⟨hfin, -, hcard⟩ := HardJoint_count (N := N) (kc := kc) hρ hL α s vs h0 hH ht hK
  refine ⟨hfin, hcard.trans ?_⟩
  have hn2 : (2 : ℝ) ≤ ((s + vs.card : ℕ) : ℝ) := by exact_mod_cast hst
  have he : ((s + vs.card : ℕ) : ℝ) / 2 + 1 ≤ ((s + vs.card : ℕ) : ℝ) := by linarith
  have hk3 : 1 ≤ max kc 1 ^ 3 := one_le_pow₀ hk1
  have hKe : (max kc 1 ^ 3 * LN N ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) =
      (max kc 1 ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) *
        (LN N ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) :=
    Real.mul_rpow (by positivity) (by positivity)
  have hke : (max kc 1 ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) ≤
      (max kc 1 ^ 3) ^ (s + vs.card) := by
    rw [← Real.rpow_natCast (max kc 1 ^ 3) (s + vs.card)]
    exact Real.rpow_le_rpow_of_exponent_le hk3 he
  have h2 : (2 : ℝ) ≤ 2 ^ (s + vs.card) := le_self_pow₀ (by norm_num) (by omega)
  have hpow : 2 * 16 ^ (s + vs.card) * (max kc 1 ^ 3) ^ (s + vs.card) ≤
      (rhoN N ^ (-(1/40 : ℝ))) ^ (s + vs.card) := by
    calc 2 * 16 ^ (s + vs.card) * (max kc 1 ^ 3) ^ (s + vs.card) ≤
          2 ^ (s + vs.card) * 16 ^ (s + vs.card) * (max kc 1 ^ 3) ^ (s + vs.card) := by gcongr
      _ = (32 * max kc 1 ^ 3) ^ (s + vs.card) := by rw [← mul_pow, ← mul_pow]; norm_num
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hρk _
  have hA : 0 ≤ (vs.card.factorial : ℝ) * (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) *
      (LN N ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) := by positivity
  calc 2 * 16 ^ (s + vs.card) * (vs.card.factorial : ℝ) *
        (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) *
          (max kc 1 ^ 3 * LN N ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1)
      = ((vs.card.factorial : ℝ) * (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) *
          (LN N ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1)) *
        (2 * 16 ^ (s + vs.card) * (max kc 1 ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1)) := by
        rw [hKe]; ring
    _ ≤ ((vs.card.factorial : ℝ) * (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) *
          (LN N ^ 3) ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1)) *
        (rhoN N ^ (-(1/40 : ℝ))) ^ (s + vs.card) := by
        refine mul_le_mul_of_nonneg_left (le_trans ?_ hpow) hA
        gcongr
    _ = _ := by ring

end LHYUpper
