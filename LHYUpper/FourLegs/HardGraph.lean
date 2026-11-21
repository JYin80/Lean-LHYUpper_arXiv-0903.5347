module

public import LHYUpper.FourLegs.Defs

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

namespace HardGraph

/-- The total momentum `q + q'` of an unordered pair `{q, q'}`. -/
def tot (p : Sym2 Idx) : Idx := Sym2.lift ⟨fun a b => a + b, fun a b => add_comm a b⟩ p

/-- The momenta of a multiset of unordered pairs, with multiplicity: the vertices of the
graph of (11.24) [temp4.178]. -/
def legs (P : Multiset (Sym2 Idx)) : Multiset Idx :=
  P.bind fun p => Sym2.lift ⟨fun a b => ({a, b} : Multiset Idx), fun a b => Multiset.pair_comm a b⟩ p

/-- The configurations of Lemma 11.3 [lem11.1]: legs `k₁, k₂, k₃, k₄` pairwise `≠ ±`
((10.7) [conditionk2]), multisets `B`, `G` of unordered pairs with momenta in `H` and total
momenta `S` ((11.20) [112]), no common pair, leg multisets `{k₁, k₂} + P` and `{k₃, k₄} + P`,
`{k₁, k₂} ∉ B` and `{k₃, k₄} ∉ G` ((11.26) [uboundl]). -/
def Adm (H : Finset Idx) (S : Multiset Idx)
    (x : (Fin 4 → Idx) × Multiset (Sym2 Idx) × Multiset (Sym2 Idx)) : Prop :=
  (∀ i j, i ≠ j → Legs_pm (x.1 i) (x.1 j)) ∧
    (∀ q ∈ legs x.2.1, q ∈ H) ∧ (∀ q ∈ legs x.2.2, q ∈ H) ∧
    x.2.1.map tot = S ∧ x.2.2.map tot = S ∧ (∀ p ∈ x.2.1, p ∉ x.2.2) ∧
    legs x.2.1 + {x.1 2, x.1 3} = legs x.2.2 + {x.1 0, x.1 1} ∧
    s(x.1 0, x.1 1) ∉ x.2.1 ∧ s(x.1 2, x.1 3) ∉ x.2.2

/-! ## The graph of chains and loops of Lemma 11.3 [lem11.1] and its encoding -/

private def lst : List Idx → Idx
  | [] => 0
  | [a] => a
  | _ :: b :: r => lst (b :: r)

private def altE : List Idx → Multiset (Sym2 Idx) × Multiset (Sym2 Idx)
  | a :: b :: r => (s(a, b) ::ₘ (altE (b :: r)).2, (altE (b :: r)).1)
  | _ => (0, 0)

/-- Labels `q_i + q_{i+1}` of consecutive vertices. -/
private def lab : List Idx → List Idx
  | a :: b :: r => (a + b) :: lab (b :: r)
  | _ => []

/-- The walk from `m` with labels `ws`. -/
private def walk (m : Idx) : List Idx → List Idx
  | [] => [m]
  | w :: ws => m :: walk (w - m) ws

/-- Entries at even positions. -/
private def evn : List Idx → List Idx
  | a :: _ :: r => a :: evn r
  | l => l

/-- Interleaving `x₀ y₀ x₁ y₁ …`. -/
private def ilv : List Idx → List Idx → List Idx
  | [], ys => ys
  | x :: xs, ys => x :: ilv ys xs
termination_by xs ys => xs.length + ys.length

private def zb (a : Idx) : Bool := decide (a = 0)

/-- Refill a list from its zero pattern and its nonzero entries. -/
private def fill : List Bool → List Idx → List Idx
  | [], _ => []
  | true :: bs, vs => 0 :: fill bs vs
  | false :: bs, [] => 0 :: fill bs []
  | false :: bs, v :: vs => v :: fill bs vs

private lemma walk_lab : ∀ (a : Idx) (r : List Idx), walk a (lab (a :: r)) = a :: r
  | a, [] => by simp [lab, walk]
  | a, b :: r => by simp [lab, walk, walk_lab b r]

private lemma evn_cons (a : Idx) : ∀ l : List Idx, evn (a :: l) = a :: evn l.tail
  | [] => by simp [evn]
  | b :: r => by simp [evn]

private lemma ilv_evn : ∀ l : List Idx, ilv (evn l) (evn l.tail) = l
  | [] => by simp [evn, ilv]
  | [a] => by simp [evn, ilv]
  | a :: b :: r => by
    have h := ilv_evn (b :: r)
    simp only [List.tail_cons] at h
    simp only [evn, List.tail_cons, ilv, h]

private lemma fill_spec : ∀ (L R : List Idx),
    fill (L.map zb) (L.filter (fun a => !zb a) ++ R) = L
  | [], R => by simp [fill]
  | a :: L, R => by
    by_cases ha : a = 0
    · subst ha
      have h0 : zb 0 = true := by simp [zb]
      simp only [List.map_cons, h0, List.filter_cons, Bool.not_true, Bool.false_eq_true,
        ite_false, fill, fill_spec L R]
    · have : zb a = false := by simp [zb, ha]
      simp [this, fill, fill_spec L R]

private lemma sum_filter : ∀ L : List Idx, (L.filter (fun a => !zb a)).sum = L.sum
  | [] => by simp
  | a :: L => by
    by_cases ha : a = 0
    · subst ha
      have h0 : zb 0 = true := by simp [zb]
      simp only [List.filter_cons, h0, Bool.not_true, Bool.false_eq_true, ite_false,
        sum_filter L, List.sum_cons, zero_add]
    · have : zb a = false := by simp [zb, ha]
      simp [this, sum_filter L]

private lemma count_map_zb : ∀ L : List Idx,
    (L.map zb).count false = (L.filter (fun a => !zb a)).length
  | [] => by simp
  | a :: L => by
    by_cases ha : a = 0
    · have : zb a = true := by simp [zb, ha]
      simp [this, count_map_zb L]
    · have : zb a = false := by simp [zb, ha]
      simp [this, count_map_zb L]

private lemma length_lab : ∀ l : List Idx, (lab l).length = l.length - 1
  | [] => by simp [lab]
  | [a] => by simp [lab]
  | a :: b :: r => by simp [lab, length_lab (b :: r)]

private lemma length_evn : ∀ l : List Idx, (evn l).length = (l.length + 1) / 2
  | [] => by simp [evn]
  | [a] => by simp [evn]
  | a :: b :: r => by simp [evn, length_evn r]; omega

private lemma tot_mk (a b : Idx) : tot s(a, b) = a + b := rfl

/-- The totals of the two sides of a walk are its labels at even and at odd positions. -/
private lemma altE_tot : ∀ w : List Idx,
    (altE w).1.map tot = ↑(evn (lab w)) ∧ (altE w).2.map tot = ↑(evn (lab w).tail)
  | [] => by simp [altE, lab, evn]
  | [a] => by simp [altE, lab, evn]
  | a :: b :: r => by
    obtain ⟨h1, h2⟩ := altE_tot (b :: r)
    refine ⟨?_, ?_⟩
    · simp only [altE, lab, Multiset.map_cons, tot_mk, h2, evn_cons, Multiset.cons_coe]
    · simp only [altE, lab, List.tail_cons, h1]

/-- On a walk with an even number of steps, the alternating sum of the labels telescopes. -/
private lemma alt_sum : ∀ (a : Idx) (r : List Idx), Even r.length →
    (evn (lab (a :: r))).sum - (evn (lab (a :: r)).tail).sum = a - lst (a :: r)
  | a, [] => by simp [lab, evn, lst]
  | a, [b] => by simp
  | a, b :: c :: r => by
    intro h
    have hr : Even r.length := by simpa [Nat.even_add_one, parity_simps] using h
    have ih := alt_sum c r hr
    have e1 : evn (lab (a :: b :: c :: r)) = (a + b) :: evn (lab (c :: r)) := by
      simp [lab, evn]
    have e2 : evn (lab (a :: b :: c :: r)).tail = (b + c) :: evn (lab (c :: r)).tail := by
      simp only [lab, List.tail_cons, evn_cons]
    have e3 : lst (a :: b :: c :: r) = lst (c :: r) := rfl
    rw [e1, e2, e3, List.sum_cons, List.sum_cons,
      show a - lst (c :: r) = a - c + (c - lst (c :: r)) by abel, ← ih]
    abel


/-- The labels on the second side of a component: refilled from the zero pattern `g` and the
nonzero entries `nz`; on a loop the last nonzero entry is fixed by the loop sum. -/
private def gam (cy : Bool) (β : List Idx) (g : List Bool) (nz : List Idx) : List Idx :=
  if cy then fill g (nz ++ [β.sum - nz.sum]) else fill g nz

/-- The vertices of one component from its start `m` and its labels. -/
private def decOne (gf cy : Bool) (β : List Idx) (g : List Bool) (nz : List Idx) (m : Idx) :
    List Idx :=
  walk m (if gf then ilv (gam cy β g nz) β else ilv β (gam cy β g nz))

/-- The number of nonzero entries a component reads. -/
private def nzc (cy : Bool) (g : List Bool) : ℕ := if cy then g.count false - 1 else g.count false

/-- All components, read one after the other. -/
private def decAll : List (ℕ × ℕ × Bool × Bool) → List Idx → List Bool → List Idx → List Idx →
    List (List Idx × Bool)
  | (b, g, cy, gf) :: sp, βs, gs, nz, m :: ms =>
      (decOne gf cy (βs.take b) (gs.take g) (nz.take (nzc cy (gs.take g))) m, gf) ::
        decAll sp (βs.drop b) (gs.drop g) (nz.drop (nzc cy (gs.take g))) ms
  | _, _, _, _, _ => []

/-- The total number of nonzero entries read. -/
private def nzTot : List (ℕ × ℕ × Bool × Bool) → List Bool → ℕ
  | (_, g, cy, _) :: sp, gs => nzc cy (gs.take g) + nzTot sp (gs.drop g)
  | [], _ => 0

/-- The component types: two chains, then loops. -/
private def spec (p : Fin 3) : List ℕ → List (ℕ × ℕ × Bool × Bool)
  | b₀ :: b₁ :: r => (b₀, if p = 0 then b₀ - 1 else b₀, false, false) ::
      (b₁, if p = 0 then b₁ + 1 else b₁, false, decide (p = 0)) ::
        r.map fun b => (b, b, true, false)
  | l => l.map fun b => (b, b, true, false)

/-- The legs from the ends of the two chains. -/
private def kOf (p : Fin 3) : List (List Idx × Bool) → Fin 4 → Idx
  | c₀ :: c₁ :: _ => if p = 0 then ![c₀.1.headD 0, lst c₀.1, c₁.1.headD 0, lst c₁.1]
      else if p = 1 then ![c₀.1.headD 0, c₁.1.headD 0, lst c₀.1, lst c₁.1]
      else ![c₀.1.headD 0, c₁.1.headD 0, lst c₁.1, lst c₀.1]
  | _ => 0

private def bSide (c : List Idx × Bool) : Multiset (Sym2 Idx) :=
  if c.2 then (altE c.1).2 else (altE c.1).1

private def gSide (c : List Idx × Bool) : Multiset (Sym2 Idx) :=
  if c.2 then (altE c.1).1 else (altE c.1).2

/-- The configuration encoded by a code. -/
private def dec (n : ℕ)
    (cd : (Fin 3 × Composition n × List Bool) × List Idx × List Idx × List Idx) :
    (Fin 4 → Idx) × Multiset (Sym2 Idx) × Multiset (Sym2 Idx) :=
  (kOf cd.1.1 (decAll (spec cd.1.1 cd.1.2.1.blocks) cd.2.1 cd.1.2.2 cd.2.2.1 cd.2.2.2),
    ((decAll (spec cd.1.1 cd.1.2.1.blocks) cd.2.1 cd.1.2.2 cd.2.2.1 cd.2.2.2).map bSide).sum,
    ((decAll (spec cd.1.1 cd.1.2.1.blocks) cd.2.1 cd.1.2.2 cd.2.2.1 cd.2.2.2).map gSide).sum)

/-! Components `(w, cy, gf)`: vertices, loop flag, and whether the first step is on the second
side. -/

private def bL (c : List Idx × Bool × Bool) : List Idx :=
  if c.2.2 then evn (lab c.1).tail else evn (lab c.1)

private def gL (c : List Idx × Bool × Bool) : List Idx :=
  if c.2.2 then evn (lab c.1) else evn (lab c.1).tail

private def nzv (c : List Idx × Bool × Bool) : List Idx :=
  if c.2.1 then ((gL c).filter fun a => !zb a).dropLast else (gL c).filter fun a => !zb a

private def spc (c : List Idx × Bool × Bool) : ℕ × ℕ × Bool × Bool :=
  ((bL c).length, (gL c).length, c.2.1, c.2.2)

private lemma gam_spec (c : List Idx × Bool × Bool) (hcy : c.2.1 = true → (bL c).sum = (gL c).sum) :
    gam c.2.1 (bL c) ((gL c).map zb) (nzv c) = gL c := by
  unfold gam nzv
  by_cases hc : c.2.1 = true
  · simp only [hc, ite_true]
    set F := (gL c).filter fun a => !zb a with hF
    by_cases hF0 : F = []
    · rw [hF0]
      have := fill_spec (gL c) [(bL c).sum - ([] : List Idx).dropLast.sum]
      rw [← hF, hF0] at this
      simpa using this
    · have hlast := List.dropLast_append_getLast hF0
      have hs : F.sum = (gL c).sum := sum_filter _
      have hsum : F.sum = F.dropLast.sum + F.getLast hF0 := by
        conv_lhs => rw [← hlast]
        rw [List.sum_append, List.sum_singleton]
      have e : F.dropLast ++ [(bL c).sum - F.dropLast.sum] = F := by
        rw [hcy hc, ← hs, hsum, add_sub_cancel_left]; exact hlast
      rw [e]
      have := fill_spec (gL c) []
      rwa [List.append_nil] at this
  · simp only [hc, Bool.false_eq_true, ite_false]
    have := fill_spec (gL c) []
    rwa [List.append_nil] at this

private lemma decOne_spec (c : List Idx × Bool × Bool) {a : Idx} {r : List Idx} (hw : c.1 = a :: r)
    (hcy : c.2.1 = true → (bL c).sum = (gL c).sum) :
    decOne c.2.2 c.2.1 (bL c) ((gL c).map zb) (nzv c) a = c.1 := by
  unfold decOne
  rw [gam_spec c hcy]
  by_cases hg : c.2.2 = true
  · simp only [hg, ite_true, gL, bL]
    rw [ilv_evn, hw, walk_lab]
  · simp only [hg, Bool.false_eq_true, ite_false, gL, bL]
    rw [ilv_evn, hw, walk_lab]

private lemma nzc_spec (c : List Idx × Bool × Bool) :
    nzc c.2.1 ((gL c).map zb) = (nzv c).length := by
  unfold nzc nzv
  by_cases hc : c.2.1 = true
  · simp [hc, count_map_zb, List.length_dropLast]
  · simp [hc, count_map_zb]

private lemma decAll_spec : ∀ cs : List (List Idx × Bool × Bool),
    (∀ c ∈ cs, c.1 ≠ [] ∧ (c.2.1 = true → (bL c).sum = (gL c).sum)) →
    decAll (cs.map spc) (cs.flatMap bL) (cs.flatMap fun c => (gL c).map zb) (cs.flatMap nzv)
      (cs.map fun c => c.1.headD 0) = cs.map fun c => (c.1, c.2.2)
  | [], _ => by simp [decAll]
  | c :: cs, h => by
    obtain ⟨hne, hcy⟩ := h c (by simp)
    obtain ⟨a, r, hw⟩ := List.exists_cons_of_ne_nil hne
    have ih := decAll_spec cs fun c' hc' => h c' (by simp [hc'])
    have l1 : ((gL c).map zb).length = (gL c).length := List.length_map _
    simp only [List.map_cons, List.flatMap_cons, spc, decAll]
    rw [List.take_left' rfl, List.drop_left' rfl, List.take_left' l1, List.drop_left' l1,
      nzc_spec, List.take_left' rfl, List.drop_left' rfl, ih, hw]
    simp only [List.headD_cons]
    rw [← hw, decOne_spec c hw hcy]

private lemma nzTot_spec : ∀ cs : List (List Idx × Bool × Bool),
    nzTot (cs.map spc) (cs.flatMap fun c => (gL c).map zb) = (cs.flatMap nzv).length
  | [] => by simp [nzTot]
  | c :: cs => by
    have l1 : ((gL c).map zb).length = (gL c).length := List.length_map _
    simp only [List.map_cons, List.flatMap_cons, spc, nzTot]
    rw [List.take_left' l1, List.drop_left' l1, nzc_spec, nzTot_spec cs, List.length_append]

private lemma legs_zero : legs 0 = 0 := by simp [legs]

private lemma legs_cons (a b : Idx) (P : Multiset (Sym2 Idx)) :
    legs (s(a, b) ::ₘ P) = a ::ₘ b ::ₘ legs P := by
  simp [legs, Multiset.cons_bind]

private lemma card_legs (P : Multiset (Sym2 Idx)) :
    Multiset.card (legs P) = 2 * Multiset.card P := by
  induction P using Multiset.induction_on with
  | empty => simp [legs]
  | cons p P ih =>
    induction p using Sym2.ind with
    | h a b => rw [legs_cons]; simp [ih]; ring

private lemma mem_legs {q : Idx} {P : Multiset (Sym2 Idx)} : q ∈ legs P ↔ ∃ a, s(q, a) ∈ P := by
  constructor
  · intro h
    obtain ⟨p, hp, hq⟩ := Multiset.mem_bind.1 h
    induction p using Sym2.ind with
    | h x y =>
      simp only [Sym2.lift_mk, Multiset.insert_eq_cons, Multiset.mem_cons,
        Multiset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact ⟨y, hp⟩
      · exact ⟨x, by rwa [Sym2.eq_swap]⟩
  · rintro ⟨a, ha⟩
    exact Multiset.mem_bind.2 ⟨_, ha, by simp⟩


private lemma add_sing (M : Multiset Idx) (q : Idx) : M + {q} = q ::ₘ M := by
  rw [add_comm, Multiset.singleton_add]

private lemma stop_eq {B G : Multiset (Sym2 Idx)} {X Y : Multiset Idx} {q : Idx} (hq : q ∈ Y)
    (h : legs B + Y = legs G + X + {q}) : legs B + Y.erase q = legs G + X := by
  rw [← Multiset.cons_erase hq, add_sing, Multiset.add_cons] at h
  exact Multiset.cons_inj_right q |>.1 h

/-- A chain of (11.24) [temp4.178]: from an unmatched leg `q`, pairs of the two sides
alternate until an unmatched leg on the other side is reached. -/
private lemma walk_ex : ∀ (N : ℕ) (B G : Multiset (Sym2 Idx)) (X Y : Multiset Idx) (q : Idx),
    Multiset.card B + Multiset.card G ≤ N → legs B + Y = legs G + X + {q} →
    ∃ v : List Idx, ∃ B' G', B = (altE (q :: v)).1 + B' ∧ G = (altE (q :: v)).2 + G' ∧
      ((Even v.length ∧ lst (q :: v) ∈ Y ∧ legs B' + Y.erase (lst (q :: v)) = legs G' + X) ∨
       (Odd v.length ∧ lst (q :: v) ∈ X ∧ legs B' + Y = legs G' + X.erase (lst (q :: v)))) := by
  intro N
  induction N with
  | zero =>
    intro B G X Y q hc h
    have hB : B = 0 := Multiset.card_eq_zero.1 (by omega)
    have hG : G = 0 := Multiset.card_eq_zero.1 (by omega)
    subst hB hG
    have hq : q ∈ Y := by
      have : q ∈ legs 0 + Y := by rw [h]; simp
      simpa [legs_zero] using this
    exact ⟨[], 0, 0, by simp [altE], by simp [altE], Or.inl ⟨by simp, hq, stop_eq hq h⟩⟩
  | succ N ih =>
    intro B G X Y q hc h
    by_cases hq : q ∈ Y
    · exact ⟨[], B, G, by simp [altE], by simp [altE], Or.inl ⟨by simp, hq, stop_eq hq h⟩⟩
    have hqB : q ∈ legs B := by
      have : q ∈ legs B + Y := by rw [h]; simp
      rcases Multiset.mem_add.1 this with h1 | h1
      · exact h1
      · exact absurd h1 hq
    obtain ⟨a, ha⟩ := mem_legs.1 hqB
    set B₁ := B.erase s(q, a) with hB₁
    have hB : B = s(q, a) ::ₘ B₁ := (Multiset.cons_erase ha).symm
    have h' : legs G + X = legs B₁ + Y + {a} := by
      rw [hB, legs_cons, add_sing, Multiset.cons_add, Multiset.cons_add] at h
      have h2 := (Multiset.cons_inj_right q).1 h
      rw [add_sing, ← h2]
    have hc' : Multiset.card G + Multiset.card B₁ ≤ N := by
      rw [hB, Multiset.card_cons] at hc; omega
    obtain ⟨v, B'', G'', hG, hB1, hend⟩ := ih G B₁ Y X a hc' h'
    refine ⟨a :: v, G'', B'', ?_, ?_, ?_⟩
    · rw [hB, hB1]; simp [altE]
    · rw [hG]; simp [altE]
    · have hl : lst (q :: a :: v) = lst (a :: v) := rfl
      rw [hl]
      rcases hend with ⟨he, hm, heq⟩ | ⟨he, hm, heq⟩
      · exact Or.inr ⟨by simpa [Nat.odd_add_one] using he, hm, heq.symm⟩
      · exact Or.inl ⟨by simpa [Nat.even_add_one] using he, hm, heq.symm⟩


private lemma mem_sum_map {α : Type*} {f : α → Multiset (Sym2 Idx)} {x : Sym2 Idx} :
    ∀ {cs : List α} {w : α}, w ∈ cs → x ∈ f w → x ∈ (cs.map f).sum
  | [], _, h, _ => by simp at h
  | c :: cs, w, h, hx => by
    rw [List.map_cons, List.sum_cons, Multiset.mem_add]
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl hx
    · exact Or.inr (mem_sum_map h hx)

/-- If both sides have the same legs, the pairs split into the loops of (11.24) [temp4.178]. -/
private lemma cyc_ex : ∀ (N : ℕ) (B G : Multiset (Sym2 Idx)), Multiset.card B ≤ N →
    legs B = legs G →
    ∃ cs : List (List Idx), (∀ w ∈ cs, ∃ q a v, w = q :: a :: v ∧ Odd v.length ∧ lst w = q) ∧
      B = (cs.map fun w => (altE w).1).sum ∧ G = (cs.map fun w => (altE w).2).sum := by
  intro N
  induction N with
  | zero =>
    intro B G hc h
    have hB : B = 0 := Multiset.card_eq_zero.1 (by omega)
    subst hB
    have hG : G = 0 := by
      have := congrArg Multiset.card h
      rw [card_legs, card_legs, Multiset.card_zero] at this
      exact Multiset.card_eq_zero.1 (by omega)
    exact ⟨[], by simp, by simp, by simp [hG]⟩
  | succ N ih =>
    intro B G hc h
    by_cases hB0 : B = 0
    · subst hB0
      have hG : G = 0 := by
        have := congrArg Multiset.card h
        rw [card_legs, card_legs, Multiset.card_zero] at this
        exact Multiset.card_eq_zero.1 (by omega)
      exact ⟨[], by simp, by simp, by simp [hG]⟩
    obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hB0
    induction p using Sym2.ind with
    | h q a =>
    set B₁ := B.erase s(q, a) with hB₁
    have hB : B = s(q, a) ::ₘ B₁ := (Multiset.cons_erase hp).symm
    have h' : legs G + 0 = legs B₁ + {q} + {a} := by
      rw [hB, legs_cons] at h
      rw [add_zero, add_sing, add_sing, ← h, Multiset.cons_swap]
    obtain ⟨v, G', B', hG, hB1, hend⟩ := walk_ex _ G B₁ {q} 0 a le_rfl h'
    rcases hend with ⟨_, hm, _⟩ | ⟨hodd, hm, heq⟩
    · simp at hm
    have hlq : lst (a :: v) = q := by simpa using hm
    rw [hlq, Multiset.erase_singleton, add_zero, add_zero] at heq
    have hcB : Multiset.card B' ≤ N := by
      have e1 := congrArg Multiset.card hB
      have e2 := congrArg Multiset.card hB1
      simp only [Multiset.card_cons, Multiset.card_add] at e1 e2
      omega
    obtain ⟨cs, hcs, hB', hG'⟩ := ih B' G' hcB heq.symm
    refine ⟨(q :: a :: v) :: cs, ?_, ?_, ?_⟩
    · intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨q, a, v, rfl, hodd, hlq⟩
      · exact hcs w hw
    · rw [hB, hB1, hB']
      simp [altE]
    · rw [hG, hG']
      simp [altE]


/-- A loop has at least two pairs of each side, since no pair lies on both sides. -/
private lemma cyc_long {B G : Multiset (Sym2 Idx)} (h4 : ∀ p ∈ B, p ∉ G) {cs : List (List Idx)}
    (hcs : ∀ w ∈ cs, ∃ q a v, w = q :: a :: v ∧ Odd v.length ∧ lst w = q)
    (hB : ∀ w ∈ cs, ∀ x ∈ (altE w).1, x ∈ B) (hG : ∀ w ∈ cs, ∀ x ∈ (altE w).2, x ∈ G) :
    ∀ w ∈ cs, ∃ q a v, w = q :: a :: v ∧ Odd v.length ∧ 3 ≤ v.length ∧ lst w = q := by
  intro w hw
  obtain ⟨q, a, v, rfl, hodd, hl⟩ := hcs w hw
  refine ⟨q, a, v, rfl, hodd, ?_, hl⟩
  by_contra hlt
  have hv1 : v.length = 1 := by obtain ⟨m, hm⟩ := hodd; omega
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 hv1
  have hb : b = q := hl
  subst hb
  have h1 : s(b, a) ∈ B := hB _ hw _ (by simp [altE])
  have h2 : s(b, a) ∈ G := by
    have := hG _ hw s(a, b) (by simp [altE])
    rwa [Sym2.eq_swap] at this
  exact h4 _ h1 h2

/-- The graph of (11.24) [temp4.178]: two chains joining `k₁, k₂, k₃, k₄` and loops. A chain
from `k₃` to `k₄` contains a pair of the first side, since `{k₃, k₄}` is not a pair of the second
side ((11.26) [uboundl]). -/
private lemma decomp {H : Finset Idx} {S : Multiset Idx} {k : Fin 4 → Idx}
    {B G : Multiset (Sym2 Idx)} (hA : Adm H S (k, B, G)) :
    ∃ (p : Fin 3) (w₀ w₁ : List Idx) (cs : List (List Idx)),
      (∃ v, w₀ = k 0 :: v ∧ v ≠ [] ∧ (Odd v.length ↔ p = 0)) ∧
      (∃ q v, w₁ = q :: v ∧ (p = 0 → 2 ≤ v.length) ∧ v ≠ [] ∧ (Odd v.length ↔ p = 0)) ∧
      (∀ w ∈ cs, ∃ q a v, w = q :: a :: v ∧ Odd v.length ∧ 3 ≤ v.length ∧ lst w = q) ∧
      k = kOf p [(w₀, false), (w₁, decide (p = 0))] ∧
      B = bSide (w₀, false) + bSide (w₁, decide (p = 0)) + (cs.map fun w => (altE w).1).sum ∧
      G = gSide (w₀, false) + gSide (w₁, decide (p = 0)) + (cs.map fun w => (altE w).2).sum := by
  obtain ⟨h1, -, -, -, -, h4, h5, -, h7⟩ := hA
  simp only at h1 h4 h5 h7
  have hne : ∀ i j, i ≠ j → k i ≠ k j := fun i j h => (h1 i j h).1
  have h5' : legs B + {k 2, k 3} = legs G + {k 1} + {k 0} := by
    rw [h5, add_sing, ← Multiset.add_cons]; rfl
  have fin : ∀ B₂ G₂ : Multiset (Sym2 Idx), legs B₂ = legs G₂ → (∀ x ∈ B₂, x ∈ B) →
      (∀ x ∈ G₂, x ∈ G) → ∃ cs : List (List Idx),
        (∀ w ∈ cs, ∃ q a v, w = q :: a :: v ∧ Odd v.length ∧ 3 ≤ v.length ∧ lst w = q) ∧
        B₂ = (cs.map fun w => (altE w).1).sum ∧ G₂ = (cs.map fun w => (altE w).2).sum := by
    intro B₂ G₂ h hB hG
    obtain ⟨cs, hcs, e1, e2⟩ := cyc_ex _ B₂ G₂ le_rfl h
    refine ⟨cs, cyc_long h4 hcs ?_ ?_, e1, e2⟩
    · intro w hw x hx; exact hB _ (e1 ▸ mem_sum_map hw hx)
    · intro w hw x hx; exact hG _ (e2 ▸ mem_sum_map hw hx)
  obtain ⟨v₀, B₁, G₁, hB, hG, hend⟩ := walk_ex _ B G {k 1} {k 2, k 3} (k 0) le_rfl h5'
  rcases hend with ⟨hev, hm, heq⟩ | ⟨hodd, hm, heq⟩
  · have hm' : lst (k 0 :: v₀) = k 2 ∨ lst (k 0 :: v₀) = k 3 := by simpa using hm
    have hv0 : v₀ ≠ [] := by
      rintro rfl
      rcases hm' with h | h
      · exact hne 0 2 (by decide) h
      · exact hne 0 3 (by decide) h
    have hodd0 : ¬ Odd v₀.length := Nat.not_odd_iff_even.2 hev
    rcases hm' with he | he
    · rw [he, Multiset.insert_eq_cons, Multiset.erase_cons_head] at heq
      have h' : legs B₁ + {k 3} = legs G₁ + 0 + {k 1} := by rw [heq, add_zero]
      obtain ⟨v₁, B₂, G₂, hB₁, hG₁, hend₁⟩ := walk_ex _ B₁ G₁ 0 {k 3} (k 1) le_rfl h'
      rcases hend₁ with ⟨hev₁, hm₁, heq₁⟩ | ⟨_, hm₁, _⟩
      swap
      · simp at hm₁
      have he₁ : lst (k 1 :: v₁) = k 3 := by simpa using hm₁
      rw [he₁, Multiset.erase_singleton, add_zero, add_zero] at heq₁
      obtain ⟨cs, hcs, eB, eG⟩ := fin B₂ G₂ heq₁
        (fun x hx => by rw [hB, hB₁]; simp [hx]) (fun x hx => by rw [hG, hG₁]; simp [hx])
      refine ⟨1, k 0 :: v₀, k 1 :: v₁, cs, ⟨v₀, rfl, hv0, ?_⟩, ⟨k 1, v₁, rfl, ?_, ?_, ?_⟩, hcs,
        ?_, ?_, ?_⟩
      · simp [hodd0]
      · intro h; exact absurd h (by decide)
      · rintro rfl; exact hne 1 3 (by decide) he₁
      · simp [Nat.not_odd_iff_even.2 hev₁]
      · funext i; fin_cases i <;> simp [kOf, he, he₁]
      · rw [hB, hB₁, eB]; simp [bSide, add_assoc]
      · rw [hG, hG₁, eG]; simp [gSide, add_assoc]
    · rw [he, Multiset.insert_eq_cons, Multiset.erase_cons_tail _ (hne 2 3 (by decide)),
        Multiset.erase_singleton] at heq
      have h' : legs B₁ + {k 2} = legs G₁ + 0 + {k 1} := by rw [add_zero]; exact heq
      obtain ⟨v₁, B₂, G₂, hB₁, hG₁, hend₁⟩ := walk_ex _ B₁ G₁ 0 {k 2} (k 1) le_rfl h'
      rcases hend₁ with ⟨hev₁, hm₁, heq₁⟩ | ⟨_, hm₁, _⟩
      swap
      · simp at hm₁
      have he₁ : lst (k 1 :: v₁) = k 2 := by simpa using hm₁
      rw [he₁, Multiset.erase_singleton, add_zero, add_zero] at heq₁
      obtain ⟨cs, hcs, eB, eG⟩ := fin B₂ G₂ heq₁
        (fun x hx => by rw [hB, hB₁]; simp [hx]) (fun x hx => by rw [hG, hG₁]; simp [hx])
      refine ⟨2, k 0 :: v₀, k 1 :: v₁, cs, ⟨v₀, rfl, hv0, ?_⟩, ⟨k 1, v₁, rfl, ?_, ?_, ?_⟩, hcs,
        ?_, ?_, ?_⟩
      · simp [hodd0]
      · intro h; exact absurd h (by decide)
      · rintro rfl; exact hne 1 2 (by decide) he₁
      · simp [Nat.not_odd_iff_even.2 hev₁]
      · funext i; fin_cases i <;> simp [kOf, he, he₁]
      · rw [hB, hB₁, eB]; simp [bSide, add_assoc]
      · rw [hG, hG₁, eG]; simp [gSide, add_assoc]
  · have he : lst (k 0 :: v₀) = k 1 := by simpa using hm
    rw [he, Multiset.erase_singleton, add_zero] at heq
    have h' : legs G₁ + 0 = legs B₁ + {k 3} + {k 2} := by
      rw [add_zero, ← heq, add_sing, ← Multiset.add_cons]; rfl
    obtain ⟨v₁, G₂, B₂, hG₁, hB₁, hend₁⟩ := walk_ex _ G₁ B₁ {k 3} 0 (k 2) le_rfl h'
    rcases hend₁ with ⟨_, hm₁, _⟩ | ⟨hodd₁, hm₁, heq₁⟩
    · simp at hm₁
    have he₁ : lst (k 2 :: v₁) = k 3 := by simpa using hm₁
    rw [he₁, Multiset.erase_singleton, add_zero, add_zero] at heq₁
    have hv1 : 2 ≤ v₁.length := by
      by_contra hlt
      have hl1 : v₁.length = 1 := by obtain ⟨m, hm⟩ := hodd₁; omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 hl1
      have hb : b = k 3 := he₁
      subst hb
      apply h7
      rw [hG, hG₁]
      simp [altE]
    obtain ⟨cs, hcs, eB, eG⟩ := fin B₂ G₂ heq₁.symm
      (fun x hx => by rw [hB, hB₁]; simp [hx]) (fun x hx => by rw [hG, hG₁]; simp [hx])
    refine ⟨0, k 0 :: v₀, k 2 :: v₁, cs, ⟨v₀, rfl, ?_, ?_⟩, ⟨k 2, v₁, rfl, fun _ => hv1, ?_, ?_⟩,
      hcs, ?_, ?_, ?_⟩
    · rintro rfl; simp at hodd
    · simp [hodd]
    · rintro rfl; simp at hv1
    · simp [hodd₁]
    · funext i; fin_cases i <;> simp [kOf, he, he₁]
    · rw [hB, hB₁, eB]; simp [bSide, add_assoc]
    · rw [hG, hG₁, eG]; simp [gSide, add_assoc]


/-! ### The codes of Lemma 11.3 [lem11.1] and their number -/

private def lists (A : Finset Idx) (m : ℕ) : Finset (List Idx) :=
  (Fintype.piFinset fun _ : Fin m => A).image List.ofFn

private def bools (m : ℕ) : Finset (List Bool) :=
  (Finset.univ : Finset (Fin m → Bool)).image List.ofFn

private lemma mem_lists {A : Finset Idx} {m : ℕ} {L : List Idx} (hl : L.length = m)
    (hA : ∀ a ∈ L, a ∈ A) : L ∈ lists A m := by
  subst hl
  exact Finset.mem_image.2 ⟨fun i => L.get i,
    Fintype.mem_piFinset.2 fun i => hA _ (List.get_mem _ _), List.ofFn_get L⟩

private lemma mem_bools {L : List Bool} {m : ℕ} (hl : L.length = m) : L ∈ bools m := by
  subst hl
  exact Finset.mem_image.2 ⟨L.get, Finset.mem_univ _, List.ofFn_get L⟩

private lemma card_lists (A : Finset Idx) (m : ℕ) : (lists A m).card ≤ A.card ^ m :=
  Finset.card_image_le.trans (by simp [Fintype.card_piFinset])

private lemma card_bools (m : ℕ) : (bools m).card ≤ 2 ^ m :=
  Finset.card_image_le.trans (by simp)

/-- The list `0, …, 0, v₁, …, v_t` of the totals. -/
private def slist (s : ℕ) (vs : Finset Idx) : List Idx := List.replicate s 0 ++ vs.toList

private def permS (s : ℕ) (vs : Finset Idx) : Finset (List Idx) :=
  (slist s vs).permutations.toFinset

private lemma filter_slist (s : ℕ) {vs : Finset Idx} (h0 : (0 : Idx) ∉ vs) :
    (slist s vs).filter (fun a => !zb a) = vs.toList := by
  rw [slist, List.filter_append]
  have e1 : (List.replicate s (0 : Idx)).filter (fun a => !zb a) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    rw [List.eq_of_mem_replicate ha]
    simp [zb]
  have e2 : vs.toList.filter (fun a => !zb a) = vs.toList := by
    rw [List.filter_eq_self]
    intro a ha
    have : a ≠ 0 := fun h => h0 (h ▸ Finset.mem_toList.1 ha)
    simp [zb, this]
  rw [e1, e2, List.nil_append]

private lemma length_slist (s : ℕ) (vs : Finset Idx) : (slist s vs).length = s + vs.card := by
  simp [slist]

private lemma card_permS (s : ℕ) {vs : Finset Idx} (h0 : (0 : Idx) ∉ vs) :
    (permS s vs).card ≤ 2 ^ (s + vs.card) * vs.card.factorial := by
  have h : (permS s vs).card ≤ (bools (s + vs.card) ×ˢ vs.toList.permutations.toFinset).card := by
    apply Finset.card_le_card_of_injOn (fun L => (L.map zb, L.filter fun a => !zb a))
    · intro L hL
      have hp : L.Perm (slist s vs) := List.mem_permutations.1 (List.mem_toFinset.1 hL)
      refine Finset.mem_product.2 ⟨mem_bools ?_, ?_⟩
      · rw [List.length_map, hp.length_eq, length_slist]
      · rw [List.mem_toFinset, List.mem_permutations, ← filter_slist s h0]
        exact hp.filter _
    · intro L₁ _ L₂ _ h
      simp only [Prod.mk.injEq] at h
      have e1 := fill_spec L₁ []
      have e2 := fill_spec L₂ []
      rw [List.append_nil] at e1 e2
      rw [← e1, ← e2, h.1, h.2]
  refine h.trans ?_
  rw [Finset.card_product]
  refine Nat.mul_le_mul (card_bools _) ?_
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_permutations, Finset.length_toList]

private def shapes (n : ℕ) : Finset (Fin 3 × Composition n × List Bool) :=
  Finset.univ ×ˢ (Finset.univ ×ˢ bools n)

/-- The shapes of Lemma 11.3 [lem11.1]: `l ≤ (s+t)/2 + 1` components, and the loop count. -/
private def ok (n t s : ℕ) (sh : Fin 3 × Composition n × List Bool) : Prop :=
  2 * sh.2.1.blocks.length ≤ n + 2 ∧
    2 * nzTot (spec sh.1 sh.2.1.blocks) sh.2.2 + 2 * sh.2.1.blocks.length ≤ 2 * t + s + 4

private def codes (H : Finset Idx) (s : ℕ) (vs : Finset Idx) :
    Finset ((Fin 3 × Composition (s + vs.card) × List Bool) × List Idx × List Idx × List Idx) :=
  ((shapes (s + vs.card)).filter (ok (s + vs.card) vs.card s)).biUnion fun sh =>
    (permS s vs ×ˢ (lists vs (nzTot (spec sh.1 sh.2.1.blocks) sh.2.2) ×ˢ
      lists H sh.2.1.blocks.length)).image fun r => (sh, r)

/-- `t^j K^l ≤ t^{t/2+1} K^{(s+t)/2+1}` for `l ≤ (s+t)/2 + 1` and `j ≤ t + 2 + s/2 - l`. -/
private lemma real_ineq {t s l j : ℕ} {K : ℝ} (ht : 1 ≤ t) (htK : (t : ℝ) ≤ K) (hK : 1 ≤ K)
    (h1 : 2 * l ≤ s + t + 2) (h2 : 2 * j + 2 * l ≤ 2 * t + s + 4) :
    (t : ℝ) ^ j * K ^ l ≤ (t : ℝ) ^ ((t : ℝ) / 2 + 1) * K ^ (((s + t : ℕ) : ℝ) / 2 + 1) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have ht1 : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hK0 : (0 : ℝ) < K := by linarith
  have h1' : (2 * l : ℝ) ≤ s + t + 2 := by exact_mod_cast h1
  have h2' : (2 * j + 2 * l : ℝ) ≤ 2 * t + s + 4 := by exact_mod_cast h2
  set d : ℝ := (j : ℝ) - ((t : ℝ) / 2 + 1) with hd
  set e : ℝ := ((s + t : ℕ) : ℝ) / 2 + 1 - l with he
  have he0 : 0 ≤ e := by rw [he]; push_cast; linarith
  have hde : d ≤ e := by rw [hd, he]; push_cast; linarith
  have htd : (t : ℝ) ^ d ≤ K ^ e := by
    by_cases hd0 : d ≤ 0
    · exact (Real.rpow_le_one_of_one_le_of_nonpos ht1 hd0).trans (Real.one_le_rpow hK he0)
    · replace hd0 := (not_le.1 hd0)
      exact (Real.rpow_le_rpow ht0.le htK hd0.le).trans (Real.rpow_le_rpow_of_exponent_le hK hde)
  have e1 : (t : ℝ) ^ j = (t : ℝ) ^ ((t : ℝ) / 2 + 1) * (t : ℝ) ^ d := by
    rw [← Real.rpow_add ht0, ← Real.rpow_natCast]; congr 1; rw [hd]; ring
  have e2 : K ^ (((s + t : ℕ) : ℝ) / 2 + 1) = K ^ e * K ^ l := by
    rw [← Real.rpow_natCast K l, ← Real.rpow_add hK0]; congr 1; rw [he]; ring
  rw [e1, e2, mul_assoc]
  have : 0 ≤ (t : ℝ) ^ ((t : ℝ) / 2 + 1) := by positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htd (by positivity)) this

/-- The number of codes, as in (11.29) [alstvlm]. -/
private lemma card_codes (H : Finset Idx) (s : ℕ) {vs : Finset Idx} (h0 : (0 : Idx) ∉ vs)
    {K : ℝ} (hH : (H.card : ℝ) ≤ K) (ht : (vs.card : ℝ) ≤ K) (hK : 1 ≤ K) (ht1 : 1 ≤ vs.card) :
    ((codes H s vs).card : ℝ) ≤ (3 * 2 ^ (s + vs.card - 1) * 2 ^ (s + vs.card) : ℕ) *
      ((2 ^ (s + vs.card) * vs.card.factorial : ℕ) *
        ((vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) * K ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1))) := by
  set n := s + vs.card with hn
  set t := vs.card with htt
  set M : ℝ := ((2 ^ n * t.factorial : ℕ) : ℝ) *
    ((t : ℝ) ^ ((t : ℝ) / 2 + 1) * K ^ (((s + t : ℕ) : ℝ) / 2 + 1)) with hM
  have hterm : ∀ sh ∈ (shapes n).filter (ok n t s),
      (((permS s vs ×ˢ (lists vs (nzTot (spec sh.1 sh.2.1.blocks) sh.2.2) ×ˢ
        lists H sh.2.1.blocks.length)).image fun r => (sh, r)).card : ℝ) ≤ M := by
    intro sh hsh
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hsh).2
    have hc := (Finset.card_image_le (s := permS s vs ×ˢ (lists vs (nzTot (spec sh.1 sh.2.1.blocks)
      sh.2.2) ×ˢ lists H sh.2.1.blocks.length)) (f := fun r => (sh, r)))
    rw [Finset.card_product, Finset.card_product] at hc
    have hc' : (((permS s vs ×ˢ (lists vs (nzTot (spec sh.1 sh.2.1.blocks) sh.2.2) ×ˢ
        lists H sh.2.1.blocks.length)).image fun r => (sh, r)).card : ℝ) ≤
        ((2 ^ n * t.factorial : ℕ) : ℝ) * ((t : ℝ) ^ nzTot (spec sh.1 sh.2.1.blocks) sh.2.2 *
          (H.card : ℝ) ^ sh.2.1.blocks.length) := by
      have := hc.trans (Nat.mul_le_mul (card_permS s h0)
        (Nat.mul_le_mul (card_lists vs _) (card_lists H _)))
      exact_mod_cast this
    refine hc'.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hH _)
      (by positivity)).trans ?_
    exact real_ineq ht1 ht hK (by omega) (by omega)
  have hsum := Finset.sum_le_card_nsmul _ _ M hterm
  have hcard : (codes H s vs).card ≤ ∑ sh ∈ (shapes n).filter (ok n t s),
      ((permS s vs ×ˢ (lists vs (nzTot (spec sh.1 sh.2.1.blocks) sh.2.2) ×ˢ
        lists H sh.2.1.blocks.length)).image fun r => (sh, r)).card := Finset.card_biUnion_le
  have hsh : ((shapes n).filter (ok n t s)).card ≤ 3 * 2 ^ (n - 1) * 2 ^ n := by
    refine (Finset.card_filter_le _ _).trans ?_
    rw [shapes, Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, composition_card, mul_assoc]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (card_bools n))
  calc ((codes H s vs).card : ℝ) ≤ ∑ sh ∈ (shapes n).filter (ok n t s),
      (((permS s vs ×ˢ (lists vs (nzTot (spec sh.1 sh.2.1.blocks) sh.2.2) ×ˢ
        lists H sh.2.1.blocks.length)).image fun r => (sh, r)).card : ℝ) := by exact_mod_cast hcard
    _ ≤ ((shapes n).filter (ok n t s)).card • M := hsum
    _ ≤ (3 * 2 ^ (n - 1) * 2 ^ n : ℕ) * M := by
      rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hsh) (by positivity)


private lemma len_bl (q : Idx) (r : List Idx) :
    (evn (lab (q :: r))).length = (r.length + 1) / 2 := by
  rw [length_evn, length_lab]; simp

private lemma len_gl (q : Idx) (r : List Idx) :
    (evn (lab (q :: r)).tail).length = r.length / 2 := by
  rw [length_evn, List.length_tail, length_lab]; simp; omega

private lemma tot_sum {ι : Type*} (f : ι → Multiset (Sym2 Idx)) (g : ι → List Idx)
    (hfg : ∀ c, (f c).map tot = ↑(g c)) : ∀ cs : List ι, ((cs.map f).sum).map tot = ↑(cs.flatMap g)
  | [] => by simp
  | c :: cs => by
    rw [List.map_cons, List.sum_cons, Multiset.map_add, hfg, tot_sum f g hfg cs, List.flatMap_cons,
      Multiset.coe_add]

private lemma tot_b (c : List Idx × Bool × Bool) : (bSide (c.1, c.2.2)).map tot = ↑(bL c) := by
  unfold bSide bL
  by_cases h : c.2.2 = true
  · simp only [h, ite_true]; exact (altE_tot c.1).2
  · simp only [h, Bool.false_eq_true, ite_false]; exact (altE_tot c.1).1

private lemma tot_g (c : List Idx × Bool × Bool) : (gSide (c.1, c.2.2)).map tot = ↑(gL c) := by
  unfold gSide gL
  by_cases h : c.2.2 = true
  · simp only [h, ite_true]; exact (altE_tot c.1).1
  · simp only [h, Bool.false_eq_true, ite_false]; exact (altE_tot c.1).2

private lemma lab_zero : ∀ (a : Idx) (r : List Idx), (∀ x ∈ lab (a :: r), x = 0) →
    lst (a :: r) = a ∨ lst (a :: r) = -a
  | a, [] => fun _ => Or.inl rfl
  | a, b :: r => by
    intro h
    have hab : a + b = 0 := h _ (by simp [lab])
    have hb : b = -a := by rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hab
    have ih := lab_zero b r fun x hx => h x (by simp [lab, hx])
    have e : lst (a :: b :: r) = lst (b :: r) := rfl
    rw [e, hb] at *
    rcases ih with h' | h'
    · exact Or.inr h'
    · exact Or.inl (by rw [h', neg_neg])

private lemma mem_ilv : ∀ (xs ys : List Idx) (z : Idx), z ∈ ilv xs ys → z ∈ xs ∨ z ∈ ys
  | [], ys, z, h => by rw [ilv] at h; exact Or.inr h
  | x :: xs, ys, z, h => by
    rw [ilv] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact Or.inl (by simp)
    · rcases mem_ilv ys xs z h with h | h
      · exact Or.inr h
      · exact Or.inl (by simp [h])
termination_by xs ys => xs.length + ys.length

/-- Every configuration has a code: `s + t ≥ 2` and `t ≥ 1` ((11.11) [stgeq2]), at most
`(s+t)/2 + 1` components ((11.26) [uboundl]) and at least `l - 2 - s/2` nontrivial loops
((11.29) [alstvlm]). -/
private lemma key {H : Finset Idx} {s : ℕ} {vs : Finset Idx} (h0 : (0 : Idx) ∉ vs)
    {x : (Fin 4 → Idx) × Multiset (Sym2 Idx) × Multiset (Sym2 Idx)}
    (hA : Adm H (Multiset.replicate s 0 + vs.val) x) :
    2 ≤ s + vs.card ∧ 1 ≤ vs.card ∧ ∃ cd ∈ codes H s vs, dec (s + vs.card) cd = x := by
  obtain ⟨k, B, G⟩ := x
  have hA' := hA
  obtain ⟨h1, hHB, hHG, hSB, hSG, -, -, -, -⟩ := hA
  simp only at h1 hHB hHG hSB hSG
  obtain ⟨p, w₀, w₁, cs, ⟨v₀, hw₀, hv₀, hp₀⟩, ⟨q₁, v₁, hw₁, hv₁2, hv₁, hp₁⟩, hcs, hk, hB, hG⟩ :=
    decomp hA'
  set comps : List (List Idx × Bool × Bool) := (w₀, false, false) ::
    (w₁, false, decide (p = 0)) :: cs.map fun w => (w, true, false) with hcomps
  have eB : B = (comps.map fun c => bSide (c.1, c.2.2)).sum := by
    rw [hB]; simp [comps, add_assoc, bSide, Function.comp_def]
  have eG : G = (comps.map fun c => gSide (c.1, c.2.2)).sum := by
    rw [hG]; simp [comps, add_assoc, gSide, Function.comp_def]
  have hS : Multiset.replicate s (0 : Idx) + vs.val = ↑(slist s vs) := by
    rw [slist, ← Multiset.coe_add, Multiset.coe_replicate, Finset.coe_toList]
  have pB : (comps.flatMap bL).Perm (slist s vs) := by
    rw [← Multiset.coe_eq_coe, ← tot_sum _ _ tot_b, ← eB, hSB, hS]
  have pG : (comps.flatMap gL).Perm (slist s vs) := by
    rw [← Multiset.coe_eq_coe, ← tot_sum _ _ tot_g, ← eG, hSG, hS]
  -- facts on each component
  have hcomp : ∀ c ∈ comps, ∃ q a r, c.1 = q :: a :: r ∧
      (c.2.1 = true → (bL c).sum = (gL c).sum) ∧
      2 ≤ (bL c).length + (if c.2.1 then 0 else 1) ∧
      (c.2.1 = true → 2 ≤ (gL c).length) ∧ q ∈ H := by
    intro c hc
    have hmem : ∀ q a r, c.1 = q :: a :: r → q ∈ H := by
      intro q a r hq
      have hsa : s(q, a) ∈ (altE c.1).1 := by rw [hq]; simp [altE]
      by_cases hg : c.2.2 = true
      · have : s(q, a) ∈ gSide (c.1, c.2.2) := by simp [gSide, hg, hsa]
        have := mem_sum_map (f := fun c : List Idx × Bool × Bool => gSide (c.1, c.2.2)) hc this
        rw [← eG] at this
        exact hHG q (mem_legs.2 ⟨a, this⟩)
      · have : s(q, a) ∈ bSide (c.1, c.2.2) := by simp [bSide, hg, hsa]
        have := mem_sum_map (f := fun c : List Idx × Bool × Bool => bSide (c.1, c.2.2)) hc this
        rw [← eB] at this
        exact hHB q (mem_legs.2 ⟨a, this⟩)
    rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hv₀
      refine ⟨k 0, a, r, hw₀, by simp, ?_, by simp, hmem _ _ _ hw₀⟩
      simp only [bL, hw₀, Bool.false_eq_true, ite_false]; rw [len_bl]; simp; omega
    rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hv₁
      refine ⟨q₁, a, r, hw₁, by simp, ?_, by simp, hmem _ _ _ hw₁⟩
      by_cases hp : p = 0
      · have := hv₁2 hp
        simp only [bL, hw₁, hp, decide_true, ite_true, len_gl, List.length_cons] at this ⊢
        simp; omega
      · simp only [bL, hw₁, hp, decide_false, Bool.false_eq_true, ite_false, len_bl]; simp; omega
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hc
      obtain ⟨q, a, v, hwq, hodd, hv3, hl⟩ := hcs w hw
      refine ⟨q, a, v, hwq, ?_, ?_, ?_, hmem _ _ _ hwq⟩
      · intro _
        have hev : Even (a :: v).length := by simpa [Nat.even_add_one] using hodd
        have := alt_sum q (a :: v) hev
        simp only [bL, gL, Bool.false_eq_true, ite_false]
        rw [hwq, ← sub_eq_zero, this, ← hwq, hl, sub_self]
      · simp only [bL, Bool.false_eq_true, ite_false, ite_true, hwq, len_bl, List.length_cons]
        omega
      · intro _
        simp only [gL, Bool.false_eq_true, ite_false, hwq, len_gl, List.length_cons]
        omega
  have hne : ∀ c ∈ comps, c.1 ≠ [] ∧ (c.2.1 = true → (bL c).sum = (gL c).sum) := by
    intro c hc
    obtain ⟨q, a, r, hq, hs, -⟩ := hcomp c hc
    exact ⟨by simp [hq], hs⟩
  set n := s + vs.card with hn
  set bl := comps.map fun c => (bL c).length with hbl
  have hblsum : bl.sum = n := by rw [hbl, ← List.length_flatMap, pB.length_eq, length_slist]
  have hblpos : ∀ {i}, i ∈ bl → 0 < i := by
    intro i hi
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
    obtain ⟨_, _, _, _, _, h2, _⟩ := hcomp c hc
    split_ifs at h2 <;> omega
  let cmp : Composition n := ⟨bl, hblpos, hblsum⟩
  have g0 : (gL (w₀, false, false)).length =
      if p = 0 then (bL (w₀, false, false)).length - 1 else (bL (w₀, false, false)).length := by
    simp only [gL, bL, Bool.false_eq_true, ite_false, hw₀]
    rw [len_gl, len_bl]
    have := Nat.odd_iff.symm.trans hp₀
    split_ifs with hp <;> omega
  have g1 : (gL (w₁, false, decide (p = 0))).length = if p = 0 then
      (bL (w₁, false, decide (p = 0))).length + 1 else (bL (w₁, false, decide (p = 0))).length := by
    have := Nat.odd_iff.symm.trans hp₁
    by_cases hp : p = 0
    · simp only [gL, bL, hp, decide_true, ite_true, hw₁]
      rw [len_gl, len_bl]; omega
    · simp only [gL, bL, hp, decide_false, Bool.false_eq_true, ite_false, hw₁]
      rw [len_gl, len_bl]; omega
  have gc : ∀ w ∈ cs, (gL (w, true, false)).length = (bL (w, true, false)).length := by
    intro w hw
    obtain ⟨q, a, v, hwq, hodd, -, -⟩ := hcs w hw
    simp only [gL, bL, Bool.false_eq_true, ite_false, hwq]
    rw [len_gl, len_bl]
    have := Nat.odd_iff.1 hodd
    simp only [List.length_cons]
    omega
  have hspec : spec p bl = comps.map spc := by
    simp only [hbl, hcomps, List.map_cons, spec, spc, List.map_map]
    rw [← g0, ← g1]
    congr 2
    apply List.map_congr_left
    intro w hw
    change _ = ((bL (w, true, false)).length, (gL (w, true, false)).length, true, false)
    rw [gc w hw]
    rfl
  set gb := comps.flatMap fun c => (gL c).map zb with hgb
  set βG := comps.flatMap bL with hβG
  set nz := comps.flatMap nzv with hnz
  set ms := comps.map fun c => c.1.headD 0 with hms
  have hdec : decAll (spec p bl) βG gb nz ms = comps.map fun c => (c.1, c.2.2) := by
    rw [hspec]; exact decAll_spec comps hne
  have hj : nzTot (spec p bl) gb = nz.length := by rw [hspec]; exact nzTot_spec comps
  -- counts
  have sind : (comps.map fun c => if c.2.1 = true then 0 else 1).sum = 2 := by
    simp [hcomps, Function.comp_def]
  have sg : (comps.map fun c => (gL c).length).sum = n := by
    rw [← List.length_flatMap, pG.length_eq, length_slist]
  have sf : (comps.map fun c => ((gL c).filter fun a => !zb a).length).sum = vs.card := by
    rw [← List.length_flatMap, ← List.filter_flatMap, (pG.filter _).length_eq, filter_slist s h0,
      Finset.length_toList]
  have snz : (comps.map fun c => (nzv c).length).sum = nz.length := by
    rw [hnz, List.length_flatMap]
  have ia : (comps.map fun _ => 2).sum ≤
      (comps.map fun c => (bL c).length + if c.2.1 = true then 0 else 1).sum := by
    apply List.sum_le_sum
    intro c hc
    obtain ⟨_, _, _, _, _, h2, _⟩ := hcomp c hc
    exact h2
  have ib : (comps.map fun c => 2 * (nzv c).length + 2).sum ≤
      (comps.map fun c => ((gL c).filter fun a => !zb a).length + (gL c).length +
        2 * (if c.2.1 = true then 0 else 1)).sum := by
    apply List.sum_le_sum
    intro c hc
    obtain ⟨_, _, _, _, _, _, h3, _⟩ := hcomp c hc
    have hf := List.length_filter_le (fun a => !zb a) (gL c)
    unfold nzv
    by_cases hcy : c.2.1 = true
    · have := h3 hcy
      simp only [hcy, ite_true, List.length_dropLast]
      omega
    · simp only [hcy, Bool.false_eq_true, ite_false]
      omega
  simp only [List.sum_map_add, List.sum_map_mul_left, List.map_const', List.sum_replicate,
    smul_eq_mul] at ia ib
  rw [← hbl] at ia
  have hL : 2 ≤ comps.length := by simp [hcomps]
  have hlen : cmp.blocks.length = comps.length := by simp [cmp, hbl]
  refine ⟨by omega, ?_, ⟨(p, cmp, gb), βG, nz, ms⟩, ?_, ?_⟩
  · -- `t ≥ 1`: a chain whose labels are all `0` ends at `±k₁`
    by_contra ht0
    have hvs : vs = ∅ := Finset.card_eq_zero.1 (by omega)
    have hz : ∀ x ∈ lab w₀, x = 0 := by
      intro x hx
      have hx' : x ∈ bL (w₀, false, false) ∨ x ∈ gL (w₀, false, false) := by
        simp only [bL, gL, Bool.false_eq_true, ite_false]
        rw [← ilv_evn (lab w₀)] at hx
        exact mem_ilv _ _ _ hx
      have hxs : x ∈ slist s vs := by
        rcases hx' with h | h
        · exact pB.subset (List.mem_flatMap.2 ⟨_, by simp [hcomps], h⟩)
        · exact pG.subset (List.mem_flatMap.2 ⟨_, by simp [hcomps], h⟩)
      simp only [slist, hvs, Finset.toList_empty, List.append_nil, List.mem_replicate] at hxs
      exact hxs.2
    rw [hw₀] at hz
    have hl := lab_zero _ _ hz
    rw [← hw₀] at hl
    have hkj : ∃ j : Fin 4, j ≠ 0 ∧ k j = lst w₀ := by
      fin_cases p
      · exact ⟨1, by decide, by rw [hk]; simp [kOf]⟩
      · exact ⟨2, by decide, by rw [hk]; simp [kOf]⟩
      · exact ⟨3, by decide, by rw [hk]; simp [kOf]⟩
    obtain ⟨j, hj0, hkj⟩ := hkj
    obtain ⟨hne1, hne2⟩ := h1 0 j (Ne.symm hj0)
    rcases hl with h | h
    · exact hne1 (by rw [hkj, h])
    · exact hne2 (by rw [hkj, h, neg_neg])
  · refine Finset.mem_biUnion.2 ⟨(p, cmp, gb), Finset.mem_filter.2 ⟨?_, ?_⟩,
      Finset.mem_image.2 ⟨(βG, nz, ms), ?_, rfl⟩⟩
    · refine Finset.mem_product.2 ⟨Finset.mem_univ _, Finset.mem_product.2 ⟨Finset.mem_univ _,
        mem_bools ?_⟩⟩
      rw [hgb, List.length_flatMap]
      simp only [List.length_map]
      exact sg
    · refine ⟨?_, ?_⟩
      · rw [hlen]; omega
      · change 2 * nzTot (spec p bl) gb + 2 * cmp.blocks.length ≤ 2 * vs.card + s + 4
        rw [hj, hlen]; omega
    · refine Finset.mem_product.2 ⟨List.mem_toFinset.2 (List.mem_permutations.2 pB),
        Finset.mem_product.2 ⟨mem_lists ?_ ?_, mem_lists ?_ ?_⟩⟩
      · exact hj.symm
      · intro x hx
        obtain ⟨c, hc, hxc⟩ := List.mem_flatMap.1 hx
        have hxf : x ∈ (gL c).filter fun a => !zb a := by
          unfold nzv at hxc
          split_ifs at hxc
          · exact List.mem_of_mem_dropLast hxc
          · exact hxc
        obtain ⟨hxg, hx0⟩ := List.mem_filter.1 hxf
        have hxs : x ∈ slist s vs := pG.subset (List.mem_flatMap.2 ⟨c, hc, hxg⟩)
        have hx0' : x ≠ 0 := by simpa [zb] using hx0
        simp only [slist, List.mem_append, List.mem_replicate, Finset.mem_toList] at hxs
        rcases hxs with h | h
        · exact absurd h.2 hx0'
        · exact h
      · rw [hms, List.length_map, hlen]
      · intro x hx
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hx
        obtain ⟨q, a, r, hq, -, -, -, hqH⟩ := hcomp c hc
        rw [hq]; exact hqH
  · change (kOf p (decAll (spec p bl) βG gb nz ms),
      ((decAll (spec p bl) βG gb nz ms).map bSide).sum,
      ((decAll (spec p bl) βG gb nz ms).map gSide).sum) = (k, B, G)
    rw [hdec, List.map_map, List.map_map, eB, eG, hk]
    rfl

end HardGraph

/-- Lemma 11.3 [lem11.1], counting form of (11.19) [0.025]: for `S = s·{0} + {v_1, …, v_t}`
and `K ≥ |H|, t, 1`, there is no configuration if `s + t ≤ 1` ((11.11) [stgeq2]), and the
configurations number at most `2 · 16^{s+t} t! t^{t/2+1} K^{(s+t)/2+1}` (none if `t = 0`),
with `l ≤ (s+t)/2 + 1` components ((11.26) [uboundl]) and at least `l - 2 - s/2`
non-trivial loops ((11.29) [alstvlm]). -/
theorem HardGraph_count (H : Finset Idx) (s : ℕ) (vs : Finset Idx) (h0 : (0 : Idx) ∉ vs)
    {K : ℝ} (hH : (H.card : ℝ) ≤ K) (ht : (vs.card : ℝ) ≤ K) (hK : 1 ≤ K) :
    {x | HardGraph.Adm H (Multiset.replicate s 0 + vs.val) x}.Finite ∧
      (s + vs.card ≤ 1 → {x | HardGraph.Adm H (Multiset.replicate s 0 + vs.val) x} = ∅) ∧
      ({x | HardGraph.Adm H (Multiset.replicate s 0 + vs.val) x}.ncard : ℝ) ≤
        2 * 16 ^ (s + vs.card) * (vs.card.factorial : ℝ) *
          (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) * K ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) := by
  have hsub : {x | HardGraph.Adm H (Multiset.replicate s 0 + vs.val) x} ⊆
      ↑((HardGraph.codes H s vs).image (HardGraph.dec (s + vs.card))) := by
    intro x hx
    obtain ⟨-, -, cd, hcd, rfl⟩ := HardGraph.key h0 hx
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hcd)
  refine ⟨(Finset.finite_toSet _).subset hsub, ?_, ?_⟩
  · intro hn
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hx
    have := (HardGraph.key h0 hx).1
    omega
  · set X : ℝ := (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) *
      K ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) with hXdef
    have hX : 0 ≤ X := by positivity
    have hR : 2 * 16 ^ (s + vs.card) * (vs.card.factorial : ℝ) *
        (vs.card : ℝ) ^ ((vs.card : ℝ) / 2 + 1) * K ^ (((s + vs.card : ℕ) : ℝ) / 2 + 1) =
        ((2 * 16 ^ (s + vs.card) : ℕ) : ℝ) * vs.card.factorial * X := by
      rw [hXdef]; push_cast; ring
    rw [hR]
    rcases Set.eq_empty_or_nonempty {x | HardGraph.Adm H (Multiset.replicate s 0 + vs.val) x}
      with hE | ⟨x, hx⟩
    · rw [hE, Set.ncard_empty, Nat.cast_zero]; positivity
    obtain ⟨hn2, ht1, -⟩ := HardGraph.key h0 hx
    have h1 : ({x | HardGraph.Adm H (Multiset.replicate s 0 + vs.val) x}.ncard : ℝ) ≤
        (HardGraph.codes H s vs).card := by
      have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at this
      exact_mod_cast this.trans Finset.card_image_le
    refine h1.trans ((HardGraph.card_codes H s h0 hH ht hK ht1).trans ?_)
    rw [← hXdef]
    have hnat : 3 * 2 ^ (s + vs.card - 1) * 2 ^ (s + vs.card) * 2 ^ (s + vs.card) ≤
        2 * 16 ^ (s + vs.card) := by
      obtain ⟨m, hm⟩ : ∃ m, s + vs.card = m + 1 := ⟨s + vs.card - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      have h8 : 8 ^ m ≤ 16 ^ m := Nat.pow_le_pow_left (by norm_num) m
      have e : 2 ^ m * 2 ^ (m + 1) * 2 ^ (m + 1) = 4 * 8 ^ m := by
        rw [show (8 : ℕ) = 2 * 2 * 2 by rfl, mul_pow, mul_pow, pow_succ]; ring
      rw [pow_succ 16, mul_assoc 3, mul_assoc 3, e]
      omega
    have hnat' : ((3 * 2 ^ (s + vs.card - 1) * 2 ^ (s + vs.card) * 2 ^ (s + vs.card) : ℕ) : ℝ) ≤
        ((2 * 16 ^ (s + vs.card) : ℕ) : ℝ) := by exact_mod_cast hnat
    calc ((3 * 2 ^ (s + vs.card - 1) * 2 ^ (s + vs.card) : ℕ) : ℝ) *
          (((2 ^ (s + vs.card) * vs.card.factorial : ℕ) : ℝ) * X)
        = ((3 * 2 ^ (s + vs.card - 1) * 2 ^ (s + vs.card) * 2 ^ (s + vs.card) : ℕ) : ℝ) *
          vs.card.factorial * X := by push_cast; ring
      _ ≤ ((2 * 16 ^ (s + vs.card) : ℕ) : ℝ) * vs.card.factorial * X := by gcongr

end LHYUpper
