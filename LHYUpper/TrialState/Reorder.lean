module

public import LHYUpper.TrialState.MStar

@[expose] public section

/-!
# Reordering of pair creations; Propositions 5.2 [prop1] and 5.3 [prop2]

Commutation and injectivity of the pair creations of Definition 3.3, Proposition 5.2 [prop1],
Proposition 5.3 [prop2] (with the argument of the Appendix carried out by induction on the last
creation step of Definition 3.4 [M]), and the description of `M_u^a` used in (5.19)
[ubpsiuroughPL1.5]: an element of `M` with `α(-u) = α(u) + 1`, `u ∈ P_L`, is a soft pair
creation at `u` from `M_u^s`.
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

section Reorder
variable {ρ L kc : ℝ} {N : ℕ}

/-- `a ≠ ±b`. -/
def Legs_pm (a b : Idx) : Prop := a ≠ b ∧ a ≠ -b

private lemma Reorder_neg_ne_self {u : Idx} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congrFun h i
  simp only [Pi.neg_apply] at this
  simp only [Pi.zero_apply]
  omega

/-- Value of a strict pair creation away from `0`. -/
private lemma Reorder_strict_val (k : Idx) (α : Occ) {n : Idx} (hn : n ≠ 0) :
    strictPair k α n = α n + (if n = k then 1 else 0) + (if n = -k then 1 else 0) := by
  rw [MBasic_strictPair_apply]
  simp [hn]

private lemma Reorder_strict_ne (k : Idx) (α : Occ) {n : Idx} (hn : n ≠ 0) (h1 : n ≠ k)
    (h2 : n ≠ -k) : strictPair k α n = α n := by
  rw [Reorder_strict_val k α hn]
  simp [h1, h2]

private lemma Reorder_strict_zero {k : Idx} (hk : k ≠ 0) (α : Occ) :
    strictPair k α 0 = α 0 - 2 := by
  rw [MBasic_strictPair_apply]
  have h : (0 : Idx) ≠ -k := fun h => hk (neg_eq_zero.mp h.symm)
  simp [Ne.symm hk, h]

private lemma Reorder_strict_self {k : Idx} (hk : k ≠ 0) (α : Occ) :
    strictPair k α k = α k + 1 := by
  rw [Reorder_strict_val k α hk]
  simp [(Reorder_neg_ne_self hk).symm]

private lemma Reorder_strict_neg (k : Idx) : strictPair (-k) = strictPair k := by
  funext α
  unfold strictPair
  rw [neg_neg, add_right_comm]

private lemma Reorder_ind (k v : Idx) :
    ((if v = k then 1 else 0) + (if v = -k then 1 else 0) : ℕ) =
      (if -v = k then 1 else 0) + (if -v = -k then 1 else 0) := by
  have e1 : (-v = k) ↔ (v = -k) := neg_eq_iff_eq_neg
  have e2 : (-v = -k) ↔ (v = k) := neg_inj
  simp only [e1, e2]
  rw [add_comm]

/-- A strict pair creation keeps a state symmetric at `v`. -/
private lemma Reorder_strict_symm (k : Idx) {v : Idx} {α : Occ} (hv : v ≠ 0)
    (h : α v = α (-v)) : strictPair k α v = strictPair k α (-v) := by
  rw [Reorder_strict_val k α hv, Reorder_strict_val k α (neg_ne_zero.mpr hv), h, add_assoc,
    add_assoc, Reorder_ind k v]

private lemma Reorder_soft_comm (u p₁ p₂ : Idx) : softPair u p₁ p₂ = softPair u p₂ p₁ := by
  funext α
  unfold softPair
  rw [add_right_comm]

private lemma Reorder_soft_ne {v p₁ p₂ n : Idx} (α : Occ) (h0 : n ≠ 0) (hv : n ≠ v)
    (h1 : n ≠ p₁) (h2 : n ≠ p₂) : softPair v p₁ p₂ α n = α n := by
  rw [MBasic_softPair_apply]
  simp [h0, hv, h1, h2]

private lemma Reorder_soft_zero {v p₁ p₂ : Idx} (α : Occ) (hv : v ≠ 0) (h1 : p₁ ≠ 0)
    (h2 : p₂ ≠ 0) : softPair v p₁ p₂ α 0 = α 0 - 1 := by
  rw [MBasic_softPair_apply]
  simp [Ne.symm hv, Ne.symm h1, Ne.symm h2]

private lemma Reorder_soft_fst {v p₁ p₂ : Idx} (α : Occ) (h0 : p₁ ≠ 0) (hv : p₁ ≠ v)
    (h12 : p₁ ≠ p₂) : softPair v p₁ p₂ α p₁ = α p₁ + 1 := by
  rw [MBasic_softPair_apply]
  simp [h0, hv, h12]

private lemma Reorder_ne_PL_PH (hρ : 0 < ρ) {a b : Idx} (ha : inPL ρ L a) (hb : inPH ρ L b) :
    a ≠ b := fun h => Regions_PL_PH hρ ha (h ▸ hb)

private lemma Reorder_ne_PL_PI {a b : Idx} (ha : inPL ρ L a) (hb : inPI ρ L b) : a ≠ b :=
  fun h => Regions_PL_PI ha (h ▸ hb)

private lemma Reorder_ne_PI_PH {a b : Idx} (ha : inPI ρ L a) (hb : inPH ρ L b) : a ≠ b :=
  fun h => Regions_PI_PH ha (h ▸ hb)

private lemma Reorder_ne_neg {a b : Idx} (h : a ≠ -b) : -a ≠ b := fun e => h (by rw [← e, neg_neg])

/-- Two strict pair creations commute when nothing truncates (Appendix). -/
theorem Reorder_strict_strict {k k' : Idx} {α : Occ} (h : 4 ≤ α 0) :
    strictPair k (strictPair k' α) = strictPair k' (strictPair k α) := by
  ext n
  simp only [MBasic_strictPair_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [↓reduceIte]
    split_ifs <;> omega
  · simp only [hn, ↓reduceIte]
    split_ifs <;> omega

/-- A soft and a strict pair creation commute when nothing truncates (Appendix). -/
theorem Reorder_soft_strict {u p₁ p₂ k : Idx} {α : Occ} (hu : u ≠ 0) (h0 : 3 ≤ α 0)
    (h1 : 1 ≤ α u) :
    softPair u p₁ p₂ (strictPair k α) = strictPair k (softPair u p₁ p₂ α) := by
  ext n
  simp only [MBasic_strictPair_apply, MBasic_softPair_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Ne.symm hu, ↓reduceIte]
    split_ifs <;> omega
  · rcases eq_or_ne n u with rfl | hnu
    · simp only [hn, ↓reduceIte]
      split_ifs <;> omega
    · simp only [hn, hnu, ↓reduceIte]
      split_ifs <;> omega

/-- Two soft pair creations at different `u ≠ u'` commute when nothing truncates (Appendix). -/
theorem Reorder_soft_soft {u p₁ p₂ u' q₁ q₂ : Idx} {α : Occ} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (huu : u ≠ u') (h0 : 2 ≤ α 0) (h1 : 1 ≤ α u) (h2 : 1 ≤ α u') :
    softPair u p₁ p₂ (softPair u' q₁ q₂ α) = softPair u' q₁ q₂ (softPair u p₁ p₂ α) := by
  ext n
  simp only [MBasic_softPair_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Ne.symm hu, Ne.symm hu', ↓reduceIte]
    split_ifs <;> omega
  · rcases eq_or_ne n u with rfl | hnu
    · simp only [hn, huu, ↓reduceIte]
      split_ifs <;> omega
    · rcases eq_or_ne n u' with rfl | hnu'
      · simp only [hn, hnu, ↓reduceIte]
        split_ifs <;> omega
      · simp only [hn, hnu, hnu', ↓reduceIte]
        split_ifs <;> omega

/-- `𝓐^u` is one to one (§7, before (7.21)). -/
theorem Reorder_strictPair_injOn (k : Idx) : Set.InjOn (strictPair k) {β : Occ | 2 ≤ β 0} := by
  intro β₁ h₁ β₂ h₂ he
  have h₁' : 2 ≤ β₁ 0 := h₁
  have h₂' : 2 ≤ β₂ 0 := h₂
  ext n
  have e := DFunLike.congr_fun he n
  simp only [MBasic_strictPair_apply] at e
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [↓reduceIte] at e
    split_ifs at e <;> omega
  · simp only [hn, ↓reduceIte] at e
    split_ifs at e <;> omega

/-- The soft pair creation at `u ≠ 0` is one to one where it does not truncate. -/
theorem Reorder_softPair_injOn {u : Idx} (hu : u ≠ 0) (p₁ p₂ : Idx) :
    Set.InjOn (softPair u p₁ p₂) {β : Occ | 1 ≤ β 0 ∧ 1 ≤ β u} := by
  intro β₁ h₁ β₂ h₂ he
  obtain ⟨h₁0, h₁u⟩ : 1 ≤ β₁ 0 ∧ 1 ≤ β₁ u := h₁
  obtain ⟨h₂0, h₂u⟩ : 1 ≤ β₂ 0 ∧ 1 ≤ β₂ u := h₂
  ext n
  have e := DFunLike.congr_fun he n
  simp only [MBasic_softPair_apply] at e
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Ne.symm hu, ↓reduceIte] at e
    split_ifs at e <;> omega
  · rcases eq_or_ne n u with rfl | hnu
    · simp only [hn, ↓reduceIte] at e
      split_ifs at e <;> omega
    · simp only [hn, hnu, ↓reduceIte] at e
      split_ifs at e <;> omega

/-- `α*` at `k` is unchanged by `𝓐^u` when `k ≠ ±u`, `k ≠ 0`. -/
private lemma Reorder_alphaStar_strict {u k : Idx} (β : Occ) (hk0 : k ≠ 0) (h1 : k ≠ u)
    (h2 : k ≠ -u) : alphaStar (strictPair u β) k = alphaStar β k := by
  unfold alphaStar
  rw [Reorder_strict_ne u β hk0 h1 h2,
    Reorder_strict_ne u β (neg_ne_zero.mpr hk0) (Reorder_ne_neg h2)
      (fun e => h1 (neg_inj.mp e))]

/-- Value at `n ∈ P_L` of a soft pair creation with created momenta in `P_H`. -/
private lemma Reorder_soft_PL (hρ : 0 < ρ) {v q₁ q₂ n : Idx} (β : Occ) (hq₁ : inPH ρ L q₁)
    (hq₂ : inPH ρ L q₂) (hn : inPL ρ L n) :
    softPair v q₁ q₂ β n = β n - (if n = v then 1 else 0) := by
  rw [MBasic_softPair_apply]
  simp [Regions_PL_ne_zero hρ hn, Reorder_ne_PL_PH hρ hn hq₁, Reorder_ne_PL_PH hρ hn hq₂]

/-- A soft pair creation at `v ∈ P_L` from a state symmetric at `v` leaves `α*` unchanged on
`P_L`. -/
private lemma Reorder_alphaStar_soft (hρ : 0 < ρ) {v q₁ q₂ k : Idx} {β : Occ}
    (hv : inPL ρ L v) (hq₁ : inPH ρ L q₁) (hq₂ : inPH ρ L q₂) (hsym : β v = β (-v))
    (hk : inPL ρ L k) : alphaStar (softPair v q₁ q₂ β) k = alphaStar β k := by
  have hv0 := Regions_PL_ne_zero hρ hv
  have hvn := Reorder_neg_ne_self hv0
  unfold alphaStar
  rw [Reorder_soft_PL hρ β hq₁ hq₂ hk, Reorder_soft_PL hρ β hq₁ hq₂ (Regions_PL_neg.2 hk)]
  by_cases h1 : k = v
  · subst h1
    simp only [↓reduceIte, hvn]
    rw [← hsym]
    omega
  · by_cases h2 : -k = v
    · have hk' : k = -v := by rw [← h2, neg_neg]
      subst hk'
      simp only [neg_neg, ↓reduceIte, hvn]
      rw [hsym]
      omega
    · simp [h1, h2]

/-- The soft pair creation at `v ∈ P_L` from a state symmetric at `v` makes it asymmetric. -/
private lemma Reorder_soft_asym (hρ : 0 < ρ) {v q₁ q₂ : Idx} {β : Occ} (hv : inPL ρ L v)
    (hq₁ : inPH ρ L q₁) (hq₂ : inPH ρ L q₂) (hsym : β v = β (-v)) (h1 : 1 ≤ β v) :
    softPair v q₁ q₂ β v + 1 = softPair v q₁ q₂ β (-v) := by
  have hvn := Reorder_neg_ne_self (Regions_PL_ne_zero hρ hv)
  rw [Reorder_soft_PL hρ β hq₁ hq₂ hv, Reorder_soft_PL hρ β hq₁ hq₂ (Regions_PL_neg.2 hv)]
  simp only [↓reduceIte, hvn]
  omega

/-- A strict pair creation moved before `𝓐^u` (proof of Proposition 5.2 [prop1]). -/
private lemma Reorder_A_strict {u k : Idx} {α' β' : Occ} (hu0 : u ≠ 0) (hku : k ≠ u)
    (hku' : k ≠ -u) (hβ' : InM ρ L kc N β') (h2 : 2 ≤ β' 0) (he : strictPair u β' = α')
    (hα2 : 2 ≤ α' 0) (hstep : InM ρ L kc N β' → 2 ≤ β' 0 → InM ρ L kc N (strictPair k β'))
    (hval : β' u + 1 = α' u) :
    ∃ β, InM ρ L kc N β ∧ 2 ≤ β 0 ∧ strictPair u β = strictPair k α' ∧
      β u + 1 = strictPair k α' u := by
  have hz : α' 0 = β' 0 - 2 := by rw [← he, Reorder_strict_zero hu0]
  have huk : u ≠ -k := fun e => hku' (by rw [e, neg_neg])
  refine ⟨strictPair k β', hstep hβ' h2, ?_, ?_, ?_⟩
  · rw [MBasic_strictPair_apply]
    split_ifs <;> omega
  · rw [Reorder_strict_strict (by omega), he]
  · rw [Reorder_strict_ne k β' hu0 (Ne.symm hku) huk, Reorder_strict_ne k α' hu0 (Ne.symm hku) huk,
      hval]

/-- A soft pair creation moved before `𝓐^u` (proof of Proposition 5.2 [prop1]). -/
private lemma Reorder_A_soft {u v p₁ p₂ : Idx} {α' β' : Occ} (hu0 : u ≠ 0) (hv0 : v ≠ 0)
    (huv : u ≠ v) (hvu : v ≠ -u) (hu1 : u ≠ p₁) (hu2 : u ≠ p₂) (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (hβ' : InM ρ L kc N β') (h2 : 2 ≤ β' 0) (he : strictPair u β' = α')
    (hval : β' u + 1 = α' u) (hsym : α' v = α' (-v)) (h0 : 1 ≤ α' 0) (h1 : 1 ≤ α' v)
    (hstep : InM ρ L kc N β' → β' v = β' (-v) → 1 ≤ β' 0 → 1 ≤ β' v →
      InM ρ L kc N (softPair v p₁ p₂ β')) :
    ∃ β, InM ρ L kc N β ∧ 2 ≤ β 0 ∧ strictPair u β = softPair v p₁ p₂ α' ∧
      β u + 1 = softPair v p₁ p₂ α' u := by
  have hz : α' 0 = β' 0 - 2 := by rw [← he, Reorder_strict_zero hu0]
  have ev : α' v = β' v := by rw [← he, Reorder_strict_ne u β' hv0 (Ne.symm huv) hvu]
  have ev' : α' (-v) = β' (-v) := by
    rw [← he, Reorder_strict_ne u β' (neg_ne_zero.mpr hv0) (Reorder_ne_neg hvu)
      (fun e => huv (neg_inj.mp e).symm)]
  refine ⟨softPair v p₁ p₂ β', hstep hβ' (by rw [← ev, ← ev', hsym]) (by omega) (by omega),
    ?_, ?_, ?_⟩
  · rw [Reorder_soft_zero β' hv0 hp₁ hp₂]
    omega
  · rw [← Reorder_soft_strict hv0 (by omega) (by omega), he]
  · rw [Reorder_soft_ne β' hu0 huv hu1 hu2, Reorder_soft_ne α' hu0 huv hu1 hu2, hval]

/-- A strict pair creation moved before a soft pair creation at `v ∈ P_L` (proofs of
Proposition 5.3 [prop2] and of (5.19) [ubpsiuroughPL1.5]). -/
private lemma Reorder_B_strict (hρ : 0 < ρ) {v q₁ q₂ k : Idx} {α' β' : Occ}
    (hv : inPL ρ L v) (hq₁ : inPH ρ L q₁) (hq₂ : inPH ρ L q₂) (hk0 : k ≠ 0)
    (hβ' : InMuS ρ L kc N v β') (h1 : 1 ≤ β' v) (he : softPair v q₁ q₂ β' = α')
    (h0 : 1 ≤ β' 0) (hα2 : 2 ≤ α' 0)
    (hstep : InM ρ L kc N β' → 2 ≤ β' 0 → InM ρ L kc N (strictPair k β')) :
    InMuS ρ L kc N v (strictPair k β') ∧ 1 ≤ strictPair k β' 0 ∧ 1 ≤ strictPair k β' v ∧
      softPair v q₁ q₂ (strictPair k β') = strictPair k α' := by
  have hv0 := Regions_PL_ne_zero hρ hv
  have hz : α' 0 = β' 0 - 1 := by
    rw [← he, Reorder_soft_zero β' hv0 (Regions_PH_ne_zero hρ hq₁) (Regions_PH_ne_zero hρ hq₂)]
  refine ⟨⟨hstep hβ'.1 (by omega), Reorder_strict_symm k hv0 hβ'.2⟩, ?_, ?_, ?_⟩
  · rw [Reorder_strict_zero hk0]
    omega
  · rw [Reorder_strict_val k β' hv0]
    omega
  · rw [Reorder_soft_strict hv0 (by omega) h1, he]

/-- A soft pair creation at `v' ≠ ±v` moved before a soft pair creation at `v ∈ P_L` (proofs of
Proposition 5.3 [prop2] and of (5.19) [ubpsiuroughPL1.5]). -/
private lemma Reorder_B_soft (hρ : 0 < ρ) {v q₁ q₂ v' p₁ p₂ : Idx} {α' β' : Occ}
    (hv : inPL ρ L v) (hq₁ : inPH ρ L q₁) (hq₂ : inPH ρ L q₂) (hv' : inPL ρ L v')
    (hp₁ : inPH ρ L p₁) (hp₂ : inPH ρ L p₂) (hvv : v' ≠ v) (hvv' : v' ≠ -v)
    (hβ' : InMuS ρ L kc N v β') (h1 : 1 ≤ β' v) (he : softPair v q₁ q₂ β' = α')
    (h0 : 1 ≤ β' 0) (hsym : α' v' = α' (-v')) (hα0 : 1 ≤ α' 0) (hα1 : 1 ≤ α' v')
    (hstep : InM ρ L kc N β' → β' v' = β' (-v') → 1 ≤ β' 0 → 1 ≤ β' v' →
      InM ρ L kc N (softPair v' p₁ p₂ β')) :
    InMuS ρ L kc N v (softPair v' p₁ p₂ β') ∧ 1 ≤ softPair v' p₁ p₂ β' 0 ∧
      1 ≤ softPair v' p₁ p₂ β' v ∧
      softPair v q₁ q₂ (softPair v' p₁ p₂ β') = softPair v' p₁ p₂ α' := by
  have hv0 := Regions_PL_ne_zero hρ hv
  have hv'0 := Regions_PL_ne_zero hρ hv'
  have hz : α' 0 = β' 0 - 1 := by
    rw [← he, Reorder_soft_zero β' hv0 (Regions_PH_ne_zero hρ hq₁) (Regions_PH_ne_zero hρ hq₂)]
  have e1 : α' v' = β' v' := by
    rw [← he, Reorder_soft_ne β' hv'0 hvv (Reorder_ne_PL_PH hρ hv' hq₁)
      (Reorder_ne_PL_PH hρ hv' hq₂)]
  have hnv' := Regions_PL_neg.2 hv'
  have e2 : α' (-v') = β' (-v') := by
    rw [← he, Reorder_soft_ne β' (neg_ne_zero.mpr hv'0) (Reorder_ne_neg hvv')
      (Reorder_ne_PL_PH hρ hnv' hq₁) (Reorder_ne_PL_PH hρ hnv' hq₂)]
  have hnv := Regions_PL_neg.2 hv
  have f1 : softPair v' p₁ p₂ β' v = β' v :=
    Reorder_soft_ne β' hv0 (Ne.symm hvv) (Reorder_ne_PL_PH hρ hv hp₁) (Reorder_ne_PL_PH hρ hv hp₂)
  have f2 : softPair v' p₁ p₂ β' (-v) = β' (-v) :=
    Reorder_soft_ne β' (neg_ne_zero.mpr hv0) (fun e => hvv' (by rw [← e]))
      (Reorder_ne_PL_PH hρ hnv hp₁) (Reorder_ne_PL_PH hρ hnv hp₂)
  refine ⟨⟨hstep hβ'.1 (by rw [← e1, ← e2, hsym]) h0 (by omega), by rw [f1, f2, hβ'.2]⟩, ?_,
    by rw [f1]; exact h1, ?_⟩
  · rw [Reorder_soft_zero β' hv'0 (Regions_PH_ne_zero hρ hp₁) (Regions_PH_ne_zero hρ hp₂)]
    omega
  · rw [Reorder_soft_soft hv0 hv'0 (Ne.symm hvv) (by omega) h1 (by omega), he]

/-- Proposition 5.2 [prop1]. -/
theorem Prop5_2 (hρ : 0 < ρ) {u : Idx} (hu : inPI ρ L u) {α : Occ} (hα : InM ρ L kc N α)
    (h1 : 1 ≤ α u) :
    ∃ β, InM ρ L kc N β ∧ 2 ≤ β 0 ∧ strictPair u β = α ∧ β u + 1 = α u := by
  have hu0 : u ≠ 0 := Regions_PI_ne_zero hρ hu
  have hnu := Regions_PI_neg.2 hu
  revert h1
  induction hα with
  | free =>
    intro h1
    simp [Ne.symm hu0] at h1
  | @strictIH α' k hα' hk h2 ih =>
    intro h1
    by_cases hku : k = u
    · subst hku
      exact ⟨α', hα', h2, rfl, (Reorder_strict_self hu0 α').symm⟩
    by_cases hku' : k = -u
    · subst hku'
      rw [Reorder_strict_neg]
      exact ⟨α', hα', h2, rfl, (Reorder_strict_self hu0 α').symm⟩
    have huk : u ≠ -k := fun e => hku' (by rw [e, neg_neg])
    rw [Reorder_strict_ne k α' hu0 (Ne.symm hku) huk] at h1
    obtain ⟨β', hβ', hβ'0, he, hv⟩ := ih h1
    exact Reorder_A_strict hu0 hku hku' hβ' hβ'0 he h2 (fun hb h => InM.strictIH hb hk h) hv
  | @strictL α' k hα' hk hmc h2 ih =>
    intro h1
    have hku : k ≠ u := Reorder_ne_PL_PI hk hu
    have hku' : k ≠ -u := Reorder_ne_PL_PI hk hnu
    have huk : u ≠ -k := fun e => hku' (by rw [e, neg_neg])
    rw [Reorder_strict_ne k α' hu0 (Ne.symm hku) huk] at h1
    obtain ⟨β', hβ', hβ'0, he, hv⟩ := ih h1
    refine Reorder_A_strict hu0 hku hku' hβ' hβ'0 he h2 (fun hb h => InM.strictL hb hk ?_ h) hv
    rw [← Reorder_alphaStar_strict β' (Regions_PL_ne_zero hρ hk) hku hku', he]
    exact hmc
  | @soft α' v p₁ p₂ hα' hv hsym hs hp₁ hp₂ hk₁ hk₂ h0 hv1 ih =>
    intro h1
    have huv : u ≠ v := Ne.symm (Reorder_ne_PL_PI hv hu)
    have hvu : v ≠ -u := Reorder_ne_PL_PI hv hnu
    have hu1 : u ≠ p₁ := Reorder_ne_PI_PH hu hp₁
    have hu2 : u ≠ p₂ := Reorder_ne_PI_PH hu hp₂
    rw [Reorder_soft_ne α' hu0 huv hu1 hu2] at h1
    obtain ⟨β', hβ', hβ'0, he, hval⟩ := ih h1
    exact Reorder_A_soft hu0 (Regions_PL_ne_zero hρ hv) huv hvu hu1 hu2
      (Regions_PH_ne_zero hρ hp₁) (Regions_PH_ne_zero hρ hp₂) hβ' hβ'0 he hval hsym h0 hv1
      (fun hb hb' hb0 hb1 => InM.soft hb hv hb' hs hp₁ hp₂ hk₁ hk₂ hb0 hb1)

/-- Proposition 5.3 [prop2]. -/
theorem Prop5_3 (hρ : 0 < ρ) {u : Idx} (hu : inPH ρ L u) {α : Occ} (hα : InM ρ L kc N α)
    (h1 : 1 ≤ α u) :
    (∃ β, InM ρ L kc N β ∧ 2 ≤ β 0 ∧ strictPair u β = α ∧ β u + 1 = α u) ∨
    (∃ v β, inPL ρ L v ∧ InMuS ρ L kc N v β ∧ 1 ≤ β 0 ∧ 1 ≤ β v ∧
      inPHc ρ L kc u ∧ inPHc ρ L kc (v - u) ∧ softPair v u (v - u) β = α ∧
      β u + 1 = α u) := by
  have hu0 : u ≠ 0 := Regions_PH_ne_zero hρ hu
  have hnu := Regions_PH_neg.2 hu
  revert h1
  induction hα with
  | free =>
    intro h1
    simp [Ne.symm hu0] at h1
  | @strictIH α' k hα' hk h2 ih =>
    intro h1
    by_cases hku : k = u
    · subst hku
      exact Or.inl ⟨α', hα', h2, rfl, (Reorder_strict_self hu0 α').symm⟩
    by_cases hku' : k = -u
    · subst hku'
      rw [Reorder_strict_neg]
      exact Or.inl ⟨α', hα', h2, rfl, (Reorder_strict_self hu0 α').symm⟩
    have huk : u ≠ -k := fun e => hku' (by rw [e, neg_neg])
    have hk0 : k ≠ 0 := by
      rcases hk with hk | hk
      · exact Regions_PI_ne_zero hρ hk
      · exact Regions_PH_ne_zero hρ hk
    rw [Reorder_strict_ne k α' hu0 (Ne.symm hku) huk] at h1
    rcases ih h1 with ⟨β', hβ', hβ'0, he, hv⟩ | ⟨v, β', hv, hβ', hb0, hb1, hc₁, hc₂, he, hval⟩
    · exact Or.inl (Reorder_A_strict hu0 hku hku' hβ' hβ'0 he h2
        (fun hb h => InM.strictIH hb hk h) hv)
    · obtain ⟨m1, m2, m3, m4⟩ := Reorder_B_strict hρ hv hc₁.1 hc₂.1 hk0 hβ' hb1 he hb0 h2
        (fun hb h => InM.strictIH hb hk h)
      refine Or.inr ⟨v, strictPair k β', hv, m1, m2, m3, hc₁, hc₂, m4, ?_⟩
      rw [Reorder_strict_ne k β' hu0 (Ne.symm hku) huk,
        Reorder_strict_ne k α' hu0 (Ne.symm hku) huk, hval]
  | @strictL α' k hα' hk hmc h2 ih =>
    intro h1
    have hku : k ≠ u := Reorder_ne_PL_PH hρ hk hu
    have hku' : k ≠ -u := Reorder_ne_PL_PH hρ hk hnu
    have huk : u ≠ -k := fun e => hku' (by rw [e, neg_neg])
    have hk0 := Regions_PL_ne_zero hρ hk
    rw [Reorder_strict_ne k α' hu0 (Ne.symm hku) huk] at h1
    rcases ih h1 with ⟨β', hβ', hβ'0, he, hv⟩ | ⟨v, β', hv, hβ', hb0, hb1, hc₁, hc₂, he, hval⟩
    · refine Or.inl (Reorder_A_strict hu0 hku hku' hβ' hβ'0 he h2
        (fun hb h => InM.strictL hb hk ?_ h) hv)
      rw [← Reorder_alphaStar_strict β' hk0 hku hku', he]
      exact hmc
    · have hst : InM ρ L kc N β' → 2 ≤ β' 0 → InM ρ L kc N (strictPair k β') := by
        intro hb h
        refine InM.strictL hb hk ?_ h
        rw [← Reorder_alphaStar_soft hρ hv hc₁.1 hc₂.1 hβ'.2 hk, he]
        exact hmc
      obtain ⟨m1, m2, m3, m4⟩ := Reorder_B_strict hρ hv hc₁.1 hc₂.1 hk0 hβ' hb1 he hb0 h2 hst
      refine Or.inr ⟨v, strictPair k β', hv, m1, m2, m3, hc₁, hc₂, m4, ?_⟩
      rw [Reorder_strict_ne k β' hu0 (Ne.symm hku) huk,
        Reorder_strict_ne k α' hu0 (Ne.symm hku) huk, hval]
  | @soft α' v' p₁ p₂ hα' hv' hsym hs hp₁ hp₂ hk₁ hk₂ h0 hv1 ih =>
    intro h1
    obtain ⟨d12, -, d10, d20, d1v, -, d2v, -⟩ := Regions_soft_distinct hρ hv' hp₁ hp₂ hs
    by_cases hu1 : u = p₁
    · subst hu1
      have e : p₂ = v' - u := eq_sub_of_add_eq' hs
      refine Or.inr ⟨v', α', hv', ⟨hα', hsym⟩, h0, hv1, ⟨hp₁, hk₁⟩, ?_, ?_, ?_⟩
      · rw [← e]
        exact ⟨hp₂, hk₂⟩
      · rw [← e]
      · rw [Reorder_soft_fst α' d10 d1v d12]
    by_cases hu2 : u = p₂
    · subst hu2
      have e : p₁ = v' - u := eq_sub_of_add_eq hs
      refine Or.inr ⟨v', α', hv', ⟨hα', hsym⟩, h0, hv1, ⟨hp₂, hk₂⟩, ?_, ?_, ?_⟩
      · rw [← e]
        exact ⟨hp₁, hk₁⟩
      · rw [← e, Reorder_soft_comm]
      · rw [Reorder_soft_comm, Reorder_soft_fst α' d20 d2v (Ne.symm d12)]
    have huv : u ≠ v' := Ne.symm (Reorder_ne_PL_PH hρ hv' hu)
    have hvu : v' ≠ -u := Reorder_ne_PL_PH hρ hv' hnu
    have hv'0 := Regions_PL_ne_zero hρ hv'
    rw [Reorder_soft_ne α' hu0 huv hu1 hu2] at h1
    rcases ih h1 with ⟨β', hβ', hβ'0, he, hval⟩ | ⟨v, β', hv, hβ', hb0, hb1, hc₁, hc₂, he, hval⟩
    · exact Or.inl (Reorder_A_soft hu0 hv'0 huv hvu hu1 hu2 d10 d20 hβ' hβ'0 he hval hsym h0
        hv1 (fun hb hb' hb0 hb1 => InM.soft hb hv' hb' hs hp₁ hp₂ hk₁ hk₂ hb0 hb1))
    · have hasym := Reorder_soft_asym hρ hv hc₁.1 hc₂.1 hβ'.2 hb1
      rw [he] at hasym
      have hvv : v' ≠ v := by
        rintro rfl
        omega
      have hvv' : v' ≠ -v := by
        rintro rfl
        rw [neg_neg] at hsym
        omega
      obtain ⟨m1, m2, m3, m4⟩ := Reorder_B_soft hρ hv hc₁.1 hc₂.1 hv' hp₁ hp₂ hvv hvv' hβ' hb1
        he hb0 hsym h0 hv1
        (fun hb hb' hb0 hb1 => InM.soft hb hv' hb' hs hp₁ hp₂ hk₁ hk₂ hb0 hb1)
      refine Or.inr ⟨v, softPair v' p₁ p₂ β', hv, m1, m2, m3, hc₁, hc₂, m4, ?_⟩
      rw [Reorder_soft_ne β' hu0 huv hu1 hu2, Reorder_soft_ne α' hu0 huv hu1 hu2, hval]

/-- An element of `M_u^a` with `α(-u) = α(u) + 1` is a soft pair creation at `u` from
`M_u^s`, (5.19) [ubpsiuroughPL1.5]. -/
theorem Reorder_softLast (hρ : 0 < ρ) {u : Idx} (hu : inPL ρ L u) {α : Occ}
    (hα : InM ρ L kc N α) (ha : α (-u) = α u + 1) :
    ∃ β p₁ p₂, InMuS ρ L kc N u β ∧ inPHc ρ L kc p₁ ∧ inPHc ρ L kc p₂ ∧ p₁ + p₂ = u ∧
      1 ≤ β 0 ∧ 1 ≤ β u ∧ softPair u p₁ p₂ β = α := by
  have hu0 := Regions_PL_ne_zero hρ hu
  have hun := Reorder_neg_ne_self hu0
  have hnu := Regions_PL_neg.2 hu
  have hstrict : ∀ (k : Idx) (α' : Occ), strictPair k α' (-u) = strictPair k α' u + 1 →
      α' (-u) = α' u + 1 := by
    intro k α' h
    rw [Reorder_strict_val k α' hu0, Reorder_strict_val k α' (neg_ne_zero.mpr hu0), add_assoc,
      add_assoc, ← Reorder_ind k u] at h
    omega
  revert ha
  induction hα with
  | free =>
    intro ha
    simp [Ne.symm hu0, Ne.symm (neg_ne_zero.mpr hu0)] at ha
  | @strictIH α' k hα' hk h2 ih =>
    intro ha
    have hk0 : k ≠ 0 := by
      rcases hk with hk | hk
      · exact Regions_PI_ne_zero hρ hk
      · exact Regions_PH_ne_zero hρ hk
    obtain ⟨β', p₁, p₂, hβ', hc₁, hc₂, hs, hb0, hb1, he⟩ := ih (hstrict k α' ha)
    obtain ⟨m1, m2, m3, m4⟩ := Reorder_B_strict hρ hu hc₁.1 hc₂.1 hk0 hβ' hb1 he hb0 h2
      (fun hb h => InM.strictIH hb hk h)
    exact ⟨strictPair k β', p₁, p₂, m1, hc₁, hc₂, hs, m2, m3, m4⟩
  | @strictL α' k hα' hk hmc h2 ih =>
    intro ha
    obtain ⟨β', p₁, p₂, hβ', hc₁, hc₂, hs, hb0, hb1, he⟩ := ih (hstrict k α' ha)
    have hst : InM ρ L kc N β' → 2 ≤ β' 0 → InM ρ L kc N (strictPair k β') := by
      intro hb h
      refine InM.strictL hb hk ?_ h
      rw [← Reorder_alphaStar_soft hρ hu hc₁.1 hc₂.1 hβ'.2 hk, he]
      exact hmc
    obtain ⟨m1, m2, m3, m4⟩ :=
      Reorder_B_strict hρ hu hc₁.1 hc₂.1 (Regions_PL_ne_zero hρ hk) hβ' hb1 he hb0 h2 hst
    exact ⟨strictPair k β', p₁, p₂, m1, hc₁, hc₂, hs, m2, m3, m4⟩
  | @soft α' v q₁ q₂ hα' hv hsym hs hq₁ hq₂ hk₁ hk₂ h0 hv1 ih =>
    intro ha
    by_cases hvu : v = u
    · subst hvu
      exact ⟨α', q₁, q₂, ⟨hα', hsym⟩, ⟨hq₁, hk₁⟩, ⟨hq₂, hk₂⟩, hs, h0, hv1, rfl⟩
    by_cases hvu' : v = -u
    · exfalso
      subst hvu'
      rw [neg_neg] at hsym
      rw [Reorder_soft_PL hρ α' hq₁ hq₂ hnu, Reorder_soft_PL hρ α' hq₁ hq₂ hu] at ha
      simp only [↓reduceIte, hun.symm] at ha
      omega
    have hnv : -u ≠ v := fun e => hvu' (by rw [← e])
    rw [Reorder_soft_PL hρ α' hq₁ hq₂ hnu, Reorder_soft_PL hρ α' hq₁ hq₂ hu] at ha
    simp only [Ne.symm hvu, hnv, ↓reduceIte, tsub_zero] at ha
    obtain ⟨β', p₁, p₂, hβ', hc₁, hc₂, hs', hb0, hb1, he⟩ := ih ha
    obtain ⟨m1, m2, m3, m4⟩ := Reorder_B_soft hρ hu hc₁.1 hc₂.1 hv hq₁ hq₂ hvu hvu' hβ' hb1 he
      hb0 hsym h0 hv1 (fun hb hb' hb0 hb1 => InM.soft hb hv hb' hs hq₁ hq₂ hk₁ hk₂ hb0 hb1)
    exact ⟨softPair v q₁ q₂ β', p₁, p₂, m1, hc₁, hc₂, hs', m2, m3, m4⟩

end Reorder

/-! ### Concrete instances at `N = 2^51` (`ρ = 2^{-24}`, `L = 2^{25}`), `k_c = 10` -/

end LHYUpper
