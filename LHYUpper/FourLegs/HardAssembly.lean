import LHYUpper.FourLegs.HighLegs
import LHYUpper.FourLegs.HardRep
import LHYUpper.FourLegs.HardBounds
import LHYUpper.FourLegs.HardJoint
import LHYUpper.FourLegs.Assembly

/-!
# Lemma 11.2 [thehardestlemma], Lemma 11.1 [113] and Lemma 4.6 [lemHAS2]

The regrouping (11.12) [temp8.173]–(11.17) of the sum (11.2) [resulthardest] over the sets
`N(α, s, {v_1, …, v_t})`, the bound (11.2) with the rate `C max(k_c, 1)⁶ ρ^{6/5} |Λ|` from
Lemma 11.3 [lem11.1] and the series (11.18) [temp8.178], and the paper forms of
Lemma 11.2 [thehardestlemma], Lemma 11.1 [113] and Lemma 4.6 [lemHAS2], (4.13).
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

section HardAssemblyAux

/-- `Ψ` of (3.18) [deffal] vanishes off `M`. -/
private lemma HA_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  exact h (by simp [trialState, hc])

private lemma HA_hardTerm_nonneg (V w : R3 → ℝ) (kc : ℝ) (N : ℕ)
    (i : Idx × Idx × Idx × Occ) : 0 ≤ FourLegs.hardTerm V w kc N i := by
  unfold FourLegs.hardTerm
  split_ifs
  · positivity
  · exact le_rfl

private lemma HA_le_num (α : Occ) : α 0 ≤ α.num := by
  have h := Finsupp.single_le_sum α (g := fun _ m => m) (fun _ _ => Nat.zero_le _) 0
  rwa [Finsupp.sum_single_index rfl] at h

/-- Every nonzero summand of (11.2) [resulthardest] lies in some `N(α, s, {v_1, …, v_t})` with
`s ≤ N`, `{v_i} ⊂ P_L`, and is at most `|Ψ(α)|²` times the weight of (11.13). -/
private lemma HA_key {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (i : Idx × Idx × Idx × Occ)
    (h : FourLegs.hardTerm V w kc N i ≠ 0) :
    ∃ κ : Occ × ℕ × Finset Idx, κ.2.1 ≤ N ∧ (∀ v ∈ κ.2.2, inPL (rhoN N) (LN N) v) ∧
      i ∈ HardJoint.NSet (rhoN N) (LN N) kc N κ.1 (Multiset.replicate κ.2.1 0 + κ.2.2.val) ∧
      FourLegs.hardTerm V w kc N i ≤
        ‖trialState V w kc N κ.1‖ ^ 2 * HardRep.wt V w N κ.2.1 κ.2.2.card := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  obtain ⟨k₁, k₂, u, γ⟩ := i
  unfold FourLegs.hardTerm at h ⊢
  split_ifs at h ⊢ with hc
  swap
  · exact absurd rfl h
  obtain ⟨hcls, hcoef⟩ := hc
  have hcls' := hcls
  obtain ⟨hk, hgen, hrest⟩ := hcls
  dsimp only at h hcoef hk hgen hrest ⊢
  obtain ⟨hβ0, hγ0⟩ := mul_ne_zero_iff.1 h
  have hβM := HA_inM (norm_ne_zero_iff.1 hβ0)
  have hγM := HA_inM (norm_ne_zero_iff.1 hγ0)
  obtain ⟨α, B, G, hB, hG, hBe, hGe, hsum, hnc⟩ :=
    HardJoint_rep (k₁ := k₁) (k₂ := k₂) (k₃ := k₁ - u) (k₄ := k₂ + u) hρ
      ⟨hk 0, hk 1, hk 2, hk 3⟩ hcoef hβM hγM
  set S := HardRep.sums B with hSdef
  set s := S.count 0 with hsdef
  set vs := (S.filter (· ≠ 0)).toFinset with hvsdef
  have hnd : (S.filter (· ≠ 0)).Nodup := by
    rw [hSdef, HardRep.sums, Multiset.filter_coe, Multiset.coe_nodup]
    exact hB.2.2.1.imp fun h => h.1
  have hS : S = Multiset.replicate s 0 + vs.val := by
    rw [hvsdef, Multiset.toFinset_val, Multiset.dedup_eq_self.2 hnd, hsdef,
      ← Multiset.filter_eq' S 0]
    exact (Multiset.filter_add_not (· = 0) S).symm
  have hcard : B.length = s + vs.card := by
    have := congrArg Multiset.card hS
    rw [hSdef, HardRep.sums, Multiset.coe_card, List.length_map, Multiset.card_add,
      Multiset.card_replicate, Finset.card_val] at this
    exact this
  have hcardG : G.length = s + vs.card := by
    have := congrArg Multiset.card hsum
    simp only [hSdef, HardRep.sums, Multiset.coe_card, List.length_map] at this
    rw [← this, hcard]
  have hsN : s ≤ N := by
    have h1 : s ≤ B.length := by
      have := Multiset.count_le_card 0 S
      rwa [hSdef, HardRep.sums, Multiset.coe_card, List.length_map] at this
    have h2 : B.length ≤ (B.map (fun o : Idx × Idx => if o.1 + o.2 = 0 then 2 else 1)).sum := by
      have := List.length_le_sum_of_one_le
        (B.map (fun o : Idx × Idx => if o.1 + o.2 = 0 then 2 else 1)) (by
          intro x hx
          obtain ⟨o, -, rfl⟩ := List.mem_map.1 hx
          split_ifs <;> omega)
      rwa [List.length_map] at this
    have h3 := hB.2.2.2
    have h4 := HA_le_num α
    rw [MBasic_num hρ hB.1] at h4
    omega
  have hvs : ∀ v ∈ vs, inPL (rhoN N) (LN N) v := by
    intro v hv
    rw [hvsdef, Multiset.mem_toFinset, Multiset.mem_filter] at hv
    obtain ⟨hvS, hv0⟩ := hv
    rw [hSdef, HardRep.sums, Multiset.mem_coe] at hvS
    obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hvS
    rcases (hB.2.1 o ho).2.2 with h0 | ⟨hPL, -⟩
    · exact absurd h0 hv0
    · exact hPL
  refine ⟨(α, s, vs), hsN, hvs, ⟨hcls', hcoef, hβM, hγM, B, G, hB, hG, hBe, hGe, hS,
    hsum ▸ hS, hnc⟩, ?_⟩
  have hwB := HardRep_weight hV hw kc hN hB (s := s) (t := vs.card) rfl hcard
  have hwG := HardRep_weight hV hw kc hN hG (s := s) (t := vs.card) (by rw [← hsum]) hcardG
  rw [← hBe] at hwB
  rw [← hGe] at hwG
  simp only
  nlinarith [sq_nonneg (‖trialState V w kc N (a4 k₁ k₂ (k₁ - u) (k₂ + u) γ).2‖ -
    ‖trialState V w kc N γ‖), norm_nonneg (trialState V w kc N (a4 k₁ k₂ (k₁ - u) (k₂ + u) γ).2),
    norm_nonneg (trialState V w kc N γ)]

/-- `P_L` of Definition 3.1 [def1] is finite. -/
private lemma HA_PL_finite {N : ℕ} (hN : 1 ≤ N) : {n | inPL (rhoN N) (LN N) n}.Finite := by
  obtain ⟨-, -, -, hL⟩ := Particles_rhoN_LN hN
  have hRL : π ≤ max ((epsP (rhoN N))⁻¹ * rhoN N ^ (1/2 : ℝ)) (π / LN N) * LN N :=
    calc π = π / LN N * LN N := (div_mul_cancel₀ π hL.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hL.le
  exact (HardBounds_card_ball hL hRL).1.subset fun n hn => hn.2.trans (le_max_left _ _)

/-- The count of Lemma 11.3 [lem11.1] with `K` free momenta, `0` for `s + t ≤ 1`. -/
private def HA_c (K : ℝ) (s t : ℕ) : ℝ :=
  if s + t ≤ 1 then 0 else
    2 * 16 ^ (s + t) * (t.factorial : ℝ) * (t : ℝ) ^ ((t : ℝ) / 2 + 1) *
      K ^ (((s + t : ℕ) : ℝ) / 2 + 1)

/-- Lemma 11.3 [lem11.1] gives the count hypothesis of the regrouping for every
`K ≥ #P_{H,c}, #P_L, 1`. -/
private lemma HA_hc {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {K : ℝ}
    (hH : ({n | inPHc (rhoN N) (LN N) kc n}.ncard : ℝ) ≤ K)
    (hT : ({n | inPL (rhoN N) (LN N) n}.ncard : ℝ) ≤ K) (hK : 1 ≤ K) :
    ∀ (α : Occ) (s : ℕ) (vs : Finset Idx), (∀ v ∈ vs, inPL (rhoN N) (LN N) v) →
      (HardJoint.NSet (rhoN N) (LN N) kc N α (Multiset.replicate s 0 + vs.val)).Finite ∧
      ((HardJoint.NSet (rhoN N) (LN N) kc N α (Multiset.replicate s 0 + vs.val)).ncard : ℝ) ≤
        HA_c K s vs.card := by
  intro α s vs hvs
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have h0 : (0 : Idx) ∉ vs := fun h => Regions_PL_ne_zero hρ (hvs 0 h) rfl
  have hvK : (vs.card : ℝ) ≤ K := by
    refine le_trans ?_ hT
    rw [← Set.ncard_coe_finset]
    exact_mod_cast Set.ncard_le_ncard (fun v hv => hvs v (Finset.mem_coe.1 hv)) (HA_PL_finite hN)
  obtain ⟨hfin, hemp, hcard⟩ := HardJoint_count (N := N) (kc := kc) hρ hL α s vs h0 hH hvK hK
  refine ⟨hfin, ?_⟩
  unfold HA_c
  split_ifs with h
  · rw [hemp h, Set.ncard_empty, Nat.cast_zero]
  · exact hcard

/-- `x^{n/2+1} = x (√x)^n`. -/
private lemma HA_rpow_half {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ ((n : ℝ) / 2 + 1) = x * √x ^ n := by
  rw [Real.rpow_add hx, Real.rpow_one, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hx.le]
  ring_nf

/-- One `(s, t)` term of the regrouped bound (11.17) with the count of Lemma 11.3 [lem11.1]
and the weight of (11.13) is at most `2K · t (a√t)^t y^s`, the term of the series of (11.18)
[temp8.178]. -/
private lemma HA_term {T s t : ℕ} {K ρ g ε m Λ : ℝ} (hK : 0 < K) (hρ : 0 ≤ ρ) (hε : 0 < ε)
    (hm : 1 ≤ m) (hΛ : 0 < Λ) :
    (T.choose t : ℝ) * HA_c K s t *
        (ρ ^ (2 * s + t) * (g / ε ^ 2) ^ (2 * s + 2 * t) * (4 * (⌈m⌉₊ : ℝ) / Λ) ^ t) ≤
      2 * K * (if 2 ≤ s + t then (t : ℝ) * (16 * 8 * T * √K * ρ * g ^ 2 * m / (ε ^ 4 * Λ) *
        √(t : ℝ)) ^ t * (16 * √K * ρ ^ 2 * g ^ 2 / ε ^ 4) ^ s else 0) := by
  unfold HA_c
  by_cases h1 : s + t ≤ 1
  · simp [h1, show ¬ 2 ≤ s + t by omega]
  simp only [h1, ite_false, show 2 ≤ s + t by omega, ite_true]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  rw [HA_rpow_half ht0, HA_rpow_half hK]
  have hg : (g / ε ^ 2) ^ (2 * s + 2 * t) = (g ^ 2 / ε ^ 4) ^ (s + t) := by ring
  rw [hg]
  have hceil : 4 * (⌈m⌉₊ : ℝ) ≤ 8 * m := by
    have := Nat.ceil_le_two_mul (a := m) (by linarith)
    linarith
  have hch : (T.choose t : ℝ) ≤ (T : ℝ) ^ t / t.factorial := by
    exact_mod_cast Nat.choose_le_pow_div (α := ℝ) t T
  have hf : (0 : ℝ) < t.factorial := by exact_mod_cast Nat.factorial_pos t
  calc _ ≤ ((T : ℝ) ^ t / t.factorial) *
        (2 * 16 ^ (s + t) * (t.factorial : ℝ) * (t * √t ^ t) * (K * √K ^ (s + t))) *
        (ρ ^ (2 * s + t) * (g ^ 2 / ε ^ 4) ^ (s + t) * (8 * m / Λ) ^ t) := by gcongr
    _ = _ := by
      field_simp
      simp only [mul_pow, div_pow, pow_add]
      ring

end HardAssemblyAux

/-- The regrouping (11.12) [temp8.173]–(11.17) of the proof of Lemma 11.2
[thehardestlemma]: if every `N(α, s, {v_1, …, v_t})` has at most `c s t` elements, then the
family (11.2) [resulthardest] is summable with sum at most
`Σ_{s ≤ N} Σ_{t ≤ #P_L} C(#P_L, t) c(s, t) W(s, t)`, `W` the weight of (11.13). -/
theorem HardAssembly_regroup {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (c : ℕ → ℕ → ℝ)
    (hc : ∀ (α : Occ) (s : ℕ) (vs : Finset Idx), (∀ v ∈ vs, inPL (rhoN N) (LN N) v) →
      (HardJoint.NSet (rhoN N) (LN N) kc N α (Multiset.replicate s 0 + vs.val)).Finite ∧
      ((HardJoint.NSet (rhoN N) (LN N) kc N α (Multiset.replicate s 0 + vs.val)).ncard : ℝ) ≤
        c s vs.card) :
    Summable (FourLegs.hardTerm V w kc N) ∧
      ∑' i, FourLegs.hardTerm V w kc N i ≤
        ∑ s ∈ Finset.range (N + 1),
          ∑ t ∈ Finset.range ({n | inPL (rhoN N) (LN N) n}.ncard + 1),
            ({n | inPL (rhoN N) (LN N) n}.ncard.choose t : ℝ) * c s t * HardRep.wt V w N s t := by
  have hPfin := HA_PL_finite hN
  set P := hPfin.toFinset with hPdef
  have hT : {n | inPL (rhoN N) (LN N) n}.ncard = P.card := Set.ncard_eq_toFinset_card _ hPfin
  have hPmem : ∀ vs : Finset Idx, vs ∈ P.powerset → ∀ v ∈ vs, inPL (rhoN N) (LN N) v := by
    intro vs hvs v hv
    exact (Set.Finite.mem_toFinset hPfin).1 (Finset.mem_powerset.1 hvs hv)
  have hwt : ∀ s t, 0 ≤ HardRep.wt V w N s t := by
    intro s t
    obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
    unfold HardRep.wt
    have : 0 ≤ (g0 V w / epsP (rhoN N) ^ 2) ^ (2 * s + 2 * t) :=
      Even.pow_nonneg ⟨s + t, by ring⟩ _
    have : 0 ≤ (4 * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3) := by positivity
    positivity
  have hc0 : ∀ s, ∀ vs ∈ P.powerset, 0 ≤ c s vs.card :=
    fun s vs hvs => (Nat.cast_nonneg _).trans (hc 0 s vs (hPmem vs hvs)).2
  -- the bound on every finite partial sum
  have hfin : ∀ F : Finset (Idx × Idx × Idx × Occ), ∑ i ∈ F, FourLegs.hardTerm V w kc N i ≤
      ∑ s ∈ Finset.range (N + 1),
        ∑ t ∈ Finset.range ({n | inPL (rhoN N) (LN N) n}.ncard + 1),
          ({n | inPL (rhoN N) (LN N) n}.ncard.choose t : ℝ) * c s t * HardRep.wt V w N s t := by
    intro F
    let key : Idx × Idx × Idx × Occ → Occ × ℕ × Finset Idx := fun i =>
      if h : FourLegs.hardTerm V w kc N i ≠ 0 then (HA_key hV hw kc hN i h).choose
      else (0, 0, ∅)
    have hkey : ∀ i, FourLegs.hardTerm V w kc N i ≠ 0 → (key i).2.1 ≤ N ∧
        (∀ v ∈ (key i).2.2, inPL (rhoN N) (LN N) v) ∧
        i ∈ HardJoint.NSet (rhoN N) (LN N) kc N (key i).1
          (Multiset.replicate (key i).2.1 0 + (key i).2.2.val) ∧
        FourLegs.hardTerm V w kc N i ≤
          ‖trialState V w kc N (key i).1‖ ^ 2 * HardRep.wt V w N (key i).2.1 (key i).2.2.card := by
      intro i h
      simp only [key, ne_eq, h, not_false_eq_true, ↓reduceDIte]
      exact (HA_key hV hw kc hN i h).choose_spec
    set F' := F.filter (fun i => FourLegs.hardTerm V w kc N i ≠ 0) with hF'
    have hF'mem : ∀ i ∈ F', FourLegs.hardTerm V w kc N i ≠ 0 :=
      fun i hi => (Finset.mem_filter.1 hi).2
    set A := F'.image (fun i => (key i).1) with hA
    set Ks := A ×ˢ (Finset.range (N + 1) ×ˢ P.powerset) with hKs
    have hmaps : ∀ i ∈ F', key i ∈ Ks := by
      intro i hi
      obtain ⟨h1, h2, -, -⟩ := hkey i (hF'mem i hi)
      refine Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hi, Finset.mem_product.2
        ⟨Finset.mem_range.2 (Nat.lt_succ_of_le h1), Finset.mem_powerset.2 ?_⟩⟩
      intro v hv
      exact (Set.Finite.mem_toFinset hPfin).2 (h2 v hv)
    have hA1 : ∑ α ∈ A, ‖trialState V w kc N α‖ ^ 2 ≤ 1 :=
      sum_le_hasSum A (fun _ _ => sq_nonneg _) (Normalization_isNState V w kc hN).1
    have hX0 : 0 ≤ ∑ s ∈ Finset.range (N + 1), ∑ vs ∈ P.powerset,
        c s vs.card * HardRep.wt V w N s vs.card :=
      Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun vs hvs =>
        mul_nonneg (hc0 s vs hvs) (hwt _ _)
    calc ∑ i ∈ F, FourLegs.hardTerm V w kc N i = ∑ i ∈ F', FourLegs.hardTerm V w kc N i :=
          (Finset.sum_filter_ne_zero F).symm
      _ = ∑ κ ∈ Ks, ∑ i ∈ F' with key i = κ, FourLegs.hardTerm V w kc N i :=
          (Finset.sum_fiberwise_of_maps_to hmaps _).symm
      _ ≤ ∑ κ ∈ Ks, ‖trialState V w kc N κ.1‖ ^ 2 *
            (c κ.2.1 κ.2.2.card * HardRep.wt V w N κ.2.1 κ.2.2.card) := by
          refine Finset.sum_le_sum fun κ hκ => ?_
          obtain ⟨-, -, hκP⟩ := Finset.mem_product.1 hκ |>.imp id Finset.mem_product.1
          have hvsP := hPmem κ.2.2 hκP
          obtain ⟨hNfin, hNc⟩ := hc κ.1 κ.2.1 κ.2.2 hvsP
          have hsub : ((F'.filter fun i => key i = κ : Finset _) : Set _) ⊆
              HardJoint.NSet (rhoN N) (LN N) kc N κ.1
                (Multiset.replicate κ.2.1 0 + κ.2.2.val) := by
            intro i hi
            obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hi)
            have := (hkey i (hF'mem i hi1)).2.2.1
            rwa [hi2] at this
          have hcnt : ((F'.filter fun i => key i = κ).card : ℝ) ≤ c κ.2.1 κ.2.2.card := by
            rw [← Set.ncard_coe_finset]
            exact le_trans (by exact_mod_cast Set.ncard_le_ncard hsub hNfin) hNc
          calc ∑ i ∈ F' with key i = κ, FourLegs.hardTerm V w kc N i
              ≤ ∑ i ∈ F' with key i = κ,
                  ‖trialState V w kc N κ.1‖ ^ 2 * HardRep.wt V w N κ.2.1 κ.2.2.card := by
                refine Finset.sum_le_sum fun i hi => ?_
                obtain ⟨hi1, hi2⟩ := Finset.mem_filter.1 hi
                have := (hkey i (hF'mem i hi1)).2.2.2
                rwa [hi2] at this
            _ = ((F'.filter fun i => key i = κ).card : ℝ) *
                  (‖trialState V w kc N κ.1‖ ^ 2 * HardRep.wt V w N κ.2.1 κ.2.2.card) := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ c κ.2.1 κ.2.2.card *
                  (‖trialState V w kc N κ.1‖ ^ 2 * HardRep.wt V w N κ.2.1 κ.2.2.card) :=
                mul_le_mul_of_nonneg_right hcnt (mul_nonneg (sq_nonneg _) (hwt _ _))
            _ = _ := by ring
      _ = (∑ α ∈ A, ‖trialState V w kc N α‖ ^ 2) *
            ∑ s ∈ Finset.range (N + 1), ∑ vs ∈ P.powerset,
              c s vs.card * HardRep.wt V w N s vs.card := by
          rw [hKs, Finset.sum_product, Finset.sum_mul]
          refine Finset.sum_congr rfl fun α _ => ?_
          rw [Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.mul_sum]
      _ ≤ 1 * ∑ s ∈ Finset.range (N + 1), ∑ vs ∈ P.powerset,
              c s vs.card * HardRep.wt V w N s vs.card :=
          mul_le_mul_of_nonneg_right hA1 hX0
      _ = _ := by
          rw [one_mul, hT]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Finset.sum_powerset_apply_card (fun t => c s t * HardRep.wt V w N s t)]
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [nsmul_eq_mul, mul_assoc]
  have hnn : 0 ≤ FourLegs.hardTerm V w kc N := fun i => HA_hardTerm_nonneg V w kc N i
  exact ⟨summable_of_sum_le hnn hfin, Real.tsum_le_of_sum_le hnn hfin⟩

/-- Lemma 11.2 [thehardestlemma], (11.2) [resulthardest], with the rate
`C max(k_c, 1)⁶ ρ^{6/5} |Λ|`; the constant depends only on `V`, `w`. -/
theorem Lemma11_2_rate {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ kc : ℝ, ∀ᶠ N in atTop, Summable (FourLegs.hardTerm V w kc N) ∧
      ∑' i, FourLegs.hardTerm V w kc N i ≤
        C * (max kc 1) ^ 6 * rhoN N ^ (6/5 : ℝ) * LN N ^ 3 := by
  refine ⟨1450000 * g0 V w ^ 4, by positivity, fun kc => ?_⟩
  set k := max kc 1 with hkdef
  have hk1 : (1 : ℝ) ≤ k := le_max_right _ _
  set G := g0 V w ^ 2 with hGdef
  have hG : 0 ≤ G := sq_nonneg _
  have hD : 0 < 8192 * k ^ 2 * (G + 1) := by positivity
  have hδ : 0 < (8192 * k ^ 2 * (G + 1))⁻¹ := inv_pos.2 hD
  have hut : Tendsto (fun N : ℕ => rhoN N ^ (1/400 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1/850 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    unfold rhoN
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  filter_upwards [eventually_ge_atTop 1, hut.eventually (gt_mem_nhds hδ)] with N hN huδ
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  -- `u = ρ^{1/400}`: every power below is a power of `u`
  set ρ := rhoN N with hρdef
  set u := ρ ^ (1/400 : ℝ) with hudef
  have hu0 : 0 < u := Real.rpow_pos_of_pos hρ _
  have hDu : 8192 * k ^ 2 * (G + 1) * u ≤ 1 := by
    have := mul_le_mul_of_nonneg_left huδ.le hD.le
    rwa [mul_inv_cancel₀ hD.ne'] at this
  have hu1 : u ≤ 1 / 8192 := by
    have : 8192 ≤ 8192 * k ^ 2 * (G + 1) := by
      have : 1 ≤ k ^ 2 := one_le_pow₀ hk1
      nlinarith
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  have hu1' : u ≤ 1 := hu1.trans (by norm_num)
  have hpow : ∀ a : ℕ, u ^ a = ρ ^ ((a : ℝ) / 400) := by
    intro a
    rw [hudef, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    ring_nf
  have hρu : ρ = u ^ 400 := by rw [hpow]; norm_num
  have hε : epsP ρ = u ^ 2 := by rw [hpow, epsP]; norm_num
  have hmc : mc ρ = (u ^ 2)⁻¹ := by rw [hpow, mc, Real.rpow_neg hρ.le]; norm_num
  have hsq : ρ ^ (1/2 : ℝ) = u ^ 200 := by rw [hpow]; norm_num
  have hΛ : LN N ^ 3 = (u ^ 1250)⁻¹ := by
    rw [hpow, LN, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le, ← Real.rpow_neg hρ.le]
    norm_num
  have h65 : ρ ^ (6/5 : ℝ) = u ^ 480 := by rw [hpow]; norm_num
  clear_value u
  -- lattice counts
  have hπ3 : π ^ 3 ≤ 32 :=
    (pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d2.le 3).trans (by norm_num)
  have h8π : 8 / π ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ π ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith [Real.pi_gt_three]) 3
  have hinv : ∀ n : ℕ, n ≠ 0 → 32 ≤ (u ^ n)⁻¹ := by
    intro n hn
    rw [le_inv_comm₀ (by norm_num) (by positivity)]
    exact (pow_le_of_le_one hu0.le hu1' hn).trans (hu1.trans (by norm_num))
  have hLπ : π ≤ LN N :=
    le_of_pow_le_pow_left₀ (by norm_num) hL.le (hπ3.trans (hΛ ▸ hinv 1250 (by norm_num)))
  have hkL : π ≤ k * LN N := le_trans hLπ (le_mul_of_one_le_left hL.le hk1)
  obtain ⟨hbf, hbc⟩ := HardBounds_card_ball hL hkL
  have hH : ({n | inPHc ρ (LN N) kc n}.ncard : ℝ) ≤ k ^ 3 * LN N ^ 3 := by
    have hHb : {n | inPHc ρ (LN N) kc n}.ncard ≤ {n : Idx | ‖mom (LN N) n‖ ≤ k}.ncard :=
      Set.ncard_le_ncard (fun n (hn : inPHc ρ (LN N) kc n) =>
        hn.2.trans (le_max_left _ _)) hbf
    refine le_trans (by exact_mod_cast hHb) (hbc.trans ?_)
    calc 8 / π ^ 3 * (k * LN N) ^ 3 ≤ 1 * (k * LN N) ^ 3 :=
          mul_le_mul_of_nonneg_right h8π (by positivity)
      _ = k ^ 3 * LN N ^ 3 := by ring
  set R := (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) with hR
  have hRL3 : (R * LN N) ^ 3 = (u ^ 656)⁻¹ := by
    rw [hR, mul_pow, hΛ, hε, hsq]
    field_simp
  have hRLπ : π ≤ R * LN N :=
    le_of_pow_le_pow_left₀ (by norm_num) (by rw [hR, hε, hsq]; positivity)
      (hπ3.trans (hRL3 ▸ hinv 656 (by norm_num)))
  obtain ⟨hbfR, hbcR⟩ := HardBounds_card_ball hL hRLπ
  set T := {n | inPL ρ (LN N) n}.ncard with hTdef
  have hTb : (T : ℝ) ≤ (u ^ 656)⁻¹ := by
    have hTR : T ≤ {n : Idx | ‖mom (LN N) n‖ ≤ R}.ncard :=
      Set.ncard_le_ncard (fun n (hn : inPL ρ (LN N) n) => hn.2) hbfR
    refine le_trans (by exact_mod_cast hTR) (hbcR.trans ?_)
    rw [← hRL3]
    calc 8 / π ^ 3 * (R * LN N) ^ 3 ≤ 1 * (R * LN N) ^ 3 :=
          mul_le_mul_of_nonneg_right h8π (by rw [hRL3]; positivity)
      _ = _ := one_mul _
  have hT1 : (T : ℝ) * u ^ 656 ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hTb (by positivity : (0 : ℝ) ≤ u ^ 656)
    rwa [inv_mul_cancel₀ (by positivity)] at this
  set K := k ^ 3 * LN N ^ 3 with hKdef
  have hK1 : 1 ≤ K := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hk1)
    (by rw [hΛ]; linarith [hinv 1250 (by norm_num)])
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK1
  have hTK : (T : ℝ) ≤ K := by
    refine hTb.trans ?_
    rw [hKdef, hΛ]
    calc (u ^ 656)⁻¹ ≤ (u ^ 1250)⁻¹ :=
          inv_anti₀ (by positivity) (pow_le_pow_of_le_one hu0.le hu1' (by norm_num))
      _ ≤ k ^ 3 * (u ^ 1250)⁻¹ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hk1)
  -- the regrouping with the count of Lemma 11.3 [lem11.1]
  obtain ⟨hs, hb⟩ := HardAssembly_regroup hV hw kc hN (HA_c K) (HA_hc hN hH hTK hK1)
  refine ⟨hs, hb.trans ?_⟩
  set κ := √(k ^ 3) with hκdef
  have hκ0 : 0 ≤ κ := Real.sqrt_nonneg _
  have hκ2 : κ ^ 2 = k ^ 3 := Real.sq_sqrt (by positivity)
  have hκk : κ ≤ k ^ 2 := by
    rw [hκdef, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [← pow_mul]
    exact pow_le_pow_right₀ hk1 (by norm_num)
  have hsK : √K = κ * (u ^ 625)⁻¹ := by
    rw [hKdef, Real.sqrt_mul (by positivity), hΛ,
      show (u ^ 1250)⁻¹ = ((u ^ 625)⁻¹) ^ 2 by rw [inv_pow, ← pow_mul],
      Real.sqrt_sq (by positivity)]
  have hKκ : K = κ ^ 2 * (u ^ 1250)⁻¹ := by rw [hKdef, hκ2, hΛ]
  set a := 16 * 8 * (T : ℝ) * √K * ρ * g0 V w ^ 2 * mc ρ / (epsP ρ ^ 4 * LN N ^ 3) with ha
  set y := 16 * √K * ρ ^ 2 * g0 V w ^ 2 / epsP ρ ^ 4 with hy
  have ha_eq : a = 128 * κ * G * ((T : ℝ) * u ^ 1015) := by
    rw [ha, hsK, hε, hmc, hΛ, hρu]
    field_simp
    ring
  have hy_eq : y = 16 * κ * G * u ^ 167 := by
    rw [hy, hsK, hε, hρu]
    field_simp
    ring
  have hsT : √(T : ℝ) * u ^ 328 ≤ 1 := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ u ^ 328), ← Real.sqrt_mul (by positivity),
      Real.sqrt_le_one, ← pow_mul]
    exact hT1
  have hu31 : u ^ 31 ≤ u := pow_le_of_le_one hu0.le hu1' (by norm_num)
  have hu167 : u ^ 167 ≤ u := pow_le_of_le_one hu0.le hu1' (by norm_num)
  have hκG : κ * G ≤ k ^ 2 * (G + 1) := mul_le_mul hκk (by linarith) hG (by positivity)
  have ha0 : 0 ≤ a := by rw [ha_eq]; positivity
  have hy0 : 0 ≤ y := by rw [hy_eq]; positivity
  have hy12 : y ≤ 1 / 2 := by
    rw [hy_eq]
    calc 16 * κ * G * u ^ 167 = 16 * (κ * G) * u ^ 167 := by ring
      _ ≤ 16 * (k ^ 2 * (G + 1)) * u := by gcongr
      _ ≤ 1 / 2 := by linarith
  have haT : a * √(T : ℝ) ≤ 1 / 2 := by
    rw [ha_eq]
    have hTu : 0 ≤ (T : ℝ) * u ^ 656 := by positivity
    calc 128 * κ * G * ((T : ℝ) * u ^ 1015) * √(T : ℝ) =
          128 * (κ * G) * (((T : ℝ) * u ^ 656) * (√(T : ℝ) * u ^ 328)) * u ^ 31 := by ring
      _ ≤ 128 * (k ^ 2 * (G + 1)) * (1 * 1) * u := by gcongr
      _ ≤ 1 / 2 := by linarith
  have hA : a ≤ 128 * κ * G * u ^ 359 := by
    rw [ha_eq]
    calc 128 * κ * G * ((T : ℝ) * u ^ 1015) = 128 * κ * G * ((T : ℝ) * u ^ 656) * u ^ 359 := by
          ring
      _ ≤ 128 * κ * G * 1 * u ^ 359 := by gcongr
      _ = _ := by ring
  -- the series (11.18) [temp8.178]
  have hterm : ∀ s t, (T.choose t : ℝ) * HA_c K s t * HardRep.wt V w N s t ≤
      2 * K * (if 2 ≤ s + t then (t : ℝ) * (a * √(t : ℝ)) ^ t * y ^ s else 0) := by
    intro s t
    have hm1 : 1 ≤ mc ρ := by
      rw [hmc]
      exact one_le_inv₀ (by positivity) |>.2 (pow_le_one₀ hu0.le hu1')
    exact HA_term hK0 hρ.le (by rw [hε]; positivity) hm1 (by positivity)
  have hu526 : u ^ 526 ≤ u ^ 480 := pow_le_pow_of_le_one hu0.le hu1' (by norm_num)
  have hu718 : u ^ 718 ≤ u ^ 480 := pow_le_pow_of_le_one hu0.le hu1' (by norm_num)
  calc ∑ s ∈ Finset.range (N + 1), ∑ t ∈ Finset.range (T + 1),
        (T.choose t : ℝ) * HA_c K s t * HardRep.wt V w N s t
      ≤ ∑ s ∈ Finset.range (N + 1), ∑ t ∈ Finset.range (T + 1),
        2 * K * (if 2 ≤ s + t then (t : ℝ) * (a * √(t : ℝ)) ^ t * y ^ s else 0) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => hterm s t
    _ = 2 * K * ∑ t ∈ Finset.Icc 1 T, ∑ s ∈ Finset.range (N + 1),
        (if 2 ≤ s + t then (t : ℝ) * (a * √(t : ℝ)) ^ t * y ^ s else 0) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        symm
        refine Finset.sum_subset (fun t ht => ?_) (fun t ht hn => ?_)
        · rw [Finset.mem_Icc] at ht
          exact Finset.mem_range.2 (by omega)
        · have ht0 : t = 0 := by
            rw [Finset.mem_Icc] at hn
            rw [Finset.mem_range] at ht
            omega
          subst ht0
          simp
    _ ≤ 2 * K * (2 * a * y + 44 * a ^ 2) := by
        gcongr
        exact HardBounds_series ha0 hy0 hy12 T N haT
    _ ≤ 2 * K * (2 * (128 * κ * G * u ^ 359) * y + 44 * (128 * κ * G * u ^ 359) ^ 2) := by
        gcongr
    _ = κ ^ 4 * G ^ 2 * (u ^ 1250)⁻¹ * (8192 * u ^ 526 + 1441792 * u ^ 718) := by
        rw [hKκ, hy_eq]
        ring
    _ ≤ κ ^ 4 * G ^ 2 * (u ^ 1250)⁻¹ * (1450000 * u ^ 480) := by
        gcongr
        linarith [pow_nonneg hu0.le 480]
    _ = 1450000 * g0 V w ^ 4 * k ^ 6 * ρ ^ (6/5 : ℝ) * LN N ^ 3 := by
        rw [h65, hΛ, show k ^ 6 = (k ^ 3) ^ 2 by ring, ← hκ2, hGdef]
        ring

/-- Lemma 11.2 [thehardestlemma], (11.2) [resulthardest]. -/
theorem Lemma11_2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma11_2 V w := by
  obtain ⟨C, hC, h⟩ := Lemma11_2_rate hV hw
  intro kc
  have hlim : Tendsto (fun N : ℕ => rhoN N ^ (6/5 : ℝ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(48/85 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    unfold rhoN
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have hpos : 0 < C * (max kc 1) ^ 6 + 1 := by positivity
  have hev := hlim.eventually (gt_mem_nhds (inv_pos.2 hpos))
  filter_upwards [h kc, hev, eventually_ge_atTop 1] with N hN hρs hN1
  obtain ⟨hs, hb⟩ := hN
  refine ⟨hs, hb.trans ?_⟩
  obtain ⟨-, hρ0, -, hL0⟩ := Particles_rhoN_LN hN1
  have hρ : 0 ≤ rhoN N ^ (6/5 : ℝ) := by positivity
  have hk : 0 ≤ C * (max kc 1) ^ 6 := by positivity
  have h1 : C * (max kc 1) ^ 6 * rhoN N ^ (6/5 : ℝ) ≤ 1 := by
    have h2 : (C * (max kc 1) ^ 6 + 1) * rhoN N ^ (6/5 : ℝ) < 1 := by
      have := mul_lt_mul_of_pos_left hρs hpos
      rwa [mul_inv_cancel₀ hpos.ne'] at this
    nlinarith
  calc C * (max kc 1) ^ 6 * rhoN N ^ (6/5 : ℝ) * LN N ^ 3 ≤ 1 * LN N ^ 3 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = LN N ^ 3 := one_mul _

/-- Lemma 11.1 [113], (11.1) [totalresultinMk1k2]. -/
theorem Lemma11_1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma11_1 V w :=
  Lemma11_1_of_Lemma11_2 hV hw (Lemma11_2 hV hw)

/-- Lemma 4.6 [lemHAS2], (4.13). -/
theorem Lemma4_6 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma4_6 V w :=
  Lemma4_6_of_Lemma11_1 hV hw (Lemma11_1 hV hw)

end LHYUpper
