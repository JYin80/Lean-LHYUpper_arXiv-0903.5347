import LHYUpper.Fock.Decomp
import LHYUpper.Fock.Expect
import LHYUpper.Riemann.Bridge
import LHYUpper.TrialState.FRatio
import LHYUpper.TrialState.Normalization
import LHYUpper.FourLegs.Defs

/-!
# The four nonzero legs of `H_{A2}`: classes, summability, Schwarz bound, ratio (§9)

The decomposition of every summand of `H_{A2}`, (4.7), into the classes of Lemma 9.1
[fourlegslemma1]; the summability of `|V_u|` over `Λ*`; the Schwarz bound for
`⟨a†_{v₁} a†_{v₂} a_{v₃} a_{v₄}⟩_Ψ` with absolute values; and the ratio bound of Lemma 9.1
[fourlegslemma1] with `ρ^{±1/20}`, squared and multiplied out.
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### The classes -/

/-- `ρ_N L_N³ = N`, `0 < ρ_N ≤ 1` and `0 < L_N` for `N ≥ 1`. -/
private lemma Classes_rhoN_LN {N : ℕ} (hN : 1 ≤ N) :
    rhoN N * LN N ^ 3 = N ∧ 0 < rhoN N ∧ rhoN N ≤ 1 ∧ 0 < LN N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hρ : 0 < rhoN N := Real.rpow_pos_of_pos hNpos _
  have hL : LN N = (N : ℝ) ^ (25 / 51 : ℝ) := by
    rw [LN, rhoN, ← Real.rpow_mul hNpos.le]
    norm_num
  refine ⟨?_, hρ, ?_, ?_⟩
  · rw [hL, rhoN, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos]
    norm_num
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)
  · rw [hL]
    exact Real.rpow_pos_of_pos hNpos _

private lemma Classes_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hM
  exact h (by simp [trialState, hM])

private lemma Classes_PL_not_PHc {ρ L kc : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inPL ρ L n) :
    ¬ inPHc ρ L kc n := fun h' => Regions_PL_PH hρ h h'.1

private lemma Classes_forall_legs {P : Idx → Prop} (p q u : Idx) :
    (∀ j, P (FourLegs.legs p q u j)) ↔ P p ∧ P q ∧ P (p - u) ∧ P (q + u) := by
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3⟩
  · rintro ⟨h0, h1, h2, h3⟩ j
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
    · exact h3

/-- At `ρ > 0` an index lies in at most one class. -/
private lemma Classes_unique {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {i : Idx × Idx × Idx × Occ}
    {c c' : FourLegs.Cls} (hc : c.mem ρ L kc N i) (hc' : c'.mem ρ L kc N i) : c = c' := by
  obtain ⟨p, q, u, α⟩ := i
  have h1 := Classes_PL_not_PHc (L := L) (kc := kc) hρ (n := p)
  have h2 := Classes_PL_not_PHc (L := L) (kc := kc) hρ (n := q)
  have h3 := Classes_PL_not_PHc (L := L) (kc := kc) hρ (n := p - u)
  have h4 := Classes_PL_not_PHc (L := L) (kc := kc) hρ (n := q + u)
  cases c <;> cases c' <;> first
    | rfl
    | (exfalso
       simp only [FourLegs.Cls.mem, Classes_forall_legs] at hc hc'
       revert hc hc' h1 h2 h3 h4
       generalize FourLegs.Gen (FourLegs.legs p q u) = g
       generalize FourLegs.InMk ρ L kc N p q (a4 p q (p - u) (q + u) α).2 = k
       generalize inPL ρ L p = a₁
       generalize inPL ρ L q = a₂
       generalize inPL ρ L (p - u) = a₃
       generalize inPL ρ L (q + u) = a₄
       generalize inPHc ρ L kc p = b₁
       generalize inPHc ρ L kc q = b₂
       generalize inPHc ρ L kc (p - u) = b₃
       generalize inPHc ρ L kc (q + u) = b₄
       intro hc hc' h1 h2 h3 h4
       simp_all)

/-- Every summand of `H_{A2}`, (4.7), for the trial state lies in exactly one class
(Lemma 9.1 [fourlegslemma1]). -/
theorem FourLegs_partTerm_eq_sum (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (i : Idx × Idx × Idx × Occ) :
    Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i =
      ∑ c : FourLegs.Cls, if c.mem (rhoN N) (LN N) kc N i then
        Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i else 0 := by
  by_cases h0 : Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i = 0
  · simp [h0]
  obtain ⟨p, q, u, α⟩ := i
  have hρ := (Classes_rhoN_LN hN).2.1
  have hmem : Decomp.Part.A2.mem p q u := by
    by_contra h
    exact h0 (by simp [Decomp.partTerm, h])
  have hint : intTerm (LN N) V (trialState V w kc N) (p, q, u, α) ≠ 0 := by
    intro h
    exact h0 (by simp [Decomp.partTerm, h])
  simp only [intTerm, ne_eq, mul_eq_zero, not_or, map_eq_zero, Complex.ofReal_eq_zero] at hint
  obtain ⟨⟨⟨⟨-, -⟩, hΨβ⟩, hc⟩, hΨα⟩ := hint
  obtain ⟨hz, hpq, hS⟩ := hmem
  have hp : p ≠ 0 := by
    intro h; simp [Decomp.zeros, h] at hz
  have hq : q ≠ 0 := by
    intro h; simp [Decomp.zeros, h] at hz
  have hpu : p - u ≠ 0 := by
    intro h; simp [Decomp.zeros, h] at hz
  have hqu : q + u ≠ 0 := by
    intro h; simp [Decomp.zeros, h] at hz
  have h13 : p ≠ p - u := fun e => hS (Or.inl (by
    have : p - u = p - 0 := by rw [← e, sub_zero]
    exact sub_right_injective this))
  have h14 : p ≠ q + u := fun e => hS (Or.inr (by rw [e]; abel))
  have hcls := Lemma9_1 hρ hp hq hpu hqu hpq h13 h14 (Classes_inM hΨβ) (Classes_inM hΨα) hc rfl
  obtain ⟨c, hcmem⟩ : ∃ c : FourLegs.Cls, c.mem (rhoN N) (LN N) kc N (p, q, u, α) := by
    rcases hcls with h | h | h | h | h
    · exact ⟨.one, (Classes_forall_legs (P := inPL (rhoN N) (LN N)) p q u).2 h⟩
    · exact ⟨.two, h⟩
    · exact ⟨.twoAdj, h⟩
    · exact ⟨.three, h⟩
    · have hall := (Classes_forall_legs (P := inPHc (rhoN N) (LN N) kc) p q u).2 h
      by_cases hg : FourLegs.Gen (FourLegs.legs p q u)
      · by_cases hk : FourLegs.InMk (rhoN N) (LN N) kc N p q (a4 p q (p - u) (q + u) α).2
        · exact ⟨.fourMain, hall, hg, hk⟩
        · exact ⟨.fourRest, hall, hg, hk⟩
      · exact ⟨.fourSpecial, hall, hg⟩
  rw [Finset.sum_eq_single c]
  · rw [ite_eq_left hcmem]
  · intro b _ hb
    rw [ite_eq_right]
    intro hb'
    exact hb (Classes_unique hρ hb' hcmem)
  · intro h
    exact absurd (Finset.mem_univ c) h

/-! ### Summability of the coefficients `V_u` -/

private lemma Classes_mom_smul (L : ℝ) (n : Idx) : mom L n = L⁻¹ • mom 1 n := by
  ext i
  simp [mom]
  ring

/-- `Σ_{u ∈ Λ*} |V_u| < ∞` for a Schwartz potential. -/
theorem FourLegs_ftV_summable {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 0 < L) :
    Summable fun u : Idx => ‖ft V (mom L u)‖ := by
  rcases le_total 1 L with h1 | h1
  · exact ((scat_lattice_V hV).choose_spec L h1).1
  obtain ⟨C, hC⟩ := scat_ft_V_decay hV 4
  obtain ⟨C', hC'⟩ := scat_lattice_decay4
  have hs := (hC' 1 le_rfl).1
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) (hs.mul_left C)
  have hmom : ‖mom 1 n‖ ≤ ‖mom L n‖ := by
    rw [Classes_mom_smul L n, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hL)]
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_inv₀ hL |>.2 h1)
  have hpos : 0 < (1 + ‖mom L n‖) ^ 4 := by positivity
  have h := hC (mom L n)
  calc ‖ft V (mom L n)‖ ≤ C * ((1 + ‖mom L n‖) ^ 4)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]
        linarith
    _ ≤ C * ((1 + ‖mom 1 n‖) ^ 4)⁻¹ := by
        gcongr

/-! ### The Schwarz bound -/

/-- `⟨β| a†_{v₁} a†_{v₂} a_{v₃} a_{v₄} |α⟩ = √(w₃₄(α)) √(w₁₂(β))`, where
`w₁₂(β) = β(v₁)β(v₂) − δ_{v₁v₂}β(v₁)` and `w₃₄(α) = α(v₃)α(v₄) − δ_{v₃v₄}α(v₃)`. -/
private lemma Classes_a4_fst (v₁ v₂ v₃ v₄ : Idx) (α : Occ) :
    (a4 v₁ v₂ v₃ v₄ α).1 =
      Real.sqrt ((α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0) *
        Real.sqrt (((a4 v₁ v₂ v₃ v₄ α).2 v₁ : ℝ) * (a4 v₁ v₂ v₃ v₄ α).2 v₂ -
          if v₁ = v₂ then ((a4 v₁ v₂ v₃ v₄ α).2 v₁ : ℝ) else 0) := by
  simp only [a4]
  set γ := α - Finsupp.single v₄ 1 - Finsupp.single v₃ 1 + Finsupp.single v₂ 1 with hγ
  have e1 : ((α v₄ : ℕ) : ℝ) * (((α - Finsupp.single v₄ 1 : Occ) v₃ : ℕ) : ℝ) =
      (α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0 := by
    by_cases h : v₃ = v₄
    · subst h
      simp only [Finsupp.tsub_apply, Finsupp.single_eq_same, ite_true]
      rcases Nat.eq_zero_or_pos (α v₃) with h0 | h0
      · simp [h0]
      · rw [Nat.cast_sub h0]; push_cast; ring
    · simp only [Finsupp.tsub_apply, Finsupp.single_apply, Ne.symm h, ite_false, h, tsub_zero]
      ring
  have e2 : ((γ v₂ : ℕ) : ℝ) * (((γ + Finsupp.single v₁ 1 : Occ) v₁ : ℕ) : ℝ) =
      ((γ + Finsupp.single v₁ 1 : Occ) v₁ : ℝ) * (γ + Finsupp.single v₁ 1 : Occ) v₂ -
        if v₁ = v₂ then ((γ + Finsupp.single v₁ 1 : Occ) v₁ : ℝ) else 0 := by
    by_cases h : v₁ = v₂
    · subst h
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, ite_true]
      push_cast; ring
    · simp only [Finsupp.add_apply, Finsupp.single_apply, h, ite_false, add_zero]
      ring
  rw [← e1, ← e2, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

/-- Schwarz bound for `⟨a†_{v₁} a†_{v₂} a_{v₃} a_{v₄}⟩_Ψ` with absolute values:
`Σ_α |Ψ(β) c Ψ(α)| ≤ ‖a_{v₁} a_{v₂} Ψ‖ ‖a_{v₃} a_{v₄} Ψ‖`. -/
theorem FourLegs_schwarz {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ v₂ v₃ v₄ : Idx) :
    ∑' α : Occ, ‖conj (Ψ (a4 v₁ v₂ v₃ v₄ α).2) * ((a4 v₁ v₂ v₃ v₄ α).1 : ℂ) * Ψ α‖ ≤
      Real.sqrt (∑' β : Occ,
          ((β v₁ : ℝ) * β v₂ - if v₁ = v₂ then (β v₁ : ℝ) else 0) * ‖Ψ β‖ ^ 2) *
        Real.sqrt (∑' α : Occ,
          ((α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0) * ‖Ψ α‖ ^ 2) := by
  set w₁₂ : Occ → ℝ := fun β => (β v₁ : ℝ) * β v₂ - if v₁ = v₂ then (β v₁ : ℝ) else 0
    with hw₁₂
  set w₃₄ : Occ → ℝ := fun α => (α v₃ : ℝ) * α v₄ - if v₃ = v₄ then (α v₃ : ℝ) else 0
    with hw₃₄
  set b : Occ → Occ := fun α => (a4 v₁ v₂ v₃ v₄ α).2 with hb
  set S : Set Occ := {α | (a4 v₁ v₂ v₃ v₄ α).1 ≠ 0} with hS
  have hw₁₂0 : ∀ β, 0 ≤ w₁₂ β := fun β => by
    rw [hw₁₂]; simp only; rw [← a4_diag_fst]; exact a4_fst_nonneg _ _ _ _ _
  have hw₃₄0 : ∀ α, 0 ≤ w₃₄ α := fun α => by
    rw [hw₃₄]; simp only; rw [← a4_diag_fst]; exact a4_fst_nonneg _ _ _ _ _
  have hwle : ∀ (x y : Idx) (β : Occ), Ψ β ≠ 0 →
      (β x : ℝ) * β y - (if x = y then (β x : ℝ) else 0) ≤ (N : ℝ) ^ 2 := fun x y β h => by
    rw [← a4_diag_fst]; exact a4_fst_le _ _ _ _ _ _ (hΨ.2 β h)
  have hsq : Summable fun β : Occ => ‖Ψ β‖ ^ 2 := hΨ.1.summable
  have hwsum : ∀ (x y : Idx), Summable fun β : Occ =>
      ((β x : ℝ) * β y - (if x = y then (β x : ℝ) else 0)) * ‖Ψ β‖ ^ 2 := fun x y => by
    refine Summable.of_nonneg_of_le (fun β => ?_) (fun β => ?_) (hsq.mul_left ((N : ℝ) ^ 2))
    · refine mul_nonneg ?_ (sq_nonneg _)
      rw [← a4_diag_fst]; exact a4_fst_nonneg _ _ _ _ _
    · by_cases h : Ψ β = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (hwle x y β h) (sq_nonneg _)
  set H : Occ → ℝ := fun β => w₁₂ β * ‖Ψ β‖ ^ 2 with hH
  have hHsum : Summable H := hwsum v₁ v₂
  have hH0 : ∀ β, 0 ≤ H β := fun β => mul_nonneg (hw₁₂0 β) (sq_nonneg _)
  set F : Occ → ℝ := fun α => if α ∈ S then Real.sqrt (w₁₂ (b α)) * ‖Ψ (b α)‖ else 0 with hF
  set G : Occ → ℝ := fun α => Real.sqrt (w₃₄ α) * ‖Ψ α‖ with hG
  have hF0 : ∀ α, 0 ≤ F α := fun α => by
    rw [hF]; simp only; split_ifs <;> positivity
  have hG0 : ∀ α, 0 ≤ G α := fun α => by rw [hG]; positivity
  have hterm : ∀ α : Occ,
      ‖conj (Ψ (a4 v₁ v₂ v₃ v₄ α).2) * ((a4 v₁ v₂ v₃ v₄ α).1 : ℂ) * Ψ α‖ = F α * G α := by
    intro α
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (a4_fst_nonneg _ _ _ _ _)]
    by_cases hα : α ∈ S
    · rw [hF, hG]
      simp only [ite_eq_left hα]
      rw [Classes_a4_fst]
      ring
    · have h0 : (a4 v₁ v₂ v₃ v₄ α).1 = 0 := by
        simpa [hS] using hα
      rw [hF]
      simp only [ite_eq_right hα, h0]
      ring
  have hinj : Function.Injective fun α : S => b α.1 := by
    intro x y h
    exact Subtype.ext (a4_injOn v₁ v₂ v₃ v₄ x.2 y.2 h)
  have hFsq : ∀ α, F α ^ (2 : ℝ) = S.indicator (fun α => H (b α)) α := by
    intro α
    rw [Real.rpow_two, hF, hH]
    by_cases hα : α ∈ S
    · simp only [ite_eq_left hα, Set.indicator_of_mem hα]
      rw [mul_pow, Real.sq_sqrt (hw₁₂0 _)]
    · simp only [ite_eq_right hα, Set.indicator_of_notMem hα]
      ring
  have hGsq : ∀ α, G α ^ (2 : ℝ) = w₃₄ α * ‖Ψ α‖ ^ 2 := by
    intro α
    rw [Real.rpow_two, hG]
    simp only
    rw [mul_pow, Real.sq_sqrt (hw₃₄0 _)]
  have hFsum : Summable fun α => F α ^ (2 : ℝ) := by
    simp only [hFsq]
    exact (summable_subtype_iff_indicator (s := S)).1 (hHsum.comp_injective hinj)
  have hGsum : Summable fun α => G α ^ (2 : ℝ) := by
    simp only [hGsq]
    exact hwsum v₃ v₄
  have hCS := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hF0 hG0
    hFsum hGsum
  have hFle : ∑' α, F α ^ (2 : ℝ) ≤ ∑' β, H β := by
    simp only [hFsq]
    rw [← tsum_subtype S (fun α => H (b α))]
    exact tsum_comp_le_tsum_of_inj hHsum hH0 hinj
  simp only [hterm]
  refine hCS.trans ?_
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  simp only [hGsq]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hFle) (Real.sqrt_nonneg _)

/-! ### The ratio bound of Lemma 9.1 [fourlegslemma1] with `ρ^{±1/20}` -/

private lemma Classes_norm_csqrt_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h, abs_of_nonneg h]
  · have h' : 0 ≤ -x := by linarith [not_le.1 h]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt h', abs_of_neg (not_le.1 h)]

private lemma Classes_trial_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} {α : Occ}
    (h : InM (rhoN N) (LN N) kc N α) :
    trialState V w kc N α = (CN V w kc N : ℂ) * f0 V w (rhoN N) (LN N) α := by
  rw [FIdentities_trialState]
  simp [h]

private lemma Classes_rpow_eps {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {x : ℝ} (hx : x = (k : ℝ) / 200) :
    ρ ^ x = epsP ρ ^ k := by
  rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ, hx]
  ring_nf

private lemma Classes_rpow_eps_neg {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {x : ℝ}
    (hx : x = -((k : ℝ) / 200)) : ρ ^ x = (epsP ρ ^ k)⁻¹ := by
  rw [hx, Real.rpow_neg hρ, Classes_rpow_eps hρ k rfl]

/-- `m_c = ε⁻¹`, (3.8) [defmc]. -/
private lemma Classes_mc {ρ : ℝ} (hρ : 0 ≤ ρ) : mc ρ = (epsP ρ)⁻¹ := by
  rw [mc, Classes_rpow_eps_neg hρ 1 (by norm_num), pow_one]

private lemma Classes_tendsto_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := 8 / 17 * a) (by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp, rhoN]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  ring_nf

private lemma Classes_ev_eps {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop, epsP (rhoN N) ≤ δ :=
  ((Classes_tendsto_rpow (a := 1 / 200) (by norm_num)).eventually_lt_const hδ).mono
    fun _ h => h.le

private lemma Classes_tendsto_rho : Tendsto rhoN atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using Classes_tendsto_rpow (a := 1) one_pos
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (Classes_rhoN_LN hN).2.1

/-- (5.10) [lublambdaPL0] at `ρ = ρ_N`, for all large `N`. -/
private lemma Classes_ev_lam {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∀ᶠ N : ℕ in atTop, ∀ (L : ℝ) (n : Idx), inPL (rhoN N) L n →
      lam V w (rhoN N) L n ≤ -(g0 V w / 2) * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹ :=
  Classes_tendsto_rho.eventually (scat_lam_PL_le hV hw)

/-- `c ≤ -ρ λ_u ≤ 1` on `P_L` with `c = g₀ ε² / 2`, (5.10) [lublambdaPL0]. -/
private lemma Classes_hlam {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w)
    {N : ℕ} (hN : 1 ≤ N)
    (hl : ∀ (L : ℝ) (n : Idx), inPL (rhoN N) L n →
      lam V w (rhoN N) L n ≤ -(g0 V w / 2) * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹)
    (u : Idx) (hu : inPL (rhoN N) (LN N) u) :
    g0 V w / 2 * epsP (rhoN N) ^ 2 ≤ -(rhoN N * lam V w (rhoN N) (LN N) u) ∧
      -(rhoN N * lam V w (rhoN N) (LN N) u) ≤ 1 := by
  have hρ := (Classes_rhoN_LN hN).2.1
  have h1 := hl _ u hu
  have h2 := scat_lam_PL hV hw _ hρ _ u hu
  constructor
  · have := mul_le_mul_of_nonneg_left h1 hρ.le
    rw [show rhoN N * (-(g0 V w / 2) * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) =
      -(g0 V w / 2 * epsP (rhoN N) ^ 2) by field_simp] at this
    linarith
  · have := mul_lt_mul_of_pos_left h2.1 hρ
    rw [show rhoN N * -(rhoN N)⁻¹ = -1 by field_simp] at this
    linarith

/-- The constant `K⁴` of the ratio bound is at most `ρ^{-1/10}` once `ε ≤ min (1/2) (2g)⁴`. -/
private lemma Classes_K4 {ρ g : ℝ} (hρ : 0 < ρ) (hg : 0 < g) (ht : epsP ρ ≤ 1 / 2)
    (ht' : epsP ρ ≤ (2 * g) ^ 4) :
    max (4 * (mc ρ + 1)) (1 / (4 * (g / 2 * epsP ρ ^ 2))) ^ 4 ≤ ρ ^ (-(1 / 10 : ℝ)) := by
  rw [Classes_mc hρ.le, Classes_rpow_eps_neg hρ.le 20 (by norm_num)]
  set t := epsP ρ with ht_def
  have t0 : 0 < t := by rw [ht_def, epsP]; positivity
  have t1 : t ≤ 1 := ht.trans (by norm_num)
  rw [show (t ^ 20)⁻¹ = 1 / t ^ 20 from (one_div _).symm, le_div_iff₀ (by positivity)]
  rcases le_total (4 * (t⁻¹ + 1)) (1 / (4 * (g / 2 * t ^ 2))) with h | h
  · rw [max_eq_right h]
    have e : (1 / (4 * (g / 2 * t ^ 2))) ^ 4 * t ^ 20 = t ^ 12 / (2 * g) ^ 4 := by
      field_simp
      ring
    rw [e, div_le_one (by positivity)]
    calc t ^ 12 ≤ t ^ 1 := pow_le_pow_of_le_one t0.le t1 (by norm_num)
      _ = t := pow_one t
      _ ≤ (2 * g) ^ 4 := ht'
  · rw [max_eq_left h]
    have e : (4 * (t⁻¹ + 1)) ^ 4 * t ^ 20 = (4 * (1 + t)) ^ 4 * t ^ 16 := by
      field_simp
    rw [e]
    have h1 : (4 * (1 + t)) ^ 4 ≤ 1296 := by
      have : 4 * (1 + t) ≤ 6 := by linarith
      calc (4 * (1 + t)) ^ 4 ≤ 6 ^ 4 := pow_le_pow_left₀ (by positivity) this 4
        _ = 1296 := by norm_num
    have h2 : t ^ 16 ≤ (1 / 2) ^ 16 := pow_le_pow_left₀ t0.le ht 16
    calc (4 * (1 + t)) ^ 4 * t ^ 16 ≤ 1296 * (1 / 2) ^ 16 :=
          mul_le_mul h1 h2 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num

/-- Lemma 9.1 [fourlegslemma1], the ratio bound with `ρ^{±1/20}`, squared and multiplied out:
`N^{F(β)} |Ψ(β)|² |λ_{v₁} λ_{v₂}| ≤ ρ^{-1/10} N^{F(α)} |Ψ(α)|² |λ_{v₃} λ_{v₄}|` and the converse,
for `α = a†_{v₁} a†_{v₂} a_{v₃} a_{v₄} β`. -/
theorem Lemma9_1_ratio_rho {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ (α β : Occ) (v : Fin 4 → Idx), (∀ i, v i ≠ 0) →
      (∀ i j, i ≠ j → Legs_pm (v i) (v j)) →
      InM (rhoN N) (LN N) kc N α → InM (rhoN N) (LN N) kc N β →
      (a4 (v 0) (v 1) (v 2) (v 3) β).1 ≠ 0 → (a4 (v 0) (v 1) (v 2) (v 3) β).2 = α →
      (N : ℝ) ^ Fal (rhoN N) (LN N) v β * (‖trialState V w kc N β‖ ^ 2 *
          |lam V w (rhoN N) (LN N) (v 0) * lam V w (rhoN N) (LN N) (v 1)|) ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) v α *
          (‖trialState V w kc N α‖ ^ 2 *
            |lam V w (rhoN N) (LN N) (v 2) * lam V w (rhoN N) (LN N) (v 3)|) ∧
      (N : ℝ) ^ Fal (rhoN N) (LN N) v α * (‖trialState V w kc N α‖ ^ 2 *
          |lam V w (rhoN N) (LN N) (v 2) * lam V w (rhoN N) (LN N) (v 3)|) ≤
        rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) v β *
          (‖trialState V w kc N β‖ ^ 2 *
            |lam V w (rhoN N) (LN N) (v 0) * lam V w (rhoN N) (LN N) (v 1)|) := by
  have hg := scat_g0_pos hV hw
  set δ : ℝ := min (1 / 2) ((2 * g0 V w) ^ 4) with hδ_def
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((eventually_ge_atTop 1).and ((Classes_ev_lam hV hw).and (Classes_ev_eps hδ)))
  refine ⟨N₀, fun N hN kc α β v h0 hpm hα hβ hne heq => ?_⟩
  obtain ⟨hN1, hl, hε⟩ := hN₀ N hN
  obtain ⟨hNL, hρ, -, hL⟩ := Classes_rhoN_LN hN1
  have hc : 0 < g0 V w / 2 * epsP (rhoN N) ^ 2 := by unfold epsP; positivity
  have hR := Lemma9_1_ratio (V := V) (w := w) (kc := kc) hρ hL hNL hc
    (Classes_hlam hV hw hN1 hl) h0 hpm hα hβ hne heq
  simp only at hR
  have hK := Classes_K4 hρ hg (hε.trans (min_le_left _ _)) (hε.trans (min_le_right _ _))
  set K := max (4 * (mc (rhoN N) + 1)) (1 / (4 * (g0 V w / 2 * epsP (rhoN N) ^ 2)))
  set Y := ‖f0 V w (rhoN N) (LN N) β * csqrt (lam V w (rhoN N) (LN N) (v 0)) *
      csqrt (lam V w (rhoN N) (LN N) (v 1))‖ ^ 2 with hY_def
  set X := ‖f0 V w (rhoN N) (LN N) α * csqrt (lam V w (rhoN N) (LN N) (v 2)) *
      csqrt (lam V w (rhoN N) (LN N) (v 3))‖ ^ 2 with hX_def
  have hY : ‖trialState V w kc N β‖ ^ 2 *
      |lam V w (rhoN N) (LN N) (v 0) * lam V w (rhoN N) (LN N) (v 1)| = CN V w kc N ^ 2 * Y := by
    rw [hY_def, Classes_trial_eq V w kc hβ, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow,
      mul_pow, Classes_norm_csqrt_sq, Classes_norm_csqrt_sq, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, abs_mul]
    ring
  have hX : ‖trialState V w kc N α‖ ^ 2 *
      |lam V w (rhoN N) (LN N) (v 2) * lam V w (rhoN N) (LN N) (v 3)| = CN V w kc N ^ 2 * X := by
    rw [hX_def, Classes_trial_eq V w kc hα, norm_mul, norm_mul, norm_mul, mul_pow, mul_pow,
      mul_pow, Classes_norm_csqrt_sq, Classes_norm_csqrt_sq, Complex.norm_real,
      Real.norm_eq_abs, sq_abs, abs_mul]
    ring
  rw [hY, hX]
  have hX0 : 0 ≤ X := by rw [hX_def]; positivity
  have hY0 : 0 ≤ Y := by rw [hY_def]; positivity
  have hC := sq_nonneg (CN V w kc N)
  have hNα : (0 : ℝ) ≤ (N : ℝ) ^ Fal (rhoN N) (LN N) v α := by positivity
  have hNβ : (0 : ℝ) ≤ (N : ℝ) ^ Fal (rhoN N) (LN N) v β := by positivity
  constructor
  · calc (N : ℝ) ^ Fal (rhoN N) (LN N) v β * (CN V w kc N ^ 2 * Y)
        = CN V w kc N ^ 2 * ((N : ℝ) ^ Fal (rhoN N) (LN N) v β * Y) := by ring
      _ ≤ CN V w kc N ^ 2 * (K ^ 4 * (N : ℝ) ^ Fal (rhoN N) (LN N) v α * X) :=
          mul_le_mul_of_nonneg_left hR.1 hC
      _ ≤ CN V w kc N ^ 2 * (rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) v α * X) := by
          gcongr
      _ = rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) v α * (CN V w kc N ^ 2 * X) := by
          ring
  · calc (N : ℝ) ^ Fal (rhoN N) (LN N) v α * (CN V w kc N ^ 2 * X)
        = CN V w kc N ^ 2 * ((N : ℝ) ^ Fal (rhoN N) (LN N) v α * X) := by ring
      _ ≤ CN V w kc N ^ 2 * (K ^ 4 * (N : ℝ) ^ Fal (rhoN N) (LN N) v β * Y) :=
          mul_le_mul_of_nonneg_left hR.2 hC
      _ ≤ CN V w kc N ^ 2 * (rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) v β * Y) := by
          gcongr
      _ = rhoN N ^ (-(1/10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) v β * (CN V w kc N ^ 2 * Y) := by
          ring

end LHYUpper
