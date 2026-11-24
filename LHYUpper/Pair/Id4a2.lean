module

public import LHYUpper.Fock.A4
public import LHYUpper.Riemann.Cells
public import LHYUpper.Scattering.Solution
public import LHYUpper.TrialState.FIdentities
public import LHYUpper.TrialState.Legs
public import LHYUpper.Pair.Identities

@[expose] public section

/-!
# Lemma 7.3 [id4a2]: `⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ` and `P(u, v)`

The series `P(u, v)` of (7.25) [defPuv]; the identity (7.26) [resultid4a2] when one of `u`, `v`
lies in `P_L ∪ P_I`; the bound on the states of `M` that are not of the form `𝓐^v γ`, behind
(7.39) [temp8.44]–(7.43); and the bound (7.27) [resultid4a2o] for `u, v ∈ P_H`.
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- `P(u, v) = Σ_{γ ∈ M} conj(Ψ(𝓐^u γ)) Ψ(𝓐^v γ) √((γ(u)+1)(γ(−u)+1)(γ(v)+1)(γ(−v)+1))`, (7.25)
[defPuv] with the complex conjugate of Lemma 7.1 [id4a], over `γ ∈ M` with `γ(0) ≥ 2`. -/
def Puv (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (u v : Idx) : ℂ :=
  ∑' γ : Occ, if InM (rhoN N) (LN N) kc N γ ∧ 2 ≤ γ 0 then
    conj (trialState V w kc N (strictPair u γ)) * trialState V w kc N (strictPair v γ) *
      (Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) * ((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1)) : ℂ)
    else 0

/-! ### Auxiliary facts -/

/-- `ρ_N L_N³ = N`, `0 < ρ_N ≤ 1` and `0 < L_N` for `N ≥ 1`. -/
private lemma Id4a2_rhoN_LN {N : ℕ} (hN : 1 ≤ N) :
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

/-- `|Re ĝ(p)| ≤ ∫ |g|`. -/
private lemma Id4a2_abs_re_ft_le (V w : R3 → ℝ) (p : R3) :
    |(ft (gfun V w) p).re| ≤ ∫ x, |gfun V w x| := by
  refine (Complex.abs_re_le_norm _).trans ?_
  unfold ft
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  ext x
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp

/-- Off `P_L`, `|λ_k| ≤ ‖g‖₁ |k|⁻²`, (5.9) [ublambda] with `‖g‖₁`. -/
private lemma Id4a2_lam_abs_le (V w : R3 → ℝ) (ρ L : ℝ) (n : Idx) (h : ¬ inPL ρ L n) :
    |lam V w ρ L n| ≤ (∫ x, |gfun V w x|) / ‖mom L n‖ ^ 2 := by
  have h0 := Id4a2_abs_re_ft_le V w (mom L n)
  simp only [lam, h, ↓reduceIte]
  rw [abs_div, abs_neg, abs_of_nonneg (by positivity : 0 ≤ ‖mom L n‖ ^ 2)]
  exact div_le_div_of_nonneg_right h0 (by positivity)

/-- On `P_H`, `|λ_k| ≤ ‖g‖₁ ε_H⁻²`. -/
private lemma Id4a2_lam_PH_le (V w : R3 → ℝ) {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx}
    (h : inPH ρ L n) : |lam V w ρ L n| ≤ (∫ x, |gfun V w x|) / epsP ρ ^ 2 := by
  have hg : 0 ≤ ∫ x, |gfun V w x| := integral_nonneg fun x => abs_nonneg _
  have hε : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  refine (Id4a2_lam_abs_le V w ρ L n fun h' => Regions_PL_PH hρ h' h).trans ?_
  exact div_le_div_of_nonneg_left hg (by positivity) (pow_le_pow_left₀ hε.le h.le 2)

/-- `‖√x‖² = |x|` for the square root of Definition 3.6. -/
private lemma Id4a2_norm_csqrt_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h, abs_of_nonneg h]
  · have h' : 0 ≤ -x := by linarith [not_le.1 h]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt h', abs_of_neg (not_le.1 h)]

/-- A single occupation number is at most the particle number. -/
private lemma Id4a2_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]; exact Nat.zero_le _

/-- `-u ≠ u` for `u ≠ 0`. -/
private lemma Id4a2_neg_ne_self {u : Idx} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congr_fun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
  omega

/-- `𝓐^{−k} = 𝓐^k`. -/
private lemma Id4a2_strictPair_neg (k : Idx) (γ : Occ) : strictPair (-k) γ = strictPair k γ := by
  unfold strictPair
  rw [neg_neg, add_right_comm]

/-- `Ψ(α) ≠ 0` forces `α ∈ M`. -/
private lemma Id4a2_inM_of_ne {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  simp [trialState, hc]

/-- The summand of `⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ` in (7.4) [resultid4a]. -/
private def Id4a2_term (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (u v : Idx) (α : Occ) : ℂ :=
  conj (trialState V w kc N (a4 u (-u) v (-v) α).2) * ((a4 u (-u) v (-v) α).1 : ℂ) *
    trialState V w kc N α

/-- `√(abcd) = √a √b √c √d` for `a, b, c ≥ 0`. -/
private lemma Id4a2_sqrt4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt (a * b * c * d) = Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul ha]

/-- `a†_u a†_{−u} a_v a_{−v} 𝓐^v γ` is `𝓐^u γ` with coefficient
`√((γ(u)+1)(γ(−u)+1)(γ(v)+1)(γ(−v)+1))`. -/
private lemma Id4a2_a4_strict {u v : Idx} (hu : u ≠ 0) (hv : v ≠ 0) (γ : Occ) :
    a4 u (-u) v (-v) (strictPair v γ) =
      (Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) * ((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1)),
        strictPair u γ) := by
  have e : strictPair v γ =
      (γ - Finsupp.single 0 2) + Finsupp.single v 1 + Finsupp.single (-v) 1 := rfl
  have hu' : -u ≠ u := Id4a2_neg_ne_self hu
  have hv' : -v ≠ v := Id4a2_neg_ne_self hv
  have hu0 : -u ≠ 0 := neg_ne_zero.2 hu
  have hv0 : -v ≠ 0 := neg_ne_zero.2 hv
  rw [e, a4_of_add]
  refine Prod.ext ?_ ?_
  · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply, Ne.symm hu, Ne.symm hv, Ne.symm hu0, Ne.symm hv0, hu',
      hv'.symm, ↓reduceIte, Nat.sub_zero, add_zero, Nat.cast_add, Nat.cast_one]
    rw [Id4a2_sqrt4 (by positivity) (by positivity) (by positivity)]
    ring
  · simp only [strictPair]
    exact add_right_comm _ _ _

/-- The summand of (7.4) [resultid4a] at `𝓐^v γ` is the summand of (7.25) [defPuv] at `γ`. -/
private lemma Id4a2_term_strict (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {u v : Idx} (hu : u ≠ 0)
    (hv : v ≠ 0) (γ : Occ) :
    Id4a2_term V w kc N u v (strictPair v γ) =
      conj (trialState V w kc N (strictPair u γ)) * trialState V w kc N (strictPair v γ) *
        (Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) * ((γ v : ℝ) + 1) *
          ((γ (-v) : ℝ) + 1)) : ℂ) := by
  rw [Id4a2_term, Id4a2_a4_strict hu hv]
  ring

/-- A series over `α` that agrees with (7.4) [resultid4a] on `𝓐^v γ`, `γ ∈ M`, and vanishes off
`{𝓐^v γ : γ ∈ M}` is `P(u, v)`. -/
private lemma Id4a2_reindex (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : u ≠ 0) (hv : v ≠ 0) (g : Occ → ℂ)
    (hg : ∀ γ, InM (rhoN N) (LN N) kc N γ →
      g (strictPair v γ) = Id4a2_term V w kc N u v (strictPair v γ))
    (hs : ∀ α, g α ≠ 0 → InM (rhoN N) (LN N) kc N α ∧
      ∃ γ, InM (rhoN N) (LN N) kc N γ ∧ strictPair v γ = α) :
    ∑' α, g α = Puv V w kc N u v := by
  have hρ := (Id4a2_rhoN_LN hN).2.1
  have hmem : ∀ γ : Occ, (if InM (rhoN N) (LN N) kc N γ ∧ 2 ≤ γ 0 then
      conj (trialState V w kc N (strictPair u γ)) * trialState V w kc N (strictPair v γ) *
        (Real.sqrt (((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) * ((γ v : ℝ) + 1) *
          ((γ (-v) : ℝ) + 1)) : ℂ) else 0) ≠ 0 →
      InM (rhoN N) (LN N) kc N γ ∧ 2 ≤ γ 0 := by
    intro γ h
    by_contra hc
    exact h (ite_eq_right hc)
  unfold Puv
  refine tsum_eq_tsum_of_ne_zero_bij (fun γ => strictPair v γ.1) ?_ ?_ ?_
  · intro γ₁ γ₂ h
    exact Subtype.ext (Reorder_strictPair_injOn v (hmem _ γ₁.2).2 (hmem _ γ₂.2).2 h)
  · intro α hα
    obtain ⟨hαM, γ, hγ, he⟩ := hs α hα
    have h2 : 2 ≤ γ 0 := MBasic_strict_le hρ hγ (he ▸ hαM)
    refine ⟨⟨γ, ?_⟩, he⟩
    rw [Function.mem_support, ite_eq_left ⟨hγ, h2⟩, ← Id4a2_term_strict V w kc N hu hv,
      ← hg γ hγ, he]
    exact hα
  · intro γ
    obtain ⟨hγ, h2⟩ := hmem _ γ.2
    rw [ite_eq_left ⟨hγ, h2⟩, hg _ hγ, Id4a2_term_strict V w kc N hu hv]

/-- A nonzero coefficient of `a†_u a†_{−u} a_v a_{−v}` on `|α⟩` needs `α(v), α(−v) ≥ 1`. -/
private lemma Id4a2_legs_pos {u v : Idx} (hv : v ≠ 0) {α : Occ}
    (h : (a4 u (-u) v (-v) α).1 ≠ 0) : 1 ≤ α v ∧ 1 ≤ α (-v) := by
  obtain ⟨β, rfl⟩ := a4_exists_add u (-u) v (-v) α h
  have hv' : -v ≠ v := Id4a2_neg_ne_self hv
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, ↓reduceIte, hv', hv'.symm]
  omega

/-- (7.26) [resultid4a2] when `v ∈ P_L ∪ P_I`. -/
private lemma Id4a2_main (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : u ≠ 0) (hv : v ≠ 0) (h : inPL (rhoN N) (LN N) v ∨ inPI (rhoN N) (LN N) v) :
    Expect.E4 (trialState V w kc N) u (-u) v (-v) = Puv V w kc N u v := by
  have hρ := (Id4a2_rhoN_LN hN).2.1
  refine Id4a2_reindex V w kc hN hu hv (Id4a2_term V w kc N u v) (fun _ _ => rfl) ?_
  intro α hα
  have hΨ : trialState V w kc N α ≠ 0 := by
    intro h0
    apply hα
    simp [Id4a2_term, h0]
  have hc : (a4 u (-u) v (-v) α).1 ≠ 0 := by
    intro h0
    apply hα
    simp [Id4a2_term, h0]
  have hαM := Id4a2_inM_of_ne hΨ
  obtain ⟨h1, h2⟩ := Id4a2_legs_pos hv hc
  obtain ⟨γ, ⟨hγ, he⟩, -⟩ := Legs_unique_gamma hρ h hαM h1 h2
  exact ⟨hαM, γ, hγ, he⟩

/-- `P(v, u) = conj P(u, v)`. -/
private lemma Id4a2_Puv_swap (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (u v : Idx) :
    Puv V w kc N u v = conj (Puv V w kc N v u) := by
  unfold Puv
  rw [Complex.conj_tsum]
  congr 1
  funext γ
  split_ifs
  · simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    rw [show ((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1) * ((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) =
      ((γ u : ℝ) + 1) * ((γ (-u) : ℝ) + 1) * ((γ v : ℝ) + 1) * ((γ (-v) : ℝ) + 1) by ring]
    ring
  · simp

/-- Lemma 7.3 [id4a2], (7.26) [resultid4a2], for `u, v ≠ 0` with `u ≠ ±v` and one of `u`, `v` in
`P_L ∪ P_I`: `⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ = P(u, v)`. -/
theorem Lemma7_3 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx} (hu : u ≠ 0)
    (hv : v ≠ 0) (huv : u ≠ v) (huv' : u + v ≠ 0)
    (h : inPL (rhoN N) (LN N) u ∨ inPI (rhoN N) (LN N) u ∨ inPL (rhoN N) (LN N) v ∨
      inPI (rhoN N) (LN N) v) :
    Expect.E4 (trialState V w kc N) u (-u) v (-v) = Puv V w kc N u v := by
  rcases h with h | h | h | h
  rotate_left 2
  · exact Id4a2_main V w kc hN hu hv (Or.inl h)
  · exact Id4a2_main V w kc hN hu hv (Or.inr h)
  all_goals
    have hu' : inPL (rhoN N) (LN N) u ∨ inPI (rhoN N) (LN N) u := by tauto
    have hΨ := Normalization_isNState V w kc hN
    rw [(Lemma7_1 N _ hΨ (-v) v (-u) u).2, Id4a2_Puv_swap]
    congr 1
    rw [← Id4a2_main V w kc hN hv hu hu']
    unfold Expect.E4
    congr 1
    funext α
    rw [a4_comm]

/-! ### The states of `M` that are not `𝓐^v γ`: (7.37) [alv'2]–(7.43) -/

/-- `ρ_N^a ≤ c` for `N` large, `a, c > 0`. -/
private lemma Id4a2_ev_rpow {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, rhoN N ^ a ≤ c := by
  have h := (tendsto_rpow_neg_atTop (by positivity : 0 < 8 / 17 * a)).comp
    tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_order.1 h).2 c hc] with N hN
  rw [rhoN, ← Real.rpow_mul (Nat.cast_nonneg N), show -(8 / 17 : ℝ) * a = -(8 / 17 * a) by ring]
  exact hN.le

/-- `ε_H^n = ρ^{n/200}`. -/
private lemma Id4a2_eps_pow {ρ : ℝ} (hρ : 0 < ρ) (n : ℕ) : epsP ρ ^ n = ρ ^ ((n : ℝ) / 200) := by
  rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  congr 1
  ring

/-- A function on `Idx` supported in `{|p_n| ≤ R}` is summable. -/
private lemma Id4a2_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
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
      have e : (mom L n).ofLp i = 2 * π / L * (n i : ℝ) := rfl
      rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
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

/-- The set `N_v` of the states of `M` that are not `𝓐^v γ` for any `γ ∈ M`. -/
private def Id4a2_Nv (kc : ℝ) (N : ℕ) (v : Idx) (α : Occ) : Prop :=
  InM (rhoN N) (LN N) kc N α ∧ ∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair v γ ≠ α

/-- `N_{−v} = N_v`. -/
private lemma Id4a2_Nv_neg {kc : ℝ} {N : ℕ} {v : Idx} {α : Occ} :
    Id4a2_Nv kc N (-v) α ↔ Id4a2_Nv kc N v α := by
  simp only [Id4a2_Nv, Id4a2_strictPair_neg]

/-- `|Ψ(α)|²` in `[0, ∞]`. -/
private def Id4a2_W (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (α : Occ) : ENNReal :=
  ENNReal.ofReal (‖trialState V w kc N α‖ ^ 2)

/-- `Σ_{α ∈ N_v, α(v) + α(−v) = j} |Ψ(α)|²`. -/
private def Id4a2_S (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (v : Idx) (j : ℕ) : ENNReal :=
  ∑' α : Occ, if Id4a2_Nv kc N v α ∧ α v + α (-v) = j then Id4a2_W V w kc N α else 0

/-- `#P_L` in `[0, ∞]`. -/
private def Id4a2_PL (N : ℕ) : ENNReal :=
  ∑' n : Idx, if inPL (rhoN N) (LN N) n then 1 else 0

/-- The factor `4ρ(m_c + 1)|Λ|⁻¹ |λ_v| ‖g‖₁ ε_H⁻²` of one soft pair creation. -/
private def Id4a2_A (V w : R3 → ℝ) (N : ℕ) (v : Idx) : ℝ :=
  4 * rhoN N * ((mc (rhoN N) + 1) / LN N ^ 3) *
    (|lam V w (rhoN N) (LN N) v| * ((∫ x, |gfun V w x|) / epsP (rhoN N) ^ 2))

private lemma Id4a2_A_nonneg (V w : R3 → ℝ) {N : ℕ} (hN : 1 ≤ N) (v : Idx) :
    0 ≤ Id4a2_A V w N v := by
  obtain ⟨-, hρ, -, hL⟩ := Id4a2_rhoN_LN hN
  have hg : 0 ≤ ∫ x, |gfun V w x| := integral_nonneg fun x => abs_nonneg _
  have hm : 0 ≤ mc (rhoN N) := Real.rpow_nonneg hρ.le _
  unfold Id4a2_A
  positivity

private lemma Id4a2_A_neg (V w : R3 → ℝ) (N : ℕ) (v : Idx) :
    Id4a2_A V w N (-v) = Id4a2_A V w N v := by
  simp only [Id4a2_A, Regions_lam_neg]

/-- One step of (7.37) [alv'2]: by Proposition 5.3 [prop2], `α ∈ N_p` with `α(p) ≥ 1`,
`p ∈ P_H`, is `𝓐^{v', ·}β` for some `v' ∈ P_L` and `β ∈ N_p` with one particle fewer at `p`,
and `|Ψ(α)|² ≤ 4ρ(m_c + 1)|Λ|⁻¹ |λ_p| ‖g‖₁ ε_H⁻² |Ψ(β)|²` by (5.7) [properf4]. -/
private lemma Id4a2_step (V w : R3 → ℝ) {kc : ℝ} {N : ℕ} (hN : 1 ≤ N) {p : Idx}
    (hp : inPH (rhoN N) (LN N) p) {α : Occ} (hα : Id4a2_Nv kc N p α) (h1 : 1 ≤ α p) :
    ∃ v' β, inPL (rhoN N) (LN N) v' ∧ Id4a2_Nv kc N p β ∧ α = softPair v' p (v' - p) β ∧
      β p + 1 = α p ∧ β (-p) = α (-p) ∧
      ‖trialState V w kc N α‖ ^ 2 ≤ Id4a2_A V w N p * ‖trialState V w kc N β‖ ^ 2 := by
  obtain ⟨hNL, hρ, -, hL⟩ := Id4a2_rhoN_LN hN
  obtain ⟨hαM, hNv⟩ := hα
  rcases Prop5_3 hρ hp hαM h1 with ⟨β, hβ, -, he, -⟩ |
      ⟨v', β, hv', ⟨hβ, hβs⟩, hβ0, hβv', hpc, hqc, he, hβp⟩
  · exact absurd he (hNv β hβ)
  have hsum : p + (v' - p) = v' := by abel
  obtain ⟨-, -, d3, -, d5, d6, -, -⟩ := Regions_soft_distinct hρ hv' hpc.1 hqc.1 hsum
  have hv0 : v' ≠ 0 := Regions_PL_ne_zero hρ hv'
  have f1 : v' ≠ -p := fun h => d6 (by rw [h, neg_neg])
  have f2 : -v' ≠ -p := fun h => d5 (neg_injective h).symm
  have f3 : -v' ≠ p := Ne.symm d6
  have f4 : -v' ≠ 0 := neg_ne_zero.2 hv0
  have f5 : (0 : Idx) ≠ -p := Ne.symm (neg_ne_zero.2 d3)
  have f6 : -p ≠ p := Id4a2_neg_ne_self d3
  have f7 : -p ≠ v' - p := fun h => hv0 (by
    have := congrArg (fun x => x + p) h
    simpa using this.symm)
  subst he
  refine ⟨v', β, hv', ⟨hβ, ?_⟩, rfl, hβp, ?_, ?_⟩
  · intro γ hγ hγe
    have h2 : 2 ≤ γ 0 := MBasic_strict_le hρ hγ (hγe ▸ hβ)
    have e0 := congrArg (fun x : Occ => x 0) hγe
    have ev := congrArg (fun x : Occ => x v') hγe
    have ev' := congrArg (fun x : Occ => x (-v')) hγe
    simp [MBasic_strictPair_apply, Ne.symm d3, f5, hv0, Ne.symm d5, f1, f2, f3, f4] at e0 ev ev'
    have hsoft : InM (rhoN N) (LN N) kc N (softPair v' p (v' - p) γ) :=
      InM.soft hγ hv' (by omega) hsum hpc.1 hqc.1 hpc.2 hqc.2 (by omega) (by omega)
    have hc := Reorder_soft_strict (u := v') (p₁ := p) (p₂ := v' - p) (k := p) (α := γ) hv0
      (by omega) (by omega)
    exact hNv _ hsoft (by rw [← hc, hγe])
  · rw [MBasic_softPair_apply]
    simp [f6, f7, Ne.symm f1, neg_ne_zero.2 d3]
  · have hf := Lemma5_1_properf4 (V := V) (w := w) hρ hL hv' hpc.1 hqc.1 hsum ⟨hβ, hβs⟩ hαM
    rw [FIdentities_trialState, ite_eq_left hαM, FIdentities_trialState, ite_eq_left hβ, hf]
    have hx0 : 0 ≤ (β 0 : ℝ) / LN N ^ 3 := by positivity
    have hxv : 0 ≤ (β v' : ℝ) / LN N ^ 3 := by positivity
    have hb0 : (β 0 : ℝ) / LN N ^ 3 ≤ rhoN N := by
      rw [div_le_iff₀ (by positivity), hNL]
      exact_mod_cast (Id4a2_occ_le_num β 0).trans (MBasic_num hρ hβ).le
    have hbv : (β v' : ℝ) / LN N ^ 3 ≤ (mc (rhoN N) + 1) / LN N ^ 3 := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h1 : (β v' : ℝ) ≤ (alphaStar β v' : ℝ) := by
        exact_mod_cast le_max_left (β v') (β (-v'))
      exact h1.trans (MStar_PL_mc hρ hβ hv').le
    have hlq := Id4a2_lam_PH_le V w hρ hqc.1
    calc _ = 4 * ((β 0 : ℝ) / LN N ^ 3) * ((β v' : ℝ) / LN N ^ 3) *
          (|lam V w (rhoN N) (LN N) p| * |lam V w (rhoN N) (LN N) (v' - p)|) *
            ‖(CN V w kc N : ℂ) * f0 V w (rhoN N) (LN N) β‖ ^ 2 := by
          simp only [norm_mul, mul_pow, Id4a2_norm_csqrt_sq, Complex.norm_real, Real.norm_eq_abs,
            sq_abs, Real.sq_sqrt hx0, Real.sq_sqrt hxv]
          ring
      _ ≤ _ := by
          have hm : 0 ≤ mc (rhoN N) := Real.rpow_nonneg hρ.le _
          unfold Id4a2_A
          gcongr

/-- The weight of `N_v` at total occupation `j + 1` of `±v` is at most `#P_L · 2A` times the
weight at `j`: the "Similarly" step of (7.42). -/
private lemma Id4a2_S_succ (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {v : Idx}
    (hv : inPH (rhoN N) (LN N) v) (j : ℕ) :
    Id4a2_S V w kc N v (j + 1) ≤
      Id4a2_PL N * Id4a2_S V w kc N v j * (ENNReal.ofReal (Id4a2_A V w N v) * 2) := by
  set A := ENNReal.ofReal (Id4a2_A V w N v) with hA
  let F : Occ → Idx → Occ → ENNReal := fun α v' β =>
    (if inPL (rhoN N) (LN N) v' then 1 else 0) *
      ((if Id4a2_Nv kc N v β ∧ β v + β (-v) = j then Id4a2_W V w kc N β else 0) *
        (A * ((if α = softPair v' v (v' - v) β then 1 else 0) +
          (if α = softPair v' (-v) (v' - -v) β then 1 else 0))))
  have hW : ∀ α β, ‖trialState V w kc N α‖ ^ 2 ≤ Id4a2_A V w N v * ‖trialState V w kc N β‖ ^ 2 →
      Id4a2_W V w kc N α ≤ A * Id4a2_W V w kc N β := by
    intro α β h
    rw [hA, Id4a2_W, Id4a2_W, ← ENNReal.ofReal_mul (Id4a2_A_nonneg V w hN v)]
    exact ENNReal.ofReal_le_ofReal h
  have hpt : ∀ α, (if Id4a2_Nv kc N v α ∧ α v + α (-v) = j + 1 then Id4a2_W V w kc N α
      else 0) ≤ ∑' v', ∑' β, F α v' β := by
    intro α
    split_ifs with hα
    swap
    · exact zero_le
    obtain ⟨hNv, hlev⟩ := hα
    have key : ∃ v' β, Id4a2_W V w kc N α ≤ F α v' β := by
      by_cases h1 : 1 ≤ α v
      · obtain ⟨v', β, hv', hβ, he, hβp, hβm, hw⟩ := Id4a2_step V w hN hv hNv h1
        refine ⟨v', β, ?_⟩
        have hlevβ : β v + β (-v) = j := by omega
        simp only [F, ite_eq_left hv',
          ite_eq_left (show Id4a2_Nv kc N v β ∧ β v + β (-v) = j from ⟨hβ, hlevβ⟩),
          ite_eq_left he, one_mul]
        calc Id4a2_W V w kc N α ≤ A * Id4a2_W V w kc N β := hW α β hw
          _ = Id4a2_W V w kc N β * (A * 1) := by ring
          _ ≤ _ := by gcongr; exact le_self_add
      · have h1' : 1 ≤ α (-v) := by omega
        obtain ⟨v', β, hv', hβ, he, hβp, hβm, hw⟩ :=
          Id4a2_step V w hN (Regions_PH_neg.2 hv) (Id4a2_Nv_neg.2 hNv) h1'
        rw [neg_neg] at hβm
        rw [Id4a2_A_neg] at hw
        refine ⟨v', β, ?_⟩
        have hlevβ : β v + β (-v) = j := by omega
        simp only [F, ite_eq_left hv', ite_eq_left
          (show Id4a2_Nv kc N v β ∧ β v + β (-v) = j from ⟨Id4a2_Nv_neg.1 hβ, hlevβ⟩),
          ite_eq_left he, one_mul]
        calc Id4a2_W V w kc N α ≤ A * Id4a2_W V w kc N β := hW α β hw
          _ = Id4a2_W V w kc N β * (A * 1) := by ring
          _ ≤ _ := by gcongr; exact le_add_self
    obtain ⟨v', β, h⟩ := key
    exact h.trans ((ENNReal.le_tsum (f := fun β => F α v' β) β).trans
      (ENNReal.le_tsum (f := fun v' => ∑' β, F α v' β) v'))
  calc Id4a2_S V w kc N v (j + 1) ≤ ∑' α, ∑' v', ∑' β, F α v' β := ENNReal.tsum_le_tsum hpt
    _ = ∑' v', ∑' β, ∑' α, F α v' β := by
        rw [ENNReal.tsum_comm]
        congr 1
        funext v'
        rw [ENNReal.tsum_comm]
    _ = ∑' v', ∑' β, (if inPL (rhoN N) (LN N) v' then 1 else 0) *
          ((if Id4a2_Nv kc N v β ∧ β v + β (-v) = j then Id4a2_W V w kc N β else 0) *
            (A * 2)) := by
        congr 1
        funext v'
        congr 1
        funext β
        simp only [F, ENNReal.tsum_mul_left, ENNReal.tsum_add, tsum_ite_eq, one_add_one_eq_two]
    _ = Id4a2_PL N * Id4a2_S V w kc N v j * (A * 2) := by
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, Id4a2_PL, Id4a2_S]
        ring

/-- `Σ_α |Ψ(α)|² = 1`. -/
private lemma Id4a2_W_tsum (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∑' α, Id4a2_W V w kc N α = 1 := by
  have hΨ := Normalization_isNState V w kc hN
  unfold Id4a2_W
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hΨ.1.summable, hΨ.1.tsum_eq,
    ENNReal.ofReal_one]

/-- `S_j ≤ (#P_L · 2A)^j`: (7.42) for every `j`. -/
private lemma Id4a2_S_le (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {v : Idx}
    (hv : inPH (rhoN N) (LN N) v) (j : ℕ) :
    Id4a2_S V w kc N v j ≤ (Id4a2_PL N * (ENNReal.ofReal (Id4a2_A V w N v) * 2)) ^ j := by
  induction j with
  | zero =>
    rw [pow_zero, ← Id4a2_W_tsum V w kc hN]
    refine ENNReal.tsum_le_tsum fun α => ?_
    split_ifs
    · exact le_rfl
    · exact zero_le
  | succ j ih =>
    calc Id4a2_S V w kc N v (j + 1)
        ≤ Id4a2_PL N * Id4a2_S V w kc N v j * (ENNReal.ofReal (Id4a2_A V w N v) * 2) :=
          Id4a2_S_succ V w kc hN hv j
      _ ≤ Id4a2_PL N * (Id4a2_PL N * (ENNReal.ofReal (Id4a2_A V w N v) * 2)) ^ j *
          (ENNReal.ofReal (Id4a2_A V w N v) * 2) := by gcongr
      _ = _ := by ring

/-- `mn ≤ 2^{m+n}` for `m + n ≥ 2`, and `mn = 0` otherwise. -/
private lemma Id4a2_mul_le (m n : ℕ) :
    (m : ℝ) * n ≤ if 2 ≤ m + n then (2 : ℝ) ^ (m + n) else 0 := by
  split_ifs with h
  · have h1 : (m : ℝ) ≤ 2 ^ m := by exact_mod_cast Nat.lt_two_pow_self.le
    have h2 : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self.le
    rw [pow_add]
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  · have : m = 0 ∨ n = 0 := by omega
    rcases this with rfl | rfl <;> simp

/-- `[j ≥ 2] 2^j b^j ≤ 16 b² 2^{−j}` for `0 ≤ b ≤ 1/4`. -/
private lemma Id4a2_geom {b : ℝ} (hb0 : 0 ≤ b) (hb : b ≤ 1 / 4) (j : ℕ) :
    (if 2 ≤ j then (2 : ℝ) ^ j else 0) * b ^ j ≤ 16 * b ^ 2 * (1 / 2) ^ j := by
  split_ifs with h
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    calc (2 : ℝ) ^ (k + 2) * b ^ (k + 2) = 4 * b ^ 2 * (2 * b) ^ k := by ring
      _ ≤ 4 * b ^ 2 * (1 / 2) ^ k := by
          gcongr
          linarith
      _ = 16 * b ^ 2 * (1 / 2) ^ (k + 2) := by ring
  · rw [zero_mul]
    positivity

/-- The bound of the weight `b = #P_L · 2A` of one soft step in powers of `ε_H = ρ^{1/200}`. -/
private lemma Id4a2_b_le {K g l ρ t L m s : ℝ} (hK : 0 ≤ K) (hg : 0 ≤ g) (hl : 0 ≤ l)
    (ht : 0 < t) (ht1 : t ≤ 1) (hL : 0 < L) (hρ : ρ = t ^ 200) (hm : m = t⁻¹)
    (hs : s = t ^ 100) :
    K * (t⁻¹ * s) ^ 3 * L ^ 3 * (4 * ρ * ((m + 1) / L ^ 3) * (l * (g / t ^ 2))) * 2 ≤
      16 * K * g * l * t ^ 494 := by
  rw [hρ, hm, hs]
  have e1 : t⁻¹ * t ^ 100 = t ^ 99 := by
    rw [pow_succ' t 99, ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
  have e2 : t ^ 200 * (t⁻¹ + 1) = t ^ 199 + t ^ 200 := by
    rw [mul_add, pow_succ t 199, mul_assoc, mul_inv_cancel₀ ht.ne', mul_one, mul_one]
  have e3 : t ^ 297 * (t ^ 199 + t ^ 200) / t ^ 2 = t ^ 494 + t ^ 495 := by
    rw [div_eq_iff (by positivity)]
    ring
  have e : K * (t⁻¹ * t ^ 100) ^ 3 * L ^ 3 *
      (4 * t ^ 200 * ((t⁻¹ + 1) / L ^ 3) * (l * (g / t ^ 2))) * 2 =
        8 * K * g * l * (t ^ 494 + t ^ 495) := by
    rw [e1]
    calc _ = 8 * K * g * l * (t ^ 297 * (t ^ 200 * (t⁻¹ + 1)) / t ^ 2) * (L ^ 3 / L ^ 3) := by
          ring
      _ = _ := by rw [e2, e3, div_self (by positivity), mul_one]
  rw [e]
  have h1 : t ^ 495 ≤ t ^ 494 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
  have h3 : K * g * l * t ^ 495 ≤ K * g * l * t ^ 494 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  linarith

/-- The bound behind (7.39) [temp8.44]–(7.43), in `[0, ∞]`. -/
private lemma Id4a2_Nv_ennreal (V w : R3 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ kc : ℝ, ∀ v : Idx,
      inPH (rhoN N) (LN N) v →
      (∑' α : Occ, ENNReal.ofReal (if InM (rhoN N) (LN N) kc N α ∧
          (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair v γ ≠ α) then
        (α v : ℝ) * (α (-v) : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0)) ≤
        ENNReal.ofReal (C * rhoN N ^ (5 - 12/200 : ℝ) * lam V w (rhoN N) (LN N) v ^ 2) := by
  obtain ⟨K, hK, hKb⟩ := sum_norm_rpow_le (s := 0) (by norm_num)
  set g₁ := ∫ x, |gfun V w x| with hg₁
  have hg : 0 ≤ g₁ := integral_nonneg fun x => abs_nonneg _
  have ev1 := Id4a2_ev_rpow (a := 41 / 75) (c := 1 / (2 * π)) (by norm_num) (by positivity)
  have ev2 := Id4a2_ev_rpow (a := 492 / 200) (c := 1 / (64 * K * g₁ ^ 2 + 1)) (by norm_num)
    (by positivity)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (ev1.and ev2)
  refine ⟨8192 * K ^ 2 * g₁ ^ 2, by positivity, max N₀ 1, le_max_right _ _,
    fun N hN kc v hv => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨h1, h2⟩ := hN₀ N (le_trans (le_max_left _ _) hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Id4a2_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set t := epsP ρ with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos hρ _
  have ht1 : t ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hρt : ρ = t ^ 200 := by
    rw [htdef, Id4a2_eps_pow hρ]
    norm_num
  have hst : ρ ^ (1 / 2 : ℝ) = t ^ 100 := by
    rw [htdef, Id4a2_eps_pow hρ]
    norm_num
  have hmt : mc ρ = t⁻¹ := by rw [mc, htdef, epsP, Real.rpow_neg hρ.le]
  set R := t⁻¹ * ρ ^ (1 / 2 : ℝ) with hR
  have hR0 : 0 < R := by positivity
  have hLR : 2 * π ≤ L * R := by
    have e : L * R = (ρ ^ (41 / 75 : ℝ))⁻¹ := by
      rw [hR, hLdef, LN, htdef, epsP, ← Real.rpow_neg hρ.le, ← Real.rpow_neg hρ.le,
        ← Real.rpow_add hρ, ← Real.rpow_add hρ]
      norm_num
    rw [e]
    have := inv_anti₀ (by positivity) h1
    rwa [one_div, inv_inv] at this
  -- `#P_L ≤ K R³ |Λ|`
  have hPL : Id4a2_PL N ≤ ENNReal.ofReal (K * R ^ 3 * L ^ 3) := by
    set f : Idx → ℝ := fun n => if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-(0 : ℝ)) else 0
      with hf
    have hfs : Summable f := Id4a2_summable_ball hL f (fun n hn => by
      by_contra hc
      apply hn
      simp only [hf]
      rw [ite_eq_right (fun h => hc h.2)])
    have hf0 : ∀ n, 0 ≤ f n := fun n => by
      simp only [hf]
      split_ifs <;> positivity
    have hb := hKb L R hR0 hLR
    have hb' : ∑' n, f n ≤ K * R ^ 3 * L ^ 3 := by
      rw [show (3 : ℝ) - 0 = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        inv_mul_le_iff₀ (by positivity)] at hb
      linarith
    calc Id4a2_PL N ≤ ∑' n, ENNReal.ofReal (f n) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          split_ifs with hn
          · have h0 : n ≠ 0 := Regions_PL_ne_zero hρ hn
            have hle : ‖mom L n‖ ≤ R := hn.2
            simp only [hf, ite_eq_left (show n ≠ 0 ∧ ‖mom L n‖ ≤ R from ⟨h0, hle⟩), neg_zero,
              Real.rpow_zero, ENNReal.ofReal_one]
            exact le_rfl
          · exact zero_le
      _ = ENNReal.ofReal (∑' n, f n) := (ENNReal.ofReal_tsum_of_nonneg hf0 hfs).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb'
  -- the weight `b` of one soft step
  set A := Id4a2_A V w N v with hAdef
  have hA0 : 0 ≤ A := Id4a2_A_nonneg V w hN1 v
  set l := lam V w ρ L v with hl
  set b := K * R ^ 3 * L ^ 3 * A * 2 with hb
  have hb0 : 0 ≤ b := mul_nonneg (mul_nonneg (by positivity) hA0) (by norm_num)
  have hB : Id4a2_PL N * (ENNReal.ofReal A * 2) ≤ ENNReal.ofReal b := by
    calc _ ≤ ENNReal.ofReal (K * R ^ 3 * L ^ 3) * (ENNReal.ofReal A * 2) := by gcongr
      _ = ENNReal.ofReal b := by
        rw [hb, ENNReal.ofReal_mul (p := K * R ^ 3 * L ^ 3 * A) (mul_nonneg (by positivity) hA0),
          ENNReal.ofReal_mul (p := K * R ^ 3 * L ^ 3) (by positivity), ENNReal.ofReal_ofNat]
        ring
  have hlam : |l| ≤ g₁ / t ^ 2 := Id4a2_lam_PH_le V w hρ hv
  have hble : b ≤ 16 * K * g₁ * |l| * t ^ 494 :=
    Id4a2_b_le hK hg (abs_nonneg _) ht ht1 hL hρt hmt hst
  have hb4 : b ≤ 1 / 4 := by
    have e1 : 16 * K * g₁ * |l| * t ^ 494 ≤ 16 * K * g₁ * (g₁ / t ^ 2) * t ^ 494 := by gcongr
    have e2 : 16 * K * g₁ * (g₁ / t ^ 2) * t ^ 494 = 16 * K * g₁ ^ 2 * t ^ 492 := by
      rw [show t ^ 494 = t ^ 2 * t ^ 492 by ring]
      field_simp
    have e3 : t ^ 492 = ρ ^ (492 / 200 : ℝ) := by
      rw [htdef, Id4a2_eps_pow hρ]
      norm_num
    have e4 : 16 * K * g₁ ^ 2 * t ^ 492 ≤ 1 / 4 := by
      rw [e3]
      calc 16 * K * g₁ ^ 2 * ρ ^ (492 / 200 : ℝ) ≤
            16 * K * g₁ ^ 2 * (1 / (64 * K * g₁ ^ 2 + 1)) := by gcongr
        _ ≤ 1 / 4 := by
          rw [mul_one_div, div_le_iff₀ (by positivity)]
          linarith
    linarith
  have hS : ∀ j, Id4a2_S V w kc N v j ≤ ENNReal.ofReal b ^ j := fun j =>
    (Id4a2_S_le V w kc hN1 hv j).trans (by gcongr)
  -- the weighted sum
  set c : ℕ → ℝ := fun j => if 2 ≤ j then (2 : ℝ) ^ j else 0 with hc
  have hc0 : ∀ j, 0 ≤ c j := fun j => by
    simp only [hc]
    split_ifs <;> positivity
  calc (∑' α : Occ, ENNReal.ofReal (if InM ρ L kc N α ∧
          (∀ γ : Occ, InM ρ L kc N γ → strictPair v γ ≠ α) then
        (α v : ℝ) * (α (-v) : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0))
      ≤ ∑' α, ∑' j, (if Id4a2_Nv kc N v α ∧ α v + α (-v) = j then
          ENNReal.ofReal (c j) * Id4a2_W V w kc N α else 0) := by
        refine ENNReal.tsum_le_tsum fun α => ?_
        split_ifs with hα
        · refine le_trans ?_ (ENNReal.le_tsum (α v + α (-v)))
          rw [ite_eq_left (show Id4a2_Nv kc N v α ∧ α v + α (-v) = α v + α (-v) from ⟨hα, rfl⟩),
            Id4a2_W, ← ENNReal.ofReal_mul (hc0 _)]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (Id4a2_mul_le _ _) (by positivity))
        · simp
    _ = ∑' j, ENNReal.ofReal (c j) * Id4a2_S V w kc N v j := by
        rw [ENNReal.tsum_comm]
        congr 1
        funext j
        rw [Id4a2_S, ← ENNReal.tsum_mul_left]
        congr 1
        funext α
        split_ifs <;> simp
    _ ≤ ∑' j, ENNReal.ofReal (16 * b ^ 2 * (1 / 2) ^ j) := by
        refine ENNReal.tsum_le_tsum fun j => ?_
        calc ENNReal.ofReal (c j) * Id4a2_S V w kc N v j
            ≤ ENNReal.ofReal (c j) * ENNReal.ofReal b ^ j := by gcongr; exact hS j
          _ = ENNReal.ofReal (c j * b ^ j) := by
            rw [ENNReal.ofReal_mul (hc0 j), ENNReal.ofReal_pow hb0]
          _ ≤ _ := ENNReal.ofReal_le_ofReal (Id4a2_geom hb0 hb4 j)
    _ = ENNReal.ofReal (32 * b ^ 2) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
          (summable_geometric_two.mul_left _), tsum_mul_left, tsum_geometric_two]
        ring_nf
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e988 : ρ ^ (5 - 12 / 200 : ℝ) = t ^ 988 := by
          rw [htdef, Id4a2_eps_pow hρ]
          norm_num
        rw [e988]
        have hsq := pow_le_pow_left₀ hb0 hble 2
        have e : (16 * K * g₁ * |l| * t ^ 494) ^ 2 = 256 * K ^ 2 * g₁ ^ 2 * l ^ 2 * t ^ 988 := by
          rw [show l ^ 2 = |l| ^ 2 from (sq_abs l).symm]
          ring
        rw [e] at hsq
        linarith

/-! ### (7.27) [resultid4a2o] for `u, v ∈ P_H` -/

/-- A nonzero coefficient `c(α)` of `a†_u a†_{−u} a_v a_{−v}` on `|α⟩`: `α = β' + δ_v + δ_{−v}`,
`T(α) = β' + δ_{−u} + δ_u`, and `c(α) = √(α(v)α(−v)) √(T(α)(u) T(α)(−u))`. -/
private lemma Id4a2_c_facts {u v : Idx} (hu : u ≠ 0) (hv : v ≠ 0) {α : Occ}
    (hc : (a4 u (-u) v (-v) α).1 ≠ 0) :
    ∃ β' : Occ, α = β' + Finsupp.single v 1 + Finsupp.single (-v) 1 ∧
      (a4 u (-u) v (-v) α).2 = β' + Finsupp.single (-u) 1 + Finsupp.single u 1 ∧
      (a4 u (-u) v (-v) α).1 = Real.sqrt ((α v : ℝ) * α (-v)) *
        Real.sqrt (((a4 u (-u) v (-v) α).2 u : ℝ) * (a4 u (-u) v (-v) α).2 (-u)) := by
  obtain ⟨β', rfl⟩ := a4_exists_add u (-u) v (-v) α hc
  have hu' : -u ≠ u := Id4a2_neg_ne_self hu
  have hv' : -v ≠ v := Id4a2_neg_ne_self hv
  refine ⟨β', rfl, by rw [a4_of_add], ?_⟩
  rw [a4_of_add]
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply, hu', hv', hu'.symm, hv'.symm,
    ↓reduceIte, Nat.cast_add, Nat.cast_one, add_zero]
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  ring

/-- (7.36) [temp8.41] with `β = T(α) ∈ N_u`: if `α ∈ N_v`, `c(α) ≠ 0` and `T(α) ∈ M`, then
`T(α)` is not `𝓐^u γ` for any `γ ∈ M`. -/
private lemma Id4a2_T_Nu {kc : ℝ} {N : ℕ} {u v : Idx} (hu : u ≠ 0) (hv : v ≠ 0) {α : Occ}
    (hα : Id4a2_Nv kc N v α) (hc : (a4 u (-u) v (-v) α).1 ≠ 0)
    (hT : InM (rhoN N) (LN N) kc N (a4 u (-u) v (-v) α).2) :
    Id4a2_Nv kc N u (a4 u (-u) v (-v) α).2 := by
  obtain ⟨β', hα', hT', -⟩ := Id4a2_c_facts hu hv hc
  refine ⟨hT, fun γ hγ he => hα.2 γ hγ ?_⟩
  rw [hT'] at he
  have e : γ - Finsupp.single 0 2 = β' := by
    have h : (γ - Finsupp.single 0 2) + Finsupp.single u 1 + Finsupp.single (-u) 1 =
        β' + Finsupp.single u 1 + Finsupp.single (-u) 1 := by
      rw [add_right_comm β']
      exact he
    exact add_right_cancel (add_right_cancel h)
  rw [hα']
  change (γ - Finsupp.single 0 2) + Finsupp.single v 1 + Finsupp.single (-v) 1 = _
  rw [e]

/-- (7.27) [resultid4a2o] at fixed `N`: bounds `Dλ_u²`, `Dλ_v²` for the weighted sums over
`N_u` and `N_v` give `|⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ − P(u, v)| ≤ D|λ_u λ_v|`. -/
private lemma Id4a2_PH_fixed (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u v : Idx}
    (hu : u ≠ 0) (hv : v ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (Hu : (∑' α : Occ, ENNReal.ofReal (if InM (rhoN N) (LN N) kc N α ∧
          (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair u γ ≠ α) then
        (α u : ℝ) * (α (-u) : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0)) ≤
        ENNReal.ofReal (D * lam V w (rhoN N) (LN N) u ^ 2))
    (Hv : (∑' α : Occ, ENNReal.ofReal (if InM (rhoN N) (LN N) kc N α ∧
          (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair v γ ≠ α) then
        (α v : ℝ) * (α (-v) : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0)) ≤
        ENNReal.ofReal (D * lam V w (rhoN N) (LN N) v ^ 2)) :
    ‖Expect.E4 (trialState V w kc N) u (-u) v (-v) - Puv V w kc N u v‖ ≤
      D * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| := by
  set lu := lam V w (rhoN N) (LN N) u with hlu
  set lv := lam V w (rhoN N) (LN N) v with hlv
  set t := Id4a2_term V w kc N u v with htdef
  have hΨ := Normalization_isNState V w kc hN
  have hsum : Summable fun α => ‖t α‖ := Expect.id4a_summable N _ hΨ u (-u) v (-v)
  set g1 : Occ → ℂ := fun α => if Id4a2_Nv kc N v α then 0 else t α with hg1
  set g2 : Occ → ℂ := fun α => if Id4a2_Nv kc N v α then t α else 0 with hg2
  have hb1 : ∀ α, ‖g1 α‖ ≤ ‖t α‖ := fun α => by
    simp only [hg1]
    split_ifs <;> simp
  have hb2 : ∀ α, ‖g2 α‖ ≤ ‖t α‖ := fun α => by
    simp only [hg2]
    split_ifs <;> simp
  have hs1 : Summable g1 := Summable.of_norm_bounded hsum hb1
  have hs2 : Summable g2 := Summable.of_norm_bounded hsum hb2
  have hs2n : Summable fun α => ‖g2 α‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb2 hsum
  have hE : Expect.E4 (trialState V w kc N) u (-u) v (-v) = (∑' α, g1 α) + ∑' α, g2 α := by
    rw [← hs1.tsum_add hs2]
    change ∑' α, t α = _
    congr 1
    funext α
    simp only [hg1, hg2]
    split_ifs <;> simp
  have hP : ∑' α, g1 α = Puv V w kc N u v := by
    refine Id4a2_reindex V w kc hN hu hv g1 (fun γ hγ => ?_) (fun α hα => ?_)
    · simp only [hg1]
      rw [ite_eq_right (fun h => h.2 γ hγ rfl)]
    · simp only [hg1] at hα
      split_ifs at hα with h
      · exact absurd rfl hα
      · have hΨα : trialState V w kc N α ≠ 0 := by
          intro h0
          apply hα
          simp [htdef, Id4a2_term, h0]
        have hαM := Id4a2_inM_of_ne hΨα
        refine ⟨hαM, ?_⟩
        by_contra hne
        push Not at hne
        exact h ⟨hαM, hne⟩
  rw [hE, hP, add_sub_cancel_left]
  refine (norm_tsum_le_tsum_norm hs2n).trans ?_
  have hreal : ∑' α, ‖g2 α‖ = (∑' α, ENNReal.ofReal ‖g2 α‖).toReal := by
    rw [ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    congr 1
    funext α
    rw [ENNReal.toReal_ofReal (norm_nonneg _)]
  rw [hreal]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_).trans
    (ENNReal.toReal_ofReal (by positivity)).le
  -- the summands of `Hu`, `Hv`
  set Gu : Occ → ENNReal := fun β => ENNReal.ofReal (if InM (rhoN N) (LN N) kc N β ∧
      (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair u γ ≠ β) then
        (β u : ℝ) * (β (-u) : ℝ) * ‖trialState V w kc N β‖ ^ 2 else 0) with hGu
  set Gv : Occ → ENNReal := fun α => ENNReal.ofReal (if InM (rhoN N) (LN N) kc N α ∧
      (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair v γ ≠ α) then
        (α v : ℝ) * (α (-v) : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) with hGv
  set S : Set Occ := {α | (a4 u (-u) v (-v) α).1 ≠ 0} with hS
  set H : Occ → ENNReal := S.indicator fun α => Gu (a4 u (-u) v (-v) α).2 with hH
  -- the facts at a nonzero summand
  have facts : ∀ α, g2 α ≠ 0 →
      Id4a2_Nv kc N v α ∧ (a4 u (-u) v (-v) α).1 ≠ 0 ∧ trialState V w kc N α ≠ 0 ∧
        trialState V w kc N (a4 u (-u) v (-v) α).2 ≠ 0 ∧
        Id4a2_Nv kc N u (a4 u (-u) v (-v) α).2 ∧ g2 α = t α := by
    intro α hα
    simp only [hg2] at hα ⊢
    split_ifs at hα ⊢ with h
    · have hc : (a4 u (-u) v (-v) α).1 ≠ 0 := by
        intro h0
        apply hα
        simp [htdef, Id4a2_term, h0]
      have hΨα : trialState V w kc N α ≠ 0 := by
        intro h0
        apply hα
        simp [htdef, Id4a2_term, h0]
      have hΨT : trialState V w kc N (a4 u (-u) v (-v) α).2 ≠ 0 := by
        intro h0
        apply hα
        simp [htdef, Id4a2_term, h0]
      exact ⟨h, hc, hΨα, hΨT, Id4a2_T_Nu hu hv h hc (Id4a2_inM_of_ne hΨT), rfl⟩
    · exact absurd rfl hα
  have hpt : ∀ α, ENNReal.ofReal |lu * lv| * ENNReal.ofReal ‖g2 α‖ ≤
      ENNReal.ofReal (lu ^ 2 / 2) * Gv α + ENNReal.ofReal (lv ^ 2 / 2) * H α := by
    intro α
    by_cases hg : g2 α = 0
    · simp [hg]
    obtain ⟨hNv, hc, hΨα, hΨT, hNu, he⟩ := facts α hg
    obtain ⟨-, -, -, hceq⟩ := Id4a2_c_facts hu hv hc
    set T := (a4 u (-u) v (-v) α).2 with hT
    set X : ℝ := (α v : ℝ) * α (-v) with hX
    set Y : ℝ := (T u : ℝ) * T (-u) with hY
    have hX0 : 0 ≤ X := by positivity
    have hY0 : 0 ≤ Y := by positivity
    have hNv' : InM (rhoN N) (LN N) kc N α ∧
        (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair v γ ≠ α) := hNv
    have hNu' : InM (rhoN N) (LN N) kc N T ∧
        (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair u γ ≠ T) := hNu
    have hGvα : Gv α = ENNReal.ofReal (X * ‖trialState V w kc N α‖ ^ 2) := by
      rw [hGv]
      dsimp only
      rw [ite_eq_left hNv']
    have hHα : H α = ENNReal.ofReal (Y * ‖trialState V w kc N T‖ ^ 2) := by
      rw [hH, Set.indicator_of_mem (show α ∈ S from hc), hGu]
      dsimp only
      rw [ite_eq_left hNu']
    have hnorm : ‖g2 α‖ = ‖trialState V w kc N T‖ * (Real.sqrt X * Real.sqrt Y) *
        ‖trialState V w kc N α‖ := by
      rw [he, htdef, Id4a2_term, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (a4_fst_nonneg _ _ _ _ _), hceq]
    have key : |lu * lv| * ‖g2 α‖ ≤ lu ^ 2 / 2 * (X * ‖trialState V w kc N α‖ ^ 2) +
        lv ^ 2 / 2 * (Y * ‖trialState V w kc N T‖ ^ 2) := by
      set a := |lu| * Real.sqrt X * ‖trialState V w kc N α‖ with ha
      set b := |lv| * Real.sqrt Y * ‖trialState V w kc N T‖ with hb
      have hab := two_mul_le_add_sq a b
      have ha2 : a ^ 2 = lu ^ 2 * (X * ‖trialState V w kc N α‖ ^ 2) := by
        rw [ha, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hX0]
        ring
      have hb2 : b ^ 2 = lv ^ 2 * (Y * ‖trialState V w kc N T‖ ^ 2) := by
        rw [hb, mul_pow, mul_pow, sq_abs, Real.sq_sqrt hY0]
        ring
      have hl : |lu * lv| * ‖g2 α‖ = a * b := by
        rw [hnorm, abs_mul, ha, hb]
        ring
      rw [hl]
      linarith
    rw [hGvα, hHα, ← ENNReal.ofReal_mul (abs_nonneg _), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal key
  have hinj : Function.Injective fun x : S => (a4 u (-u) v (-v) x.1).2 :=
    fun x y h => Subtype.ext (a4_injOn u (-u) v (-v) x.2 y.2 h)
  have hsumH : ∑' α, H α ≤ ENNReal.ofReal (D * lu ^ 2) := by
    calc ∑' α, H α = ∑' x : S, Gu (a4 u (-u) v (-v) x.1).2 := (tsum_subtype S _).symm
      _ ≤ ∑' β, Gu β := ENNReal.tsum_comp_le_tsum_of_injective hinj Gu
      _ ≤ _ := Hu
  have hmain : ENNReal.ofReal |lu * lv| * ∑' α, ENNReal.ofReal ‖g2 α‖ ≤
      ENNReal.ofReal (D * lu ^ 2 * lv ^ 2) := by
    calc ENNReal.ofReal |lu * lv| * ∑' α, ENNReal.ofReal ‖g2 α‖
        = ∑' α, ENNReal.ofReal |lu * lv| * ENNReal.ofReal ‖g2 α‖ := ENNReal.tsum_mul_left.symm
      _ ≤ ∑' α, (ENNReal.ofReal (lu ^ 2 / 2) * Gv α + ENNReal.ofReal (lv ^ 2 / 2) * H α) :=
          ENNReal.tsum_le_tsum hpt
      _ = ENNReal.ofReal (lu ^ 2 / 2) * (∑' α, Gv α) +
            ENNReal.ofReal (lv ^ 2 / 2) * ∑' α, H α := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal (lu ^ 2 / 2) * ENNReal.ofReal (D * lv ^ 2) +
          ENNReal.ofReal (lv ^ 2 / 2) * ENNReal.ofReal (D * lu ^ 2) :=
          add_le_add (mul_le_mul_of_nonneg_left Hv zero_le)
            (mul_le_mul_of_nonneg_left hsumH zero_le)
      _ = ENNReal.ofReal (D * lu ^ 2 * lv ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  by_cases h0 : lu * lv = 0
  · have hz : ∑' α, ENNReal.ofReal ‖g2 α‖ = 0 := by
      refine ENNReal.tsum_eq_zero.2 fun α => ?_
      by_contra hne
      have hg : g2 α ≠ 0 := by
        intro h
        apply hne
        simp [h]
      obtain ⟨hNv, hc, hΨα, hΨT, hNu, -⟩ := facts α hg
      obtain ⟨-, -, -, hceq⟩ := Id4a2_c_facts hu hv hc
      have hXY : 0 < Real.sqrt ((α v : ℝ) * α (-v)) * Real.sqrt
          (((a4 u (-u) v (-v) α).2 u : ℝ) * (a4 u (-u) v (-v) α).2 (-u)) := by
        rw [← hceq]
        exact lt_of_le_of_ne (a4_fst_nonneg _ _ _ _ _) (Ne.symm hc)
      have hX : 0 < (α v : ℝ) * α (-v) := by
        by_contra hX
        rw [Real.sqrt_eq_zero'.2 (not_lt.1 hX), zero_mul] at hXY
        exact lt_irrefl _ hXY
      have hY : 0 < ((a4 u (-u) v (-v) α).2 u : ℝ) * (a4 u (-u) v (-v) α).2 (-u) := by
        by_contra hY
        rw [Real.sqrt_eq_zero'.2 (not_lt.1 hY), mul_zero] at hXY
        exact lt_irrefl _ hXY
      rcases mul_eq_zero.1 h0 with h | h
      · have h1 : Gu (a4 u (-u) v (-v) α).2 ≤ ENNReal.ofReal (D * lu ^ 2) :=
          (ENNReal.le_tsum _).trans Hu
        have hNu' : InM (rhoN N) (LN N) kc N (a4 u (-u) v (-v) α).2 ∧
            (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ →
              strictPair u γ ≠ (a4 u (-u) v (-v) α).2) := hNu
        simp only [hGu, ite_eq_left hNu', h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, mul_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero,
          ENNReal.ofReal_eq_zero] at h1
        have : 0 < ((a4 u (-u) v (-v) α).2 u : ℝ) * (a4 u (-u) v (-v) α).2 (-u) *
            ‖trialState V w kc N (a4 u (-u) v (-v) α).2‖ ^ 2 := by
          have := norm_pos_iff.2 hΨT
          positivity
        linarith
      · have h1 : Gv α ≤ ENNReal.ofReal (D * lv ^ 2) := (ENNReal.le_tsum _).trans Hv
        have hNv' : InM (rhoN N) (LN N) kc N α ∧
            (∀ γ : Occ, InM (rhoN N) (LN N) kc N γ → strictPair v γ ≠ α) := hNv
        simp only [hGv, ite_eq_left hNv', h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, mul_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero,
          ENNReal.ofReal_eq_zero] at h1
        have : 0 < (α v : ℝ) * α (-v) * ‖trialState V w kc N α‖ ^ 2 := by
          have := norm_pos_iff.2 hΨα
          positivity
        linarith
    rw [hz]
    exact zero_le
  · have hpos : 0 < |lu * lv| := abs_pos.2 h0
    have e : ENNReal.ofReal (D * lu ^ 2 * lv ^ 2) =
        ENNReal.ofReal |lu * lv| * ENNReal.ofReal (D * |lu * lv|) := by
      rw [← ENNReal.ofReal_mul (abs_nonneg _)]
      congr 1
      calc D * lu ^ 2 * lv ^ 2 = D * (lu * lv) ^ 2 := by ring
        _ = D * |lu * lv| ^ 2 := by rw [sq_abs]
        _ = _ := by ring
    rw [e] at hmain
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.2 hpos).ne' ENNReal.ofReal_ne_top).1
      hmain

/-- Lemma 7.3 [id4a2], (7.27) [resultid4a2o], for `u, v ∈ P_H` with `u ≠ ±v`:
`|⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ − P(u, v)| ≤ ρ⁴|λ_u λ_v|` for `ρ` small. -/
theorem Lemma7_3_PH (V w : R3 → ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u v : Idx,
      inPH (rhoN N) (LN N) u → inPH (rhoN N) (LN N) v → u ≠ v → u + v ≠ 0 →
      ‖Expect.E4 (trialState V w kc N) u (-u) v (-v) - Puv V w kc N u v‖ ≤
        rhoN N ^ 4 * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| := by
  obtain ⟨C, hC, N₁, hN₁, hNv⟩ := Id4a2_Nv_ennreal V w
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (Id4a2_ev_rpow (a := 188 / 200) (c := 1 / (C + 1)) (by norm_num) (by positivity))
  refine ⟨max N₁ N₂, fun N hN kc u v hu hv _ _ => ?_⟩
  have hN1 : 1 ≤ N := le_trans hN₁ (le_trans (le_max_left _ _) hN)
  obtain ⟨-, hρ, -, -⟩ := Id4a2_rhoN_LN hN1
  have hD : 0 ≤ C * rhoN N ^ (5 - 12/200 : ℝ) := mul_nonneg hC (Real.rpow_nonneg hρ.le _)
  have key := Id4a2_PH_fixed V w kc hN1 (Regions_PH_ne_zero hρ hu) (Regions_PH_ne_zero hρ hv) hD
    (hNv N (le_trans (le_max_left _ _) hN) kc u hu) (hNv N (le_trans (le_max_left _ _) hN) kc v hv)
  refine key.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have h2 := hN₂ N (le_trans (le_max_right _ _) hN)
  rw [show (5 - 12 / 200 : ℝ) = 188 / 200 + (4 : ℕ) by norm_num, Real.rpow_add hρ,
    Real.rpow_natCast]
  have h3 : C * rhoN N ^ (188 / 200 : ℝ) ≤ 1 := by
    calc C * rhoN N ^ (188 / 200 : ℝ) ≤ C * (1 / (C + 1)) := by gcongr
      _ ≤ 1 := by
        rw [mul_one_div, div_le_one (by positivity)]
        linarith
  have h4 : 0 ≤ rhoN N ^ 4 := by positivity
  nlinarith

end LHYUpper
