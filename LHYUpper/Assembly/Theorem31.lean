import LHYUpper.Assembly.Section4
import LHYUpper.Fock.Decomp
import LHYUpper.Fock.Variational

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate RealInnerProductSpace

noncomputable section
open Classical

namespace LHYUpper

/-! # From Lemmas 4.1–4.6 to Theorem 2.2

Assembles Theorem 3.1 [lemma2.1] from Lemmas 4.1–4.6 together with the identities at the end of §4
and the normalization of the trial state (3.18) [deffal] (`theorem3_1_of_lemmas`). It then derives
Theorem 2.2 [lemma2] from Theorem 3.1 with a diagonal choice of the cutoff `k_c(N)`, and combines
Theorem 2.2 with the variational principle to bound the upper limit of the ratio of Theorem 2.1
[mainthm] for `e₀^P`, which is the hypothesis of Lemma 2.2 [lemma1]. -/

namespace Theorem31

private theorem rpow52_eq_zero_of_nonpos {g : ℝ} (hg : g ≤ 0) : g ^ (5/2 : ℝ) = 0 := by
  rcases hg.eq_or_lt with h | h
  · rw [h]; exact Real.zero_rpow (by norm_num)
  · rw [Real.rpow_def_of_neg h]
    have : (5/2 : ℝ) * π = π / 2 + 2 * π := by ring
    rw [this, Real.cos_add_two_pi, Real.cos_pi_div_two, mul_zero]

private theorem rpow52_nonneg (g : ℝ) : 0 ≤ g ^ (5/2 : ℝ) := by
  by_cases h : 0 ≤ g
  · exact Real.rpow_nonneg h _
  · rw [rpow52_eq_zero_of_nonpos (by linarith [not_le.mp h])]

private theorem rhoN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < rhoN N :=
  Real.rpow_pos_of_pos (by exact_mod_cast hN) _

private theorem rhoN_nonneg (N : ℕ) : 0 ≤ rhoN N :=
  Real.rpow_nonneg (Nat.cast_nonneg N) _

private theorem LN_pos {N : ℕ} (hN : 1 ≤ N) : 0 < LN N :=
  Real.rpow_pos_of_pos (rhoN_pos hN) _

private theorem rhoN_mul_LN_cube {N : ℕ} (hN : 1 ≤ N) : rhoN N * LN N ^ 3 = N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hρ : 0 < rhoN N := rhoN_pos hN
  unfold LN
  rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
  conv_lhs => arg 1; rw [← Real.rpow_one (rhoN N)]
  rw [← Real.rpow_add hρ, rhoN, ← Real.rpow_mul hN0.le]
  norm_num

/-- The `ρ₀` correction of (3.14) [defrho0]:
`g (ρ₀² - ρ²) ρ^{-5/2} = -(2/(3π²)) g^{5/2} + g⁴ ρ^{1/2} / (9π⁴)`. -/
private theorem corr_identity (g ρ : ℝ) (hg : 0 < g) (hρ : 0 < ρ) :
    g * (rho0 g ρ ^ 2 - ρ ^ 2) / ρ ^ (5/2 : ℝ) =
      -(2 / (3 * π ^ 2)) * g ^ (5/2 : ℝ) + g ^ 4 * ρ ^ (1/2 : ℝ) / (9 * π ^ 4) := by
  have e1 : ρ ^ (5/2 : ℝ) = ρ ^ (3/2 : ℝ) * ρ := by
    rw [show (5/2 : ℝ) = 3/2 + 1 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have e2 : ρ ^ (3/2 : ℝ) * ρ ^ (3/2 : ℝ) = ρ ^ (5/2 : ℝ) * ρ ^ (1/2 : ℝ) := by
    rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]; norm_num
  have e3 : g ^ (5/2 : ℝ) = g ^ (3/2 : ℝ) * g := by
    rw [show (5/2 : ℝ) = 3/2 + 1 by norm_num, Real.rpow_add hg, Real.rpow_one]
  have e4 : g ^ (3/2 : ℝ) * g ^ (3/2 : ℝ) = g ^ 3 := by
    rw [← Real.rpow_add hg]; norm_num
  have hp : 0 < ρ ^ (5/2 : ℝ) := Real.rpow_pos_of_pos hρ _
  unfold rho0
  rw [div_eq_iff hp.ne', e3]
  linear_combination (2 * g * (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ)) * e1 +
    (g * ((3 * π ^ 2)⁻¹) ^ 2 * g ^ (3/2 : ℝ) * g ^ (3/2 : ℝ)) * e2 +
    (g * ((3 * π ^ 2)⁻¹) ^ 2 * ρ ^ (5/2 : ℝ) * ρ ^ (1/2 : ℝ)) * e4

/-- The constants of (4.8)–(4.13) and the limit of the correction add up to `c* g₀^{5/2}`. -/
private theorem const_identity (V w : R3 → ℝ) (hg : 0 < g0 V w)
    (hI1 : normGradW2 w - normVw V w + normVw2 V w = 0)
    (hI2 : V0 V - normVw V w = g0 V w) :
    (4 * normGradW2 w * Section4.G V w / 3 - 8 * g0 V w ^ (5/2 : ℝ) / (5 * π ^ 2)) +
      4 * V0 V * Section4.G V w / 3 + 2 * V0 V * Section4.G V w +
      (-2 * normVw V w * Section4.G V w) + (-8 * normVw V w * Section4.G V w / 3) +
      4 * normVw2 V w * Section4.G V w / 3 + (-2 * g0 V w ^ (5/2 : ℝ) / (3 * π ^ 2)) =
    cLHY * g0 V w ^ (5/2 : ℝ) := by
  have h52 : g0 V w ^ (5/2 : ℝ) = g0 V w ^ (3/2 : ℝ) * g0 V w := by
    rw [show (5/2 : ℝ) = 3/2 + 1 by norm_num, Real.rpow_add hg, Real.rpow_one]
  have hV0 : V0 V = g0 V w + normVw V w := by linarith
  have hgr : normGradW2 w = normVw V w - normVw2 V w := by linarith
  rw [h52, hV0, hgr]
  unfold Section4.G cLHY
  have hπ : π ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- Algebra of the ratio at `N ≥ 1`: `ρ L³ = N` turns `(E/N - gρ)/(g^{5/2}ρ^{3/2})` into the sum of
the `excess` terms plus the `ρ₀` correction, divided by `g^{5/2}`. -/
private theorem ratio_alg (E g ρ L Nn c p r : ℝ) (hρ : 0 < ρ) (hN : 0 < Nn)
    (hL : ρ * L ^ 3 = Nn) (hp : 0 < p) (hc : 0 < c) :
    (E / Nn - g * ρ) * (c * p)⁻¹ =
      c⁻¹ * ((E / L ^ 3 - g * r ^ 2) / (p * ρ) + g * (r ^ 2 - ρ ^ 2) / (p * ρ)) := by
  have hL3 : L ^ 3 = Nn / ρ := by
    field_simp; linarith
  rw [hL3]
  field_simp
  ring

/-- The diagonal step: if for each `k` the property `P k N` holds for large `N`, and the iterated
upper limit of `F` is at most `c`, then there is a sequence `k(N)` along which `P` holds for large
`N` and the upper limit of `F (k N) N` is at most `c`. -/
private theorem diagonal (P : ℝ → ℕ → Prop) (F : ℝ → ℕ → EReal) (c : ℝ)
    (hP : ∀ k : ℝ, ∀ᶠ N : ℕ in atTop, P k N)
    (hF : limsup (fun k : ℝ => limsup (fun N : ℕ => F k N) atTop) atTop ≤ (c : EReal)) :
    ∃ k : ℕ → ℝ, (∀ᶠ N : ℕ in atTop, P (k N) N) ∧
      limsup (fun N : ℕ => F (k N) N) atTop ≤ (c : EReal) := by
  have step : ∀ n : ℕ, ∃ K : ℝ, ∃ T : ℕ, ∀ N ≥ T,
      P K N ∧ F K N < ((c + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
    intro n
    have hlt : (c : EReal) < ((c + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
      exact_mod_cast lt_add_of_pos_right c (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    obtain ⟨K, hK⟩ := (eventually_lt_of_limsup_lt (hF.trans_lt hlt)).exists
    have h2 := eventually_lt_of_limsup_lt hK
    obtain ⟨T, hT⟩ := eventually_atTop.1 ((hP K).and h2)
    exact ⟨K, T, hT⟩
  choose K T hKT using step
  let T' : ℕ → ℕ := fun n => (Finset.range (n + 1)).sup T
  have hTT' : ∀ n, T n ≤ T' n := fun n => Finset.le_sup (f := T) (Finset.self_mem_range_succ n)
  let m : ℕ → ℕ := fun N => Nat.findGreatest (fun n => T' n ≤ N) N
  have hm_spec : ∀ N, T' 0 ≤ N → T' (m N) ≤ N := fun N hN =>
    Nat.findGreatest_spec (P := fun n => T' n ≤ N) (Nat.zero_le N) hN
  have hm_ge : ∀ N n, n ≤ N → T' n ≤ N → n ≤ m N := fun N n h1 h2 =>
    Nat.le_findGreatest h1 h2
  refine ⟨fun N => K (m N), ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop (T' 0)] with N hN
    exact (hKT (m N) N ((hTT' (m N)).trans (hm_spec N hN))).1
  · have key : ∀ n : ℕ, limsup (fun N : ℕ => F (K (m N)) N) atTop ≤
        ((c + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
      intro n
      refine limsup_le_of_le (h := ?_)
      filter_upwards [eventually_ge_atTop (max n (T' n))] with N hN
      have hn : n ≤ m N := hm_ge N n (le_trans (le_max_left _ _) hN)
        (le_trans (le_max_right _ _) hN)
      have hT0 : T' 0 ≤ N := by
        have : T' 0 ≤ T' n := Finset.sup_mono (Finset.range_mono (by omega))
        exact this.trans (le_trans (le_max_right _ _) hN)
      have h := (hKT (m N) N ((hTT' (m N)).trans (hm_spec N hT0))).2
      refine h.le.trans ?_
      have : 1 / ((m N : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (n : ℝ) ≤ m N := by exact_mod_cast hn
        linarith
      exact_mod_cast (by linarith : c + 1 / ((m N : ℝ) + 1) ≤ c + 1 / ((n : ℝ) + 1))
    refine le_of_forall_gt_imp_ge_of_dense (fun a ha => ?_)
    induction a using EReal.rec with
    | bot => exact absurd ha (not_lt_of_ge bot_le)
    | top => exact le_top
    | coe b =>
      have hb : c < b := by exact_mod_cast ha
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hb)
      exact (key n).trans (by exact_mod_cast (by linarith : c + 1 / ((n : ℝ) + 1) ≤ b))

/-- §4: Lemmas 4.1–4.6, the identities at the end of §4 and the normalization of (3.18)
[deffal] give Theorem 3.1 [lemma2.1]. -/
theorem theorem3_1_of_lemmas (V w : R3 → ℝ)
    (h1 : Stmt.Lemma4_1 V w) (h2 : Stmt.Lemma4_2 V w) (h3 : Stmt.Lemma4_3 V w)
    (h4 : Stmt.Lemma4_4 V w) (h5 : Stmt.Lemma4_5 V w) (h6 : Stmt.Lemma4_6 V w)
    (hI1 : normGradW2 w - normVw V w + normVw2 V w = 0)
    (hI2 : V0 V - normVw V w = g0 V w)
    (hnorm : ∀ kc : ℝ, ∀ᶠ N in atTop, IsNState N (trialState V w kc N)) :
    Stmt.Theorem3_1 V w := by
  obtain ⟨E1, hE1, hb1⟩ := h1
  obtain ⟨E2, hE2, hb2⟩ := h2
  obtain ⟨E3, hE3, hb3⟩ := h3
  obtain ⟨E4, hE4, hb4⟩ := h4
  obtain ⟨E5, hE5, hb5⟩ := h5
  obtain ⟨E6, hE6, hb6⟩ := h6
  refine ⟨fun kc N => E1 kc N + E2 kc N + E3 kc N + E4 kc N + E5 kc N + E6 kc N, ?_, ?_⟩
  · intro kc
    filter_upwards [hE1 kc, hE2 kc, hE3 kc, hE4 kc, hE5 kc, hE6 kc, hnorm kc] with
      N a1 a2 a3 a4 a5 a6 hn
    refine ⟨hn, ?_⟩
    rw [Decomp.hasEnergy_iff]
    refine ⟨E1 kc N, fun j => match j with
      | .S1 => E2 kc N | .S2 => E3 kc N | .S3 => E4 kc N | .A1 => E5 kc N | .A2 => E6 kc N,
      a1, fun j => ?_, ?_⟩
    · cases j
      exacts [a2, a3, a4, a5, a6]
    · have hu : (Finset.univ : Finset Decomp.Part) =
          {.S1, .S2, .S3, .A1, .A2} := by
        ext j; cases j <;> simp
      rw [hu]
      simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, reduceCtorEq,
        or_self, not_false_eq_true, Finset.sum_singleton]
      ring
  · by_cases hg : 0 < g0 V w
    · let X : Fin 6 → ℝ → ℕ → ℝ := ![
        fun kc N => Section4.excess (g0 V w) (normGradW2 w) (E1 kc N) N,
        fun kc N => Section4.excess (g0 V w) (V0 V) (E2 kc N) N,
        fun kc N => Section4.excess (g0 V w) (-2 * normVw V w) (E3 kc N) N,
        fun kc N => Section4.excess (g0 V w) (normVw2 V w) (E4 kc N) N,
        fun kc N => Section4.excess (g0 V w) 0 (E5 kc N) N,
        fun kc N => Section4.excess (g0 V w) 0 (E6 kc N) N]
      let R : Fin 6 → ℝ := ![
        4 * normGradW2 w * Section4.G V w / 3 - 8 * g0 V w ^ (5/2 : ℝ) / (5 * π ^ 2),
        4 * V0 V * Section4.G V w / 3,
        2 * V0 V * Section4.G V w,
        -2 * normVw V w * Section4.G V w,
        -8 * normVw V w * Section4.G V w / 3,
        4 * normVw2 V w * Section4.G V w / 3]
      let Y : ℕ → ℝ := fun N => g0 V w * (rho0 (g0 V w) (rhoN N) ^ 2 - rhoN N ^ 2) /
        rhoN N ^ (5/2 : ℝ)
      let y : ℝ := -2 * g0 V w ^ (5/2 : ℝ) / (3 * π ^ 2)
      have hX : ∀ j ∈ (Finset.univ : Finset (Fin 6)), Section4.limsup2 (X j) ≤ (R j : EReal) := by
        intro j _
        fin_cases j
        exacts [hb1, hb2, hb3, hb4, hb5, hb6]
      have hρ0 : Tendsto (fun N : ℕ => rhoN N) atTop (𝓝 0) :=
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 8/17)).comp tendsto_natCast_atTop_atTop
      have hρh : Tendsto (fun N : ℕ => rhoN N ^ (1/2 : ℝ)) atTop (𝓝 0) := by
        have := hρ0.rpow_const (p := 1/2) (Or.inr (by norm_num))
        simpa using this
      have hY : Tendsto Y atTop (𝓝 y) := by
        have h1 : Tendsto (fun N : ℕ => y + g0 V w ^ 4 * rhoN N ^ (1/2 : ℝ) / (9 * π ^ 4))
            atTop (𝓝 (y + g0 V w ^ 4 * 0 / (9 * π ^ 4))) :=
          tendsto_const_nhds.add ((hρh.const_mul _).div_const _)
        rw [mul_zero, zero_div, add_zero] at h1
        refine h1.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        simp only [Y, y]
        rw [corr_identity _ _ hg (rhoN_pos hN)]
        ring
      have hmain := Section4.limsup2_sum_add_le Finset.univ X R Y y hX hY
      have hconst : ∑ j, R j + y = cLHY * g0 V w ^ (5/2 : ℝ) := by
        rw [Fin.sum_univ_six]
        exact const_identity V w hg hI1 hI2
      have hm : normGradW2 w + V0 V + -2 * normVw V w + normVw2 V w + 0 + 0 = g0 V w := by
        linarith
      have hsumX : ∀ (kc : ℝ) (N : ℕ), ∑ j, X j kc N =
          ((E1 kc N + E2 kc N + E3 kc N + E4 kc N + E5 kc N + E6 kc N) / LN N ^ 3 -
            g0 V w * rho0 (g0 V w) (rhoN N) ^ 2) / rhoN N ^ (5/2 : ℝ) := by
        intro kc N
        have e : ∑ j, X j kc N = Section4.excess (g0 V w) (normGradW2 w) (E1 kc N) N +
            Section4.excess (g0 V w) (V0 V) (E2 kc N) N +
            Section4.excess (g0 V w) (-2 * normVw V w) (E3 kc N) N +
            Section4.excess (g0 V w) (normVw2 V w) (E4 kc N) N +
            Section4.excess (g0 V w) 0 (E5 kc N) N +
            Section4.excess (g0 V w) 0 (E6 kc N) N := Fin.sum_univ_six (fun j => X j kc N)
        rw [e]
        unfold Section4.excess
        linear_combination (-(rho0 (g0 V w) (rhoN N) ^ 2 / rhoN N ^ (5/2 : ℝ))) * hm
      have hratio : ∀ (kc : ℝ) (N : ℕ), 1 ≤ N →
          ratio (g0 V w) (rhoN N)
            (((E1 kc N + E2 kc N + E3 kc N + E4 kc N + E5 kc N + E6 kc N) / N : ℝ) : EReal) =
          (((g0 V w ^ (5/2 : ℝ))⁻¹ : ℝ) : EReal) * ((∑ j, X j kc N + Y N : ℝ) : EReal) := by
        intro kc N hN
        have hρ := rhoN_pos hN
        have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
        have e1 : rhoN N ^ (5/2 : ℝ) = rhoN N ^ (3/2 : ℝ) * rhoN N := by
          rw [show (5/2 : ℝ) = 3/2 + 1 by norm_num, Real.rpow_add hρ, Real.rpow_one]
        unfold ratio
        rw [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_mul]
        congr 1
        rw [hsumX]
        simp only [Y]
        rw [e1]
        exact ratio_alg _ _ _ _ _ _ _ _ hρ hN0 (rhoN_mul_LN_cube hN)
          (Real.rpow_pos_of_pos hρ _) (Real.rpow_pos_of_pos hg _)
      have hc0 : (0 : EReal) ≤ (((g0 V w ^ (5/2 : ℝ))⁻¹ : ℝ) : EReal) :=
        EReal.coe_nonneg.2 (inv_nonneg.2 (rpow52_nonneg _))
      have hctop : (((g0 V w ^ (5/2 : ℝ))⁻¹ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
      have hin : ∀ kc : ℝ, limsup (fun N : ℕ => ratio (g0 V w) (rhoN N)
          (((E1 kc N + E2 kc N + E3 kc N + E4 kc N + E5 kc N + E6 kc N) / N : ℝ) : EReal))
            atTop =
          (((g0 V w ^ (5/2 : ℝ))⁻¹ : ℝ) : EReal) *
            limsup (fun N : ℕ => ((∑ j, X j kc N + Y N : ℝ) : EReal)) atTop := by
        intro kc
        refine (limsup_congr ?_).trans
          (EReal.limsup_const_mul_of_nonneg_of_ne_top hc0 hctop)
        filter_upwards [eventually_ge_atTop 1] with N hN
        exact hratio kc N hN
      simp only [hin]
      rw [EReal.limsup_const_mul_of_nonneg_of_ne_top hc0 hctop]
      have hmain' : Section4.limsup2 (fun kc N => ∑ j, X j kc N + Y N) ≤
          ((cLHY * g0 V w ^ (5/2 : ℝ) : ℝ) : EReal) := by
        rw [← hconst]; exact hmain
      have hcpos : 0 < g0 V w ^ (5/2 : ℝ) := Real.rpow_pos_of_pos hg _
      calc (((g0 V w ^ (5/2 : ℝ))⁻¹ : ℝ) : EReal) *
            limsup (fun kc : ℝ => limsup (fun N : ℕ => ((∑ j, X j kc N + Y N : ℝ) : EReal))
              atTop) atTop
          ≤ (((g0 V w ^ (5/2 : ℝ))⁻¹ : ℝ) : EReal) *
              ((cLHY * g0 V w ^ (5/2 : ℝ) : ℝ) : EReal) :=
            mul_le_mul_of_nonneg_left hmain' hc0
        _ = (cLHY : EReal) := by
            rw [← EReal.coe_mul]
            congr 1
            field_simp
    · have h0 := rpow52_eq_zero_of_nonpos (not_lt.1 hg)
      have hz : ∀ (kc : ℝ) (N : ℕ), ratio (g0 V w) (rhoN N)
          (((E1 kc N + E2 kc N + E3 kc N + E4 kc N + E5 kc N + E6 kc N) / N : ℝ) : EReal) = 0 := by
        intro kc N
        unfold ratio
        rw [h0]
        simp
      simp only [hz, limsup_const]
      exact EReal.coe_nonneg.2 (by unfold cLHY; positivity)

/-- Theorem 3.1 [lemma2.1] gives Theorem 2.2 [lemma2] with a diagonal choice `k_c(N)`. -/
theorem theorem2_2_of_theorem3_1 (V w : R3 → ℝ) (h : Stmt.Theorem3_1 V w) :
    Stmt.Theorem2_2 V w := by
  obtain ⟨E, hE, hlim⟩ := h
  obtain ⟨k, hk, hkl⟩ := diagonal
    (fun kc N => IsNState N (trialState V w kc N) ∧
      HasEnergy (LN N) V (trialState V w kc N) (E kc N))
    (fun kc N => ratio (g0 V w) (rhoN N) ((E kc N / N : ℝ) : EReal)) cLHY hE hlim
  exact ⟨fun N => trialState V w (k N) N, fun N => E (k N) N, hk, hkl⟩

/-- Theorem 2.2 [lemma2] and the variational principle give the hypothesis of
Lemma 2.2 [lemma1]. -/
theorem limsup_ratio_e0P_le (V w : R3 → ℝ) (hV : PotentialHyp V) (h : Stmt.Theorem2_2 V w) :
    limsup (fun N : ℕ => ratio (g0 V w) (rhoN N) (e0P (LN N) V N)) atTop ≤ (cLHY : EReal) := by
  obtain ⟨Ψ, E, hΨ, hlim⟩ := h
  refine le_trans (limsup_le_limsup ?_) hlim
  filter_upwards [hΨ, eventually_ge_atTop 1] with N hN hN1
  have hv := variational_principle V hV (LN N) (LN_pos hN1) N (Ψ N) (E N) hN.1 hN.2
  unfold ratio
  have hc : (0 : EReal) ≤ (((g0 V w ^ (5/2 : ℝ) * rhoN N ^ (3/2 : ℝ))⁻¹ : ℝ) : EReal) :=
    EReal.coe_nonneg.2 (inv_nonneg.2 (mul_nonneg (rpow52_nonneg _)
      (Real.rpow_nonneg (rhoN_nonneg N) _)))
  exact mul_le_mul_of_nonneg_right (EReal.sub_le_sub hv le_rfl) hc

end Theorem31

end LHYUpper
