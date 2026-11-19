import LHYUpper.Particles.Basic
import LHYUpper.TrialState.Legs

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Auxiliary facts on `M`, on `Ψ` and on nonnegative series -/

/-- A single occupation number is at most the particle number. -/
private lemma Ratios_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]; exact Nat.zero_le _

/-- On `M`, `α(n) ≤ N`. -/
private lemma Ratios_occ_le {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {α : Occ}
    (hα : InM (rhoN N) (LN N) kc N α) (n : Idx) : (α n : ℝ) ≤ N := by
  have h := (Ratios_occ_le_num α n).trans (MBasic_num (Particles_rhoN_LN hN).2.1 hα).le
  exact_mod_cast h

/-- On `M`, `α(n)/|Λ| ≤ ρ`. -/
private lemma Ratios_occ_div_le {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {α : Occ}
    (hα : InM (rhoN N) (LN N) kc N α) (n : Idx) : (α n : ℝ) / LN N ^ 3 ≤ rhoN N := by
  obtain ⟨hNL, -, -, hL⟩ := Particles_rhoN_LN hN
  rw [div_le_iff₀ (by positivity), hNL]
  exact Ratios_occ_le hN hα n

/-- `|p_{-n}| = |p_n|`. -/
private lemma Ratios_norm_mom_neg (L : ℝ) (n : Idx) : ‖mom L (-n)‖ = ‖mom L n‖ := by
  have : mom L (-n) = -mom L n := by
    ext i
    simp [mom]
  rw [this, norm_neg]

/-- `P_{H,c}` of (8.1) [defPHc] is symmetric. -/
private lemma Ratios_PHc_neg {ρ L kc : ℝ} {n : Idx} : inPHc ρ L kc (-n) ↔ inPHc ρ L kc n := by
  simp only [inPHc, Regions_PH_neg, Ratios_norm_mom_neg]

/-- `-u ≠ u` for `u ≠ 0`. -/
private lemma Ratios_neg_ne_self {u : Idx} (hu : u ≠ 0) : -u ≠ u := by
  intro h
  apply hu
  funext i
  have := congr_fun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at this ⊢
  omega

/-- A function on `Idx` supported in `{|p_n| ≤ R}` is summable. -/
private lemma Ratios_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
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

/-- A restriction of a nonnegative summable family is summable. -/
private lemma Ratios_summable_ite {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (p : Occ → Prop) [DecidablePred p] : Summable fun α => if p α then ψ α else 0 :=
  Summable.of_nonneg_of_le (fun α => by split_ifs <;> simp [hψ α])
    (fun α => by split_ifs <;> simp [hψ α]) hs

/-- Splitting a restricted sum along a second condition. -/
private lemma Ratios_split {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (p q : Occ → Prop) [DecidablePred p] [DecidablePred q] :
    (∑' α, if p α then ψ α else 0) =
      (∑' α, if p α ∧ q α then ψ α else 0) + (∑' α, if p α ∧ ¬ q α then ψ α else 0) := by
  have s1 : Summable fun α => if p α ∧ q α then ψ α else 0 := Ratios_summable_ite hs hψ _
  have s2 : Summable fun α => if p α ∧ ¬ q α then ψ α else 0 := Ratios_summable_ite hs hψ _
  rw [← Summable.tsum_add s1 s2]
  congr 1
  funext α
  by_cases hp : p α <;> by_cases hq : q α <;> simp [hp, hq]

/-- Covering bound: if every `α` with `F(α) ≠ 0` is `back j` for some `j` with
`F(α) ≤ G(j)`, then `Σ_α F(α) ≤ Σ_j G(j)`; the choice map `α ↦ j` is injective because
`back` inverts it. -/
private lemma Ratios_cover {ι : Type*} (F : Occ → ℝ) (G : ι → ℝ) (hF : ∀ α, 0 ≤ F α)
    (hG : ∀ j, 0 ≤ G j) (hGs : Summable G) (back : ι → Occ)
    (h : ∀ α, F α ≠ 0 → ∃ j, back j = α ∧ F α ≤ G j) : (∑' α, F α) ≤ ∑' j, G j := by
  let φ : Function.support F → ι := fun x => (h x.1 x.2).choose
  have hφ1 : ∀ x, back (φ x) = x.1 := fun x => (h x.1 x.2).choose_spec.1
  have hφ2 : ∀ x, F x.1 ≤ G (φ x) := fun x => (h x.1 x.2).choose_spec.2
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply Subtype.ext
    rw [← hφ1 x, ← hφ1 y, hxy]
  have hGc : Summable (G ∘ φ) := hGs.comp_injective hinj
  have hFs : Summable (fun x : Function.support F => F x.1) :=
    Summable.of_nonneg_of_le (fun x => hF x.1) hφ2 hGc
  rw [← tsum_subtype_eq_of_support_subset (s := Function.support F) subset_rfl]
  calc (∑' x : Function.support F, F x.1) ≤ ∑' x : Function.support F, G (φ x) :=
        hFs.tsum_le_tsum hφ2 hGc
    _ ≤ ∑' j, G j := tsum_comp_le_tsum_of_inj hGs hG hinj

/-- `Ψ` vanishes off `M`. -/
private lemma Ratios_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : ‖trialState V w kc N α‖ ^ 2 ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hc
  apply h
  rw [FIdentities_trialState, ite_eq_right hc, norm_zero]
  norm_num

/-- `Q_Ψ({u, m})` as a restricted sum. -/
private lemma Ratios_Qm_single (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) :
    Expect.Qm Ψ [(u, m)] = ∑' α : Occ, if α u = m then ‖Ψ α‖ ^ 2 else 0 := by
  simp [Expect.Qm, Expect.Ev]

/-- `|Ψ(α)|² = |z|²|Ψ(β)|²` when `f(α) = z f(β)` on `M`, (3.18) [deffal]. -/
private lemma Ratios_normsq (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {α β : Occ}
    (hα : InM (rhoN N) (LN N) kc N α) (hβ : InM (rhoN N) (LN N) kc N β) (z : ℂ)
    (h : f0 V w (rhoN N) (LN N) α = z * f0 V w (rhoN N) (LN N) β) :
    ‖trialState V w kc N α‖ ^ 2 = ‖z‖ ^ 2 * ‖trialState V w kc N β‖ ^ 2 := by
  rw [FIdentities_trialState, FIdentities_trialState, ite_eq_left hα, ite_eq_left hβ, h]
  simp only [norm_mul]
  ring

/-- `|√x|² = |x|` for the square root of Definition 3.6. -/
private lemma Ratios_norm_csqrt_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h, abs_of_nonneg h]
  · have h' : x < 0 := not_le.1 h
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by linarith), abs_of_neg h']

/-- `|Ψ(𝓐^k β)|² = β(0)(β(0) − 1)|Λ|⁻²λ_k²|Ψ(β)|²` from (5.4) [properf1] or (5.5) [properf2]. -/
private lemma Ratios_strict_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} {k : Idx} {β : Occ}
    (hβ : InM (rhoN N) (LN N) kc N β) (hα : InM (rhoN N) (LN N) kc N (strictPair k β))
    (h1 : 1 ≤ β 0)
    (hf : f0 V w (rhoN N) (LN N) (strictPair k β) =
      ((Real.sqrt ((β 0 : ℝ) / LN N ^ 3) * Real.sqrt (((β 0 : ℝ) - 1) / LN N ^ 3) *
        lam V w (rhoN N) (LN N) k : ℝ) : ℂ) * f0 V w (rhoN N) (LN N) β)
    (hL : 0 < LN N) :
    ‖trialState V w kc N (strictPair k β)‖ ^ 2 =
      (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) * lam V w (rhoN N) (LN N) k ^ 2 *
        ‖trialState V w kc N β‖ ^ 2 := by
  have h1' : (1 : ℝ) ≤ β 0 := by exact_mod_cast h1
  rw [Ratios_normsq V w kc N hα hβ _ hf, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow,
    mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (div_nonneg (by linarith) (by positivity))]

/-- `|Ψ(𝓐^{u;p₁,p₂} β)|² = 4β(0)β(u)|Λ|⁻²|λ_{p₁}λ_{p₂}||Ψ(β)|²` from (5.7) [properf4]. -/
private lemma Ratios_soft_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u p₁ p₂ : Idx}
    {β : Occ} (hu : inPL (rhoN N) (LN N) u) (h₁ : inPH (rhoN N) (LN N) p₁)
    (h₂ : inPH (rhoN N) (LN N) p₂) (hs : p₁ + p₂ = u) (hβ : InMuS (rhoN N) (LN N) kc N u β)
    (hα : InM (rhoN N) (LN N) kc N (softPair u p₁ p₂ β)) :
    ‖trialState V w kc N (softPair u p₁ p₂ β)‖ ^ 2 =
      4 * ((β 0 : ℝ) / LN N ^ 3) * ((β u : ℝ) / LN N ^ 3) *
        |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| *
          ‖trialState V w kc N β‖ ^ 2 := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hf := Lemma5_1_properf4 (V := V) (w := w) hρ hL hu h₁ h₂ hs hβ hα
  rw [Ratios_normsq V w kc N hα hβ.1 _ hf, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, mul_pow, mul_pow,
    Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity), Ratios_norm_csqrt_sq,
    Ratios_norm_csqrt_sq, abs_mul]
  ring

/-- `β(0)(β(0) − 1)|Λ|⁻²λ² ≤ (ρλ)²` on `M`. -/
private lemma Ratios_strict_le {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {β : Occ}
    (hβ : InM (rhoN N) (LN N) kc N β) (h1 : 1 ≤ β 0) (l : ℝ) :
    (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) * l ^ 2 ≤ (rhoN N * l) ^ 2 := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have h1' : (1 : ℝ) ≤ β 0 := by exact_mod_cast h1
  have ha := Ratios_occ_div_le hN hβ 0
  have hb : ((β 0 : ℝ) - 1) / LN N ^ 3 ≤ (β 0 : ℝ) / LN N ^ 3 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hb0 : 0 ≤ ((β 0 : ℝ) - 1) / LN N ^ 3 := div_nonneg (by linarith) (by positivity)
  rw [mul_pow]
  have : (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) ≤ rhoN N ^ 2 := by
    rw [sq]
    exact mul_le_mul ha (hb.trans ha) hb0 hρ.le
  exact mul_le_mul_of_nonneg_right this (sq_nonneg _)

/-- `4xy|Λ|⁻¹tψ ≤ 4ρY|Λ|⁻¹ψt` for `0 ≤ x ≤ ρ`, `0 ≤ y ≤ Y`, `t, ψ ≥ 0`. -/
private lemma Ratios_soft_le {ρ L x y Y t ψ : ℝ} (hL : 0 < L) (hx0 : 0 ≤ x) (hx : x ≤ ρ)
    (hy0 : 0 ≤ y) (hy : y ≤ Y) (ht : 0 ≤ t) (hψ : 0 ≤ ψ) :
    4 * x * (y / L ^ 3) * t * ψ ≤ 4 * ρ * Y / L ^ 3 * (ψ * t) := by
  have hL3 : 0 < L ^ 3 := by positivity
  have hxy : x * y ≤ ρ * Y := mul_le_mul hx hy hy0 (hx0.trans hx)
  have e1 : 4 * x * (y / L ^ 3) * t * ψ = (x * y) * (4 * t * ψ / L ^ 3) := by ring
  have e2 : 4 * ρ * Y / L ^ 3 * (ψ * t) = (ρ * Y) * (4 * t * ψ / L ^ 3) := by ring
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_right hxy (by positivity)

/-- One step of Proposition 5.1 [prop5]: `Q_Ψ({u, m + 1}) ≤ (ρλ_u)² Q_Ψ({u, m})` on `P_I`. -/
private lemma Ratios_PI_step (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPI (rhoN N) (LN N) u) (m : ℕ) :
    Expect.Qm (trialState V w kc N) [(u, m + 1)] ≤
      (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 * Expect.Qm (trialState V w kc N) [(u, m)] := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  rw [Ratios_Qm_single, Ratios_Qm_single, ← tsum_mul_left]
  refine Ratios_cover _ _ (fun α => by split_ifs <;> positivity)
    (fun β => mul_nonneg (sq_nonneg _) (by split_ifs <;> positivity))
    ((Ratios_summable_ite hs (fun _ => by positivity) _).mul_left _) (strictPair u) ?_
  intro α hα
  have hm : α u = m + 1 := by
    by_contra h
    exact hα (ite_eq_right (by exact_mod_cast h))
  have hψ : ‖trialState V w kc N α‖ ^ 2 ≠ 0 := by
    intro h
    exact hα (by simp [h])
  have hαM := Ratios_inM hψ
  obtain ⟨β, hβ, h2, he, hv⟩ := Prop5_2 hρ hu hαM (by omega)
  refine ⟨β, he, ?_⟩
  have hβm : (β u : ℕ) = m := by omega
  rw [ite_eq_left (by exact_mod_cast hm), ite_eq_left hβm]
  subst he
  have hf := Lemma5_1_properf1 (V := V) (w := w) hρ hL (Or.inl hu) hβ hαM
  rw [Ratios_strict_eq V w kc hβ hαM (by omega) hf hL]
  exact mul_le_mul_of_nonneg_right (Ratios_strict_le hN hβ (by omega) _) (by positivity)

/-- Proposition 5.1 [prop5], (5.16) [7]: `Q_Ψ({u, m + i}) ≤ (ρλ_u)^{2i} Q_Ψ({u, m})` on `P_I`. -/
theorem Prop5_1 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPI (rhoN N) (LN N) u) (m i : ℕ) :
    Expect.Qm (trialState V w kc N) [(u, m + i)] ≤
      ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) ^ i *
        Expect.Qm (trialState V w kc N) [(u, m)] := by
  induction i with
  | zero => simp
  | succ i ih =>
    calc Expect.Qm (trialState V w kc N) [(u, m + (i + 1))]
        = Expect.Qm (trialState V w kc N) [(u, (m + i) + 1)] := by rw [add_assoc]
      _ ≤ (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
            Expect.Qm (trialState V w kc N) [(u, m + i)] := Ratios_PI_step V w kc hN hu _
      _ ≤ (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
            (((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) ^ i *
              Expect.Qm (trialState V w kc N) [(u, m)]) :=
          mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2) ^ (i + 1) *
            Expect.Qm (trialState V w kc N) [(u, m)] := by ring

/-- (5.26) [pubrho3]: the symmetric part of `Q_Ψ({u, m + 1})` on `P_L`. -/
theorem Eq5_26 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) (m : ℕ) :
    (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m + 1 then
        ‖trialState V w kc N β‖ ^ 2 else 0) ≤
      (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 *
        (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m then
          ‖trialState V w kc N β‖ ^ 2 else 0) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  have hu0 := Regions_PL_ne_zero hρ hu
  have hnu := Ratios_neg_ne_self hu0
  rw [← tsum_mul_left]
  refine Ratios_cover _ _ (fun α => by split_ifs <;> positivity)
    (fun β => mul_nonneg (sq_nonneg _) (by split_ifs <;> positivity))
    ((Ratios_summable_ite hs (fun _ => by positivity) _).mul_left _) (strictPair u) ?_
  intro α hα
  have hc : InMuS (rhoN N) (LN N) kc N u α ∧ α u = m + 1 := by
    by_contra h
    exact hα (ite_eq_right h)
  obtain ⟨⟨hαM, hsym⟩, hm⟩ := hc
  obtain ⟨γ, ⟨hγ, he⟩, -⟩ := Legs_unique_gamma hρ (Or.inl hu) hαM (by omega) (by omega)
  have hγ2 : 2 ≤ γ 0 := MBasic_strict_le hρ hγ (by rw [he]; exact hαM)
  have e1 := MBasic_strictPair_apply u γ u
  have e2 := MBasic_strictPair_apply u γ (-u)
  rw [he] at e1 e2
  simp only [hu0, hnu, Ne.symm hnu, neg_eq_zero, ite_false, ite_true] at e1 e2
  have hγu : γ u = m := by omega
  have hγS : InMuS (rhoN N) (LN N) kc N u γ := ⟨hγ, by omega⟩
  refine ⟨γ, he, ?_⟩
  rw [ite_eq_left ⟨⟨hαM, hsym⟩, hm⟩, ite_eq_left ⟨hγS, hγu⟩]
  subst he
  have hf := Lemma5_1_properf2 (V := V) (w := w) hρ hL hu hγS hαM
  rw [Ratios_strict_eq V w kc hγ hαM (by omega) hf hL]
  exact mul_le_mul_of_nonneg_right (Ratios_strict_le hN hγ (by omega) _) (by positivity)

/-- The soft creation bound for one sign of the asymmetry: the configurations of `M_u^a`
with `α(-u) = α(u) + 1` (`pos = true`) or with `α(u) = α(-u) + 1` (`pos = false`) and
`α*(u) = m` are bounded by `4ρm|Λ|⁻¹ Σ_p |λ_p λ_{u−p}|` times the symmetric ones,
(5.19) [ubpsiuroughPL1.5], (5.20) [ubpsiuroughPL2]. -/
private lemma Ratios_soft_sign (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) (E : Occ → Prop)
    (hE : ∀ α β : Occ, (∀ n, n ≠ 0 → n ≠ u → n ≠ -u → ¬ inPH (rhoN N) (LN N) n → α n = β n) →
      (E α ↔ E β)) (m : ℕ) (pos : Bool) :
    (∑' α : Occ, if (InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m ∧ E α) ∧
        (α (-u) = α u + 1 ↔ pos = true) then ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      4 * rhoN N * m / LN N ^ 3 *
        ((∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m ∧ E β then
          ‖trialState V w kc N β‖ ^ 2 else 0) *
        (∑' p : Idx, if inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (u - p) then
          |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (u - p)| else 0)) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  have hu0 := Regions_PL_ne_zero hρ hu
  have hnu := Ratios_neg_ne_self hu0
  have hnu0 : -u ≠ 0 := neg_ne_zero.2 hu0
  set S : Occ → ℝ := fun β => if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m ∧ E β then
    ‖trialState V w kc N β‖ ^ 2 else 0 with hS
  set T : Idx → ℝ := fun p => if inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (u - p)
    then |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (u - p)| else 0 with hT
  have hS0 : ∀ β, 0 ≤ S β := fun β => by simp only [hS]; split_ifs <;> positivity
  have hT0 : ∀ p, 0 ≤ T p := fun p => by simp only [hT]; split_ifs <;> positivity
  have hSs : Summable S := Ratios_summable_ite hs (fun _ => by positivity) _
  have hTs : Summable T := Ratios_summable_ball (R := kc) hL T (fun p hp => by
    simp only [hT] at hp
    split_ifs at hp with h
    · exact h.1.2
    · exact absurd rfl hp)
  have hST : Summable fun j : Occ × Idx => S j.1 * T j.2 :=
    hSs.mul_of_nonneg hTs (fun β => hS0 β) (fun p => hT0 p)
  have hc : 0 ≤ 4 * rhoN N * m / LN N ^ 3 := by positivity
  rw [Summable.tsum_mul_tsum hSs hTs hST, ← tsum_mul_left]
  -- the choice map depends on the sign
  let back : Occ × Idx → Occ := fun j =>
    if pos then softPair u j.2 (u - j.2) j.1 else softPair (-u) (-j.2) (j.2 - u) j.1
  refine Ratios_cover _ _ (fun α => by split_ifs <;> positivity)
    (fun j => mul_nonneg hc (mul_nonneg (hS0 _) (hT0 _))) (hST.mul_left _) back ?_
  intro α hα
  have hc' : (InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m ∧ E α) ∧
      (α (-u) = α u + 1 ↔ pos = true) := by
    by_contra h
    exact hα (ite_eq_right h)
  obtain ⟨⟨⟨hαM, hne⟩, hm, hEα⟩, hpos⟩ := hc'
  rw [ite_eq_left ⟨⟨⟨hαM, hne⟩, hm, hEα⟩, hpos⟩]
  -- agreement off `{0, ±u} ∪ P_H` transfers the event
  have hagree : ∀ (s p₁ p₂ : Idx) (β : Occ), (s = u ∨ s = -u) →
      inPH (rhoN N) (LN N) p₁ → inPH (rhoN N) (LN N) p₂ → softPair s p₁ p₂ β = α →
      (E α ↔ E β) := by
    intro s p₁ p₂ β hs' h₁ h₂ he
    refine hE α β (fun n hn0 hnu' hnnu hnH => ?_)
    rw [← he, MBasic_softPair_apply]
    have hns : n ≠ s := by rcases hs' with rfl | rfl <;> assumption
    have hn1 : n ≠ p₁ := fun h => hnH (h ▸ h₁)
    have hn2 : n ≠ p₂ := fun h => hnH (h ▸ h₂)
    simp [hn0, hns, hn1, hn2]
  cases pos with
  | true =>
    have ha : α (-u) = α u + 1 := hpos.2 rfl
    obtain ⟨β, p₁, p₂, hβS, hc₁, hc₂, hsum, hb0, hbu, he⟩ := Reorder_softLast hρ hu hαM ha
    have hp₂ : u - p₁ = p₂ := by rw [← hsum]; abel
    obtain ⟨-, -, -, -, h1u, h1nu, h2u, h2nu⟩ := Regions_soft_distinct hρ hu hc₁.1 hc₂.1 hsum
    refine ⟨(β, p₁), by simp only [back, ite_true, hp₂, he], ?_⟩
    have e1 := MBasic_softPair_apply u p₁ p₂ β u
    have e2 := MBasic_softPair_apply u p₁ p₂ β (-u)
    rw [he] at e1 e2
    simp only [hu0, hnu, Ne.symm h1u, Ne.symm h2u, Ne.symm h1nu, Ne.symm h2nu, ite_false,
      ite_true, hnu0] at e1 e2
    have hsym : β u = β (-u) := hβS.2
    have hβm : β u = m := by
      simp only [alphaStar] at hm
      omega
    have hEβ : E β := (hagree u p₁ p₂ β (Or.inl rfl) hc₁.1 hc₂.1 he).1 hEα
    have hSβ : S β = ‖trialState V w kc N β‖ ^ 2 := by
      simp only [hS]; rw [ite_eq_left ⟨hβS, hβm, hEβ⟩]
    have hTp : T p₁ = |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| := by
      simp only [hT]; rw [hp₂, ite_eq_left ⟨hc₁, hc₂⟩]
    rw [hSβ, hTp]
    subst he
    rw [Ratios_soft_eq V w kc hN hu hc₁.1 hc₂.1 hsum hβS hαM, hβm]
    exact Ratios_soft_le hL (by positivity) (Ratios_occ_div_le hN hβS.1 0) (by positivity)
      le_rfl (abs_nonneg _) (by positivity)
  | false =>
    have ha : ¬ α (-u) = α u + 1 := fun h => Bool.false_ne_true (hpos.1 h)
    have hs1 := MStar_PL_star hρ hαM hu
    have hs2 := MStar_PL_star hρ hαM (Regions_PL_neg.2 hu)
    simp only [alphaStar, neg_neg] at hs1 hs2 hm
    have ha' : α (-(-u)) = α (-u) + 1 := by rw [neg_neg]; omega
    have hnL := Regions_PL_neg.2 hu
    obtain ⟨β, p₁, p₂, hβS, hc₁, hc₂, hsum, hb0, hbu, he⟩ := Reorder_softLast hρ hnL hαM ha'
    have hp : -(-p₁) = p₁ := neg_neg p₁
    have hp₂ : -p₁ - u = p₂ := by
      have : u = -(p₁ + p₂) := by rw [hsum, neg_neg]
      rw [this]; abel
    have hp₂' : u - -p₁ = -p₂ := by
      have : u = -(p₁ + p₂) := by rw [hsum, neg_neg]
      rw [this]; abel
    obtain ⟨-, -, -, -, h1u, h1nu, h2u, h2nu⟩ := Regions_soft_distinct hρ hnL hc₁.1 hc₂.1 hsum
    rw [neg_neg] at h1nu h2nu
    refine ⟨(β, -p₁), by simp only [back, hp, hp₂, he]; simp, ?_⟩
    have e1 := MBasic_softPair_apply (-u) p₁ p₂ β u
    have e2 := MBasic_softPair_apply (-u) p₁ p₂ β (-u)
    rw [he] at e1 e2
    simp only [hu0, Ne.symm hnu, Ne.symm h1u, Ne.symm h2u, Ne.symm h1nu, Ne.symm h2nu,
      ite_false, ite_true, hnu0] at e1 e2
    have hsym : β u = β (-u) := by have := hβS.2; rw [neg_neg] at this; omega
    have hβm : β u = m := by omega
    have hβS' : InMuS (rhoN N) (LN N) kc N u β := ⟨hβS.1, hsym⟩
    have hEβ : E β := (hagree (-u) p₁ p₂ β (Or.inr rfl) hc₁.1 hc₂.1 he).1 hEα
    have hSβ : S β = ‖trialState V w kc N β‖ ^ 2 := by
      simp only [hS]; rw [ite_eq_left ⟨hβS', hβm, hEβ⟩]
    have hTp : T (-p₁) = |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| := by
      simp only [hT]
      rw [hp₂', ite_eq_left ⟨Ratios_PHc_neg.2 hc₁, Ratios_PHc_neg.2 hc₂⟩, Regions_lam_neg,
        Regions_lam_neg]
    rw [hSβ, hTp]
    subst he
    rw [Ratios_soft_eq V w kc hN hnL hc₁.1 hc₂.1 hsum hβS hαM, ← hsym, hβm]
    exact Ratios_soft_le hL (by positivity) (Ratios_occ_div_le hN hβS.1 0) (by positivity)
      le_rfl (abs_nonneg _) (by positivity)

/-- (5.19)–(5.21) with both signs of the asymmetry: for an event `E` that depends only on
the occupations outside `{0, ±u} ∪ P_H`, the asymmetric configurations with `α*(u) = m` are
bounded by `8ρm|Λ|⁻¹ Σ_p |λ_p λ_{u−p}|` times the symmetric ones with `β(u) = m`. -/
theorem Particles_softCreation (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) (E : Occ → Prop)
    (hE : ∀ α β : Occ, (∀ n, n ≠ 0 → n ≠ u → n ≠ -u → ¬ inPH (rhoN N) (LN N) n → α n = β n) →
      (E α ↔ E β)) (m : ℕ) :
    (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m ∧ E α then
        ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      8 * rhoN N * m / LN N ^ 3 *
        (∑' p : Idx, if inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (u - p) then
          |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (u - p)| else 0) *
        (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N u β ∧ β u = m ∧ E β then
          ‖trialState V w kc N β‖ ^ 2 else 0) := by
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  rw [Ratios_split hs (fun _ => by positivity) _ (fun α => α (-u) = α u + 1 ↔ true = true)]
  have h1 := Ratios_soft_sign V w kc hN hu E hE m true
  have h2 := Ratios_soft_sign V w kc hN hu E hE m false
  have e : (fun α : Occ => if (InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m ∧ E α) ∧
      ¬ (α (-u) = α u + 1 ↔ true = true) then ‖trialState V w kc N α‖ ^ 2 else 0) =
      fun α => if (InMuA (rhoN N) (LN N) kc N u α ∧ alphaStar α u = m ∧ E α) ∧
        (α (-u) = α u + 1 ↔ false = true) then ‖trialState V w kc N α‖ ^ 2 else 0 := by
    funext α
    congr 1
    simp
  rw [e]
  exact (add_le_add h1 h2).trans_eq (by ring)

/-- Proposition 5.3 [prop2] (A) as a predicate: `α = 𝓐^u β` for some `β ∈ M` with
`β(0) ≥ 2` and `β(u) + 1 = α(u)`. -/
private def Ratios_caseA (ρ L kc : ℝ) (N : ℕ) (u : Idx) (α : Occ) : Prop :=
  ∃ β, InM ρ L kc N β ∧ 2 ≤ β 0 ∧ strictPair u β = α ∧ β u + 1 = α u

/-- (5.27) [4.1], case (A) of Proposition 5.3 [prop2]: for `u ∈ P_H` and any condition `c`
on `α(u)` that is shifted by one to `c'` on `β(u)`, the strict images are bounded by
`ρ²λ_u²` (or `λ_u²|Λ|⁻²β(0)²` in the weighted form). -/
private lemma Ratios_PH_caseA (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPH (rhoN N) (LN N) u) (c c' : ℕ → Prop) [DecidablePred c]
    (hcc : ∀ k, c (k + 1) → c' k) (wt : Occ → ℝ) (hwt0 : ∀ β, 0 ≤ wt β) (hwts : Summable wt)
    (hwt : ∀ β, InM (rhoN N) (LN N) kc N β → 2 ≤ β 0 → c' (β u) →
      (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) * lam V w (rhoN N) (LN N) u ^ 2 *
        ‖trialState V w kc N β‖ ^ 2 ≤ wt β) :
    (∑' α : Occ, if c (α u) ∧ Ratios_caseA (rhoN N) (LN N) kc N u α then
      ‖trialState V w kc N α‖ ^ 2 else 0) ≤ ∑' β, wt β := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  refine Ratios_cover _ _ (fun α => by split_ifs <;> positivity) hwt0 hwts (strictPair u) ?_
  intro α hα
  have hc : c (α u) ∧ Ratios_caseA (rhoN N) (LN N) kc N u α := by
    by_contra h
    exact hα (ite_eq_right h)
  obtain ⟨hcα, β, hβ, h2, he, hv⟩ := hc
  have hψ : ‖trialState V w kc N α‖ ^ 2 ≠ 0 := by
    intro h
    exact hα (by simp [h])
  have hαM := Ratios_inM hψ
  refine ⟨β, he, ?_⟩
  rw [ite_eq_left ⟨hcα, β, hβ, h2, he, hv⟩]
  have hcβ : c' (β u) := hcc _ (by rw [hv]; exact hcα)
  subst he
  have hf := Lemma5_1_properf1 (V := V) (w := w) hρ hL (Or.inr hu) hβ hαM
  rw [Ratios_strict_eq V w kc hβ hαM (by omega) hf hL]
  exact hwt β hβ h2 hcβ

/-- (5.27) [4.1], case (B) of Proposition 5.3 [prop2]: for `u ∈ P_H`, the soft images
`α = 𝓐^{v;u,v−u} β` (`v ∈ P_L`, `β ∈ M_v^s`) with `c(α(u))` are bounded by a weight on
`(β, v)`. -/
private lemma Ratios_PH_caseB (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPH (rhoN N) (LN N) u) (c : ℕ → Prop) [DecidablePred c] (h0 : ¬ c 0) (wt : Occ × Idx → ℝ)
    (hwt0 : ∀ j, 0 ≤ wt j) (hwts : Summable wt)
    (hwt : ∀ v β, inPL (rhoN N) (LN N) v → InMuS (rhoN N) (LN N) kc N v β →
      inPHc (rhoN N) (LN N) kc u → inPHc (rhoN N) (LN N) kc (v - u) → c (β u + 1) →
      4 * ((β 0 : ℝ) / LN N ^ 3) * ((β v : ℝ) / LN N ^ 3) *
        |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (v - u)| *
          ‖trialState V w kc N β‖ ^ 2 ≤ wt (β, v)) :
    (∑' α : Occ, if c (α u) ∧ ¬ Ratios_caseA (rhoN N) (LN N) kc N u α then
      ‖trialState V w kc N α‖ ^ 2 else 0) ≤ ∑' j, wt j := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  refine Ratios_cover _ _ (fun α => by split_ifs <;> positivity) hwt0 hwts
    (fun j => softPair j.2 u (j.2 - u) j.1) ?_
  intro α hα
  have hc : c (α u) ∧ ¬ Ratios_caseA (rhoN N) (LN N) kc N u α := by
    by_contra h
    exact hα (ite_eq_right h)
  obtain ⟨hcα, hnA⟩ := hc
  have hψ : ‖trialState V w kc N α‖ ^ 2 ≠ 0 := by
    intro h
    exact hα (by simp [h])
  have hαM := Ratios_inM hψ
  have h1 : 1 ≤ α u := by
    by_contra h
    exact h0 (by rw [show α u = 0 by omega] at hcα; exact hcα)
  rcases Prop5_3 hρ hu hαM h1 with hA | ⟨v, β, hv, hβS, hb0, hbv, hcu, hcvu, he, hval⟩
  · exact absurd hA hnA
  refine ⟨(β, v), he, ?_⟩
  rw [ite_eq_left ⟨hcα, hnA⟩]
  have hcβ : c (β u + 1) := by rw [hval]; exact hcα
  subst he
  have hs : u + (v - u) = v := by abel
  rw [Ratios_soft_eq V w kc hN hv hcu.1 hcvu.1 hs hβS hαM]
  exact hwt v β hv hβS hcu hcvu hcβ

/-- (5.27) [4.1] in the exact form: `Q_Ψ({u, m + 1}) ≤ c_u Q_Ψ({u, m})` on `P_H`, with
`c_u = ρ²λ_u² + 4ρ⌈m_c⌉|Λ|⁻¹ Σ_{v ∈ P_L, v − u ∈ P_{H,c}} |λ_u λ_{v−u}|`. -/
theorem Eq5_27 (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPH (rhoN N) (LN N) u) (m : ℕ) :
    Expect.Qm (trialState V w kc N) [(u, m + 1)] ≤
      ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 +
        4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 *
          (∑' v : Idx, (if inPL (rhoN N) (LN N) v ∧ inPHc (rhoN N) (LN N) kc (v - u) then
            |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (v - u)| else 0))) *
        Expect.Qm (trialState V w kc N) [(u, m)] := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  have hs0 : ∀ α, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψdef
  set Sm : Occ → ℝ := fun β => if β u = m then ψ β else 0 with hSm
  set A : Idx → ℝ := fun v => if inPL (rhoN N) (LN N) v ∧ inPHc (rhoN N) (LN N) kc (v - u) then
    |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (v - u)| else 0 with hA
  have hSm0 : ∀ β, 0 ≤ Sm β := fun β => by simp only [hSm]; split_ifs <;> simp [hψdef, hs0]
  have hA0 : ∀ v, 0 ≤ A v := fun v => by simp only [hA]; split_ifs <;> positivity
  have hSms : Summable Sm := Ratios_summable_ite hs hs0 _
  have hAs : Summable A := Ratios_summable_ball (R := (epsP (rhoN N))⁻¹ * rhoN N ^ (1/2 : ℝ))
    hL A (fun v hv => by
      simp only [hA] at hv
      split_ifs at hv with h
      · exact h.1.2
      · exact absurd rfl hv)
  have hSA : Summable fun j : Occ × Idx => Sm j.1 * A j.2 :=
    hSms.mul_of_nonneg hAs (fun β => hSm0 β) (fun v => hA0 v)
  have hQm : ∀ k : ℕ, Expect.Qm (trialState V w kc N) [(u, k)] =
      ∑' α, if α u = k then ψ α else 0 := fun k => Ratios_Qm_single _ _ _
  rw [hQm, hQm]
  have hsplit := Ratios_split hs hs0 (fun α => α u = m + 1) (Ratios_caseA (rhoN N) (LN N) kc N u)
  beta_reduce at hsplit
  rw [hsplit]
  have hcA := Ratios_PH_caseA V w kc hN hu (fun k => k = m + 1) (fun k => k = m)
    (fun k hk => by have : k + 1 = m + 1 := hk; omega) (fun β =>
      (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 * Sm β)
    (fun β => mul_nonneg (sq_nonneg _) (hSm0 β)) (hSms.mul_left _) (fun β hβ h2 hc => by
      simp only [hSm, ite_eq_left hc]
      exact mul_le_mul_of_nonneg_right (Ratios_strict_le hN hβ (by omega) _) (hs0 _))
  have hc : 0 ≤ 4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 := by positivity
  have hwB0 : ∀ j : Occ × Idx, 0 ≤ 4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 * (Sm j.1 * A j.2) :=
    fun j => mul_nonneg hc (mul_nonneg (hSm0 _) (hA0 _))
  have hwBs : Summable fun j : Occ × Idx =>
      4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 * (Sm j.1 * A j.2) := hSA.mul_left _
  have hcB := Ratios_PH_caseB V w kc hN hu (fun k => k = m + 1) (by simp) (fun j =>
      4 * rhoN N * ⌈mc (rhoN N)⌉₊ / LN N ^ 3 * (Sm j.1 * A j.2)) hwB0 hwBs
    (fun v β hv hβS hcu hcvu hc => by
      have hβm : β u = m := by omega
      simp only [hSm, hA]
      rw [ite_eq_left hβm, ite_eq_left (And.intro hv hcvu)]
      have hbv : (β v : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := by
        have := (le_max_left (β v) (β (-v))).trans (MStar_PL_ceil hρ hβS.1 hv)
        exact_mod_cast this
      exact Ratios_soft_le hL (by positivity) (Ratios_occ_div_le hN hβS.1 0) (by positivity)
        hbv (abs_nonneg _) (hs0 _))
  rw [tsum_mul_left] at hcA
  rw [tsum_mul_left, ← Summable.tsum_mul_tsum hSms hAs hSA] at hcB
  exact (add_le_add hcA hcB).trans_eq (by ring)

/-- `Σ_{m ≥ 0} Q_Ψ({u, m + 1}) = Σ_{α(u) ≥ 1} |Ψ(α)|²`. -/
private lemma Ratios_tsum_Qm_succ (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx) :
    (∑' m : ℕ, Expect.Qm (trialState V w kc N) [(u, m + 1)]) =
      ∑' α : Occ, if 1 ≤ α u then ‖trialState V w kc N α‖ ^ 2 else 0 := by
  have hΨ := Normalization_isNState V w kc hN
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hs0 : ∀ α, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  have h1 := Expect.tsum_Qm_single N _ hΨ u
  have hsm : Summable fun m : ℕ => Expect.Qm (trialState V w kc N) [(u, m)] := by
    by_contra hc
    rw [tsum_eq_zero_of_not_summable hc] at h1
    norm_num at h1
  rw [hsm.tsum_eq_zero_add, Ratios_Qm_single] at h1
  have h2 : (∑' α, ‖trialState V w kc N α‖ ^ 2) =
      (∑' α : Occ, if α u = ((0 : ℕ) : ℕ) then ‖trialState V w kc N α‖ ^ 2 else 0) +
        ∑' α : Occ, if 1 ≤ α u then ‖trialState V w kc N α‖ ^ 2 else 0 := by
    rw [← Summable.tsum_add (Ratios_summable_ite hs hs0 _) (Ratios_summable_ite hs hs0 _)]
    congr 1
    funext α
    by_cases h : α u = 0 <;> simp [h, Nat.one_le_iff_ne_zero]
  rw [hΨ.1.tsum_eq] at h2
  linarith

/-- (5.27) [4.1] summed over `m ≥ 1`, the form used in §6: for `u ∈ P_H`,
`Σ_{m≥1} Q_Ψ({u, m}) ≤ λ_u²|Λ|⁻² Q_Ψ(0, 0) + 4ρ|Λ|⁻¹ Σ_{v ∈ P_L} Q_Ψ(v)|λ_u λ_{v−u}|`. -/
theorem Eq5_27_sum (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPH (rhoN N) (LN N) u) :
    (∑' m : ℕ, Expect.Qm (trialState V w kc N) [(u, m + 1)]) ≤
      lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2 * Expect.Q (trialState V w kc N) [0, 0] +
        4 * rhoN N / LN N ^ 3 *
          (∑' v : Idx, (if inPL (rhoN N) (LN N) v ∧ inPHc (rhoN N) (LN N) kc (v - u) then
            Expect.Q (trialState V w kc N) [v] *
              |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (v - u)| else 0)) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hs : Summable fun α => ‖trialState V w kc N α‖ ^ 2 :=
    (Normalization_isNState V w kc hN).1.summable
  have hs0 : ∀ α, 0 ≤ ‖trialState V w kc N α‖ ^ 2 := fun _ => by positivity
  set ψ : Occ → ℝ := fun α => ‖trialState V w kc N α‖ ^ 2 with hψdef
  set A : Idx → ℝ := fun v => if inPL (rhoN N) (LN N) v ∧ inPHc (rhoN N) (LN N) kc (v - u) then
    |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (v - u)| else 0 with hA
  have hA0 : ∀ v, 0 ≤ A v := fun v => by simp only [hA]; split_ifs <;> positivity
  have hAs : Summable A := Ratios_summable_ball (R := (epsP (rhoN N))⁻¹ * rhoN N ^ (1/2 : ℝ))
    hL A (fun v hv => by
      simp only [hA] at hv
      split_ifs at hv with h
      · exact h.1.2
      · exact absurd rfl hv)
  -- `β(n)|Ψ(β)|² ≤ N|Ψ(β)|²`
  have hocc : ∀ (n : Idx) (β : Occ), (β n : ℝ) * ψ β ≤ N * ψ β := by
    intro n β
    by_cases h : ψ β = 0
    · simp [h]
    · exact mul_le_mul_of_nonneg_right (Ratios_occ_le hN (Ratios_inM h) n) (hs0 β)
  have hQ1 : ∀ v : Idx, Expect.Q (trialState V w kc N) [v] = ∑' β, (β v : ℝ) * ψ β := by
    intro v
    simp [Expect.Q, hψdef]
  have hQ2 : Expect.Q (trialState V w kc N) [0, 0] = ∑' β, (β 0 : ℝ) * (β 0 : ℝ) * ψ β := by
    simp [Expect.Q, hψdef]
  -- weights of the two cases
  set WA : Occ → ℝ := fun β =>
    lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2 * ((β 0 : ℝ) * (β 0 : ℝ) * ψ β) with hWA
  have hNN : Summable fun β => (N : ℝ) * N * ψ β := hs.mul_left _
  have hWAs : Summable WA := by
    refine Summable.mul_left _ (Summable.of_nonneg_of_le (fun β => by positivity)
      (fun β => ?_) hNN)
    have h1 := hocc 0 β
    have h2 : (β 0 : ℝ) ≤ N ∨ ψ β = 0 := by
      by_cases h : ψ β = 0
      · exact Or.inr h
      · exact Or.inl (Ratios_occ_le hN (Ratios_inM h) 0)
    rcases h2 with h2 | h2
    · have := mul_le_mul h2 h2 (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right this (hs0 β)
    · simp [h2]
  set WB : Idx × Occ → ℝ := fun j => 4 * rhoN N / LN N ^ 3 * (A j.1 * ((j.2 j.1 : ℝ) * ψ j.2))
    with hWB
  have hc : 0 ≤ 4 * rhoN N / LN N ^ 3 := by positivity
  have hoccψ : ∀ (n : Idx) (β : Occ), 0 ≤ (β n : ℝ) * ψ β :=
    fun n β => mul_nonneg (Nat.cast_nonneg _) (hs0 β)
  have hWB0 : ∀ j, 0 ≤ WB j := fun j => mul_nonneg hc (mul_nonneg (hA0 _) (hoccψ _ _))
  have hAψ : Summable fun j : Idx × Occ => A j.1 * ψ j.2 :=
    hAs.mul_of_nonneg hs (fun v => hA0 v) (fun β => hs0 β)
  have hWB1 : Summable fun j : Idx × Occ => A j.1 * ((j.2 j.1 : ℝ) * ψ j.2) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hA0 _) (hoccψ _ _))
      (fun j => (mul_le_mul_of_nonneg_left (hocc j.1 j.2) (hA0 _)).trans_eq
        (mul_left_comm _ _ _)) (hAψ.mul_left (N : ℝ))
  have hWBs : Summable WB := hWB1.mul_left _
  rw [Ratios_tsum_Qm_succ V w kc hN u]
  have hsplit := Ratios_split hs hs0 (fun α => 1 ≤ α u) (Ratios_caseA (rhoN N) (LN N) kc N u)
  beta_reduce at hsplit
  rw [hsplit]
  have hWA0 : ∀ β, 0 ≤ WA β := fun β => by simp only [hWA]; positivity
  have hcA := Ratios_PH_caseA V w kc hN hu (fun k => 1 ≤ k) (fun _ => True)
    (fun _ _ => trivial) WA hWA0 hWAs
    (fun β hβ h2 _ => by
      simp only [hWA]
      have h1' : (1 : ℝ) ≤ β 0 := by exact_mod_cast (show 1 ≤ β 0 by omega)
      have hb : ((β 0 : ℝ) - 1) / LN N ^ 3 ≤ (β 0 : ℝ) / LN N ^ 3 :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      have hb0 : 0 ≤ ((β 0 : ℝ) - 1) / LN N ^ 3 := div_nonneg (by linarith) (by positivity)
      have hab : (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) ≤
          (β 0 : ℝ) * (β 0 : ℝ) / (LN N ^ 3) ^ 2 := by
        calc (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3)
            ≤ (β 0 : ℝ) / LN N ^ 3 * ((β 0 : ℝ) / LN N ^ 3) :=
              mul_le_mul_of_nonneg_left hb (by positivity)
          _ = (β 0 : ℝ) * (β 0 : ℝ) / (LN N ^ 3) ^ 2 := by ring
      calc (β 0 : ℝ) / LN N ^ 3 * (((β 0 : ℝ) - 1) / LN N ^ 3) *
            lam V w (rhoN N) (LN N) u ^ 2 * ψ β
          ≤ (β 0 : ℝ) * (β 0 : ℝ) / (LN N ^ 3) ^ 2 * lam V w (rhoN N) (LN N) u ^ 2 * ψ β := by
            gcongr
        _ = _ := by ring)
  have hWB'0 : ∀ j : Occ × Idx, 0 ≤ WB (j.2, j.1) := fun j => hWB0 _
  have hWB's : Summable fun j : Occ × Idx => WB (j.2, j.1) :=
    (Equiv.prodComm Occ Idx).summable_iff.2 hWBs
  have hcB := Ratios_PH_caseB V w kc hN hu (fun k => 1 ≤ k) (by simp)
    (fun j => WB (j.2, j.1)) hWB'0 hWB's
    (fun v β hv hβS hcu hcvu _ => by
      change _ ≤ WB (v, β)
      simp only [hWB, hA]
      rw [ite_eq_left (And.intro hv hcvu)]
      have := Ratios_soft_le (Y := (β v : ℝ)) hL (by positivity) (Ratios_occ_div_le hN hβS.1 0)
        (by positivity) le_rfl (abs_nonneg (lam V w (rhoN N) (LN N) u *
          lam V w (rhoN N) (LN N) (v - u))) (hs0 β)
      refine this.trans_eq ?_
      ring)
  have hswap : (∑' j : Occ × Idx, WB (j.2, j.1)) = ∑' j, WB j :=
    (Equiv.prodComm Occ Idx).tsum_eq WB
  rw [hswap] at hcB
  have hWBsum : (∑' j, WB j) = 4 * rhoN N / LN N ^ 3 *
      (∑' v : Idx, (if inPL (rhoN N) (LN N) v ∧ inPHc (rhoN N) (LN N) kc (v - u) then
        Expect.Q (trialState V w kc N) [v] *
          |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (v - u)| else 0)) := by
    rw [hWBs.tsum_prod' (fun v => hWBs.prod_factor v), ← tsum_mul_left]
    congr 1
    funext v
    simp only [hWB]
    rw [tsum_mul_left, tsum_mul_left, ← hQ1]
    simp only [hA]
    split_ifs <;> ring
  have hWAsum : (∑' β, WA β) = lam V w (rhoN N) (LN N) u ^ 2 / (LN N ^ 3) ^ 2 *
      Expect.Q (trialState V w kc N) [0, 0] := by
    simp only [hWA]
    rw [tsum_mul_left, hQ2]
  rw [hWBsum] at hcB
  rw [hWAsum] at hcA
  exact add_le_add hcA hcB

end LHYUpper
