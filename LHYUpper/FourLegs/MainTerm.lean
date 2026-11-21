module

public import LHYUpper.Assembly.Section4
public import LHYUpper.Particles.UpperL
public import LHYUpper.Riemann.Bridge
public import LHYUpper.Scattering.Identities
public import LHYUpper.FourLegs.Defs
public import LHYUpper.FourLegs.Classes
public import LHYUpper.FourLegs.HighLegs
public import LHYUpper.Particles.Lower
public import LHYUpper.Particles.Lemma55
public import LHYUpper.OneLeg.Sums

@[expose] public section

/-!
# The main term of the four nonzero legs: (10.20) [temp8.150] and Lemma 10.2 [101]

The inner sum (10.11) [temp8.140] of (10.10) [resultinMk1k2] compared with
`4 λ_{k₁} λ_{k₃} |Λ|^{-2} Q_Ψ(0, v)`, (10.20) [temp8.150], with the bounds (10.14) [temp8.144] and
(10.16) [temp8.146] and the difference of `λ` on `P_H`; the sum over the legs with the Riemann
sum of `V_{k₁-k₃} w_{k₁} w_{k₃}` over the fuzzy shell `A_v` (Lemma 10.2 [101] with a rate); and
(10.10) [resultinMk1k2] as a double lim sup, with (8.29) [sum0PL].
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Scaling facts at `ρ = ρ_N`, `ε = ρ^{1/200}` -/

private lemma MT_tendsto_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := 8 / 17 * a) (by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp, rhoN]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  ring_nf

private lemma MT_tendsto_rho : Tendsto rhoN atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using MT_tendsto_rpow (a := 1) one_pos
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (Particles_rhoN_LN hN).2.1

/-- `ε ≤ δ` for all large `N`. -/
private lemma MT_ev_eps {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ N : ℕ in atTop, epsP (rhoN N) ≤ δ :=
  ((MT_tendsto_rpow (a := 1 / 200) (by norm_num)).eventually_lt_const hδ).mono
    fun _ h => h.le

/-- `ρ^x = ε^k` for `x = k/200`. -/
private lemma MT_rpow_eps {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {x : ℝ} (hx : x = (k : ℝ) / 200) :
    ρ ^ x = epsP ρ ^ k := by
  rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ, hx]
  ring_nf

/-- `ρ = ε^{200}`. -/
private lemma MT_rho_eps {ρ : ℝ} (hρ : 0 ≤ ρ) : ρ = epsP ρ ^ 200 := by
  rw [← MT_rpow_eps hρ 200 (x := 1) (by norm_num), Real.rpow_one]

/-- `m_c = ε⁻¹`, (3.8) [defmc]. -/
private lemma MT_mc {ρ : ℝ} (hρ : 0 ≤ ρ) : mc ρ = (epsP ρ)⁻¹ := by
  rw [mc, Real.rpow_neg hρ, MT_rpow_eps hρ 1 (by norm_num), pow_one]

private lemma MT_eps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < epsP ρ := by
  unfold epsP; positivity

private lemma MT_mom_sub (L : ℝ) (n m : Idx) : mom L (n - m) = mom L n - mom L m := by
  ext i; simp [mom, mul_sub]

/-- `Q_Ψ(u₁, …, u_s) ≥ 0`. -/
private lemma MT_Q_nonneg (Ψ : Occ → ℂ) (us : List Idx) : 0 ≤ Expect.Q Ψ us :=
  tsum_nonneg fun α => mul_nonneg (List.prod_nonneg (by simp)) (by positivity)

/-! ### The square root of Definition 3.6 -/

/-- `‖√x‖ = √|x|`. -/
private lemma MT_norm_csqrt (x : ℝ) : ‖csqrt x‖ = Real.sqrt |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg h]
  · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_neg (not_le.1 h)]

/-- `‖√a √b‖ ≤ Λ` when `|a|, |b| ≤ Λ`. -/
private lemma MT_norm_csqrt_mul_le {a b Λ : ℝ} (ha : |a| ≤ Λ) (hb : |b| ≤ Λ) :
    ‖csqrt a * csqrt b‖ ≤ Λ := by
  have hΛ : 0 ≤ Λ := (abs_nonneg a).trans ha
  rw [norm_mul, MT_norm_csqrt, MT_norm_csqrt, ← Real.sqrt_mul (abs_nonneg a)]
  calc Real.sqrt (|a| * |b|) ≤ Real.sqrt (Λ * Λ) :=
        Real.sqrt_le_sqrt (mul_le_mul ha hb (abs_nonneg _) hΛ)
    _ = Λ := Real.sqrt_mul_self hΛ

/-- `|√a √b - a| ≤ 2|a - b|` for real `a, b`, in the four sign cases of Definition 3.6. -/
private lemma MT_csqrt_mul_sub_le (a b : ℝ) : ‖csqrt a * csqrt b - a‖ ≤ 2 * |a - b| := by
  have key : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |s * t - s ^ 2| ≤ |s ^ 2 - t ^ 2| := by
    intro s t hs ht
    have e1 : s * t - s ^ 2 = s * (t - s) := by ring
    have e2 : s ^ 2 - t ^ 2 = (s + t) * (s - t) := by ring
    rw [e1, e2, abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg (by linarith : 0 ≤ s + t),
      abs_sub_comm t s]
    exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
  have hxy : ∀ x y : ℝ, ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ |x| + |y| := by
    intro x y
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  unfold csqrt
  split_ifs with ha hb hb
  · have := key (Real.sqrt a) (Real.sqrt b) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt ha, Real.sq_sqrt hb] at this
    rw [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    linarith [abs_nonneg (a - b)]
  · have hb' : b < 0 := not_le.1 hb
    have e : (Real.sqrt a : ℂ) * ((Real.sqrt (-b) : ℂ) * Complex.I) - (a : ℂ) =
        ((-a : ℝ) : ℂ) + ((Real.sqrt a * Real.sqrt (-b) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e]
    refine (hxy _ _).trans ?_
    have hst : Real.sqrt a * Real.sqrt (-b) ≤ (a + -b) / 2 := by
      have := sq_nonneg (Real.sqrt a - Real.sqrt (-b))
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt (by linarith : 0 ≤ -b)]
    rw [abs_neg, abs_of_nonneg ha, abs_of_nonneg (by positivity),
      abs_of_pos (by linarith : 0 < a - b)]
    linarith
  · have ha' : a < 0 := not_le.1 ha
    have e : (Real.sqrt (-a) : ℂ) * Complex.I * (Real.sqrt b : ℂ) - (a : ℂ) =
        ((-a : ℝ) : ℂ) + ((Real.sqrt (-a) * Real.sqrt b : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [e]
    refine (hxy _ _).trans ?_
    have hst : Real.sqrt (-a) * Real.sqrt b ≤ (-a + b) / 2 := by
      have := sq_nonneg (Real.sqrt (-a) - Real.sqrt b)
      nlinarith [Real.sq_sqrt hb, Real.sq_sqrt (by linarith : 0 ≤ -a)]
    rw [abs_of_pos (by linarith : 0 < -a), abs_of_nonneg (by positivity), abs_sub_comm,
      abs_of_pos (by linarith : 0 < b - a)]
    linarith
  · have ha' : a < 0 := not_le.1 ha
    have hb' : b < 0 := not_le.1 hb
    have := key (Real.sqrt (-a)) (Real.sqrt (-b)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)] at this
    have e : (Real.sqrt (-a) : ℂ) * Complex.I * ((Real.sqrt (-b) : ℂ) * Complex.I) - (a : ℂ) =
        ((-(Real.sqrt (-a) * Real.sqrt (-b) - -a)) : ℝ) := by
      push_cast
      linear_combination ((Real.sqrt (-a) : ℂ) * (Real.sqrt (-b) : ℂ)) * Complex.I_mul_I
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_neg]
    have h2 : |-a - -b| = |a - b| := by rw [show -a - -b = -(a - b) by ring, abs_neg]
    linarith [abs_nonneg (a - b)]

/-! ### (10.14) [temp8.144] and (10.16) [temp8.146] -/

/-- `Ψ` vanishes off `M`. -/
private lemma MT_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hM
  exact h (by simp [trialState, hM])

/-- A single occupation number of an `N`-particle state is at most `N`. -/
private lemma MT_occ_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) {α : Occ} (h : Ψ α ≠ 0)
    (u : Idx) : (α u : ℝ) ≤ N := by
  have h2 : α u ≤ α.num := by
    by_cases hu : u ∈ α.support
    · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hu
    · rw [Finsupp.notMem_support_iff.mp hu]; exact Nat.zero_le _
  rw [hΨ.2 α h] at h2
  exact_mod_cast h2

/-- `1 ≤ √∏(x_i+1) ≤ 1 + Σ x_i + x₁x₂ + x₃x₄` for `x_i ≥ 0`, a form of (10.13)
[inequalityx1234]. -/
private lemma MT_sqrt_prod {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    1 ≤ Real.sqrt ((a + 1) * (b + 1) * (c + 1) * (d + 1)) ∧
      Real.sqrt ((a + 1) * (b + 1) * (c + 1) * (d + 1)) ≤
        1 + (a + b + c + d + (a * b + c * d)) := by
  set A := (a + 1) * (b + 1) with hA
  set B := (c + 1) * (d + 1) with hB
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith [mul_nonneg ha hb]
  have hB1 : 1 ≤ B := by rw [hB]; nlinarith [mul_nonneg hc hd]
  have e : (a + 1) * (b + 1) * (c + 1) * (d + 1) = A * B := by rw [hA, hB]; ring
  have e2 : 1 + (a + b + c + d + (a * b + c * d)) = A + B - 1 := by rw [hA, hB]; ring
  rw [e, e2]
  constructor
  · calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt (by nlinarith)
  · calc Real.sqrt (A * B) ≤ Real.sqrt ((A + B - 1) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (sub_nonneg.2 hA1) (sub_nonneg.2 hB1)])
      _ = A + B - 1 := Real.sqrt_sq (by linarith)

/-- The comparison behind (10.14) [temp8.144] and (10.16) [temp8.146]: the sum of (10.11)
[temp8.140] differs from `Q_Ψ(0, v)` by at most `N(m_c+1)` times
`Σ_{M_v^a}|Ψ|² + Σ_i Q_Ψ(k_i) + Q_Ψ(k₁,k₂) + Q_Ψ(k₃,k₄)`. -/
private lemma MT_X_sub_Q (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {v k₁ k₂ k₃ k₄ : Idx}
    (hv : inPL (rhoN N) (LN N) v) :
    |(∑' α : Occ, if InMuS (rhoN N) (LN N) kc N v α then
        (α 0 : ℝ) * (α v : ℝ) *
          Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) *
            ((α k₄ : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 2 else 0) -
        Expect.Q (trialState V w kc N) [0, v]| ≤
      N * (mc (rhoN N) + 1) *
        ((∑' α : Occ, if InMuA (rhoN N) (LN N) kc N v α then
            ‖trialState V w kc N α‖ ^ 2 else 0) +
          (Expect.Q (trialState V w kc N) [k₁] + Expect.Q (trialState V w kc N) [k₂] +
            Expect.Q (trialState V w kc N) [k₃] + Expect.Q (trialState V w kc N) [k₄] +
            (Expect.Q (trialState V w kc N) [k₁, k₂] +
              Expect.Q (trialState V w kc N) [k₃, k₄]))) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  set Ψ := trialState V w kc N with hΨdef
  set c₀ : ℝ := N * (mc (rhoN N) + 1) with hc₀
  have hmc : 0 ≤ mc (rhoN N) := by unfold mc; positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hc₀0 : 0 ≤ c₀ := by positivity
  have hsq : Summable fun α => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have summ : ∀ (f : Occ → ℝ) (K : ℝ), (∀ α, Ψ α ≠ 0 → |f α| ≤ K * ‖Ψ α‖ ^ 2) →
      (∀ α, Ψ α = 0 → f α = 0) → Summable f := by
    intro f K hf h0
    refine Summable.of_norm_bounded (hsq.mul_left K) (fun α => ?_)
    by_cases h : Ψ α = 0
    · simp [h0 α h, h]
    · rw [Real.norm_eq_abs]; exact hf α h
  set fX : Occ → ℝ := fun α => if InMuS (rhoN N) (LN N) kc N v α then
        (α 0 : ℝ) * (α v : ℝ) *
          Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) *
            ((α k₄ : ℝ) + 1)) * ‖Ψ α‖ ^ 2 else 0 with hfX
  set fQ : Occ → ℝ := fun α => (α 0 : ℝ) * (α v : ℝ) * ‖Ψ α‖ ^ 2 with hfQ
  set fA : Occ → ℝ := fun α => if InMuA (rhoN N) (LN N) kc N v α then ‖Ψ α‖ ^ 2 else 0
    with hfA
  set f1 : Idx → Occ → ℝ := fun u α => (α u : ℝ) * ‖Ψ α‖ ^ 2 with hf1
  set f2 : Idx → Idx → Occ → ℝ := fun u u' α => (α u : ℝ) * (α u' : ℝ) * ‖Ψ α‖ ^ 2 with hf2
  have hQ : Expect.Q Ψ [0, v] = ∑' α, fQ α := by simp [Expect.Q, hfQ]
  have hQ1 : ∀ u, Expect.Q Ψ [u] = ∑' α, f1 u α := by intro u; simp [Expect.Q, hf1]
  have hQ2 : ∀ u u', Expect.Q Ψ [u, u'] = ∑' α, f2 u u' α := by
    intro u u'; simp [Expect.Q, hf2]
  have hb : ∀ α, Ψ α ≠ 0 → ∀ u, (α u : ℝ) ≤ N := fun α h => MT_occ_le hΨ h
  have sQ : Summable fQ := summ fQ ((N : ℝ) * N) (fun α h => by
      simp only [hfQ]
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hb α h 0) (hb α h v) (Nat.cast_nonneg _) hN0)
        (sq_nonneg _))
    (fun α h => by simp [hfQ, h])
  have sA : Summable fA := summ fA 1 (fun α h => by
      simp only [hfA]
      split_ifs <;> simp)
    (fun α h => by simp [hfA, h])
  have s1 : ∀ u, Summable (f1 u) := fun u => summ (f1 u) N (fun α h => by
      simp only [hf1]
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hb α h u) (sq_nonneg _))
    (fun α h => by simp [hf1, h])
  have s2 : ∀ u u', Summable (f2 u u') := fun u u' => summ (f2 u u') ((N : ℝ) * N)
    (fun α h => by
      simp only [hf2]
      rw [abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hb α h u) (hb α h u') (Nat.cast_nonneg _) hN0)
        (sq_nonneg _))
    (fun α h => by simp [hf2, h])
  set D : Occ → ℝ := fun α => c₀ * (fA α + (f1 k₁ α + f1 k₂ α + f1 k₃ α + f1 k₄ α +
      (f2 k₁ k₂ α + f2 k₃ k₄ α))) with hD
  have hDs : HasSum D (c₀ * ((∑' α, fA α) + ((∑' α, f1 k₁ α) + (∑' α, f1 k₂ α) +
      (∑' α, f1 k₃ α) + (∑' α, f1 k₄ α) + ((∑' α, f2 k₁ k₂ α) + (∑' α, f2 k₃ k₄ α))))) :=
    (sA.hasSum.add (((((s1 k₁).hasSum.add (s1 k₂).hasSum).add (s1 k₃).hasSum).add
      (s1 k₄).hasSum).add ((s2 k₁ k₂).hasSum.add (s2 k₃ k₄).hasSum))).mul_left c₀
  have pt : ∀ α, |fX α - fQ α| ≤ D α := by
    intro α
    have hn := sq_nonneg ‖Ψ α‖
    by_cases h0 : Ψ α = 0
    · simp [hfX, hfQ, hD, hfA, hf1, hf2, h0]
    have hM : InM (rhoN N) (LN N) kc N α := MT_inM h0
    have hαv : (α v : ℝ) ≤ mc (rhoN N) + 1 := by
      have h1 := MStar_PL_mc hρ hM hv
      have h2 : ((α v : ℕ) : ℝ) ≤ ((alphaStar α v : ℕ) : ℝ) := by
        exact_mod_cast le_max_left _ _
      linarith
    have hP : (α 0 : ℝ) * α v ≤ c₀ := mul_le_mul (hb α h0 0) hαv (Nat.cast_nonneg _) hN0
    set E : ℝ := (α k₁ : ℝ) + α k₂ + α k₃ + α k₄ + ((α k₁ : ℝ) * α k₂ + (α k₃ : ℝ) * α k₄)
      with hE
    have hE0 : 0 ≤ E := by positivity
    have hDe : D α = c₀ * (fA α + E * ‖Ψ α‖ ^ 2) := by
      simp only [hD, hf1, hf2, hE]; ring
    rw [hDe]
    by_cases hs : α v = α (-v)
    · have hS : InMuS (rhoN N) (LN N) kc N v α := ⟨hM, hs⟩
      have hA : ¬ InMuA (rhoN N) (LN N) kc N v α := fun h => h.2 hs
      obtain ⟨hq1, hq2⟩ := MT_sqrt_prod (Nat.cast_nonneg (α k₁)) (Nat.cast_nonneg (α k₂))
        (Nat.cast_nonneg (α k₃)) (Nat.cast_nonneg (α k₄))
      set s := Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) *
        ((α k₄ : ℝ) + 1)) with hsdef
      have e : fX α - fQ α = (α 0 : ℝ) * α v * (s - 1) * ‖Ψ α‖ ^ 2 := by
        simp only [hfX, hfQ, ite_eq_left hS]; ring
      have eA : fA α = 0 := by simp only [hfA, ite_eq_right hA]
      have hs1 : 0 ≤ s - 1 := by linarith
      rw [e, eA, zero_add, abs_of_nonneg (by positivity)]
      calc (α 0 : ℝ) * α v * (s - 1) * ‖Ψ α‖ ^ 2 ≤ c₀ * E * ‖Ψ α‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul hP (by linarith) hs1 hc₀0) hn
        _ = c₀ * (E * ‖Ψ α‖ ^ 2) := by ring
    · have hA : InMuA (rhoN N) (LN N) kc N v α := ⟨hM, hs⟩
      have hS : ¬ InMuS (rhoN N) (LN N) kc N v α := fun h => hs h.2
      have e : fX α - fQ α = -((α 0 : ℝ) * α v * ‖Ψ α‖ ^ 2) := by
        simp only [hfX, hfQ, ite_eq_right hS]; ring
      have eA : fA α = ‖Ψ α‖ ^ 2 := by simp only [hfA, ite_eq_left hA]
      rw [e, eA, abs_neg, abs_of_nonneg (by positivity)]
      calc (α 0 : ℝ) * α v * ‖Ψ α‖ ^ 2 ≤ c₀ * ‖Ψ α‖ ^ 2 := mul_le_mul_of_nonneg_right hP hn
        _ ≤ c₀ * (‖Ψ α‖ ^ 2 + E * ‖Ψ α‖ ^ 2) := by
          nlinarith [mul_nonneg hc₀0 (mul_nonneg hE0 hn)]
  have sdiff : Summable fun α => fX α - fQ α :=
    Summable.of_norm_bounded hDs.summable (fun α => by rw [Real.norm_eq_abs]; exact pt α)
  have sX : Summable fX := by
    have := sdiff.add sQ
    simpa using this
  rw [hQ, hQ1, hQ1, hQ1, hQ1, hQ2, hQ2, ← sX.tsum_sub sQ]
  rw [abs_le]
  constructor
  · have := hasSum_le (fun α => (abs_le.1 (pt α)).1) hDs.neg sdiff.hasSum
    linarith
  · exact hasSum_le (fun α => (abs_le.1 (pt α)).2) sdiff.hasSum hDs

/-- The four legs of `Gen` as the six pairwise relations. -/
private lemma MT_gen {k₁ k₂ k₃ k₄ : Idx} (hg : FourLegs.Gen ![k₁, k₂, k₃, k₄]) :
    k₁ ≠ k₂ ∧ k₁ ≠ -k₂ ∧ k₁ ≠ k₃ ∧ k₁ ≠ -k₃ ∧ k₁ ≠ k₄ ∧ k₁ ≠ -k₄ ∧ k₂ ≠ k₃ ∧ k₂ ≠ -k₃ ∧
      k₂ ≠ k₄ ∧ k₂ ≠ -k₄ ∧ k₃ ≠ k₄ ∧ k₃ ≠ -k₄ := by
  have g01 := hg 0 1 (by decide)
  have g02 := hg 0 2 (by decide)
  have g03 := hg 0 3 (by decide)
  have g12 := hg 1 2 (by decide)
  have g13 := hg 1 3 (by decide)
  have g23 := hg 2 3 (by decide)
  simp only [Legs_pm, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val, Matrix.tail_cons] at g01 g02 g03 g12 g13 g23
  exact ⟨g01.1, g01.2, g02.1, g02.2, g03.1, g03.2, g12.1, g12.2, g13.1, g13.2, g23.1, g23.2⟩

/-- (10.20) [temp8.150] with the bounds (10.14) [temp8.144], (10.16) [temp8.146] and the
difference bound of `λ` on `P_H`: `|(10.11) - 4 λ_{k₁} λ_{k₃} |Λ|^{-2} Q_Ψ(0, v)| ≤
C ρ^{19/10} |Λ|⁻¹ + C ρ^{2/5} |Λ|^{-2} Q_Ψ(0, v)`, uniformly in `k_c`. -/
theorem Eq10_20 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ k₁ k₂ k₃ k₄ : Idx,
      inPHc (rhoN N) (LN N) kc k₁ → inPHc (rhoN N) (LN N) kc k₂ →
      inPHc (rhoN N) (LN N) kc k₃ → inPHc (rhoN N) (LN N) kc k₄ →
      FourLegs.Gen ![k₁, k₂, k₃, k₄] → k₁ + k₂ = k₃ + k₄ → inPL (rhoN N) (LN N) (k₁ + k₂) →
      ‖FourLegs.mainTuple V w kc N k₁ k₂ k₃ k₄ -
          ((4 * lam V w (rhoN N) (LN N) k₁ * lam V w (rhoN N) (LN N) k₃ / (LN N ^ 3) ^ 2 *
            Expect.Q (trialState V w kc N) [0, k₁ + k₂] : ℝ) : ℂ)‖ ≤
        C * rhoN N ^ (19/10 : ℝ) / LN N ^ 3 +
          C * rhoN N ^ (2/5 : ℝ) / (LN N ^ 3) ^ 2 * Expect.Q (trialState V w kc N) [0, k₁ + k₂] := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C23, hC23, N23, h23⟩ := Eq5_23 V w
  obtain ⟨C4, hC4, N4, h4⟩ := Lemma5_4_PH V w
  obtain ⟨C42, hC42, N42, h42⟩ := Eq5_42 V w
  obtain ⟨Cs, hCs⟩ := scat_lam_sub_le hV hw
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((((MT_tendsto_rho.eventually hCs).and
    (MT_ev_eps (δ := 1 / 2) (by norm_num))).and (eventually_ge_atTop 1)).and
    ((eventually_ge_atTop N23).and ((eventually_ge_atTop N4).and (eventually_ge_atTop N42))))
  set g := g0 V w with hgdef
  set C₁ := 8 * g ^ 2 * (C23 + 4 * C4 * g + 2 * C42 * g ^ 2) with hC₁
  set C₂ := 16 * g * |Cs| with hC₂
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hC₂0 : 0 ≤ C₂ := by positivity
  refine ⟨C₁ + C₂, by positivity, N₀, ?_⟩
  intro N hN kc k₁ k₂ k₃ k₄ hk₁ hk₂ hk₃ hk₄ hgen hs hv
  obtain ⟨⟨⟨hsub, hε2⟩, hN1⟩, hN23, hN4, hN42⟩ := hN₀ N hN
  have hρ := (Particles_rhoN_LN hN1).2.1
  have hL := (Particles_rhoN_LN hN1).2.2.2
  have hNL := (Particles_rhoN_LN hN1).1
  rw [Eq10_11 V w kc hN1 ⟨hk₁, hk₂, hk₃, hk₄⟩ hgen hs hv]
  have hXQ := MT_X_sub_Q V w kc hN1 (k₁ := k₁) (k₂ := k₂) (k₃ := k₃) (k₄ := k₄) hv
  have hA := h23 N hN23 kc (k₁ + k₂) hv
  have hQk := fun n hn => h4 N hN4 kc n hn
  have hQ12 := h42 N hN42 kc
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set ε := epsP ρ with hεdef
  set Ψ := trialState V w kc N with hΨdef
  set v := k₁ + k₂ with hvdef
  have hε0 : 0 < ε := MT_eps_pos hρ
  have hε1 : ε ≤ 1 := by linarith
  have hρε : ρ = ε ^ 200 := MT_rho_eps hρ.le
  have hmc : mc ρ = ε⁻¹ := MT_mc hρ.le
  have hL3 : 0 < L ^ 3 := by positivity
  obtain ⟨h12, -, -, -, -, -, -, -, -, -, h34, -⟩ := MT_gen hgen
  have hv0 : v ≠ 0 := Regions_PL_ne_zero hρ hv
  have hp : ∀ n : Idx, inPHc ρ L kc n → epsP ρ < ‖mom L n‖ := fun n hn => hn.1
  have hlam : ∀ n : Idx, inPHc ρ L kc n → |lam V w ρ L n| ≤ g / ε ^ 2 :=
    fun n hn => scat_lam_PH hV hw ρ hρ L n hn.1
  -- `‖p_v‖ ≤ ε^{99} ≤ ε/2`
  have hmv : ‖mom L v‖ ≤ ε ^ 99 := by
    have h2 : ‖mom L v‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := hv.2
    rw [MT_rpow_eps hρ.le 100 (by norm_num)] at h2
    change ‖mom L v‖ ≤ ε⁻¹ * ε ^ 100 at h2
    refine h2.trans (le_of_eq ?_)
    field_simp
  have hmv2 : ‖mom L v‖ ≤ ε / 2 := by
    refine hmv.trans ?_
    have : ε ^ 98 ≤ ε ^ 1 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
    calc ε ^ 99 = ε * ε ^ 98 := by ring
      _ ≤ ε * (1 / 2) :=
          mul_le_mul_of_nonneg_left (by rw [pow_one] at this; exact this.trans hε2) hε0.le
      _ = ε / 2 := by ring
  have hlsub : ∀ n m : Idx, inPHc ρ L kc n → inPHc ρ L kc m → n + m = v →
      |lam V w ρ L n - lam V w ρ L m| ≤ |Cs| * ε ^ 96 := by
    intro n m hn hm hnm
    have := hsub L n m (hp n hn).le (hp m hm).le (by rw [hnm]; exact hmv2)
    rw [hnm] at this
    refine this.trans ?_
    calc Cs / ε ^ 3 * ‖mom L v‖ ≤ |Cs| / ε ^ 3 * ε ^ 99 :=
          mul_le_mul (div_le_div_of_nonneg_right (le_abs_self Cs) (by positivity)) hmv
            (norm_nonneg _) (by positivity)
      _ = |Cs| * ε ^ 96 := by field_simp
  set a := lam V w ρ L k₁ with ha
  set b := lam V w ρ L k₂ with hb
  set c := lam V w ρ L k₃ with hc
  set d := lam V w ρ L k₄ with hd
  set Λ := g / ε ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  have hab : |a - b| ≤ |Cs| * ε ^ 96 := hlsub k₁ k₂ hk₁ hk₂ rfl
  have hcd : |c - d| ≤ |Cs| * ε ^ 96 := hlsub k₃ k₄ hk₃ hk₄ hs.symm
  set X : ℝ := ∑' α : Occ, if InMuS ρ L kc N v α then
            (α 0 : ℝ) * (α v : ℝ) *
              Real.sqrt (((α k₁ : ℝ) + 1) * ((α k₂ : ℝ) + 1) * ((α k₃ : ℝ) + 1) *
                ((α k₄ : ℝ) + 1)) * ‖Ψ α‖ ^ 2 else 0 with hX
  set Q := Expect.Q Ψ [0, v] with hQ
  have hQ0 : 0 ≤ Q := MT_Q_nonneg _ _
  set s₁₂ := csqrt a * csqrt b with hs₁₂
  set s₃₄ := csqrt c * csqrt d with hs₃₄
  have hn12 : ‖s₁₂‖ ≤ Λ := MT_norm_csqrt_mul_le (hlam k₁ hk₁) (hlam k₂ hk₂)
  have hn34 : ‖s₃₄‖ ≤ Λ := MT_norm_csqrt_mul_le (hlam k₃ hk₃) (hlam k₄ hk₄)
  have e : 4 * conj s₁₂ * s₃₄ / (((L ^ 3) ^ 2 : ℝ) : ℂ) * (X : ℂ) -
      ((4 * a * c / (L ^ 3) ^ 2 * Q : ℝ) : ℂ) =
      4 * conj s₁₂ * s₃₄ / (((L ^ 3) ^ 2 : ℝ) : ℂ) * ((X - Q : ℝ) : ℂ) +
        (4 / (((L ^ 3) ^ 2 : ℝ) : ℂ)) * (conj s₁₂ * (s₃₄ - c) + (c : ℂ) * (conj s₁₂ - a)) *
          (Q : ℂ) := by
    push_cast; ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  -- first term: (10.14) [temp8.144] and (10.16) [temp8.146]
  have hT1 : ‖4 * conj s₁₂ * s₃₄ / (((L ^ 3) ^ 2 : ℝ) : ℂ) * ((X - Q : ℝ) : ℂ)‖ ≤
      C₁ * ρ ^ (19/10 : ℝ) / L ^ 3 := by
    have hn : ‖4 * conj s₁₂ * s₃₄ / (((L ^ 3) ^ 2 : ℝ) : ℂ) * ((X - Q : ℝ) : ℂ)‖ =
        4 * ‖s₁₂‖ * ‖s₃₄‖ / (L ^ 3) ^ 2 * |X - Q| := by
      rw [norm_mul, norm_div, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity)]
      norm_num
    rw [hn]
    have hk : ∀ n : Idx, inPHc ρ L kc n → Expect.Q Ψ [n] ≤ C4 * ρ ^ 2 * Λ / ε ^ 2 := by
      intro n hn
      refine (hQk n hn.1).trans ?_
      have h1 : ε ^ 2 ≤ ‖mom L n‖ ^ 2 := pow_le_pow_left₀ hε0.le (hp n hn).le 2
      exact div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left (hlam n hn) (by positivity)) (by positivity) h1
    have hpair : ∀ n m : Idx, inPHc ρ L kc n → inPHc ρ L kc m → n ≠ m → n + m = v →
        Expect.Q Ψ [n, m] ≤ C42 * (Λ * Λ) * ρ ^ 4 / ε ^ 4 := by
      intro n m hn hm hnm hsum
      refine (hQ12 n m hn.1 hm.1 hnm (by rw [hsum]; exact hv0)).trans ?_
      have : |lam V w ρ L n * lam V w ρ L m| ≤ Λ * Λ := by
        rw [abs_mul]; exact mul_le_mul (hlam n hn) (hlam m hm) (abs_nonneg _) hΛ0
      gcongr
    have hXQ' : |X - Q| ≤ 2 * ρ * L ^ 3 / ε *
        (C23 * ρ * ε⁻¹ / ε + (4 * (C4 * ρ ^ 2 * Λ / ε ^ 2) +
          2 * (C42 * (Λ * Λ) * ρ ^ 4 / ε ^ 4))) := by
      refine hXQ.trans ?_
      have hc0 : (N : ℝ) * (mc ρ + 1) ≤ 2 * ρ * L ^ 3 / ε := by
        rw [hmc, ← hNL]
        have : ε⁻¹ + 1 ≤ 2 / ε := by
          rw [div_eq_mul_inv]
          have : 1 ≤ ε⁻¹ := one_le_inv_iff₀.2 ⟨hε0, hε1⟩
          linarith
        calc ρ * L ^ 3 * (ε⁻¹ + 1) ≤ ρ * L ^ 3 * (2 / ε) :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = 2 * ρ * L ^ 3 / ε := by ring
      have hA' : (∑' α : Occ, if InMuA ρ L kc N v α then ‖Ψ α‖ ^ 2 else 0) ≤
          C23 * ρ * ε⁻¹ / ε := by rw [← hmc]; exact hA
      have hsumb := add_le_add hA' (add_le_add (add_le_add (add_le_add (add_le_add
        (hk k₁ hk₁) (hk k₂ hk₂)) (hk k₃ hk₃)) (hk k₄ hk₄))
        (add_le_add (hpair k₁ k₂ hk₁ hk₂ h12 rfl) (hpair k₃ k₄ hk₃ hk₄ h34 hs.symm)))
      have hS0 : 0 ≤ (∑' α : Occ, if InMuA ρ L kc N v α then ‖Ψ α‖ ^ 2 else 0) +
          (Expect.Q Ψ [k₁] + Expect.Q Ψ [k₂] + Expect.Q Ψ [k₃] + Expect.Q Ψ [k₄] +
            (Expect.Q Ψ [k₁, k₂] + Expect.Q Ψ [k₃, k₄])) := by
        have : (0 : ℝ) ≤ ∑' α : Occ, (if InMuA ρ L kc N v α then ‖Ψ α‖ ^ 2 else 0) :=
          tsum_nonneg (fun α => by split_ifs <;> positivity)
        have := MT_Q_nonneg Ψ [k₁]; have := MT_Q_nonneg Ψ [k₂]; have := MT_Q_nonneg Ψ [k₃]
        have := MT_Q_nonneg Ψ [k₄]; have := MT_Q_nonneg Ψ [k₁, k₂]
        have := MT_Q_nonneg Ψ [k₃, k₄]
        linarith
      calc (N : ℝ) * (mc ρ + 1) * ((∑' α : Occ, if InMuA ρ L kc N v α then ‖Ψ α‖ ^ 2 else 0) +
            (Expect.Q Ψ [k₁] + Expect.Q Ψ [k₂] + Expect.Q Ψ [k₃] + Expect.Q Ψ [k₄] +
              (Expect.Q Ψ [k₁, k₂] + Expect.Q Ψ [k₃, k₄])))
          ≤ 2 * ρ * L ^ 3 / ε * ((∑' α : Occ, if InMuA ρ L kc N v α then ‖Ψ α‖ ^ 2 else 0) +
            (Expect.Q Ψ [k₁] + Expect.Q Ψ [k₂] + Expect.Q Ψ [k₃] + Expect.Q Ψ [k₄] +
              (Expect.Q Ψ [k₁, k₂] + Expect.Q Ψ [k₃, k₄]))) :=
            mul_le_mul_of_nonneg_right hc0 hS0
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left (le_trans hsumb (le_of_eq (by ring))) (by positivity)
    have hfin : 4 * Λ * Λ / (L ^ 3) ^ 2 * (2 * ρ * L ^ 3 / ε *
        (C23 * ρ * ε⁻¹ / ε + (4 * (C4 * ρ ^ 2 * Λ / ε ^ 2) +
          2 * (C42 * (Λ * Λ) * ρ ^ 4 / ε ^ 4)))) =
        8 * g ^ 2 * (C23 * ε ^ 393 + 4 * C4 * g * ε ^ 591 + 2 * C42 * g ^ 2 * ε ^ 987) / L ^ 3 := by
      rw [hΛ, hρε]
      field_simp
      ring
    have hp1 : ε ^ 393 ≤ ε ^ 380 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
    have hp2 : ε ^ 591 ≤ ε ^ 380 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
    have hp3 : ε ^ 987 ≤ ε ^ 380 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
    have h19 : ρ ^ (19/10 : ℝ) = ε ^ 380 := MT_rpow_eps hρ.le 380 (by norm_num)
    calc 4 * ‖s₁₂‖ * ‖s₃₄‖ / (L ^ 3) ^ 2 * |X - Q|
        ≤ 4 * Λ * Λ / (L ^ 3) ^ 2 * (2 * ρ * L ^ 3 / ε *
          (C23 * ρ * ε⁻¹ / ε + (4 * (C4 * ρ ^ 2 * Λ / ε ^ 2) +
            2 * (C42 * (Λ * Λ) * ρ ^ 4 / ε ^ 4)))) := by
          refine mul_le_mul (div_le_div_of_nonneg_right ?_ (by positivity)) hXQ' (abs_nonneg _)
            (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hn12 (by norm_num)) hn34 (norm_nonneg _)
            (by positivity)
      _ = 8 * g ^ 2 * (C23 * ε ^ 393 + 4 * C4 * g * ε ^ 591 + 2 * C42 * g ^ 2 * ε ^ 987) /
            L ^ 3 := hfin
      _ ≤ 8 * g ^ 2 * (C23 * ε ^ 380 + 4 * C4 * g * ε ^ 380 + 2 * C42 * g ^ 2 * ε ^ 380) /
            L ^ 3 := by gcongr
      _ = C₁ * ρ ^ (19/10 : ℝ) / L ^ 3 := by rw [h19, hC₁]; ring
  -- second term: the difference of `λ` on `P_H`
  have hT2 : ‖(4 / (((L ^ 3) ^ 2 : ℝ) : ℂ)) * (conj s₁₂ * (s₃₄ - c) + (c : ℂ) * (conj s₁₂ - a)) *
      (Q : ℂ)‖ ≤ C₂ * ρ ^ (2/5 : ℝ) / (L ^ 3) ^ 2 * Q := by
    have hd1 : ‖conj s₁₂ * (s₃₄ - c)‖ ≤ Λ * (2 * (|Cs| * ε ^ 96)) := by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul hn12 ((MT_csqrt_mul_sub_le c d).trans (by linarith)) (norm_nonneg _) hΛ0
    have hd2 : ‖(c : ℂ) * (conj s₁₂ - a)‖ ≤ Λ * (2 * (|Cs| * ε ^ 96)) := by
      have e2 : conj s₁₂ - (a : ℂ) = conj (s₁₂ - a) := by simp [map_sub]
      rw [norm_mul, e2, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hlam k₃ hk₃) ((MT_csqrt_mul_sub_le a b).trans (by linarith))
        (norm_nonneg _) hΛ0
    have hn : ‖(4 / (((L ^ 3) ^ 2 : ℝ) : ℂ)) * (conj s₁₂ * (s₃₄ - c) + (c : ℂ) * (conj s₁₂ - a)) *
        (Q : ℂ)‖ = 4 / (L ^ 3) ^ 2 * ‖conj s₁₂ * (s₃₄ - c) + (c : ℂ) * (conj s₁₂ - a)‖ * Q := by
      rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_nonneg hQ0]
      norm_num
    rw [hn]
    have h25 : ρ ^ (2/5 : ℝ) = ε ^ 80 := MT_rpow_eps hρ.le 80 (by norm_num)
    have hp : ε ^ 94 ≤ ε ^ 80 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
    calc 4 / (L ^ 3) ^ 2 * ‖conj s₁₂ * (s₃₄ - c) + (c : ℂ) * (conj s₁₂ - a)‖ * Q
        ≤ 4 / (L ^ 3) ^ 2 * (Λ * (2 * (|Cs| * ε ^ 96)) + Λ * (2 * (|Cs| * ε ^ 96))) * Q := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            ((norm_add_le _ _).trans (add_le_add hd1 hd2)) (by positivity)) hQ0
      _ = 16 * g * |Cs| * ε ^ 94 / (L ^ 3) ^ 2 * Q := by
          rw [hΛ]; field_simp; ring
      _ ≤ 16 * g * |Cs| * ε ^ 80 / (L ^ 3) ^ 2 * Q := by gcongr
      _ = C₂ * ρ ^ (2/5 : ℝ) / (L ^ 3) ^ 2 * Q := by rw [h25, hC₂]
  calc _ ≤ C₁ * ρ ^ (19/10 : ℝ) / L ^ 3 + C₂ * ρ ^ (2/5 : ℝ) / (L ^ 3) ^ 2 * Q :=
        add_le_add hT1 hT2
    _ ≤ (C₁ + C₂) * ρ ^ (19/10 : ℝ) / L ^ 3 + (C₁ + C₂) * ρ ^ (2/5 : ℝ) / (L ^ 3) ^ 2 * Q := by
        gcongr
        · linarith
        · linarith

/-! ### Finite sums over the legs -/

/-- The lattice points of a ball of radius `R` lie in a box of at most `(4LR)³` points. -/
private lemma MT_count {L R : ℝ} (hL : 0 < L) (hLR : 1 ≤ L * R) :
    ∃ F : Finset Idx, (∀ n : Idx, ‖mom L n‖ ≤ R → n ∈ F) ∧ (F.card : ℝ) ≤ (4 * L * R) ^ 3 := by
  set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
  refine ⟨Finset.Icc (fun _ : Fin 3 => -B) (fun _ => B), ?_, ?_⟩
  · intro n hn
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
    rw [Finset.mem_Icc]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have := (abs_le.1 (hi i)).1
      exact_mod_cast this
    · have := (abs_le.1 (hi i)).2
      exact_mod_cast this
  · have hB1 : (B : ℝ) < L * R / (2 * π) + 1 := Int.ceil_lt_add_one _
    have hB0 : (0 : ℝ) ≤ B := by
      have : (0 : ℝ) < L * R / (2 * π) := by
        have : 0 < L * R := by linarith
        positivity
      exact_mod_cast (Int.ceil_pos.2 this).le
    rw [Pi.card_Icc]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h3 := Real.pi_gt_three
    have hq : L * R / (2 * π) ≤ L * R / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hb : (2 * (B : ℝ) + 1) ≤ 4 * L * R := by nlinarith
    have : ((B + 1 - -B).toNat : ℝ) = 2 * (B : ℝ) + 1 := by
      have : (0 : ℤ) ≤ B + 1 - -B := by
        have : (0 : ℤ) ≤ B := by exact_mod_cast hB0
        omega
      rw [← Int.cast_natCast, Int.toNat_of_nonneg this]
      push_cast; ring
    push_cast [this]
    exact pow_le_pow_left₀ (by linarith) hb 3

/-- A family on `(p, q, u, α)` supported on finitely many tuples `(p, q, u)`, with summable
fibres, sums to the sum of its fibre sums. -/
private lemma MT_tuples_eq (T : Finset (Idx × Idx × Idx)) (F : Idx × Idx × Idx × Occ → ℂ)
    (hT : ∀ i, F i ≠ 0 → (i.1, i.2.1, i.2.2.1) ∈ T)
    (hs : ∀ t ∈ T, Summable fun α : Occ => F (t.1, t.2.1, t.2.2, α)) :
    ∑' i, F i = ∑ t ∈ T, ∑' α : Occ, F (t.1, t.2.1, t.2.2, α) := by
  set Ft : Idx × Idx × Idx → Idx × Idx × Idx × Occ → ℂ := fun t i =>
    if (i.1, i.2.1, i.2.2.1) = t then F i else 0 with hFt
  have hinj : ∀ t : Idx × Idx × Idx, Function.Injective fun α : Occ => (t.1, t.2.1, t.2.2, α) := by
    intro t a b h
    simpa using h
  have hsupp : ∀ t : Idx × Idx × Idx,
      Function.support (Ft t) ⊆ Set.range fun α : Occ => (t.1, t.2.1, t.2.2, α) := by
    intro t i hi
    simp only [Function.mem_support, hFt] at hi
    by_cases h : (i.1, i.2.1, i.2.2.1) = t
    · obtain ⟨p, q, u, α⟩ := i
      obtain ⟨p', q', u'⟩ := t
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨α, rfl⟩
    · exact absurd (by simp [h]) hi
  have hFts : ∀ t ∈ T, Summable (Ft t) := by
    intro t ht
    rw [← (hinj t).summable_iff (fun i hi => by
      by_contra hc
      exact hi (hsupp t hc))]
    simpa [Function.comp_def, hFt] using hs t ht
  have hFt_tsum : ∀ t ∈ T, ∑' i, Ft t i = ∑' α : Occ, F (t.1, t.2.1, t.2.2, α) := by
    intro t _
    rw [← (hinj t).tsum_eq (hsupp t)]
    simp [hFt]
  have hsum : ∀ i, F i = ∑ t ∈ T, Ft t i := by
    intro i
    by_cases h : F i = 0
    · simp [h, hFt]
    · have := hT i h
      simp only [hFt]
      rw [Finset.sum_ite_eq T]
      simp [this]
  calc ∑' i, F i = ∑' i, ∑ t ∈ T, Ft t i := tsum_congr hsum
    _ = ∑ t ∈ T, ∑' i, Ft t i := Summable.tsum_finsetSum hFts
    _ = _ := Finset.sum_congr rfl hFt_tsum

/-- The terms of the class `fourMain` at one tuple `(p, q, u)` sum to `|Λ|⁻¹ V_u` times the
inner sum of (10.10) [resultinMk1k2]. -/
private lemma MT_fiber (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {p q u : Idx}
    (hl : ∀ j, inPHc (rhoN N) (LN N) kc (FourLegs.legs p q u j))
    (hg : FourLegs.Gen (FourLegs.legs p q u)) (hv : inPL (rhoN N) (LN N) (p + q)) :
    Summable (fun α : Occ => if (FourLegs.Cls.fourMain).mem (rhoN N) (LN N) kc N (p, q, u, α)
        then Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α) else 0) ∧
    ∑' α : Occ, (if (FourLegs.Cls.fourMain).mem (rhoN N) (LN N) kc N (p, q, u, α) then
        Decomp.partTerm .A2 (LN N) V (trialState V w kc N) (p, q, u, α) else 0) =
      ((LN N : ℂ) ^ 3)⁻¹ * ft V (mom (LN N) u) *
        FourLegs.mainTuple V w kc N p q (p - u) (q + u) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  have hp : p ≠ 0 := Regions_PH_ne_zero hρ (hl 0).1
  have hq : q ≠ 0 := Regions_PH_ne_zero hρ (hl 1).1
  have hpu : p - u ≠ 0 := Regions_PH_ne_zero hρ (hl 2).1
  have hqu : q + u ≠ 0 := Regions_PH_ne_zero hρ (hl 3).1
  have hpq := Regions_PL_ne_zero hρ hv
  have g02 : p ≠ p - u := (hg 0 2 (by decide)).1
  have g12 : q ≠ p - u := (hg 1 2 (by decide)).1
  have hA2 : Decomp.Part.A2.mem p q u := by
    refine ⟨?_, hpq, ?_⟩
    · simp only [Decomp.zeros, hp, hq, hpu, hqu, ite_false]
    · rintro (h | h)
      · exact g02 (by rw [h, sub_zero])
      · exact g12 (by rw [h]; abel)
  set Ψ := trialState V w kc N with hΨdef
  set s : Occ → ℂ := fun γ => if FourLegs.InMk (rhoN N) (LN N) kc N p q
      (a4 p q (p - u) (q + u) γ).2 then
    conj (Ψ (a4 p q (p - u) (q + u) γ).2) * ((a4 p q (p - u) (q + u) γ).1 : ℂ) * Ψ γ else 0
    with hs
  have hpt : ∀ α : Occ, (if (FourLegs.Cls.fourMain).mem (rhoN N) (LN N) kc N (p, q, u, α) then
      Decomp.partTerm .A2 (LN N) V Ψ (p, q, u, α) else 0) =
      ((LN N : ℂ) ^ 3)⁻¹ * ft V (mom (LN N) u) * s α := by
    intro α
    by_cases hm : FourLegs.InMk (rhoN N) (LN N) kc N p q (a4 p q (p - u) (q + u) α).2
    · have hmem : (FourLegs.Cls.fourMain).mem (rhoN N) (LN N) kc N (p, q, u, α) := ⟨hl, hg, hm⟩
      rw [ite_eq_left hmem, hs]
      simp only [ite_eq_left hm, Decomp.partTerm, ite_eq_left hA2, intTerm]
      push_cast
      ring
    · have hmem : ¬ (FourLegs.Cls.fourMain).mem (rhoN N) (LN N) kc N (p, q, u, α) :=
        fun h => hm h.2.2
      rw [ite_eq_right hmem, hs]
      simp [hm]
  have hss : Summable s := by
    refine Summable.of_norm_bounded (Expect.id4a_summable N Ψ hΨ p q (p - u) (q + u))
      (fun γ => ?_)
    simp only [hs]
    split_ifs
    · exact le_rfl
    · simp only [norm_zero]; positivity
  simp only [hpt]
  exact ⟨hss.mul_left _, tsum_mul_left⟩

set_option linter.flexible false in
set_option linter.unusedTactic false in
/-- If two of the legs `k₁, v - k₁, k₃, v - k₃` agree up to sign, then `v = 0`, or `k₃` is one of
six linear expressions in `k₁, v`, or `2k₁ = v`, or `2k₃ = v`. -/
private lemma MT_rel {v k₁ k₃ : Idx} (h : ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃]) :
    v = 0 ∨ k₃ = k₁ ∨ k₃ = -k₁ ∨ k₃ = v - k₁ ∨ k₃ = v + k₁ ∨ k₃ = k₁ - v ∨
      k₃ = v + v - k₁ ∨ (∀ i, 2 * k₁ i = v i) ∨ (∀ i, 2 * k₃ i = v i) := by
  unfold FourLegs.Gen at h
  push Not at h
  obtain ⟨i, j, hij, hl⟩ := h
  unfold Legs_pm at hl
  have hl' : ![k₁, v - k₁, k₃, v - k₃] i = ![k₁, v - k₁, k₃, v - k₃] j ∨
      ![k₁, v - k₁, k₃, v - k₃] i = -![k₁, v - k₁, k₃, v - k₃] j := by
    by_contra hc
    push Not at hc
    exact hl hc
  clear hl
  fin_cases i <;> fin_cases j <;> simp at hij hl' <;> rcases hl' with h | h <;>
  first
    | exact Or.inl (funext fun k => by have := congrFun h k; (try simp at this ⊢); omega)
    | exact Or.inr (Or.inl (funext fun k => by have := congrFun h k; (try simp at this ⊢); omega))
    | exact Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega)))
    | exact Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega)))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (funext fun k => by
        have := congrFun h k; (try simp at this ⊢); omega)))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (fun k => by
        have := congrFun h k; (try simp at this ⊢); omega))))))))
    | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (fun k => by
        have := congrFun h k; (try simp at this ⊢); omega))))))))

/-- The pairs `(k₁, k₃)` of `F × F` excluded by (10.7) [conditionk2] at a fixed `v ≠ 0`. -/
private def MT_img (v : Idx) (F : Finset Idx) : Finset (Idx × Idx) :=
  F.biUnion fun k => ([(k, k), (k, -k), (k, v - k), (k, v + k), (k, k - v), (k, v + v - k),
    ((fun i => v i / 2), k), (k, fun i => v i / 2)] : List (Idx × Idx)).toFinset

private lemma MT_img_card (v : Idx) (F : Finset Idx) : (MT_img v F).card ≤ 8 * F.card := by
  unfold MT_img
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ k ∈ F, (([(k, k), (k, -k), (k, v - k), (k, v + k), (k, k - v), (k, v + v - k),
        ((fun i => v i / 2), k), (k, fun i => v i / 2)] : List (Idx × Idx)).toFinset.card)
      ≤ ∑ _k ∈ F, 8 := Finset.sum_le_sum fun k _ => List.toFinset_card_le _
    _ = 8 * F.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

private lemma MT_img_mem {v k₁ k₃ : Idx} {F : Finset Idx} (h1 : k₁ ∈ F) (h3 : k₃ ∈ F)
    (hv : v ≠ 0) (hng : ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃]) : (k₁, k₃) ∈ MT_img v F := by
  unfold MT_img
  rw [Finset.mem_biUnion]
  rcases MT_rel hng with h | h | h | h | h | h | h | h | h
  · exact absurd h hv
  · exact ⟨k₁, h1, by simp [h]⟩
  · exact ⟨k₁, h1, by simp [h]⟩
  · exact ⟨k₁, h1, by simp [h]⟩
  · exact ⟨k₁, h1, by simp [h]⟩
  · exact ⟨k₁, h1, by simp [h]⟩
  · exact ⟨k₁, h1, by simp [h]⟩
  · have h' : k₁ = fun i => v i / 2 := funext fun i => by have := h i; omega
    exact ⟨k₃, h3, by simp [h']⟩
  · have h' : k₃ = fun i => v i / 2 := funext fun i => by have := h i; omega
    exact ⟨k₁, h1, by simp [h']⟩

/-! ### The fuzzy shell `A_v` -/

/-- `A_v = {p : ε < |p| ≤ k_c, ε < |p_v - p| ≤ k_c}`: `p_n ∈ A_v` iff `n, v - n ∈ P_{H,c}`. -/
private def MT_A (L ε kc : ℝ) (v : Idx) : Set R3 :=
  {p | ε < ‖p‖ ∧ ‖p‖ ≤ kc ∧ ε < ‖mom L v - p‖ ∧ ‖mom L v - p‖ ≤ kc}

private lemma MT_A_mem {ρ L kc : ℝ} {v n : Idx} :
    mom L n ∈ MT_A L (epsP ρ) kc v ↔ inPHc ρ L kc n ∧ inPHc ρ L kc (v - n) := by
  simp only [MT_A, Set.mem_ofPred_eq, inPHc, inPH, MT_mom_sub]
  tauto

/-- `A_v` lies between the shells of `IsShell` with `r₁ = ε`, `s = |p_v|`, `r₂ = k_c` (the fuzzy
shell of Lemma 10.2 [101]). -/
private lemma MT_A_shell {L ε kc : ℝ} (hkc : 0 < kc) (v : Idx) :
    IsShell ε (ENNReal.ofReal kc) ‖mom L v‖ (MT_A L ε kc v) := by
  refine ⟨fun p h1 h2 => ?_, fun p hp => ⟨hp.1.le, ENNReal.ofReal_le_ofReal hp.2.1⟩⟩
  rw [ENNReal.ofReal_lt_ofReal_iff hkc] at h2
  have hs := norm_nonneg (mom L v)
  have h3 : ‖p‖ - ‖mom L v‖ ≤ ‖mom L v - p‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  have h4 : ‖mom L v - p‖ ≤ ‖mom L v‖ + ‖p‖ := norm_sub_le _ _
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

private lemma MT_A_meas (L ε kc : ℝ) (v : Idx) : MeasurableSet (MT_A L ε kc v) := by
  have hm : Measurable fun p : R3 => ‖mom L v - p‖ := (measurable_const.sub measurable_id).norm
  exact (measurableSet_lt measurable_const measurable_norm).inter
    ((measurableSet_le measurable_norm measurable_const).inter
      ((measurableSet_lt measurable_const hm).inter (measurableSet_le hm measurable_const)))

/-- `E_2(δ) = δ(1 + log δ⁻¹) ≤ 3ε` for `0 < δ ≤ ε² ≤ 1`. -/
private lemma MT_rate {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ ≤ ε ^ 2) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    riemannRate 2 δ ≤ 3 * ε := by
  have hr : riemannRate 2 δ = δ * (1 + Real.log δ⁻¹) := by
    simp [riemannRate]
  rw [hr]
  have hlog : Real.log δ⁻¹ ≤ 2 * (Real.sqrt δ)⁻¹ := by
    have := Real.log_le_rpow_div (x := δ⁻¹) (ε := 1 / 2) (by positivity) (by norm_num)
    rw [← Real.sqrt_eq_rpow, Real.sqrt_inv] at this
    linarith
  have hsq : Real.sqrt δ ≤ ε := by
    calc Real.sqrt δ ≤ Real.sqrt (ε ^ 2) := Real.sqrt_le_sqrt hδε
      _ = ε := Real.sqrt_sq hε.le
  have hsδ : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hδs : δ * (Real.sqrt δ)⁻¹ = Real.sqrt δ := by
    field_simp
    rw [Real.sq_sqrt hδ.le]
  have hδ1 : δ ≤ ε := hδε.trans (by nlinarith)
  calc δ * (1 + Real.log δ⁻¹) = δ + δ * Real.log δ⁻¹ := by ring
    _ ≤ δ + δ * (2 * (Real.sqrt δ)⁻¹) := by gcongr
    _ = δ + 2 * (δ * (Real.sqrt δ)⁻¹) := by ring
    _ = δ + 2 * Real.sqrt δ := by rw [hδs]
    _ ≤ ε + 2 * ε := by linarith
    _ = 3 * ε := by ring

/-! ### Lemma 10.2 [101] -/

/-- `2π ≤ L ε²` for all large `N`. -/
private lemma MT_ev_L : ∀ᶠ N : ℕ in atTop, 2 * π ≤ LN N * epsP (rhoN N) ^ 2 := by
  have h : Tendsto (fun N : ℕ => rhoN N ^ (-(25/24 - 1/100 : ℝ))) atTop atTop := by
    have e : ∀ N : ℕ, rhoN N ^ (-(25/24 - 1/100 : ℝ)) =
        (N : ℝ) ^ ((8/17 : ℝ) * (25/24 - 1/100)) := by
      intro N; rw [rhoN, ← Real.rpow_mul (Nat.cast_nonneg N)]; ring_nf
    simp_rw [e]
    exact (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h.eventually_ge_atTop (2 * π), eventually_ge_atTop 1] with N hN hN1
  have hρ := (Particles_rhoN_LN hN1).2.1
  rw [LN, ← MT_rpow_eps hρ.le 2 rfl, ← Real.rpow_add hρ]
  convert hN using 2
  norm_num

/-- `0 ≤ ρ^{-5/2}|Λ|^{-2} Σ_{v ∈ P_L} Q_Ψ(0, v) ≤ g₀^{3/2}/(3π²) + C ρ^{1/400}`, from (8.29)
[sum0PL]. -/
private lemma MT_SN {V w : R3 → ℝ} (hg : 0 < g0 V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      0 ≤ rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ *
          (∑' v : Idx, if inPL (rhoN N) (LN N) v then
            Expect.Q (trialState V w kc N) [0, v] else 0) ∧
      rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ *
          (∑' v : Idx, if inPL (rhoN N) (LN N) v then
            Expect.Q (trialState V w kc N) [0, v] else 0) ≤
        g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) + C * rhoN N ^ (1/400 : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := Eq8_29 hg
  refine ⟨C, hC, max N₀ 1, fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  have h8 := (abs_le.1 (h N (le_of_max_le_left hN) kc)).2
  set S := ∑' v : Idx, if inPL (rhoN N) (LN N) v then
    Expect.Q (trialState V w kc N) [0, v] else 0 with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun v => by
    split_ifs
    · exact MT_Q_nonneg _ _
    · exact le_rfl
  refine ⟨by positivity, ?_⟩
  set ρ := rhoN N with hρdef
  set g := g0 V w with hgdef
  have hr : ρ - rho0 g ρ = (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) * ρ ^ (3/2 : ℝ) := by
    rw [rho0]; ring
  have hle : rho0 g ρ * (ρ - rho0 g ρ) ≤ ρ * (ρ - rho0 g ρ) := by
    nlinarith [sq_nonneg (ρ - rho0 g ρ)]
  have h52 : ρ * ρ ^ (3/2 : ℝ) = ρ ^ (5/2 : ℝ) := by
    rw [show (5/2 : ℝ) = 1 + 3/2 by norm_num, Real.rpow_add hρ, Real.rpow_one]
  have h52' : ρ ^ (5/2 + 1/400 : ℝ) = ρ ^ (5/2 : ℝ) * ρ ^ (1/400 : ℝ) := Real.rpow_add hρ _ _
  have hinv : ρ ^ (-(5/2 : ℝ)) * ρ ^ (5/2 : ℝ) = 1 := by
    rw [Real.rpow_neg hρ.le, inv_mul_cancel₀ (by positivity)]
  have hup : ((LN N ^ 3) ^ 2)⁻¹ * S ≤
      ρ ^ (5/2 : ℝ) * ((3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) + C * ρ ^ (1/400 : ℝ)) := by
    have : ρ * (ρ - rho0 g ρ) = ρ ^ (5/2 : ℝ) * ((3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ)) := by
      rw [hr, ← h52]; ring
    rw [h52'] at h8
    nlinarith
  have hn : 0 ≤ ρ ^ (-(5/2 : ℝ)) := by positivity
  calc ρ ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ * S = ρ ^ (-(5/2 : ℝ)) * (((LN N ^ 3) ^ 2)⁻¹ * S) := by
        ring
    _ ≤ ρ ^ (-(5/2 : ℝ)) * (ρ ^ (5/2 : ℝ) * ((3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) +
          C * ρ ^ (1/400 : ℝ))) := mul_le_mul_of_nonneg_left hup hn
    _ = g ^ (3/2 : ℝ) / (3 * π ^ 2) + C * ρ ^ (1/400 : ℝ) := by
        rw [← mul_assoc, hinv, one_mul]
        ring

set_option maxRecDepth 10000 in
/-- The final count of Lemma 10.2 [101] with a rate: the four error terms (the `ρ^{19/10}` part
of (10.20) [temp8.150] over all tuples, its `ρ^{2/5}` part, the Riemann sum and the tuples
excluded by (10.7) [conditionk2]), normalized by `ρ^{-5/2}|Λ|^{-1}`. -/
private lemma MT_alg {L3 ε kc nF nFL V₀ C20 K g CS SN Er : ℝ}
    (hL3 : 0 < L3) (hε : 0 < ε) (hε1 : ε ≤ 1) (hkc : 1 ≤ kc) (hL3ε : L3 * ε ^ 625 = 1)
    (hnF0 : 0 ≤ nF) (hnF : nF ≤ 64 * L3 * kc ^ 3) (hnFL0 : 0 ≤ nFL)
    (hnFL : nFL ≤ 64 * L3 * ε ^ 297) (hV₀ : 0 ≤ V₀) (hC20 : 0 ≤ C20) (hK : 0 ≤ K)
    (hSN0 : 0 ≤ SN) (hSN : SN ≤ CS)
    (hEr : |Er| ≤ nF ^ 2 * (L3⁻¹ * V₀ * (nFL * (C20 * ε ^ 380 / L3) +
        C20 * ε ^ 80 / L3 ^ 2 * (SN * (L3 ^ 2 * ε ^ 500)))) +
      4 * L3⁻¹ * (K * (5 * ε + kc⁻¹) +
        (L3 ^ 2)⁻¹ * (8 * (64 * L3 * kc ^ 3) * (V₀ * (g / ε ^ 2) ^ 2))) *
        (SN * (L3 ^ 2 * ε ^ 500))) :
    |Er| / (L3 * ε ^ 500) ≤ (20 * K * CS + 64 ^ 3 * V₀ * C20 + 64 ^ 2 * V₀ * C20 * CS +
      2048 * CS * V₀ * g ^ 2) * (ε + kc⁻¹ + kc ^ 6 * ε ^ 80) := by
  have hCS : 0 ≤ CS := hSN0.trans hSN
  have hP : 0 < L3 * ε ^ 500 := by positivity
  have hkc0 : 0 < kc := by linarith
  refine (div_le_iff₀ hP).2 (hEr.trans ?_)
  have hk6 : kc ^ 3 ≤ kc ^ 6 := pow_le_pow_right₀ hkc (by norm_num)
  have e177 : ε ^ 177 ≤ ε ^ 80 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have e621 : ε ^ 621 ≤ ε ^ 80 := pow_le_pow_of_le_one hε.le hε1 (by norm_num)
  have ha : nF ^ 2 * (L3⁻¹ * V₀ * (nFL * (C20 * ε ^ 380 / L3))) ≤
      64 ^ 3 * V₀ * C20 * (kc ^ 6 * ε ^ 80) * (L3 * ε ^ 500) := by
    calc _ ≤ (64 * L3 * kc ^ 3) ^ 2 * (L3⁻¹ * V₀ * ((64 * L3 * ε ^ 297) *
          (C20 * ε ^ 380 / L3))) := by gcongr
      _ = 64 ^ 3 * V₀ * C20 * (kc ^ 6 * ε ^ 177) * (L3 * ε ^ 500) := by
          field_simp
      _ ≤ _ := by gcongr
  have hb : nF ^ 2 * (L3⁻¹ * V₀ * (C20 * ε ^ 80 / L3 ^ 2 * (SN * (L3 ^ 2 * ε ^ 500)))) ≤
      64 ^ 2 * V₀ * C20 * CS * (kc ^ 6 * ε ^ 80) * (L3 * ε ^ 500) := by
    calc _ ≤ (64 * L3 * kc ^ 3) ^ 2 * (L3⁻¹ * V₀ * (C20 * ε ^ 80 / L3 ^ 2 *
          (CS * (L3 ^ 2 * ε ^ 500)))) := by gcongr
      _ = _ := by field_simp
  have hc : 4 * L3⁻¹ * (K * (5 * ε + kc⁻¹)) * (SN * (L3 ^ 2 * ε ^ 500)) ≤
      (20 * K * CS * ε + 4 * K * CS * kc⁻¹) * (L3 * ε ^ 500) := by
    calc _ ≤ 4 * L3⁻¹ * (K * (5 * ε + kc⁻¹)) * (CS * (L3 ^ 2 * ε ^ 500)) := by gcongr
      _ = _ := by field_simp; ring
  have hd : 4 * L3⁻¹ * ((L3 ^ 2)⁻¹ * (8 * (64 * L3 * kc ^ 3) * (V₀ * (g / ε ^ 2) ^ 2))) *
      (SN * (L3 ^ 2 * ε ^ 500)) ≤ 2048 * CS * V₀ * g ^ 2 * (kc ^ 6 * ε ^ 80) * (L3 * ε ^ 500) := by
    calc _ ≤ 4 * L3⁻¹ * ((L3 ^ 2)⁻¹ * (8 * (64 * L3 * kc ^ 3) * (V₀ * (g / ε ^ 2) ^ 2))) *
          (CS * (L3 ^ 2 * ε ^ 500)) := by gcongr
      _ = 2048 * CS * V₀ * g ^ 2 * kc ^ 3 * ε ^ 496 := by field_simp; ring
      _ = 2048 * CS * V₀ * g ^ 2 * (kc ^ 3 * ε ^ 621) * (L3 * ε ^ 500) := by
          linear_combination (-(2048 * CS * V₀ * g ^ 2 * kc ^ 3 * ε ^ 496)) * hL3ε
      _ ≤ _ := by gcongr
  set X := 64 ^ 3 * V₀ * C20 + 64 ^ 2 * V₀ * C20 * CS + 2048 * CS * V₀ * g ^ 2 with hX
  have hX0 : 0 ≤ X := by positivity
  have hpos : 0 ≤ (L3 * ε ^ 500) * (X * ε + (16 * K * CS + X) * kc⁻¹ +
      20 * K * CS * (kc ^ 6 * ε ^ 80)) := by positivity
  have hsplit : nF ^ 2 * (L3⁻¹ * V₀ * (nFL * (C20 * ε ^ 380 / L3) +
        C20 * ε ^ 80 / L3 ^ 2 * (SN * (L3 ^ 2 * ε ^ 500)))) +
      4 * L3⁻¹ * (K * (5 * ε + kc⁻¹) +
        (L3 ^ 2)⁻¹ * (8 * (64 * L3 * kc ^ 3) * (V₀ * (g / ε ^ 2) ^ 2))) *
        (SN * (L3 ^ 2 * ε ^ 500)) =
      nF ^ 2 * (L3⁻¹ * V₀ * (nFL * (C20 * ε ^ 380 / L3))) +
        nF ^ 2 * (L3⁻¹ * V₀ * (C20 * ε ^ 80 / L3 ^ 2 * (SN * (L3 ^ 2 * ε ^ 500)))) +
        4 * L3⁻¹ * (K * (5 * ε + kc⁻¹)) * (SN * (L3 ^ 2 * ε ^ 500)) +
        4 * L3⁻¹ * ((L3 ^ 2)⁻¹ * (8 * (64 * L3 * kc ^ 3) * (V₀ * (g / ε ^ 2) ^ 2))) *
          (SN * (L3 ^ 2 * ε ^ 500)) := by ring
  have hR : (20 * K * CS + X) * (ε + kc⁻¹ + kc ^ 6 * ε ^ 80) * (L3 * ε ^ 500) -
      (64 ^ 3 * V₀ * C20 * (kc ^ 6 * ε ^ 80) * (L3 * ε ^ 500) +
        64 ^ 2 * V₀ * C20 * CS * (kc ^ 6 * ε ^ 80) * (L3 * ε ^ 500) +
        (20 * K * CS * ε + 4 * K * CS * kc⁻¹) * (L3 * ε ^ 500) +
        2048 * CS * V₀ * g ^ 2 * (kc ^ 6 * ε ^ 80) * (L3 * ε ^ 500)) =
      (L3 * ε ^ 500) * (X * ε + (16 * K * CS + X) * kc⁻¹ + 20 * K * CS * (kc ^ 6 * ε ^ 80)) := by
    rw [hX]; ring
  rw [hsplit]
  have : 20 * K * CS + 64 ^ 3 * V₀ * C20 + 64 ^ 2 * V₀ * C20 * CS + 2048 * CS * V₀ * g ^ 2 =
      20 * K * CS + X := by rw [hX]; ring
  rw [this]
  linarith

/-- The legs `k₁, v - k₁, k₃, v - k₃` of (10.7) [conditionk2] with `v ∈ P_L`. -/
private def MT_cnd (ρ L kc : ℝ) (v k₁ k₃ : Idx) : Prop :=
  inPL ρ L v ∧ (inPHc ρ L kc k₁ ∧ inPHc ρ L kc (v - k₁)) ∧
    (inPHc ρ L kc k₃ ∧ inPHc ρ L kc (v - k₃)) ∧ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃]

/-- `V_{k₁-k₃} λ_{k₁} λ_{k₃}`. -/
private def MT_y (V w : R3 → ℝ) (ρ L : ℝ) (k₁ k₃ : Idx) : ℝ :=
  (ft V (mom L (k₁ - k₃))).re * lam V w ρ L k₁ * lam V w ρ L k₃

/-- `Σ_{k₁, k₃ ∈ F} V_{k₁-k₃} λ_{k₁} λ_{k₃}` over the legs (10.7) [conditionk2] at fixed `v`. -/
private def MT_I (V w : R3 → ℝ) (ρ L kc : ℝ) (F : Finset Idx) (v : Idx) : ℝ :=
  ∑ k₁ ∈ F, ∑ k₃ ∈ F, if MT_cnd ρ L kc v k₁ k₃ then MT_y V w ρ L k₁ k₃ else 0

/-- (10.10) [resultinMk1k2] at fixed `v ∈ P_L`: `|Λ|^{-2} Σ_{k₁, k₃} V_{k₁-k₃} λ_{k₁} λ_{k₃}`
over the legs (10.7) [conditionk2] is `‖Vw²‖₁` up to the Riemann sum over the fuzzy shell `A_v`
and the excluded legs. -/
private lemma MT_riemann {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ kc : ℝ, 0 < kc →
      2 * π ≤ LN N * epsP (rhoN N) ^ 2 → ∀ F : Finset Idx,
      (∀ n : Idx, ‖mom (LN N) n‖ ≤ kc → n ∈ F) → ∀ v : Idx, inPL (rhoN N) (LN N) v →
      |((LN N ^ 3) ^ 2)⁻¹ * MT_I V w (rhoN N) (LN N) kc F v - normVw2 V w| ≤
        K * (5 * epsP (rhoN N) + kc⁻¹) + ((LN N ^ 3) ^ 2)⁻¹ *
          (8 * F.card * ((∫ x, V x) * (g0 V w / epsP (rhoN N) ^ 2) ^ 2)) := by
  obtain ⟨Cm, hVm, hgm⟩ := Bridge_momDecay hV hw 4
  obtain ⟨K, hK0, hK⟩ := sum_Vww (le_refl (4 : ℝ)) hVm hgm
  refine ⟨K, hK0, fun N hN1 kc hkc0 hLe F hF v hv => ?_⟩
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set ε := epsP ρ with hεdef
  set g := g0 V w with hgdef
  set V₀ := ∫ x, V x with hV₀def
  have hV₀ : ∀ p, ‖ft V p‖ ≤ V₀ := scat_ft_V_norm_le hV
  have hV₀0 : 0 ≤ V₀ := (norm_nonneg _).trans (hV₀ 0)
  have hε0 : 0 < ε := MT_eps_pos hρ
  have hε1 : ε ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hL3 : 0 < L ^ 3 := by positivity
  set Λ := g / ε ^ 2 with hΛ
  have hΛ0 : 0 ≤ Λ := div_nonneg (scat_g0_pos hV hw).le (by positivity)
  have hlam : ∀ n, inPHc ρ L kc n → |lam V w ρ L n| ≤ Λ :=
    fun n hn => scat_lam_PH hV hw ρ hρ L n hn.1
  have hyb : ∀ k₁ k₃, inPHc ρ L kc k₁ → inPHc ρ L kc k₃ → |MT_y V w ρ L k₁ k₃| ≤ V₀ * Λ ^ 2 := by
    intro k₁ k₃ h1 h3
    simp only [MT_y, abs_mul]
    have hv := (Complex.abs_re_le_norm _).trans (hV₀ (mom L (k₁ - k₃)))
    calc |(ft V (mom L (k₁ - k₃))).re| * |lam V w ρ L k₁| * |lam V w ρ L k₃| ≤ V₀ * Λ * Λ :=
          mul_le_mul (mul_le_mul hv (hlam _ h1) (abs_nonneg _) hV₀0) (hlam _ h3) (abs_nonneg _)
            (mul_nonneg hV₀0 hΛ0)
      _ = V₀ * Λ ^ 2 := by ring
  have hL2π : 2 * π ≤ L := hLe.trans (mul_le_of_le_one_right hL.le (pow_le_one₀ hε0.le hε1))
  have hrate : riemannRate 2 (2 * π / L) ≤ 3 * ε :=
    MT_rate (div_pos (by positivity) hL) (by rw [div_le_iff₀ hL]; linarith [hLe]) hε0 hε1
  set Gf : R3 → R3 → ℝ := fun p q => (ft V (p - q)).re * ((ft (gfun V w) p).re / ‖p‖ ^ 2) *
    ((ft (gfun V w) q).re / ‖q‖ ^ 2) with hGf
  have hWeq : normVw2 V w = (((2 * π) ^ 3) ^ 2)⁻¹ * ∫ p, ∫ q, Gf p q := by
    have e1 : normVw2 V w = ∫ x, V x * w x ^ 2 := by
      rw [normVw2]
      exact integral_congr_ae (Eventually.of_forall fun x =>
        abs_of_nonneg (mul_nonneg (hV.nonneg x) (sq_nonneg _)))
    rw [e1, scat_Vw2_eq hV hw, inv_pow, ← pow_mul]
    rfl
  have hv0 : v ≠ 0 := Regions_PL_ne_zero hρ hv
  set A : Idx → Prop := fun k => inPHc ρ L kc k ∧ inPHc ρ L kc (v - k) with hA
  set J := ∑ k₁ ∈ F, ∑ k₃ ∈ F, if A k₁ ∧ A k₃ then MT_y V w ρ L k₁ k₃ else 0 with hJ
  set X := ∑ k₁ ∈ F, ∑ k₃ ∈ F,
    if A k₁ ∧ A k₃ ∧ ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃] then MT_y V w ρ L k₁ k₃ else 0
    with hX
  have hIJX : MT_I V w ρ L kc F v = J - X := by
    simp only [MT_I, hJ, hX, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₃ _ => ?_))
    by_cases h1 : A k₁
    · by_cases h3 : A k₃
      · by_cases hG : FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃]
        · rw [ite_eq_left (show MT_cnd ρ L kc v k₁ k₃ from ⟨hv, h1, h3, hG⟩),
            ite_eq_left (show A k₁ ∧ A k₃ from ⟨h1, h3⟩),
            ite_eq_right (show ¬ (A k₁ ∧ A k₃ ∧ ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃]) from
              fun h => h.2.2 hG)]
          ring
        · rw [ite_eq_right (show ¬ MT_cnd ρ L kc v k₁ k₃ from fun h => hG h.2.2.2),
            ite_eq_left (show A k₁ ∧ A k₃ from ⟨h1, h3⟩),
            ite_eq_left (show A k₁ ∧ A k₃ ∧ ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃] from
              ⟨h1, h3, hG⟩)]
          ring
      · rw [ite_eq_right (show ¬ MT_cnd ρ L kc v k₁ k₃ from fun h => h3 h.2.2.1),
          ite_eq_right (show ¬ (A k₁ ∧ A k₃) from fun h => h3 h.2),
          ite_eq_right (show ¬ (A k₁ ∧ A k₃ ∧ ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃]) from
            fun h => h3 h.2.1)]
        ring
    · rw [ite_eq_right (show ¬ MT_cnd ρ L kc v k₁ k₃ from fun h => h1 h.2.1),
        ite_eq_right (show ¬ (A k₁ ∧ A k₃) from fun h => h1 h.1),
        ite_eq_right (show ¬ (A k₁ ∧ A k₃ ∧ ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃]) from
          fun h => h1 h.1)]
      ring
  have hXb : |X| ≤ 8 * F.card * (V₀ * Λ ^ 2) := by
    have h1 : |X| ≤ ∑ k₁ ∈ F, ∑ k₃ ∈ F,
        if A k₁ ∧ A k₃ ∧ ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃] then V₀ * Λ ^ 2 else 0 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k₁ _ => ?_))
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun k₃ _ => ?_))
      split_ifs with h
      · exact hyb k₁ k₃ h.1.1 h.2.1.1
      · simp
    refine h1.trans ?_
    have hp := Finset.sum_product' F F (fun k₁ k₃ =>
      if A k₁ ∧ A k₃ ∧ ¬ FourLegs.Gen ![k₁, v - k₁, k₃, v - k₃] then V₀ * Λ ^ 2 else 0)
    rw [← hp, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((F ×ˢ F).filter (fun x : Idx × Idx =>
        A x.1 ∧ A x.2 ∧ ¬ FourLegs.Gen ![x.1, v - x.1, x.2, v - x.2])).card ≤ 8 * F.card := by
      refine (Finset.card_le_card (fun x hx => ?_)).trans (MT_img_card v F)
      obtain ⟨hxF, -, -, hng⟩ := Finset.mem_filter.1 hx
      obtain ⟨h1, h3⟩ := Finset.mem_product.1 hxF
      exact MT_img_mem h1 h3 hv0 hng
    have hc' : (((F ×ˢ F).filter (fun x : Idx × Idx =>
        A x.1 ∧ A x.2 ∧ ¬ FourLegs.Gen ![x.1, v - x.1, x.2, v - x.2])).card : ℝ) ≤
        8 * F.card := by exact_mod_cast hc
    exact mul_le_mul_of_nonneg_right hc' (by positivity)
  have hJlat : J = latSum2 L (MT_A L ε kc v) Gf := by
    unfold latSum2
    rw [tsum_eq_sum (s := F ×ˢ F)]
    · rw [Finset.sum_product]
      refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₃ _ => ?_))
      by_cases h1 : A k₁
      · by_cases h3 : A k₃
        · have hc : k₁ ≠ 0 ∧ k₃ ≠ 0 ∧ mom L k₁ ∈ MT_A L ε kc v ∧ mom L k₃ ∈ MT_A L ε kc v :=
            ⟨Regions_PH_ne_zero hρ h1.1.1, Regions_PH_ne_zero hρ h3.1.1,
              MT_A_mem (ρ := ρ).2 h1, MT_A_mem (ρ := ρ).2 h3⟩
          rw [ite_eq_left (show A k₁ ∧ A k₃ from ⟨h1, h3⟩), ite_eq_left hc]
          have l1 : lam V w ρ L k₁ = -wmom V w (mom L k₁) :=
            scat_lam_of_not_PL ρ L k₁ (fun h => Regions_PL_PH hρ h h1.1.1)
          have l3 : lam V w ρ L k₃ = -wmom V w (mom L k₃) :=
            scat_lam_of_not_PL ρ L k₃ (fun h => Regions_PL_PH hρ h h3.1.1)
          simp only [MT_y, hGf, l1, l3, MT_mom_sub, wmom]
          ring
        · rw [ite_eq_right (fun h : A k₁ ∧ A k₃ => h3 h.2),
            ite_eq_right (fun h : k₁ ≠ 0 ∧ k₃ ≠ 0 ∧ mom L k₁ ∈ MT_A L ε kc v ∧
              mom L k₃ ∈ MT_A L ε kc v => h3 (MT_A_mem (ρ := ρ).1 h.2.2.2))]
      · rw [ite_eq_right (fun h : A k₁ ∧ A k₃ => h1 h.1),
          ite_eq_right (fun h : k₁ ≠ 0 ∧ k₃ ≠ 0 ∧ mom L k₁ ∈ MT_A L ε kc v ∧
            mom L k₃ ∈ MT_A L ε kc v => h1 (MT_A_mem (ρ := ρ).1 h.2.2.1))]
    · intro nm hnm
      rw [ite_eq_right]
      rintro ⟨-, -, h1, h2⟩
      exact hnm (Finset.mem_product.2 ⟨hF _ (MT_A_mem (ρ := ρ).1 h1).1.2,
        hF _ (MT_A_mem (ρ := ρ).1 h2).1.2⟩)
  obtain ⟨-, hRS⟩ := hK L ε ‖mom L v‖ (ENNReal.ofReal kc) (MT_A L ε kc v) hL2π hε0.le
    (norm_nonneg _) (ENNReal.ofReal_pos.2 hkc0) (MT_A_meas _ _ _ _) (MT_A_shell hkc0 v)
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hkc0.le] at hRS
  have hRS' : |((L ^ 3) ^ 2)⁻¹ * latSum2 L (MT_A L ε kc v) Gf -
      (((2 * π) ^ 3) ^ 2)⁻¹ * ∫ p, ∫ q, Gf p q| ≤
      K * (ε + ‖mom L v‖ + kc⁻¹ + riemannRate 2 (2 * π / L)) := hRS
  have hmv : ‖mom L v‖ ≤ ε ^ 99 := by
    have h2 : ‖mom L v‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := hv.2
    rw [MT_rpow_eps hρ.le 100 (by norm_num)] at h2
    change ‖mom L v‖ ≤ ε⁻¹ * ε ^ 100 at h2
    refine h2.trans (le_of_eq ?_)
    field_simp
  have he99 : ε ^ 99 ≤ ε := by
    simpa using pow_le_pow_of_le_one hε0.le hε1 (show 1 ≤ 99 by norm_num)
  have hK5 : K * (ε + ‖mom L v‖ + kc⁻¹ + riemannRate 2 (2 * π / L)) ≤ K * (5 * ε + kc⁻¹) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  have e : ((L ^ 3) ^ 2)⁻¹ * MT_I V w ρ L kc F v - normVw2 V w =
      (((L ^ 3) ^ 2)⁻¹ * latSum2 L (MT_A L ε kc v) Gf -
        (((2 * π) ^ 3) ^ 2)⁻¹ * ∫ p, ∫ q, Gf p q) - ((L ^ 3) ^ 2)⁻¹ * X := by
    rw [hIJX, ← hJlat, ← hWeq]; ring
  rw [e]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul (((L ^ 3) ^ 2)⁻¹) X, abs_of_pos (show 0 < ((L ^ 3) ^ 2)⁻¹ by positivity)]
  exact add_le_add (hRS'.trans hK5) (mul_le_mul_of_nonneg_left hXb (by positivity))

set_option maxRecDepth 10000 in
/-- The class `fourMain` as a finite sum over the legs `(v, k₁, k₃)` of (10.7) [conditionk2],
with (10.20) [temp8.150] for each of them: the real part of the sum differs from
`4 |Λ|^{-3} Σ_v Q_Ψ(0, v) Σ_{k₁, k₃} V_{k₁-k₃} λ_{k₁} λ_{k₃}` by the error terms of (10.20)
summed over the legs. -/
private lemma MT_tuples {V w : R3 → ℝ} (hV : PotentialHyp V) {N : ℕ} (hN1 : 1 ≤ N)
    {kc C20 : ℝ} (hC20 : 0 ≤ C20) {F FL : Finset Idx} (hF : ∀ n : Idx, ‖mom (LN N) n‖ ≤ kc → n ∈ F)
    (hFL : ∀ n : Idx, inPL (rhoN N) (LN N) n → n ∈ FL)
    (h20 : ∀ k₁ k₂ k₃ k₄ : Idx,
      inPHc (rhoN N) (LN N) kc k₁ → inPHc (rhoN N) (LN N) kc k₂ →
      inPHc (rhoN N) (LN N) kc k₃ → inPHc (rhoN N) (LN N) kc k₄ →
      FourLegs.Gen ![k₁, k₂, k₃, k₄] → k₁ + k₂ = k₃ + k₄ → inPL (rhoN N) (LN N) (k₁ + k₂) →
      ‖FourLegs.mainTuple V w kc N k₁ k₂ k₃ k₄ -
          ((4 * lam V w (rhoN N) (LN N) k₁ * lam V w (rhoN N) (LN N) k₃ / (LN N ^ 3) ^ 2 *
            Expect.Q (trialState V w kc N) [0, k₁ + k₂] : ℝ) : ℂ)‖ ≤
        C20 * epsP (rhoN N) ^ 380 / LN N ^ 3 +
          C20 * epsP (rhoN N) ^ 80 / (LN N ^ 3) ^ 2 *
            Expect.Q (trialState V w kc N) [0, k₁ + k₂]) :
    |(∑' i : Idx × Idx × Idx × Occ, if (FourLegs.Cls.fourMain).mem (rhoN N) (LN N) kc N i then
        Decomp.partTerm .A2 (LN N) V (trialState V w kc N) i else 0).re -
      ∑ v ∈ FL, 4 * (LN N ^ 3)⁻¹ * ((LN N ^ 3) ^ 2)⁻¹ * Expect.Q (trialState V w kc N) [0, v] *
        MT_I V w (rhoN N) (LN N) kc F v| ≤
      (F.card : ℝ) ^ 2 * ((LN N ^ 3)⁻¹ * (∫ x, V x) *
        ((FL.card : ℝ) * (C20 * epsP (rhoN N) ^ 380 / LN N ^ 3) +
          C20 * epsP (rhoN N) ^ 80 / (LN N ^ 3) ^ 2 *
            ∑ v ∈ FL, if inPL (rhoN N) (LN N) v then
              Expect.Q (trialState V w kc N) [0, v] else 0)) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set ε := epsP ρ with hεdef
  set Ψ := trialState V w kc N with hΨdef
  set V₀ := ∫ x, V x with hV₀def
  have hV₀ : ∀ p, ‖ft V p‖ ≤ V₀ := scat_ft_V_norm_le hV
  have hV₀0 : 0 ≤ V₀ := (norm_nonneg _).trans (hV₀ 0)
  have hε0 : 0 < ε := MT_eps_pos hρ
  have hL3 : 0 < L ^ 3 := by positivity
  set Φ : Idx × Idx × Idx × Occ → ℂ := fun i =>
    if (FourLegs.Cls.fourMain).mem ρ L kc N i then Decomp.partTerm .A2 L V Ψ i else 0 with hΦ
  set T' := (FL ×ˢ (F ×ˢ F)).filter (fun x => MT_cnd ρ L kc x.1 x.2.1 x.2.2) with hT'
  set φ : Idx × Idx × Idx → Idx × Idx × Idx := fun x => (x.2.1, x.1 - x.2.1, x.2.1 - x.2.2)
    with hφ
  set T := T'.image φ with hT
  have hφinj : Set.InjOn φ ↑T' := by
    intro x _ y _ hxy
    obtain ⟨v, k₁, k₃⟩ := x
    obtain ⟨v', k₁', k₃'⟩ := y
    simp only [hφ, Prod.mk.injEq] at hxy
    obtain ⟨h1, h2, h3⟩ := hxy
    subst h1
    exact Prod.ext (sub_left_injective h2) (Prod.ext rfl (sub_right_injective h3))
  have hlegs : ∀ v k₁ k₃ : Idx,
      FourLegs.legs k₁ (v - k₁) (k₁ - k₃) = ![k₁, v - k₁, k₃, v - k₃] := by
    intro v k₁ k₃
    have e1 : k₁ - (k₁ - k₃) = k₃ := sub_sub_cancel _ _
    have e2 : v - k₁ + (k₁ - k₃) = v - k₃ := by abel
    simp only [FourLegs.legs, e1, e2]
  have hreidx : ∀ f : Idx × Idx × Idx → ℝ, ∑ t ∈ T, f t = ∑ v ∈ FL, ∑ k₁ ∈ F, ∑ k₃ ∈ F,
      if MT_cnd ρ L kc v k₁ k₃ then f (k₁, v - k₁, k₁ - k₃) else 0 := by
    intro f
    rw [hT, Finset.sum_image hφinj, hT', Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.sum_product]
  have hgood : ∀ t ∈ T, (∀ j, inPHc ρ L kc (FourLegs.legs t.1 t.2.1 t.2.2 j)) ∧
      FourLegs.Gen (FourLegs.legs t.1 t.2.1 t.2.2) ∧ inPL ρ L (t.1 + t.2.1) := by
    intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨v, k₁, k₃⟩ := x
    obtain ⟨hv, ⟨h1, h2⟩, ⟨h3, h4⟩, hgen⟩ := (Finset.mem_filter.1 hx).2
    simp only [hφ]
    rw [hlegs, add_sub_cancel]
    refine ⟨fun j => ?_, hgen, hv⟩
    fin_cases j
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  have hsupp : ∀ i, Φ i ≠ 0 → (i.1, i.2.1, i.2.2.1) ∈ T := by
    intro i hi
    obtain ⟨p, q, u, α⟩ := i
    have hm : (FourLegs.Cls.fourMain).mem ρ L kc N (p, q, u, α) := by
      by_contra hc
      exact hi (by simp only [hΦ, hc, ite_false])
    obtain ⟨hall, hgen, hmk⟩ := hm
    have hv : inPL ρ L (p + q) := hmk.2.1
    have h1 : inPHc ρ L kc p := hall 0
    have h2 : inPHc ρ L kc q := hall 1
    have h3 : inPHc ρ L kc (p - u) := hall 2
    have h4 : inPHc ρ L kc (q + u) := hall 3
    have e1 : p + q - p = q := by abel
    have e2 : p + q - (p - u) = q + u := by abel
    have e3 : p - (p - u) = u := sub_sub_cancel _ _
    refine Finset.mem_image.2 ⟨(p + q, p, p - u), ?_, ?_⟩
    · rw [hT', Finset.mem_filter]
      refine ⟨Finset.mem_product.2 ⟨hFL _ hv,
        Finset.mem_product.2 ⟨hF _ h1.2, hF _ h3.2⟩⟩, ?_⟩
      simp only [MT_cnd, e1, e2]
      exact ⟨hv, ⟨h1, h2⟩, ⟨h3, h4⟩, hgen⟩
    · simp only [hφ, e1, e3]
  have hfib : ∀ t ∈ T, _ := fun t ht =>
    MT_fiber V w kc hN1 (hgood t ht).1 (hgood t ht).2.1 (hgood t ht).2.2
  have hΞ : ∑' i, Φ i = ∑ t ∈ T, ((L : ℂ) ^ 3)⁻¹ * ft V (mom L t.2.2) *
      FourLegs.mainTuple V w kc N t.1 t.2.1 (t.1 - t.2.2) (t.2.1 + t.2.2) := by
    rw [MT_tuples_eq T Φ hsupp (fun t ht => (hfib t ht).1)]
    exact Finset.sum_congr rfl (fun t ht => (hfib t ht).2)
  set Q0 : Idx → ℝ := fun v => Expect.Q Ψ [0, v] with hQ0
  have hQ0nn : ∀ v, 0 ≤ Q0 v := fun v => MT_Q_nonneg _ _
  set mf : Idx × Idx × Idx → ℝ := fun t => (L ^ 3)⁻¹ * (ft V (mom L t.2.2)).re *
    (4 * lam V w ρ L t.1 * lam V w ρ L (t.1 - t.2.2) / (L ^ 3) ^ 2 * Q0 (t.1 + t.2.1)) with hmf
  set ef : Idx × Idx × Idx → ℝ := fun t => (L ^ 3)⁻¹ * V₀ *
    (C20 * ε ^ 380 / L ^ 3 + C20 * ε ^ 80 / (L ^ 3) ^ 2 * Q0 (t.1 + t.2.1)) with hef
  have hpt : ∀ t ∈ T, |(((L : ℂ) ^ 3)⁻¹ * ft V (mom L t.2.2) *
      FourLegs.mainTuple V w kc N t.1 t.2.1 (t.1 - t.2.2) (t.2.1 + t.2.2)).re - mf t| ≤ ef t := by
    intro t ht
    obtain ⟨hall, hgen, hv⟩ := hgood t ht
    obtain ⟨p, q, u⟩ := t
    simp only at hall hgen hv ⊢
    have hb := h20 p q (p - u) (q + u) (hall 0) (hall 1) (hall 2) (hall 3) hgen (by abel) hv
    set mt := FourLegs.mainTuple V w kc N p q (p - u) (q + u) with hmt
    set M := 4 * lam V w ρ L p * lam V w ρ L (p - u) / (L ^ 3) ^ 2 * Q0 (p + q) with hM
    have hre : ft V (mom L u) = (((ft V (mom L u)).re : ℝ) : ℂ) := scat_ft_V_real hV _
    have e : ((L : ℂ) ^ 3)⁻¹ * ft V (mom L u) * mt =
        (((L ^ 3)⁻¹ * (ft V (mom L u)).re : ℝ) : ℂ) * mt := by
      conv_lhs => rw [hre]
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    have e2 : (L ^ 3)⁻¹ * (ft V (mom L u)).re * mt.re - mf (p, q, u) =
        (L ^ 3)⁻¹ * (ft V (mom L u)).re * (mt - (M : ℂ)).re := by
      simp only [hmf, hM, Complex.sub_re, Complex.ofReal_re]; ring
    rw [e2, abs_mul, abs_mul, abs_of_pos (by positivity)]
    have h1 : |(ft V (mom L u)).re| ≤ V₀ := (Complex.abs_re_le_norm _).trans (hV₀ _)
    have h2 : |(mt - (M : ℂ)).re| ≤
        C20 * ε ^ 380 / L ^ 3 + C20 * ε ^ 80 / (L ^ 3) ^ 2 * Q0 (p + q) :=
      (Complex.abs_re_le_norm _).trans hb
    simp only [hef]
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (abs_nonneg _)
      (by positivity)
  have hdiff : |(∑' i, Φ i).re - ∑ t ∈ T, mf t| ≤ ∑ t ∈ T, ef t := by
    rw [hΞ, Complex.re_sum, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hpt)
  have hmain : ∑ t ∈ T, mf t =
      ∑ v ∈ FL, 4 * (L ^ 3)⁻¹ * ((L ^ 3) ^ 2)⁻¹ * Q0 v * MT_I V w ρ L kc F v := by
    rw [hreidx]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [MT_I, Finset.mul_sum, mul_ite, mul_zero]
    refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₃ _ => ?_))
    split_ifs
    · simp only [hmf, MT_y, sub_sub_cancel, add_sub_cancel]
      ring
    · rfl
  have herr : ∑ t ∈ T, ef t ≤ (F.card : ℝ) ^ 2 * ((L ^ 3)⁻¹ * V₀ *
      ((FL.card : ℝ) * (C20 * ε ^ 380 / L ^ 3) + C20 * ε ^ 80 / (L ^ 3) ^ 2 *
        ∑ v ∈ FL, if inPL ρ L v then Q0 v else 0)) := by
    rw [hreidx]
    set b : Idx → ℝ := fun v => (L ^ 3)⁻¹ * V₀ * (C20 * ε ^ 380 / L ^ 3 +
      C20 * ε ^ 80 / (L ^ 3) ^ 2 * (if inPL ρ L v then Q0 v else 0)) with hb
    have hb0 : ∀ v, 0 ≤ b v := fun v => by
      simp only [hb]
      have := hQ0nn v
      split_ifs <;> positivity
    calc _ ≤ ∑ v ∈ FL, ∑ _k₁ ∈ F, ∑ _k₃ ∈ F, b v := by
          refine Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun k₁ _ =>
            Finset.sum_le_sum (fun k₃ _ => ?_)))
          split_ifs with hc
          · have hv : inPL ρ L v := hc.1
            simp only [hef, hb, ite_eq_left hv, add_sub_cancel]
            exact le_rfl
          · exact hb0 v
      _ = (F.card : ℝ) ^ 2 * ∑ v ∈ FL, b v := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun v _ => ?_)
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
      _ = _ := by
          congr 1
          simp only [hb]
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
            ← Finset.mul_sum]
  rw [← hmain]
  exact hdiff.trans herr

set_option maxRecDepth 10000 in
/-- Lemma 10.2 [101] with a rate: the main term of (10.10) [resultinMk1k2] is
`4 ‖Vw²‖₁ ρ^{-5/2} |Λ|^{-2} Σ_{v ∈ P_L} Q_Ψ(0, v)` up to `C(ρ^η + k_c⁻¹ + k_c⁶ ρ^{2/5})`. -/
theorem Lemma10_2_rate {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc →
      |FourLegs.part V w .fourMain kc N - 4 * normVw2 V w *
          (rhoN N ^ (-(5/2 : ℝ)) * ((LN N ^ 3) ^ 2)⁻¹ *
            (∑' v : Idx, if inPL (rhoN N) (LN N) v then
              Expect.Q (trialState V w kc N) [0, v] else 0))| ≤
        C * (rhoN N ^ (1/200 : ℝ) + kc⁻¹ + kc ^ 6 * rhoN N ^ (2/5 : ℝ)) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C20, hC20, N20, h20⟩ := Eq10_20 hV hw
  obtain ⟨CS0, hCS0, NS, hSN⟩ := MT_SN hg
  obtain ⟨K, hK0, hK⟩ := MT_riemann hV hw
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 MT_ev_L
  set g := g0 V w with hgdef
  set V₀ := ∫ x, V x with hV₀def
  have hV₀0 : 0 ≤ V₀ := (norm_nonneg _).trans (scat_ft_V_norm_le hV 0)
  set CS := g ^ (3/2 : ℝ) / (3 * π ^ 2) + CS0 with hCS
  have hCS0' : 0 ≤ CS := by positivity
  refine ⟨20 * K * CS + 64 ^ 3 * V₀ * C20 + 64 ^ 2 * V₀ * C20 * CS + 2048 * CS * V₀ * g ^ 2,
    by positivity, max (max N20 NS) (max N₁ 1), ?_⟩
  intro N hN kc hkc
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨hN20, hNS⟩, hN1', hN1⟩ := hN
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hLe := hN₁ N hN1'
  have hL3ε : LN N ^ 3 * epsP (rhoN N) ^ 625 = 1 := by
    have e1 : LN N ^ 3 = rhoN N ^ (-(25/8 : ℝ)) := by
      rw [LN, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]; norm_num
    rw [e1, ← MT_rpow_eps hρ.le 625 (x := 25/8) (by norm_num), ← Real.rpow_add hρ]
    norm_num
  have h19 : rhoN N ^ (19/10 : ℝ) = epsP (rhoN N) ^ 380 := MT_rpow_eps hρ.le 380 (by norm_num)
  have h25 : rhoN N ^ (2/5 : ℝ) = epsP (rhoN N) ^ 80 := MT_rpow_eps hρ.le 80 (by norm_num)
  have h200 : rhoN N ^ (1/200 : ℝ) = epsP (rhoN N) := by
    rw [MT_rpow_eps hρ.le 1 (by norm_num), pow_one]
  have h52 : rhoN N ^ (5/2 : ℝ) = epsP (rhoN N) ^ 500 := MT_rpow_eps hρ.le 500 (by norm_num)
  obtain ⟨hS0, hS1⟩ := hSN N hNS kc
  have h20' := h20 N hN20 kc
  simp only [h19, h25] at h20'
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set ε := epsP ρ with hεdef
  set Ψ := trialState V w kc N with hΨdef
  have hε0 : 0 < ε := MT_eps_pos hρ
  have hε1 : ε ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hkc0 : 0 < kc := by linarith
  have hL3 : 0 < L ^ 3 := by positivity
  have hL1 : 1 ≤ L := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  -- the boxes containing `P_{H,c}` and `P_L`
  obtain ⟨F, hF, hFc⟩ := MT_count hL (R := kc) (by nlinarith)
  have hLR : 1 ≤ L * ε ^ 99 := by
    by_contra hc
    have h1 : (L * ε ^ 99) ^ 3 < 1 := pow_lt_one₀ (by positivity) (not_le.1 hc) (by norm_num)
    have h2 : 1 ≤ (L * ε ^ 99) ^ 3 := by
      have : ε ^ 625 ≤ ε ^ 297 := pow_le_pow_of_le_one hε0.le hε1 (by norm_num)
      calc (1 : ℝ) = L ^ 3 * ε ^ 625 := hL3ε.symm
        _ ≤ L ^ 3 * ε ^ 297 := by gcongr
        _ = (L * ε ^ 99) ^ 3 := by ring
    linarith
  obtain ⟨FL, hFL, hFLc⟩ := MT_count hL (R := ε ^ 99) hLR
  have hPLmom : ∀ v, inPL ρ L v → ‖mom L v‖ ≤ ε ^ 99 := by
    intro v hv
    have h2 : ‖mom L v‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) := hv.2
    rw [MT_rpow_eps hρ.le 100 (by norm_num)] at h2
    change ‖mom L v‖ ≤ ε⁻¹ * ε ^ 100 at h2
    refine h2.trans (le_of_eq ?_)
    field_simp
  have hFL' : ∀ v, inPL ρ L v → v ∈ FL := fun v hv => hFL _ (hPLmom v hv)
  have hT := MT_tuples hV hN1 hC20 hF hFL' h20'
  set W := normVw2 V w with hW
  set S := ∑ v ∈ FL, if inPL ρ L v then Expect.Q Ψ [0, v] else 0 with hSdef
  set Δ := K * (5 * ε + kc⁻¹) + ((L ^ 3) ^ 2)⁻¹ * (8 * (64 * L ^ 3 * kc ^ 3) *
    (V₀ * (g / ε ^ 2) ^ 2)) with hΔdef
  have hFc' : (F.card : ℝ) ≤ 64 * L ^ 3 * kc ^ 3 := hFc.trans (le_of_eq (by ring))
  have hΔv : ∀ v ∈ FL, inPL ρ L v → |((L ^ 3) ^ 2)⁻¹ * MT_I V w ρ L kc F v - W| ≤ Δ := by
    intro v _ hv
    refine (hK N hN1 kc hkc0 hLe F hF v hv).trans ?_
    rw [hΔdef]
    have : 0 ≤ V₀ * (g / ε ^ 2) ^ 2 := mul_nonneg hV₀0 (by positivity)
    gcongr
  -- the main term against `4 ‖Vw²‖₁ |Λ|⁻¹ Σ_{v ∈ P_L} Q_Ψ(0, v)`
  have hmainW : |(∑ v ∈ FL, 4 * (L ^ 3)⁻¹ * ((L ^ 3) ^ 2)⁻¹ * Expect.Q Ψ [0, v] *
      MT_I V w ρ L kc F v) - 4 * (L ^ 3)⁻¹ * W * S| ≤ 4 * (L ^ 3)⁻¹ * Δ * S := by
    have e : (∑ v ∈ FL, 4 * (L ^ 3)⁻¹ * ((L ^ 3) ^ 2)⁻¹ * Expect.Q Ψ [0, v] *
        MT_I V w ρ L kc F v) - 4 * (L ^ 3)⁻¹ * W * S =
        ∑ v ∈ FL, (if inPL ρ L v then 4 * (L ^ 3)⁻¹ * Expect.Q Ψ [0, v] *
          (((L ^ 3) ^ 2)⁻¹ * MT_I V w ρ L kc F v - W) else 0) := by
      rw [hSdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      by_cases hv : inPL ρ L v
      · rw [ite_eq_left hv, ite_eq_left hv]; ring
      · have hI0 : MT_I V w ρ L kc F v = 0 :=
          Finset.sum_eq_zero (fun k₁ _ => Finset.sum_eq_zero (fun k₃ _ =>
            ite_eq_right (fun h => hv h.1)))
        rw [ite_eq_right hv, ite_eq_right hv, hI0]; ring
    rw [e, hSdef, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v hvF => ?_))
    have hq := MT_Q_nonneg Ψ [0, v]
    by_cases hv : inPL ρ L v
    · rw [ite_eq_left hv, ite_eq_left hv, abs_mul, abs_of_nonneg (by positivity)]
      calc 4 * (L ^ 3)⁻¹ * Expect.Q Ψ [0, v] * |((L ^ 3) ^ 2)⁻¹ * MT_I V w ρ L kc F v - W|
          ≤ 4 * (L ^ 3)⁻¹ * Expect.Q Ψ [0, v] * Δ :=
            mul_le_mul_of_nonneg_left (hΔv v hvF hv) (by positivity)
        _ = 4 * (L ^ 3)⁻¹ * Δ * Expect.Q Ψ [0, v] := by ring
    · rw [ite_eq_right hv, ite_eq_right hv, abs_zero, mul_zero]
  -- assembly
  have hSeq : (∑' v : Idx, if inPL ρ L v then Expect.Q Ψ [0, v] else 0) = S := by
    rw [hSdef]
    exact tsum_eq_sum (fun v hv => ite_eq_right (fun h => hv (hFL' _ h)))
  rw [hSeq] at hS0 hS1
  have hpart : FourLegs.part V w .fourMain kc N =
      (∑' i : Idx × Idx × Idx × Occ, if (FourLegs.Cls.fourMain).mem ρ L kc N i then
        Decomp.partTerm .A2 L V Ψ i else 0).re / (L ^ 3 * ρ ^ (5/2 : ℝ)) := rfl
  rw [hpart, hSeq, h200, h25, h52, Real.rpow_neg hρ.le, h52]
  rw [Real.rpow_neg hρ.le, h52] at hS0 hS1
  set SN := (ε ^ 500)⁻¹ * ((L ^ 3) ^ 2)⁻¹ * S with hSNdef
  have hSN' : SN ≤ CS := by
    refine hS1.trans ?_
    have : ρ ^ (1/400 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
    have h2 := mul_le_of_le_one_right hCS0 this
    rw [hCS]
    linarith
  have hP : 0 < L ^ 3 * ε ^ 500 := mul_pos hL3 (pow_pos hε0 500)
  have hSS : S = SN * ((L ^ 3) ^ 2 * ε ^ 500) := by
    rw [hSNdef]; field_simp
  set Re := (∑' i : Idx × Idx × Idx × Occ, if (FourLegs.Cls.fourMain).mem ρ L kc N i then
    Decomp.partTerm .A2 L V Ψ i else 0).re with hRe
  set Er := Re - 4 * (L ^ 3)⁻¹ * W * S with hErdef
  have hlhs : Re / (L ^ 3 * ε ^ 500) - 4 * W * SN = Er / (L ^ 3 * ε ^ 500) := by
    rw [hErdef, hSNdef]; field_simp
  rw [hlhs, abs_div, abs_of_pos hP]
  have hEr : |Er| ≤ (F.card : ℝ) ^ 2 * ((L ^ 3)⁻¹ * V₀ *
        ((FL.card : ℝ) * (C20 * ε ^ 380 / L ^ 3) +
          C20 * ε ^ 80 / (L ^ 3) ^ 2 * (SN * ((L ^ 3) ^ 2 * ε ^ 500)))) +
      4 * (L ^ 3)⁻¹ * (K * (5 * ε + kc⁻¹) +
        ((L ^ 3) ^ 2)⁻¹ * (8 * (64 * L ^ 3 * kc ^ 3) * (V₀ * (g / ε ^ 2) ^ 2))) *
        (SN * ((L ^ 3) ^ 2 * ε ^ 500)) := by
    rw [← hSS]
    have e : Er = (Re - ∑ v ∈ FL, 4 * (L ^ 3)⁻¹ * ((L ^ 3) ^ 2)⁻¹ * Expect.Q Ψ [0, v] *
        MT_I V w ρ L kc F v) + ((∑ v ∈ FL, 4 * (L ^ 3)⁻¹ * ((L ^ 3) ^ 2)⁻¹ * Expect.Q Ψ [0, v] *
        MT_I V w ρ L kc F v) - 4 * (L ^ 3)⁻¹ * W * S) := by
      rw [hErdef]; ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add hT hmainW)
  exact MT_alg hL3 hε0 hε1 hkc hL3ε (Nat.cast_nonneg _) hFc' (Nat.cast_nonneg _)
    (hFLc.trans (le_of_eq (by ring))) hV₀0 hC20 hK0 hS0 hSN' hEr

/-- Lemma 10.2 [101], (10.10) [resultinMk1k2]:
`lim sup_{k_c} lim sup_N` of the main term is at most `4 ‖Vw²‖₁ g₀^{3/2} / (3π²)`. -/
theorem Lemma10_2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Section4.limsup2 (fun kc N => FourLegs.part V w .fourMain kc N) ≤
      ((4 * normVw2 V w * Section4.G V w / 3 : ℝ) : EReal) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C, hC, N₀, h⟩ := Lemma10_2_rate hV hw
  obtain ⟨CS0, hCS0, NS, hSN⟩ := MT_SN hg
  set W := normVw2 V w with hWdef
  have hW : 0 ≤ W := integral_nonneg (fun x => abs_nonneg _)
  set R := 4 * W * Section4.G V w / 3 with hR
  have hbound : ∀ kc : ℝ, 1 ≤ kc → ∀ N ≥ max N₀ NS, FourLegs.part V w .fourMain kc N ≤
      R + 4 * W * CS0 * rhoN N ^ (1/400 : ℝ) +
        C * (rhoN N ^ (1/200 : ℝ) + kc⁻¹ + kc ^ 6 * rhoN N ^ (2/5 : ℝ)) := by
    intro kc hkc N hN
    have h1 := (abs_le.1 (h N (le_of_max_le_left hN) kc hkc)).2
    have h2 := (hSN N (le_of_max_le_right hN) kc).2
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * W)
    have hG : 4 * W * (g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) + CS0 * rhoN N ^ (1/400 : ℝ)) =
        R + 4 * W * CS0 * rhoN N ^ (1/400 : ℝ) := by
      rw [hR, Section4.G]; ring
    linarith
  have hin : ∀ kc : ℝ, 1 ≤ kc →
      limsup (fun N : ℕ => (FourLegs.part V w .fourMain kc N : EReal)) atTop ≤
        ((R + C * kc⁻¹ : ℝ) : EReal) := by
    intro kc hkc
    have hT : Tendsto (fun N : ℕ => R + 4 * W * CS0 * rhoN N ^ (1/400 : ℝ) +
        C * (rhoN N ^ (1/200 : ℝ) + kc⁻¹ + kc ^ 6 * rhoN N ^ (2/5 : ℝ))) atTop
        (𝓝 (R + C * kc⁻¹)) := by
      have h1 := MT_tendsto_rpow (a := 1/400) (by norm_num)
      have h2 := MT_tendsto_rpow (a := 1/200) (by norm_num)
      have h3 := MT_tendsto_rpow (a := 2/5) (by norm_num)
      have := ((h1.const_mul (4 * W * CS0)).const_add R).add
        (((h2.add_const kc⁻¹).add (h3.const_mul (kc ^ 6))).const_mul C)
      simpa using this
    have hT' : Tendsto (fun N : ℕ => ((R + 4 * W * CS0 * rhoN N ^ (1/400 : ℝ) +
        C * (rhoN N ^ (1/200 : ℝ) + kc⁻¹ + kc ^ 6 * rhoN N ^ (2/5 : ℝ)) : ℝ) : EReal)) atTop
        (𝓝 ((R + C * kc⁻¹ : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp hT
    calc limsup (fun N : ℕ => (FourLegs.part V w .fourMain kc N : EReal)) atTop
        ≤ limsup (fun N : ℕ => ((R + 4 * W * CS0 * rhoN N ^ (1/400 : ℝ) +
            C * (rhoN N ^ (1/200 : ℝ) + kc⁻¹ + kc ^ 6 * rhoN N ^ (2/5 : ℝ)) : ℝ) : EReal))
            atTop := by
          refine limsup_le_limsup ?_
          filter_upwards [eventually_ge_atTop (max N₀ NS)] with N hN
          exact EReal.coe_le_coe_iff.2 (hbound kc hkc N hN)
      _ = ((R + C * kc⁻¹ : ℝ) : EReal) := hT'.limsup_eq
  have hT2 : Tendsto (fun kc : ℝ => ((R + C * kc⁻¹ : ℝ) : EReal)) atTop (𝓝 (R : EReal)) := by
    have : Tendsto (fun kc : ℝ => R + C * kc⁻¹) atTop (𝓝 R) := by
      simpa using (tendsto_inv_atTop_zero.const_mul C).const_add R
    exact (continuous_coe_real_ereal.tendsto _).comp this
  unfold Section4.limsup2
  calc limsup (fun kc : ℝ => limsup (fun N : ℕ =>
        (FourLegs.part V w .fourMain kc N : EReal)) atTop) atTop
      ≤ limsup (fun kc : ℝ => ((R + C * kc⁻¹ : ℝ) : EReal)) atTop := by
        refine limsup_le_limsup ?_
        filter_upwards [eventually_ge_atTop 1] with kc hkc
        exact hin kc hkc
    _ = (R : EReal) := hT2.limsup_eq

end LHYUpper
