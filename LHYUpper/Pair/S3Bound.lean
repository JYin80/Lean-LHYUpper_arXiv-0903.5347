import LHYUpper.Fock.DecompDefs
import LHYUpper.Fock.Expect
import LHYUpper.Riemann.ScaledLimits
import LHYUpper.Scattering.Solution
import LHYUpper.TrialState.MStar
import LHYUpper.Pair.Sums
import LHYUpper.Pair.UUVV
import LHYUpper.Particles.Lower
import LHYUpper.Particles.Lemma55

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Elementary facts on `ρ_N`, `L_N`, the regions and `λ` -/

/-- `ρ_N^a → 0` for `a > 0`. -/
private lemma S3Bound_tendsto_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (mul_pos (by norm_num : (0 : ℝ) < 8 / 17) ha)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr' (Eventually.of_forall fun N => ?_)
  simp only [Function.comp, rhoN]
  rw [← Real.rpow_mul (Nat.cast_nonneg N), neg_mul]

/-- Eventually `ρ_N^a < c`, for `a, c > 0`. -/
private lemma S3Bound_ev_rpow_lt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, rhoN N ^ a < c :=
  (S3Bound_tendsto_rpow ha).eventually (gt_mem_nhds hc)

/-- `x^b ≤ x^a` for `0 < x ≤ 1`, `a ≤ b`. -/
private lemma S3Bound_rpow_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {a b : ℝ} (h : a ≤ b) :
    x ^ b ≤ x ^ a :=
  Real.rpow_le_rpow_of_exponent_ge hx hx1 h

/-- `L_N ρ_N^{1/2} = (ρ_N^{13/24})⁻¹`. -/
private lemma S3Bound_L_sqrt {N : ℕ} (hN : 1 ≤ N) :
    LN N * rhoN N ^ (1/2 : ℝ) = (rhoN N ^ (13/24 : ℝ))⁻¹ := by
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  rw [LN, ← Real.rpow_add hρ, ← Real.rpow_neg hρ.le]
  norm_num

/-- Eventually `2π ≤ L_N ρ_N^{1/2}`. -/
private lemma S3Bound_ev_L : ∀ᶠ N : ℕ in atTop, 2 * π ≤ LN N * rhoN N ^ (1/2 : ℝ) := by
  filter_upwards [S3Bound_ev_rpow_lt (by norm_num : (0 : ℝ) < 13 / 24)
    (inv_pos.2 (by positivity : (0 : ℝ) < 2 * π)), eventually_ge_atTop 1] with N h hN
  have hρ : 0 < rhoN N := (Particles_rhoN_LN hN).2.1
  rw [S3Bound_L_sqrt hN, le_inv_comm₀ (by positivity) (Real.rpow_pos_of_pos hρ _)]
  exact h.le

/-- `ε^{-1}ρ^{1/2} = ρ^{1/2 − 1/200}`, the outer radius of `P_L`. -/
private lemma S3Bound_R_eq {ρ : ℝ} (hρ : 0 < ρ) :
    (epsP ρ)⁻¹ * ρ ^ (1/2 : ℝ) = ρ ^ (1/2 - 1/200 : ℝ) := by
  rw [epsP, ← Real.rpow_neg hρ.le, ← Real.rpow_add hρ]
  norm_num

/-- `1 ≤ L_N` for `N ≥ 1`. -/
private lemma S3Bound_one_le_L {N : ℕ} (hN : 1 ≤ N) : 1 ≤ LN N := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)

/-- `mom L (u − v) = mom L u − mom L v`. -/
private lemma S3Bound_mom_sub (L : ℝ) (u v : Idx) : mom L (u - v) = mom L u - mom L v := by
  ext i
  simp [mom, mul_sub]

/-- `V_{v−u} = V_{u−v}`. -/
private lemma S3Bound_V_swap {V : R3 → ℝ} (hV : PotentialHyp V) (L : ℝ) (u v : Idx) :
    ft V (mom L (v - u)) = ft V (mom L (u - v)) := by
  rw [← scat_ft_V_neg hV, S3Bound_mom_sub, S3Bound_mom_sub, neg_sub]

/-- `|V_p| ≤ V₀ = ∫ V`. -/
private lemma S3Bound_abs_V_le {V : R3 → ℝ} (hV : PotentialHyp V) (p : R3) :
    |(ft V p).re| ≤ ∫ x, V x :=
  (Complex.abs_re_le_norm _).trans (scat_ft_V_norm_le hV p)

/-- `Q_Ψ(u₁, …, u_s) ≥ 0`. -/
private lemma S3Bound_Q_nonneg (Ψ : Occ → ℂ) (us : List Idx) : 0 ≤ Expect.Q Ψ us :=
  tsum_nonneg fun α => mul_nonneg (List.prod_nonneg (by simp)) (by positivity)

/-- `Q_Ψ(v, u) = Q_Ψ(u, v)`. -/
private lemma S3Bound_Q_comm (Ψ : Occ → ℂ) (u v : Idx) :
    Expect.Q Ψ [v, u] = Expect.Q Ψ [u, v] := by
  unfold Expect.Q
  refine tsum_congr fun α => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil]
  ring

/-- `P` excludes `0`. -/
private lemma S3Bound_inP_ne_zero {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inP ρ L n) : n ≠ 0 := by
  rcases h with h | h | h
  · exact Regions_PL_ne_zero hρ h
  · exact Regions_PI_ne_zero hρ h
  · exact Regions_PH_ne_zero hρ h

/-- `P` is symmetric. -/
private lemma S3Bound_inP_neg {ρ L : ℝ} {n : Idx} : inP ρ L (-n) ↔ inP ρ L n := by
  unfold inP
  rw [Regions_PL_neg, Regions_PI_neg, Regions_PH_neg]

/-- `P_I ∪ P_H ⊆ P`. -/
private lemma S3Bound_IH_P {ρ L : ℝ} {n : Idx} (h : inPI ρ L n ∨ inPH ρ L n) : inP ρ L n := by
  rcases h with h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- For `u ∈ P_L` and `v ∈ P_I ∪ P_H`: `u ≠ v` and `u + v ≠ 0`. -/
private lemma S3Bound_L_IH_ne {ρ L : ℝ} (hρ : 0 < ρ) {u v : Idx} (hu : inPL ρ L u)
    (hv : inPI ρ L v ∨ inPH ρ L v) : u ≠ v ∧ u + v ≠ 0 := by
  have key : ∀ n : Idx, inPL ρ L n → ¬ (inPI ρ L n ∨ inPH ρ L n) := fun n hn h => by
    rcases h with h | h
    · exact Regions_PL_PI hn h
    · exact Regions_PL_PH hρ hn h
  refine ⟨fun h => key v (h ▸ hu) hv, fun h => ?_⟩
  have hv' : v = -u := eq_neg_of_add_eq_zero_right h
  rw [hv', Regions_PI_neg, Regions_PH_neg] at hv
  exact key u hu hv

/-- On `P_L`, `λ_u = λ_{P_L}(g₀, ρ, p_u)`. -/
private lemma S3Bound_lam_PL (V w : R3 → ℝ) {ρ L : ℝ} {n : Idx} (h : inPL ρ L n) :
    lam V w ρ L n = lamPL (g0 V w) ρ (mom L n) := by
  simp [lam, lamPL, h]

/-- On `P_L`, `|λ_u| ≤ g₀|p_u|^{-2}`, (5.9) [ublambda]. -/
private lemma S3Bound_lam_PL_le {V w : R3 → ℝ} (hg : 0 < g0 V w) {ρ L : ℝ} (hρ : 0 < ρ)
    {n : Idx} (h : inPL ρ L n) (hn : 0 < ‖mom L n‖) :
    |lam V w ρ L n| ≤ g0 V w / ‖mom L n‖ ^ 2 := by
  rw [lam]
  simp only [h, ↓reduceIte]
  have hq : 0 < ‖mom L n‖ ^ 2 := by positivity
  set a : ℝ := 4 * ρ * g0 V w / ‖mom L n‖ ^ 2 with ha
  have ha0 : 0 ≤ a := by positivity
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + a)
  have hs1 : 1 ≤ Real.sqrt (1 + a) := Real.one_le_sqrt.2 (by linarith)
  generalize Real.sqrt (1 + a) = s at hs hs1
  have hga : g0 V w / ‖mom L n‖ ^ 2 = a / (4 * ρ) := by
    rw [ha]
    field_simp
  rw [hga, abs_div, abs_div, abs_of_pos hρ, abs_of_pos (by linarith : 0 < 1 + s),
    abs_of_nonpos (by linarith : 1 - s ≤ 0), div_div, div_le_div_iff₀ (by positivity)
    (by positivity)]
  have h1 : 0 ≤ (s - 1) * (s - 1) * (s + 3) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h2 : -(1 - s) * 4 ≤ a * (1 + s) := by nlinarith
  nlinarith

/-- `‖p_n‖^{-2} = (‖p_n‖²)⁻¹`. -/
private lemma S3Bound_rpow_neg_two (x : ℝ) (hx : 0 ≤ x) : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- On `P_L`, `Q_Ψ(u) ≤ ⌈m_c⌉`, from `α(u) ≤ α*(u) ≤ ⌈m_c⌉` on `M`, (3.8) [defmc]. -/
private lemma S3Bound_Q_PL_le (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) :
    Expect.Q (trialState V w kc N) [u] ≤ ⌈mc (rhoN N)⌉₊ := by
  have hΨ := Normalization_isNState V w kc hN
  have hρ := (Particles_rhoN_LN hN).2.1
  have hs : Summable fun α : Occ => ‖trialState V w kc N α‖ ^ 2 := hΨ.1.summable
  have hle : ∀ α : Occ, (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) * ‖trialState V w kc N α‖ ^ 2 := by
    intro α
    by_cases hM : InM (rhoN N) (LN N) kc N α
    · have h1 := MStar_PL_ceil hρ hM hu
      have h2 : α u ≤ alphaStar α u := le_max_left _ _
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h2.trans h1) (by positivity)
    · have hz : trialState V w kc N α = 0 := by
        unfold trialState
        simp [hM]
      simp [hz]
  have hA : Summable fun α : Occ => (α u : ℝ) * ‖trialState V w kc N α‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun α => by positivity) hle (hs.mul_left _)
  have h := hA.tsum_le_tsum hle (hs.mul_left _)
  rw [tsum_mul_left, hΨ.1.tsum_eq, mul_one] at h
  simpa [Expect.Q] using h

/-! ### Nonnegative series on `Idx × Idx` -/

/-- `(u, v) ↦ Q_Ψ(u, v)` is summable on `Idx × Idx` for a normalized `N`-particle state. -/
private lemma S3Bound_Q2_summable {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) :
    Summable fun uv : Idx × Idx => Expect.Q Ψ [uv.1, uv.2] := by
  have hfib : ∀ α : Occ, HasSum (fun uv : Idx × Idx => (α uv.1 : ℝ) * α uv.2 * ‖Ψ α‖ ^ 2)
      ((N : ℝ) ^ 2 * ‖Ψ α‖ ^ 2) := by
    intro α
    have h : HasSum (fun uv : Idx × Idx => (α uv.1 : ℝ) * α uv.2 * ‖Ψ α‖ ^ 2)
        (∑ uv ∈ α.support ×ˢ α.support, (α uv.1 : ℝ) * α uv.2 * ‖Ψ α‖ ^ 2) :=
      hasSum_sum_of_ne_finset_zero (fun uv huv => by
        rw [Finset.mem_product, not_and_or] at huv
        rcases huv with h | h <;> simp [Finsupp.notMem_support_iff.mp h])
    convert h using 1
    rw [← Finset.sum_mul, Finset.sum_product]
    simp only
    rw [← Finset.sum_mul_sum]
    by_cases hz : Ψ α = 0
    · simp [hz]
    · have hn := hΨ.2 α hz
      have e : (α.num : ℝ) = ∑ p ∈ α.support, (α p : ℝ) := by simp [Occ.num, Finsupp.sum]
      rw [← e, hn, sq]
  have hF : Summable (fun x : Occ × (Idx × Idx) => (x.1 x.2.1 : ℝ) * x.1 x.2.2 * ‖Ψ x.1‖ ^ 2) := by
    rw [summable_prod_of_nonneg (fun x => by positivity)]
    refine ⟨fun α => (hfib α).summable, ?_⟩
    simpa [(hfib _).tsum_eq] using hΨ.1.summable.mul_left ((N : ℝ) ^ 2)
  have h := hF.prod_symm.prod
  refine h.congr fun uv => ?_
  simp [Expect.Q, mul_assoc]

/-- A nonnegative family on `Idx × Idx` dominated by `a(u) s(u, v)`, with `a` summable and every
`s(u, ·)` summable with sum at most `B`, is summable with sum at most `B Σ_u a(u)`. -/
private lemma S3Bound_fiber {a : Idx → ℝ} {s : Idx → Idx → ℝ} {f : Idx × Idx → ℝ} {B : ℝ}
    (ha0 : ∀ u, 0 ≤ a u) (has : Summable a) (hs0 : ∀ u v, 0 ≤ s u v)
    (hss : ∀ u, Summable (s u)) (hsB : ∀ u, ∑' v, s u v ≤ B) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x, f x ≤ a x.1 * s x.1 x.2) :
    Summable f ∧ ∑' x, f x ≤ B * ∑' u, a u := by
  have hh0 : ∀ x : Idx × Idx, 0 ≤ a x.1 * s x.1 x.2 := fun x => mul_nonneg (ha0 _) (hs0 _ _)
  have hfib : ∀ u, Summable fun v => a (u, v).1 * s (u, v).1 (u, v).2 := fun u =>
    (hss u).mul_left (a u)
  have hmarg : ∀ u, ∑' v, a (u, v).1 * s (u, v).1 (u, v).2 ≤ a u * B := fun u => by
    simp only
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hsB u) (ha0 u)
  have hh : Summable fun x : Idx × Idx => a x.1 * s x.1 x.2 := by
    rw [summable_prod_of_nonneg (fun x => hh0 x)]
    refine ⟨hfib, Summable.of_nonneg_of_le (fun u => tsum_nonneg fun v => hh0 _) hmarg
      (has.mul_right B)⟩
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hf hh
  refine ⟨hfs, ?_⟩
  calc ∑' x, f x ≤ ∑' x : Idx × Idx, a x.1 * s x.1 x.2 := hfs.tsum_le_tsum hf hh
    _ = ∑' u, ∑' v, a (u, v).1 * s (u, v).1 (u, v).2 := hh.tsum_prod' hfib
    _ ≤ ∑' u, a u * B :=
        (hh.prod).tsum_le_tsum hmarg (has.mul_right B)
    _ = B * ∑' u, a u := by rw [tsum_mul_right, mul_comm]

/-- The lattice points with `‖p_n‖ ≤ R` form a finite set. -/
private lemma S3Bound_finite_ball {L R : ℝ} (hL : 0 < L) : {n : Idx | ‖mom L n‖ ≤ R}.Finite := by
  set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
  refine (Set.finite_Icc (fun _ : Fin 3 => -B) (fun _ => B)).subset ?_
  intro n hn
  have hi : ∀ i : Fin 3, |(n i : ℝ)| ≤ B := by
    intro i
    have h1 : |(mom L n).ofLp i| ≤ R := by
      have := PiLp.norm_apply_le (mom L n) i
      rw [Real.norm_eq_abs] at this
      exact this.trans hn
    rw [Cells_mom_apply, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / L)] at h1
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

/-- A family on `Idx` supported in `{‖p_n‖ ≤ R}` is summable. -/
private lemma S3Bound_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
    (hf : ∀ n, f n ≠ 0 → ‖mom L n‖ ≤ R) : Summable f := by
  have hfin := S3Bound_finite_ball (R := R) hL
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  by_contra h
  exact hn (hfin.mem_toFinset.2 (hf n h))

/-- `ρ^{-a} X ≤ Y` gives `X ≤ ρ^a Y`. -/
private lemma S3Bound_unscale {ρ a X Y : ℝ} (hρ : 0 < ρ) (h : ρ ^ (-a) * X ≤ Y) :
    X ≤ ρ ^ a * Y := by
  have hp : 0 < ρ ^ a := Real.rpow_pos_of_pos hρ a
  rw [Real.rpow_neg hρ.le] at h
  have := mul_le_mul_of_nonneg_left h hp.le
  rwa [← mul_assoc, mul_inv_cancel₀ hp.ne', one_mul] at this

/-! ### The four bounds of (7.64) [temp8.70] with summability -/

/-- First term of (7.64) [temp8.70], with the summability of the family. -/
private lemma S3Bound_Q2_core {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      Summable (fun uv : Idx × Idx =>
          if inP (rhoN N) (LN N) uv.1 ∧ inP (rhoN N) (LN N) uv.2 then
            |lam V w (rhoN N) (LN N) uv.1 * lam V w (rhoN N) (LN N) uv.2| *
              Expect.Q (trialState V w kc N) [uv.1, uv.2] else 0) ∧
      rhoN N ^ 2 * (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
          if inP (rhoN N) (LN N) uv.1 ∧ inP (rhoN N) (LN N) uv.2 then
            |lam V w (rhoN N) (LN N) uv.1 * lam V w (rhoN N) (LN N) uv.2| *
              Expect.Q (trialState V w kc N) [uv.1, uv.2] else 0))
        ≤ C * rhoN N ^ (5/2 + 1/200 : ℝ) := by
  obtain ⟨C, hC, N₁, h61⟩ := Eq6_1 (scat_g0_pos hV hw)
  obtain ⟨N₂, hlam⟩ := Pair_rho_lam_le V w
  refine ⟨C, hC, max (max N₁ N₂) 1, fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  set ρ := rhoN N with hρdef
  set Ψ := trialState V w kc N with hΨdef
  set f : Idx × Idx → ℝ := fun uv =>
    if inP ρ (LN N) uv.1 ∧ inP ρ (LN N) uv.2 then
      |lam V w ρ (LN N) uv.1 * lam V w ρ (LN N) uv.2| * Expect.Q Ψ [uv.1, uv.2] else 0 with hf
  set g : Idx × Idx → ℝ := fun uv =>
    if uv.1 ≠ 0 ∧ uv.2 ≠ 0 then Expect.Q Ψ [uv.1, uv.2] else 0 with hgdef
  have hg0 : ∀ x, 0 ≤ g x := fun x => by
    simp only [hgdef]
    split_ifs <;> simp [S3Bound_Q_nonneg]
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 (fun x => by
      simp only [hgdef]
      split_ifs <;> simp [S3Bound_Q_nonneg]) (S3Bound_Q2_summable hΨ)
  have hf0 : ∀ x, 0 ≤ ρ ^ 2 * f x := fun x => by
    refine mul_nonneg (sq_nonneg _) ?_
    simp only [hf]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (S3Bound_Q_nonneg _ _)
    · exact le_rfl
  have hle : ∀ x, ρ ^ 2 * f x ≤ g x := fun x => by
    simp only [hf, hgdef]
    by_cases h : inP ρ (LN N) x.1 ∧ inP ρ (LN N) x.2
    · have hne : x.1 ≠ 0 ∧ x.2 ≠ 0 :=
        ⟨S3Bound_inP_ne_zero hρ h.1, S3Bound_inP_ne_zero hρ h.2⟩
      rw [ite_eq_left h, ite_eq_left hne]
      have h1 := hlam N hN₂ x.1 h.1
      have h2 := hlam N hN₂ x.2 h.2
      have hQ := S3Bound_Q_nonneg Ψ [x.1, x.2]
      have e : ρ ^ 2 * (|lam V w ρ (LN N) x.1 * lam V w ρ (LN N) x.2| * Expect.Q Ψ [x.1, x.2]) =
          (|ρ * lam V w ρ (LN N) x.1| * |ρ * lam V w ρ (LN N) x.2|) * Expect.Q Ψ [x.1, x.2] := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hρ]
        ring
      rw [e]
      have : |ρ * lam V w ρ (LN N) x.1| * |ρ * lam V w ρ (LN N) x.2| ≤ 1 := by
        calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      nlinarith
    · rw [ite_eq_right h, mul_zero]
      exact hg0 x
  have hfs' : Summable fun x => ρ ^ 2 * f x := Summable.of_nonneg_of_le hf0 hle hgs
  have hfs : Summable f := (summable_mul_left_iff (by positivity : ρ ^ 2 ≠ 0)).1 hfs'
  refine ⟨hfs, ?_⟩
  have h1 : ρ ^ 2 * (((LN N ^ 3) ^ 2)⁻¹ * ∑' x, f x) ≤ ((LN N ^ 3) ^ 2)⁻¹ * ∑' x, g x := by
    rw [mul_left_comm, ← tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (hfs'.tsum_le_tsum hle hgs) (by positivity)
  have h2 : ∑' x, g x = ∑' u : Idx, ∑' v : Idx,
      (if u ≠ 0 ∧ v ≠ 0 then Expect.Q Ψ [u, v] else 0) :=
    hgs.tsum_prod' fun u => hgs.prod_factor u
  have h3 := h61 N hN₁ kc
  rw [← hρdef, ← hΨdef, mul_assoc, ← h2] at h3
  have h4 := S3Bound_unscale hρ h3
  refine h1.trans (h4.trans (le_of_eq ?_))
  rw [Real.rpow_add hρ]
  ring

/-- `ρ^{5/2 + c} = ρ · ρ^{3/2} · ρ^c`. -/
private lemma S3Bound_pow_split {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) :
    ρ ^ (5/2 + c : ℝ) = ρ * ρ ^ (3/2 : ℝ) * ρ ^ c := by
  rw [Real.rpow_add hρ, show (5/2 : ℝ) = 1 + 3/2 by norm_num, Real.rpow_add hρ, Real.rpow_one]

/-- Facts (1)–(2) before (7.65) [temp8.73] at `ρ = ρ_N`, `L = L_N`: for `u ∈ P`, `|ρλ_u| ≤ 1`, and
for every `u`, `Σ_{v ≠ 0} |λ_v V_{u−v}|` is summable with sum at most `K|Λ|`. -/
private lemma S3Bound_facts {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N ∧
      (∀ u : Idx, inP (rhoN N) (LN N) u → |rhoN N * lam V w (rhoN N) (LN N) u| ≤ 1) ∧
      (∀ u : Idx, Summable (fun v : Idx => if v ≠ 0 then
          |lam V w (rhoN N) (LN N) v * (ft V (mom (LN N) u - mom (LN N) v)).re| else 0) ∧
        ∑' v : Idx, (if v ≠ 0 then
          |lam V w (rhoN N) (LN N) v * (ft V (mom (LN N) u - mom (LN N) v)).re| else 0) ≤
          K * LN N ^ 3) ∧
      Summable (fun nm : Idx × Idx => if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then
          |lam V w (rhoN N) (LN N) nm.1 * (ft V (mom (LN N) (nm.1 - nm.2))).re *
            lam V w (rhoN N) (LN N) nm.2| else 0) ∧
      ((LN N ^ 3) ^ 2)⁻¹ * (∑' nm : Idx × Idx, if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then
          |lam V w (rhoN N) (LN N) nm.1 * (ft V (mom (LN N) (nm.1 - nm.2))).re *
            lam V w (rhoN N) (LN N) nm.2| else 0) ≤ K := by
  obtain ⟨K, hK, N₁, hs⟩ := Pair_sum_lamV hV hw
  obtain ⟨N₂, hlam⟩ := Pair_rho_lam_le V w
  refine ⟨K, hK, max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₁ : N₁ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  obtain ⟨h1, h2, h3⟩ := hs N hN₁
  have hL := (Particles_rhoN_LN hN1).2.2.2
  refine ⟨hN1, hlam N hN₂, fun u => ⟨(h1 (mom (LN N) u)).1, ?_⟩, h2, h3⟩
  have h := (h1 (mom (LN N) u)).2
  have hL3 : 0 < LN N ^ 3 := by positivity
  rw [inv_mul_le_iff₀ hL3] at h
  linarith

/-- Second term of (7.64) [temp8.70], with the summability of the family. -/
private lemma S3Bound_Q1_core {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      Summable (fun uv : Idx × Idx =>
          if (inPI (rhoN N) (LN N) uv.1 ∨ inPH (rhoN N) (LN N) uv.1) ∧
              inP (rhoN N) (LN N) uv.2 then
            |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
              lam V w (rhoN N) (LN N) uv.2| * Expect.Q (trialState V w kc N) [uv.1] else 0) ∧
      rhoN N ^ 2 * (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
          if (inPI (rhoN N) (LN N) uv.1 ∨ inPH (rhoN N) (LN N) uv.1) ∧
              inP (rhoN N) (LN N) uv.2 then
            |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
              lam V w (rhoN N) (LN N) uv.2| * Expect.Q (trialState V w kc N) [uv.1] else 0))
        ≤ C * rhoN N ^ (5/2 + 1/200 : ℝ) := by
  obtain ⟨K, hK, N₁, hfacts⟩ := S3Bound_facts hV hw
  obtain ⟨C₅, hC₅, N₅, h5⟩ := Thm5_1 (scat_g0_pos hV hw)
  refine ⟨K * C₅, by positivity, max N₁ N₅, fun N hN kc => ?_⟩
  have hN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN₅ : N₅ ≤ N := le_trans (le_max_right _ _) hN
  obtain ⟨hN1, hlam, hs, -, -⟩ := hfacts N hN₁
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN1
  have hQs : Summable (fun n : Idx => Expect.Q (trialState V w kc N) [n]) :=
    (Particles_hasSum_Q V w kc hN1).summable
  set ρ := rhoN N with hρdef
  set Ψ := trialState V w kc N with hΨdef
  set a : Idx → ℝ := fun u =>
    if inPI ρ (LN N) u ∨ inPH ρ (LN N) u then Expect.Q Ψ [u] else 0 with hadef
  set sv : Idx → Idx → ℝ := fun u v => if v ≠ 0 then
    |lam V w ρ (LN N) v * (ft V (mom (LN N) u - mom (LN N) v)).re| else 0 with hsvdef
  set f : Idx × Idx → ℝ := fun uv =>
    if (inPI ρ (LN N) uv.1 ∨ inPH ρ (LN N) uv.1) ∧ inP ρ (LN N) uv.2 then
      |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w ρ (LN N) uv.1 *
        lam V w ρ (LN N) uv.2| * Expect.Q Ψ [uv.1] else 0 with hf
  have ha0 : ∀ u, 0 ≤ a u := fun u => by
    simp only [hadef]
    split_ifs
    · exact S3Bound_Q_nonneg _ _
    · exact le_rfl
  have has : Summable a := Summable.of_nonneg_of_le ha0 (fun u => by
      simp only [hadef]
      split_ifs
      · exact le_rfl
      · exact S3Bound_Q_nonneg _ _) hQs
  have hs0 : ∀ u v, 0 ≤ sv u v := fun u v => by
    simp only [hsvdef]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hf0 : ∀ x, 0 ≤ ρ * f x := fun x => by
    refine mul_nonneg hρ.le ?_
    simp only [hf]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (S3Bound_Q_nonneg _ _)
    · exact le_rfl
  have hle : ∀ x : Idx × Idx, ρ * f x ≤ a x.1 * sv x.1 x.2 := fun x => by
    simp only [hf, hadef, hsvdef]
    by_cases h : (inPI ρ (LN N) x.1 ∨ inPH ρ (LN N) x.1) ∧ inP ρ (LN N) x.2
    · rw [ite_eq_left h, ite_eq_left h.1, ite_eq_left (S3Bound_inP_ne_zero hρ h.2)]
      have h1 := hlam x.1 (S3Bound_IH_P h.1)
      have hQ := S3Bound_Q_nonneg Ψ [x.1]
      have e : ρ * (|(ft V (mom (LN N) (x.1 - x.2))).re * lam V w ρ (LN N) x.1 *
          lam V w ρ (LN N) x.2| * Expect.Q Ψ [x.1]) = |ρ * lam V w ρ (LN N) x.1| *
            (Expect.Q Ψ [x.1] * |lam V w ρ (LN N) x.2 *
              (ft V (mom (LN N) x.1 - mom (LN N) x.2)).re|) := by
        simp only [S3Bound_mom_sub, abs_mul, abs_of_pos hρ]
        ring
      rw [e]
      have h0 : 0 ≤ Expect.Q Ψ [x.1] * |lam V w ρ (LN N) x.2 *
          (ft V (mom (LN N) x.1 - mom (LN N) x.2)).re| := mul_nonneg hQ (abs_nonneg _)
      calc _ ≤ 1 * (Expect.Q Ψ [x.1] * |lam V w ρ (LN N) x.2 *
            (ft V (mom (LN N) x.1 - mom (LN N) x.2)).re|) := mul_le_mul_of_nonneg_right h1 h0
        _ = _ := one_mul _
    · rw [ite_eq_right h, mul_zero]
      exact mul_nonneg (ha0 _) (hs0 _ _)
  obtain ⟨hfs', hsum⟩ := S3Bound_fiber ha0 has hs0 (fun u => (hs u).1) (fun u => (hs u).2) hf0
    hle
  have hfs : Summable f := (summable_mul_left_iff hρ.ne').1 hfs'
  refine ⟨hfs, ?_⟩
  have h5' := (h5 N hN₅ kc).1
  rw [← hρdef, ← hΨdef, mul_assoc] at h5'
  have hA := S3Bound_unscale hρ h5'
  have hL3 : 0 < LN N ^ 3 := by positivity
  rw [tsum_mul_left] at hsum
  calc ρ ^ 2 * (((LN N ^ 3) ^ 2)⁻¹ * ∑' x, f x)
      = ρ * ((LN N ^ 3)⁻¹ * ((LN N ^ 3)⁻¹ * (ρ * ∑' x, f x))) := by ring
    _ ≤ ρ * ((LN N ^ 3)⁻¹ * ((LN N ^ 3)⁻¹ * (K * LN N ^ 3 * ∑' u, a u))) := by gcongr
    _ = ρ * K * ((LN N ^ 3)⁻¹ * ∑' u, a u) := by field_simp
    _ ≤ ρ * K * (ρ ^ (3/2 : ℝ) * (C₅ * ρ ^ (1/200 : ℝ))) := by gcongr
    _ = K * C₅ * ρ ^ (5/2 + 1/200 : ℝ) := by rw [S3Bound_pow_split hρ]; ring

/-- `ρ² m_c (ρ^{1/2 − 1/200})² = ρ^{3 − 3/200}`. -/
private lemma S3Bound_pow_PL {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ 2 * mc ρ * (ρ ^ (1/2 - 1/200 : ℝ)) ^ 2 = ρ ^ (3 - 3/200 : ℝ) := by
  rw [mc, ← Real.rpow_natCast ρ 2, ← Real.rpow_natCast (ρ ^ (1/2 - 1/200 : ℝ)) 2,
    ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
  norm_num

/-- On `P_L`, `x_u/(1 − x_u) ≥ 0` with `x_u = (ρλ_u)²`, (5.9) [ublambda]. -/
private lemma S3Bound_X_nonneg {V w : R3 → ℝ} (hg : 0 < g0 V w) {ρ L : ℝ} (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) {n : Idx} (hn : inPL ρ L n) :
    0 ≤ (ρ * lam V w ρ L n) ^ 2 / (1 - (ρ * lam V w ρ L n) ^ 2) := by
  obtain ⟨h1, h2⟩ := Particles_rho_lam_PL hg hρ hρ1 hn
  have he : 0 < epsP ρ / (1 + Real.sqrt (g0 V w)) := by
    have : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
    positivity
  refine div_nonneg (sq_nonneg _) ?_
  nlinarith

/-- Third term of (7.64) [temp8.70], with the summability of the family. -/
private lemma S3Bound_PL_core {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      Summable (fun uv : Idx × Idx =>
          if inPL (rhoN N) (LN N) uv.1 ∧ inPL (rhoN N) (LN N) uv.2 then
            |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
              lam V w (rhoN N) (LN N) uv.2| *
              (Expect.Q (trialState V w kc N) [uv.1] + 1) else 0) ∧
      rhoN N ^ 2 * (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
          if inPL (rhoN N) (LN N) uv.1 ∧ inPL (rhoN N) (LN N) uv.2 then
            |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
              lam V w (rhoN N) (LN N) uv.2| *
              (Expect.Q (trialState V w kc N) [uv.1] + 1) else 0))
        ≤ C * rhoN N ^ (3 - 3/200 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨K₂, hK₂, hball⟩ := sum_norm_rpow_le (s := 2) (by norm_num)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 S3Bound_ev_L
  have hV0 : 0 ≤ ∫ x, V x := (abs_nonneg _).trans (S3Bound_abs_V_le hV 0)
  refine ⟨3 * (∫ x, V x) * g0 V w ^ 2 * K₂ ^ 2, by positivity, max N₁ 1, fun N hN kc => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have h2π := hN₁ N (le_trans (le_max_left _ _) hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set Ψ := trialState V w kc N with hΨdef
  have hε0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hε1 : epsP ρ ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hsq : 0 < ρ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  set R := (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) with hRdef
  have hR0 : 0 < R := by positivity
  have h2πR : 2 * π ≤ L * R := by
    refine h2π.trans ?_
    have h1 : 1 ≤ (epsP ρ)⁻¹ := (one_le_inv₀ hε0).2 hε1
    calc L * ρ ^ (1 / 2 : ℝ) = L * (1 * ρ ^ (1 / 2 : ℝ)) := by rw [one_mul]
      _ ≤ L * R := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 hsq.le) hL.le
  have hbB := hball L R hR0 h2πR
  rw [show (3 : ℝ) - 2 = 1 by norm_num, Real.rpow_one] at hbB
  set bb : Idx → ℝ := fun n => if n ≠ 0 ∧ ‖mom L n‖ ≤ R then ‖mom L n‖ ^ (-(2 : ℝ)) else 0
    with hbbdef
  have hbb0 : ∀ n, 0 ≤ bb n := fun n => by
    simp only [hbbdef]
    split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hbbs : Summable bb := S3Bound_summable_ball hL bb fun n hn => by
    simp only [hbbdef] at hn
    by_contra h
    exact hn (by rw [ite_eq_right fun h' => h h'.2])
  have hmc1 : 1 ≤ mc ρ := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ hρ1 (by norm_num)
  have hceil : ((⌈mc ρ⌉₊ : ℕ) : ℝ) < mc ρ + 1 := Nat.ceil_lt_add_one (by linarith)
  have hlamb : ∀ n, inPL ρ L n → |lam V w ρ L n| ≤ g0 V w * bb n := fun n hn => by
    have hpos : 0 < ‖mom L n‖ := lt_of_lt_of_le (mul_pos hε0 hsq) hn.1
    have hb : bb n = (‖mom L n‖ ^ 2)⁻¹ := by
      simp only [hbbdef]
      rw [ite_eq_left ⟨Regions_PL_ne_zero hρ hn, hn.2⟩, S3Bound_rpow_neg_two _ (norm_nonneg _)]
    rw [hb, ← div_eq_mul_inv]
    exact S3Bound_lam_PL_le hg hρ hn hpos
  set f : Idx × Idx → ℝ := fun uv =>
    if inPL ρ L uv.1 ∧ inPL ρ L uv.2 then
      |(ft V (mom L (uv.1 - uv.2))).re * lam V w ρ L uv.1 * lam V w ρ L uv.2| *
        (Expect.Q Ψ [uv.1] + 1) else 0 with hf
  set M : ℝ := 3 * (∫ x, V x) * mc ρ * g0 V w ^ 2 with hMdef
  have hf0 : ∀ x, 0 ≤ f x := fun x => by
    simp only [hf]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (by linarith [S3Bound_Q_nonneg Ψ [x.1]])
    · exact le_rfl
  have hle : ∀ x : Idx × Idx, f x ≤ M * (bb x.1 * bb x.2) := fun x => by
    simp only [hf]
    by_cases h : inPL ρ L x.1 ∧ inPL ρ L x.2
    · rw [ite_eq_left h]
      have hu := hlamb x.1 h.1
      have hv := hlamb x.2 h.2
      have hQ : Expect.Q Ψ [x.1] + 1 ≤ 3 * mc ρ := by
        have := S3Bound_Q_PL_le V w kc hN1 h.1
        linarith
      have hVr := S3Bound_abs_V_le hV (mom L (x.1 - x.2))
      have hb1 := hbb0 x.1
      have hb2 := hbb0 x.2
      have hQ0 : 0 ≤ Expect.Q Ψ [x.1] + 1 := by linarith [S3Bound_Q_nonneg Ψ [x.1]]
      rw [abs_mul, abs_mul]
      calc |(ft V (mom L (x.1 - x.2))).re| * |lam V w ρ L x.1| * |lam V w ρ L x.2| *
            (Expect.Q Ψ [x.1] + 1)
          ≤ (∫ x, V x) * (g0 V w * bb x.1) * (g0 V w * bb x.2) * (3 * mc ρ) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul hVr hu (abs_nonneg _) hV0) hv
              (abs_nonneg _) (mul_nonneg hV0 (mul_nonneg hg.le hb1))) hQ hQ0
              (mul_nonneg (mul_nonneg hV0 (mul_nonneg hg.le hb1)) (mul_nonneg hg.le hb2))
        _ = M * (bb x.1 * bb x.2) := by rw [hMdef]; ring
    · rw [ite_eq_right h]
      exact mul_nonneg (by positivity) (mul_nonneg (hbb0 _) (hbb0 _))
  have hprod : Summable fun x : Idx × Idx => bb x.1 * bb x.2 :=
    Summable.mul_of_nonneg hbbs hbbs (fun n => hbb0 n) (fun n => hbb0 n)
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hle (hprod.mul_left M)
  refine ⟨hfs, ?_⟩
  have hnorm : Summable fun n => ‖bb n‖ :=
    hbbs.congr fun n => (Real.norm_of_nonneg (hbb0 n)).symm
  have hsq' : (∑' n, bb n) * (∑' n, bb n) = ∑' x : Idx × Idx, bb x.1 * bb x.2 :=
    tsum_mul_tsum_of_summable_norm hnorm hnorm
  have htb : ∑' x, f x ≤ M * ((∑' n, bb n) * (∑' n, bb n)) := by
    rw [hsq', ← tsum_mul_left]
    exact hfs.tsum_le_tsum hle (hprod.mul_left M)
  have hB0 : 0 ≤ (L ^ 3)⁻¹ * ∑' n, bb n := mul_nonneg (by positivity) (tsum_nonneg hbb0)
  have hB2 := pow_le_pow_left₀ hB0 hbB 2
  have hM0 : 0 ≤ M := by positivity
  calc ρ ^ 2 * (((L ^ 3) ^ 2)⁻¹ * ∑' x, f x)
      ≤ ρ ^ 2 * (((L ^ 3) ^ 2)⁻¹ * (M * ((∑' n, bb n) * (∑' n, bb n)))) := by gcongr
    _ = ρ ^ 2 * M * ((L ^ 3)⁻¹ * ∑' n, bb n) ^ 2 := by ring
    _ ≤ ρ ^ 2 * M * (K₂ * R) ^ 2 := by gcongr
    _ = 3 * (∫ x, V x) * g0 V w ^ 2 * K₂ ^ 2 * (ρ ^ 2 * mc ρ * R ^ 2) := by rw [hMdef]; ring
    _ = _ := by rw [hRdef, S3Bound_R_eq hρ, S3Bound_pow_PL hρ]

/-- `(1 + 2√m_c)^{-2} ≤ ρ^{1/400}`, `m_c = ρ^{-1/200}`. -/
private lemma S3Bound_tau1 {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (1 + 2 * Real.sqrt (mc ρ)) ^ (-2 : ℝ) ≤ ρ ^ (1/400 : ℝ) := by
  have hm : 0 < mc ρ := Real.rpow_pos_of_pos hρ _
  have hs := Real.sq_sqrt hm.le
  have hs0 := Real.sqrt_nonneg (mc ρ)
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  have h1 : 4 * mc ρ ≤ (1 + 2 * Real.sqrt (mc ρ)) ^ 2 := by nlinarith
  have h2 : ((1 + 2 * Real.sqrt (mc ρ)) ^ 2)⁻¹ ≤ (4 * mc ρ)⁻¹ := inv_anti₀ (by positivity) h1
  have h3 : (mc ρ)⁻¹ = ρ ^ (1/200 : ℝ) := by
    rw [mc, Real.rpow_neg hρ.le, inv_inv]
  have h4 : ρ ^ (1/200 : ℝ) ≤ ρ ^ (1/400 : ℝ) := S3Bound_rpow_le hρ hρ1 (by norm_num)
  have h5 : (4 * mc ρ)⁻¹ = (mc ρ)⁻¹ / 4 := by rw [mul_inv]; ring
  have h6 : 0 ≤ ρ ^ (1/200 : ℝ) := by positivity
  rw [h5, h3] at h2
  linarith

/-- `2π/(L_N ρ_N^{1/2}) ≤ 2π ρ_N^{1/400}`. -/
private lemma S3Bound_tau2 {N : ℕ} (hN : 1 ≤ N) :
    2 * π / (LN N * rhoN N ^ (1/2 : ℝ)) ≤ 2 * π * rhoN N ^ (1/400 : ℝ) := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  rw [S3Bound_L_sqrt hN, div_inv_eq_mul]
  exact mul_le_mul_of_nonneg_left (S3Bound_rpow_le hρ hρ1 (by norm_num)) (by positivity)

/-- Last term of (7.64) [temp8.70], with the summability of the family. -/
private lemma S3Bound_tail_core {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      Summable (fun uv : Idx × Idx =>
          if inPL (rhoN N) (LN N) uv.1 ∧
              (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
            |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
              lam V w (rhoN N) (LN N) uv.2| *
              ((rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2 /
                (1 - (rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2)) *
              (rhoN N ^ (1/400 : ℝ) +
                |rhoN N * lam V w (rhoN N) (LN N) uv.1| ^ (2 * Real.sqrt (mc (rhoN N)))) else 0) ∧
      rhoN N ^ 2 * (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
          if inPL (rhoN N) (LN N) uv.1 ∧
              (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
            |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
              lam V w (rhoN N) (LN N) uv.2| *
              ((rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2 /
                (1 - (rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2)) *
              (rhoN N ^ (1/400 : ℝ) +
                |rhoN N * lam V w (rhoN N) (LN N) uv.1| ^ (2 * Real.sqrt (mc (rhoN N)))) else 0))
        ≤ C * rhoN N ^ (5/2 + 1/400 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨K, hK, N₁, hfacts⟩ := S3Bound_facts hV hw
  obtain ⟨K₁, hK₁, hocc⟩ := sum_PL_occ hg
  obtain ⟨K₂, hK₂, htail⟩ := sum_PL_tail hg
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 S3Bound_ev_L
  set G' : ℝ := g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) with hG'
  have hG0 : 0 ≤ G' := by positivity
  refine ⟨K * (G' + 2 * K₁ + K₂ * (1 + 2 * π)), by positivity, max N₁ N₂, fun N hN => ?_⟩
  obtain ⟨hN1, hlam, hs, -, -⟩ := hfacts N (le_trans (le_max_left _ _) hN)
  have h2π := hN₂ N (le_trans (le_max_right _ _) hN)
  have hτ2 := S3Bound_tau2 hN1
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  have hε0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hsq : 0 < ρ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  set t : ℝ := 2 * Real.sqrt (mc ρ) with htdef
  have ht : 0 ≤ t := by positivity
  set X : Idx → ℝ := fun n => (ρ * lam V w ρ L n) ^ 2 / (1 - (ρ * lam V w ρ L n) ^ 2) with hX
  set T : Idx → ℝ := fun n => ρ ^ (1/400 : ℝ) + |ρ * lam V w ρ L n| ^ t with hT
  have hT0 : ∀ n, 0 ≤ T n := fun n => by
    simp only [hT]
    positivity
  set a : Idx → ℝ := fun n => if inPL ρ L n then X n * T n else 0 with hadef
  set sv : Idx → Idx → ℝ := fun u v => if v ≠ 0 then
    |lam V w ρ L v * (ft V (mom L u - mom L v)).re| else 0 with hsvdef
  set f : Idx × Idx → ℝ := fun uv =>
    if inPL ρ L uv.1 ∧ (inPI ρ L uv.2 ∨ inPH ρ L uv.2) then
      |(ft V (mom L (uv.1 - uv.2))).re * lam V w ρ L uv.1 * lam V w ρ L uv.2| *
        X uv.1 * T uv.1 else 0 with hf
  have ha0 : ∀ u, 0 ≤ a u := fun u => by
    simp only [hadef]
    split_ifs with h
    · exact mul_nonneg (S3Bound_X_nonneg hg hρ hρ1 h) (hT0 u)
    · exact le_rfl
  have has : Summable a := S3Bound_summable_ball hL a fun n hn => by
    simp only [hadef] at hn
    by_contra h
    exact hn (by rw [ite_eq_right fun h' => h h'.2])
  have hs0 : ∀ u v, 0 ≤ sv u v := fun u v => by
    simp only [hsvdef]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hf0 : ∀ x, 0 ≤ ρ * f x := fun x => by
    refine mul_nonneg hρ.le ?_
    simp only [hf]
    split_ifs with h
    · exact mul_nonneg (mul_nonneg (abs_nonneg _) (S3Bound_X_nonneg hg hρ hρ1 h.1)) (hT0 _)
    · exact le_rfl
  have hle : ∀ x : Idx × Idx, ρ * f x ≤ a x.1 * sv x.1 x.2 := fun x => by
    simp only [hf, hadef, hsvdef]
    by_cases h : inPL ρ L x.1 ∧ (inPI ρ L x.2 ∨ inPH ρ L x.2)
    · rw [ite_eq_left h, ite_eq_left h.1,
        ite_eq_left (S3Bound_inP_ne_zero hρ (S3Bound_IH_P h.2))]
      have h1 := hlam x.1 (Or.inl h.1)
      have hXT : 0 ≤ X x.1 * T x.1 := mul_nonneg (S3Bound_X_nonneg hg hρ hρ1 h.1) (hT0 _)
      have e : ρ * (|(ft V (mom L (x.1 - x.2))).re * lam V w ρ L x.1 * lam V w ρ L x.2| *
          X x.1 * T x.1) = |ρ * lam V w ρ L x.1| *
            (X x.1 * T x.1 * |lam V w ρ L x.2 * (ft V (mom L x.1 - mom L x.2)).re|) := by
        simp only [S3Bound_mom_sub, abs_mul, abs_of_pos hρ]
        ring
      rw [e]
      have h0 : 0 ≤ X x.1 * T x.1 * |lam V w ρ L x.2 * (ft V (mom L x.1 - mom L x.2)).re| :=
        mul_nonneg hXT (abs_nonneg _)
      calc _ ≤ 1 * (X x.1 * T x.1 * |lam V w ρ L x.2 * (ft V (mom L x.1 - mom L x.2)).re|) :=
            mul_le_mul_of_nonneg_right h1 h0
        _ = _ := one_mul _
    · rw [ite_eq_right h, mul_zero]
      exact mul_nonneg (ha0 _) (hs0 _ _)
  obtain ⟨hfs', hsum⟩ := S3Bound_fiber ha0 has hs0 (fun u => (hs u).1) (fun u => (hs u).2) hf0
    hle
  have hfs : Summable f := (summable_mul_left_iff hρ.ne').1 hfs'
  refine ⟨hfs, ?_⟩
  set a1 : Idx → ℝ := fun n => if inPL ρ L n then
    (ρ * lamPL (g0 V w) ρ (mom L n)) ^ 2 / (1 - (ρ * lamPL (g0 V w) ρ (mom L n)) ^ 2) else 0
    with ha1
  set a2 : Idx → ℝ := fun n => if inPL ρ L n then
    |ρ * lamPL (g0 V w) ρ (mom L n)| ^ t * ((ρ * lamPL (g0 V w) ρ (mom L n)) ^ 2 /
      (1 - (ρ * lamPL (g0 V w) ρ (mom L n)) ^ 2)) else 0 with ha2
  have has1 : Summable a1 := S3Bound_summable_ball hL a1 fun n hn => by
    simp only [ha1] at hn
    by_contra h
    exact hn (by rw [ite_eq_right fun h' => h h'.2])
  have has2 : Summable a2 := S3Bound_summable_ball hL a2 fun n hn => by
    simp only [ha2] at hn
    by_contra h
    exact hn (by rw [ite_eq_right fun h' => h h'.2])
  have hasplit : ∀ n, a n = ρ ^ (1/400 : ℝ) * a1 n + a2 n := fun n => by
    simp only [hadef, ha1, ha2, hX, hT]
    by_cases h : inPL ρ L n
    · rw [ite_eq_left h, ite_eq_left h, ite_eq_left h, S3Bound_lam_PL V w h]
      ring
    · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
      ring
  have hsa : ∑' n, a n = ρ ^ (1/400 : ℝ) * (∑' n, a1 n) + ∑' n, a2 n := by
    rw [tsum_congr hasplit, (has1.mul_left _).tsum_add has2, tsum_mul_left]
  have h1 := hocc ρ L hρ hρ1 h2π
  have h2 := htail t ρ L ht hρ h2π
  have hτ1 := S3Bound_tau1 hρ hρ1
  have hr1 : ρ ^ (1/200 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hr0 : 0 ≤ ρ ^ (1/400 : ℝ) := Real.rpow_nonneg hρ.le _
  have hd1 : 2 * π / (L * ρ ^ (1/2 : ℝ)) ≤ 1 :=
    (div_le_one (lt_of_lt_of_le (by positivity) h2π)).2 h2π
  have hA1 : (L ^ 3)⁻¹ * ∑' n, a1 n ≤ ρ ^ (3/2 : ℝ) * (G' + 2 * K₁) := by
    refine S3Bound_unscale hρ ?_
    have h1' := (abs_le.1 h1).2
    have : K₁ * (ρ ^ (1/200 : ℝ) + 2 * π / (L * ρ ^ (1/2 : ℝ))) ≤ K₁ * 2 := by
      have := add_le_add hr1 hd1
      nlinarith
    calc ρ ^ (-(3/2 : ℝ)) * ((L ^ 3)⁻¹ * ∑' n, a1 n)
        = (L ^ 3)⁻¹ * ρ ^ (-(3/2 : ℝ)) * ∑' n, a1 n := by ring
      _ ≤ G' + 2 * K₁ := by linarith
  have hA2 : (L ^ 3)⁻¹ * ∑' n, a2 n ≤ ρ ^ (3/2 : ℝ) * (K₂ * (1 + 2 * π) * ρ ^ (1/400 : ℝ)) := by
    refine S3Bound_unscale hρ ?_
    have : K₂ * ((1 + t) ^ (-2 : ℝ) + 2 * π / (L * ρ ^ (1/2 : ℝ))) ≤
        K₂ * (1 + 2 * π) * ρ ^ (1/400 : ℝ) := by
      have := add_le_add hτ1 hτ2
      nlinarith
    calc ρ ^ (-(3/2 : ℝ)) * ((L ^ 3)⁻¹ * ∑' n, a2 n)
        = (L ^ 3)⁻¹ * ρ ^ (-(3/2 : ℝ)) * ∑' n, a2 n := by ring
      _ ≤ _ := h2.trans this
  have hA : (L ^ 3)⁻¹ * ∑' n, a n ≤
      ρ ^ (3/2 : ℝ) * ρ ^ (1/400 : ℝ) * (G' + 2 * K₁ + K₂ * (1 + 2 * π)) := by
    rw [hsa]
    have e : (L ^ 3)⁻¹ * (ρ ^ (1/400 : ℝ) * (∑' n, a1 n) + ∑' n, a2 n) =
        ρ ^ (1/400 : ℝ) * ((L ^ 3)⁻¹ * ∑' n, a1 n) + (L ^ 3)⁻¹ * ∑' n, a2 n := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hA1 hr0
    nlinarith
  have hL3 : 0 < L ^ 3 := by positivity
  rw [tsum_mul_left] at hsum
  calc ρ ^ 2 * (((L ^ 3) ^ 2)⁻¹ * ∑' x, f x)
      = ρ * ((L ^ 3)⁻¹ * ((L ^ 3)⁻¹ * (ρ * ∑' x, f x))) := by ring
    _ ≤ ρ * ((L ^ 3)⁻¹ * ((L ^ 3)⁻¹ * (K * L ^ 3 * ∑' u, a u))) := by gcongr
    _ = ρ * K * ((L ^ 3)⁻¹ * ∑' u, a u) := by field_simp
    _ ≤ ρ * K * (ρ ^ (3/2 : ℝ) * ρ ^ (1/400 : ℝ) * (G' + 2 * K₁ + K₂ * (1 + 2 * π))) := by
        gcongr
    _ = K * (G' + 2 * K₁ + K₂ * (1 + 2 * π)) * ρ ^ (5/2 + 1/400 : ℝ) := by
        rw [S3Bound_pow_split hρ]; ring

/-! ### The pointwise estimates behind (7.62)–(7.63) [longexpression1] -/

/-- `|Re z − m| ≤ ‖z − m‖`. -/
private lemma S3Bound_re_sub (z : ℂ) (m : ℝ) : |z.re - m| ≤ ‖z - (m : ℂ)‖ := by
  have := Complex.abs_re_le_norm (z - (m : ℂ))
  simpa using this

/-- The block `u, v ∈ P_I ∪ P_H` of (7.62): from (7.44) [u-uv-vPMH]. -/
private lemma S3Bound_alg_IH {Vr l1 l2 Er D ρ V0 Q2 Q2' Qu Qv : ℝ}
    (hE : |Er - l1 * l2 * D| ≤ |l1 * l2| * ρ ^ 2 * ((Q2 + Q2') / 2 + Qu + Qv + ρ ^ 2))
    (hV : |Vr| ≤ V0) (hQ2 : 0 ≤ Q2) (hQ2' : 0 ≤ Q2') (hQu : 0 ≤ Qu) (hQv : 0 ≤ Qv) :
    Vr * Er ≤ D * (Vr * l1 * l2) +
      ρ ^ 2 * (V0 * (|l1 * l2| * Q2 + |l1 * l2| * Q2') +
        2 * (|Vr * l1 * l2| * Qu + |Vr * l1 * l2| * Qv)) + ρ ^ 4 * |l1 * Vr * l2| := by
  have h1 : Vr * Er - Vr * (l1 * l2 * D) ≤
      |Vr| * (|l1 * l2| * ρ ^ 2 * ((Q2 + Q2') / 2 + Qu + Qv + ρ ^ 2)) := by
    rw [← mul_sub]
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hE (abs_nonneg _)
  have eA : |Vr * l1 * l2| = |Vr| * |l1 * l2| := by rw [mul_assoc, abs_mul]
  have eA' : |l1 * Vr * l2| = |Vr| * |l1 * l2| := by
    rw [mul_comm l1 Vr, mul_assoc, abs_mul]
  rw [eA, eA']
  set A := |Vr| with hA
  set B := |l1 * l2| with hB
  have hA0 : 0 ≤ A := abs_nonneg _
  have hB0 : 0 ≤ B := abs_nonneg _
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg _
  have k1 := mul_le_mul_of_nonneg_right hV (mul_nonneg (mul_nonneg hB0 hρ2) hQ2)
  have k2 := mul_le_mul_of_nonneg_right hV (mul_nonneg (mul_nonneg hB0 hρ2) hQ2')
  have k3 : 0 ≤ A * (B * ρ ^ 2 * Qu) := by positivity
  have k4 : 0 ≤ A * (B * ρ ^ 2 * Qv) := by positivity
  have k5 : 0 ≤ A * (B * ρ ^ 2 * Q2) := by positivity
  have k6 : 0 ≤ A * (B * ρ ^ 2 * Q2') := by positivity
  nlinarith

/-- The block `u ∈ P_L`, `v ∈ P_I ∪ P_H` of (7.62): from (7.45) [u-uv-vPLMH]. -/
private lemma S3Bound_alg_mixed {Vr l1 l2 Er D ρ X V0 Q2 Q2' Qw r Y C Cm : ℝ}
    (hE : |Er - l1 * l2 * (D + ρ ^ 2 * X)| ≤
      |l1 * l2| * ρ ^ 2 * ((Q2 + Q2') / 2 + 2 * Qw + X * (C * r + Y)))
    (hV : |Vr| ≤ V0) (hQ2 : 0 ≤ Q2) (hQ2' : 0 ≤ Q2') (hQw : 0 ≤ Qw) (hX : 0 ≤ X) (hr : 0 ≤ r)
    (hY : 0 ≤ Y) (hC : C ≤ Cm) (hCm : 1 ≤ Cm) :
    Vr * Er ≤ D * (Vr * l1 * l2) + ρ ^ 2 * (Vr * l1 * l2 * X) +
      ρ ^ 2 * (V0 * (|l1 * l2| * Q2 + |l1 * l2| * Q2') + 2 * (|Vr * l1 * l2| * Qw) +
        Cm * (|Vr * l1 * l2| * X * (r + Y))) := by
  have h1 : Vr * Er - Vr * (l1 * l2 * (D + ρ ^ 2 * X)) ≤
      |Vr| * (|l1 * l2| * ρ ^ 2 * ((Q2 + Q2') / 2 + 2 * Qw + X * (C * r + Y))) := by
    rw [← mul_sub]
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hE (abs_nonneg _)
  have eA : |Vr * l1 * l2| = |Vr| * |l1 * l2| := by rw [mul_assoc, abs_mul]
  rw [eA]
  set A := |Vr| with hA
  set B := |l1 * l2| with hB
  have hA0 : 0 ≤ A := abs_nonneg _
  have hB0 : 0 ≤ B := abs_nonneg _
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg _
  have hCr : C * r + Y ≤ Cm * (r + Y) := by nlinarith
  have k1 := mul_le_mul_of_nonneg_right hV (mul_nonneg (mul_nonneg hB0 hρ2) hQ2)
  have k2 := mul_le_mul_of_nonneg_right hV (mul_nonneg (mul_nonneg hB0 hρ2) hQ2')
  have k3 : 0 ≤ A * (B * ρ ^ 2 * Qw) := by positivity
  have k5 : 0 ≤ A * (B * ρ ^ 2 * Q2) := by positivity
  have k6 : 0 ≤ A * (B * ρ ^ 2 * Q2') := by positivity
  have k7 := mul_le_mul_of_nonneg_left hCr (mul_nonneg (mul_nonneg (mul_nonneg hA0 hB0) hρ2) hX)
  nlinarith

/-- The block `u, v ∈ P_L` of (7.62): from (7.46) [u-uv-vPL] and `V_{u−v} ≥ 0`. -/
private lemma S3Bound_alg_L {Vr l1 l2 Er D ρ V0 Q2 Qu Qv : ℝ}
    (hE : Er - l1 * l2 * D ≤ |l1 * l2| * ρ ^ 2 * (Q2 + 2 * Qu + 2 * Qv + 3))
    (hV0 : 0 ≤ Vr) (hV : |Vr| ≤ V0) (hQ2 : 0 ≤ Q2) :
    Vr * Er ≤ D * (Vr * l1 * l2) +
      ρ ^ 2 * (V0 * (|l1 * l2| * Q2) + 2 * (|Vr * l1 * l2| * (Qu + 1)) +
        2 * (|Vr * l1 * l2| * (Qv + 1))) := by
  have h1 : Vr * Er - Vr * (l1 * l2 * D) ≤
      Vr * (|l1 * l2| * ρ ^ 2 * (Q2 + 2 * Qu + 2 * Qv + 3)) := by
    rw [← mul_sub]
    exact mul_le_mul_of_nonneg_left hE hV0
  have eA : |Vr * l1 * l2| = Vr * |l1 * l2| := by rw [mul_assoc, abs_mul, abs_of_nonneg hV0]
  rw [eA]
  rw [abs_of_nonneg hV0] at hV
  set B := |l1 * l2| with hB
  have hB0 : 0 ≤ B := abs_nonneg _
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg _
  have k1 := mul_le_mul_of_nonneg_right hV (mul_nonneg (mul_nonneg hB0 hρ2) hQ2)
  have k3 : 0 ≤ Vr * (B * ρ ^ 2) := by positivity
  nlinarith

/-- For `u, v ≠ 0` not both in `P`, `⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ = 0`: a state of `M` occupies
only `0` and momenta of `P` (Definition 3.4 [M]). -/
private lemma S3Bound_E4_zero (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) {u v : Idx} (hu : u ≠ 0)
    (hv : v ≠ 0) (hP : ¬ (inP (rhoN N) (LN N) u ∧ inP (rhoN N) (LN N) v)) :
    Expect.E4 (trialState V w kc N) u (-u) v (-v) = 0 := by
  unfold Expect.E4
  refine (tsum_congr (g := fun _ : Occ => (0 : ℂ)) fun α => ?_).trans tsum_zero
  have hM : ∀ β : Occ, trialState V w kc N β ≠ 0 → InM (rhoN N) (LN N) kc N β := fun β h => by
    by_contra hM
    apply h
    unfold trialState
    simp [hM]
  by_cases hc : (a4 u (-u) v (-v) α).1 = 0
  · simp [hc]
  obtain ⟨β, rfl⟩ := a4_exists_add u (-u) v (-v) α hc
  rw [a4_of_add u (-u) v (-v) β]
  by_cases hPv : inP (rhoN N) (LN N) v
  · have hPu : ¬ inP (rhoN N) (LN N) u := fun h => hP ⟨h, hPv⟩
    have hz : trialState V w kc N (β + Finsupp.single (-u) 1 + Finsupp.single u 1) = 0 := by
      by_contra h
      rcases MBasic_support (hM _ h) u (by simp [Finsupp.single_apply]) with h0 | h1
      · exact hu h0
      · exact hPu h1
    simp [hz]
  · have hz : trialState V w kc N (β + Finsupp.single v 1 + Finsupp.single (-v) 1) = 0 := by
      by_contra h
      rcases MBasic_support (hM _ h) v (by simp [Finsupp.single_apply]) with h0 | h1
      · exact hv h0
      · exact hPv h1
    simp [hz]

/-- `⟨a†_v a†_{−v} a_u a_{−u}⟩_Ψ = conj ⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ`, Lemma 7.1 [id4a]. -/
private lemma S3Bound_E4_swap {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (u v : Idx) :
    Expect.E4 Ψ v (-v) u (-u) = conj (Expect.E4 Ψ u (-u) v (-v)) := by
  rw [← (Lemma7_1 N Ψ hΨ u (-u) v (-v)).2]
  unfold Expect.E4
  refine tsum_congr fun α => ?_
  rw [a4_comm]

/-- The index set of `H_{S3}` at `(p, q, u) = (p, −p, p − v)`, (4.5). -/
private lemma S3Bound_S3_mem (p v : Idx) :
    Decomp.Part.S3.mem p (-p) (p - v) ↔ p ≠ 0 ∧ v ≠ 0 ∧ p ≠ v ∧ p + v ≠ 0 := by
  have h1 : -p + (p - v) = -v := by abel
  have h2 : p - v = p - -p ↔ p + v = 0 := by
    rw [sub_right_inj, eq_neg_iff_add_eq_zero, add_comm]
  simp only [Decomp.Part.mem, Decomp.zeros, Decomp.InS1, sub_sub_cancel, h1, neg_eq_zero,
    add_neg_cancel, h2, sub_eq_zero]
  constructor
  · rintro ⟨hz, -, hs⟩
    simp only [Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false] at hz
    exact ⟨hz.1.1.1, hz.1.2, (not_or.mp hs).1, (not_or.mp hs).2⟩
  · rintro ⟨hp, hv, hpv, hs⟩
    simp [hp, hv, hpv, hs]

/-- The summand of (4.5) at `(p, q, u) = (p, −p, p − v)`: `a†_p a†_{−p} a_v a_{−v}`. -/
private lemma S3Bound_intTerm_S3 (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (p v : Idx) (α : Occ) :
    intTerm L V Ψ (p, -p, p - v, α) = (L ^ 3)⁻¹ * ft V (mom L (p - v)) *
      (conj (Ψ (a4 p (-p) v (-v) α).2) * ((a4 p (-p) v (-v) α).1 : ℂ) * Ψ α) := by
  have h1 : -p + (p - v) = -v := by abel
  simp only [intTerm, sub_sub_cancel, h1]
  ring

/-- The family `(u, v) ↦ V_{u−v} ⟨a†_u a†_{−u} a_v a_{−v}⟩_Ψ` over `u, v ≠ 0`, `u ≠ ±v` of
`⟨H_{S3}⟩_Ψ` is summable. -/
private lemma S3Bound_S3_summable {L : ℝ} (hL : L ≠ 0) {V : R3 → ℝ} {N : ℕ} {Ψ : Occ → ℂ}
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    Summable fun uv : Idx × Idx =>
      if uv.1 ≠ 0 ∧ uv.2 ≠ 0 ∧ uv.1 ≠ uv.2 ∧ uv.1 + uv.2 ≠ 0 then
        ft V (mom L (uv.1 - uv.2)) * Expect.E4 Ψ uv.1 (-uv.1) uv.2 (-uv.2) else 0 := by
  set g : (Idx × Idx) × Occ → Idx × Idx × Idx × Occ :=
    fun x => (x.1.1, -x.1.1, x.1.1 - x.1.2, x.2) with hgdef
  have hg : Function.Injective g := by
    rintro ⟨⟨p, v⟩, α⟩ ⟨⟨p', v'⟩, α'⟩ h
    simp only [hgdef, Prod.mk.injEq] at h
    obtain ⟨rfl, -, h3, rfl⟩ := h
    rw [sub_right_inj] at h3
    rw [h3]
  have hG : Summable fun x => Decomp.partTerm .S3 L V Ψ (g x) := by
    refine Summable.of_norm_bounded
      ((Decomp.intTerm_summable_norm L V N Ψ hV hΨ).comp_injective hg) (fun x => ?_)
    simp only [Function.comp, Decomp.partTerm]
    split_ifs <;> simp
  have hf : ∀ uv : Idx × Idx, HasSum (fun α => Decomp.partTerm .S3 L V Ψ (g (uv, α)))
      ((L ^ 3)⁻¹ * (if uv.1 ≠ 0 ∧ uv.2 ≠ 0 ∧ uv.1 ≠ uv.2 ∧ uv.1 + uv.2 ≠ 0 then
        ft V (mom L (uv.1 - uv.2)) * Expect.E4 Ψ uv.1 (-uv.1) uv.2 (-uv.2) else 0)) := by
    rintro ⟨p, v⟩
    simp only [hgdef, Decomp.partTerm]
    by_cases h : p ≠ 0 ∧ v ≠ 0 ∧ p ≠ v ∧ p + v ≠ 0
    · simp only [(S3Bound_S3_mem p v).mpr h, h, ne_eq, not_false_eq_true, and_self,
        ite_true, S3Bound_intTerm_S3]
      convert (Lemma7_1 N Ψ hΨ p (-p) v (-v)).1.mul_left ((L ^ 3)⁻¹ * ft V (mom L (p - v)))
        using 1
      ring
    · have h' : ¬ Decomp.Part.S3.mem p (-p) (p - v) := fun hm =>
        h ((S3Bound_S3_mem p v).mp hm)
      simp only [h', h, ite_false, mul_zero]
      exact hasSum_zero
  have hs := (hG.hasSum.prod_fiberwise hf).summable
  have hL3 : ((L : ℂ) ^ 3) ≠ 0 := by exact_mod_cast pow_ne_zero 3 hL
  refine (hs.mul_left ((L : ℂ) ^ 3)).congr fun uv => ?_
  rw [Complex.ofReal_inv, Complex.ofReal_pow, ← mul_assoc, mul_inv_cancel₀ hL3, one_mul]

/-- `V_{u−v} ≥ 0` for `u, v ∈ P_L` and `N` large: `|V_p − V₀| ≤ C|p|` and
`|p_u − p_v| ≤ 2ρ^{1/2−η}`. -/
private lemma S3Bound_V_PL_nonneg {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ u v : Idx, inPL (rhoN N) (LN N) u → inPL (rhoN N) (LN N) v →
      0 ≤ (ft V (mom (LN N) (u - v))).re := by
  obtain ⟨CL, hCL⟩ := scat_ft_V_lipschitz hV
  have hV0 : 0 < ∫ x, V x := (scat_g0_pos hV hw).trans_le (scat_g0_le hV hw)
  have hc : 0 < (∫ x, V x) / (2 * |CL| + 1) := by positivity
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((S3Bound_ev_rpow_lt (by norm_num : (0 : ℝ) < 1/2 - 1/200)
    hc).and (eventually_ge_atTop 1))
  refine ⟨N₀, fun N hN u v hu hv => ?_⟩
  obtain ⟨hlt, hN1⟩ := hN₀ N hN
  have hρ := (Particles_rhoN_LN hN1).2.1
  set R := rhoN N ^ (1/2 - 1/200 : ℝ) with hR
  have hR0 : 0 ≤ R := Real.rpow_nonneg hρ.le _
  have hu2 : ‖mom (LN N) u‖ ≤ R := by rw [hR, ← S3Bound_R_eq hρ]; exact hu.2
  have hv2 : ‖mom (LN N) v‖ ≤ R := by rw [hR, ← S3Bound_R_eq hρ]; exact hv.2
  have hp : ‖mom (LN N) (u - v)‖ ≤ 2 * R := by
    rw [S3Bound_mom_sub]
    exact (norm_sub_le _ _).trans (by linarith)
  have h1 := hCL (mom (LN N) (u - v)) 0
  rw [sub_zero, scat_ft_zero] at h1
  have h2 : (∫ x, V x) - (ft V (mom (LN N) (u - v))).re ≤
      ‖ft V (mom (LN N) (u - v)) - ((∫ x, V x : ℝ) : ℂ)‖ := by
    have := Complex.abs_re_le_norm (ft V (mom (LN N) (u - v)) - ((∫ x, V x : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at this
    linarith [neg_abs_le ((ft V (mom (LN N) (u - v))).re - ∫ x, V x)]
  have h3 : CL * ‖mom (LN N) (u - v)‖ ≤ |CL| * (2 * R) :=
    (le_abs_self CL |>.trans le_rfl) |> fun h => by
      calc CL * ‖mom (LN N) (u - v)‖ ≤ |CL| * ‖mom (LN N) (u - v)‖ :=
            mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ ≤ |CL| * (2 * R) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
  have h4 : (2 * |CL| + 1) * R < ∫ x, V x := by
    rw [lt_div_iff₀ (by positivity)] at hlt
    linarith
  nlinarith [abs_nonneg CL]

/-- `P_I ∪ P_H` is disjoint from `P_L`. -/
private lemma S3Bound_IH_not_L {ρ L : ℝ} (hρ : 0 < ρ) {n : Idx} (h : inPI ρ L n ∨ inPH ρ L n) :
    ¬ inPL ρ L n := fun hL => by
  rcases h with h | h
  · exact Regions_PL_PI hL h
  · exact Regions_PL_PH hρ hL h

/-- `Q_Ψ(v, −u) = Q_Ψ(u, −v)` for the trial state. -/
private lemma S3Bound_Q_neg_swap (V w : R3 → ℝ) (kc : ℝ) (N : ℕ) (u v : Idx) :
    Expect.Q (trialState V w kc N) [v, -u] = Expect.Q (trialState V w kc N) [u, -v] := by
  rw [← Pair_Q_neg V w kc N [v, -u], S3Bound_Q_comm]
  simp

/-! ### (7.62)–(7.63) [longexpression1] -/

/-- (7.62)–(7.63) [longexpression1]: `|Λ|⁻¹⟨H_{S3}⟩_Ψ ≤ A + B + Ω` with `Ω ≤ Cρ^{5/2+η/2}` by
(7.64) [temp8.70], where `A = |Λ|⁻²(Q_Ψ(0, 0) − Q_Ψ(0)) · |Λ|⁻² Σ_{u, v ∈ P, u ≠ ±v} V_{u−v}λ_uλ_v`
and `B = 2ρ²|Λ|⁻² Σ_{u ∈ P_L, v ∈ P_I ∪ P_H} V_{u−v}λ_uλ_v x_u/(1 − x_u)`. -/
theorem Eq7_62 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      ∃ I : ℝ, HasSum (Decomp.partTerm .S3 (LN N) V (trialState V w kc N)) (I : ℂ) ∧
        I / LN N ^ 3 ≤
          (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
                (LN N ^ 3) ^ 2 *
              (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
                if inP (rhoN N) (LN N) uv.1 ∧ inP (rhoN N) (LN N) uv.2 ∧ uv.1 ≠ uv.2 ∧
                    uv.1 + uv.2 ≠ 0 then
                  (ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
                    lam V w (rhoN N) (LN N) uv.2 else 0)) +
            2 * rhoN N ^ 2 * (((LN N ^ 3) ^ 2)⁻¹ * (∑' uv : Idx × Idx,
                if inPL (rhoN N) (LN N) uv.1 ∧
                    (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
                  (ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
                    lam V w (rhoN N) (LN N) uv.2 *
                    ((rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2 /
                      (1 - (rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2)) else 0)) +
            C * rhoN N ^ (5/2 + 1/400 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C₁, hC₁, N₁, hQ2⟩ := S3Bound_Q2_core hV hw
  obtain ⟨C₂, hC₂, N₂, hQ1⟩ := S3Bound_Q1_core hV hw
  obtain ⟨C₃, hC₃, N₃, hPL⟩ := S3Bound_PL_core hV hw
  obtain ⟨C₄, hC₄, N₄, htl⟩ := S3Bound_tail_core hV hw
  obtain ⟨K, hK, N₅, hfacts⟩ := S3Bound_facts hV hw
  obtain ⟨N₆, h44⟩ := Eq7_44 V w
  obtain ⟨C₇, hC₇, N₇, h45⟩ := Eq7_45 hg
  obtain ⟨N₈, hVL⟩ := S3Bound_V_PL_nonneg hV hw
  obtain ⟨CV, hVsum⟩ := scat_lattice_V hV
  have hV0 : 0 ≤ ∫ x, V x := (abs_nonneg _).trans (S3Bound_abs_V_le hV 0)
  set Cm := max C₇ 1 with hCm
  have hCm1 : 1 ≤ Cm := le_max_right _ _
  have hC7m : C₇ ≤ Cm := le_max_left _ _
  have hCm0 : 0 ≤ Cm := zero_le_one.trans hCm1
  refine ⟨2 * (∫ x, V x) * C₁ + 4 * C₂ + 4 * C₃ + 2 * Cm * C₄ + K, by positivity,
    max (max (max N₁ N₂) (max N₃ N₄)) (max (max N₅ N₆) (max N₇ N₈)), fun N hN kc => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hN
  obtain ⟨⟨⟨hN₁, hN₂⟩, hN₃, hN₄⟩, ⟨hN₅, hN₆⟩, hN₇, hN₈⟩ := hN
  obtain ⟨hN1, hlam, -, hggs, hggB⟩ := hfacts N hN₅
  obtain ⟨hf2s, hf2B⟩ := hQ2 N hN₁ kc
  obtain ⟨hf1s, hf1B⟩ := hQ1 N hN₂ kc
  obtain ⟨hfLs, hfLB⟩ := hPL N hN₃ kc
  obtain ⟨hfts, hftB⟩ := htl N hN₄
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  have hΨ := Normalization_isNState V w kc hN1
  have hV' := (hVsum (LN N) (S3Bound_one_le_L hN1)).1
  have hS := Lemma7_1_S3 (LN N) V N (trialState V w kc N) hV' hΨ
  have hFs := S3Bound_S3_summable hL.ne' hV' hΨ
  have him := Decomp.im_eq_zero_of_hasSum _ _ _ _ _ hS
  -- the real summand of `⟨H_{S3}⟩_Ψ`
  set y : Idx × Idx → ℝ := fun uv =>
    if uv.1 ≠ 0 ∧ uv.2 ≠ 0 ∧ uv.1 ≠ uv.2 ∧ uv.1 + uv.2 ≠ 0 then
      (ft V (mom (LN N) (uv.1 - uv.2))).re *
        (Expect.E4 (trialState V w kc N) uv.1 (-uv.1) uv.2 (-uv.2)).re else 0 with hydef
  have hyre : ∀ uv : Idx × Idx, (if uv.1 ≠ 0 ∧ uv.2 ≠ 0 ∧ uv.1 ≠ uv.2 ∧ uv.1 + uv.2 ≠ 0 then
      ft V (mom (LN N) (uv.1 - uv.2)) *
        Expect.E4 (trialState V w kc N) uv.1 (-uv.1) uv.2 (-uv.2) else 0).re = y uv := by
    intro uv
    simp only [hydef]
    split_ifs
    · have h0 : (ft V (mom (LN N) (uv.1 - uv.2))).im = 0 := by
        rw [scat_ft_V_real hV (mom (LN N) (uv.1 - uv.2)), Complex.ofReal_im]
      rw [Complex.mul_re, h0, zero_mul, sub_zero]
    · rfl
  have hys : Summable y := (Complex.hasSum_re hFs.hasSum).summable.congr hyre
  refine ⟨(LN N ^ 3)⁻¹ * ∑' uv, y uv, ?_, ?_⟩
  · convert hS using 1
    apply Complex.ext
    · rw [Complex.ofReal_re, Complex.re_ofReal_mul, Complex.re_tsum hFs]
      exact congrArg _ (tsum_congr fun uv => (hyre uv).symm)
    · rw [Complex.ofReal_im]
      exact him.symm
  have hρ2 : 0 ≤ rhoN N ^ 2 := sq_nonneg _
  have hρ4 : 0 ≤ rhoN N ^ 4 := by positivity
  have hQ0 := S3Bound_Q_nonneg (trialState V w kc N)
  have h44' := h44 N hN₆ kc
  have h45' := h45 N hN₇ kc
  have hVL' := hVL N hN₈
  have hX0 : ∀ n, inPL (rhoN N) (LN N) n →
      0 ≤ (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2 /
        (1 - (rhoN N * lam V w (rhoN N) (LN N) n) ^ 2) := fun n hn =>
    S3Bound_X_nonneg hg hρ hρ1 hn
  have hT0 : ∀ n, 0 ≤ rhoN N ^ (1/400 : ℝ) +
      |rhoN N * lam V w (rhoN N) (LN N) n| ^ (2 * Real.sqrt (mc (rhoN N))) := fun n => by
    positivity
  have hr0 : 0 < rhoN N ^ (1/400 : ℝ) := Real.rpow_pos_of_pos hρ _
  -- the summands of `A`, `B` and of the four bounds of (7.64) [temp8.70]
  set a : Idx × Idx → ℝ := fun uv =>
    if inP (rhoN N) (LN N) uv.1 ∧ inP (rhoN N) (LN N) uv.2 ∧ uv.1 ≠ uv.2 ∧ uv.1 + uv.2 ≠ 0 then
      (ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
        lam V w (rhoN N) (LN N) uv.2 else 0 with hadef
  set b : Idx × Idx → ℝ := fun uv =>
    if inPL (rhoN N) (LN N) uv.1 ∧ (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
      (ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
        lam V w (rhoN N) (LN N) uv.2 *
        ((rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2)) else 0 with hbdef
  set f2 : Idx × Idx → ℝ := fun uv =>
    if inP (rhoN N) (LN N) uv.1 ∧ inP (rhoN N) (LN N) uv.2 then
      |lam V w (rhoN N) (LN N) uv.1 * lam V w (rhoN N) (LN N) uv.2| *
        Expect.Q (trialState V w kc N) [uv.1, uv.2] else 0 with hf2def
  set f1 : Idx × Idx → ℝ := fun uv =>
    if (inPI (rhoN N) (LN N) uv.1 ∨ inPH (rhoN N) (LN N) uv.1) ∧ inP (rhoN N) (LN N) uv.2 then
      |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
        lam V w (rhoN N) (LN N) uv.2| * Expect.Q (trialState V w kc N) [uv.1] else 0 with hf1def
  set fL : Idx × Idx → ℝ := fun uv =>
    if inPL (rhoN N) (LN N) uv.1 ∧ inPL (rhoN N) (LN N) uv.2 then
      |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
        lam V w (rhoN N) (LN N) uv.2| *
        (Expect.Q (trialState V w kc N) [uv.1] + 1) else 0 with hfLdef
  set fT : Idx × Idx → ℝ := fun uv =>
    if inPL (rhoN N) (LN N) uv.1 ∧ (inPI (rhoN N) (LN N) uv.2 ∨ inPH (rhoN N) (LN N) uv.2) then
      |(ft V (mom (LN N) (uv.1 - uv.2))).re * lam V w (rhoN N) (LN N) uv.1 *
        lam V w (rhoN N) (LN N) uv.2| *
        ((rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2 /
          (1 - (rhoN N * lam V w (rhoN N) (LN N) uv.1) ^ 2)) *
        (rhoN N ^ (1/400 : ℝ) +
          |rhoN N * lam V w (rhoN N) (LN N) uv.1| ^ (2 * Real.sqrt (mc (rhoN N)))) else 0
    with hfTdef
  set gg : Idx × Idx → ℝ := fun nm => if nm.1 ≠ 0 ∧ nm.2 ≠ 0 then
      |lam V w (rhoN N) (LN N) nm.1 * (ft V (mom (LN N) (nm.1 - nm.2))).re *
        lam V w (rhoN N) (LN N) nm.2| else 0 with hggdef
  set Dq := (Expect.Q (trialState V w kc N) [0, 0] - Expect.Q (trialState V w kc N) [0]) /
    (LN N ^ 3) ^ 2 with hDq
  set r := rhoN N ^ (1/400 : ℝ) with hrdef
  -- nonnegativity
  have hf2_0 : ∀ x, 0 ≤ f2 x := fun x => by
    simp only [hf2def]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (hQ0 _)
    · exact le_rfl
  have hf1_0 : ∀ x, 0 ≤ f1 x := fun x => by
    simp only [hf1def]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (hQ0 _)
    · exact le_rfl
  have hfL_0 : ∀ x, 0 ≤ fL x := fun x => by
    simp only [hfLdef]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (by linarith [hQ0 [x.1]])
    · exact le_rfl
  have hfT_0 : ∀ x, 0 ≤ fT x := fun x => by
    simp only [hfTdef]
    split_ifs with h
    · exact mul_nonneg (mul_nonneg (abs_nonneg _) (hX0 _ h.1)) (hT0 _)
    · exact le_rfl
  have hgg_0 : ∀ x, 0 ≤ gg x := fun x => by
    simp only [hggdef]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  -- summability of `a` and `b`
  have has : Summable a := by
    refine Summable.of_norm_bounded hggs (fun x => ?_)
    simp only [hadef, hggdef]
    by_cases h : inP (rhoN N) (LN N) x.1 ∧ inP (rhoN N) (LN N) x.2 ∧ x.1 ≠ x.2 ∧ x.1 + x.2 ≠ 0
    · rw [ite_eq_left h, ite_eq_left ⟨S3Bound_inP_ne_zero hρ h.1, S3Bound_inP_ne_zero hρ h.2.1⟩,
        Real.norm_eq_abs, mul_comm ((ft V (mom (LN N) (x.1 - x.2))).re)]
    · rw [ite_eq_right h, norm_zero]
      split_ifs
      · exact abs_nonneg _
      · exact le_rfl
  have hbs : Summable b := by
    refine Summable.of_norm_bounded (hfts.mul_left r⁻¹) (fun x => ?_)
    simp only [hbdef, hfTdef]
    by_cases h : inPL (rhoN N) (LN N) x.1 ∧
        (inPI (rhoN N) (LN N) x.2 ∨ inPH (rhoN N) (LN N) x.2)
    · rw [ite_eq_left h, ite_eq_left h, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hX0 _ h.1)]
      set A := |(ft V (mom (LN N) (x.1 - x.2))).re * lam V w (rhoN N) (LN N) x.1 *
        lam V w (rhoN N) (LN N) x.2|
      have hA : 0 ≤ A := abs_nonneg _
      have hX := hX0 _ h.1
      have hY : 0 ≤ |rhoN N * lam V w (rhoN N) (LN N) x.1| ^ (2 * Real.sqrt (mc (rhoN N))) := by
        positivity
      rw [le_inv_mul_iff₀ hr0]
      have := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hY : r ≤ r + _)
        (mul_nonneg hA hX)
      linarith
    · rw [ite_eq_right h, ite_eq_right h, norm_zero, mul_zero]
  -- the pointwise estimate, block by block
  have hpt : ∀ x : Idx × Idx, y x ≤ Dq * a x + rhoN N ^ 2 * b x + rhoN N ^ 2 * b (x.2, x.1) +
      (rhoN N ^ 2 * ((∫ x, V x) * (f2 x + f2 (x.1, -x.2)) + 2 * (f1 x + f1 (x.2, x.1)) +
        2 * (fL x + fL (x.2, x.1)) + Cm * (fT x + fT (x.2, x.1))) + rhoN N ^ 4 * gg x) := by
    rintro ⟨u, v⟩
    simp only
    have e0 : 0 ≤ rhoN N ^ 2 * ((∫ x, V x) * (f2 (u, v) + f2 (u, -v)) +
        2 * (f1 (u, v) + f1 (v, u)) + 2 * (fL (u, v) + fL (v, u)) +
        Cm * (fT (u, v) + fT (v, u))) + rhoN N ^ 4 * gg (u, v) := by
      have := hf2_0 (u, v); have := hf2_0 (u, -v); have := hf1_0 (u, v); have := hf1_0 (v, u)
      have := hfL_0 (u, v); have := hfL_0 (v, u); have := hfT_0 (u, v); have := hfT_0 (v, u)
      have := hgg_0 (u, v)
      positivity
    by_cases hc : u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ u + v ≠ 0
    swap
    · have hy : y (u, v) = 0 := by simp only [hydef]; exact ite_eq_right hc
      have ha : a (u, v) = 0 := by
        simp only [hadef]
        exact ite_eq_right fun h => hc ⟨S3Bound_inP_ne_zero hρ h.1,
          S3Bound_inP_ne_zero hρ h.2.1, h.2.2.1, h.2.2.2⟩
      have hb : b (u, v) = 0 := by
        simp only [hbdef]
        exact ite_eq_right fun h => hc ⟨Regions_PL_ne_zero hρ h.1,
          S3Bound_inP_ne_zero hρ (S3Bound_IH_P h.2), (S3Bound_L_IH_ne hρ h.1 h.2).1,
          (S3Bound_L_IH_ne hρ h.1 h.2).2⟩
      have hb' : b (v, u) = 0 := by
        simp only [hbdef]
        exact ite_eq_right fun h => hc ⟨S3Bound_inP_ne_zero hρ (S3Bound_IH_P h.2),
          Regions_PL_ne_zero hρ h.1, Ne.symm (S3Bound_L_IH_ne hρ h.1 h.2).1,
          by rw [add_comm]; exact (S3Bound_L_IH_ne hρ h.1 h.2).2⟩
      rw [hy, ha, hb, hb']
      linarith
    have hy : y (u, v) = (ft V (mom (LN N) (u - v))).re *
        (Expect.E4 (trialState V w kc N) u (-u) v (-v)).re := by
      simp only [hydef]
      exact ite_eq_left hc
    by_cases hPP : inP (rhoN N) (LN N) u ∧ inP (rhoN N) (LN N) v
    swap
    · have hE := S3Bound_E4_zero V w kc N hc.1 hc.2.1 hPP
      rw [hE, Complex.zero_re, mul_zero] at hy
      have ha : a (u, v) = 0 := by
        simp only [hadef]
        exact ite_eq_right fun h => hPP ⟨h.1, h.2.1⟩
      have hb : b (u, v) = 0 := by
        simp only [hbdef]
        exact ite_eq_right fun h => hPP ⟨Or.inl h.1, S3Bound_IH_P h.2⟩
      have hb' : b (v, u) = 0 := by
        simp only [hbdef]
        exact ite_eq_right fun h => hPP ⟨S3Bound_IH_P h.2, Or.inl h.1⟩
      rw [hy, ha, hb, hb']
      linarith
    have hVr := S3Bound_abs_V_le hV (mom (LN N) (u - v))
    have hVs := congrArg Complex.re (S3Bound_V_swap hV (LN N) u v)
    have hlv := Regions_lam_neg V w (rhoN N) (LN N) v
    have ha : a (u, v) = (ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) u *
        lam V w (rhoN N) (LN N) v := by
      simp only [hadef]
      exact ite_eq_left ⟨hPP.1, hPP.2, hc.2.2.1, hc.2.2.2⟩
    have v2 : f2 (u, v) = |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| *
        Expect.Q (trialState V w kc N) [u, v] := by
      simp only [hf2def]
      exact ite_eq_left hPP
    have v2' : f2 (u, -v) = |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| *
        Expect.Q (trialState V w kc N) [u, -v] := by
      simp only [hf2def]
      rw [ite_eq_left ⟨hPP.1, S3Bound_inP_neg.2 hPP.2⟩, hlv]
    rcases hPP.1 with hLu | hIu
    · rcases hPP.2 with hLv | hIv
      · -- `u, v ∈ P_L`: (7.46) [u-uv-vPL]
        have hE := Eq7_46 hg kc hN1 hLu hLv hc.2.2.1 hc.2.2.2
        rw [mul_div_assoc] at hE
        have key := S3Bound_alg_L hE (hVL' u v hLu hLv) hVr (hQ0 _)
        have hb : b (u, v) = 0 := by
          simp only [hbdef]
          exact ite_eq_right fun h => S3Bound_IH_not_L hρ h.2 hLv
        have hb' : b (v, u) = 0 := by
          simp only [hbdef]
          exact ite_eq_right fun h => S3Bound_IH_not_L hρ h.2 hLu
        have vL : fL (u, v) = |(ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) u *
            lam V w (rhoN N) (LN N) v| * (Expect.Q (trialState V w kc N) [u] + 1) := by
          simp only [hfLdef]
          exact ite_eq_left ⟨hLu, hLv⟩
        have vL' : fL (v, u) = |(ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) u *
            lam V w (rhoN N) (LN N) v| * (Expect.Q (trialState V w kc N) [v] + 1) := by
          simp only [hfLdef]
          rw [ite_eq_left ⟨hLv, hLu⟩, hVs, mul_right_comm _ (lam V w (rhoN N) (LN N) v)]
        rw [hy, ha, hb, hb']
        rw [← v2, ← vL, ← vL'] at key
        have := hf2_0 (u, -v); have := hf1_0 (u, v); have := hf1_0 (v, u)
        have := hfT_0 (u, v); have := hfT_0 (v, u); have := hgg_0 (u, v)
        have k1 := mul_nonneg hρ2 (mul_nonneg hV0 (hf2_0 (u, -v)))
        have k2 := mul_nonneg hρ2 (add_nonneg (hf1_0 (u, v)) (hf1_0 (v, u)))
        have k3 := mul_nonneg hρ2 (mul_nonneg hCm0 (add_nonneg (hfT_0 (u, v)) (hfT_0 (v, u))))
        have k4 := mul_nonneg hρ4 (hgg_0 (u, v))
        linarith
      · -- `u ∈ P_L`, `v ∈ P_I ∪ P_H`: (7.45) [u-uv-vPLMH]
        have hE := (S3Bound_re_sub _ _).trans (h45' u v hLu hIv)
        have hY : 0 ≤ |rhoN N * lam V w (rhoN N) (LN N) u| ^ (2 * Real.sqrt (mc (rhoN N))) := by
          positivity
        have key := S3Bound_alg_mixed hE hVr (hQ0 _) (hQ0 _) (hQ0 _) (hX0 u hLu) hr0.le hY
          hC7m hCm1
        have hb : b (u, v) = (ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) u *
            lam V w (rhoN N) (LN N) v * ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
              (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2)) := by
          simp only [hbdef]
          exact ite_eq_left ⟨hLu, hIv⟩
        have hb' : b (v, u) = 0 := by
          simp only [hbdef]
          exact ite_eq_right fun h => S3Bound_IH_not_L hρ hIv h.1
        have v1' : f1 (v, u) = |(ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) u *
            lam V w (rhoN N) (LN N) v| * Expect.Q (trialState V w kc N) [v] := by
          simp only [hf1def]
          rw [ite_eq_left ⟨hIv, hPP.1⟩, hVs, mul_right_comm _ (lam V w (rhoN N) (LN N) v)]
        have vT : fT (u, v) = |(ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) u *
            lam V w (rhoN N) (LN N) v| * ((rhoN N * lam V w (rhoN N) (LN N) u) ^ 2 /
              (1 - (rhoN N * lam V w (rhoN N) (LN N) u) ^ 2)) *
            (r + |rhoN N * lam V w (rhoN N) (LN N) u| ^ (2 * Real.sqrt (mc (rhoN N)))) := by
          simp only [hfTdef]
          exact ite_eq_left ⟨hLu, hIv⟩
        rw [hy, ha, hb']
        rw [← v2, ← v2', ← v1', ← vT, ← hb] at key
        have k1 := mul_nonneg hρ2 (hf1_0 (u, v))
        have k2 := mul_nonneg hρ2 (add_nonneg (hfL_0 (u, v)) (hfL_0 (v, u)))
        have k3 := mul_nonneg hρ2 (mul_nonneg hCm0 (hfT_0 (v, u)))
        have k4 := mul_nonneg hρ4 (hgg_0 (u, v))
        linarith
    · rcases hPP.2 with hLv | hIv
      · -- `u ∈ P_I ∪ P_H`, `v ∈ P_L`: (7.45) [u-uv-vPLMH] at `(v, u)` and Lemma 7.1 [id4a]
        have hE0 := h45' v u hLv hIu
        rw [S3Bound_E4_swap hΨ u v] at hE0
        have hE := (S3Bound_re_sub _ _).trans hE0
        rw [Complex.conj_re, S3Bound_Q_comm (trialState V w kc N) u v,
          S3Bound_Q_neg_swap V w kc N u v] at hE
        have hY : 0 ≤ |rhoN N * lam V w (rhoN N) (LN N) v| ^ (2 * Real.sqrt (mc (rhoN N))) := by
          positivity
        have key := S3Bound_alg_mixed hE hVr (hQ0 _) (hQ0 _) (hQ0 _) (hX0 v hLv) hr0.le hY
          hC7m hCm1
        have ha' : a (u, v) = (ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) v *
            lam V w (rhoN N) (LN N) u := by
          rw [ha]
          ring
        have hb : b (u, v) = 0 := by
          simp only [hbdef]
          exact ite_eq_right fun h => S3Bound_IH_not_L hρ hIu h.1
        have hb' : b (v, u) = (ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) v *
            lam V w (rhoN N) (LN N) u * ((rhoN N * lam V w (rhoN N) (LN N) v) ^ 2 /
              (1 - (rhoN N * lam V w (rhoN N) (LN N) v) ^ 2)) := by
          simp only [hbdef]
          rw [ite_eq_left ⟨hLv, hIu⟩, hVs]
        have v2s : f2 (u, v) = |lam V w (rhoN N) (LN N) v * lam V w (rhoN N) (LN N) u| *
            Expect.Q (trialState V w kc N) [u, v] := by
          rw [v2, mul_comm (lam V w (rhoN N) (LN N) u)]
        have v2s' : f2 (u, -v) = |lam V w (rhoN N) (LN N) v * lam V w (rhoN N) (LN N) u| *
            Expect.Q (trialState V w kc N) [u, -v] := by
          rw [v2', mul_comm (lam V w (rhoN N) (LN N) u)]
        have v1 : f1 (u, v) = |(ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) v *
            lam V w (rhoN N) (LN N) u| * Expect.Q (trialState V w kc N) [u] := by
          simp only [hf1def]
          rw [ite_eq_left ⟨hIu, hPP.2⟩, mul_right_comm _ (lam V w (rhoN N) (LN N) u)]
        have vT' : fT (v, u) = |(ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) v *
            lam V w (rhoN N) (LN N) u| * ((rhoN N * lam V w (rhoN N) (LN N) v) ^ 2 /
              (1 - (rhoN N * lam V w (rhoN N) (LN N) v) ^ 2)) *
            (r + |rhoN N * lam V w (rhoN N) (LN N) v| ^ (2 * Real.sqrt (mc (rhoN N)))) := by
          simp only [hfTdef]
          rw [ite_eq_left ⟨hLv, hIu⟩, hVs]
        rw [hy, hb]
        rw [← hb', ← vT', ← v1, ← v2s, ← v2s', ← ha'] at key
        have k1 := mul_nonneg hρ2 (hf1_0 (v, u))
        have k2 := mul_nonneg hρ2 (add_nonneg (hfL_0 (u, v)) (hfL_0 (v, u)))
        have k3 := mul_nonneg hρ2 (mul_nonneg hCm0 (hfT_0 (u, v)))
        have k4 := mul_nonneg hρ4 (hgg_0 (u, v))
        linarith
      · -- `u, v ∈ P_I ∪ P_H`: (7.44) [u-uv-vPMH]
        have hE := (S3Bound_re_sub _ _).trans (h44' u v hIu hIv hc.2.2.1 hc.2.2.2)
        rw [mul_div_assoc] at hE
        have key := S3Bound_alg_IH hE hVr (hQ0 _) (hQ0 _) (hQ0 _) (hQ0 _)
        have hb : b (u, v) = 0 := by
          simp only [hbdef]
          exact ite_eq_right fun h => S3Bound_IH_not_L hρ hIu h.1
        have hb' : b (v, u) = 0 := by
          simp only [hbdef]
          exact ite_eq_right fun h => S3Bound_IH_not_L hρ hIv h.1
        have v1 : f1 (u, v) = |(ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) u *
            lam V w (rhoN N) (LN N) v| * Expect.Q (trialState V w kc N) [u] := by
          simp only [hf1def]
          exact ite_eq_left ⟨hIu, hPP.2⟩
        have v1' : f1 (v, u) = |(ft V (mom (LN N) (u - v))).re * lam V w (rhoN N) (LN N) u *
            lam V w (rhoN N) (LN N) v| * Expect.Q (trialState V w kc N) [v] := by
          simp only [hf1def]
          rw [ite_eq_left ⟨hIv, hPP.1⟩, hVs, mul_right_comm _ (lam V w (rhoN N) (LN N) v)]
        have vg : gg (u, v) = |lam V w (rhoN N) (LN N) u * (ft V (mom (LN N) (u - v))).re *
            lam V w (rhoN N) (LN N) v| := by
          simp only [hggdef]
          exact ite_eq_left ⟨hc.1, hc.2.1⟩
        rw [hy, ha, hb, hb']
        rw [← v1, ← v1', ← v2, ← v2', ← vg] at key
        have k2 := mul_nonneg hρ2 (add_nonneg (hfL_0 (u, v)) (hfL_0 (v, u)))
        have k3 := mul_nonneg hρ2 (mul_nonneg hCm0 (add_nonneg (hfT_0 (u, v)) (hfT_0 (v, u))))
        linarith
  -- summation, with the reindexings `(u, v) ↦ (v, u)` and `v ↦ −v`
  have hsw : ∀ {f : Idx × Idx → ℝ}, Summable f →
      HasSum (fun x : Idx × Idx => f (x.2, x.1)) (∑' x, f x) :=
    fun hf => (Equiv.prodComm Idx Idx).hasSum_iff.mpr hf.hasSum
  have hng : HasSum (fun x : Idx × Idx => f2 (x.1, -x.2)) (∑' x, f2 x) :=
    (Equiv.prodCongr (Equiv.refl Idx) (Equiv.neg Idx)).hasSum_iff.mpr hf2s.hasSum
  have hR1 := ((has.hasSum.mul_left Dq).add (hbs.hasSum.mul_left (rhoN N ^ 2))).add
    ((hsw hbs).mul_left (rhoN N ^ 2))
  have hR2 := (((((hf2s.hasSum.add hng).mul_left (∫ x, V x)).add
      ((hf1s.hasSum.add (hsw hf1s)).mul_left 2)).add
      ((hfLs.hasSum.add (hsw hfLs)).mul_left 2)).add
      ((hfts.hasSum.add (hsw hfts)).mul_left Cm)).mul_left (rhoN N ^ 2)
  have hR := hR1.add (hR2.add (hggs.hasSum.mul_left (rhoN N ^ 4)))
  have hle := hasSum_le hpt hys.hasSum hR
  have hL3 : 0 < LN N ^ 3 := by positivity
  have hW : 0 ≤ ((LN N ^ 3) ^ 2)⁻¹ := by positivity
  have hle' := mul_le_mul_of_nonneg_left hle hW
  have e1 : ((LN N ^ 3)⁻¹ * ∑' uv, y uv) / LN N ^ 3 =
      ((LN N ^ 3) ^ 2)⁻¹ * ∑' uv, y uv := by
    field_simp
  rw [e1]
  set P := rhoN N ^ (5/2 + 1/400 : ℝ) with hP
  have hexp1 : rhoN N ^ (5/2 + 1/200 : ℝ) ≤ P := S3Bound_rpow_le hρ hρ1 (by norm_num)
  have hexpL : rhoN N ^ (3 - 3/200 : ℝ) ≤ P := S3Bound_rpow_le hρ hρ1 (by norm_num)
  have hexp4 : rhoN N ^ 4 ≤ P := by
    rw [hP, ← Real.rpow_natCast]
    exact S3Bound_rpow_le hρ hρ1 (by norm_num)
  have b2 := mul_le_mul_of_nonneg_left (hf2B.trans (mul_le_mul_of_nonneg_left hexp1 hC₁))
    (by positivity : (0 : ℝ) ≤ 2 * ∫ x, V x)
  have b1 := mul_le_mul_of_nonneg_left (hf1B.trans (mul_le_mul_of_nonneg_left hexp1 hC₂))
    (by norm_num : (0 : ℝ) ≤ 4)
  have bL := mul_le_mul_of_nonneg_left (hfLB.trans (mul_le_mul_of_nonneg_left hexpL hC₃))
    (by norm_num : (0 : ℝ) ≤ 4)
  have bT := mul_le_mul_of_nonneg_left hftB (by positivity : (0 : ℝ) ≤ 2 * Cm)
  have bg := (mul_le_mul_of_nonneg_left hggB hρ4).trans (mul_le_mul_of_nonneg_right hexp4 hK)
  linarith

end LHYUpper
