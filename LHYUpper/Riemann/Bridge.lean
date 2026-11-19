import LHYUpper.Riemann.MomentumSums
import LHYUpper.Scattering.Lambda
import LHYUpper.Scattering.MomentumG

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! The local hypotheses `MomDecay` of the lattice sums of §4–§10 hold for `V_p = Re V̂_p` and
`g_p = Re ĝ_p` with one constant, and `λ_n` has the decay of facts (2) and (5) before (7.65)
[temp8.73], uniformly in `L`. -/

/-- `((1 + x)^k)⁻¹ ≤ (1 + x)^{-M}` for `x ≥ 0` and `M ≤ k`. -/
private lemma Bridge_weight_le {x M : ℝ} (hx : 0 ≤ x) {k : ℕ} (hk : M ≤ k) :
    ((1 + x) ^ k)⁻¹ ≤ (1 + x) ^ (-M) := by
  have h1 : (1 : ℝ) ≤ 1 + x := by linarith
  have h := Real.rpow_le_rpow_of_exponent_le h1 (show -(k : ℝ) ≤ -M by linarith)
  rwa [Real.rpow_neg (by linarith), Real.rpow_natCast] at h

/-- `(1 + x)^{-M} ≥ 2^{-|M|}` for `0 ≤ x ≤ 1`, in the form `1 ≤ 2^{|M|} (1 + x)^{-M}`. -/
private lemma Bridge_weight_ge {x M : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 ≤ (2 : ℝ) ^ |M| * (1 + x) ^ (-M) := by
  have h1 : (1 : ℝ) ≤ 1 + x := by linarith
  have h0 : (0 : ℝ) < 1 + x := by linarith
  have ha : 0 < (1 + x) ^ |M| := Real.rpow_pos_of_pos h0 _
  have hb : (1 + x) ^ |M| ≤ (2 : ℝ) ^ |M| :=
    Real.rpow_le_rpow h0.le (by linarith) (abs_nonneg M)
  have hc : (1 + x) ^ (-|M|) ≤ (1 + x) ^ (-M) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by linarith [le_abs_self M])
  rw [Real.rpow_neg h0.le] at hc
  calc (1 : ℝ) = (1 + x) ^ |M| * ((1 + x) ^ |M|)⁻¹ := (mul_inv_cancel₀ ha.ne').symm
    _ ≤ (2 : ℝ) ^ |M| * (1 + x) ^ (-M) :=
        mul_le_mul hb hc (by positivity) (by positivity)

/-- The real part of a Schwartz function `S : ℝ³ → ℂ` satisfies `MomDecay` for every `M`:
the bound from `(1 + |p|)^k |S p|` and the Lipschitz estimate from the mean value inequality
on the unit ball around `p`, on which `1 + |p| ≤ 2 (1 + |x|)`. -/
private lemma Bridge_schwartz_momDecay (S : SchwartzMap R3 ℂ) (M : ℝ) :
    ∃ C, MomDecay (fun p => (S p).re) C M := by
  set k : ℕ := ⌈|M|⌉₊ + 1 with hk
  have hMk : M ≤ k := by
    have h1 : |M| ≤ ⌈|M|⌉₊ := Nat.le_ceil _
    have h2 : M ≤ |M| := le_abs_self M
    rw [hk]
    push_cast
    linarith
  set A : ℝ := 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S
    with hA
  set D : ℝ := 2 ^ k * (Finset.Iic (k, 1)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S
    with hD
  have hA0 : ∀ p, (1 + ‖p‖) ^ k * ‖S p‖ ≤ A := fun p => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
      le_rfl le_rfl S p
    rwa [norm_iteratedFDeriv_zero] at h
  have hD1 : ∀ p, (1 + ‖p‖) ^ k * ‖fderiv ℝ S p‖ ≤ D := fun p => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 1)) (k := k) (n := 1)
      le_rfl le_rfl S p
    rwa [norm_iteratedFDeriv_one] at h
  have hAnn : 0 ≤ A := le_trans (by positivity) (hA0 0)
  have hDnn : 0 ≤ D := le_trans (by positivity) (hD1 0)
  have hSb : ∀ p, ‖S p‖ ≤ A * ((1 + ‖p‖) ^ k)⁻¹ := fun p => by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hA0 p
  have hSd : ∀ p, ‖fderiv ℝ S p‖ ≤ D * ((1 + ‖p‖) ^ k)⁻¹ := fun p => by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hD1 p
  refine ⟨max A (2 ^ k * D), fun p => ?_, fun p q hq => ?_⟩
  · have hB : 0 ≤ (1 + ‖p‖) ^ (-M) := Real.rpow_nonneg (by positivity) _
    calc |(S p).re| ≤ ‖S p‖ := Complex.abs_re_le_norm _
      _ ≤ A * ((1 + ‖p‖) ^ k)⁻¹ := hSb p
      _ ≤ A * (1 + ‖p‖) ^ (-M) :=
          mul_le_mul_of_nonneg_left (Bridge_weight_le (norm_nonneg p) hMk) hAnn
      _ ≤ max A (2 ^ k * D) * (1 + ‖p‖) ^ (-M) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hB
  · have hB : 0 < (1 + ‖p‖) ^ (-M) := Real.rpow_pos_of_pos (by positivity) _
    have hdiff : ∀ x : R3, HasFDerivAt (fun y => (S y).re)
        (Complex.reCLM.comp (fderiv ℝ S x)) x := fun x =>
      Complex.reCLM.hasFDerivAt.comp x (S.differentiable x).hasFDerivAt
    have hbound : ∀ x ∈ Metric.closedBall p 1,
        ‖fderiv ℝ (fun y => (S y).re) x‖ ≤ 2 ^ k * D * (1 + ‖p‖) ^ (-M) := by
      intro x hx
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      have hxp : 1 + ‖p‖ ≤ 2 * (1 + ‖x‖) := by
        have : ‖p‖ ≤ ‖x‖ + ‖x - p‖ := by
          calc ‖p‖ = ‖x - (x - p)‖ := by rw [sub_sub_cancel]
            _ ≤ ‖x‖ + ‖x - p‖ := norm_sub_le _ _
        linarith [norm_nonneg x]
      have hdec : ((1 + ‖x‖) ^ k)⁻¹ ≤ 2 ^ k * ((1 + ‖p‖) ^ k)⁻¹ := by
        have h2 : (1 + ‖p‖) ^ k ≤ (2 * (1 + ‖x‖)) ^ k :=
          pow_le_pow_left₀ (by positivity) hxp k
        rw [mul_pow] at h2
        have h3 : ((1 + ‖x‖) ^ k)⁻¹ ≤ ((1 + ‖p‖) ^ k / 2 ^ k)⁻¹ :=
          inv_anti₀ (by positivity) ((div_le_iff₀ (by positivity)).2 (by linarith [h2]))
        refine h3.trans (le_of_eq ?_)
        rw [inv_div, div_eq_mul_inv]
      rw [(hdiff x).fderiv]
      calc ‖Complex.reCLM.comp (fderiv ℝ S x)‖ ≤ ‖fderiv ℝ S x‖ := by
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            rw [Complex.reCLM_norm, one_mul]
        _ ≤ D * ((1 + ‖x‖) ^ k)⁻¹ := hSd x
        _ ≤ D * (2 ^ k * ((1 + ‖p‖) ^ k)⁻¹) := mul_le_mul_of_nonneg_left hdec hDnn
        _ ≤ D * (2 ^ k * (1 + ‖p‖) ^ (-M)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (Bridge_weight_le (norm_nonneg p) hMk) (by positivity)) hDnn
        _ = 2 ^ k * D * (1 + ‖p‖) ^ (-M) := by ring
    have hq' : q ∈ Metric.closedBall p 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hq
    have hMV := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun y => (S y).re)
      (s := Metric.closedBall p 1) (x := p) (y := q) (fun x _ => (hdiff x).differentiableAt)
      hbound (convex_closedBall p 1) (Metric.mem_closedBall_self zero_le_one) hq'
    rw [Real.norm_eq_abs] at hMV
    calc |(S q).re - (S p).re| ≤ 2 ^ k * D * (1 + ‖p‖) ^ (-M) * ‖q - p‖ := hMV
      _ = (2 ^ k * D) * ‖q - p‖ * (1 + ‖p‖) ^ (-M) := by ring
      _ ≤ max A (2 ^ k * D) * ‖q - p‖ * (1 + ‖p‖) ^ (-M) := by
          gcongr
          exact le_max_right _ _

variable {V w : R3 → ℝ}

/-- `MomDecay` is monotone in its constant. -/
theorem Bridge_momDecay_mono {f : R3 → ℝ} {C C' M : ℝ} (h : MomDecay f C M) (hC : C ≤ C') :
    MomDecay f C' M := by
  refine ⟨fun p => ?_, fun p q hq => ?_⟩
  · have hB : 0 ≤ (1 + ‖p‖) ^ (-M) := Real.rpow_nonneg (by positivity) _
    exact (h.bound p).trans (mul_le_mul_of_nonneg_right hC hB)
  · have hB : 0 ≤ (1 + ‖p‖) ^ (-M) := Real.rpow_nonneg (by positivity) _
    exact (h.lip p q hq).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (norm_nonneg _)) hB)

/-- `p ↦ Re V̂_p` is bounded and locally Lipschitz with decay `(1 + |p|)^{-M}`, for every `M`
(`V` is a Schwartz function). -/
theorem Bridge_momDecay_V (hV : PotentialHyp V) (M : ℝ) :
    ∃ C, MomDecay (fun p => (ft V p).re) C M := by
  obtain ⟨S, hS⟩ := scat_ft_V_schwartz hV
  obtain ⟨C, hC⟩ := Bridge_schwartz_momDecay S M
  rw [hS] at hC
  exact ⟨C, hC⟩

/-- `p ↦ g_p = Re ĝ_p` is bounded and locally Lipschitz with decay `(1 + |p|)^{-M}`, for every `M`. -/
theorem Bridge_momDecay_g (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (M : ℝ) :
    ∃ C, MomDecay (fun p => (ft (gfun V w) p).re) C M := by
  obtain ⟨S, hS⟩ := scat_ft_g_schwartz hV hw
  obtain ⟨C, hC⟩ := Bridge_schwartz_momDecay S M
  rw [hS] at hC
  exact ⟨C, hC⟩

/-- One constant for `V_p` and `g_p`, in the form the lattice sums of §4–§10 take them. -/
theorem Bridge_momDecay (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (M : ℝ) :
    ∃ C, MomDecay (fun p => (ft V p).re) C M ∧ MomDecay (fun p => (ft (gfun V w) p).re) C M := by
  obtain ⟨C₁, h₁⟩ := Bridge_momDecay_V hV M
  obtain ⟨C₂, h₂⟩ := Bridge_momDecay_g hV hw M
  exact ⟨max C₁ C₂, Bridge_momDecay_mono h₁ (le_max_left _ _),
    Bridge_momDecay_mono h₂ (le_max_right _ _)⟩

/-- The decay of `λ` used by facts (2) and (5) before (7.65) [temp8.73]: for `ρ` small,
`|λ_n| ≤ c |p_n|^{-2} (1 + |p_n|)^{-M}` for every `n ≠ 0`, uniformly in `L`. -/
theorem Bridge_lam_decay (hV : PotentialHyp V) (hw : IsScatteringSolution V w) (M : ℝ) :
    ∃ c, ∀ᶠ ρ in 𝓝[>] 0, ∀ (L : ℝ) (n : Idx), n ≠ 0 →
      |lam V w ρ L n| ≤ c * ‖mom L n‖ ^ (-2 : ℝ) * (1 + ‖mom L n‖) ^ (-M) := by
  obtain ⟨Cg, hCg⟩ := Bridge_momDecay_g hV hw M
  refine ⟨max Cg ((2 : ℝ) ^ |M| * g0 V w), ?_⟩
  have h1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ := self_mem_nhdsWithin
  have h2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [h1, h2] with ρ hρ hρ1 L n _
  have hr0 : 0 ≤ ‖mom L n‖ := norm_nonneg _
  have hneg2 : ‖mom L n‖ ^ (-2 : ℝ) = (‖mom L n‖ ^ 2)⁻¹ := by
    rw [Real.rpow_neg hr0, Real.rpow_two]
  have hW : 0 ≤ (1 + ‖mom L n‖) ^ (-M) := Real.rpow_nonneg (by positivity) _
  have hI : 0 ≤ (‖mom L n‖ ^ 2)⁻¹ := by positivity
  rw [hneg2]
  by_cases hPL : inPL ρ L n
  · have hε : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
    have hs : 0 < ρ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
    have hle : |lam V w ρ L n| ≤ g0 V w / ‖mom L n‖ ^ 2 :=
      scat_lam_abs_le hV hw ρ hρ L n (Or.inl hPL)
    have hr1 : ‖mom L n‖ ≤ 1 := by
      refine hPL.2.trans ?_
      rw [inv_mul_le_iff₀ hε, mul_one]
      exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1.le (by norm_num)
    have hge := Bridge_weight_ge (M := M) hr0 hr1
    have hX : 0 ≤ g0 V w * (‖mom L n‖ ^ 2)⁻¹ := by
      have := scat_g0_pos hV hw
      positivity
    calc |lam V w ρ L n| ≤ g0 V w / ‖mom L n‖ ^ 2 := hle
      _ = g0 V w * (‖mom L n‖ ^ 2)⁻¹ := div_eq_mul_inv _ _
      _ ≤ g0 V w * (‖mom L n‖ ^ 2)⁻¹ * ((2 : ℝ) ^ |M| * (1 + ‖mom L n‖) ^ (-M)) :=
          le_mul_of_one_le_right hX hge
      _ = ((2 : ℝ) ^ |M| * g0 V w) * (‖mom L n‖ ^ 2)⁻¹ * (1 + ‖mom L n‖) ^ (-M) := by ring
      _ ≤ max Cg ((2 : ℝ) ^ |M| * g0 V w) * (‖mom L n‖ ^ 2)⁻¹ * (1 + ‖mom L n‖) ^ (-M) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hI) hW
  · rw [scat_lam_of_not_PL ρ L n hPL, abs_neg]
    unfold wmom
    rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖mom L n‖ ^ 2), div_eq_mul_inv]
    calc |(ft (gfun V w) (mom L n)).re| * (‖mom L n‖ ^ 2)⁻¹
        ≤ Cg * (1 + ‖mom L n‖) ^ (-M) * (‖mom L n‖ ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (hCg.bound _) hI
      _ = Cg * (‖mom L n‖ ^ 2)⁻¹ * (1 + ‖mom L n‖) ^ (-M) := by ring
      _ ≤ max Cg ((2 : ℝ) ^ |M| * g0 V w) * (‖mom L n‖ ^ 2)⁻¹ * (1 + ‖mom L n‖) ^ (-M) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hI) hW

end LHYUpper
