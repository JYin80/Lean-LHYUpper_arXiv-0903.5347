module

public import LHYUpper.Kinetic.Basic
public import LHYUpper.Kinetic.LowMid
public import LHYUpper.Kinetic.MainTerm
public import LHYUpper.Particles.Totals
public import LHYUpper.Particles.Lemma55
public import LHYUpper.Assembly.Theorem31

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Auxiliary facts on the parameters -/

/-- `ρ_N → 0`. -/
private lemma Lemma41_rho_tendsto : Tendsto (fun N : ℕ => rhoN N) atTop (𝓝 0) := by
  have := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 8/17)).comp
    tendsto_natCast_atTop_atTop
  simpa [rhoN, Function.comp_def] using this

/-- For `p > 0` and `δ > 0`, eventually `ρ_N^p ≤ δ`. -/
private lemma Lemma41_rpow_small {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, rhoN N ^ p ≤ δ := by
  have h1 : Tendsto (fun N : ℕ => rhoN N ^ p) atTop (𝓝 0) := by
    have := Lemma41_rho_tendsto.rpow_const (p := p) (Or.inr hp.le)
    simpa [Real.zero_rpow hp.ne'] using this
  exact h1.eventually (Iic_mem_nhds hδ)

/-- A single occupation number is at most the particle number. -/
private lemma Lemma41_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases hn : n ∈ α.support
  · exact Finset.single_le_sum (f := fun n => α n) (fun _ _ => Nat.zero_le _) hn
  · rw [Finsupp.notMem_support_iff.mp hn]; exact Nat.zero_le _

/-- `Q_Ψ({u, m}) ≥ 0`. -/
private lemma Lemma41_Qm_nonneg (Ψ : Occ → ℂ) (u : Idx) (m : ℕ) :
    0 ≤ Expect.Qm Ψ [(u, m)] :=
  tsum_nonneg fun α => by split_ifs <;> positivity

/-- `Q_Ψ(n) ≥ 0`. -/
private lemma Lemma41_Q_nonneg (Ψ : Occ → ℂ) (n : Idx) : 0 ≤ Expect.Q Ψ [n] := by
  unfold Expect.Q
  refine tsum_nonneg fun α => ?_
  simp only [List.map, List.prod_cons, List.prod_nil, mul_one]
  positivity

/-- `Q_Ψ({u, m}) = 0` for `m > N`. -/
private lemma Lemma41_Qm_eq_zero (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (u : Idx)
    {m : ℕ} (hm : N < m) : Expect.Qm (trialState V w kc N) [(u, m)] = 0 := by
  have hΨ := Normalization_isNState V w kc hN
  unfold Expect.Qm
  refine (tsum_congr fun α => ?_).trans tsum_zero
  by_cases hz : trialState V w kc N α = 0
  · simp [hz]
  · have h1 : α u ≤ N := (Lemma41_occ_le_num α u).trans (hΨ.2 α hz).le
    have h2 : ¬ Expect.Ev [(u, m)] α := by
      simp only [Expect.Ev, List.mem_singleton, forall_eq]
      omega
    simp [h2]

/-- A function on `Idx` supported in `{‖p_n‖ ≤ R}` is summable. -/
private lemma Lemma41_summable_ball {L R : ℝ} (hL : 0 < L) (f : Idx → ℝ)
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
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun n hn => ?_
  by_contra h
  exact hn (hfin.mem_toFinset.2 (hf n h))

/-- Geometric tail: for `a ≥ 0` vanishing beyond `N`, `0 ≤ c ≤ 1/2` and `a_{m+1} ≤ c a_m`,
`Σ_m m a_m ≤ (1 + 2c) Σ_m a_{m+1}`. -/
private lemma Lemma41_geom {a : ℕ → ℝ} {c : ℝ} {N : ℕ} (ha : ∀ m, 0 ≤ a m)
    (haN : ∀ m, N < m → a m = 0) (hc0 : 0 ≤ c) (hc : c ≤ 1/2)
    (hstep : ∀ m, a (m + 1) ≤ c * a m) :
    ∑' m : ℕ, (m : ℝ) * a m ≤ (1 + 2 * c) * ∑' m : ℕ, a (m + 1) := by
  have hs1 : Summable fun m : ℕ => (m : ℝ) * a m :=
    summable_of_ne_finset_zero (s := Finset.range (N + 1)) (fun m hm => by
      rw [haN m (by simp only [Finset.mem_range] at hm; omega), mul_zero])
  have hs2 : Summable fun m : ℕ => a (m + 1) :=
    summable_of_ne_finset_zero (s := Finset.range N) (fun m hm =>
      haN (m + 1) (by simp only [Finset.mem_range] at hm; omega))
  have hs3 : Summable fun m : ℕ => (m : ℝ) * a (m + 1) :=
    summable_of_ne_finset_zero (s := Finset.range N) (fun m hm => by
      rw [haN (m + 1) (by simp only [Finset.mem_range] at hm; omega), mul_zero])
  have hT : ∑' m : ℕ, (m : ℝ) * a m = ∑' m : ℕ, ((m : ℝ) * a (m + 1) + a (m + 1)) := by
    rw [hs1.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one]
    congr 1
    funext m
    ring
  have h1 : ∑' m : ℕ, (m : ℝ) * a (m + 1) ≤ c * ∑' m : ℕ, (m : ℝ) * a m := by
    rw [← tsum_mul_left]
    refine hs3.tsum_le_tsum (fun m => ?_) (hs1.mul_left c)
    have := mul_le_mul_of_nonneg_left (hstep m) (Nat.cast_nonneg (α := ℝ) m)
    linarith [show (m : ℝ) * (c * a m) = c * ((m : ℝ) * a m) by ring]
  have hS0 : 0 ≤ ∑' m : ℕ, a (m + 1) := tsum_nonneg fun m => ha _
  have h2 : ∑' m : ℕ, (m : ℝ) * a m ≤
      c * (∑' m : ℕ, (m : ℝ) * a m) + ∑' m : ℕ, a (m + 1) := by
    have hT' := hT.trans (hs3.tsum_add hs2)
    linarith
  have h3 : ∑' m : ℕ, (m : ℝ) * a m ≤ 2 * ∑' m : ℕ, a (m + 1) := by nlinarith
  nlinarith

/-! ### (6.11) [temp7.16] -/

/-- (6.11) [temp7.16]: for `u ∈ P_H`, `Q_Ψ(u) ≤ (1 + 2ρ^{3/2}) Σ_{m≥1} Q_Ψ({u, m})`. -/
theorem Eq6_11 (V w : R3 → ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPH (rhoN N) (LN N) u →
      Expect.Q (trialState V w kc N) [u] ≤
        (1 + 2 * rhoN N ^ (3/2 : ℝ)) *
          (∑' m : ℕ, Expect.Qm (trialState V w kc N) [(u, m + 1)]) := by
  obtain ⟨C, hC, N₁, h28⟩ := Eq5_28 V w
  set g₁ : ℝ := ∫ x, |gfun V w x| with hg₁def
  have hg₁ : 0 ≤ g₁ := integral_nonneg fun _ => abs_nonneg _
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((eventually_ge_atTop 1).and
    ((Lemma41_rpow_small (p := 12/25) (δ := 1 / (C * g₁ + 1)) (by norm_num)
      (by positivity)).and
     (Lemma41_rpow_small (p := 3/2) (δ := 1/2) (by norm_num) (by norm_num))))
  refine ⟨max N₁ N₂, fun N hN kc u hu => ?_⟩
  obtain ⟨hN1, hs1, hs2⟩ := hN₂ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set Ψ := trialState V w kc N with hΨdef
  have hε0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
  have hu0 : 0 < ‖mom L u‖ := hε0.trans hu
  set c : ℝ := C * ρ ^ 2 * |lam V w ρ L u| / ‖mom L u‖ ^ 2 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hlam : |lam V w ρ L u| ≤ g₁ / ‖mom L u‖ ^ 2 :=
    Particles_lam_abs_le V w ρ L u (fun h => Regions_PL_PH hρ h hu)
  have hε4 : epsP ρ ^ 4 ≤ ‖mom L u‖ ^ 2 * ‖mom L u‖ ^ 2 := by
    rw [← pow_add]
    exact pow_le_pow_left₀ hε0.le hu.le 4
  have hc1 : c ≤ C * g₁ * ρ ^ 2 / epsP ρ ^ 4 := by
    rw [hcdef]
    calc C * ρ ^ 2 * |lam V w ρ L u| / ‖mom L u‖ ^ 2
        ≤ C * ρ ^ 2 * (g₁ / ‖mom L u‖ ^ 2) / ‖mom L u‖ ^ 2 := by gcongr
      _ = C * g₁ * ρ ^ 2 / (‖mom L u‖ ^ 2 * ‖mom L u‖ ^ 2) := by
          field_simp
      _ ≤ C * g₁ * ρ ^ 2 / epsP ρ ^ 4 := by gcongr
  have hsplit : ρ ^ 2 = ρ ^ (3/2 : ℝ) * ρ ^ (12/25 : ℝ) * epsP ρ ^ 4 := by
    unfold epsP
    rw [← Real.rpow_natCast (ρ ^ (1/200 : ℝ)), ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ,
      ← Real.rpow_add hρ, ← Real.rpow_natCast]
    norm_num
  have hcg : C * g₁ * ρ ^ (12/25 : ℝ) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ C * g₁)
    have h' : C * g₁ * (1 / (C * g₁ + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]
      linarith
    linarith
  have hc2 : c ≤ ρ ^ (3/2 : ℝ) := by
    refine hc1.trans ?_
    rw [hsplit, div_le_iff₀ (by positivity)]
    have h32 : 0 ≤ ρ ^ (3/2 : ℝ) * epsP ρ ^ 4 := by positivity
    nlinarith
  have hc3 : c ≤ 1/2 := hc2.trans hs2
  have hstep : ∀ m : ℕ, Expect.Qm Ψ [(u, m + 1)] ≤ c * Expect.Qm Ψ [(u, m)] :=
    fun m => h28 N (le_of_max_le_left hN) kc u hu m
  have hgeom := Lemma41_geom (a := fun m => Expect.Qm Ψ [(u, m)]) (c := c) (N := N)
    (fun m => Lemma41_Qm_nonneg Ψ u m) (fun m hm => Lemma41_Qm_eq_zero V w kc hN1 u hm)
    hc0 hc3 hstep
  have hS0 : 0 ≤ ∑' m : ℕ, Expect.Qm Ψ [(u, m + 1)] :=
    tsum_nonneg fun m => Lemma41_Qm_nonneg Ψ u (m + 1)
  rw [Particles_Q_eq_tsum V w kc hN1 u]
  refine hgeom.trans ?_
  gcongr

/-! ### (6.16) [temp7.20] -/

/-- (6.16) [temp7.20]: for `u ∈ P_H`, the last term of (6.12) [proofubpsiu12] is at most
`λ_u² ρ^{5/2} (4g₀^{3/2}/(3π²) + Cρ^η) + C ρ³ ε_H^{-4} |u|^{-2} (1 + |u|)^{-4}`. -/
theorem Eq6_16 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u : Idx, inPH (rhoN N) (LN N) u →
      4 * rhoN N / LN N ^ 3 *
          (∑' v : Idx, (if inPL (rhoN N) (LN N) v ∧ inPHc (rhoN N) (LN N) kc (v - u) then
            Expect.Q (trialState V w kc N) [v] *
              |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) (v - u)| else 0)) ≤
        lam V w (rhoN N) (LN N) u ^ 2 * rhoN N ^ (5/2 : ℝ) *
            (4 * g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) + C * rhoN N ^ (1/200 : ℝ))
          + C * rhoN N ^ 3 / epsP (rhoN N) ^ 4 / ‖mom (LN N) u‖ ^ 2 *
            ((1 + ‖mom (LN N) u‖) ^ 4)⁻¹ := by
  have hg := scat_g0_pos hV hw
  obtain ⟨Cp, hCp, Np, hpair⟩ := Kinetic_lam_pair hV hw
  obtain ⟨C₅, hC₅, N₅, h5⟩ := Prop5_4_PL hg
  set g := g0 V w with hgdef
  set G₃ : ℝ := g ^ (3/2 : ℝ) / (3 * π ^ 2) with hG₃def
  have hG₃ : 0 ≤ G₃ := by positivity
  refine ⟨max (4 * C₅) (4 * g * Cp * (G₃ + C₅)), le_max_of_le_left (by positivity),
    max (max Np N₅) 1, fun N hN kc u hu => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNp : N ≥ Np := le_trans (le_max_left _ _) (le_of_max_le_left hN)
  have hN5 : N ≥ N₅ := le_trans (le_max_right _ _) (le_of_max_le_left hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set Ψ := trialState V w kc N with hΨdef
  set ε := epsP ρ with hεdef
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hρ _
  have hu0 : 0 < ‖mom L u‖ := hε0.trans hu
  set lu := lam V w ρ L u with hludef
  set d : ℝ := ((1 + ‖mom L u‖) ^ 4)⁻¹ with hddef
  have hd0 : 0 ≤ d := by positivity
  set D : ℝ := g * Cp * ρ ^ (1/2 : ℝ) / ε ^ 4 / ‖mom L u‖ ^ 2 * d with hDdef
  have hD0 : 0 ≤ D := by positivity
  have hlu : |lu| ≤ g / ‖mom L u‖ ^ 2 :=
    scat_lam_abs_le hV hw ρ hρ L u (Or.inr (Or.inr hu))
  have hpt : ∀ v : Idx, (if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
      Expect.Q Ψ [v] * |lu * lam V w ρ L (v - u)| else 0) ≤
      (if inPL ρ L v then Expect.Q Ψ [v] else 0) * (lu ^ 2 + D) := by
    intro v
    by_cases hv : inPL ρ L v
    · have hQ := Lemma41_Q_nonneg Ψ v
      have hp := hpair N hNp u v hu hv
      have hvn : ‖mom L v‖ ≤ ε⁻¹ * ρ ^ (1/2 : ℝ) := hv.2
      have hb : |lu * lam V w ρ L (v - u)| ≤ lu ^ 2 + D := by
        rw [abs_mul]
        have h1 : |lam V w ρ L (v - u)| ≤ |lu| + |lam V w ρ L (v - u) - lu| := by
          have := abs_add_le lu (lam V w ρ L (v - u) - lu)
          simpa using this
        have h2 : |lam V w ρ L (v - u) - lu| ≤ Cp / ε ^ 3 * d * (ε⁻¹ * ρ ^ (1/2 : ℝ)) :=
          hp.trans (by gcongr)
        have h3 : |lu| * |lam V w ρ L (v - u) - lu| ≤ D := by
          calc |lu| * |lam V w ρ L (v - u) - lu|
              ≤ (g / ‖mom L u‖ ^ 2) * (Cp / ε ^ 3 * d * (ε⁻¹ * ρ ^ (1/2 : ℝ))) := by
                gcongr
            _ = D := by
                rw [hDdef]
                field_simp
        calc |lu| * |lam V w ρ L (v - u)|
            ≤ |lu| * (|lu| + |lam V w ρ L (v - u) - lu|) := by gcongr
          _ = lu ^ 2 + |lu| * |lam V w ρ L (v - u) - lu| := by rw [mul_add, ← sq, sq_abs]
          _ ≤ lu ^ 2 + D := by linarith
      split_ifs with hc
      · exact mul_le_mul_of_nonneg_left hb hQ
      · positivity
    · simp [hv]
  have hQs : Summable fun v : Idx => Expect.Q Ψ [v] :=
    (Particles_hasSum_Q V w kc hN1).summable
  have hsQ : Summable fun v : Idx => if inPL ρ L v then Expect.Q Ψ [v] else 0 :=
    Summable.of_nonneg_of_le (fun v => by split_ifs <;> simp [Lemma41_Q_nonneg])
      (fun v => by split_ifs <;> simp [Lemma41_Q_nonneg]) hQs
  have hsL : Summable fun v : Idx => if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
      Expect.Q Ψ [v] * |lu * lam V w ρ L (v - u)| else 0 :=
    Summable.of_nonneg_of_le
      (fun v => by split_ifs <;> first | exact le_rfl | positivity [Lemma41_Q_nonneg Ψ v])
      hpt (hsQ.mul_right _)
  have hsum := hsL.tsum_le_tsum hpt (hsQ.mul_right _)
  rw [tsum_mul_right] at hsum
  have h5' := h5 N hN5 kc
  set P := ∑' v : Idx, (if inPL ρ L v then Expect.Q Ψ [v] else 0) with hPdef
  have ht0 : 0 ≤ ρ ^ (1/200 : ℝ) := by positivity
  have ht1 : ρ ^ (1/200 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hX : ρ * ρ ^ (3/2 : ℝ) = ρ ^ (5/2 : ℝ) := by
    rw [← Real.rpow_one_add' hρ.le (by norm_num)]
    norm_num
  have hX3 : ρ ^ (5/2 : ℝ) * ρ ^ (1/2 : ℝ) = ρ ^ 3 := by
    rw [← Real.rpow_add hρ, ← Real.rpow_natCast]
    norm_num
  have hP0 : 0 ≤ (L ^ 3)⁻¹ * P := by
    have : 0 ≤ P := tsum_nonneg fun v => by split_ifs <;> simp [Lemma41_Q_nonneg]
    positivity
  set Cm := max (4 * C₅) (4 * g * Cp * (G₃ + C₅)) with hCmdef
  have hCm1 : 4 * C₅ ≤ Cm := le_max_left _ _
  have hCm2 : 4 * g * Cp * (G₃ + C₅) ≤ Cm := le_max_right _ _
  have hlu2 : 0 ≤ lu ^ 2 := sq_nonneg _
  calc 4 * ρ / L ^ 3 * (∑' v : Idx, (if inPL ρ L v ∧ inPHc ρ L kc (v - u) then
          Expect.Q Ψ [v] * |lu * lam V w ρ L (v - u)| else 0))
      ≤ 4 * ρ / L ^ 3 * (P * (lu ^ 2 + D)) := by gcongr
    _ = 4 * ρ * ((L ^ 3)⁻¹ * P) * (lu ^ 2 + D) := by ring
    _ ≤ 4 * ρ * ((G₃ + C₅ * ρ ^ (1/200 : ℝ)) * ρ ^ (3/2 : ℝ)) * (lu ^ 2 + D) := by gcongr
    _ = lu ^ 2 * (ρ * ρ ^ (3/2 : ℝ)) * (4 * G₃ + 4 * C₅ * ρ ^ (1/200 : ℝ))
          + 4 * g * Cp * (G₃ + C₅ * ρ ^ (1/200 : ℝ)) *
            ((ρ * ρ ^ (3/2 : ℝ)) * ρ ^ (1/2 : ℝ)) / ε ^ 4 / ‖mom L u‖ ^ 2 * d := by
        rw [hDdef]; ring
    _ ≤ lu ^ 2 * ρ ^ (5/2 : ℝ) * (4 * G₃ + Cm * ρ ^ (1/200 : ℝ))
          + Cm * ρ ^ 3 / ε ^ 4 / ‖mom L u‖ ^ 2 * d := by
        rw [hX, hX3]
        have hX0 : 0 ≤ ρ ^ (5/2 : ℝ) := by positivity
        have e1 : 4 * C₅ * ρ ^ (1/200 : ℝ) ≤ Cm * ρ ^ (1/200 : ℝ) :=
          mul_le_mul_of_nonneg_right hCm1 ht0
        have e2 : 4 * g * Cp * (G₃ + C₅ * ρ ^ (1/200 : ℝ)) ≤ Cm := by
          refine le_trans ?_ hCm2
          have : C₅ * ρ ^ (1/200 : ℝ) ≤ C₅ := mul_le_of_le_one_right hC₅ ht1
          have : 0 ≤ 4 * g * Cp := by positivity
          nlinarith
        gcongr
    _ = lu ^ 2 * ρ ^ (5/2 : ℝ) * (4 * g ^ (3/2 : ℝ) / (3 * π ^ 2) + Cm * ρ ^ (1/200 : ℝ))
          + Cm * ρ ^ 3 / ε ^ 4 / ‖mom L u‖ ^ 2 * d := by
        rw [hG₃def]; ring

/-! ### (6.4) [boundspsiu2PHtotal] -/

/-- With `κ = (3π²)⁻¹g^{3/2}` and `κρ^{1/2} ≤ 1/2`: `0 ≤ ρ₀ ≤ ρ` and
`0 ≤ ρ^{5/2} − ρ₀^{5/2} ≤ 3κρ^{5/2}ρ^{1/2}`, for `ρ₀` of (3.14) [defrho0]. -/
private lemma Lemma41_rho0 {g ρ : ℝ} (hρ : 0 < ρ) (hg : 0 ≤ g)
    (hk : (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) * ρ ^ (1/2 : ℝ) ≤ 1/2) :
    0 ≤ rho0 g ρ ∧ rho0 g ρ ≤ ρ ∧ 0 ≤ rho0 g ρ ^ (5/2 : ℝ) ∧
      rho0 g ρ ^ (5/2 : ℝ) ≤ ρ ^ (5/2 : ℝ) ∧
      ρ ^ (5/2 : ℝ) - rho0 g ρ ^ (5/2 : ℝ) ≤
        3 * ((3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ)) * (ρ ^ (5/2 : ℝ) * ρ ^ (1/2 : ℝ)) := by
  set κ := (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) with hκdef
  have hκ : 0 ≤ κ := by positivity
  have hkt : 0 ≤ κ * ρ ^ (1/2 : ℝ) := by positivity
  set x := 1 - κ * ρ ^ (1/2 : ℝ) with hxdef
  have hx0 : 1/2 ≤ x := by linarith
  have hx1 : x ≤ 1 := by linarith
  have h0 : rho0 g ρ = ρ * x := by
    unfold rho0
    have e : ρ ^ (3/2 : ℝ) = ρ * ρ ^ (1/2 : ℝ) := by
      rw [← Real.rpow_one_add' hρ.le (by norm_num)]
      norm_num
    rw [e, hxdef, hκdef]
    ring
  have h5 : rho0 g ρ ^ (5/2 : ℝ) = ρ ^ (5/2 : ℝ) * x ^ (5/2 : ℝ) := by
    rw [h0, Real.mul_rpow hρ.le (by linarith)]
  have hx3 : x ^ 3 ≤ x ^ (5/2 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge (by linarith) hx1 (by norm_num)
  have hx52 : x ^ (5/2 : ℝ) ≤ 1 := Real.rpow_le_one (by linarith) hx1 (by norm_num)
  have hx52' : 0 ≤ x ^ (5/2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hb : 1 - x ^ 3 ≤ 3 * (1 - x) := by
    nlinarith [mul_nonneg (sq_nonneg (x - 1)) (by linarith : (0 : ℝ) ≤ x + 2)]
  have hX : 0 ≤ ρ ^ (5/2 : ℝ) := by positivity
  refine ⟨by rw [h0]; nlinarith, by rw [h0]; nlinarith, by rw [h5]; positivity,
    by rw [h5]; nlinarith, ?_⟩
  rw [h5]
  have : 1 - x = κ * ρ ^ (1/2 : ℝ) := by rw [hxdef]; ring
  nlinarith

/-- (6.4) [boundspsiu2PHtotal] with a rate uniform in `k_c`; both `P_H` series converge. -/
theorem Eq6_4 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      Summable (fun n : Idx => if inPH (rhoN N) (LN N) n then
          ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n] else 0) ∧
      Summable (fun n : Idx => if inPH (rhoN N) (LN N) n then
          ‖mom (LN N) n‖ ^ 2 * lam V w (rhoN N) (LN N) n ^ 2 else 0) ∧
      rhoN N ^ (-(5/2 : ℝ)) * (LN N ^ 3)⁻¹ *
          (∑' n : Idx, (if inPH (rhoN N) (LN N) n then ‖mom (LN N) n‖ ^ 2 *
            (Expect.Q (trialState V w kc N) [n]
              - (rho0 (g0 V w) (rhoN N) ^ 2
                + 4 * g0 V w ^ (3/2 : ℝ) / (3 * π ^ 2) * rho0 (g0 V w) (rhoN N) ^ (5/2 : ℝ))
                * lam V w (rhoN N) (LN N) n ^ 2) else 0))
        ≤ C * rhoN N ^ (1/400 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨N₁₁, h11⟩ := Eq6_11 V w
  obtain ⟨C₁₆, hC₁₆, N₁₆, h16⟩ := Eq6_16 hV hw
  obtain ⟨C₆, hC₆, N₆, h6⟩ := Lemma5_6 hg
  obtain ⟨CH, hCH, NH, hH⟩ := Kinetic_sum_PH_w2 hV hw
  obtain ⟨Kd, hKd, hdec⟩ := Kinetic_sum_decay
  set g := g0 V w with hgdef
  set G₃ : ℝ := g ^ (3/2 : ℝ) / (3 * π ^ 2) with hG₃def
  have hG₃ : 0 ≤ G₃ := by positivity
  set κ : ℝ := (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) with hκdef
  have hκ : 0 ≤ κ := by positivity
  set m := normGradW2 w with hmdef
  have hm : 0 ≤ m := integral_nonneg fun _ => by positivity
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((eventually_ge_atTop 1).and
    ((Lemma41_rpow_small (p := 1/2) (δ := 1 / (2 * (κ + 1))) (by norm_num)
      (by positivity)).and
     (Lemma41_rpow_small (p := 25/24) (δ := (2 * π)⁻¹) (by norm_num) (by positivity))))
  set K₁ : ℝ := C₆ + 12 * G₃ * κ + C₁₆ + 2 * (1 + C₆ + 4 * G₃ + C₁₆) with hK₁def
  have hK₁ : 0 ≤ K₁ := by positivity
  refine ⟨K₁ * (m + CH) + 3 * C₁₆ * Kd, by positivity,
    max (max (max N₁₁ N₁₆) (max N₆ NH)) N₂, fun N hN kc => ?_⟩
  have hNa : N ≥ max (max N₁₁ N₁₆) (max N₆ NH) := le_of_max_le_left hN
  have hN11 : N ≥ N₁₁ := le_trans (le_max_left _ _) (le_of_max_le_left hNa)
  have hN16 : N ≥ N₁₆ := le_trans (le_max_right _ _) (le_of_max_le_left hNa)
  have hN6 : N ≥ N₆ := le_trans (le_max_left _ _) (le_of_max_le_right hNa)
  have hNH : N ≥ NH := le_trans (le_max_right _ _) (le_of_max_le_right hNa)
  obtain ⟨hN1, hsm, hLs⟩ := hN₂ N (le_of_max_le_right hN)
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set Ψ := trialState V w kc N with hΨdef
  set ρ₀ := rho0 g ρ with hρ₀def
  -- powers of `ρ`
  set s : ℝ := ρ ^ (1/400 : ℝ) with hsdef
  set X : ℝ := ρ ^ (5/2 : ℝ) with hXdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hρ _
  have hs1 : s ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have hX0 : 0 < X := Real.rpow_pos_of_pos hρ _
  have hmono : ∀ a b : ℝ, b ≤ a → ρ ^ a ≤ ρ ^ b := fun a b h =>
    Real.rpow_le_rpow_of_exponent_ge hρ hρ1 h
  have hY : ρ ^ (5/2 + 1/400 : ℝ) = X * s := Real.rpow_add hρ _ _
  have h12 : ρ ^ (1/2 : ℝ) ≤ s := hmono _ _ (by norm_num)
  have h32 : ρ ^ (3/2 : ℝ) ≤ s := hmono _ _ (by norm_num)
  have h32' : ρ ^ (3/2 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have h200 : ρ ^ (1/200 : ℝ) ≤ s := hmono _ _ (by norm_num)
  have h200' : ρ ^ (1/200 : ℝ) ≤ 1 := Real.rpow_le_one hρ.le hρ1 (by norm_num)
  have h1225 : ρ ^ (12/25 : ℝ) ≤ s := hmono _ _ (by norm_num)
  have hρs : ρ ≤ s := by
    have := hmono 1 (1/400) (by norm_num)
    rwa [Real.rpow_one] at this
  have hρ2 : ρ ^ (3/2 : ℝ) * ρ ^ 2 = X * ρ := by
    rw [hXdef, show (5/2 : ℝ) = 3/2 + 1 by norm_num, Real.rpow_add_one hρ.ne']
    ring
  have hρ3 : ρ ^ 3 = X * ρ ^ (12/25 : ℝ) * epsP ρ ^ 4 := by
    unfold epsP
    rw [hXdef, ← Real.rpow_natCast (ρ ^ (1/200 : ℝ)), ← Real.rpow_mul hρ.le, ← Real.rpow_add hρ,
      ← Real.rpow_add hρ, ← Real.rpow_natCast]
    norm_num
  have hk : κ * ρ ^ (1/2 : ℝ) ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_left hsm hκ
    have h' : κ * (1 / (2 * (κ + 1))) ≤ 1/2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  obtain ⟨hρ₀0, hρ₀ρ, hρ₀50, -, hρ₀5⟩ := Lemma41_rho0 (g := g) hρ hg.le hk
  have hL2 : 2 * π ≤ L := by
    rw [hLdef, LN, Real.rpow_neg hρ.le]
    have h0 : 0 < ρ ^ (25/24 : ℝ) := Real.rpow_pos_of_pos hρ _
    rw [le_inv_comm₀ (by positivity) h0]
    exact hLs
  obtain ⟨hsd, hbd⟩ := hdec L hL2
  obtain ⟨hsw, hbw⟩ := hH N hNH
  set c₀ : ℝ := ρ₀ ^ 2 + 4 * g ^ (3/2 : ℝ) / (3 * π ^ 2) * ρ₀ ^ (5/2 : ℝ) with hc₀def
  have hc₀ : 0 ≤ c₀ := by positivity
  -- `λ_n² = w_n²` on `P_H`
  have hlw : ∀ n : Idx, inPH ρ L n → lam V w ρ L n ^ 2 = wmom V w (mom L n) ^ 2 := by
    intro n hn
    rw [scat_lam_of_not_PL ρ L n (fun h => Regions_PL_PH hρ h hn), neg_sq]
  have hfun : (fun n : Idx => if inPH ρ L n then ‖mom L n‖ ^ 2 * lam V w ρ L n ^ 2 else 0) =
      fun n : Idx => if inPH ρ L n then ‖mom L n‖ ^ 2 * wmom V w (mom L n) ^ 2 else 0 := by
    funext n
    split_ifs with hn
    · rw [hlw n hn]
    · rfl
  have hsl : Summable fun n : Idx =>
      if inPH ρ L n then ‖mom L n‖ ^ 2 * lam V w ρ L n ^ 2 else 0 := by
    rw [hfun]; exact hsw
  -- the bound for one `u ∈ P_H`
  have hpu : ∀ u : Idx, inPH ρ L u →
      Expect.Q Ψ [u] ≤ (c₀ + K₁ * (X * s)) * lam V w ρ L u ^ 2 +
        3 * (C₁₆ * (X * ρ ^ (12/25 : ℝ)) / ‖mom L u‖ ^ 2 * ((1 + ‖mom L u‖) ^ 4)⁻¹) := by
    intro u hu
    set lu := lam V w ρ L u with hludef
    set E : ℝ := C₁₆ * (X * ρ ^ (12/25 : ℝ)) / ‖mom L u‖ ^ 2 * ((1 + ‖mom L u‖) ^ 4)⁻¹
      with hEdef
    have hE : 0 ≤ E := by positivity
    have e11 := h11 N hN11 kc u hu
    have e27 := Eq5_27_sum V w kc hN1 hu
    have e16 := h16 N hN16 kc u hu
    have e6 := (abs_le.mp (h6 N hN6 kc)).2
    rw [hY] at e6
    have hε0 : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _
    have hEeq : C₁₆ * ρ ^ 3 / epsP ρ ^ 4 / ‖mom L u‖ ^ 2 * ((1 + ‖mom L u‖) ^ 4)⁻¹ = E := by
      rw [hEdef, hρ3]
      field_simp
    rw [hEeq] at e16
    set S := ∑' m : ℕ, Expect.Qm Ψ [(u, m + 1)] with hSdef
    set q := Expect.Q Ψ [0, 0] / (L ^ 3) ^ 2 with hqdef
    set A : ℝ := ρ₀ ^ 2 + C₆ * (X * s) + X * (4 * G₃ + C₁₆ * ρ ^ (1/200 : ℝ)) with hAdef
    have hl2 : 0 ≤ lu ^ 2 := sq_nonneg _
    have hSA : S ≤ lu ^ 2 * A + E := by
      have hq : q ≤ ρ₀ ^ 2 + C₆ * (X * s) := by linarith
      have h0 : lu ^ 2 / (L ^ 3) ^ 2 * Expect.Q Ψ [0, 0] = lu ^ 2 * q := by
        rw [hqdef]; ring
      have h1 : lu ^ 2 * q ≤ lu ^ 2 * (ρ₀ ^ 2 + C₆ * (X * s)) :=
        mul_le_mul_of_nonneg_left hq hl2
      have h2 : lu ^ 2 * X * (4 * g ^ (3/2 : ℝ) / (3 * π ^ 2) + C₁₆ * ρ ^ (1/200 : ℝ)) =
          lu ^ 2 * (X * (4 * G₃ + C₁₆ * ρ ^ (1/200 : ℝ))) := by rw [hG₃def]; ring
      have h3 : lu ^ 2 * A = lu ^ 2 * (ρ₀ ^ 2 + C₆ * (X * s)) +
          lu ^ 2 * (X * (4 * G₃ + C₁₆ * ρ ^ (1/200 : ℝ))) := by rw [hAdef]; ring
      linarith
    have hA1 : A ≤ c₀ + (C₆ + 12 * G₃ * κ + C₁₆) * (X * s) := by
      have f1 : X * ρ ^ (1/2 : ℝ) ≤ X * s := mul_le_mul_of_nonneg_left h12 hX0.le
      have f2 : X * ρ ^ (1/200 : ℝ) ≤ X * s := mul_le_mul_of_nonneg_left h200 hX0.le
      have f3 := mul_le_mul_of_nonneg_left f1 (by positivity : (0 : ℝ) ≤ 12 * G₃ * κ)
      have f4 := mul_le_mul_of_nonneg_left f2 hC₁₆
      have f5 := mul_le_mul_of_nonneg_left hρ₀5 (by positivity : (0 : ℝ) ≤ 4 * G₃)
      have hc : c₀ = ρ₀ ^ 2 + 4 * G₃ * ρ₀ ^ (5/2 : ℝ) := by rw [hc₀def, hG₃def]; ring
      rw [hAdef, hc]
      rw [← hXdef] at f5
      linarith
    have hA2 : 2 * ρ ^ (3/2 : ℝ) * A ≤ 2 * (1 + C₆ + 4 * G₃ + C₁₆) * (X * s) := by
      have r0 : 0 ≤ ρ ^ (3/2 : ℝ) := by positivity
      have g1 : ρ ^ (3/2 : ℝ) * ρ₀ ^ 2 ≤ X * s := by
        have := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ₀0 hρ₀ρ 2) r0
        rw [hρ2] at this
        exact this.trans (mul_le_mul_of_nonneg_left hρs hX0.le)
      have g2 : ρ ^ (3/2 : ℝ) * (C₆ * (X * s)) ≤ C₆ * (X * s) :=
        mul_le_of_le_one_left (by positivity) h32'
      have g3 : ρ ^ (3/2 : ℝ) * (X * (4 * G₃ + C₁₆ * ρ ^ (1/200 : ℝ))) ≤
          (X * s) * (4 * G₃ + C₁₆) := by
        have e1 : 4 * G₃ + C₁₆ * ρ ^ (1/200 : ℝ) ≤ 4 * G₃ + C₁₆ := by
          have := mul_le_of_le_one_right hC₁₆ h200'
          linarith
        have e2 : ρ ^ (3/2 : ℝ) * X ≤ X * s := by
          rw [mul_comm]; exact mul_le_mul_of_nonneg_left h32 hX0.le
        calc ρ ^ (3/2 : ℝ) * (X * (4 * G₃ + C₁₆ * ρ ^ (1/200 : ℝ)))
            = (ρ ^ (3/2 : ℝ) * X) * (4 * G₃ + C₁₆ * ρ ^ (1/200 : ℝ)) := by ring
          _ ≤ (X * s) * (4 * G₃ + C₁₆) := by
              apply mul_le_mul e2 e1 (by positivity) (by positivity)
      have h3 : 2 * ρ ^ (3/2 : ℝ) * A = 2 * (ρ ^ (3/2 : ℝ) * ρ₀ ^ 2) +
          2 * (ρ ^ (3/2 : ℝ) * (C₆ * (X * s))) +
          2 * (ρ ^ (3/2 : ℝ) * (X * (4 * G₃ + C₁₆ * ρ ^ (1/200 : ℝ)))) := by rw [hAdef]; ring
      have h4 : 0 ≤ X * s := by positivity
      linarith
    have hA : A + 2 * ρ ^ (3/2 : ℝ) * A ≤ c₀ + K₁ * (X * s) := by
      rw [hK₁def]; linarith
    have hS0 : 0 ≤ S := tsum_nonneg fun m => Lemma41_Qm_nonneg Ψ u (m + 1)
    have k1 : (1 + 2 * ρ ^ (3/2 : ℝ)) * S ≤ (1 + 2 * ρ ^ (3/2 : ℝ)) * (lu ^ 2 * A + E) :=
      mul_le_mul_of_nonneg_left hSA (by positivity)
    have k2 := mul_le_mul_of_nonneg_left hA hl2
    have k3 : (1 + 2 * ρ ^ (3/2 : ℝ)) * E ≤ 3 * E :=
      mul_le_mul_of_nonneg_right (by linarith) hE
    have k4 : (1 + 2 * ρ ^ (3/2 : ℝ)) * (lu ^ 2 * A + E) =
        lu ^ 2 * (A + 2 * ρ ^ (3/2 : ℝ) * A) + (1 + 2 * ρ ^ (3/2 : ℝ)) * E := by ring
    have k5 : lu ^ 2 * (c₀ + K₁ * (X * s)) = (c₀ + K₁ * (X * s)) * lu ^ 2 := by ring
    linarith
  set d : Idx → ℝ := fun n => ((1 + ‖mom L n‖) ^ 4)⁻¹ with hddef
  set B : Idx → ℝ := fun n => if inPH ρ L n then ‖mom L n‖ ^ 2 * lam V w ρ L n ^ 2 else 0
    with hBdef
  have hB0 : ∀ n, 0 ≤ B n := fun n => by
    simp only [hBdef]; split_ifs <;> positivity
  have hd0 : ∀ n, 0 ≤ d n := fun n => by simp only [hddef]; positivity
  set Z : ℝ := C₁₆ * (X * ρ ^ (12/25 : ℝ)) with hZdef
  have hZ0 : 0 ≤ Z := by positivity
  -- pointwise bound of `|n|² Q_Ψ(n)` on `P_H`
  have hptQ : ∀ n : Idx, (if inPH ρ L n then ‖mom L n‖ ^ 2 * Expect.Q Ψ [n] else 0) ≤
      (c₀ + K₁ * (X * s)) * B n + 3 * Z * d n := by
    intro n
    by_cases hn : inPH ρ L n
    · have hn0 : 0 < ‖mom L n‖ := (Real.rpow_pos_of_pos hρ _).trans hn
      have h := mul_le_mul_of_nonneg_left (hpu n hn) (sq_nonneg ‖mom L n‖)
      have e : ‖mom L n‖ ^ 2 * ((c₀ + K₁ * (X * s)) * lam V w ρ L n ^ 2 +
          3 * (C₁₆ * (X * ρ ^ (12/25 : ℝ)) / ‖mom L n‖ ^ 2 * ((1 + ‖mom L n‖) ^ 4)⁻¹)) =
          (c₀ + K₁ * (X * s)) * (‖mom L n‖ ^ 2 * lam V w ρ L n ^ 2) +
            3 * Z * ((1 + ‖mom L n‖) ^ 4)⁻¹ := by
        rw [hZdef]
        field_simp
      have hB : B n = ‖mom L n‖ ^ 2 * lam V w ρ L n ^ 2 := by simp only [hBdef]; simp [hn]
      have hdn : d n = ((1 + ‖mom L n‖) ^ 4)⁻¹ := rfl
      rw [hB, hdn]
      simp only [hn, ite_true]
      linarith
    · have hB : B n = 0 := by simp only [hBdef]; simp [hn]
      rw [hB]
      simp only [hn, ite_false]
      have := hd0 n
      positivity
  have hsQ : Summable fun n : Idx =>
      if inPH ρ L n then ‖mom L n‖ ^ 2 * Expect.Q Ψ [n] else 0 :=
    Summable.of_nonneg_of_le
      (fun n => by split_ifs <;> first | exact le_rfl | positivity [Lemma41_Q_nonneg Ψ n])
      hptQ ((hsl.mul_left _).add (hsd.mul_left _))
  refine ⟨hsQ, hsl, ?_⟩
  -- the sum
  have hF : ∀ n : Idx, (if inPH ρ L n then ‖mom L n‖ ^ 2 *
      (Expect.Q Ψ [n] - c₀ * lam V w ρ L n ^ 2) else 0) =
      (if inPH ρ L n then ‖mom L n‖ ^ 2 * Expect.Q Ψ [n] else 0) - c₀ * B n := by
    intro n
    by_cases hn : inPH ρ L n
    · have hB : B n = ‖mom L n‖ ^ 2 * lam V w ρ L n ^ 2 := by simp only [hBdef]; simp [hn]
      rw [hB]; simp only [hn, ite_true]; ring
    · have hB : B n = 0 := by simp only [hBdef]; simp [hn]
      rw [hB]; simp [hn]
  have hptF : ∀ n : Idx, (if inPH ρ L n then ‖mom L n‖ ^ 2 *
      (Expect.Q Ψ [n] - c₀ * lam V w ρ L n ^ 2) else 0) ≤
      K₁ * (X * s) * B n + 3 * Z * d n := by
    intro n
    have h1 := hptQ n
    have h2 := hF n
    have h3 : (c₀ + K₁ * (X * s)) * B n = c₀ * B n + K₁ * (X * s) * B n := by ring
    linarith
  have hsF : Summable fun n : Idx => if inPH ρ L n then ‖mom L n‖ ^ 2 *
      (Expect.Q Ψ [n] - c₀ * lam V w ρ L n ^ 2) else 0 := by
    have := hsQ.sub (hsl.mul_left c₀)
    refine this.congr fun n => ?_
    rw [hF n]
  have hsB : Summable B := hsl
  have hT := hsF.tsum_le_tsum hptF ((hsB.mul_left _).add (hsd.mul_left _))
  rw [(hsB.mul_left _).tsum_add (hsd.mul_left _), tsum_mul_left, tsum_mul_left] at hT
  have hBw : (∑' n : Idx, B n) = ∑' n : Idx,
      (if inPH ρ L n then ‖mom L n‖ ^ 2 * wmom V w (mom L n) ^ 2 else 0) :=
    congrArg tsum hfun
  have hbw' : (L ^ 3)⁻¹ * (∑' n : Idx, B n) ≤ m + CH := by
    rw [hBw]
    have := (abs_le.mp hbw).2
    have : CH * ρ ^ (1/200 : ℝ) ≤ CH := mul_le_of_le_one_right hCH h200'
    linarith
  have hBs0 : 0 ≤ (∑' n : Idx, B n) := tsum_nonneg hB0
  have hDs0 : 0 ≤ ∑' n : Idx, d n := tsum_nonneg hd0
  have hl0 : 0 < (L ^ 3)⁻¹ := by positivity
  have hneg : ρ ^ (-(5/2 : ℝ)) = X⁻¹ := Real.rpow_neg hρ.le _
  rw [hneg]
  have hbd' : (L ^ 3)⁻¹ * ∑' n : Idx, d n ≤ Kd := hbd
  have hX1 : 0 < X⁻¹ := by positivity
  have hT' := mul_le_mul_of_nonneg_left hT (by positivity : (0 : ℝ) ≤ X⁻¹ * (L ^ 3)⁻¹)
  have hid : X⁻¹ * (L ^ 3)⁻¹ * (K₁ * (X * s) * (∑' n : Idx, B n) + 3 * Z * ∑' n : Idx, d n) =
      K₁ * s * ((L ^ 3)⁻¹ * (∑' n : Idx, B n))
        + 3 * C₁₆ * ρ ^ (12/25 : ℝ) * ((L ^ 3)⁻¹ * ∑' n : Idx, d n) := by
    rw [hZdef]
    field_simp
  have j1 : K₁ * s * ((L ^ 3)⁻¹ * (∑' n : Idx, B n)) ≤ K₁ * s * (m + CH) :=
    mul_le_mul_of_nonneg_left hbw' (by positivity)
  have j2 : 3 * C₁₆ * ρ ^ (12/25 : ℝ) * ((L ^ 3)⁻¹ * ∑' n : Idx, d n) ≤ 3 * C₁₆ * s * Kd := by
    have : 0 ≤ (L ^ 3)⁻¹ * ∑' n : Idx, d n := by positivity
    calc 3 * C₁₆ * ρ ^ (12/25 : ℝ) * ((L ^ 3)⁻¹ * ∑' n : Idx, d n)
        ≤ 3 * C₁₆ * s * ((L ^ 3)⁻¹ * ∑' n : Idx, d n) := by gcongr
      _ ≤ 3 * C₁₆ * s * Kd := by gcongr
  have j3 : K₁ * s * (m + CH) + 3 * C₁₆ * s * Kd = (K₁ * (m + CH) + 3 * C₁₆ * Kd) * s := by ring
  linarith

/-! ### Lemma 4.1 [lemkinetic] -/

/-- Lemma 4.1 [lemkinetic], (4.8) [proofthem1-1], with a rate uniform in `k_c`: the kinetic
series of `Ψ` converges to `E = Σ_u |u|² Q_Ψ(u)`, and
`(|Λ|⁻¹E − ρ₀²‖∇w‖₂²)ρ^{-5/2} ≤ 4‖∇w‖₂²g₀^{3/2}/(3π²) − 8g₀^{5/2}/(5π²) + Cρ^{η/2}`. -/
theorem Kinetic_rate {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      HasSum (kinTerm (LN N) (trialState V w kc N))
        (∑' n : Idx, ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n]) ∧
      Section4.excess (g0 V w) (normGradW2 w)
          (∑' n : Idx, ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n]) N ≤
        4 * normGradW2 w * Section4.G V w / 3 - 8 * g0 V w ^ (5/2 : ℝ) / (5 * π ^ 2)
          + C * rhoN N ^ (1/400 : ℝ) := by
  have hg := scat_g0_pos hV hw
  obtain ⟨C₂, hC₂, N₂, h2⟩ := Eq6_2_paper hV hw
  obtain ⟨C₃, hC₃, N₃, h3⟩ := Eq6_3_paper hV hw
  obtain ⟨C₄, hC₄, N₄, h4⟩ := Eq6_4 hV hw
  obtain ⟨Cw, hCw, Nw, hW⟩ := Kinetic_sum_w2 hV hw
  obtain ⟨Ch, hCh, Nh, hWH⟩ := Kinetic_sum_PH_w2 hV hw
  set g := g0 V w with hgdef
  set G₃ : ℝ := g ^ (3/2 : ℝ) / (3 * π ^ 2) with hG₃def
  have hG₃ : 0 ≤ G₃ := by positivity
  set κ : ℝ := (3 * π ^ 2)⁻¹ * g ^ (3/2 : ℝ) with hκdef
  have hκ : 0 ≤ κ := by positivity
  set m := normGradW2 w with hmdef
  have hm : 0 ≤ m := integral_nonneg fun _ => by positivity
  obtain ⟨N₅, hN₅⟩ := eventually_atTop.1 ((eventually_ge_atTop 1).and
    (Lemma41_rpow_small (p := 1/2) (δ := 1 / (2 * (κ + 1))) (by norm_num) (by positivity)))
  refine ⟨C₃ + C₂ + Cw + 4 * G₃ * Ch + C₄, by positivity,
    max (max (max N₂ N₃) (max N₄ Nw)) (max Nh N₅), fun N hN kc => ?_⟩
  have hNa : N ≥ max (max N₂ N₃) (max N₄ Nw) := le_of_max_le_left hN
  have hNb : N ≥ max Nh N₅ := le_of_max_le_right hN
  obtain ⟨hN1, hsm⟩ := hN₅ N (le_of_max_le_right hNb)
  have e2 := h2 N (le_trans (le_max_left _ _) (le_of_max_le_left hNa)) kc
  have e3 := h3 N (le_trans (le_max_right _ _) (le_of_max_le_left hNa)) kc
  obtain ⟨hsQH, hslH, e4⟩ := h4 N (le_trans (le_max_left _ _) (le_of_max_le_right hNa)) kc
  obtain ⟨hsWA, eW⟩ := hW N (le_trans (le_max_right _ _) (le_of_max_le_right hNa))
  obtain ⟨hsWH, eWH⟩ := hWH N (le_of_max_le_left hNb)
  have hsplit := Kinetic_split V w kc hN1
  have hQs := (Particles_hasSum_Q V w kc hN1).summable
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1
  set ρ := rhoN N with hρdef
  set L := LN N with hLdef
  set Ψ := trialState V w kc N with hΨdef
  set ρ₀ := rho0 g ρ with hρ₀def
  set ε := epsP ρ with hεdef
  have hk : κ * ρ ^ (1/2 : ℝ) ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_left hsm hκ
    have h' : κ * (1 / (2 * (κ + 1))) ≤ 1/2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith
    linarith
  obtain ⟨hρ₀0, hρ₀ρ, hρ₀50, hρ₀5, -⟩ := Lemma41_rho0 (g := g) hρ hg.le hk
  set c₀ : ℝ := ρ₀ ^ 2 + 4 * g ^ (3/2 : ℝ) / (3 * π ^ 2) * ρ₀ ^ (5/2 : ℝ) with hc₀def
  -- the five pieces
  set FL : Idx → ℝ := fun n => if inPL ρ L n then ‖mom L n‖ ^ 2 *
    (Expect.Q Ψ [n] - (ρ₀ * wmom V w (mom L n)) ^ 2) else 0 with hFLdef
  set FI : Idx → ℝ := fun n => if inPI ρ L n then ‖mom L n‖ ^ 2 *
    (Expect.Q Ψ [n] - (ρ₀ * lam V w ρ L n) ^ 2) else 0 with hFIdef
  set FH : Idx → ℝ := fun n => if inPH ρ L n then ‖mom L n‖ ^ 2 *
    (Expect.Q Ψ [n] - c₀ * lam V w ρ L n ^ 2) else 0 with hFHdef
  set WA : Idx → ℝ := fun n => if inPL ρ L n ∨ inPI ρ L n ∨ inPH ρ L n then
    ‖mom L n‖ ^ 2 * wmom V w (mom L n) ^ 2 else 0 with hWAdef
  set WH : Idx → ℝ := fun n => if inPH ρ L n then
    ‖mom L n‖ ^ 2 * wmom V w (mom L n) ^ 2 else 0 with hWHdef
  have hid : ∀ n : Idx, ‖mom L n‖ ^ 2 * Expect.Q Ψ [n] =
      FL n + FI n + FH n + ρ₀ ^ 2 * WA n + 4 * G₃ * ρ₀ ^ (5/2 : ℝ) * WH n := by
    intro n
    have hs := congrFun hsplit n
    simp only [hFLdef, hFIdef, hFHdef, hWAdef, hWHdef]
    by_cases hPL : inPL ρ L n
    · have h1 : ¬ inPI ρ L n := Regions_PL_PI hPL
      have h2 : ¬ inPH ρ L n := Regions_PL_PH hρ hPL
      simp only [hPL, h1, h2, ite_true, ite_false, true_or]
      ring
    · have hlw : lam V w ρ L n = -wmom V w (mom L n) := scat_lam_of_not_PL ρ L n hPL
      by_cases hPI : inPI ρ L n
      · have h2 : ¬ inPH ρ L n := Regions_PI_PH hPI
        simp only [hPL, hPI, h2, ite_true, ite_false, true_or, or_true]
        rw [hlw]
        ring
      · by_cases hPH : inPH ρ L n
        · simp only [hPL, hPI, hPH, ite_true, ite_false, or_true]
          rw [hlw, hc₀def, hG₃def]
          ring
        · simp only [hPL, hPI, hPH, ite_false, or_false] at hs ⊢
          rw [hs]
          ring
  -- summability of the pieces
  have hε0 : 0 < ε := Real.rpow_pos_of_pos hρ _
  have hsFL : Summable FL := Lemma41_summable_ball (R := ε⁻¹ * ρ ^ (1/2 : ℝ)) hL FL
    (fun n hn => by
      by_contra h
      apply hn
      simp only [hFLdef]
      exact ite_eq_right_iff.mpr (fun h' => absurd h'.2 h))
  have hsFI : Summable FI := Lemma41_summable_ball (R := ε) hL FI
    (fun n hn => by
      by_contra h
      apply hn
      simp only [hFIdef]
      exact ite_eq_right_iff.mpr (fun h' => absurd h'.2 h))
  have hFH : FH = fun n => (if inPH ρ L n then ‖mom L n‖ ^ 2 * Expect.Q Ψ [n] else 0) -
      c₀ * (if inPH ρ L n then ‖mom L n‖ ^ 2 * lam V w ρ L n ^ 2 else 0) := by
    funext n
    simp only [hFHdef]
    split_ifs <;> ring
  have hsFH : Summable FH := by rw [hFH]; exact hsQH.sub (hslH.mul_left c₀)
  have hsum : HasSum (fun n : Idx => ‖mom L n‖ ^ 2 * Expect.Q Ψ [n])
      ((∑' n, FL n) + (∑' n, FI n) + (∑' n, FH n) + ρ₀ ^ 2 * (∑' n, WA n) +
        4 * G₃ * ρ₀ ^ (5/2 : ℝ) * (∑' n, WH n)) := by
    have := ((((hsFL.hasSum.add hsFI.hasSum).add hsFH.hasSum).add
      (hsWA.hasSum.mul_left (ρ₀ ^ 2))).add (hsWH.hasSum.mul_left (4 * G₃ * ρ₀ ^ (5/2 : ℝ))))
    refine this.congr_fun fun n => ?_
    rw [hid n]
  have hE := hsum.tsum_eq
  refine ⟨(Kinetic_hasSum_iff V w kc hN1 _).2 hsum.summable.hasSum, ?_⟩
  rw [hE]
  -- the bounds
  set s : ℝ := ρ ^ (1/400 : ℝ) with hsdef
  set t : ℝ := ρ ^ (1/200 : ℝ) with htdef
  set X : ℝ := ρ ^ (5/2 : ℝ) with hXdef
  have hX0 : 0 < X := Real.rpow_pos_of_pos hρ _
  have hts : t ≤ s := Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  have hneg : ρ ^ (-(5/2 : ℝ)) = X⁻¹ := Real.rpow_neg hρ.le _
  rw [hneg] at e2 e3 e4
  set ℓ : ℝ := (L ^ 3)⁻¹ with hℓdef
  have hℓ0 : 0 < ℓ := by positivity
  have hTA := (abs_le.mp eW).2
  have hTH := abs_le.mp eWH
  have hTH0 : 0 ≤ (∑' n, WH n) := tsum_nonneg fun n => by
    simp only [hWHdef]; split_ifs <;> positivity
  have hb4 : ρ₀ ^ 2 * (ℓ * (∑' n, WA n) - m) * X⁻¹ ≤ Cw * t := by
    have hr : ρ ^ 2 * ρ ^ (1/2 + 1/200 : ℝ) = X * t := by
      rw [hXdef, htdef, ← Real.rpow_natCast, ← Real.rpow_add hρ, ← Real.rpow_add hρ]
      norm_num
    have k1 : ρ₀ ^ 2 * (ℓ * (∑' n, WA n) - m) ≤ ρ ^ 2 * (Cw * ρ ^ (1/2 + 1/200 : ℝ)) := by
      have k0 : ρ₀ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hρ₀0 hρ₀ρ 2
      have k2 : 0 ≤ Cw * ρ ^ (1/2 + 1/200 : ℝ) := by positivity
      calc ρ₀ ^ 2 * (ℓ * (∑' n, WA n) - m) ≤ ρ₀ ^ 2 * (Cw * ρ ^ (1/2 + 1/200 : ℝ)) :=
            mul_le_mul_of_nonneg_left hTA (by positivity)
        _ ≤ ρ ^ 2 * (Cw * ρ ^ (1/2 + 1/200 : ℝ)) := mul_le_mul_of_nonneg_right k0 k2
    have k3 : ρ ^ 2 * (Cw * ρ ^ (1/2 + 1/200 : ℝ)) * X⁻¹ = Cw * t := by
      rw [show ρ ^ 2 * (Cw * ρ ^ (1/2 + 1/200 : ℝ)) = Cw * (ρ ^ 2 * ρ ^ (1/2 + 1/200 : ℝ)) by
        ring, hr]
      field_simp
    calc ρ₀ ^ 2 * (ℓ * (∑' n, WA n) - m) * X⁻¹ ≤ ρ ^ 2 * (Cw * ρ ^ (1/2 + 1/200 : ℝ)) * X⁻¹ :=
          mul_le_mul_of_nonneg_right k1 (by positivity)
      _ = Cw * t := k3
  have hb5 : 4 * G₃ * (ρ₀ ^ (5/2 : ℝ) * X⁻¹) * (ℓ * (∑' n, WH n)) ≤ 4 * G₃ * (m + Ch * t) := by
    have r0 : 0 ≤ ρ₀ ^ (5/2 : ℝ) * X⁻¹ := by positivity
    have r1 : ρ₀ ^ (5/2 : ℝ) * X⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hX0]; exact hρ₀5
    have y0 : 0 ≤ ℓ * (∑' n, WH n) := by positivity
    have : (ρ₀ ^ (5/2 : ℝ) * X⁻¹) * (ℓ * (∑' n, WH n)) ≤ m + Ch * t := by
      calc (ρ₀ ^ (5/2 : ℝ) * X⁻¹) * (ℓ * (∑' n, WH n)) ≤ ℓ * (∑' n, WH n) :=
            mul_le_of_le_one_left y0 r1
        _ ≤ m + Ch * t := by linarith [hTH.2]
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 4 * G₃)
    linarith
  have hexp : Section4.excess g m ((∑' n, FL n) + (∑' n, FI n) + (∑' n, FH n) +
      ρ₀ ^ 2 * (∑' n, WA n) + 4 * G₃ * ρ₀ ^ (5/2 : ℝ) * (∑' n, WH n)) N =
      X⁻¹ * ℓ * (∑' n, FL n) + X⁻¹ * ℓ * (∑' n, FI n) + X⁻¹ * ℓ * (∑' n, FH n) +
        ρ₀ ^ 2 * (ℓ * (∑' n, WA n) - m) * X⁻¹ +
        4 * G₃ * (ρ₀ ^ (5/2 : ℝ) * X⁻¹) * (ℓ * (∑' n, WH n)) := by
    unfold Section4.excess
    rw [← hρdef, ← hLdef, ← hρ₀def, ← hXdef, div_eq_mul_inv, div_eq_mul_inv, ← hℓdef]
    ring
  rw [hexp]
  have hGG : 4 * G₃ * m = 4 * m * Section4.G V w / 3 := by
    unfold Section4.G; rw [hG₃def, ← hgdef]; ring
  have j1 : C₃ * t ≤ C₃ * s := mul_le_mul_of_nonneg_left hts hC₃
  have j2 : C₂ * t ≤ C₂ * s := mul_le_mul_of_nonneg_left hts hC₂
  have j3 : Cw * t ≤ Cw * s := mul_le_mul_of_nonneg_left hts hCw
  have j4 : 4 * G₃ * Ch * t ≤ 4 * G₃ * Ch * s := mul_le_mul_of_nonneg_left hts (by positivity)
  have j5 : 4 * G₃ * (m + Ch * t) = 4 * G₃ * m + 4 * G₃ * Ch * t := by ring
  have j6 : (C₃ + C₂ + Cw + 4 * G₃ * Ch + C₄) * s =
      C₃ * s + C₂ * s + Cw * s + 4 * G₃ * Ch * s + C₄ * s := by ring
  linarith

/-- The last step of Lemma 4.1 [lemkinetic]: a rate bound uniform in `k_c` gives `KinBound`. -/
private theorem Lemma41_kinBound_of_rate {V w : R3 → ℝ} {R : ℝ}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      HasSum (kinTerm (LN N) (trialState V w kc N))
        (∑' n : Idx, ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n]) ∧
      Section4.excess (g0 V w) (normGradW2 w)
          (∑' n : Idx, ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n]) N ≤
        R + C * rhoN N ^ (1/400 : ℝ)) :
    Section4.KinBound V w (normGradW2 w) R := by
  obtain ⟨C, -, N₀, hN⟩ := h
  refine ⟨fun kc N => ∑' n : Idx, ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n],
    fun kc => ?_, ?_⟩
  · filter_upwards [eventually_ge_atTop N₀] with N hN' using (hN N hN' kc).1
  · have h1 : Tendsto (fun N : ℕ => rhoN N ^ (1/400 : ℝ)) atTop (𝓝 0) := by
      have := Lemma41_rho_tendsto.rpow_const (p := 1/400) (Or.inr (by norm_num))
      simpa [Real.zero_rpow (by norm_num : (1/400 : ℝ) ≠ 0)] using this
    have h2 : Tendsto (fun N : ℕ => R + C * rhoN N ^ (1/400 : ℝ)) atTop (𝓝 R) := by
      simpa using (h1.const_mul C).const_add R
    have h3 : Tendsto (fun N : ℕ => ((R + C * rhoN N ^ (1/400 : ℝ) : ℝ) : EReal)) atTop
        (𝓝 (R : EReal)) := (continuous_coe_real_ereal.tendsto _).comp h2
    unfold Section4.limsup2
    refine limsup_le_of_le (h := Eventually.of_forall fun kc => ?_)
    calc limsup (fun N : ℕ => ((Section4.excess (g0 V w) (normGradW2 w)
            (∑' n : Idx, ‖mom (LN N) n‖ ^ 2 * Expect.Q (trialState V w kc N) [n]) N : ℝ) :
              EReal)) atTop
        ≤ limsup (fun N : ℕ => ((R + C * rhoN N ^ (1/400 : ℝ) : ℝ) : EReal)) atTop := by
          refine limsup_le_limsup ?_
          filter_upwards [eventually_ge_atTop N₀] with N hN'
          exact_mod_cast (hN N hN' kc).2
      _ = (R : EReal) := h3.limsup_eq

/-- Lemma 4.1 [lemkinetic], (4.8) [proofthem1-1]. -/
theorem lemma4_1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma4_1 V w := by
  exact Lemma41_kinBound_of_rate (Kinetic_rate hV hw)

end LHYUpper
