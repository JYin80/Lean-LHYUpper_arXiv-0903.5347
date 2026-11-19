import LHYUpper.Thermo.Scales
import LHYUpper.Scattering.Solution
import LHYUpper.Thermo.Bridge
import LHYUpper.Thermo.Product
import LHYUpper.Thermo.InterBox
import LHYUpper.Position.Lemma21

/-! # The duplication step after Lemma 2.1 [thm1] (§2.1)

Copies of the small-box Dirichlet trial states of Lemma 2.1 [thm1], with `N₀` or `N₀ + 1`
particles, are placed in the cells of a tiling of the torus `[0,L]³` with corridors `d` between
the cubes; their symmetrized product bounds `e₀^P` of (2.1) [ham], and the three limits of (2.2)
give Theorem 2.1 [mainthm]. -/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- For `k ∈ {N₀, N₀ + 1}` one of two given Dirichlet trial states on `[0,ℓ]³` is a trial state
of `k` particles with energy at most `k e`. -/
private lemma Duplication_pick {V : R3 → ℝ} {ℓ e : ℝ} {N₀ : ℕ} {ψ₀ : Conf N₀ → ℂ}
    {ψ₁ : Conf (N₀ + 1) → ℂ} (h₀ : IsDirichletTrial ℓ N₀ ψ₀)
    (h₁ : IsDirichletTrial ℓ (N₀ + 1) ψ₁) (he₀ : energyD V ψ₀ ≤ N₀ * e)
    (he₁ : energyD V ψ₁ ≤ ((N₀ : ℝ) + 1) * e) (k : ℕ) (hk : k = N₀ ∨ k = N₀ + 1) :
    ∃ φ : Conf k → ℂ, IsDirichletTrial ℓ k φ ∧ energyD V φ ≤ k * e := by
  rcases hk with rfl | rfl
  · exact ⟨ψ₀, h₀, he₀⟩
  · exact ⟨ψ₁, h₁, by push_cast; exact he₁⟩

/-- The corner `sL m + d (1, 1, 1)` of the cube in the cell `m` of a `K × K × K` tiling. -/
private def Duplication_corner {K : ℕ} (sL d : ℝ) (m : Fin 3 → Fin K) : R3 :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm fun a => sL * ((m a : ℕ) : ℝ) + d

private lemma Duplication_corner_apply {K : ℕ} (sL d : ℝ) (m : Fin 3 → Fin K) (a : Fin 3) :
    Duplication_corner sL d m a = sL * ((m a : ℕ) : ℝ) + d := by
  simp [Duplication_corner]

/-- The ratio `(e - gρ)/(g^{5/2}ρ^{3/2})` of Theorem 2.1 [mainthm] is monotone in `e`. -/
private lemma Duplication_ratio_mono {g ρ : ℝ} (hg : 0 ≤ g) (hρ : 0 ≤ ρ) {a b : EReal}
    (hab : a ≤ b) : ratio g ρ a ≤ ratio g ρ b := by
  unfold ratio
  exact mul_le_mul_of_nonneg_right (EReal.sub_le_sub hab le_rfl)
    (EReal.coe_nonneg.2 (by positivity))

/-- The energy bound `g r + k g^{5/2} r^{3/2}` per particle of Lemma 2.1 [thm1] is monotone in the
density `r ≥ 0`. -/
private lemma Duplication_mono {g k r R : ℝ} (hg : 0 ≤ g) (hk : 0 ≤ k) (hr : 0 ≤ r)
    (hrR : r ≤ R) :
    g * r + k * g ^ (5/2 : ℝ) * r ^ (3/2 : ℝ) ≤ g * R + k * g ^ (5/2 : ℝ) * R ^ (3/2 : ℝ) := by
  have h1 : g * r ≤ g * R := mul_le_mul_of_nonneg_left hrR hg
  have h2 : r ^ (3/2 : ℝ) ≤ R ^ (3/2 : ℝ) := Real.rpow_le_rpow hr hrR (by norm_num)
  have h3 : 0 ≤ k * g ^ (5/2 : ℝ) := mul_nonneg hk (Real.rpow_nonneg hg _)
  have h4 := mul_le_mul_of_nonneg_left h2 h3
  linarith

private lemma Duplication_rhotN_nonneg (N : ℕ) : 0 ≤ rhotN N := by
  unfold rhotN LtN LN rhoN
  positivity

/-- The normalized duplication bound at density `ρ` with corridor `d = ρ^{-1/2}` and
`N₀ + 1 ≤ ρ^{-17/8}`: with `t = ρ^{1/24}`, the ratio of
`g ρ(1 + η) + k g^{5/2} (ρ(1 + η))^{3/2} + 27 C (N₀ + 1)/(2d)⁸`, `η = 33ρ^{13/24}`, is at most
`33 t / g^{3/2} + k (1 + 33 t¹³)^{3/2} + (27/256) C t⁹ / g^{5/2}`. -/
private lemma Duplication_alg {g C k ρ : ℝ} {N₀ : ℕ} (hg : 0 < g) (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hN : (N₀ : ℝ) + 1 ≤ ρ ^ (-(17 / 8 : ℝ))) :
    (g * (ρ * (1 + 33 * ρ ^ (13/24 : ℝ))) +
        k * g ^ (5/2 : ℝ) * (ρ * (1 + 33 * ρ ^ (13/24 : ℝ))) ^ (3/2 : ℝ) +
        27 * C * ((N₀ : ℝ) + 1) / (2 * ρ ^ (-(1/2 : ℝ))) ^ 8 - g * ρ) *
        (g ^ (5/2 : ℝ) * ρ ^ (3/2 : ℝ))⁻¹ ≤
      33 * ρ ^ (1/24 : ℝ) / g ^ (3/2 : ℝ) + k * (1 + 33 * (ρ ^ (1/24 : ℝ)) ^ 13) ^ (3/2 : ℝ) +
        27 / 256 * C / g ^ (5/2 : ℝ) * (ρ ^ (1/24 : ℝ)) ^ 9 := by
  have hpow : ∀ q : ℝ, ∀ n : ℕ, q = 1/24 * n → ρ ^ q = (ρ ^ (1/24 : ℝ)) ^ n := by
    intro q n hq
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ.le, hq]
  have h13 : ρ ^ (13/24 : ℝ) = (ρ ^ (1/24 : ℝ)) ^ 13 := hpow _ _ (by norm_num)
  have h32 : ρ ^ (3/2 : ℝ) = (ρ ^ (1/24 : ℝ)) ^ 36 := hpow _ _ (by norm_num)
  have h17 : ρ ^ (-(17/8 : ℝ)) = ((ρ ^ (1/24 : ℝ)) ^ 51)⁻¹ := by
    rw [Real.rpow_neg hρ.le, hpow _ 51 (by norm_num)]
  have h12 : ρ ^ (-(1/2 : ℝ)) = ((ρ ^ (1/24 : ℝ)) ^ 12)⁻¹ := by
    rw [Real.rpow_neg hρ.le, hpow _ 12 (by norm_num)]
  have h1 : ρ = (ρ ^ (1/24 : ℝ)) ^ 24 := by rw [← hpow 1 24 (by norm_num), Real.rpow_one]
  have hmul : (ρ * (1 + 33 * ρ ^ (13/24 : ℝ))) ^ (3/2 : ℝ) =
      ρ ^ (3/2 : ℝ) * (1 + 33 * (ρ ^ (1/24 : ℝ)) ^ 13) ^ (3/2 : ℝ) := by
    rw [Real.mul_rpow hρ.le (by positivity), h13]
  have h52 : g ^ (5/2 : ℝ) = g * g ^ (3/2 : ℝ) := by
    rw [show (5/2 : ℝ) = 1 + 3/2 by norm_num, Real.rpow_add hg, Real.rpow_one]
  have ht0 : 0 < ρ ^ (1/24 : ℝ) := Real.rpow_pos_of_pos hρ _
  rw [hmul, h13, h12, h32, h52]
  rw [h17] at hN
  generalize ρ ^ (1/24 : ℝ) = t at hN h1 ht0 ⊢
  subst h1
  generalize (1 + 33 * t ^ 13) ^ (3/2 : ℝ) = X
  have ha : 0 < g ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hg _
  generalize g ^ (3/2 : ℝ) = a at ha ⊢
  have hkey : ((N₀ : ℝ) + 1) * t ^ 60 ≤ t ^ 9 := by
    calc ((N₀ : ℝ) + 1) * t ^ 60 ≤ (t ^ 51)⁻¹ * t ^ 60 :=
          mul_le_mul_of_nonneg_right hN (by positivity)
      _ = t ^ 9 := by field_simp
  have heq : (g * (t ^ 24 * (1 + 33 * t ^ 13)) + k * (g * a) * (t ^ 36 * X) +
        27 * C * ((N₀ : ℝ) + 1) / (2 * (t ^ 12)⁻¹) ^ 8 - g * t ^ 24) * (g * a * t ^ 36)⁻¹ =
      33 * t / a + k * X + 27 / 256 * C / (g * a) * (((N₀ : ℝ) + 1) * t ^ 60) := by
    field_simp
    ring
  rw [heq]
  have hc : 0 ≤ 27 / 256 * C / (g * a) := by positivity
  have := mul_le_mul_of_nonneg_left hkey hc
  linarith

/-- Duplication at a fixed density `ρ`: Dirichlet trial states of `N₀` and `N₀ + 1` particles on
`[0,L̃_{N₀}]³`, `[0,L̃_{N₀+1}]³` with energy per particle at most `e`, and a corridor `d` with
`L̃_{N₀+1} + 2d ≤ ((N₀ + 1/2)/ρ)^{1/3}`, give eventually along `L → ∞, N/L³ → ρ` the bound
`e₀^P ≤ e + 27 decayConst8 V (N₀ + 1)/(2d)⁸` for (2.1) [ham]. -/
theorem thermo_e0P_le_dup {V : R3 → ℝ} (hV : PotentialHyp V) {ρ d e : ℝ} {N₀ : ℕ}
    (hρ : 0 < ρ) (hd : 0 < d)
    (hfit : LtN (N₀ + 1) + 2 * d ≤ (((N₀ : ℝ) + 1/2) / ρ) ^ (1/3 : ℝ))
    {ψ₀ : Conf N₀ → ℂ} {ψ₁ : Conf (N₀ + 1) → ℂ} (h₀ : IsDirichletTrial (LtN N₀) N₀ ψ₀)
    (h₁ : IsDirichletTrial (LtN (N₀ + 1)) (N₀ + 1) ψ₁) (he₀ : energyD V ψ₀ ≤ N₀ * e)
    (he₁ : energyD V ψ₁ ≤ ((N₀ : ℝ) + 1) * e) :
    ∀ᶠ x in thermo ρ,
      e0P x.2 V x.1 ≤ ((e + 27 * decayConst8 V * ((N₀ : ℝ) + 1) / (2 * d) ^ 8 : ℝ) : EReal) := by
  have hq : 0 < ((N₀ : ℝ) + 1/2) / ρ := by positivity
  set s : ℝ := (((N₀ : ℝ) + 1/2) / ρ) ^ (1/3 : ℝ) with hsdef
  have hs : 0 < s := Real.rpow_pos_of_pos hq _
  have hs3 : ρ * s ^ 3 = (N₀ : ℝ) + 1/2 := by
    rw [hsdef, show (1/3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num,
      Real.rpow_inv_natCast_pow hq.le (by norm_num)]
    field_simp
  have hVc : Continuous V := by
    obtain ⟨S, hS⟩ := hV.schwartz
    rw [← hS]
    exact S.continuous
  have hℓ : LtN N₀ ≤ LtN (N₀ + 1) := LtN_monotone (Nat.le_succ N₀)
  filter_upwards [thermo_eventually_counts hρ hs hs3] with p hp
  obtain ⟨hL, hN1, hK1, hlo, hhi⟩ := hp
  set L := p.2 with hLdef
  set N := p.1 with hNdef
  set K := ⌊L / s⌋₊ with hKdef
  set ℓ := LtN (N₀ + 1) with hℓdef
  have hcard : Fintype.card (Fin 3 → Fin K) = K ^ 3 := by simp
  obtain ⟨n, hn, hsum⟩ := thermo_counts (ι := Fin 3 → Fin K) (N₀ := N₀) (N := N)
    (by rw [hcard]; exact hlo) (by rw [hcard]; exact hhi.le)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
  set sL := L / K with hsLdef
  have hsL0 : 0 ≤ sL := div_nonneg hL.le hKpos.le
  have hKs : (K : ℝ) ≤ L / s := Nat.floor_le (div_pos hL hs).le
  have hssL : s ≤ sL := by
    rw [hsLdef, le_div_iff₀ hKpos]
    rw [le_div_iff₀ hs] at hKs
    linarith
  have hfit' : ℓ + 2 * d ≤ sL := hfit.trans hssL
  have hKsL : (K : ℝ) * sL = L := by
    rw [hsLdef]
    field_simp
  choose ψ hψ hψe using fun m : Fin 3 → Fin K =>
    Duplication_pick (V := V) (isDirichletTrial_mono hℓ h₀) h₁ he₀ he₁ (n m) (hn m)
  have hbox : ∀ (m : Fin 3 → Fin K) (a : Fin 3),
      0 ≤ Duplication_corner sL d m a ∧ Duplication_corner sL d m a + ℓ ≤ L := by
    intro m a
    rw [Duplication_corner_apply]
    have hm : ((m a : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast (m a).isLt
    have hm0 : (0 : ℝ) ≤ ((m a : ℕ) : ℝ) := Nat.cast_nonneg _
    refine ⟨add_nonneg (mul_nonneg hsL0 hm0) hd.le, ?_⟩
    have := mul_le_mul_of_nonneg_left hm hsL0
    linarith
  have hsep : ∀ m m' : Fin 3 → Fin K, m ≠ m' →
      ∃ a, ℓ ≤ |Duplication_corner sL d m a - Duplication_corner sL d m' a| := by
    intro m m' hmm
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hmm
    refine ⟨a, ?_⟩
    rw [Duplication_corner_apply, Duplication_corner_apply]
    have hne : (m a : ℕ) ≠ (m' a : ℕ) := Fin.val_ne_of_ne ha
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have h' : ((m a : ℕ) : ℝ) + 1 ≤ ((m' a : ℕ) : ℝ) := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_left h' hsL0
      exact le_abs.2 (Or.inr (by linarith))
    · have h' : ((m' a : ℕ) : ℝ) + 1 ≤ ((m a : ℕ) : ℝ) := by exact_mod_cast h
      have := mul_le_mul_of_nonneg_left h' hsL0
      exact le_abs.2 (Or.inl (by linarith))
  set B : ℝ := 27 * decayConst8 V * N * ((N₀ + 1 : ℕ) : ℝ) / (2 * d) ^ 8 with hB
  obtain ⟨Φ, hΦ, hE⟩ := thermo_product (B := B) hsum hbox hsep hψ hVc
    (periodize_continuous hV hL) (by
      intro cell hcell x hx
      have hM : ∀ m, (Finset.univ.filter (fun j => cell j = m)).card ≤ N₀ + 1 := fun m => by
        have h2 : n m ≤ N₀ + 1 := by rcases hn m with h | h <;> omega
        calc _ = n m := by convert hcell m
          _ ≤ N₀ + 1 := h2
      have hx' : ∀ j a, sL * ((cell j a : ℕ) : ℝ) + d < x j a ∧
          x j a < sL * ((cell j a : ℕ) : ℝ) + d + ℓ := fun j a => by
        simpa only [Duplication_corner_apply] using hx j a
      have h := thermo_interBox_paper hV hd hfit' cell hM x hx'
      rw [hKsL] at h
      convert h)
  have hsumE : ∑ m, energyD V (ψ m) ≤ N * e := by
    calc ∑ m, energyD V (ψ m) ≤ ∑ m, (n m : ℝ) * e := Finset.sum_le_sum fun m _ => hψe m
      _ = N * e := by rw [← Finset.sum_mul, ← Nat.cast_sum, hsum]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  refine (e0P_le_energyD_periodize hV hL hΦ).trans ?_
  rw [EReal.coe_le_coe_iff, div_le_iff₀ hNpos]
  calc energyD (periodize L V) Φ ≤ (∑ m, energyD V (ψ m)) + B := hE
    _ ≤ N * e + B := by linarith
    _ = (e + 27 * decayConst8 V * ((N₀ : ℝ) + 1) / (2 * d) ^ 8) * N := by
      rw [hB]
      push_cast
      ring

/-- The duplication step after Lemma 2.1 [thm1] (§2.1), under the hypotheses of
Theorem 2.1 [mainthm]: Lemma 2.1 [thm1] implies Theorem 2.1 [mainthm]. -/
theorem duplicationStep {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.DuplicationStep V w := by
  rintro ⟨Ψ, hΨ, hlim⟩
  have hg : 0 < g0 V w := scat_g0_pos hV hw
  have hC0 : 0 ≤ decayConst8 V := by simpa using decayConst8_spec hV 0
  have hc0 : 0 ≤ cLHY := by unfold cLHY; positivity
  unfold Stmt.MainTheorem
  refine EReal.le_of_forall_lt_iff_le.1 fun z hz => ?_
  have hz' : cLHY < z := EReal.coe_lt_coe_iff.1 hz
  set ε := (z - cLHY) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1
    ((thermo_eventually_box_bound hV hw hΨ hlim hε0).and (eventually_ge_atTop 1))
  obtain ⟨ρa, hρa, hsc⟩ := thermo_scales
  set G : ℝ → ℝ := fun ρ => 33 * ρ ^ (1/24 : ℝ) / g0 V w ^ (3/2 : ℝ) +
    (cLHY + ε) * (1 + 33 * (ρ ^ (1/24 : ℝ)) ^ 13) ^ (3/2 : ℝ) +
    27 / 256 * decayConst8 V / g0 V w ^ (5/2 : ℝ) * (ρ ^ (1/24 : ℝ)) ^ 9 with hG
  have hrp : ∀ q : ℝ, 0 < q → Tendsto (fun ρ : ℝ => ρ ^ q) (𝓝[>] 0) (𝓝 0) := by
    intro q hq
    have := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto
    rw [Real.zero_rpow hq.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hGt : Tendsto G (𝓝[>] 0) (𝓝 (cLHY + ε)) := by
    have ht := hrp (1/24) (by norm_num)
    have h1 := (ht.const_mul 33).div_const (g0 V w ^ (3/2 : ℝ))
    have h2 := ((tendsto_const_nhds (x := (1 : ℝ))).add ((ht.pow 13).const_mul 33)).rpow_const
      (p := (3/2 : ℝ)) (Or.inr (by norm_num))
    have h3 := (ht.pow 9).const_mul (27 / 256 * decayConst8 V / g0 V w ^ (5/2 : ℝ))
    have h := (h1.add (h2.const_mul (cLHY + ε))).add h3
    convert h using 2
    simp
  have hev1 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), G ρ < z :=
    hGt.eventually (gt_mem_nhds (by rw [hε]; linarith))
  have hev2 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ ^ (17/8 : ℝ) < (4 * (N₁ : ℝ) + 1)⁻¹ :=
    (hrp (17/8) (by norm_num)).eventually (gt_mem_nhds (by positivity))
  have hev3 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ρ < ρa := nhdsWithin_le_nhds (Iio_mem_nhds hρa)
  have hev4 : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), 0 < ρ := self_mem_nhdsWithin
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hev1, hev2, hev3, hev4] with ρ hGz h17 hρa' hρ
  refine le_trans ?_ (EReal.coe_le_coe_iff.2 hGz.le)
  obtain ⟨N₀, hlo, hhi, hfit, hr0, hr1⟩ := hsc ρ hρ hρa'
  have hp : 0 < ρ ^ (17/8 : ℝ) := Real.rpow_pos_of_pos hρ _
  have hbig : 4 * (N₁ : ℝ) + 1 < ρ ^ (-(17/8 : ℝ)) := by
    rw [Real.rpow_neg hρ.le, lt_inv_comm₀ (by positivity) hp]
    exact h17
  have hN₀ : N₁ ≤ N₀ := by
    have : (N₁ : ℝ) < N₀ := by linarith
    exact_mod_cast this.le
  obtain ⟨⟨h₀, hb₀⟩, hN₀1⟩ := hN₁ N₀ hN₀
  obtain ⟨⟨h₁, hb₁⟩, -⟩ := hN₁ (N₀ + 1) (by omega)
  have hk : 0 ≤ cLHY + ε := by linarith
  set E : ℝ := g0 V w * (ρ * (1 + 33 * ρ ^ (13/24 : ℝ))) +
    (cLHY + ε) * g0 V w ^ (5/2 : ℝ) * (ρ * (1 + 33 * ρ ^ (13/24 : ℝ))) ^ (3/2 : ℝ) with hE
  have hN₀pos : (0 : ℝ) < N₀ := by exact_mod_cast hN₀1
  have he₀ : energyD V (Ψ N₀) ≤ N₀ * E := by
    have h := hb₀.trans (Duplication_mono hg.le hk (Duplication_rhotN_nonneg N₀) hr0)
    rw [div_le_iff₀ hN₀pos] at h
    linarith
  have he₁ : energyD V (Ψ (N₀ + 1)) ≤ ((N₀ : ℝ) + 1) * E := by
    have h := hb₁.trans (Duplication_mono hg.le hk (Duplication_rhotN_nonneg (N₀ + 1)) hr1)
    rw [div_le_iff₀ (by positivity)] at h
    push_cast at h
    linarith
  have hd : 0 < ρ ^ (-(1/2 : ℝ)) := Real.rpow_pos_of_pos hρ _
  have hdup := thermo_e0P_le_dup hV hρ hd hfit h₀ h₁ he₀ he₁
  have hkey := Duplication_alg (k := cLHY + ε) hg hC0 hρ hhi
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hdup] with x hx
  refine (Duplication_ratio_mono hg.le hρ.le hx).trans ?_
  unfold ratio
  rw [← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_le_coe_iff]
  exact hkey

/-- Theorem 2.1 [mainthm]: under the hypotheses on `V` (§2), with `1 - w` the zero-energy
scattering solution, the upper bound (2.2) holds. -/
theorem mainTheorem {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.MainTheorem V w :=
  duplicationStep hV hw (Lemma2_1 hV hw)

/-! ### Checks at a nondegenerate point

The Gaussian potential `V(x) = e^{-|x|²}` with its zero-energy scattering solution; the
duplication at density `ρ = 1/1000` with corridor `d = 1` and cells holding `N₀ = 1` or `2`
particles, `L̃₁ = 3`, `L̃₂ ≤ 6` and cell side at least `1500^{1/3} > 8`. -/

section Checks

/-- The Gaussian potential. -/
private def Duplication_QV : R3 → ℝ := fun x => Real.exp (-‖x‖ ^ 2)

/-- Its zero-energy scattering solution. -/
private def Duplication_Qw : R3 → ℝ :=
  (scattering_exists_unique Duplication_QV scat_gaussian_potentialHyp).choose

private lemma Duplication_Qw_spec : IsScatteringSolution Duplication_QV Duplication_Qw :=
  (scattering_exists_unique Duplication_QV scat_gaussian_potentialHyp).choose_spec.1

private lemma Duplication_LtN_one : LtN 1 = 3 := by
  simp [LtN, LN, rhoN]
  norm_num

private lemma Duplication_LtN_two : LtN (1 + 1) ≤ 6 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hr : rhoN 2 ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hr0 : 0 ≤ rhoN 2 := Real.rpow_nonneg h2.le _
  have hL : LN 2 ≤ 2 := by
    unfold LN rhoN
    push_cast
    rw [← Real.rpow_mul h2.le]
    calc (2 : ℝ) ^ (-(8/17 : ℝ) * -(25/24 : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  have hL0 : 0 ≤ LN 2 := Real.rpow_nonneg hr0 _
  have hp : rhoN 2 ^ (25/48 : ℝ) ≤ 1 := Real.rpow_le_one hr0 hr (by norm_num)
  change LN 2 * (1 + 2 * rhoN 2 ^ (25/48 : ℝ)) ≤ 6
  nlinarith

private lemma Duplication_fit :
    LtN (1 + 1) + 2 * 1 ≤ ((((1 : ℕ) : ℝ) + 1/2) / (1/1000 : ℝ)) ^ (1/3 : ℝ) := by
  have h8 : (8 : ℝ) = ((8 : ℝ) ^ 3) ^ ((3 : ℕ) : ℝ)⁻¹ :=
    (Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)).symm
  have h : (8 : ℝ) ≤ ((((1 : ℕ) : ℝ) + 1/2) / (1/1000 : ℝ)) ^ (1/3 : ℝ) := by
    rw [h8, show (1/3 : ℝ) = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
  linarith [Duplication_LtN_two]

/-- A Dirichlet trial state of one particle on `[0, L̃₁]³ = [0,3]³`. -/
private def Duplication_ψ₀ : Conf 1 → ℂ :=
  (isDirichletTrial_nonempty (L := LtN 1) (by rw [Duplication_LtN_one]; norm_num) 1).choose

private lemma Duplication_ψ₀_trial : IsDirichletTrial (LtN 1) 1 Duplication_ψ₀ :=
  (isDirichletTrial_nonempty (L := LtN 1) (by rw [Duplication_LtN_one]; norm_num) 1).choose_spec

private lemma Duplication_LtN_two_pos : 0 < LtN (1 + 1) := by
  have := LtN_monotone (show 1 ≤ 1 + 1 by norm_num)
  rw [Duplication_LtN_one] at this
  linarith

/-- A Dirichlet trial state of two particles on `[0, L̃₂]³`. -/
private def Duplication_ψ₁ : Conf (1 + 1) → ℂ :=
  (isDirichletTrial_nonempty Duplication_LtN_two_pos (1 + 1)).choose

private lemma Duplication_ψ₁_trial : IsDirichletTrial (LtN (1 + 1)) (1 + 1) Duplication_ψ₁ :=
  (isDirichletTrial_nonempty Duplication_LtN_two_pos (1 + 1)).choose_spec

/-- The common energy per particle `e = max(⟨H⟩_{ψ₀}, ⟨H⟩_{ψ₁}/2)`. -/
private def Duplication_e : ℝ :=
  max (energyD Duplication_QV Duplication_ψ₀) (energyD Duplication_QV Duplication_ψ₁ / 2)

private lemma Duplication_he₀ :
    energyD Duplication_QV Duplication_ψ₀ ≤ ((1 : ℕ) : ℝ) * Duplication_e := by
  rw [Nat.cast_one, one_mul]
  exact le_max_left _ _

private lemma Duplication_he₁ :
    energyD Duplication_QV Duplication_ψ₁ ≤ (((1 : ℕ) : ℝ) + 1) * Duplication_e := by
  have := le_max_right (energyD Duplication_QV Duplication_ψ₀)
    (energyD Duplication_QV Duplication_ψ₁ / 2)
  rw [Nat.cast_one]
  unfold Duplication_e
  linarith

/-- Duplication at `ρ = 1/1000`, `d = 1`, `N₀ = 1` for the Gaussian potential. -/
example := thermo_e0P_le_dup scat_gaussian_potentialHyp (ρ := 1/1000) (d := 1) (N₀ := 1)
  (by norm_num) (by norm_num) Duplication_fit Duplication_ψ₀_trial Duplication_ψ₁_trial
  Duplication_he₀ Duplication_he₁

/-- The duplication step for the Gaussian potential. -/
example := duplicationStep scat_gaussian_potentialHyp Duplication_Qw_spec

/-- Theorem 2.1 [mainthm] for the Gaussian potential. -/
example := mainTheorem scat_gaussian_potentialHyp Duplication_Qw_spec

end Checks

end LHYUpper
