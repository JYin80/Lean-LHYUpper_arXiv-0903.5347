module

public import LHYUpper.Particles.UpperIH
public import LHYUpper.Particles.UpperL
public import LHYUpper.TrialState.FRatio
public import LHYUpper.FourLegs.Defs
public import LHYUpper.FourLegs.Classes

@[expose] public section

/-!
# Proposition 9.1 and Lemma 9.2: the four nonzero legs of `H_{A2}` in the classes with a leg in `P_L`

Proposition 9.1, (9.4) [temp8.119]: for `u ∈ P_L` and `v ∈ P_{H,c}`, the sum
`Σ_{α ∈ M_u^a} α(v) |Ψ(α)|²` is at most `|λ_v| ρ^{3 - 1/10}`, with the rate form
`C k_c³ |λ_v| ρ^{3-7η} + C |λ_v| ρ^{1-3η} |Λ|⁻¹` uniform in `k_c ≥ 1`.

Lemma 9.2, (9.8)–(9.10): the four-leg terms of `H_{A2}`, normalized by `ρ^{-5/2}|Λ|^{-2}`, with
all legs in `P_L` (case 1), with two legs in `P_L` and two in `P_{H,c}` on opposite sides (case 2
and the case with the two sides exchanged), and with one `P_L` leg on each side (case 3, all four
placements) tend to `0`, with the rates `ρ^{2/5}`, `k_c³ ρ^{1/20}` and `k_c⁶ ρ^{1/50}`.

The proofs follow the paper: the ratio bound of Lemma 9.1 [fourlegslemma1] compares
the amplitudes of the two states of a matrix element, the bounds of §5 control the occupations
of the legs, and the tuples of legs with a coincidence are bounded by a Schwarz inequality.
-/

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-! ### Powers of `ε = ρ^{1/200}` -/

private lemma S9_rpow_eps {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {x : ℝ} (hx : x = (k : ℝ) / 200) :
    ρ ^ x = epsP ρ ^ k := by
  rw [epsP, ← Real.rpow_natCast, ← Real.rpow_mul hρ, hx]
  ring_nf

private lemma S9_rpow_eps_neg {ρ : ℝ} (hρ : 0 ≤ ρ) (k : ℕ) {x : ℝ}
    (hx : x = -((k : ℝ) / 200)) : ρ ^ x = (epsP ρ ^ k)⁻¹ := by
  rw [hx, Real.rpow_neg hρ, S9_rpow_eps hρ k rfl]

private lemma S9_eps_pos {ρ : ℝ} (hρ : 0 < ρ) : 0 < epsP ρ := Real.rpow_pos_of_pos hρ _

private lemma S9_eps_le_one {ρ : ℝ} (hρ : 0 < ρ) (h1 : ρ ≤ 1) : epsP ρ ≤ 1 :=
  Real.rpow_le_one hρ.le h1 (by norm_num)

private lemma S9_rho_eq {ρ : ℝ} (hρ : 0 ≤ ρ) : ρ = epsP ρ ^ 200 := by
  have := S9_rpow_eps hρ 200 (x := 1) (by norm_num)
  simpa using this

private lemma S9_mc_eq {ρ : ℝ} (hρ : 0 < ρ) : mc ρ = (epsP ρ)⁻¹ := by
  rw [mc, S9_rpow_eps_neg hρ.le 1 (by norm_num), pow_one]

/-- `|Λ| ε^{625} = 1`. -/
private lemma S9_L3 {N : ℕ} (hN : 1 ≤ N) : LN N ^ 3 * epsP (rhoN N) ^ 625 = 1 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have h1 : LN N ^ 3 = rhoN N ^ (-(25 / 8 : ℝ)) := by
    rw [LN, ← Real.rpow_natCast, ← Real.rpow_mul hρ.le]
    norm_num
  rw [h1, ← S9_rpow_eps hρ.le 625 (x := 625 / 200) (by norm_num), ← Real.rpow_add hρ]
  norm_num

/-- `N ε^{425} = 1`. -/
private lemma S9_Nt {N : ℕ} (hN : 1 ≤ N) : (N : ℝ) * epsP (rhoN N) ^ 425 = 1 := by
  obtain ⟨hNL, hρ, -, -⟩ := Particles_rhoN_LN hN
  rw [← hNL]
  have h2 := S9_L3 hN
  have h3 : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  calc rhoN N * LN N ^ 3 * epsP (rhoN N) ^ 425
      = LN N ^ 3 * (epsP (rhoN N) ^ 200 * epsP (rhoN N) ^ 425) := by rw [← h3]; ring
    _ = 1 := by rw [← pow_add]; exact h2

private lemma S9_ge_one {x y : ℝ} (n : ℕ) (h0 : 0 < x) (h1 : x ≤ 1) (h : y * x ^ n = 1) :
    1 ≤ y := by
  have h3 : x ^ n ≤ 1 := pow_le_one₀ h0.le h1
  have hp : 0 < x ^ n := pow_pos h0 n
  generalize x ^ n = z at h h3 hp
  by_contra hc
  nlinarith

private lemma S9_L3_ge {N : ℕ} (hN : 1 ≤ N) : 1 ≤ LN N ^ 3 := by
  obtain ⟨-, hρ, hρ1, -⟩ := Particles_rhoN_LN hN
  exact S9_ge_one 625 (S9_eps_pos hρ) (S9_eps_le_one hρ hρ1) (S9_L3 hN)

/-! ### Counting lattice points -/

/-- The cube of lattice points that contains the ball `‖p_n‖ ≤ R`. -/
private def S9_ball (L R : ℝ) : Finset Idx :=
  Finset.Icc (fun _ : Fin 3 => -⌈L * R / (2 * π)⌉) (fun _ => ⌈L * R / (2 * π)⌉)

private lemma S9_mem_ball {L R : ℝ} (hL : 0 < L) {n : Idx} (hn : ‖mom L n‖ ≤ R) :
    n ∈ S9_ball L R := by
  have hi : ∀ i : Fin 3, |(n i : ℝ)| ≤ (⌈L * R / (2 * π)⌉ : ℤ) := by
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
  unfold S9_ball
  rw [Finset.mem_Icc]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := (abs_le.1 (hi i)).1
    exact_mod_cast this
  · have := (abs_le.1 (hi i)).2
    exact_mod_cast this

private lemma S9_card_ball {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) :
    ((S9_ball L R).card : ℝ) ≤ (L * R / π + 3) ^ 3 := by
  have hx : 0 ≤ L * R / (2 * π) := by positivity
  set B : ℤ := ⌈L * R / (2 * π)⌉ with hB
  have hB1 : (B : ℝ) < L * R / (2 * π) + 1 := Int.ceil_lt_add_one _
  have hB0 : 0 ≤ B := Int.ceil_nonneg hx
  have hcard : (S9_ball L R).card = ((B + 1 - -B).toNat) ^ 3 := by
    unfold S9_ball
    rw [Pi.card_Icc]
    simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  rw [hcard]
  have h2 : ((B + 1 - -B).toNat : ℝ) = 2 * (B : ℝ) + 1 := by
    have : ((B + 1 - -B).toNat : ℤ) = 2 * B + 1 := by omega
    have h3 : (((B + 1 - -B).toNat : ℕ) : ℝ) = (((B + 1 - -B).toNat : ℤ) : ℝ) := by
      push_cast; rfl
    rw [h3, this]; push_cast; ring
  push_cast
  rw [h2]
  have h4 : 2 * (B : ℝ) + 1 ≤ L * R / π + 3 := by
    have : L * R / π = 2 * (L * R / (2 * π)) := by field_simp
    linarith
  have h5 : (0 : ℝ) ≤ 2 * (B : ℝ) + 1 := by
    have : (0 : ℝ) ≤ B := by exact_mod_cast hB0
    linarith
  exact pow_le_pow_left₀ h5 h4 3

private lemma S9_cube_le {x : ℝ} (hx : 0 ≤ x) : (x + 3) ^ 3 ≤ 64 * (1 + x ^ 3) := by
  rcases le_total x 1 with h | h
  · nlinarith [pow_nonneg hx 3, pow_nonneg hx 2]
  · nlinarith [pow_nonneg hx 3, pow_nonneg hx 2, mul_nonneg hx hx]


private lemma S9_card_ball_le {L R : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (h1 : 1 ≤ L ^ 3 * R ^ 3) :
    ((S9_ball L R).card : ℝ) ≤ 67 * (L ^ 3 * R ^ 3) := by
  have hx : 0 ≤ L * R / π := by positivity
  have h3 := Real.pi_gt_three
  have hπ : 0 < π := by linarith
  have e : (L * R / π) ^ 3 = (L ^ 3 * R ^ 3) / π ^ 3 := by
    rw [div_pow, mul_pow]
  have hπ3 : (27 : ℝ) ≤ π ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ π ^ 3 := pow_le_pow_left₀ (by norm_num) h3.le 3
  have hY : (L ^ 3 * R ^ 3) / π ^ 3 ≤ (L ^ 3 * R ^ 3) / 27 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hπ3
  calc ((S9_ball L R).card : ℝ) ≤ (L * R / π + 3) ^ 3 := S9_card_ball hL hR
    _ ≤ 64 * (1 + (L * R / π) ^ 3) := S9_cube_le hx
    _ ≤ 67 * (L ^ 3 * R ^ 3) := by rw [e]; nlinarith

private lemma S9_card_PL {N : ℕ} (hN : 1 ≤ N) :
    ((S9_ball (LN N) ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ))).card : ℝ) ≤
      67 * (LN N ^ 3 * epsP (rhoN N) ^ 297) := by
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN
  have ht := S9_eps_pos hρ
  have ht1 := S9_eps_le_one hρ hρ1
  have hR : (epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ) = epsP (rhoN N) ^ 99 := by
    rw [S9_rpow_eps hρ.le 100 (x := 1 / 2) (by norm_num)]
    field_simp
  have hge : 1 ≤ LN N ^ 3 * epsP (rhoN N) ^ 297 := by
    have h1 : epsP (rhoN N) ^ 625 ≤ epsP (rhoN N) ^ 297 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
    have h2 := S9_L3 hN
    have h3 : 0 ≤ LN N ^ 3 := by positivity
    calc (1 : ℝ) = LN N ^ 3 * epsP (rhoN N) ^ 625 := h2.symm
      _ ≤ LN N ^ 3 * epsP (rhoN N) ^ 297 := mul_le_mul_of_nonneg_left h1 h3
  rw [hR]
  have := S9_card_ball_le (L := LN N) (R := epsP (rhoN N) ^ 99) hL (by positivity)
    (by rw [← pow_mul]; simpa using hge)
  rw [← pow_mul] at this
  simpa using this

private lemma S9_card_PH {N : ℕ} (hN : 1 ≤ N) (K : ℝ) (hK : 1 ≤ K) :
    ((S9_ball (LN N) K).card : ℝ) ≤ 67 * (LN N ^ 3 * K ^ 3) := by
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN
  have hL3 := S9_L3_ge hN
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  exact S9_card_ball_le hL (by linarith) (by nlinarith)

/-! ### The tuple sum and the reduction of the class sums -/

/-- `|Ψ(β)| c |Ψ(α)|` for `β = a†_{v₁} a†_{v₂} a_{v₃} a_{v₄} α` with coefficient `c`. -/
private def S9_s (Ψ : Occ → ℂ) (v₁ v₂ v₃ v₄ : Idx) (α : Occ) : ℝ :=
  ‖conj (Ψ (a4 v₁ v₂ v₃ v₄ α).2) * ((a4 v₁ v₂ v₃ v₄ α).1 : ℂ) * Ψ α‖

/-- `Σ_α |Ψ(β)| c |Ψ(α)|` for the four legs `v₁, v₂, v₃, v₄`. -/
private def S9_T (Ψ : Occ → ℂ) (v₁ v₂ v₃ v₄ : Idx) : ℝ :=
  ∑' α : Occ, S9_s Ψ v₁ v₂ v₃ v₄ α

private lemma S9_s_eq (Ψ : Occ → ℂ) (v₁ v₂ v₃ v₄ : Idx) (α : Occ) :
    S9_s Ψ v₁ v₂ v₃ v₄ α = ‖Ψ (a4 v₁ v₂ v₃ v₄ α).2‖ * (a4 v₁ v₂ v₃ v₄ α).1 * ‖Ψ α‖ := by
  unfold S9_s
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real,
    Real.norm_of_nonneg (a4_fst_nonneg _ _ _ _ _)]

private lemma S9_s_nonneg (Ψ : Occ → ℂ) (v₁ v₂ v₃ v₄ : Idx) (α : Occ) :
    0 ≤ S9_s Ψ v₁ v₂ v₃ v₄ α := norm_nonneg _

private lemma S9_s_summable {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ v₂ v₃ v₄ : Idx) :
    Summable (S9_s Ψ v₁ v₂ v₃ v₄) :=
  Expect.id4a_summable N Ψ hΨ v₁ v₂ v₃ v₄

private lemma S9_tsum_prod_le {X Y : Type*} (f : X × Y → ℝ) (hf : ∀ z, 0 ≤ f z) (S : Finset X)
    (hS : ∀ x ∉ S, ∀ y, f (x, y) = 0) : ∑' z, f z ≤ ∑ x ∈ S, ∑' y, f (x, y) := by
  by_cases hs : Summable f
  · rw [hs.tsum_prod, tsum_eq_sum (s := S)]
    intro x hx
    simp [hS x hx]
  · rw [tsum_eq_zero_of_not_summable hs]
    exact Finset.sum_nonneg fun x _ => tsum_nonneg fun y => hf _

/-- The classes `one`, `two`, `twoAdj`, `three` do not depend on the state. -/
private lemma S9_mem_indep (ρ L kc : ℝ) (N : ℕ) {c : FourLegs.Cls}
    (hc : c = .one ∨ c = .two ∨ c = .twoAdj ∨ c = .three) (p q u : Idx) (α α' : Occ) :
    c.mem ρ L kc N (p, q, u, α) ↔ c.mem ρ L kc N (p, q, u, α') := by
  rcases hc with rfl | rfl | rfl | rfl <;> exact Iff.rfl

private def S9_equiv : (Idx × Idx × Idx) × Occ ≃ Idx × Idx × Idx × Occ :=
  (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodAssoc _ _ _))

private lemma S9_norm_int {L : ℝ} (hL : 0 < L) (V : R3 → ℝ) (Ψ : Occ → ℂ) (p q u : Idx)
    (α : Occ) :
    ‖intTerm L V Ψ (p, q, u, α)‖ =
      (L ^ 3)⁻¹ * ‖ft V (mom L u)‖ * S9_s Ψ p q (p - u) (q + u) α := by
  have e : intTerm L V Ψ (p, q, u, α) =
      (((L ^ 3)⁻¹ : ℝ) * ft V (mom L u)) *
        (conj (Ψ (a4 p q (p - u) (q + u) α).2) * ((a4 p q (p - u) (q + u) α).1 : ℂ) * Ψ α) := by
    simp only [intTerm]
    ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rfl

/-- Reduction of a class sum to the tuple sums `T`. -/
private lemma S9_reduce (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {c : FourLegs.Cls}
    (hc : c = .one ∨ c = .two ∨ c = .twoAdj ∨ c = .three) {V₀ : ℝ}
    (hV₀ : ∀ k, ‖ft V k‖ ≤ V₀) (S : Finset (Idx × Idx × Idx))
    (hS : ∀ x : Idx × Idx × Idx, c.mem (rhoN N) (LN N) kc N (x.1, x.2.1, x.2.2, 0) →
      Decomp.Part.A2.mem x.1 x.2.1 x.2.2 → x ∈ S) :
    FourLegs.absPart V w c kc N ≤
      V₀ / ((LN N ^ 3) ^ 2 * rhoN N ^ (5 / 2 : ℝ)) *
        ∑ x ∈ S.filter (fun x => c.mem (rhoN N) (LN N) kc N (x.1, x.2.1, x.2.2, 0) ∧
            Decomp.Part.A2.mem x.1 x.2.1 x.2.2),
          S9_T (trialState V w kc N) x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  have hL3 : 0 < LN N ^ 3 := by positivity
  have hρ52 : 0 < rhoN N ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
  set Ψ := trialState V w kc N with hΨdef
  set P : Idx × Idx × Idx → Prop := fun x => c.mem (rhoN N) (LN N) kc N (x.1, x.2.1, x.2.2, 0) ∧
    Decomp.Part.A2.mem x.1 x.2.1 x.2.2 with hP
  set f : Idx × Idx × Idx × Occ → ℝ := fun i =>
    if c.mem (rhoN N) (LN N) kc N i then ‖Decomp.partTerm .A2 (LN N) V Ψ i‖ else 0 with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => by simp only [hf]; split_ifs <;> positivity
  have hfeq : ∀ (x : Idx × Idx × Idx) (α : Occ), f (x.1, x.2.1, x.2.2, α) =
      if P x then (LN N ^ 3)⁻¹ * ‖ft V (mom (LN N) x.2.2)‖ *
        S9_s Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) α else 0 := by
    intro x α
    obtain ⟨p, q, u⟩ := x
    simp only [hf, hP, Decomp.partTerm]
    by_cases h1 : c.mem (rhoN N) (LN N) kc N (p, q, u, α)
    · have h1' := (S9_mem_indep (rhoN N) (LN N) kc N hc p q u α 0).1 h1
      by_cases h2 : Decomp.Part.A2.mem p q u
      · simp only [h1, h1', h2, and_self, ite_true]
        exact S9_norm_int hL V Ψ p q u α
      · simp [h1, h1', h2]
    · have h1' : ¬ c.mem (rhoN N) (LN N) kc N (p, q, u, 0) :=
        fun h => h1 ((S9_mem_indep (rhoN N) (LN N) kc N hc p q u α 0).2 h)
      simp [h1, h1']
  have hbound : ∀ (x : Idx × Idx × Idx) (α : Occ), f (x.1, x.2.1, x.2.2, α) ≤
      if P x then (LN N ^ 3)⁻¹ * V₀ * S9_s Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) α else 0 := by
    intro x α
    rw [hfeq]
    by_cases hPx : P x
    · simp only [hPx, ite_true]
      have h0 := S9_s_nonneg Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) α
      have h1 := hV₀ (mom (LN N) x.2.2)
      have h2 : 0 ≤ (LN N ^ 3)⁻¹ := by positivity
      gcongr
    · simp only [hPx, ite_false]
      exact le_rfl
  set g : (Idx × Idx × Idx) × Occ → ℝ := fun z => f (z.1.1, z.1.2.1, z.1.2.2, z.2) with hg
  have hsum : ∑' i, f i = ∑' z, g z := by
    rw [← S9_equiv.tsum_eq]
    rfl
  have hg0 : ∀ z, 0 ≤ g z := fun z => hf0 _
  have hgS : ∀ x ∉ S, ∀ α, g (x, α) = 0 := by
    intro x hx α
    simp only [hg, hfeq]
    rw [ite_eq_right]
    intro hPx
    exact hx (hS x hPx.1 hPx.2)
  have h1 := S9_tsum_prod_le g hg0 S hgS
  have h2 : ∀ x ∈ S, ∑' α, g (x, α) ≤
      if P x then (LN N ^ 3)⁻¹ * V₀ * S9_T Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) else 0 := by
    intro x _
    by_cases hPx : P x
    · simp only [hPx, ite_true]
      have hs := S9_s_summable hΨ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2)
      have hb : ∀ α, g (x, α) ≤
          (LN N ^ 3)⁻¹ * V₀ * S9_s Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) α := by
        intro α
        have := hbound x α
        simpa only [hPx, ite_true] using this
      have hsm : Summable fun α => (LN N ^ 3)⁻¹ * V₀ *
          S9_s Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) α := hs.mul_left _
      calc ∑' α, g (x, α) ≤ ∑' α, (LN N ^ 3)⁻¹ * V₀ *
            S9_s Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) α :=
          (Summable.of_nonneg_of_le (fun α => hg0 _) hb hsm).tsum_le_tsum hb hsm
        _ = _ := by rw [tsum_mul_left]; rfl
    · simp only [hPx, ite_false]
      have : ∀ α, g (x, α) = 0 := fun α => by
        simp only [hg, hfeq, hPx, ite_false]
      simp [this]
  have h3 : ∑' z, g z ≤ ∑ x ∈ S, if P x then (LN N ^ 3)⁻¹ * V₀ *
      S9_T Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) else 0 :=
    h1.trans (Finset.sum_le_sum h2)
  have hden : 0 < LN N ^ 3 * rhoN N ^ (5 / 2 : ℝ) := by positivity
  have h4 : ∑' i, f i ≤ (LN N ^ 3)⁻¹ * V₀ * ∑ x ∈ S.filter P,
      S9_T Ψ x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) := by
    rw [hsum, Finset.mul_sum, Finset.sum_filter]
    exact h3
  rw [FourLegs.absPart]
  refine (div_le_div_of_nonneg_right h4 hden.le).trans_eq ?_
  field_simp
  rfl

/-! ### Structure of a nonzero matrix element -/

private lemma S9_a4_struct {v₁ v₂ v₃ v₄ : Idx} {κ : Occ} (h : (a4 v₁ v₂ v₃ v₄ κ).1 ≠ 0) :
    ∃ γ : Occ, κ = γ + Finsupp.single v₃ 1 + Finsupp.single v₄ 1 ∧
      (a4 v₁ v₂ v₃ v₄ κ).2 = γ + Finsupp.single v₂ 1 + Finsupp.single v₁ 1 := by
  obtain ⟨γ, hγ⟩ := a4_exists_add v₁ v₂ v₃ v₄ κ h
  refine ⟨γ, hγ, ?_⟩
  rw [hγ, a4_of_add]

/-- The occupations of the bra and the ket at the four legs. -/
private lemma S9_occ {v₁ v₂ v₃ v₄ : Idx} {κ : Occ} (h : (a4 v₁ v₂ v₃ v₄ κ).1 ≠ 0)
    (h12 : v₁ ≠ v₂) (h34 : v₃ ≠ v₄) (h13 : v₁ ≠ v₃) (h14 : v₁ ≠ v₄) (h23 : v₂ ≠ v₃)
    (h24 : v₂ ≠ v₄) :
    (a4 v₁ v₂ v₃ v₄ κ).2 v₁ = κ v₁ + 1 ∧ (a4 v₁ v₂ v₃ v₄ κ).2 v₂ = κ v₂ + 1 ∧
      κ v₃ = (a4 v₁ v₂ v₃ v₄ κ).2 v₃ + 1 ∧ κ v₄ = (a4 v₁ v₂ v₃ v₄ κ).2 v₄ + 1 ∧
      1 ≤ κ v₃ ∧ 1 ≤ κ v₄ ∧ 1 ≤ (a4 v₁ v₂ v₃ v₄ κ).2 v₁ ∧ 1 ≤ (a4 v₁ v₂ v₃ v₄ κ).2 v₂ ∧
      (a4 v₁ v₂ v₃ v₄ κ).1 ^ 2 = (κ v₃ : ℝ) * κ v₄ * ((a4 v₁ v₂ v₃ v₄ κ).2 v₁ : ℝ) *
        ((a4 v₁ v₂ v₃ v₄ κ).2 v₂ : ℝ) := by
  obtain ⟨γ, hκ, hb⟩ := S9_a4_struct h
  have hsq := a4_fst_sq v₁ v₂ v₃ v₄ κ
  rw [hb, hκ]
  simp only [Finsupp.add_apply, Finsupp.single_apply, h12, h34, h13, h14, h23, h24,
    Ne.symm h12, Ne.symm h34, Ne.symm h13, Ne.symm h14, Ne.symm h23, Ne.symm h24, ite_true,
    ite_false]
  rw [hκ] at hsq
  simp only [Finsupp.add_apply, Finsupp.single_apply, h12, h34, h13, h14, h23, h24,
    Ne.symm h34, Ne.symm h13, Ne.symm h14, Ne.symm h23, Ne.symm h24, ite_true,
    ite_false] at hsq
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  rw [hsq]
  push_cast
  ring

/-! ### Occupation bounds, weights, numerics -/

private lemma S9_inM {V w : R3 → ℝ} {kc : ℝ} {N : ℕ} {α : Occ}
    (h : trialState V w kc N α ≠ 0) : InM (rhoN N) (LN N) kc N α := by
  by_contra hM
  exact h (by simp [trialState, hM])

private lemma S9_occ_le_num (α : Occ) (n : Idx) : α n ≤ α.num := by
  by_cases h : n ∈ α.support
  · exact Finset.single_le_sum (f := fun x => α x) (fun _ _ => Nat.zero_le _) h
  · simp [Finsupp.notMem_support_iff.mp h]

private lemma S9_occ_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) {α : Occ} (h : Ψ α ≠ 0)
    (n : Idx) : α n ≤ N :=
  (S9_occ_le_num α n).trans (hΨ.2 α h).le

/-- A weight bounded on the support of `Ψ` is summable against `|Ψ|²`. -/
private lemma S9_summable_w {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (f : Occ → ℝ) (B : ℝ)
    (hf : ∀ α, Ψ α ≠ 0 → |f α| ≤ B) : Summable fun α : Occ => f α * ‖Ψ α‖ ^ 2 := by
  refine Summable.of_norm_bounded (hΨ.1.summable.mul_left B) (fun α => ?_)
  rw [norm_mul, norm_pow, norm_norm, Real.norm_eq_abs]
  by_cases hz : Ψ α = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hf α hz) (by positivity)

/-- `α(v) ≤ ⌈m_c⌉` for `α ∈ M` and `v ∈ P_L`. -/
private lemma S9_occ_ceil {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α)
    {v : Idx} (hv : inPL ρ L v) : α v ≤ ⌈mc ρ⌉₊ :=
  (le_max_left (α v) (α (-v))).trans (MStar_PL_ceil hρ h hv)

private lemma S9_ceil_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    (⌈mc ρ⌉₊ : ℝ) ≤ 2 * (epsP ρ)⁻¹ := by
  have h0 : 0 ≤ mc ρ := by rw [S9_mc_eq hρ]; exact (inv_pos.2 (S9_eps_pos hρ)).le
  have h1 := Nat.ceil_lt_add_one h0
  have h2 : 1 ≤ mc ρ := by
    rw [S9_mc_eq hρ]
    exact (one_le_inv₀ (S9_eps_pos hρ)).2 (S9_eps_le_one hρ hρ1)
  rw [S9_mc_eq hρ] at h1 h2 ⊢
  linarith

private lemma S9_amp_ratio {x y A B A₀ B₁ K M : ℝ} (hM : 0 < M) (hA₀ : 0 < A₀) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hA : A₀ ≤ A) (hB : B ≤ B₁) (hK : 0 ≤ K) (h : M * (x * A) ≤ K * (y * B)) :
    x ≤ K * B₁ / (M * A₀) * y := by
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have h1 : M * A₀ * x ≤ M * (x * A) := by
    have : A₀ * x ≤ x * A := by nlinarith
    nlinarith
  have h2 : K * (y * B) ≤ K * (y * B₁) := by
    have : y * B ≤ y * B₁ := mul_le_mul_of_nonneg_left hB hy
    exact mul_le_mul_of_nonneg_left this hK
  nlinarith

/-- `p ≤ d q` from `p² ≤ D q²`, and the product bound `p q ≤ √D q²`. -/
private lemma S9_amp_sq {p q D : ℝ} (hq : 0 ≤ q) (hD : 0 ≤ D)
    (h : p ^ 2 ≤ D * q ^ 2) : p * q ≤ Real.sqrt D * q ^ 2 := by
  have h1 : p ≤ Real.sqrt D * q := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, Real.sq_sqrt hD]
    exact h
  calc p * q ≤ (Real.sqrt D * q) * q := mul_le_mul_of_nonneg_right h1 hq
    _ = Real.sqrt D * q ^ 2 := by ring

private lemma S9_pow_cancel {N : ℝ} (hN : 1 ≤ N) {z z' K : ℝ} (m j n : ℕ) (hz : 0 ≤ z)
    (hmj : m + j ≤ n) (h : N ^ n * z ≤ K * (N ^ m * z')) : N ^ j * z ≤ K * z' := by
  have hm : 0 < N ^ m := pow_pos (by linarith) m
  have h1 : N ^ m * (N ^ j * z) ≤ N ^ n * z := by
    rw [← mul_assoc, ← pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hN hmj) hz
  have h2 : N ^ m * (N ^ j * z) ≤ N ^ m * (K * z') := by nlinarith
  exact le_of_mul_le_mul_left h2 hm

/-! ### The eventual inputs -/

private lemma S9_tendsto_rpow {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (y := 8 / 17 * a) (by positivity)).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun N => ?_
  simp only [Function.comp, rhoN]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  ring_nf

private lemma S9_tendsto_rho : Tendsto rhoN atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using S9_tendsto_rpow (a := 1) one_pos
  · filter_upwards [eventually_ge_atTop 1] with N hN
    exact (Particles_rhoN_LN hN).2.1

/-- The inputs of §5 and Lemma 9.1 [fourlegslemma1] at the index `N`, with one constant `C`. -/
private structure S9_Env (V w : R3 → ℝ) (C : ℝ) (N : ℕ) : Prop where
  hN : 1 ≤ N
  hg : 0 < g0 V w
  hlam : ∀ n : Idx, inPL (rhoN N) (LN N) n →
    lam V w (rhoN N) (LN N) n ≤ -(g0 V w / 2) * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹
  hlam2 : ∀ n : Idx, inPL (rhoN N) (LN N) n → -(rhoN N)⁻¹ < lam V w (rhoN N) (LN N) n
  hlamH : ∀ n : Idx, inPH (rhoN N) (LN N) n → |lam V w (rhoN N) (LN N) n| ≤ g0 V w / epsP (rhoN N) ^ 2
  hQ1 : ∀ (kc : ℝ) (u : Idx), inPH (rhoN N) (LN N) u →
    Expect.Q (trialState V w kc N) [u] ≤
      C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2
  hQ2 : ∀ (kc : ℝ) (u v : Idx), inPH (rhoN N) (LN N) u → inPH (rhoN N) (LN N) v → u ≠ v →
    u + v ≠ 0 → Expect.Q (trialState V w kc N) [u, v] ≤
      C * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4
  hE24 : ∀ (kc : ℝ) (u v : Idx), inPL (rhoN N) (LN N) u → inPL (rhoN N) (LN N) v → u ≠ v →
    u + v ≠ 0 →
    (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α ∧ InMuA (rhoN N) (LN N) kc N v α then
        ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      (C * rhoN N * mc (rhoN N) / epsP (rhoN N)) ^ 2
  hratio : ∀ (kc : ℝ) (α β : Occ) (v : Fin 4 → Idx), (∀ i, v i ≠ 0) →
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
          |lam V w (rhoN N) (LN N) (v 0) * lam V w (rhoN N) (LN N) (v 1)|)

private lemma S9_env {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, S9_Env V w C N := by
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Lemma5_4_PH V w
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := Eq5_42 V w
  obtain ⟨C₃, hC₃, N₃, h₃⟩ := Eq5_24 V w
  obtain ⟨N₄, h₄⟩ := Lemma9_1_ratio_rho hV hw
  refine ⟨max (max C₁ C₂) C₃, le_max_of_le_left (le_max_of_le_left hC₁), ?_⟩
  have hl := S9_tendsto_rho.eventually (scat_lam_PL_le hV hw)
  filter_upwards [eventually_ge_atTop 1, hl, eventually_ge_atTop N₁, eventually_ge_atTop N₂,
    eventually_ge_atTop N₃, eventually_ge_atTop N₄] with N hN hlN hN1 hN2 hN3 hN4
  have hC₁' : C₁ ≤ max (max C₁ C₂) C₃ := le_max_of_le_left (le_max_left _ _)
  have hC₂' : C₂ ≤ max (max C₁ C₂) C₃ := le_max_of_le_left (le_max_right _ _)
  have hC₃' : C₃ ≤ max (max C₁ C₂) C₃ := le_max_right _ _
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  refine ⟨hN, scat_g0_pos hV hw, fun n hn => hlN _ n hn,
    fun n hn => (scat_lam_PL hV hw _ hρ _ n hn).1,
    fun n hn => scat_lam_PH hV hw _ hρ _ n hn, ?_, ?_, ?_, h₄ N hN4⟩
  · intro kc u hu
    refine (h₁ N hN1 kc u hu).trans ?_
    have : 0 ≤ rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2 := by positivity
    calc C₁ * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2
        = C₁ * (rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2) := by ring
      _ ≤ _ := by
        rw [mul_assoc]
        calc _ ≤ max (max C₁ C₂) C₃ * (rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| /
            ‖mom (LN N) u‖ ^ 2) := mul_le_mul_of_nonneg_right hC₁' this
          _ = _ := by ring
  · intro kc u v hu hv huv hsum
    refine (h₂ N hN2 kc u v hu hv huv hsum).trans ?_
    have : 0 ≤ |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4 := by
      have := S9_eps_pos hρ
      positivity
    calc C₂ * |lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 4 /
          epsP (rhoN N) ^ 4
        = C₂ * (|lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| * rhoN N ^ 4 /
          epsP (rhoN N) ^ 4) := by ring
      _ ≤ max (max C₁ C₂) C₃ * (|lam V w (rhoN N) (LN N) u * lam V w (rhoN N) (LN N) v| *
          rhoN N ^ 4 / epsP (rhoN N) ^ 4) := mul_le_mul_of_nonneg_right hC₂' this
      _ = _ := by ring
  · intro kc u v hu hv huv hsum
    refine (h₃ N hN3 kc u v hu hv huv hsum).trans ?_
    have he := S9_eps_pos hρ
    have hm : 0 ≤ mc (rhoN N) := by rw [S9_mc_eq hρ]; positivity
    have h0 : 0 ≤ rhoN N * mc (rhoN N) / epsP (rhoN N) := by positivity
    refine pow_le_pow_left₀ (by positivity) ?_ 2
    calc C₃ * rhoN N * mc (rhoN N) / epsP (rhoN N)
        = C₃ * (rhoN N * mc (rhoN N) / epsP (rhoN N)) := by ring
      _ ≤ max (max C₁ C₂) C₃ * (rhoN N * mc (rhoN N) / epsP (rhoN N)) :=
          mul_le_mul_of_nonneg_right hC₃' h0
      _ = _ := by ring

/-! ### The asymmetry counts `F` -/

private lemma S9_Fal4 (ρ L : ℝ) (v₁ v₂ v₃ v₄ : Idx) (α : Occ) :
    Fal ρ L ![v₁, v₂, v₃, v₄] α =
      (if inPL ρ L v₁ then Int.natAbs ((α v₁ : ℤ) - α (-v₁)) else 0) +
      (if inPL ρ L v₂ then Int.natAbs ((α v₂ : ℤ) - α (-v₂)) else 0) +
      (if inPL ρ L v₃ then Int.natAbs ((α v₃ : ℤ) - α (-v₃)) else 0) +
      (if inPL ρ L v₄ then Int.natAbs ((α v₄ : ℤ) - α (-v₄)) else 0) := by
  unfold Fal
  rw [Fin.sum_univ_four]
  rfl

private lemma S9_card4 (ρ L : ℝ) (v₁ v₂ v₃ v₄ : Idx) :
    (Finset.univ.filter (fun i : Fin 4 => inPL ρ L (![v₁, v₂, v₃, v₄] i))).card =
      (if inPL ρ L v₁ then 1 else 0) + (if inPL ρ L v₂ then 1 else 0) +
      (if inPL ρ L v₃ then 1 else 0) + (if inPL ρ L v₄ then 1 else 0) := by
  rw [Finset.card_filter, Fin.sum_univ_four]
  rfl

private lemma S9_asym_le {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {α : Occ} (h : InM ρ L kc N α)
    {u : Idx} (hu : inPL ρ L u) : Int.natAbs ((α u : ℤ) - α (-u)) ≤ 1 := by
  have h1 := MStar_PL_star hρ h hu
  have h2 := MStar_PL_star hρ h (Regions_PL_neg.2 hu)
  simp only [alphaStar, neg_neg] at h1 h2
  omega

private lemma S9_asym_one {ρ L kc : ℝ} {N : ℕ} {α : Occ} {u : Idx}
    (hα : InM ρ L kc N α) (h : Int.natAbs ((α u : ℤ) - α (-u)) = 1) :
    InMuA ρ L kc N u α := by
  refine ⟨hα, fun he => ?_⟩
  rw [he] at h
  simp at h

private lemma S9_ne_of_pm {a b : Idx} (h : Legs_pm a b) : a + b ≠ 0 := by
  intro h0
  exact h.2 (eq_neg_of_add_eq_zero_left h0)


/-- Sum of pointwise bounds `s(κ) ≤ A_bra(β(κ)) + A_ket(κ)`: the bra part is summed over the
bras, the map `κ ↦ β` being injective where the coefficient is nonzero. -/
private lemma S9_T_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ v₂ v₃ v₄ : Idx)
    (Abra Aket : Occ → ℝ) (hb0 : ∀ b, 0 ≤ Abra b) (hk0 : ∀ κ, 0 ≤ Aket κ)
    (hbs : Summable Abra) (hks : Summable Aket)
    (h : ∀ κ, (a4 v₁ v₂ v₃ v₄ κ).1 ≠ 0 →
      S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ Abra (a4 v₁ v₂ v₃ v₄ κ).2 + Aket κ) :
    S9_T Ψ v₁ v₂ v₃ v₄ ≤ (∑' b, Abra b) + ∑' κ, Aket κ := by
  set S : Set Occ := {κ | (a4 v₁ v₂ v₃ v₄ κ).1 ≠ 0} with hS
  have hinj : Function.Injective fun κ : S => (a4 v₁ v₂ v₃ v₄ κ.1).2 := by
    intro x y hxy
    exact Subtype.ext (a4_injOn v₁ v₂ v₃ v₄ x.2 y.2 hxy)
  have hFs : Summable (S.indicator fun κ => Abra (a4 v₁ v₂ v₃ v₄ κ).2) :=
    summable_subtype_iff_indicator.mp (hbs.comp_injective hinj)
  have hFle : ∑' κ, S.indicator (fun κ => Abra (a4 v₁ v₂ v₃ v₄ κ).2) κ ≤ ∑' b, Abra b := by
    rw [← tsum_subtype S (fun κ => Abra (a4 v₁ v₂ v₃ v₄ κ).2)]
    exact tsum_comp_le_tsum_of_inj hbs hb0 hinj
  have hpt : ∀ κ, S9_s Ψ v₁ v₂ v₃ v₄ κ ≤
      S.indicator (fun κ => Abra (a4 v₁ v₂ v₃ v₄ κ).2) κ + Aket κ := by
    intro κ
    by_cases hκ : κ ∈ S
    · rw [Set.indicator_of_mem hκ]
      exact h κ hκ
    · rw [Set.indicator_of_notMem hκ]
      have h0 : (a4 v₁ v₂ v₃ v₄ κ).1 = 0 := by simpa [hS] using hκ
      have : S9_s Ψ v₁ v₂ v₃ v₄ κ = 0 := by
        rw [S9_s_eq, h0]; ring
      rw [this, zero_add]
      exact hk0 κ
  calc S9_T Ψ v₁ v₂ v₃ v₄ ≤ ∑' κ, (S.indicator (fun κ => Abra (a4 v₁ v₂ v₃ v₄ κ).2) κ +
        Aket κ) := (S9_s_summable hΨ v₁ v₂ v₃ v₄).tsum_le_tsum hpt (hFs.add hks)
    _ = (∑' κ, S.indicator (fun κ => Abra (a4 v₁ v₂ v₃ v₄ κ).2) κ) + ∑' κ, Aket κ :=
        hFs.tsum_add hks
    _ ≤ _ := by gcongr

/-! ### Class 1: all four legs in `P_L` -/

/-- `ℓ ≤ |λ_n| ≤ ρ⁻¹` on `P_L`, (5.10) [lublambdaPL0]. -/
private lemma S9_lamPL {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) {n : Idx}
    (hn : inPL (rhoN N) (LN N) n) :
    g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹ ≤ |lam V w (rhoN N) (LN N) n| ∧
      |lam V w (rhoN N) (LN N) n| ≤ (rhoN N)⁻¹ := by
  have h1 := E.hlam n hn
  have h2 := E.hlam2 n hn
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hneg : lam V w (rhoN N) (LN N) n < 0 := by
    have : 0 < g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹ := by
      have := S9_eps_pos hρ
      have := E.hg
      positivity
    linarith
  rw [abs_of_neg hneg]
  constructor <;> linarith

private lemma S9_c_le {c M : ℝ} (hM : 0 ≤ M) (h : c ^ 2 ≤ M ^ 2) : c ≤ M :=
  le_of_sq_le_sq h hM


/-- `K B₁ / (N^j A₀)` with `K = ρ^{-1/10}`, `B₁ = ρ⁻²`, `A₀ = ℓ²`. -/
private def S9_D (V w : R3 → ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2 /
    ((N : ℝ) ^ j * (g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) ^ 2)

private lemma S9_D_nonneg (V w : R3 → ℝ) (N : ℕ) (j : ℕ) : 0 ≤ S9_D V w N j := by
  unfold S9_D
  have : 0 ≤ rhoN N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg (by unfold rhoN; positivity) _
  have h2 : 0 ≤ (rhoN N)⁻¹ := by unfold rhoN; positivity
  positivity

private lemma S9_ite_nonneg (P : Prop) [Decidable P] {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ (if P then x else 0) := by
  split_ifs <;> first | exact hx | exact le_rfl

private lemma S9_ite_pos {P : Prop} [Decidable P] {x : ℝ} (h : P) :
    (if P then x else (0 : ℝ)) = x := by simp [h]

/-- The six pair events of `F = 2`. -/
private def S9_W3 (ρ L kc : ℝ) (N : ℕ) (Ψ : Occ → ℂ) (v₁ v₂ v₃ v₄ : Idx) (b : Occ) : ℝ :=
  (if InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₂ b then ‖Ψ b‖ ^ 2 else 0) +
  (if InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₃ b then ‖Ψ b‖ ^ 2 else 0) +
  (if InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₄ b then ‖Ψ b‖ ^ 2 else 0) +
  (if InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₃ b then ‖Ψ b‖ ^ 2 else 0) +
  (if InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₄ b then ‖Ψ b‖ ^ 2 else 0) +
  (if InMuA ρ L kc N v₃ b ∧ InMuA ρ L kc N v₄ b then ‖Ψ b‖ ^ 2 else 0)

private lemma S9_W3_nonneg (ρ L kc : ℝ) (N : ℕ) (Ψ : Occ → ℂ) (v₁ v₂ v₃ v₄ : Idx) (b : Occ) :
    0 ≤ S9_W3 ρ L kc N Ψ v₁ v₂ v₃ v₄ b := by
  unfold S9_W3
  have h1 := S9_ite_nonneg (InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₂ b) (sq_nonneg ‖Ψ b‖)
  have h2 := S9_ite_nonneg (InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₃ b) (sq_nonneg ‖Ψ b‖)
  have h3 := S9_ite_nonneg (InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₄ b) (sq_nonneg ‖Ψ b‖)
  have h4 := S9_ite_nonneg (InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₃ b) (sq_nonneg ‖Ψ b‖)
  have h5 := S9_ite_nonneg (InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₄ b) (sq_nonneg ‖Ψ b‖)
  have h6 := S9_ite_nonneg (InMuA ρ L kc N v₃ b ∧ InMuA ρ L kc N v₄ b) (sq_nonneg ‖Ψ b‖)
  linarith

/-- If two of the four asymmetries are nonzero, `|Ψ(b)|² ≤ W₃(b)`. -/
private lemma S9_W3_ge {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {Ψ : Occ → ℂ} {b : Occ}
    (hb : InM ρ L kc N b) {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL ρ L v₁) (h₂ : inPL ρ L v₂)
    (h₃ : inPL ρ L v₃) (h₄ : inPL ρ L v₄)
    (hF : Fal ρ L ![v₁, v₂, v₃, v₄] b = 2) :
    ‖Ψ b‖ ^ 2 ≤ S9_W3 ρ L kc N Ψ v₁ v₂ v₃ v₄ b := by
  rw [S9_Fal4] at hF
  simp only [h₁, h₂, h₃, h₄, ite_true] at hF
  have l1 := S9_asym_le hρ hb h₁
  have l2 := S9_asym_le hρ hb h₂
  have l3 := S9_asym_le hρ hb h₃
  have l4 := S9_asym_le hρ hb h₄
  have e1 := S9_ite_nonneg (InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₂ b) (sq_nonneg ‖Ψ b‖)
  have e2 := S9_ite_nonneg (InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₃ b) (sq_nonneg ‖Ψ b‖)
  have e3 := S9_ite_nonneg (InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₄ b) (sq_nonneg ‖Ψ b‖)
  have e4 := S9_ite_nonneg (InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₃ b) (sq_nonneg ‖Ψ b‖)
  have e5 := S9_ite_nonneg (InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₄ b) (sq_nonneg ‖Ψ b‖)
  have e6 := S9_ite_nonneg (InMuA ρ L kc N v₃ b ∧ InMuA ρ L kc N v₄ b) (sq_nonneg ‖Ψ b‖)
  unfold S9_W3
  have key : (Int.natAbs ((b v₁ : ℤ) - b (-v₁)) = 1 ∧ Int.natAbs ((b v₂ : ℤ) - b (-v₂)) = 1) ∨
      (Int.natAbs ((b v₁ : ℤ) - b (-v₁)) = 1 ∧ Int.natAbs ((b v₃ : ℤ) - b (-v₃)) = 1) ∨
      (Int.natAbs ((b v₁ : ℤ) - b (-v₁)) = 1 ∧ Int.natAbs ((b v₄ : ℤ) - b (-v₄)) = 1) ∨
      (Int.natAbs ((b v₂ : ℤ) - b (-v₂)) = 1 ∧ Int.natAbs ((b v₃ : ℤ) - b (-v₃)) = 1) ∨
      (Int.natAbs ((b v₂ : ℤ) - b (-v₂)) = 1 ∧ Int.natAbs ((b v₄ : ℤ) - b (-v₄)) = 1) ∨
      (Int.natAbs ((b v₃ : ℤ) - b (-v₃)) = 1 ∧ Int.natAbs ((b v₄ : ℤ) - b (-v₄)) = 1) := by
    omega
  have a1 := fun h => S9_asym_one (u := v₁) hb h
  have a2 := fun h => S9_asym_one (u := v₂) hb h
  have a3 := fun h => S9_asym_one (u := v₃) hb h
  have a4' := fun h => S9_asym_one (u := v₄) hb h
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩ | ⟨k1, k2⟩
  · have := S9_ite_pos (P := InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₂ b) (x := ‖Ψ b‖ ^ 2) ⟨a1 k1, a2 k2⟩
    linarith
  · have := S9_ite_pos (P := InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₃ b) (x := ‖Ψ b‖ ^ 2) ⟨a1 k1, a3 k2⟩
    linarith
  · have := S9_ite_pos (P := InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₄ b) (x := ‖Ψ b‖ ^ 2) ⟨a1 k1, a4' k2⟩
    linarith
  · have := S9_ite_pos (P := InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₃ b) (x := ‖Ψ b‖ ^ 2) ⟨a2 k1, a3 k2⟩
    linarith
  · have := S9_ite_pos (P := InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₄ b) (x := ‖Ψ b‖ ^ 2) ⟨a2 k1, a4' k2⟩
    linarith
  · have := S9_ite_pos (P := InMuA ρ L kc N v₃ b ∧ InMuA ρ L kc N v₄ b) (x := ‖Ψ b‖ ^ 2) ⟨a3 k1, a4' k2⟩
    linarith

/-- Class 1: the pointwise bound for a nonzero matrix element between two `M` states. -/
private lemma S9_pt1 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) (h₄ : inPL (rhoN N) (LN N) v₄)
    (hGen : ∀ i j : Fin 4, i ≠ j → Legs_pm (![v₁, v₂, v₃, v₄] i) (![v₁, v₂, v₃, v₄] j))
    (κ : Occ) (hc : (a4 v₁ v₂ v₃ v₄ κ).1 ≠ 0) :
    S9_s (trialState V w kc N) v₁ v₂ v₃ v₄ κ ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 *
          (Real.sqrt (S9_D V w N 2) * ‖trialState V w kc N (a4 v₁ v₂ v₃ v₄ κ).2‖ ^ 2 +
            Real.sqrt (S9_D V w N 0) * S9_W3 (rhoN N) (LN N) kc N (trialState V w kc N)
              v₁ v₂ v₃ v₄ (a4 v₁ v₂ v₃ v₄ κ).2) +
        (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * Real.sqrt (S9_D V w N 2) * ‖trialState V w kc N κ‖ ^ 2 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  set Ψ := trialState V w kc N with hΨ
  set b := (a4 v₁ v₂ v₃ v₄ κ).2 with hb
  set c := (a4 v₁ v₂ v₃ v₄ κ).1 with hcdef
  set m : ℝ := (⌈mc (rhoN N)⌉₊ : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hD2 := S9_D_nonneg V w N 2
  have hD0 := S9_D_nonneg V w N 0
  have hW := S9_W3_nonneg (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b
  have hxn : 0 ≤ ‖Ψ κ‖ ^ 2 := by positivity
  have hyn : 0 ≤ ‖Ψ b‖ ^ 2 := by positivity
  have hR0 : 0 ≤ m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2 +
      Real.sqrt (S9_D V w N 0) * S9_W3 (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b) +
      m ^ 2 * Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2 := by
    have := Real.sqrt_nonneg (S9_D V w N 2)
    have := Real.sqrt_nonneg (S9_D V w N 0)
    positivity
  by_cases hΨκ : Ψ κ = 0
  · have : S9_s Ψ v₁ v₂ v₃ v₄ κ = 0 := by rw [S9_s_eq, hΨκ]; simp
    rw [this]; exact hR0
  by_cases hΨb : Ψ b = 0
  · have : S9_s Ψ v₁ v₂ v₃ v₄ κ = 0 := by rw [S9_s_eq, hΨb]; simp
    rw [this]; exact hR0
  have hκM : InM (rhoN N) (LN N) kc N κ := S9_inM hΨκ
  have hbM : InM (rhoN N) (LN N) kc N b := S9_inM hΨb
  have h0 : ∀ i : Fin 4, ![v₁, v₂, v₃, v₄] i ≠ 0 := by
    intro i
    fin_cases i
    exacts [Regions_PL_ne_zero hρ h₁, Regions_PL_ne_zero hρ h₂, Regions_PL_ne_zero hρ h₃,
      Regions_PL_ne_zero hρ h₄]
  have hF := Lemma9_1_F hρ h0 hGen hbM hκM hc rfl
  rw [S9_card4] at hF
  simp only [h₁, h₂, h₃, h₄, ite_true] at hF
  have hrat : ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ *
        (‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b *
        (‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|)) ∧
      ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b *
        (‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ *
        (‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|)) :=
    E.hratio kc b κ ![v₁, v₂, v₃, v₄] h0 hGen hbM hκM hc rfl
  have h12 : v₁ ≠ v₂ := (hGen 0 1 (by decide)).1
  have h34 : v₃ ≠ v₄ := (hGen 2 3 (by decide)).1
  have h13 : v₁ ≠ v₃ := (hGen 0 2 (by decide)).1
  have h14 : v₁ ≠ v₄ := (hGen 0 3 (by decide)).1
  have h23 : v₂ ≠ v₃ := (hGen 1 2 (by decide)).1
  have h24 : v₂ ≠ v₄ := (hGen 1 3 (by decide)).1
  obtain ⟨-, -, -, -, -, -, -, -, hsq⟩ := S9_occ hc h12 h34 h13 h14 h23 h24
  have hc0 : 0 ≤ c := a4_fst_nonneg _ _ _ _ _
  have hcm : c ≤ m ^ 2 := by
    apply S9_c_le (by positivity)
    rw [hsq]
    have e3 : ((κ v₃ : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (S9_occ_ceil hρ hκM h₃)
    have e4 : ((κ v₄ : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (S9_occ_ceil hρ hκM h₄)
    have e1 : ((b v₁ : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (S9_occ_ceil hρ hbM h₁)
    have e2 : ((b v₂ : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (S9_occ_ceil hρ hbM h₂)
    calc ((κ v₃ : ℕ) : ℝ) * (κ v₄ : ℕ) * (b v₁ : ℕ) * (b v₂ : ℕ) ≤ m * m * m * m := by gcongr
      _ = (m ^ 2) ^ 2 := by ring
  -- the bounds on `|λ|`
  have l1 := S9_lamPL E h₁
  have l2 := S9_lamPL E h₂
  have l3 := S9_lamPL E h₃
  have l4 := S9_lamPL E h₄
  have hℓ : 0 < g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹ := by
    have := S9_eps_pos hρ
    have := E.hg
    positivity
  have hAlo : (g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) ^ 2 ≤
      |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂| := by
    rw [abs_mul, sq]; exact mul_le_mul l1.1 l2.1 hℓ.le (abs_nonneg _)
  have hAhi : |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂| ≤ ((rhoN N)⁻¹) ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul l1.2 l2.2 (abs_nonneg _) (inv_pos.2 hρ).le
  have hBlo : (g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) ^ 2 ≤
      |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| := by
    rw [abs_mul, sq]; exact mul_le_mul l3.1 l4.1 hℓ.le (abs_nonneg _)
  have hBhi : |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| ≤ ((rhoN N)⁻¹) ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul l3.2 l4.2 (abs_nonneg _) (inv_pos.2 hρ).le
  have hK : 0 ≤ rhoN N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hρ.le _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast E.hN
  have hℓ2 : 0 < (g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) ^ 2 := by positivity
  have hspos : S9_s Ψ v₁ v₂ v₃ v₄ κ = ‖Ψ b‖ * c * ‖Ψ κ‖ := S9_s_eq _ _ _ _ _ _
  have hp : 0 ≤ ‖Ψ κ‖ := norm_nonneg _
  have hq : 0 ≤ ‖Ψ b‖ := norm_nonneg _
  -- three cases for `F(β)`
  rcases (by omega : Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b ≤ 1 ∨
      Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b = 2 ∨
      3 ≤ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) with ha | ha | ha
  · -- bra with `F ≤ 1`
    have h1 := S9_pow_cancel hN1 (z := ‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ *
        lam V w (rhoN N) (LN N) v₂|) (z' := ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ *
        lam V w (rhoN N) (LN N) v₄|) (K := rhoN N ^ (-(1 / 10 : ℝ)))
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) 2
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ) (by positivity) (by omega)
      (by simpa only [mul_assoc] using hrat.1)
    have h2 := S9_amp_ratio (M := (N : ℝ) ^ 2) (by positivity) hℓ2 hxn hyn hAlo hBhi hK h1
    have h3 : ‖Ψ κ‖ * ‖Ψ b‖ ≤ Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2 :=
      S9_amp_sq hq (S9_D_nonneg V w N 2) (by unfold S9_D; exact h2)
    have h4 : S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2) := by
      rw [hspos]
      calc ‖Ψ b‖ * c * ‖Ψ κ‖ = c * (‖Ψ κ‖ * ‖Ψ b‖) := by ring
        _ ≤ m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2) :=
          mul_le_mul hcm h3 (by positivity) (by positivity)
    have t1 : 0 ≤ m ^ 2 * (Real.sqrt (S9_D V w N 0) *
        S9_W3 (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b) :=
      mul_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _) hW)
    have t2 : 0 ≤ m ^ 2 * Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2 := by positivity
    linarith only [h4, t1, t2]
  · -- `F = 2`
    have hk : Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ = 2 := by omega
    have h1 := S9_pow_cancel hN1 (z := ‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ *
        lam V w (rhoN N) (LN N) v₂|) (z' := ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ *
        lam V w (rhoN N) (LN N) v₄|) (K := rhoN N ^ (-(1 / 10 : ℝ)))
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) 0
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ) (by positivity) (by omega)
      (by simpa only [mul_assoc] using hrat.1)
    have h2 := S9_amp_ratio (M := (N : ℝ) ^ 0) (by positivity) hℓ2 hxn hyn hAlo hBhi hK h1
    have h3 : ‖Ψ κ‖ * ‖Ψ b‖ ≤ Real.sqrt (S9_D V w N 0) * ‖Ψ b‖ ^ 2 :=
      S9_amp_sq hq (S9_D_nonneg V w N 0) (by unfold S9_D; exact h2)
    have hW3 := S9_W3_ge hρ hbM h₁ h₂ h₃ h₄ ha (Ψ := Ψ)
    have h4 : S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ m ^ 2 * (Real.sqrt (S9_D V w N 0) * ‖Ψ b‖ ^ 2) := by
      rw [hspos]
      calc ‖Ψ b‖ * c * ‖Ψ κ‖ = c * (‖Ψ κ‖ * ‖Ψ b‖) := by ring
        _ ≤ m ^ 2 * (Real.sqrt (S9_D V w N 0) * ‖Ψ b‖ ^ 2) :=
          mul_le_mul hcm h3 (by positivity) (by positivity)
    have h5 : m ^ 2 * (Real.sqrt (S9_D V w N 0) * ‖Ψ b‖ ^ 2) ≤ m ^ 2 * (Real.sqrt (S9_D V w N 0) *
        S9_W3 (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b) := by gcongr
    have t1 : 0 ≤ m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2) := by positivity
    have t2 : 0 ≤ m ^ 2 * Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2 := by positivity
    linarith only [h4, h5, t1, t2]
  · -- ket with `F(β) ≥ 3`
    have h1 := S9_pow_cancel hN1 (z := ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ *
        lam V w (rhoN N) (LN N) v₄|) (z' := ‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ *
        lam V w (rhoN N) (LN N) v₂|) (K := rhoN N ^ (-(1 / 10 : ℝ)))
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ) 2
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) (by positivity) (by omega)
      (by simpa only [mul_assoc] using hrat.2)
    have h2 := S9_amp_ratio (M := (N : ℝ) ^ 2) (by positivity) hℓ2 hyn hxn hBlo hAhi hK h1
    have h3 : ‖Ψ b‖ * ‖Ψ κ‖ ≤ Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2 :=
      S9_amp_sq hp (S9_D_nonneg V w N 2) (by unfold S9_D; exact h2)
    have h4 : S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ m ^ 2 * Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2 := by
      rw [hspos]
      calc ‖Ψ b‖ * c * ‖Ψ κ‖ = c * (‖Ψ b‖ * ‖Ψ κ‖) := by ring
        _ ≤ m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2) :=
          mul_le_mul hcm h3 (by positivity) (by positivity)
        _ = _ := by ring
    have t1 : 0 ≤ m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2 +
        Real.sqrt (S9_D V w N 0) * S9_W3 (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b) := by
      have := Real.sqrt_nonneg (S9_D V w N 2)
      have := Real.sqrt_nonneg (S9_D V w N 0)
      exact mul_nonneg (by positivity) (add_nonneg (by positivity) (mul_nonneg (by positivity) hW))
    linarith only [h4, t1]


private lemma S9_summable_ite {ψ : Occ → ℝ} (hs : Summable ψ) (hψ : ∀ α, 0 ≤ ψ α)
    (p : Occ → Prop) [DecidablePred p] : Summable fun α => if p α then ψ α else 0 :=
  Summable.of_nonneg_of_le (fun α => by split_ifs <;> simp [hψ α])
    (fun α => by split_ifs <;> simp [hψ α]) hs

private lemma S9_W3_hasSum {ρ L kc : ℝ} {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ)
    (v₁ v₂ v₃ v₄ : Idx) :
    HasSum (S9_W3 ρ L kc N Ψ v₁ v₂ v₃ v₄)
      ((∑' b, if InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₂ b then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₃ b then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA ρ L kc N v₁ b ∧ InMuA ρ L kc N v₄ b then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₃ b then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA ρ L kc N v₂ b ∧ InMuA ρ L kc N v₄ b then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA ρ L kc N v₃ b ∧ InMuA ρ L kc N v₄ b then ‖Ψ b‖ ^ 2 else 0)) := by
  have hs : Summable fun b : Occ => ‖Ψ b‖ ^ 2 := hΨ.1.summable
  have hn : ∀ b : Occ, 0 ≤ ‖Ψ b‖ ^ 2 := fun b => by positivity
  unfold S9_W3
  exact ((((((S9_summable_ite hs hn _).hasSum.add (S9_summable_ite hs hn _).hasSum).add
    (S9_summable_ite hs hn _).hasSum).add (S9_summable_ite hs hn _).hasSum).add
    (S9_summable_ite hs hn _).hasSum).add (S9_summable_ite hs hn _).hasSum)

/-- Class 1, generic legs: the tuple sum. -/
private lemma S9_gen1 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) (h₄ : inPL (rhoN N) (LN N) v₄)
    (hGen : ∀ i j : Fin 4, i ≠ j → Legs_pm (![v₁, v₂, v₃, v₄] i) (![v₁, v₂, v₃, v₄] j)) :
    S9_T (trialState V w kc N) v₁ v₂ v₃ v₄ ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * (Real.sqrt (S9_D V w N 2) +
        Real.sqrt (S9_D V w N 0) * (6 * (C * rhoN N * mc (rhoN N) / epsP (rhoN N)) ^ 2)) +
      (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * Real.sqrt (S9_D V w N 2) := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  set Ψ := trialState V w kc N with hΨdef
  set m : ℝ := (⌈mc (rhoN N)⌉₊ : ℝ) with hm
  have hs : Summable fun b : Occ => ‖Ψ b‖ ^ 2 := hΨ.1.summable
  have hn : ∀ b : Occ, 0 ≤ ‖Ψ b‖ ^ 2 := fun b => by positivity
  have hD2 := Real.sqrt_nonneg (S9_D V w N 2)
  have hD0 := Real.sqrt_nonneg (S9_D V w N 0)
  have hW := S9_W3_hasSum (ρ := rhoN N) (L := LN N) (kc := kc) hΨ v₁ v₂ v₃ v₄
  have hWs := hW.summable
  have hWn := S9_W3_nonneg (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄
  have hbs : Summable fun b => m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2 +
      Real.sqrt (S9_D V w N 0) * S9_W3 (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b) :=
    (((hs.mul_left _).add (hWs.mul_left _)).mul_left _)
  have hks : Summable fun κ => m ^ 2 * Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2 :=
    hs.mul_left _
  have key := S9_T_le hΨ v₁ v₂ v₃ v₄
    (fun b => m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2 +
      Real.sqrt (S9_D V w N 0) * S9_W3 (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b))
    (fun κ => m ^ 2 * Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2)
    (fun b => by have := hWn b; positivity) (fun κ => by positivity) hbs hks
    (fun κ hc => S9_pt1 E kc h₁ h₂ h₃ h₄ hGen κ hc)
  refine key.trans ?_
  have e1 : ∑' b, m ^ 2 * (Real.sqrt (S9_D V w N 2) * ‖Ψ b‖ ^ 2 +
      Real.sqrt (S9_D V w N 0) * S9_W3 (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b) =
      m ^ 2 * (Real.sqrt (S9_D V w N 2) * 1 + Real.sqrt (S9_D V w N 0) *
        ∑' b, S9_W3 (rhoN N) (LN N) kc N Ψ v₁ v₂ v₃ v₄ b) := by
    rw [tsum_mul_left, (hs.mul_left _).tsum_add (hWs.mul_left _), tsum_mul_left, tsum_mul_left,
      hΨ.1.tsum_eq]
  have e2 : ∑' κ, m ^ 2 * Real.sqrt (S9_D V w N 2) * ‖Ψ κ‖ ^ 2 =
      m ^ 2 * Real.sqrt (S9_D V w N 2) := by
    rw [tsum_mul_left, hΨ.1.tsum_eq, mul_one]
  rw [e1, e2, hW.tsum_eq]
  have p12 : v₁ ≠ v₂ ∧ v₁ + v₂ ≠ 0 :=
    ⟨(hGen 0 1 (by decide)).1, S9_ne_of_pm (hGen 0 1 (by decide))⟩
  have p13 : v₁ ≠ v₃ ∧ v₁ + v₃ ≠ 0 :=
    ⟨(hGen 0 2 (by decide)).1, S9_ne_of_pm (hGen 0 2 (by decide))⟩
  have p14 : v₁ ≠ v₄ ∧ v₁ + v₄ ≠ 0 :=
    ⟨(hGen 0 3 (by decide)).1, S9_ne_of_pm (hGen 0 3 (by decide))⟩
  have p23 : v₂ ≠ v₃ ∧ v₂ + v₃ ≠ 0 :=
    ⟨(hGen 1 2 (by decide)).1, S9_ne_of_pm (hGen 1 2 (by decide))⟩
  have p24 : v₂ ≠ v₄ ∧ v₂ + v₄ ≠ 0 :=
    ⟨(hGen 1 3 (by decide)).1, S9_ne_of_pm (hGen 1 3 (by decide))⟩
  have p34 : v₃ ≠ v₄ ∧ v₃ + v₄ ≠ 0 :=
    ⟨(hGen 2 3 (by decide)).1, S9_ne_of_pm (hGen 2 3 (by decide))⟩
  have b12 := E.hE24 kc v₁ v₂ h₁ h₂ p12.1 p12.2
  have b13 := E.hE24 kc v₁ v₃ h₁ h₃ p13.1 p13.2
  have b14 := E.hE24 kc v₁ v₄ h₁ h₄ p14.1 p14.2
  have b23 := E.hE24 kc v₂ v₃ h₂ h₃ p23.1 p23.2
  have b24 := E.hE24 kc v₂ v₄ h₂ h₄ p24.1 p24.2
  have b34 := E.hE24 kc v₃ v₄ h₃ h₄ p34.1 p34.2
  have hsum6 : ((∑' b, if InMuA (rhoN N) (LN N) kc N v₁ b ∧ InMuA (rhoN N) (LN N) kc N v₂ b
        then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA (rhoN N) (LN N) kc N v₁ b ∧ InMuA (rhoN N) (LN N) kc N v₃ b
        then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA (rhoN N) (LN N) kc N v₁ b ∧ InMuA (rhoN N) (LN N) kc N v₄ b
        then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA (rhoN N) (LN N) kc N v₂ b ∧ InMuA (rhoN N) (LN N) kc N v₃ b
        then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA (rhoN N) (LN N) kc N v₂ b ∧ InMuA (rhoN N) (LN N) kc N v₄ b
        then ‖Ψ b‖ ^ 2 else 0) +
      (∑' b, if InMuA (rhoN N) (LN N) kc N v₃ b ∧ InMuA (rhoN N) (LN N) kc N v₄ b
        then ‖Ψ b‖ ^ 2 else 0)) ≤ 6 * (C * rhoN N * mc (rhoN N) / epsP (rhoN N)) ^ 2 := by
    linarith only [b12, b13, b14, b23, b24, b34]
  have hm0 : 0 ≤ m ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hsum6 hD0
  have := mul_le_mul_of_nonneg_left (add_le_add_left this (Real.sqrt (S9_D V w N 2) * 1)) hm0
  linarith only [this]

/-! ### Schwarz bounds for the special tuples -/

/-- The weight `β(v₁)β(v₂) − δ_{v₁v₂}β(v₁)` of `‖a_{v₁} a_{v₂} Ψ‖²`. -/
private def S9_w2 (v₁ v₂ : Idx) (β : Occ) : ℝ :=
  (β v₁ : ℝ) * β v₂ - if v₁ = v₂ then (β v₁ : ℝ) else 0

private lemma S9_w2_nonneg (v₁ v₂ : Idx) (β : Occ) : 0 ≤ S9_w2 v₁ v₂ β := by
  unfold S9_w2
  rw [← a4_diag_fst]
  exact a4_fst_nonneg _ _ _ _ _

private lemma S9_w2_le (v₁ v₂ : Idx) (β : Occ) : S9_w2 v₁ v₂ β ≤ (β v₁ : ℝ) * β v₂ := by
  unfold S9_w2
  have : 0 ≤ (if v₁ = v₂ then (β v₁ : ℝ) else 0) := by split_ifs <;> simp
  linarith

private lemma S9_wsum_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (w : Occ → ℝ)
    (hw0 : ∀ β, 0 ≤ w β) {B : ℝ} (hB : ∀ β, Ψ β ≠ 0 → w β ≤ B) :
    ∑' β, w β * ‖Ψ β‖ ^ 2 ≤ B := by
  have hs := hΨ.1.summable
  have h1 : Summable fun β => w β * ‖Ψ β‖ ^ 2 :=
    S9_summable_w hΨ w B (fun β h => by rw [abs_of_nonneg (hw0 β)]; exact hB β h)
  have h2 : ∑' β, w β * ‖Ψ β‖ ^ 2 ≤ ∑' β, B * ‖Ψ β‖ ^ 2 :=
    h1.tsum_le_tsum (fun β => by
      by_cases h : Ψ β = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_right (hB β h) (by positivity)) (hs.mul_left B)
  rw [tsum_mul_left, hΨ.1.tsum_eq, mul_one] at h2
  exact h2

/-- `S9_T ≤ √B₁₂ √B₃₄` from the Schwarz bound. -/
private lemma S9_T_le_sch {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (v₁ v₂ v₃ v₄ : Idx)
    {B₁ B₂ : ℝ} (h₁ : ∑' β, S9_w2 v₁ v₂ β * ‖Ψ β‖ ^ 2 ≤ B₁)
    (h₂ : ∑' α, S9_w2 v₃ v₄ α * ‖Ψ α‖ ^ 2 ≤ B₂) :
    S9_T Ψ v₁ v₂ v₃ v₄ ≤ Real.sqrt B₁ * Real.sqrt B₂ := by
  have h := FourLegs_schwarz hΨ v₁ v₂ v₃ v₄
  refine h.trans ?_
  exact mul_le_mul (Real.sqrt_le_sqrt h₁) (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _)

/-- Class 1, all tuples: `T ≤ ⌈m_c⌉²`. -/
private lemma S9_spec1 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) (h₄ : inPL (rhoN N) (LN N) v₄) :
    S9_T (trialState V w kc N) v₁ v₂ v₃ v₄ ≤ (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  have key : ∀ x y : Idx, inPL (rhoN N) (LN N) x → inPL (rhoN N) (LN N) y →
      ∑' β, S9_w2 x y β * ‖trialState V w kc N β‖ ^ 2 ≤ (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 := by
    intro x y hx hy
    refine S9_wsum_le hΨ _ (S9_w2_nonneg x y) (fun β hβ => ?_)
    have hM := S9_inM hβ
    have e1 : ((β x : ℕ) : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := Nat.cast_le.2 (S9_occ_ceil hρ hM hx)
    have e2 : ((β y : ℕ) : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := Nat.cast_le.2 (S9_occ_ceil hρ hM hy)
    calc S9_w2 x y β ≤ (β x : ℝ) * β y := S9_w2_le x y β
      _ ≤ (⌈mc (rhoN N)⌉₊ : ℝ) * (⌈mc (rhoN N)⌉₊ : ℝ) := by gcongr
      _ = _ := by ring
  have := S9_T_le_sch hΨ v₁ v₂ v₃ v₄ (key v₁ v₂ h₁ h₂) (key v₃ v₄ h₃ h₄)
  rwa [← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)] at this

/-! ### Special tuples, splitting the tuple sum -/

private lemma S9_forall_legs {P : Idx → Prop} (p q u : Idx) :
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

private lemma S9_pm_symm {a b : Idx} (h : Legs_pm a b) : Legs_pm b a :=
  ⟨Ne.symm h.1, fun e => h.2 (by rw [e, neg_neg])⟩

/-- The legs of a summand of `H_{A2}` are pairwise `≠ ±`, except for six coincidences. -/
private lemma S9_not_gen {p q u : Idx} (hA : Decomp.Part.A2.mem p q u)
    (h : ¬ FourLegs.Gen (FourLegs.legs p q u)) :
    p = q ∨ p - u = q + u ∨ p = -(p - u) ∨ p = -(q + u) ∨ q = -(p - u) ∨ q = -(q + u) := by
  by_contra hno
  apply h
  obtain ⟨-, hpq, hS⟩ := hA
  have hu0 : u ≠ 0 := fun e => hS (Or.inl e)
  have hup : u ≠ p - q := fun e => hS (Or.inr e)
  simp only [not_or] at hno
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hno
  have e13 : p ≠ p - u := fun e => hu0 (by
    funext i; have := congr_fun e i; simp only [Pi.sub_apply] at this ⊢; simp; omega)
  have e14 : p ≠ q + u := fun e => hup (by
    funext i; have := congr_fun e i; simp only [Pi.add_apply, Pi.sub_apply] at this ⊢; omega)
  have e23 : q ≠ p - u := fun e => hup (by
    funext i; have := congr_fun e i; simp only [Pi.sub_apply] at this ⊢; omega)
  have e24 : q ≠ q + u := fun e => hu0 (by
    funext i; have := congr_fun e i; simp only [Pi.add_apply] at this ⊢; simp; omega)
  have e12 : p ≠ -q := fun e => hpq (by
    funext i; have := congr_fun e i; simp only [Pi.add_apply, Pi.neg_apply] at this ⊢; simp; omega)
  have e34 : p - u ≠ -(q + u) := fun e => hpq (by
    funext i; have := congr_fun e i; simp only [Pi.add_apply, Pi.neg_apply, Pi.sub_apply] at this ⊢
    simp; omega)
  have key : ∀ i j : Fin 4, i < j → Legs_pm (FourLegs.legs p q u i) (FourLegs.legs p q u j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | (exfalso; revert hij; decide)
      | exact ⟨c1, e12⟩
      | exact ⟨e13, c3⟩
      | exact ⟨e14, c4⟩
      | exact ⟨e23, c5⟩
      | exact ⟨e24, c6⟩
      | exact ⟨c2, e34⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h' | h'
  · exact key i j h'
  · exact S9_pm_symm (key j i h')

/-- Splitting the tuple sum into generic and special tuples. -/
private lemma S9_sum_split {α : Type*} (S Sspec : Finset α) (P G : α → Prop)
    [DecidablePred P] [DecidablePred G] (T : α → ℝ)
    {Bg Bs : ℝ} (hBg : 0 ≤ Bg) (hBs : 0 ≤ Bs)
    (hg : ∀ x ∈ S, P x → G x → T x ≤ Bg) (hs : ∀ x ∈ S, P x → T x ≤ Bs)
    (hsp : ∀ x ∈ S, P x → ¬ G x → x ∈ Sspec) :
    ∑ x ∈ S.filter P, T x ≤ S.card * Bg + Sspec.card * Bs := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter P) G]
  have h1 : ∑ x ∈ (S.filter P).filter G, T x ≤ S.card * Bg := by
    calc ∑ x ∈ (S.filter P).filter G, T x ≤ ((S.filter P).filter G).card * Bg := by
          have := Finset.sum_le_card_nsmul ((S.filter P).filter G) T Bg (fun x hx => by
            simp only [Finset.mem_filter] at hx
            exact hg x hx.1.1 hx.1.2 hx.2)
          simpa [nsmul_eq_mul] using this
      _ ≤ S.card * Bg := by
          apply mul_le_mul_of_nonneg_right _ hBg
          exact_mod_cast (Finset.card_le_card ((Finset.filter_subset _ _).trans
            (Finset.filter_subset _ _)))
  have h2 : ∑ x ∈ (S.filter P).filter (fun x => ¬ G x), T x ≤ Sspec.card * Bs := by
    calc ∑ x ∈ (S.filter P).filter (fun x => ¬ G x), T x ≤
          ((S.filter P).filter (fun x => ¬ G x)).card * Bs := by
          have := Finset.sum_le_card_nsmul ((S.filter P).filter (fun x => ¬ G x)) T Bs
            (fun x hx => by
              simp only [Finset.mem_filter] at hx
              exact hs x hx.1.1 hx.1.2)
          simpa [nsmul_eq_mul] using this
      _ ≤ Sspec.card * Bs := by
          apply mul_le_mul_of_nonneg_right _ hBs
          refine Nat.cast_le.2 (Finset.card_le_card ?_)
          intro x hx
          simp only [Finset.mem_filter] at hx
          exact hsp x hx.1.1 hx.1.2 hx.2
  linarith


/-- Closing arithmetic: `V₀ t^P (n_S B_g + n_T B_s) ≤ V₀ (c_S c_g + c_T c_s) t^k`. -/
private lemma S9_close {t V₀ nS nT Bg Bs cS cT cg cs : ℝ} {P a b e f f' k : ℕ} (ht : 0 < t)
    (ht1 : t ≤ 1) (hV : 0 ≤ V₀) (hnS : 0 ≤ nS) (hnT : 0 ≤ nT)
    (hcS : 0 ≤ cS) (hcT : 0 ≤ cT) (hcg : 0 ≤ cg) (hcs : 0 ≤ cs)
    (hnS' : nS * t ^ a ≤ cS) (hnT' : nT * t ^ b ≤ cT) (hBg' : Bg ≤ cg * t ^ e)
    (hBs' : Bs * t ^ f ≤ cs * t ^ f') (h1 : k + a ≤ P + e) (h2 : k + b + f ≤ P + f') :
    V₀ * t ^ P * (nS * Bg + nT * Bs) ≤ V₀ * (cS * cg + cT * cs) * t ^ k := by
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨d', hd'⟩ := Nat.exists_eq_add_of_le h2
  have htd : t ^ d ≤ 1 := pow_le_one₀ ht.le ht1
  have htd' : t ^ d' ≤ 1 := pow_le_one₀ ht.le ht1
  have ht0 : ∀ n : ℕ, 0 ≤ t ^ n := fun n => pow_nonneg ht.le n
  have e1 : V₀ * t ^ P * (nS * Bg) ≤ V₀ * (cS * cg) * t ^ k := by
    have h3 : t ^ P * t ^ e = t ^ k * t ^ a * t ^ d := by
      rw [← pow_add, ← pow_add, ← pow_add]; congr 1
    calc V₀ * t ^ P * (nS * Bg) ≤ V₀ * t ^ P * (nS * (cg * t ^ e)) := by gcongr
      _ = V₀ * cg * (nS * t ^ a) * (t ^ k * t ^ d) := by
          rw [show V₀ * t ^ P * (nS * (cg * t ^ e)) = V₀ * cg * nS * (t ^ P * t ^ e) by ring, h3]
          ring
      _ ≤ V₀ * cg * cS * (t ^ k * 1) := by
          gcongr
      _ = V₀ * (cS * cg) * t ^ k := by ring
  have e2 : V₀ * t ^ P * (nT * Bs) ≤ V₀ * (cT * cs) * t ^ k := by
    have h3 : t ^ P * t ^ f' = t ^ k * t ^ b * t ^ f * t ^ d' := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]; congr 1
    have htf : 0 < t ^ f := pow_pos ht f
    have hpre : 0 ≤ V₀ * t ^ P * nT := mul_nonneg (mul_nonneg hV (ht0 P)) hnT
    have e2' : t ^ f * (V₀ * t ^ P * (nT * Bs)) ≤ t ^ f * (V₀ * (cT * cs) * t ^ k) := by
      calc t ^ f * (V₀ * t ^ P * (nT * Bs)) = (V₀ * t ^ P * nT) * (Bs * t ^ f) := by ring
        _ ≤ (V₀ * t ^ P * nT) * (cs * t ^ f') := mul_le_mul_of_nonneg_left hBs' hpre
        _ = V₀ * cs * nT * (t ^ P * t ^ f') := by ring
        _ = V₀ * cs * (nT * t ^ b) * (t ^ k * t ^ f * t ^ d') := by rw [h3]; ring
        _ ≤ V₀ * cs * cT * (t ^ k * t ^ f * 1) := by
            gcongr
        _ = t ^ f * (V₀ * (cT * cs) * t ^ k) := by ring
    exact le_of_mul_le_mul_left e2' htf
  calc V₀ * t ^ P * (nS * Bg + nT * Bs) = V₀ * t ^ P * (nS * Bg) + V₀ * t ^ P * (nT * Bs) := by
        ring
    _ ≤ V₀ * (cS * cg) * t ^ k + V₀ * (cT * cs) * t ^ k := add_le_add e1 e2
    _ = _ := by ring

/-- The tuples with a coincidence of two legs, parametrized by two legs. -/
private def S9_sp (B₁ B₂ : Finset Idx) : Finset (Idx × Idx × Idx) :=
  (B₁ ×ˢ B₂).image (fun y => (y.1, y.1, y.1 - y.2)) ∪
  (B₁ ×ˢ B₂).image (fun y => (y.1, y.2 + y.2 - y.1, y.1 - y.2)) ∪
  (B₁ ×ˢ B₂).image (fun y => (y.1, y.2, y.1 + y.1)) ∪
  (B₁ ×ˢ B₂).image (fun y => (y.1, y.2, -y.1 - y.2)) ∪
  (B₁ ×ˢ B₂).image (fun y => (y.1, y.2, y.1 + y.2)) ∪
  (B₁ ×ˢ B₂).image (fun y => (y.1, y.2, -y.2 - y.2))

private lemma S9_sp_card (B₁ B₂ : Finset Idx) :
    ((S9_sp B₁ B₂).card : ℝ) ≤ 6 * ((B₁.card : ℝ) * B₂.card) := by
  have h : ∀ f : Idx × Idx → Idx × Idx × Idx,
      ((B₁ ×ˢ B₂).image f).card ≤ B₁.card * B₂.card := fun f =>
    Finset.card_image_le.trans (by rw [Finset.card_product])
  unfold S9_sp
  have a1 := h (fun y : Idx × Idx => (y.1, y.1, y.1 - y.2))
  have a2 := h (fun y : Idx × Idx => (y.1, y.2 + y.2 - y.1, y.1 - y.2))
  have a3 := h (fun y : Idx × Idx => (y.1, y.2, y.1 + y.1))
  have a4 := h (fun y : Idx × Idx => (y.1, y.2, -y.1 - y.2))
  have a5 := h (fun y : Idx × Idx => (y.1, y.2, y.1 + y.2))
  have a6 := h (fun y : Idx × Idx => (y.1, y.2, -y.2 - y.2))
  generalize ((B₁ ×ˢ B₂).image (fun y : Idx × Idx => (y.1, y.1, y.1 - y.2))) = I1 at a1 ⊢
  generalize ((B₁ ×ˢ B₂).image (fun y : Idx × Idx => (y.1, y.2 + y.2 - y.1, y.1 - y.2))) = I2
    at a2 ⊢
  generalize ((B₁ ×ˢ B₂).image (fun y : Idx × Idx => (y.1, y.2, y.1 + y.1))) = I3 at a3 ⊢
  generalize ((B₁ ×ˢ B₂).image (fun y : Idx × Idx => (y.1, y.2, -y.1 - y.2))) = I4 at a4 ⊢
  generalize ((B₁ ×ˢ B₂).image (fun y : Idx × Idx => (y.1, y.2, y.1 + y.2))) = I5 at a5 ⊢
  generalize ((B₁ ×ˢ B₂).image (fun y : Idx × Idx => (y.1, y.2, -y.2 - y.2))) = I6 at a6 ⊢
  have u1 := Finset.card_union_le I1 I2
  have u2 := Finset.card_union_le (I1 ∪ I2) I3
  have u3 := Finset.card_union_le (I1 ∪ I2 ∪ I3) I4
  have u4 := Finset.card_union_le (I1 ∪ I2 ∪ I3 ∪ I4) I5
  have u5 := Finset.card_union_le (I1 ∪ I2 ∪ I3 ∪ I4 ∪ I5) I6
  have : (I1 ∪ I2 ∪ I3 ∪ I4 ∪ I5 ∪ I6).card ≤ 6 * (B₁.card * B₂.card) := by omega
  exact_mod_cast this


private lemma S9_mem_sp1 {B₁ B₂ : Finset Idx} {p q u : Idx} (hp : p ∈ B₁) (hpu : p - u ∈ B₂)
    (h : p = q) : (p, q, u) ∈ S9_sp B₁ B₂ := by
  unfold S9_sp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product]
  refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(p, p - u), ⟨hp, hpu⟩, ?_⟩))))
  subst h
  simp

private lemma S9_mem_sp2 {B₁ B₂ : Finset Idx} {p q u : Idx} (hp : p ∈ B₁) (hpu : p - u ∈ B₂)
    (h : p - u = q + u) : (p, q, u) ∈ S9_sp B₁ B₂ := by
  unfold S9_sp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product]
  refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(p, p - u), ⟨hp, hpu⟩, ?_⟩))))
  simp only [Prod.mk.injEq, true_and, sub_sub_cancel]
  refine ⟨?_, trivial⟩
  funext i
  have := congr_fun h i
  simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
  omega

private lemma S9_mem_sp3 {B₁ B₂ : Finset Idx} {p q u : Idx} (hp : p ∈ B₁) (hq : q ∈ B₂)
    (h : p = -(p - u)) : (p, q, u) ∈ S9_sp B₁ B₂ := by
  unfold S9_sp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product]
  refine Or.inl (Or.inl (Or.inl (Or.inr ⟨(p, q), ⟨hp, hq⟩, ?_⟩)))
  simp only [Prod.mk.injEq, true_and]
  funext i
  have := congr_fun h i
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this ⊢
  omega

private lemma S9_mem_sp4 {B₁ B₂ : Finset Idx} {p q u : Idx} (hp : p ∈ B₁) (hq : q ∈ B₂)
    (h : p = -(q + u)) : (p, q, u) ∈ S9_sp B₁ B₂ := by
  unfold S9_sp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product]
  refine Or.inl (Or.inl (Or.inr ⟨(p, q), ⟨hp, hq⟩, ?_⟩))
  simp only [Prod.mk.injEq, true_and]
  funext i
  have := congr_fun h i
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this ⊢
  omega

private lemma S9_mem_sp5 {B₁ B₂ : Finset Idx} {p q u : Idx} (hp : p ∈ B₁) (hq : q ∈ B₂)
    (h : q = -(p - u)) : (p, q, u) ∈ S9_sp B₁ B₂ := by
  unfold S9_sp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product]
  refine Or.inl (Or.inr ⟨(p, q), ⟨hp, hq⟩, ?_⟩)
  simp only [Prod.mk.injEq, true_and]
  funext i
  have := congr_fun h i
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this ⊢
  omega

private lemma S9_mem_sp6 {B₁ B₂ : Finset Idx} {p q u : Idx} (hp : p ∈ B₁) (hq : q ∈ B₂)
    (h : q = -(q + u)) : (p, q, u) ∈ S9_sp B₁ B₂ := by
  unfold S9_sp
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_product]
  refine Or.inr ⟨(p, q), ⟨hp, hq⟩, ?_⟩
  simp only [Prod.mk.injEq, true_and]
  funext i
  have := congr_fun h i
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this ⊢
  omega

/-! ### Assembly of a class sum -/

/-- The sum over a class: reduction, splitting into generic and special tuples. -/
private lemma S9_assemble (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {c : FourLegs.Cls}
    (hc : c = .one ∨ c = .two ∨ c = .twoAdj ∨ c = .three) {V₀ : ℝ}
    (hV₀ : ∀ k, ‖ft V k‖ ≤ V₀) (hV₀0 : 0 ≤ V₀) (S Ssp : Finset (Idx × Idx × Idx))
    (hS : ∀ x : Idx × Idx × Idx, c.mem (rhoN N) (LN N) kc N (x.1, x.2.1, x.2.2, 0) →
      Decomp.Part.A2.mem x.1 x.2.1 x.2.2 → x ∈ S) {Bg Bs : ℝ} (hBg : 0 ≤ Bg) (hBs : 0 ≤ Bs)
    (hg : ∀ x ∈ S, (c.mem (rhoN N) (LN N) kc N (x.1, x.2.1, x.2.2, 0) ∧
        Decomp.Part.A2.mem x.1 x.2.1 x.2.2) → FourLegs.Gen (FourLegs.legs x.1 x.2.1 x.2.2) →
        S9_T (trialState V w kc N) x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) ≤ Bg)
    (hs : ∀ x ∈ S, (c.mem (rhoN N) (LN N) kc N (x.1, x.2.1, x.2.2, 0) ∧
        Decomp.Part.A2.mem x.1 x.2.1 x.2.2) →
        S9_T (trialState V w kc N) x.1 x.2.1 (x.1 - x.2.2) (x.2.1 + x.2.2) ≤ Bs)
    (hsp : ∀ x ∈ S, (c.mem (rhoN N) (LN N) kc N (x.1, x.2.1, x.2.2, 0) ∧
        Decomp.Part.A2.mem x.1 x.2.1 x.2.2) → ¬ FourLegs.Gen (FourLegs.legs x.1 x.2.1 x.2.2) →
        x ∈ Ssp) :
    FourLegs.absPart V w c kc N ≤
      V₀ / ((LN N ^ 3) ^ 2 * rhoN N ^ (5 / 2 : ℝ)) * (S.card * Bg + Ssp.card * Bs) := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  refine (S9_reduce V w kc hN hc hV₀ S hS).trans ?_
  have hpos : 0 ≤ V₀ / ((LN N ^ 3) ^ 2 * rhoN N ^ (5 / 2 : ℝ)) := by
    have : 0 < rhoN N ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
    positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  exact S9_sum_split S Ssp _ _ _ hBg hBs hg hs hsp

/-- `V₀ ≥ ‖V_k‖`. -/
private lemma S9_V0 {V : R3 → ℝ} (hV : PotentialHyp V) :
    ∃ V₀ : ℝ, 0 ≤ V₀ ∧ ∀ k, ‖ft V k‖ ≤ V₀ := by
  obtain ⟨C, hC⟩ := scat_ft_V_decay hV 0
  refine ⟨C, le_trans (norm_nonneg _) (by simpa using hC 0), fun k => ?_⟩
  simpa using hC k

/-- `D_j` in closed form. -/
private lemma S9_D_eq (V w : R3 → ℝ) {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    S9_D V w N j = (2 / (g0 V w * epsP (rhoN N) ^ 12)) ^ 2 / (N : ℝ) ^ j := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have ht := S9_eps_pos hρ
  have hK : rhoN N ^ (-(1 / 10 : ℝ)) = (epsP (rhoN N) ^ 20)⁻¹ :=
    S9_rpow_eps_neg hρ.le 20 (by norm_num)
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  unfold S9_D
  rw [hK]
  generalize epsP (rhoN N) = t at ht hr ⊢
  rw [hr]
  by_cases hg : g0 V w = 0
  · simp [hg]
  have hNj : (N : ℝ) ^ j ≠ 0 := by
    have : (N : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    exact pow_ne_zero _ this
  field_simp

/-! ### Class 1: the rate `ρ^{2/5}` -/

/-- `ρ`, `|Λ|` and `N` as powers of `ε`, and the closed forms of `D₀`, `D₂`:
the bound of the generic tuples of class 1. -/
private lemma S9_arith1 (V w : R3 → ℝ) {C : ℝ} {N : ℕ} (E : S9_Env V w C N) :
    (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * (Real.sqrt (S9_D V w N 2) +
        Real.sqrt (S9_D V w N 0) * (6 * (C * rhoN N * mc (rhoN N) / epsP (rhoN N)) ^ 2)) +
      (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * Real.sqrt (S9_D V w N 2) ≤
    (16 + 48 * C ^ 2) / g0 V w * epsP (rhoN N) ^ 382 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have ht1 := S9_eps_le_one hρ hρ1
  have hg := E.hg
  have hm := S9_ceil_le hρ hρ1
  have hm0 : (0 : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := Nat.cast_nonneg _
  have hN425 := S9_Nt E.hN
  have hmc := S9_mc_eq hρ
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  have hD2 := S9_D_eq V w E.hN 2
  have hD0 := S9_D_eq V w E.hN 0
  generalize (⌈mc (rhoN N)⌉₊ : ℝ) = m at hm hm0 ⊢
  rw [hD2, hD0, hmc]
  generalize epsP (rhoN N) = t at ht ht1 hm hN425 hr ⊢
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast E.hN
  generalize (N : ℝ) = n at hN425 hN1 ⊢
  have hn0 : 0 < n := by linarith
  have hs0 : 0 < 2 / (g0 V w * t ^ 12) := by positivity
  have e2 : Real.sqrt ((2 / (g0 V w * t ^ 12)) ^ 2 / n ^ 2) = 2 / (g0 V w * t ^ 12) * t ^ 425 := by
    rw [← div_pow, Real.sqrt_sq (by positivity)]
    have : 1 / n = t ^ 425 := by
      field_simp; linarith
    rw [div_eq_mul_one_div, this]
  have e0 : Real.sqrt ((2 / (g0 V w * t ^ 12)) ^ 2 / n ^ 0) = 2 / (g0 V w * t ^ 12) := by
    simp only [pow_zero, div_one]
    exact Real.sqrt_sq hs0.le
  rw [e2, e0, hr]
  have hm2 : m ^ 2 ≤ (2 * t⁻¹) ^ 2 := pow_le_pow_left₀ hm0 hm 2
  have hX : 0 ≤ 2 / (g0 V w * t ^ 12) * t ^ 425 + 2 / (g0 V w * t ^ 12) *
      (6 * (C * t ^ 200 * t⁻¹ / t) ^ 2) := by positivity
  have hY : 0 ≤ 2 / (g0 V w * t ^ 12) * t ^ 425 := by positivity
  calc m ^ 2 * (2 / (g0 V w * t ^ 12) * t ^ 425 + 2 / (g0 V w * t ^ 12) *
        (6 * (C * t ^ 200 * t⁻¹ / t) ^ 2)) + m ^ 2 * (2 / (g0 V w * t ^ 12) * t ^ 425)
      ≤ (2 * t⁻¹) ^ 2 * (2 / (g0 V w * t ^ 12) * t ^ 425 + 2 / (g0 V w * t ^ 12) *
        (6 * (C * t ^ 200 * t⁻¹ / t) ^ 2)) + (2 * t⁻¹) ^ 2 * (2 / (g0 V w * t ^ 12) * t ^ 425) := by
        gcongr
    _ = 16 / g0 V w * t ^ 411 + 48 * C ^ 2 / g0 V w * t ^ 382 := by
        field_simp
        ring
    _ ≤ (16 + 48 * C ^ 2) / g0 V w * t ^ 382 := by
        have h1 : t ^ 411 ≤ t ^ 382 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
        have h2 : 0 ≤ 16 / g0 V w := by positivity
        calc 16 / g0 V w * t ^ 411 + 48 * C ^ 2 / g0 V w * t ^ 382
            ≤ 16 / g0 V w * t ^ 382 + 48 * C ^ 2 / g0 V w * t ^ 382 := by gcongr
          _ = _ := by ring


/-- `V₀ / (|Λ|² ρ^{5/2}) = V₀ ε^{750}`. -/
private lemma S9_pref {N : ℕ} (hN : 1 ≤ N) (V₀ : ℝ) :
    V₀ / ((LN N ^ 3) ^ 2 * rhoN N ^ (5 / 2 : ℝ)) = V₀ * epsP (rhoN N) ^ 750 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have h1 := S9_L3 hN
  have h2 : rhoN N ^ (5 / 2 : ℝ) = epsP (rhoN N) ^ 500 := S9_rpow_eps hρ.le 500 (by norm_num)
  have ht := S9_eps_pos hρ
  have h3 : (LN N ^ 3) ^ 2 * rhoN N ^ (5 / 2 : ℝ) * epsP (rhoN N) ^ 750 = 1 := by
    rw [h2]
    calc (LN N ^ 3) ^ 2 * epsP (rhoN N) ^ 500 * epsP (rhoN N) ^ 750
        = (LN N ^ 3 * epsP (rhoN N) ^ 625) ^ 2 := by ring
      _ = 1 := by rw [h1]; norm_num
  have h4 : 0 < (LN N ^ 3) ^ 2 * rhoN N ^ (5 / 2 : ℝ) := by
    have := Particles_rhoN_LN hN
    have : 0 < rhoN N ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hρ _
    have : 0 < LN N := (Particles_rhoN_LN hN).2.2.2
    positivity
  rw [div_eq_iff h4.ne']
  calc V₀ = V₀ * ((LN N ^ 3) ^ 2 * rhoN N ^ (5 / 2 : ℝ) * epsP (rhoN N) ^ 750) := by
        rw [h3]; ring
    _ = _ := by ring

/-- Class 1 (case 1 of Lemma 9.1 [fourlegslemma1]): the rate `ε^{80} = ρ^{2/5}`. -/
private lemma S9_class1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      FourLegs.absPart V w .one kc N ≤ C' * epsP (rhoN N) ^ 80 := by
  obtain ⟨V₀, hV₀0, hV₀⟩ := S9_V0 hV
  obtain ⟨C, hC, hev⟩ := S9_env hV hw
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  have hg := scat_g0_pos hV hw
  refine ⟨V₀ * (67 ^ 3 * ((16 + 48 * C ^ 2) / g0 V w) + 6 * 67 ^ 2 * 4), by positivity, N₀,
    fun N hN kc => ?_⟩
  have E := hN₀ N hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have ht1 := S9_eps_le_one hρ hρ1
  set B := S9_ball (LN N) ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) with hB
  have hBmem : ∀ n, inPL (rhoN N) (LN N) n → n ∈ B := fun n hn => S9_mem_ball hL hn.2
  set S₁ := (B ×ˢ B ×ˢ B).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2)) with hS₁
  have hS : ∀ x : Idx × Idx × Idx, FourLegs.Cls.mem (rhoN N) (LN N) kc N .one
      (x.1, x.2.1, x.2.2, 0) → Decomp.Part.A2.mem x.1 x.2.1 x.2.2 → x ∈ S₁ := by
    rintro ⟨p, q, u⟩ hm -
    obtain ⟨hp, hq, hpu, hqu⟩ := (S9_forall_legs (P := inPL (rhoN N) (LN N)) p q u).1 hm
    rw [hS₁, Finset.mem_image]
    refine ⟨(p, q, p - u), ?_, by simp⟩
    simp only [Finset.mem_product]
    exact ⟨hBmem _ hp, hBmem _ hq, hBmem _ hpu⟩
  have hlegs : ∀ x : Idx × Idx × Idx, FourLegs.Cls.mem (rhoN N) (LN N) kc N .one
      (x.1, x.2.1, x.2.2, 0) → inPL (rhoN N) (LN N) x.1 ∧ inPL (rhoN N) (LN N) x.2.1 ∧
        inPL (rhoN N) (LN N) (x.1 - x.2.2) ∧ inPL (rhoN N) (LN N) (x.2.1 + x.2.2) := fun x hm =>
    (S9_forall_legs (P := inPL (rhoN N) (LN N)) x.1 x.2.1 x.2.2).1 hm
  have hm0 : (0 : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 := by positivity
  have hBg0 : 0 ≤ (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * (Real.sqrt (S9_D V w N 2) +
        Real.sqrt (S9_D V w N 0) * (6 * (C * rhoN N * mc (rhoN N) / epsP (rhoN N)) ^ 2)) +
      (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * Real.sqrt (S9_D V w N 2) := by positivity
  have hmain := S9_assemble V w kc E.hN (c := .one) (Or.inl rfl) hV₀ hV₀0 S₁ (S9_sp B B) hS
    hBg0 hm0
    (fun x _ hP hGen => by
      obtain ⟨h1, h2, h3, h4⟩ := hlegs x hP.1
      exact S9_gen1 E kc h1 h2 h3 h4 hGen)
    (fun x _ hP => by
      obtain ⟨h1, h2, h3, h4⟩ := hlegs x hP.1
      exact S9_spec1 E kc h1 h2 h3 h4)
    (by
      rintro ⟨p, q, u⟩ - hP hGen
      obtain ⟨hp, hq, hpu, hqu⟩ := hlegs _ hP.1
      simp only at hp hq hpu hqu
      rcases S9_not_gen hP.2 hGen with h | h | h | h | h | h
      · exact S9_mem_sp1 (hBmem _ hp) (hBmem _ hpu) h
      · exact S9_mem_sp2 (hBmem _ hp) (hBmem _ hpu) h
      · exact S9_mem_sp3 (hBmem _ hp) (hBmem _ hq) h
      · exact S9_mem_sp4 (hBmem _ hp) (hBmem _ hq) h
      · exact S9_mem_sp5 (hBmem _ hp) (hBmem _ hq) h
      · exact S9_mem_sp6 (hBmem _ hp) (hBmem _ hq) h)
  refine hmain.trans ?_
  rw [S9_pref E.hN V₀]
  -- the closing arithmetic
  have hcardB := S9_card_PL E.hN
  have hcardB' : (B.card : ℝ) ≤ 67 * (LN N ^ 3 * epsP (rhoN N) ^ 297) := hcardB
  have hnS : (S₁.card : ℝ) ≤ (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 3 := by
    have h1 : S₁.card ≤ B.card * (B.card * B.card) :=
      Finset.card_image_le.trans (by simp [Finset.card_product])
    calc (S₁.card : ℝ) ≤ (B.card : ℝ) * ((B.card : ℝ) * B.card) := by exact_mod_cast h1
      _ = (B.card : ℝ) ^ 3 := by ring
      _ ≤ _ := pow_le_pow_left₀ (Nat.cast_nonneg _) hcardB' 3
  have hnT : ((S9_sp B B).card : ℝ) ≤ 6 * (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 2 := by
    calc ((S9_sp B B).card : ℝ) ≤ 6 * ((B.card : ℝ) * B.card) := S9_sp_card B B
      _ = 6 * (B.card : ℝ) ^ 2 := by ring
      _ ≤ _ := by gcongr
  have hL3 := S9_L3 E.hN
  have hnS' : (S₁.card : ℝ) * epsP (rhoN N) ^ 984 ≤ 67 ^ 3 := by
    calc (S₁.card : ℝ) * epsP (rhoN N) ^ 984
        ≤ (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 3 * epsP (rhoN N) ^ 984 := by gcongr
      _ = 67 ^ 3 * (LN N ^ 3 * epsP (rhoN N) ^ 625) ^ 3 := by ring
      _ = 67 ^ 3 := by rw [hL3]; norm_num
  have hnT' : ((S9_sp B B).card : ℝ) * epsP (rhoN N) ^ 656 ≤ 6 * 67 ^ 2 := by
    calc ((S9_sp B B).card : ℝ) * epsP (rhoN N) ^ 656
        ≤ 6 * (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 2 * epsP (rhoN N) ^ 656 := by gcongr
      _ = 6 * 67 ^ 2 * (LN N ^ 3 * epsP (rhoN N) ^ 625) ^ 2 := by ring
      _ = 6 * 67 ^ 2 := by rw [hL3]; norm_num
  have hBg' := S9_arith1 V w E
  have hmc := S9_ceil_le hρ hρ1
  have hBs' : (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * epsP (rhoN N) ^ 2 ≤ 4 := by
    have h0 : (0 : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := Nat.cast_nonneg _
    calc (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 * epsP (rhoN N) ^ 2
        ≤ (2 * (epsP (rhoN N))⁻¹) ^ 2 * epsP (rhoN N) ^ 2 := by gcongr
      _ = 4 := by field_simp; norm_num
  have hcl := S9_close (t := epsP (rhoN N)) (V₀ := V₀) (P := 750) (a := 984) (b := 656) (e := 382)
    (f := 2) (f' := 0) (k := 80) (cs := 4) (cS := 67 ^ 3) (cT := 6 * 67 ^ 2) ht ht1 hV₀0 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by positivity) (by positivity) (by positivity) (by positivity) hnS' hnT' hBg'
    (by simpa using hBs') (by norm_num) (by norm_num)
  refine hcl.trans ?_
  have : V₀ * (67 ^ 3 * ((16 + 48 * C ^ 2) / g0 V w) + 6 * 67 ^ 2 * 4) * epsP (rhoN N) ^ 80 =
      V₀ * (67 ^ 3 * ((16 + 48 * C ^ 2) / g0 V w) + 6 * 67 ^ 2 * 4) * epsP (rhoN N) ^ 80 := rfl
  exact le_rfl

/-! ### Regions, symmetries of the four-leg coefficient -/

private lemma S9_mom_add (L : ℝ) (u v : Idx) : mom L (u + v) = mom L u + mom L v := by
  ext i
  simp [mom, mul_add]

private lemma S9_mom_sub (L : ℝ) (v u : Idx) : mom L (v - u) = mom L v - mom L u := by
  ext i
  simp [mom, mul_sub]

/-- `P_L` lies in the ball of radius `ε`. -/
private lemma S9_PL_norm_le {ρ L : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {n : Idx} (hn : inPL ρ L n) :
    ‖mom L n‖ ≤ epsP ρ := by
  have h1 := hn.2
  have ht := S9_eps_pos hρ
  have h2 : ρ ^ (1 / 2 : ℝ) ≤ epsP ρ ^ 2 := by
    have : epsP ρ ^ 2 = ρ ^ (1 / 100 : ℝ) := by
      rw [← S9_rpow_eps hρ.le 2 (x := 1 / 100) (by norm_num)]
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_ge hρ hρ1 (by norm_num)
  calc ‖mom L n‖ ≤ (epsP ρ)⁻¹ * ρ ^ (1 / 2 : ℝ) := h1
    _ ≤ (epsP ρ)⁻¹ * epsP ρ ^ 2 := mul_le_mul_of_nonneg_left h2 (inv_pos.2 ht).le
    _ = epsP ρ := by field_simp

/-- A point of `P_H` is not half the sum or difference of two points of `P_L`. -/
private lemma S9_no_double {ρ L : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {a b c : Idx}
    (ha : inPL ρ L a) (hb : inPL ρ L b) (hc : inPH ρ L c) :
    c + c ≠ a + b ∧ c + c ≠ a - b ∧ c + c ≠ b - a := by
  have h1 := S9_PL_norm_le hρ hρ1 ha
  have h2 := S9_PL_norm_le hρ hρ1 hb
  have h3 : epsP ρ < ‖mom L c‖ := hc
  have e : ‖mom L (c + c)‖ = 2 * ‖mom L c‖ := by
    rw [S9_mom_add, ← two_smul ℝ (mom L c), norm_smul]
    simp
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := norm_add_le (mom L a) (mom L b)
    rw [← S9_mom_add, ← h, e] at this
    linarith
  · have := norm_sub_le (mom L a) (mom L b)
    rw [← S9_mom_sub, ← h, e] at this
    linarith
  · have := norm_sub_le (mom L b) (mom L a)
    rw [← S9_mom_sub, ← h, e] at this
    linarith

/-- A point of `P_L` is neither equal to nor the negative of a point of `P_H`. -/
private lemma S9_PL_PH_ne {ρ L : ℝ} (hρ : 0 < ρ) {a b : Idx} (ha : inPL ρ L a)
    (hb : inPH ρ L b) : a ≠ b ∧ a ≠ -b := by
  refine ⟨fun h => Regions_PL_PH hρ ha (h ▸ hb), fun h => Regions_PL_PH hρ ha ?_⟩
  rw [h]
  exact Regions_PH_neg.2 hb

/-- The four-leg condition. -/
private def S9_Gen4 (a b c d : Idx) : Prop :=
  ∀ i j : Fin 4, i ≠ j → Legs_pm (![a, b, c, d] i) (![a, b, c, d] j)

private lemma S9_Gen4_iff (a b c d : Idx) : S9_Gen4 a b c d ↔
    Legs_pm a b ∧ Legs_pm a c ∧ Legs_pm a d ∧ Legs_pm b c ∧ Legs_pm b d ∧ Legs_pm c d := by
  constructor
  · intro h
    exact ⟨h 0 1 (by decide), h 0 2 (by decide), h 0 3 (by decide), h 1 2 (by decide),
      h 1 3 (by decide), h 2 3 (by decide)⟩
  · rintro ⟨h12, h13, h14, h23, h24, h34⟩ i j hij
    fin_cases i <;> fin_cases j <;> first
      | (exfalso; exact hij rfl)
      | exact h12 | exact h13 | exact h14 | exact h23 | exact h24 | exact h34
      | exact S9_pm_symm h12 | exact S9_pm_symm h13 | exact S9_pm_symm h14
      | exact S9_pm_symm h23 | exact S9_pm_symm h24 | exact S9_pm_symm h34

private lemma S9_Gen4_adj {a b c d : Idx} (h : S9_Gen4 a b c d) : S9_Gen4 d c b a := by
  rw [S9_Gen4_iff] at h ⊢
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := h
  exact ⟨S9_pm_symm h34, S9_pm_symm h24, S9_pm_symm h14, S9_pm_symm h23, S9_pm_symm h13,
    S9_pm_symm h12⟩

private lemma S9_Gen4_swap12 {a b c d : Idx} (h : S9_Gen4 a b c d) : S9_Gen4 b a c d := by
  rw [S9_Gen4_iff] at h ⊢
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := h
  exact ⟨S9_pm_symm h12, h23, h24, h13, h14, h34⟩

private lemma S9_Gen4_swap34 {a b c d : Idx} (h : S9_Gen4 a b c d) : S9_Gen4 a b d c := by
  rw [S9_Gen4_iff] at h ⊢
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := h
  exact ⟨h12, h14, h13, h24, h23, S9_pm_symm h34⟩

/-- `a†_p a†_q = a†_q a†_p`. -/
private lemma S9_a4_swap_bra (p q r s : Idx) (α : Occ) :
    a4 p q r s α = a4 q p r s α := by
  by_cases hpq : p = q
  · subst hpq; rfl
  simp only [a4]
  refine Prod.ext ?_ ?_
  · simp only [Finsupp.add_apply, Finsupp.single_apply, hpq, Ne.symm hpq, ite_true, ite_false,
      add_zero]
    ring
  · simp only
    rw [add_right_comm]

/-- `a_r a_s = a_s a_r`. -/
private lemma S9_a4_swap_ket (p q r s : Idx) (α : Occ) :
    a4 p q r s α = a4 p q s r α := by
  by_cases hrs : r = s
  · subst hrs; rfl
  simp only [a4]
  have h2 : α - Finsupp.single s 1 - Finsupp.single r 1 =
      α - Finsupp.single r 1 - Finsupp.single s 1 := tsub_right_comm
  rw [h2]
  refine Prod.ext ?_ rfl
  simp only [Finsupp.tsub_apply, Finsupp.single_apply, hrs, Ne.symm hrs, ite_false,
    tsub_zero]
  ring


private lemma S9_T_swap12 (Ψ : Occ → ℂ) (a b c d : Idx) :
    S9_T Ψ a b c d = S9_T Ψ b a c d := by
  unfold S9_T S9_s
  simp only [S9_a4_swap_bra a b c d]

private lemma S9_T_swap34 (Ψ : Occ → ℂ) (a b c d : Idx) :
    S9_T Ψ a b c d = S9_T Ψ a b d c := by
  unfold S9_T S9_s
  simp only [S9_a4_swap_ket a b c d]

/-- The adjoint: `T(v₁,v₂,v₃,v₄) ≤ T(v₄,v₃,v₂,v₁)`. -/
private lemma S9_T_adj_le {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (a b c d : Idx) :
    S9_T Ψ a b c d ≤ S9_T Ψ d c b a := by
  have h := S9_T_le hΨ a b c d (S9_s Ψ d c b a) (fun _ => 0) (fun β => S9_s_nonneg _ _ _ _ _ _)
    (fun _ => le_rfl) (S9_s_summable hΨ d c b a) summable_zero (fun κ hκ => by
      have := a4_adjoint a b c d κ hκ
      rw [S9_s_eq Ψ d c b a, this, S9_s_eq]
      simp only [add_zero]
      ring_nf
      exact le_rfl)
  simpa [S9_T] using h

/-! ### Weighted sums against `|Ψ|²` -/

private lemma S9_Q1_eq (Ψ : Occ → ℂ) (u : Idx) :
    Expect.Q Ψ [u] = ∑' α : Occ, (α u : ℝ) * ‖Ψ α‖ ^ 2 := by
  simp [Expect.Q]

private lemma S9_Q2_eq (Ψ : Occ → ℂ) (u v : Idx) :
    Expect.Q Ψ [u, v] = ∑' α : Occ, (α u : ℝ) * α v * ‖Ψ α‖ ^ 2 := by
  simp [Expect.Q]

/-- `Σ (α(u) + 1)(α(v) + 1)|Ψ(α)|² = 1 + Q(u) + Q(v) + Q(u, v)`. -/
private lemma S9_sum_succ2 {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (u v : Idx) :
    ∑' α : Occ, (((α u : ℝ) + 1) * ((α v : ℝ) + 1)) * ‖Ψ α‖ ^ 2 =
      1 + Expect.Q Ψ [u] + Expect.Q Ψ [v] + Expect.Q Ψ [u, v] := by
  have hs : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have bd : ∀ (f : Occ → ℝ) (B : ℝ), (∀ α, Ψ α ≠ 0 → |f α| ≤ B) →
      Summable fun α : Occ => f α * ‖Ψ α‖ ^ 2 := fun f B h => S9_summable_w hΨ f B h
  have h1 : Summable fun α : Occ => (α u : ℝ) * ‖Ψ α‖ ^ 2 := bd _ N (fun α h => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hΨ h u)
  have h2 : Summable fun α : Occ => (α v : ℝ) * ‖Ψ α‖ ^ 2 := bd _ N (fun α h => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hΨ h v)
  have h3 : Summable fun α : Occ => (α u : ℝ) * α v * ‖Ψ α‖ ^ 2 := bd _ (N * N) (fun α h => by
    rw [abs_of_nonneg (by positivity)]
    have a := S9_occ_le hΨ h u
    have b := S9_occ_le hΨ h v
    have : (α u : ℝ) ≤ N := by exact_mod_cast a
    have : (α v : ℝ) ≤ N := by exact_mod_cast b
    gcongr)
  have e : ∀ α : Occ, (((α u : ℝ) + 1) * ((α v : ℝ) + 1)) * ‖Ψ α‖ ^ 2 =
      (‖Ψ α‖ ^ 2 + (α u : ℝ) * ‖Ψ α‖ ^ 2) + ((α v : ℝ) * ‖Ψ α‖ ^ 2 +
        (α u : ℝ) * α v * ‖Ψ α‖ ^ 2) := fun α => by ring
  simp_rw [e]
  rw [Summable.tsum_add (hs.add h1) (h2.add h3), Summable.tsum_add hs h1,
    Summable.tsum_add h2 h3, hΨ.1.tsum_eq, S9_Q1_eq, S9_Q1_eq, S9_Q2_eq]
  ring

/-- `Σ α(u) (α(v) + 1)|Ψ(α)|² = Q(u, v) + Q(u)`. -/
private lemma S9_sum_succ1 {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (u v : Idx) :
    ∑' α : Occ, ((α u : ℝ) * ((α v : ℝ) + 1)) * ‖Ψ α‖ ^ 2 =
      Expect.Q Ψ [u, v] + Expect.Q Ψ [u] := by
  have bd : ∀ (f : Occ → ℝ) (B : ℝ), (∀ α, Ψ α ≠ 0 → |f α| ≤ B) →
      Summable fun α : Occ => f α * ‖Ψ α‖ ^ 2 := fun f B h => S9_summable_w hΨ f B h
  have h1 : Summable fun α : Occ => (α u : ℝ) * ‖Ψ α‖ ^ 2 := bd _ N (fun α h => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hΨ h u)
  have h3 : Summable fun α : Occ => (α u : ℝ) * α v * ‖Ψ α‖ ^ 2 := bd _ (N * N) (fun α h => by
    rw [abs_of_nonneg (by positivity)]
    have a := S9_occ_le hΨ h u
    have b := S9_occ_le hΨ h v
    have : (α u : ℝ) ≤ N := by exact_mod_cast a
    have : (α v : ℝ) ≤ N := by exact_mod_cast b
    gcongr)
  have e : ∀ α : Occ, ((α u : ℝ) * ((α v : ℝ) + 1)) * ‖Ψ α‖ ^ 2 =
      (α u : ℝ) * α v * ‖Ψ α‖ ^ 2 + (α u : ℝ) * ‖Ψ α‖ ^ 2 := fun α => by ring
  simp_rw [e]
  rw [Summable.tsum_add h3 h1, S9_Q1_eq, S9_Q2_eq]

/-! ### Class 2: `v₁, v₂ ∈ P_L`, `v₃, v₄ ∈ P_{H,c}` -/

/-- `K B₁ / (N² A₀)` with `B₁ = (g₀/ε²)²`: the constant of the bra form of class 2. -/
private def S9_Dp (V w : R3 → ℝ) (N : ℕ) : ℝ :=
  rhoN N ^ (-(1 / 10 : ℝ)) * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 /
    ((N : ℝ) ^ 2 * (g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) ^ 2)

private lemma S9_Dp_nonneg (V w : R3 → ℝ) (N : ℕ) : 0 ≤ S9_Dp V w N := by
  unfold S9_Dp
  have : 0 ≤ rhoN N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg (by unfold rhoN; positivity) _
  positivity

/-- The constant of the ket form of class 2. -/
private def S9_theta (V w : R3 → ℝ) (N : ℕ) (v₃ v₄ : Idx) : ℝ :=
  Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2 /
    |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|)

private lemma S9_theta_nonneg (V w : R3 → ℝ) (N : ℕ) (v₃ v₄ : Idx) :
    0 ≤ S9_theta V w N v₃ v₄ := Real.sqrt_nonneg _

/-- Class 2: the pointwise bound for a nonzero matrix element between two `M` states. -/
private lemma S9_pt2 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPH (rhoN N) (LN N) v₃) (h₄ : inPH (rhoN N) (LN N) v₄)
    (hGen : S9_Gen4 v₁ v₂ v₃ v₄) (κ : Occ) (hc : (a4 v₁ v₂ v₃ v₄ κ).1 ≠ 0) :
    S9_s (trialState V w kc N) v₁ v₂ v₃ v₄ κ ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_Dp V w N) *
          ((((a4 v₁ v₂ v₃ v₄ κ).2 v₃ : ℝ) + 1) * (((a4 v₁ v₂ v₃ v₄ κ).2 v₄ : ℝ) + 1)) *
          ‖trialState V w kc N (a4 v₁ v₂ v₃ v₄ κ).2‖ ^ 2 +
        (⌈mc (rhoN N)⌉₊ : ℝ) * S9_theta V w N v₃ v₄ * ((κ v₃ : ℝ) * κ v₄) *
          ‖trialState V w kc N κ‖ ^ 2 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  set Ψ := trialState V w kc N with hΨ
  set b := (a4 v₁ v₂ v₃ v₄ κ).2 with hb
  set c := (a4 v₁ v₂ v₃ v₄ κ).1 with hcdef
  set m : ℝ := (⌈mc (rhoN N)⌉₊ : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hxn : 0 ≤ ‖Ψ κ‖ ^ 2 := by positivity
  have hyn : 0 ≤ ‖Ψ b‖ ^ 2 := by positivity
  have hDp := Real.sqrt_nonneg (S9_Dp V w N)
  have hθ := S9_theta_nonneg V w N v₃ v₄
  have hbn : 0 ≤ ((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1) := by positivity
  have hkn : 0 ≤ (κ v₃ : ℝ) * κ v₄ := by positivity
  have hR0 : 0 ≤ m * Real.sqrt (S9_Dp V w N) * (((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1)) *
      ‖Ψ b‖ ^ 2 + m * S9_theta V w N v₃ v₄ * ((κ v₃ : ℝ) * κ v₄) * ‖Ψ κ‖ ^ 2 := by positivity
  by_cases hΨκ : Ψ κ = 0
  · have : S9_s Ψ v₁ v₂ v₃ v₄ κ = 0 := by rw [S9_s_eq, hΨκ]; simp
    rw [this]; exact hR0
  by_cases hΨb : Ψ b = 0
  · have : S9_s Ψ v₁ v₂ v₃ v₄ κ = 0 := by rw [S9_s_eq, hΨb]; simp
    rw [this]; exact hR0
  have hκM : InM (rhoN N) (LN N) kc N κ := S9_inM hΨκ
  have hbM : InM (rhoN N) (LN N) kc N b := S9_inM hΨb
  have hn3 : ¬ inPL (rhoN N) (LN N) v₃ := fun h => Regions_PL_PH hρ h h₃
  have hn4 : ¬ inPL (rhoN N) (LN N) v₄ := fun h => Regions_PL_PH hρ h h₄
  have h0 : ∀ i : Fin 4, ![v₁, v₂, v₃, v₄] i ≠ 0 := by
    intro i
    fin_cases i
    exacts [Regions_PL_ne_zero hρ h₁, Regions_PL_ne_zero hρ h₂, Regions_PH_ne_zero hρ h₃,
      Regions_PH_ne_zero hρ h₄]
  have hF := Lemma9_1_F hρ h0 hGen hbM hκM hc rfl
  rw [S9_card4] at hF
  simp only [h₁, h₂, hn3, hn4, ite_true, ite_false] at hF
  have hrat : ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ *
        (‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b *
        (‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|)) ∧
      ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b *
        (‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ *
        (‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|)) :=
    E.hratio kc b κ ![v₁, v₂, v₃, v₄] h0 hGen hbM hκM hc rfl
  obtain ⟨p12, p13, p14, p23, p24, p34⟩ := (S9_Gen4_iff _ _ _ _).1 hGen
  obtain ⟨o1, o2, o3, o4, q3, q4, q1, q2, hsq⟩ :=
    S9_occ hc p12.1 p34.1 p13.1 p14.1 p23.1 p24.1
  have hc0 : 0 ≤ c := a4_fst_nonneg _ _ _ _ _
  have e1 : ((b v₁ : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (S9_occ_ceil hρ hbM h₁)
  have e2 : ((b v₂ : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (S9_occ_ceil hρ hbM h₂)
  have o3' : ((κ v₃ : ℕ) : ℝ) = (b v₃ : ℝ) + 1 := by exact_mod_cast o3
  have o4' : ((κ v₄ : ℕ) : ℝ) = (b v₄ : ℝ) + 1 := by exact_mod_cast o4
  have hk1 : (1 : ℝ) ≤ (κ v₃ : ℝ) * κ v₄ := by
    have a : (1 : ℝ) ≤ (κ v₃ : ℝ) := by exact_mod_cast q3
    have b' : (1 : ℝ) ≤ (κ v₄ : ℝ) := by exact_mod_cast q4
    nlinarith
  have hb1 : (0 : ℝ) ≤ (b v₁ : ℝ) * (b v₂ : ℝ) := by positivity
  have hb12 : (b v₁ : ℝ) * (b v₂ : ℝ) ≤ m * m := by gcongr
  -- the bounds on `c`
  have hcbra : c ≤ m * (((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1)) := by
    apply S9_c_le (by positivity)
    rw [hsq, o3', o4']
    have hW1 : (1 : ℝ) ≤ ((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1) := by
      have : (1 : ℝ) ≤ (b v₃ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (b v₃)]
      have : (1 : ℝ) ≤ (b v₄ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (b v₄)]
      nlinarith
    set W := ((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1) with hW
    calc ((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1) * (b v₁ : ℝ) * (b v₂ : ℝ)
        = W * ((b v₁ : ℝ) * (b v₂ : ℝ)) := by rw [hW]; ring
      _ ≤ W * (m * m) := by gcongr
      _ ≤ W * W * (m * m) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hW1)
            (mul_nonneg hm0 hm0)
      _ = (m * W) ^ 2 := by ring
  have hcket : c ≤ m * ((κ v₃ : ℝ) * κ v₄) := by
    apply S9_c_le (by positivity)
    rw [hsq]
    set W := (κ v₃ : ℝ) * κ v₄ with hW
    calc (κ v₃ : ℝ) * κ v₄ * (b v₁ : ℝ) * (b v₂ : ℝ)
        = W * ((b v₁ : ℝ) * (b v₂ : ℝ)) := by rw [hW]; ring
      _ ≤ W * (m * m) := by gcongr
      _ ≤ W * W * (m * m) :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by linarith) hk1)
            (mul_nonneg hm0 hm0)
      _ = (m * W) ^ 2 := by ring
  -- the bounds on `|λ|`
  have l1 := S9_lamPL E h₁
  have l2 := S9_lamPL E h₂
  have l3 := E.hlamH v₃ h₃
  have l4 := E.hlamH v₄ h₄
  have hℓ : 0 < g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹ := by
    have := S9_eps_pos hρ
    have := E.hg
    positivity
  have hℓ2 : 0 < (g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) ^ 2 := by positivity
  have hAlo : (g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹) ^ 2 ≤
      |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂| := by
    rw [abs_mul, sq]; exact mul_le_mul l1.1 l2.1 hℓ.le (abs_nonneg _)
  have hAhi : |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂| ≤ ((rhoN N)⁻¹) ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul l1.2 l2.2 (abs_nonneg _) (inv_pos.2 hρ).le
  have hBhi : |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| ≤
      (g0 V w / epsP (rhoN N) ^ 2) ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul l3 l4 (abs_nonneg _) (by have := E.hg; have := S9_eps_pos hρ; positivity)
  have hK : 0 ≤ rhoN N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hρ.le _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast E.hN
  have hspos : S9_s Ψ v₁ v₂ v₃ v₄ κ = ‖Ψ b‖ * c * ‖Ψ κ‖ := S9_s_eq _ _ _ _ _ _
  have hp : 0 ≤ ‖Ψ κ‖ := norm_nonneg _
  have hq : 0 ≤ ‖Ψ b‖ := norm_nonneg _
  have t1 : 0 ≤ m * S9_theta V w N v₃ v₄ * ((κ v₃ : ℝ) * κ v₄) * ‖Ψ κ‖ ^ 2 := by positivity
  have t2 : 0 ≤ m * Real.sqrt (S9_Dp V w N) *
      (((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1)) * ‖Ψ b‖ ^ 2 := by positivity
  rcases (by omega : Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b = 0 ∨
      1 ≤ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) with ha | ha
  · -- bra form
    have h1 := S9_pow_cancel hN1 (z := ‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ *
        lam V w (rhoN N) (LN N) v₂|) (z' := ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ *
        lam V w (rhoN N) (LN N) v₄|) (K := rhoN N ^ (-(1 / 10 : ℝ)))
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) 2
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ) (by positivity) (by omega)
      (by simpa only [mul_assoc] using hrat.1)
    have h2 := S9_amp_ratio (M := (N : ℝ) ^ 2) (by positivity) hℓ2 hxn hyn hAlo hBhi hK h1
    have h3 : ‖Ψ κ‖ * ‖Ψ b‖ ≤ Real.sqrt (S9_Dp V w N) * ‖Ψ b‖ ^ 2 :=
      S9_amp_sq hq (S9_Dp_nonneg V w N) (by unfold S9_Dp; exact h2)
    have h4 : S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ m * Real.sqrt (S9_Dp V w N) *
        (((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1)) * ‖Ψ b‖ ^ 2 := by
      rw [hspos]
      calc ‖Ψ b‖ * c * ‖Ψ κ‖ = c * (‖Ψ κ‖ * ‖Ψ b‖) := by ring
        _ ≤ (m * (((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1))) *
            (Real.sqrt (S9_Dp V w N) * ‖Ψ b‖ ^ 2) :=
          mul_le_mul hcbra h3 (by positivity) (by positivity)
        _ = _ := by ring
    linarith only [h4, t1]
  · -- ket form
    have hxpos : 0 < ‖Ψ κ‖ ^ 2 := by
      have : 0 < ‖Ψ κ‖ := norm_pos_iff.2 hΨκ
      positivity
    have hApos : 0 < |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂| :=
      lt_of_lt_of_le hℓ2 hAlo
    have hBpos : 0 < |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| := by
      have hr1 := hrat.1
      have hN0 : 0 < (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ := by positivity
      have h5 : 0 < (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ *
          (‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|) := by positivity
      have h6 := lt_of_lt_of_le h5 hr1
      by_contra hB0
      have : |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| = 0 :=
        le_antisymm (not_lt.1 hB0) (abs_nonneg _)
      rw [this] at h6
      simp at h6
    have h1 := S9_pow_cancel hN1 (z := ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ *
        lam V w (rhoN N) (LN N) v₄|) (z' := ‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ *
        lam V w (rhoN N) (LN N) v₂|) (K := rhoN N ^ (-(1 / 10 : ℝ)))
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ) 0
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) (by positivity) (by omega)
      (by simpa only [mul_assoc] using hrat.2)
    simp only [pow_zero, one_mul] at h1
    -- `y B ≤ K A x ≤ K ρ⁻² x`
    have h2 : ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| ≤
        rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2 * ‖Ψ κ‖ ^ 2 := by
      refine h1.trans ?_
      calc rhoN N ^ (-(1 / 10 : ℝ)) * (‖Ψ κ‖ ^ 2 *
            |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|)
          ≤ rhoN N ^ (-(1 / 10 : ℝ)) * (‖Ψ κ‖ ^ 2 * ((rhoN N)⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAhi hxn) hK
        _ = _ := by ring
    have h3 : ‖Ψ b‖ ^ 2 ≤ S9_theta V w N v₃ v₄ ^ 2 * ‖Ψ κ‖ ^ 2 := by
      unfold S9_theta
      rw [Real.sq_sqrt (by positivity), div_mul_eq_mul_div, le_div_iff₀ hBpos]
      exact h2
    have h4 : ‖Ψ b‖ * ‖Ψ κ‖ ≤ S9_theta V w N v₃ v₄ * ‖Ψ κ‖ ^ 2 := by
      have := S9_amp_sq (p := ‖Ψ b‖) (q := ‖Ψ κ‖) hp (sq_nonneg (S9_theta V w N v₃ v₄))
        (by simpa [mul_comm] using h3)
      rwa [Real.sqrt_sq hθ] at this
    have h5 : S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ m * S9_theta V w N v₃ v₄ * ((κ v₃ : ℝ) * κ v₄) *
        ‖Ψ κ‖ ^ 2 := by
      rw [hspos]
      calc ‖Ψ b‖ * c * ‖Ψ κ‖ = c * (‖Ψ b‖ * ‖Ψ κ‖) := by ring
        _ ≤ (m * ((κ v₃ : ℝ) * κ v₄)) * (S9_theta V w N v₃ v₄ * ‖Ψ κ‖ ^ 2) :=
          mul_le_mul hcket h4 (by positivity) (by positivity)
        _ = _ := by ring
    linarith only [h5, t2]


/-- `Q_Ψ(u) ≤ C ρ² (g₀/ε²) / ε²` on `P_H`, by (5.15) [ubpsiuroughPH]. -/
private lemma S9_Q1_bound {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {u : Idx} (hu : inPH (rhoN N) (LN N) u) :
    Expect.Q (trialState V w kc N) [u] ≤
      C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have h1 := E.hQ1 kc u hu
  have h2 := E.hlamH u hu
  have h3 : epsP (rhoN N) < ‖mom (LN N) u‖ := hu
  refine h1.trans ?_
  have h4 : epsP (rhoN N) ^ 2 ≤ ‖mom (LN N) u‖ ^ 2 := pow_le_pow_left₀ ht.le h3.le 2
  have h5 : C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| ≤
      C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  calc C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) u| / ‖mom (LN N) u‖ ^ 2
      ≤ C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / ‖mom (LN N) u‖ ^ 2 :=
        div_le_div_of_nonneg_right h5 (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by have := E.hg; positivity) (by positivity) h4

/-- Class 2, generic legs: the tuple sum. -/
private lemma S9_gen2 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPH (rhoN N) (LN N) v₃) (h₄ : inPH (rhoN N) (LN N) v₄)
    (hGen : S9_Gen4 v₁ v₂ v₃ v₄) :
    S9_T (trialState V w kc N) v₁ v₂ v₃ v₄ ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_Dp V w N) *
          (1 + 2 * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2) +
            C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 4) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * (C * rhoN N ^ 4 / epsP (rhoN N) ^ 4) *
          (Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2) *
            (g0 V w / epsP (rhoN N) ^ 2)) := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  set Ψ := trialState V w kc N with hΨdef
  set m : ℝ := (⌈mc (rhoN N)⌉₊ : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have hDp := Real.sqrt_nonneg (S9_Dp V w N)
  have hθ := S9_theta_nonneg V w N v₃ v₄
  obtain ⟨p12, p13, p14, p23, p24, p34⟩ := (S9_Gen4_iff _ _ _ _).1 hGen
  have bd : ∀ (f : Occ → ℝ) (B : ℝ), (∀ α, Ψ α ≠ 0 → |f α| ≤ B) →
      Summable fun α : Occ => f α * ‖Ψ α‖ ^ 2 := fun f B h => S9_summable_w hΨ f B h
  have hW : Summable fun b : Occ => (((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1)) * ‖Ψ b‖ ^ 2 :=
    bd _ ((N + 1 : ℝ) * (N + 1)) (fun α h => by
      rw [abs_of_nonneg (by positivity)]
      have a := S9_occ_le hΨ h v₃
      have b := S9_occ_le hΨ h v₄
      have : (α v₃ : ℝ) ≤ N := by exact_mod_cast a
      have : (α v₄ : ℝ) ≤ N := by exact_mod_cast b
      gcongr)
  have hK : Summable fun κ : Occ => ((κ v₃ : ℝ) * κ v₄) * ‖Ψ κ‖ ^ 2 :=
    bd _ ((N : ℝ) * N) (fun α h => by
      rw [abs_of_nonneg (by positivity)]
      have a := S9_occ_le hΨ h v₃
      have b := S9_occ_le hΨ h v₄
      have : (α v₃ : ℝ) ≤ N := by exact_mod_cast a
      have : (α v₄ : ℝ) ≤ N := by exact_mod_cast b
      gcongr)
  have key := S9_T_le hΨ v₁ v₂ v₃ v₄
    (fun b => (m * Real.sqrt (S9_Dp V w N)) *
      ((((b v₃ : ℝ) + 1) * ((b v₄ : ℝ) + 1)) * ‖Ψ b‖ ^ 2))
    (fun κ => (m * S9_theta V w N v₃ v₄) * (((κ v₃ : ℝ) * κ v₄) * ‖Ψ κ‖ ^ 2))
    (fun b => by positivity) (fun κ => by positivity) (hW.mul_left _) (hK.mul_left _)
    (fun κ hc => (S9_pt2 E kc h₁ h₂ h₃ h₄ hGen κ hc).trans_eq (by ring))
  refine key.trans ?_
  rw [tsum_mul_left, tsum_mul_left, S9_sum_succ2 hΨ, ← S9_Q2_eq]
  have hQ3 := S9_Q1_bound E hC kc h₃
  have hQ4 := S9_Q1_bound E hC kc h₄
  have hQ34 := E.hQ2 kc v₃ v₄ h₃ h₄ p34.1 (S9_ne_of_pm p34)
  have hB := E.hlamH v₃ h₃
  have hB' := E.hlamH v₄ h₄
  have hBB : |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| ≤
      (g0 V w / epsP (rhoN N) ^ 2) ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hB hB' (abs_nonneg _) (by positivity)
  have hsum1 : 1 + Expect.Q Ψ [v₃] + Expect.Q Ψ [v₄] + Expect.Q Ψ [v₃, v₄] ≤
      1 + 2 * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2) +
        C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 4 := by
    have h1 : Expect.Q Ψ [v₃, v₄] ≤ C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4 := by
      refine hQ34.trans ?_
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBB hC) (by positivity)
    linarith only [hQ3, hQ4, h1]
  have hθB : S9_theta V w N v₃ v₄ *
      |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| ≤
      Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2) * (g0 V w / epsP (rhoN N) ^ 2) := by
    set Bv := |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| with hBv
    set a := rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2 with ha
    have ha0 : 0 ≤ a := by
      have : 0 ≤ rhoN N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hρ.le _
      positivity
    have hBv0 : 0 ≤ Bv := abs_nonneg _
    rcases hBv0.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; positivity
    · have e : S9_theta V w N v₃ v₄ * Bv = Real.sqrt a * Real.sqrt Bv := by
        unfold S9_theta
        rw [← hBv, ← ha, Real.sqrt_div ha0]
        have hs : 0 < Real.sqrt Bv := Real.sqrt_pos.2 hpos
        have hsq : Real.sqrt Bv * Real.sqrt Bv = Bv := Real.mul_self_sqrt hBv0
        calc Real.sqrt a / Real.sqrt Bv * Bv = Real.sqrt a / Real.sqrt Bv *
              (Real.sqrt Bv * Real.sqrt Bv) := by rw [hsq]
          _ = Real.sqrt a * Real.sqrt Bv := by field_simp
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
      calc Real.sqrt Bv ≤ Real.sqrt ((g0 V w / epsP (rhoN N) ^ 2) ^ 2) :=
            Real.sqrt_le_sqrt hBB
        _ = _ := Real.sqrt_sq (by positivity)
  have hsum2 : S9_theta V w N v₃ v₄ * Expect.Q Ψ [v₃, v₄] ≤
      (C * rhoN N ^ 4 / epsP (rhoN N) ^ 4) *
        (Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2) *
          (g0 V w / epsP (rhoN N) ^ 2)) := by
    calc S9_theta V w N v₃ v₄ * Expect.Q Ψ [v₃, v₄]
        ≤ S9_theta V w N v₃ v₄ * (C * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| *
          rhoN N ^ 4 / epsP (rhoN N) ^ 4) := mul_le_mul_of_nonneg_left hQ34 hθ
      _ = (C * rhoN N ^ 4 / epsP (rhoN N) ^ 4) * (S9_theta V w N v₃ v₄ *
          |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hθB (by positivity)
  have e3 : m * Real.sqrt (S9_Dp V w N) *
      (1 + Expect.Q Ψ [v₃] + Expect.Q Ψ [v₄] + Expect.Q Ψ [v₃, v₄]) ≤ m * Real.sqrt (S9_Dp V w N) *
      (1 + 2 * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2) +
        C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 4) :=
    mul_le_mul_of_nonneg_left hsum1 (by positivity)
  have e4 : m * (S9_theta V w N v₃ v₄ * Expect.Q Ψ [v₃, v₄]) ≤ m * ((C * rhoN N ^ 4 /
      epsP (rhoN N) ^ 4) * (Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2) *
        (g0 V w / epsP (rhoN N) ^ 2))) := mul_le_mul_of_nonneg_left hsum2 hm0
  calc _ = m * Real.sqrt (S9_Dp V w N) *
      (1 + Expect.Q Ψ [v₃] + Expect.Q Ψ [v₄] + Expect.Q Ψ [v₃, v₄]) +
      m * (S9_theta V w N v₃ v₄ * Expect.Q Ψ [v₃, v₄]) := by ring
    _ ≤ m * Real.sqrt (S9_Dp V w N) *
      (1 + 2 * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2) +
        C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 4) +
      m * ((C * rhoN N ^ 4 / epsP (rhoN N) ^ 4) *
        (Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2) *
          (g0 V w / epsP (rhoN N) ^ 2))) := add_le_add e3 e4
    _ = _ := by ring

/-- `Σ_β w₂(x, y; β)|Ψ(β)|² ≤ ⌈m_c⌉²` for `x, y ∈ P_L`. -/
private lemma S9_wsum_PL {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {x y : Idx} (hx : inPL (rhoN N) (LN N) x) (hy : inPL (rhoN N) (LN N) y) :
    ∑' β, S9_w2 x y β * ‖trialState V w kc N β‖ ^ 2 ≤ (⌈mc (rhoN N)⌉₊ : ℝ) ^ 2 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  refine S9_wsum_le hΨ _ (S9_w2_nonneg x y) (fun β hβ => ?_)
  have hM := S9_inM hβ
  have e1 : ((β x : ℕ) : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := Nat.cast_le.2 (S9_occ_ceil hρ hM hx)
  have e2 : ((β y : ℕ) : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := Nat.cast_le.2 (S9_occ_ceil hρ hM hy)
  calc S9_w2 x y β ≤ (β x : ℝ) * β y := S9_w2_le x y β
    _ ≤ (⌈mc (rhoN N)⌉₊ : ℝ) * (⌈mc (rhoN N)⌉₊ : ℝ) := by gcongr
    _ = _ := by ring

/-- `Σ_β w₂(x, y; β)|Ψ(β)|² = Q_Ψ(x, y)` for `x ≠ y`. -/
private lemma S9_wsum_ne (Ψ : Occ → ℂ) {x y : Idx} (h : x ≠ y) :
    ∑' β, S9_w2 x y β * ‖Ψ β‖ ^ 2 = Expect.Q Ψ [x, y] := by
  rw [S9_Q2_eq]
  congr 1
  funext β
  simp [S9_w2, h]

/-- Class 2, all tuples: `T ≤ ⌈m_c⌉ √(C (g₀/ε²)² ρ⁴ / ε⁴)`. -/
private lemma S9_spec2 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPL (rhoN N) (LN N) v₂)
    (h₃ : inPH (rhoN N) (LN N) v₃) (h₄ : inPH (rhoN N) (LN N) v₄) (h34 : v₃ ≠ v₄)
    (h34' : v₃ + v₄ ≠ 0) :
    S9_T (trialState V w kc N) v₁ v₂ v₃ v₄ ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 *
        rhoN N ^ 4 / epsP (rhoN N) ^ 4) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  have ht := S9_eps_pos hρ
  have hQ := E.hQ2 kc v₃ v₄ h₃ h₄ h34 h34'
  have hB := E.hlamH v₃ h₃
  have hB' := E.hlamH v₄ h₄
  have hBB : |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| ≤
      (g0 V w / epsP (rhoN N) ^ 2) ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hB hB' (abs_nonneg _) (by have := E.hg; positivity)
  have h2 : ∑' α, S9_w2 v₃ v₄ α * ‖trialState V w kc N α‖ ^ 2 ≤
      C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 4 := by
    rw [S9_wsum_ne _ h34]
    refine hQ.trans ?_
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBB hC) (by positivity)
  have := S9_T_le_sch hΨ v₁ v₂ v₃ v₄ (S9_wsum_PL E kc h₁ h₂) h2
  rwa [Real.sqrt_sq (by positivity)] at this


/-- `D'` in closed form. -/
private lemma S9_Dp_eq (V w : R3 → ℝ) {N : ℕ} (hN : 1 ≤ N) (hg : 0 < g0 V w) :
    S9_Dp V w N = (2 * epsP (rhoN N) ^ 186 / (N : ℝ)) ^ 2 := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have ht := S9_eps_pos hρ
  have hK : rhoN N ^ (-(1 / 10 : ℝ)) = (epsP (rhoN N) ^ 20)⁻¹ :=
    S9_rpow_eps_neg hρ.le 20 (by norm_num)
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  have hn : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold S9_Dp
  rw [hK]
  generalize epsP (rhoN N) = t at ht hr ⊢
  rw [hr]
  have hg' : g0 V w ≠ 0 := hg.ne'
  field_simp

/-- The generic tuples of class 2: the exponent. -/
private lemma S9_arith2 (V w : R3 → ℝ) {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C) :
    (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_Dp V w N) *
          (1 + 2 * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2) +
            C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 4) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * (C * rhoN N ^ 4 / epsP (rhoN N) ^ 4) *
          (Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2) *
            (g0 V w / epsP (rhoN N) ^ 2)) ≤
      (4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) + 2 * C * g0 V w) * epsP (rhoN N) ^ 583 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have ht1 := S9_eps_le_one hρ hρ1
  have hg := E.hg
  have hm := S9_ceil_le hρ hρ1
  have hm0 : (0 : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := Nat.cast_nonneg _
  have hN425 := S9_Nt E.hN
  have hK : rhoN N ^ (-(1 / 10 : ℝ)) = (epsP (rhoN N) ^ 20)⁻¹ :=
    S9_rpow_eps_neg hρ.le 20 (by norm_num)
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  have hD := S9_Dp_eq V w E.hN hg
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast E.hN
  rw [hD, hK]
  generalize (⌈mc (rhoN N)⌉₊ : ℝ) = m at hm hm0 ⊢
  generalize (N : ℝ) = n at hN425 hN1 ⊢
  generalize epsP (rhoN N) = t at ht ht1 hm hN425 hr ⊢
  have hn0 : 0 < n := by linarith
  have hs1 : Real.sqrt ((2 * t ^ 186 / n) ^ 2) = 2 * t ^ 186 * t ^ 425 := by
    rw [Real.sqrt_sq (by positivity)]
    have : 1 / n = t ^ 425 := by field_simp; linarith
    rw [div_eq_mul_one_div, this]
  have hs2 : Real.sqrt ((t ^ 20)⁻¹ * ((rhoN N)⁻¹) ^ 2) = (t ^ 210)⁻¹ := by
    rw [hr]
    have : (t ^ 20)⁻¹ * ((t ^ 200)⁻¹) ^ 2 = ((t ^ 210)⁻¹) ^ 2 := by
      field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  rw [hs1, hs2, hr]
  have hm2 : m ≤ 2 * t⁻¹ := hm
  have hQ2 : 1 + 2 * (C * (t ^ 200) ^ 2 * (g0 V w / t ^ 2) / t ^ 2) +
      C * (g0 V w / t ^ 2) ^ 2 * (t ^ 200) ^ 4 / t ^ 4 ≤ 1 + 2 * C * g0 V w + C * g0 V w ^ 2 := by
    have e : 1 + 2 * (C * (t ^ 200) ^ 2 * (g0 V w / t ^ 2) / t ^ 2) +
        C * (g0 V w / t ^ 2) ^ 2 * (t ^ 200) ^ 4 / t ^ 4 =
        1 + 2 * C * g0 V w * t ^ 396 + C * g0 V w ^ 2 * t ^ 792 := by
      field_simp
    rw [e]
    have h1 : t ^ 396 ≤ 1 := pow_le_one₀ ht.le ht1
    have h2 : t ^ 792 ≤ 1 := pow_le_one₀ ht.le ht1
    have h3 : 0 ≤ 2 * C * g0 V w := by positivity
    have h4 : 0 ≤ C * g0 V w ^ 2 := by positivity
    calc 1 + 2 * C * g0 V w * t ^ 396 + C * g0 V w ^ 2 * t ^ 792
        ≤ 1 + 2 * C * g0 V w * 1 + C * g0 V w ^ 2 * 1 := by gcongr
      _ = _ := by ring
  have hA : 0 ≤ 1 + 2 * (C * (t ^ 200) ^ 2 * (g0 V w / t ^ 2) / t ^ 2) +
      C * (g0 V w / t ^ 2) ^ 2 * (t ^ 200) ^ 4 / t ^ 4 := by positivity
  calc m * (2 * t ^ 186 * t ^ 425) * (1 + 2 * (C * (t ^ 200) ^ 2 * (g0 V w / t ^ 2) / t ^ 2) +
        C * (g0 V w / t ^ 2) ^ 2 * (t ^ 200) ^ 4 / t ^ 4) +
      m * (C * (t ^ 200) ^ 4 / t ^ 4) * ((t ^ 210)⁻¹ * (g0 V w / t ^ 2))
      ≤ (2 * t⁻¹) * (2 * t ^ 186 * t ^ 425) * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) +
        (2 * t⁻¹) * (C * (t ^ 200) ^ 4 / t ^ 4) * ((t ^ 210)⁻¹ * (g0 V w / t ^ 2)) := by
        gcongr
    _ = 4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) * t ^ 610 + 2 * C * g0 V w * t ^ 583 := by
        field_simp
        ring
    _ ≤ (4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) + 2 * C * g0 V w) * t ^ 583 := by
        have h1 : t ^ 610 ≤ t ^ 583 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
        have h2 : 0 ≤ 4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) := by positivity
        calc 4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) * t ^ 610 + 2 * C * g0 V w * t ^ 583
            ≤ 4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) * t ^ 583 + 2 * C * g0 V w * t ^ 583 := by
              gcongr
          _ = _ := by ring

/-- The special tuples of class 2: the exponent. -/
private lemma S9_arith2s (V w : R3 → ℝ) {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C) :
    (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 *
        rhoN N ^ 4 / epsP (rhoN N) ^ 4) ≤ 2 * g0 V w * Real.sqrt C * epsP (rhoN N) ^ 395 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have hm := S9_ceil_le hρ hρ1
  have hm0 : (0 : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := Nat.cast_nonneg _
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  generalize (⌈mc (rhoN N)⌉₊ : ℝ) = m at hm hm0 ⊢
  generalize epsP (rhoN N) = t at ht hm hr ⊢
  rw [hr]
  have e : C * (g0 V w / t ^ 2) ^ 2 * (t ^ 200) ^ 4 / t ^ 4 = (Real.sqrt C * g0 V w * t ^ 396) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hC]
    field_simp
  rw [e, Real.sqrt_sq (by positivity)]
  calc m * (Real.sqrt C * g0 V w * t ^ 396) ≤ (2 * t⁻¹) * (Real.sqrt C * g0 V w * t ^ 396) := by
        gcongr
    _ = 2 * g0 V w * Real.sqrt C * t ^ 395 := by
        field_simp


/-- The closing step of class 2. -/
private lemma S9_fin2 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    {V₀ : ℝ} (hV₀ : 0 ≤ V₀) {kc : ℝ} (hkc : 1 ≤ kc) {nS nT : ℝ} (hnS0 : 0 ≤ nS) (hnT0 : 0 ≤ nT)
    (hnS : nS ≤ (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 2 * (67 * (LN N ^ 3 * kc ^ 3)))
    (hnT : nT ≤ 6 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * (67 * (LN N ^ 3 * kc ^ 3)))) :
    V₀ / ((LN N ^ 3) ^ 2 * rhoN N ^ (5 / 2 : ℝ)) *
      (nS * ((⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_Dp V w N) *
          (1 + 2 * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2) +
            C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 4) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * (C * rhoN N ^ 4 / epsP (rhoN N) ^ 4) *
          (Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2) *
            (g0 V w / epsP (rhoN N) ^ 2))) +
      nT * ((⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 *
        rhoN N ^ 4 / epsP (rhoN N) ^ 4))) ≤
      V₀ * (67 ^ 3 * (4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) + 2 * C * g0 V w) +
        6 * 67 ^ 2 * (2 * g0 V w * Real.sqrt C)) * kc ^ 3 * epsP (rhoN N) ^ 10 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have ht1 := S9_eps_le_one hρ hρ1
  have hg := E.hg
  rw [S9_pref E.hN V₀]
  have hL3 := S9_L3 E.hN
  have hk3 : 0 ≤ kc ^ 3 := by positivity
  have hnS' : nS * epsP (rhoN N) ^ 1281 ≤ 67 ^ 3 * kc ^ 3 := by
    calc nS * epsP (rhoN N) ^ 1281
        ≤ (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 2 * (67 * (LN N ^ 3 * kc ^ 3)) *
          epsP (rhoN N) ^ 1281 := by gcongr
      _ = 67 ^ 3 * (LN N ^ 3 * epsP (rhoN N) ^ 625) ^ 3 * kc ^ 3 := by ring
      _ = 67 ^ 3 * kc ^ 3 := by rw [hL3]; norm_num
  have hnT' : nT * epsP (rhoN N) ^ 953 ≤ 6 * 67 ^ 2 * kc ^ 3 := by
    calc nT * epsP (rhoN N) ^ 953
        ≤ 6 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * (67 * (LN N ^ 3 * kc ^ 3))) *
          epsP (rhoN N) ^ 953 := by gcongr
      _ = 6 * 67 ^ 2 * (LN N ^ 3 * epsP (rhoN N) ^ 625) ^ 2 * kc ^ 3 := by ring
      _ = 6 * 67 ^ 2 * kc ^ 3 := by rw [hL3]; norm_num
  have hBg := S9_arith2 V w E hC
  have hBs := S9_arith2s V w E hC
  have hcl := S9_close (t := epsP (rhoN N)) (V₀ := V₀) (P := 750) (a := 1281) (b := 953)
    (e := 583) (f := 0) (f' := 395) (k := 10)
    (cS := 67 ^ 3 * kc ^ 3) (cT := 6 * 67 ^ 2 * kc ^ 3)
    (cg := 4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) + 2 * C * g0 V w)
    (cs := 2 * g0 V w * Real.sqrt C) ht ht1 hV₀ hnS0 hnT0 (by positivity) (by positivity)
    (by positivity) (by positivity) hnS' hnT' hBg (by simpa using hBs) (by norm_num)
    (by norm_num)
  refine hcl.trans (le_of_eq ?_)
  ring

private lemma S9_card3 (B₁ B₂ B₃ : Finset Idx) (f : Idx × Idx × Idx → Idx × Idx × Idx) :
    (((B₁ ×ˢ B₂ ×ˢ B₃).image f).card : ℝ) ≤ (B₁.card : ℝ) * ((B₂.card : ℝ) * B₃.card) := by
  have h : ((B₁ ×ˢ B₂ ×ˢ B₃).image f).card ≤ B₁.card * (B₂.card * B₃.card) :=
    Finset.card_image_le.trans (by simp [Finset.card_product])
  exact_mod_cast h

/-- Class 2 (case 2 of Lemma 9.1 [fourlegslemma1] and the case with `(v₁,v₂)` and `(v₃,v₄)`
exchanged): the rate `ε^{10} = ρ^{1/20}`. -/
private lemma S9_class2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc →
      FourLegs.absPart V w .two kc N ≤ C' * kc ^ 3 * epsP (rhoN N) ^ 10 ∧
      FourLegs.absPart V w .twoAdj kc N ≤ C' * kc ^ 3 * epsP (rhoN N) ^ 10 := by
  obtain ⟨V₀, hV₀0, hV₀⟩ := S9_V0 hV
  obtain ⟨C, hC, hev⟩ := S9_env hV hw
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  have hg := scat_g0_pos hV hw
  refine ⟨V₀ * (67 ^ 3 * (4 * (1 + 2 * C * g0 V w + C * g0 V w ^ 2) + 2 * C * g0 V w) +
    6 * 67 ^ 2 * (2 * g0 V w * Real.sqrt C)), by positivity, N₀, fun N hN kc hkc => ?_⟩
  have E := hN₀ N hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have hΨ := Normalization_isNState V w kc E.hN
  set BL := S9_ball (LN N) ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) with hBL
  set BH := S9_ball (LN N) kc with hBH
  have hmL : ∀ n, inPL (rhoN N) (LN N) n → n ∈ BL := fun n hn => S9_mem_ball hL hn.2
  have hmH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH := fun n hn => S9_mem_ball hL hn.2
  have hcL : (BL.card : ℝ) ≤ 67 * (LN N ^ 3 * epsP (rhoN N) ^ 297) := S9_card_PL E.hN
  have hcH : (BH.card : ℝ) ≤ 67 * (LN N ^ 3 * kc ^ 3) := S9_card_PH E.hN kc hkc
  have hnT : ((6 : ℝ) * ((BL.card : ℝ) * BH.card)) ≤
      6 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * (67 * (LN N ^ 3 * kc ^ 3))) := by
    gcongr
  have hnS : (BL.card : ℝ) * ((BL.card : ℝ) * BH.card) ≤
      (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 2 * (67 * (LN N ^ 3 * kc ^ 3)) := by
    calc (BL.card : ℝ) * ((BL.card : ℝ) * BH.card)
        ≤ (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) *
          (67 * (LN N ^ 3 * kc ^ 3))) := by gcongr
      _ = _ := by ring
  have hm0 : (0 : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := Nat.cast_nonneg _
  have hBg0 : 0 ≤ (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_Dp V w N) *
          (1 + 2 * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) / epsP (rhoN N) ^ 2) +
            C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * rhoN N ^ 4 / epsP (rhoN N) ^ 4) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * (C * rhoN N ^ 4 / epsP (rhoN N) ^ 4) *
          (Real.sqrt (rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹) ^ 2) *
            (g0 V w / epsP (rhoN N) ^ 2)) := by positivity
  have hBs0 : 0 ≤ (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (C * (g0 V w / epsP (rhoN N) ^ 2) ^ 2 *
        rhoN N ^ 4 / epsP (rhoN N) ^ 4) := by positivity
  refine ⟨?_, ?_⟩
  · -- the class `.two`
    set S₂ := (BL ×ˢ BL ×ˢ BH).image
      (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2)) with hS₂
    have hS : ∀ x : Idx × Idx × Idx, FourLegs.Cls.mem (rhoN N) (LN N) kc N .two
        (x.1, x.2.1, x.2.2, 0) → Decomp.Part.A2.mem x.1 x.2.1 x.2.2 → x ∈ S₂ := by
      rintro ⟨p, q, u⟩ hm -
      obtain ⟨hp, hq, hpu, hqu⟩ := hm
      rw [hS₂, Finset.mem_image]
      refine ⟨(p, q, p - u), ?_, by simp⟩
      simp only [Finset.mem_product]
      exact ⟨hmL _ hp, hmL _ hq, hmH _ hpu⟩
    have hmain := S9_assemble V w kc E.hN (c := .two) (Or.inr (Or.inl rfl)) hV₀ hV₀0 S₂
      (S9_sp BL BH) hS hBg0 hBs0
      (fun x _ hP hGen => by
        obtain ⟨hp, hq, hpu, hqu⟩ := hP.1
        exact S9_gen2 E hC kc hp hq hpu.1 hqu.1 hGen)
      (fun x _ hP => by
        obtain ⟨hp, hq, hpu, hqu⟩ := hP.1
        obtain ⟨x1, x2, x3⟩ := x
        obtain ⟨-, hpq, -⟩ := hP.2
        refine S9_spec2 E hC kc hp hq hpu.1 hqu.1 ?_ ?_
        · intro h
          apply (S9_no_double hρ hρ1 hp hq hpu.1).1
          calc (x1 - x3) + (x1 - x3) = (x1 - x3) + (x2 + x3) := by rw [← h]
            _ = x1 + x2 := by abel
        · have : x1 - x3 + (x2 + x3) = x1 + x2 := by abel
          rw [this]; exact hpq)
      (by
        rintro ⟨p, q, u⟩ - hP hGen
        obtain ⟨hp, hq, hpu, hqu⟩ := hP.1
        simp only at hp hq hpu hqu
        rcases S9_not_gen hP.2 hGen with h | h | h | h | h | h
        · exact S9_mem_sp1 (hmL _ hp) (hmH _ hpu) h
        · exfalso
          apply (S9_no_double hρ hρ1 hp hq hpu.1).1
          calc (p - u) + (p - u) = (p - u) + (q + u) := by rw [← h]
            _ = p + q := by abel
        · exact absurd h (S9_PL_PH_ne hρ hp hpu.1).2
        · exact absurd h (S9_PL_PH_ne hρ hp hqu.1).2
        · exact absurd h (S9_PL_PH_ne hρ hq hpu.1).2
        · exact absurd h (S9_PL_PH_ne hρ hq hqu.1).2)
    refine hmain.trans ?_
    have h1 := S9_card3 BL BL BH (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2))
    have h2 := S9_sp_card BL BH
    refine (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right
      (h1.trans hnS) hBg0) (mul_le_mul_of_nonneg_right (h2.trans hnT) hBs0))
      (by positivity)).trans ?_
    exact S9_fin2 E hC hV₀0 hkc (by positivity) (by positivity) le_rfl le_rfl
  · -- the class `.twoAdj`
    set S₂ := (BL ×ˢ BL ×ˢ BH).image
      (fun y : Idx × Idx × Idx => (y.2.2, y.1 + y.2.1 - y.2.2, y.2.2 - y.1)) with hS₂
    have hS : ∀ x : Idx × Idx × Idx, FourLegs.Cls.mem (rhoN N) (LN N) kc N .twoAdj
        (x.1, x.2.1, x.2.2, 0) → Decomp.Part.A2.mem x.1 x.2.1 x.2.2 → x ∈ S₂ := by
      rintro ⟨p, q, u⟩ hm -
      obtain ⟨hp, hq, hpu, hqu⟩ := hm
      rw [hS₂, Finset.mem_image]
      refine ⟨(p - u, q + u, p), ?_, ?_⟩
      · simp only [Finset.mem_product]
        exact ⟨hmL _ hpu, hmL _ hqu, hmH _ hp⟩
      · simp only [Prod.mk.injEq, true_and]
        refine ⟨by abel, by abel⟩
    have hmain := S9_assemble V w kc E.hN (c := .twoAdj) (Or.inr (Or.inr (Or.inl rfl))) hV₀
      hV₀0 S₂ (S9_sp BH BL) hS hBg0 hBs0
      (fun x _ hP hGen => by
        obtain ⟨hp, hq, hpu, hqu⟩ := hP.1
        obtain ⟨p, q, u⟩ := x
        refine (S9_T_adj_le hΨ p q (p - u) (q + u)).trans ?_
        exact S9_gen2 E hC kc hqu hpu hq.1 hp.1 (S9_Gen4_adj hGen))
      (fun x _ hP => by
        obtain ⟨hp, hq, hpu, hqu⟩ := hP.1
        obtain ⟨p, q, u⟩ := x
        obtain ⟨-, hpq, -⟩ := hP.2
        refine (S9_T_adj_le hΨ p q (p - u) (q + u)).trans ?_
        refine S9_spec2 E hC kc hqu hpu hq.1 hp.1 ?_ ?_
        · intro h
          have h' : q = p := h
          apply (S9_no_double hρ hρ1 hpu hqu hp.1).1
          rw [h']; abel
        · rw [add_comm]; exact hpq)
      (by
        rintro ⟨p, q, u⟩ - hP hGen
        obtain ⟨hp, hq, hpu, hqu⟩ := hP.1
        simp only at hp hq hpu hqu
        rcases S9_not_gen hP.2 hGen with h | h | h | h | h | h
        · exfalso
          have h' : p = q := h
          apply (S9_no_double hρ hρ1 hpu hqu hp.1).1
          rw [← h']; abel
        · exact S9_mem_sp2 (hmH _ hp) (hmL _ hpu) h
        · exact absurd (neg_eq_iff_eq_neg.mp h.symm) (S9_PL_PH_ne hρ hpu hp.1).2
        · exact absurd (neg_eq_iff_eq_neg.mp h.symm) (S9_PL_PH_ne hρ hqu hp.1).2
        · exact absurd (neg_eq_iff_eq_neg.mp h.symm) (S9_PL_PH_ne hρ hpu hq.1).2
        · exact absurd (neg_eq_iff_eq_neg.mp h.symm) (S9_PL_PH_ne hρ hqu hq.1).2)
    refine hmain.trans ?_
    have h1 := S9_card3 BL BL BH
      (fun y : Idx × Idx × Idx => (y.2.2, y.1 + y.2.1 - y.2.2, y.2.2 - y.1))
    have h2 := S9_sp_card BH BL
    have hnT' : ((6 : ℝ) * ((BH.card : ℝ) * BL.card)) ≤
        6 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * (67 * (LN N ^ 3 * kc ^ 3))) := by
      calc (6 : ℝ) * ((BH.card : ℝ) * BL.card) = 6 * ((BL.card : ℝ) * BH.card) := by ring
        _ ≤ _ := hnT
    refine (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right
      (h1.trans hnS) hBg0) (mul_le_mul_of_nonneg_right (h2.trans hnT') hBs0))
      (by positivity)).trans ?_
    exact S9_fin2 E hC hV₀0 hkc (by positivity) (by positivity) le_rfl le_rfl

/-! ### Proposition 9.1 -/

/-- On `M`, `α(n) ≤ N`. -/
private lemma S9_occ_le_M {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {α : Occ}
    (hα : InM (rhoN N) (LN N) kc N α) (n : Idx) : (α n : ℝ) ≤ N := by
  have h := (S9_occ_le_num α n).trans (MBasic_num (Particles_rhoN_LN hN).2.1 hα).le
  exact_mod_cast h

/-- On `M`, `α(n)/|Λ| ≤ ρ`. -/
private lemma S9_occ_div_le {N : ℕ} (hN : 1 ≤ N) {kc : ℝ} {α : Occ}
    (hα : InM (rhoN N) (LN N) kc N α) (n : Idx) : (α n : ℝ) / LN N ^ 3 ≤ rhoN N := by
  obtain ⟨hNL, -, -, hL⟩ := Particles_rhoN_LN hN
  rw [div_le_iff₀ (by positivity), hNL]
  exact S9_occ_le_M hN hα n

/-- Covering bound: if every `α` with `F(α) ≠ 0` is `back j` for some `j` with
`F(α) ≤ G(j)`, then `Σ_α F(α) ≤ Σ_j G(j)`. -/
private lemma S9_cover {ι : Type*} (F : Occ → ℝ) (G : ι → ℝ) (hF : ∀ α, 0 ≤ F α)
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

private lemma S9_trial_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} {α : Occ}
    (h : InM (rhoN N) (LN N) kc N α) :
    trialState V w kc N α = (CN V w kc N : ℂ) * f0 V w (rhoN N) (LN N) α := by
  rw [FIdentities_trialState]
  simp [h]

private lemma S9_norm_csqrt_sq (x : ℝ) : ‖csqrt x‖ ^ 2 = |x| := by
  unfold csqrt
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt h, abs_of_nonneg h]
  · have h' : 0 ≤ -x := by linarith [not_le.1 h]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt h', abs_of_neg (not_le.1 h)]

/-- `|Ψ(𝓐^{u;p₁,p₂} β)|² = 4β(0)β(u)|Λ|⁻²|λ_{p₁}λ_{p₂}||Ψ(β)|²`, (5.7) [properf4]. -/
private lemma S9_soft_eq (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u p₁ p₂ : Idx}
    {β : Occ} (hu : inPL (rhoN N) (LN N) u) (h₁ : inPH (rhoN N) (LN N) p₁)
    (h₂ : inPH (rhoN N) (LN N) p₂) (hs : p₁ + p₂ = u) (hβ : InMuS (rhoN N) (LN N) kc N u β)
    (hα : InM (rhoN N) (LN N) kc N (softPair u p₁ p₂ β)) :
    ‖trialState V w kc N (softPair u p₁ p₂ β)‖ ^ 2 =
      4 * ((β 0 : ℝ) / LN N ^ 3) * ((β u : ℝ) / LN N ^ 3) *
        |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| *
          ‖trialState V w kc N β‖ ^ 2 := by
  obtain ⟨-, hρ, -, hL⟩ := Particles_rhoN_LN hN
  have hf := Lemma5_1_properf4 (V := V) (w := w) hρ hL hu h₁ h₂ hs hβ hα
  rw [S9_trial_eq V w kc hα, S9_trial_eq V w kc hβ.1, hf]
  simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, S9_norm_csqrt_sq,
    abs_mul]
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  ring


/-- `|λ_p λ_{s-p}|` for `p, s - p ∈ P_{H,c}`. -/
private def S9_Tp (V w : R3 → ℝ) (N : ℕ) (kc : ℝ) (s p : Idx) : ℝ :=
  if inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (s - p) then
    |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (s - p)| else 0

/-- The same, restricted to `p = v` or `s - p = v`. -/
private def S9_Tp' (V w : R3 → ℝ) (N : ℕ) (kc : ℝ) (s v p : Idx) : ℝ :=
  S9_Tp V w N kc s p * ((if v = p then 1 else 0) + (if v = s - p then 1 else 0))

private lemma S9_Tp_nonneg (V w : R3 → ℝ) (N : ℕ) (kc : ℝ) (s p : Idx) :
    0 ≤ S9_Tp V w N kc s p := by
  unfold S9_Tp; split_ifs <;> positivity

private lemma S9_Tp'_nonneg (V w : R3 → ℝ) (N : ℕ) (kc : ℝ) (s v p : Idx) :
    0 ≤ S9_Tp' V w N kc s v p := by
  unfold S9_Tp'
  have := S9_Tp_nonneg V w N kc s p
  have h1 : (0 : ℝ) ≤ (if v = p then 1 else 0) + (if v = s - p then 1 else 0) := by
    split_ifs <;> norm_num
  positivity

private lemma S9_Tp_summable (V w : R3 → ℝ) {N : ℕ} {kc : ℝ} (s : Idx) (BH : Finset Idx)
    (hBH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH) : Summable (S9_Tp V w N kc s) := by
  refine summable_of_ne_finset_zero (s := BH) fun p hp => ?_
  unfold S9_Tp
  rw [ite_eq_right]
  intro h
  exact absurd (hBH p h.1) hp

private lemma S9_Tp'_summable (V w : R3 → ℝ) {N : ℕ} {kc : ℝ} (s v : Idx) (BH : Finset Idx)
    (hBH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH) : Summable (S9_Tp' V w N kc s v) := by
  refine summable_of_ne_finset_zero (s := BH) fun p hp => ?_
  unfold S9_Tp' S9_Tp
  rw [ite_mul, zero_mul]
  rw [ite_eq_right]
  intro h
  exact absurd (hBH p h.1) hp

/-- The soft creation bound with the weight `α(v)`: for `s ∈ P_L` and `v ∈ P_H`, the
configurations with `α(-s) = α(s) + 1` are `𝓐^{s;p₁,p₂} β` with `β ∈ M_s^s`,
(5.19) [ubpsiuroughPL1.5] and (9.5)–(9.7). -/
private lemma S9_soft_pos {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {s v : Idx} (hs : inPL (rhoN N) (LN N) s) (hv : inPH (rhoN N) (LN N) v)
    (BH : Finset Idx) (hBH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH) :
    (∑' α : Occ, if InM (rhoN N) (LN N) kc N α ∧ α (-s) = α s + 1 then
        (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      4 * rhoN N * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3 *
        ((∑' β : Occ, (if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0) *
            ‖trialState V w kc N β‖ ^ 2) * (∑' p : Idx, S9_Tp V w N kc s p) +
          (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N s β then
            ‖trialState V w kc N β‖ ^ 2 else 0) * (∑' p : Idx, S9_Tp' V w N kc s v p)) := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  set Ψ := trialState V w kc N with hΨdef
  have hsq : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have hs0 := Regions_PL_ne_zero hρ hs
  have hv0 := Regions_PH_ne_zero hρ hv
  have hvs : v ≠ s := fun h => Regions_PL_PH hρ hs (h ▸ hv)
  set c₀ : ℝ := 4 * rhoN N * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3 with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set Sv : Occ → ℝ := fun β => (if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0) *
    ‖Ψ β‖ ^ 2 with hSv
  set S1 : Occ → ℝ := fun β => if InMuS (rhoN N) (LN N) kc N s β then ‖Ψ β‖ ^ 2 else 0
    with hS1
  have hSv0 : ∀ β, 0 ≤ Sv β := fun β => by simp only [hSv]; split_ifs <;> positivity
  have hS10 : ∀ β, 0 ≤ S1 β := fun β => by simp only [hS1]; split_ifs <;> positivity
  have hSvs : Summable Sv := by
    refine S9_summable_w hΨ (fun β => if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0)
      N (fun β hβ => ?_)
    split_ifs
    · rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hΨ hβ v
    · simp
  have hS1s : Summable S1 := S9_summable_ite hsq (fun _ => by positivity) _
  have hTs := S9_Tp_summable V w s BH hBH
  have hTs' := S9_Tp'_summable V w s v BH hBH
  have hG1 : Summable fun j : Occ × Idx => Sv j.1 * S9_Tp V w N kc s j.2 :=
    hSvs.mul_of_nonneg hTs hSv0 (S9_Tp_nonneg V w N kc s)
  have hG2 : Summable fun j : Occ × Idx => S1 j.1 * S9_Tp' V w N kc s v j.2 :=
    hS1s.mul_of_nonneg hTs' hS10 (S9_Tp'_nonneg V w N kc s v)
  rw [show c₀ * ((∑' β, Sv β) * (∑' p, S9_Tp V w N kc s p) +
      (∑' β, S1 β) * (∑' p, S9_Tp' V w N kc s v p)) =
      ∑' j : Occ × Idx, c₀ * (Sv j.1 * S9_Tp V w N kc s j.2 +
        S1 j.1 * S9_Tp' V w N kc s v j.2) by
    rw [tsum_mul_left, (hG1.tsum_add hG2), Summable.tsum_mul_tsum hSvs hTs hG1,
      Summable.tsum_mul_tsum hS1s hTs' hG2]]
  refine S9_cover _ _ (fun α => by split_ifs <;> positivity)
    (fun j => mul_nonneg hc₀0 (add_nonneg (mul_nonneg (hSv0 _) (S9_Tp_nonneg _ _ _ _ _ _))
      (mul_nonneg (hS10 _) (S9_Tp'_nonneg _ _ _ _ _ _ _))))
    ((hG1.add hG2).mul_left c₀) (fun j => softPair s j.2 (s - j.2) j.1) ?_
  intro α hα
  have hc : InM (rhoN N) (LN N) kc N α ∧ α (-s) = α s + 1 := by
    by_contra h
    exact hα (ite_eq_right h)
  obtain ⟨hαM, ha⟩ := hc
  rw [ite_eq_left ⟨hαM, ha⟩]
  obtain ⟨β, p₁, p₂, hβS, hc₁, hc₂, hsum, hb0, hbs, he⟩ := Reorder_softLast hρ hs hαM ha
  have hp₂ : s - p₁ = p₂ := by rw [← hsum]; abel
  refine ⟨(β, p₁), by simp only [hp₂, he], ?_⟩
  -- the value of `α(v)`
  have hval : α v = β v + (if v = p₁ then 1 else 0) + (if v = p₂ then 1 else 0) := by
    rw [← he, MBasic_softPair_apply]
    simp only [hv0, hvs, ite_false]
    omega
  have hsoft : ‖Ψ α‖ ^ 2 = 4 * ((β 0 : ℝ) / LN N ^ 3) * ((β s : ℝ) / LN N ^ 3) *
      |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| * ‖Ψ β‖ ^ 2 := by
    have := S9_soft_eq V w kc E.hN hs hc₁.1 hc₂.1 hsum hβS (he ▸ hαM)
    rw [he] at this
    exact this
  have hx := S9_occ_div_le E.hN hβS.1 0
  have hy : ((β s : ℕ) : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := by
    have := (le_max_left (β s) (β (-s))).trans (MStar_PL_ceil hρ hβS.1 hs)
    exact_mod_cast this
  have hΛ : 0 ≤ |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| := abs_nonneg _
  have hψ : 0 ≤ ‖Ψ β‖ ^ 2 := by positivity
  have hnorm : ‖Ψ α‖ ^ 2 ≤ c₀ * (|lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| *
      ‖Ψ β‖ ^ 2) := by
    rw [hsoft, hc₀]
    have hL3 : 0 < LN N ^ 3 := by positivity
    have h1 : 4 * ((β 0 : ℝ) / LN N ^ 3) * ((β s : ℝ) / LN N ^ 3) ≤
        4 * rhoN N * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3 := by
      have hxy : (β 0 : ℝ) / LN N ^ 3 * (β s : ℝ) ≤ rhoN N * (⌈mc (rhoN N)⌉₊ : ℝ) :=
        mul_le_mul hx hy (Nat.cast_nonneg _) hρ.le
      calc 4 * ((β 0 : ℝ) / LN N ^ 3) * ((β s : ℝ) / LN N ^ 3)
          = 4 * ((β 0 : ℝ) / LN N ^ 3 * (β s : ℝ)) / LN N ^ 3 := by ring
        _ ≤ 4 * (rhoN N * (⌈mc (rhoN N)⌉₊ : ℝ)) / LN N ^ 3 := by gcongr
        _ = _ := by ring
    calc 4 * ((β 0 : ℝ) / LN N ^ 3) * ((β s : ℝ) / LN N ^ 3) *
          |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| * ‖Ψ β‖ ^ 2
        = (4 * ((β 0 : ℝ) / LN N ^ 3) * ((β s : ℝ) / LN N ^ 3)) *
          (|lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| * ‖Ψ β‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (mul_nonneg hΛ hψ)
  have hSβ : Sv β = (β v : ℝ) * ‖Ψ β‖ ^ 2 := by simp only [hSv]; rw [ite_eq_left hβS]
  have hS1β : S1 β = ‖Ψ β‖ ^ 2 := by simp only [hS1]; rw [ite_eq_left hβS]
  have hTp : S9_Tp V w N kc s p₁ =
      |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| := by
    unfold S9_Tp; rw [hp₂, ite_eq_left ⟨hc₁, hc₂⟩]
  have hTp' : S9_Tp' V w N kc s v p₁ =
      |lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| *
        ((if v = p₁ then 1 else 0) + (if v = p₂ then 1 else 0)) := by
    unfold S9_Tp'; rw [hTp, hp₂]
  show (α v : ℝ) * ‖Ψ α‖ ^ 2 ≤ c₀ * (Sv (β, p₁).1 * S9_Tp V w N kc s (β, p₁).2 +
    S1 (β, p₁).1 * S9_Tp' V w N kc s v (β, p₁).2)
  simp only
  rw [hSβ, hS1β, hTp, hTp', hval]
  push_cast
  have hI : (0 : ℝ) ≤ (if v = p₁ then 1 else 0) + (if v = p₂ then 1 else 0) := by
    split_ifs <;> norm_num
  have hβv : (0 : ℝ) ≤ (β v : ℝ) := Nat.cast_nonneg _
  calc ((β v : ℝ) + (if v = p₁ then 1 else 0) + (if v = p₂ then 1 else 0)) * ‖Ψ α‖ ^ 2
      ≤ ((β v : ℝ) + (if v = p₁ then 1 else 0) + (if v = p₂ then 1 else 0)) *
        (c₀ * (|lam V w (rhoN N) (LN N) p₁ * lam V w (rhoN N) (LN N) p₂| * ‖Ψ β‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = _ := by ring


private lemma S9_T_sum_le {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ) (s : Idx)
    (BH : Finset Idx) (hBH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH) :
    ∑' p : Idx, S9_Tp V w N kc s p ≤ (g0 V w / epsP (rhoN N) ^ 2) ^ 2 * BH.card := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  rw [tsum_eq_sum (s := BH) (fun p hp => by
    unfold S9_Tp
    rw [ite_eq_right]
    intro h
    exact absurd (hBH p h.1) hp)]
  calc ∑ p ∈ BH, S9_Tp V w N kc s p ≤ ∑ p ∈ BH, (g0 V w / epsP (rhoN N) ^ 2) ^ 2 := by
        refine Finset.sum_le_sum fun p _ => ?_
        unfold S9_Tp
        split_ifs with h
        · rw [abs_mul, sq]
          exact mul_le_mul (E.hlamH p h.1.1) (E.hlamH (s - p) h.2.1) (abs_nonneg _)
            (by positivity)
        · positivity
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

private lemma S9_T'_sum_le {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {s v : Idx} (BH : Finset Idx) (hBH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH) :
    ∑' p : Idx, S9_Tp' V w N kc s v p ≤
      2 * (|lam V w (rhoN N) (LN N) v| * (g0 V w / epsP (rhoN N) ^ 2)) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  set B : ℝ := |lam V w (rhoN N) (LN N) v| * (g0 V w / epsP (rhoN N) ^ 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have hs1 := (hasSum_ite_eq v B).add (hasSum_ite_eq (s - v) B)
  have key : ∀ p, S9_Tp' V w N kc s v p ≤
      (if p = v then B else 0) + (if p = s - v then B else 0) := by
    intro p
    unfold S9_Tp' S9_Tp
    by_cases h : inPHc (rhoN N) (LN N) kc p ∧ inPHc (rhoN N) (LN N) kc (s - p)
    · simp only [h, and_self, ite_true]
      have hl : |lam V w (rhoN N) (LN N) p| ≤ g0 V w / epsP (rhoN N) ^ 2 := E.hlamH p h.1.1
      have hl' : |lam V w (rhoN N) (LN N) (s - p)| ≤ g0 V w / epsP (rhoN N) ^ 2 :=
        E.hlamH (s - p) h.2.1
      have hA : v = p → |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (s - p)| ≤ B := by
        intro h1
        rw [abs_mul, hB, ← h1]
        rw [h1]
        exact mul_le_mul_of_nonneg_left hl' (abs_nonneg _)
      have hA' : v = s - p →
          |lam V w (rhoN N) (LN N) p * lam V w (rhoN N) (LN N) (s - p)| ≤ B := by
        intro h1
        rw [abs_mul, hB, h1]
        calc |lam V w (rhoN N) (LN N) p| * |lam V w (rhoN N) (LN N) (s - p)|
            ≤ (g0 V w / epsP (rhoN N) ^ 2) * |lam V w (rhoN N) (LN N) (s - p)| :=
              mul_le_mul_of_nonneg_right hl (abs_nonneg _)
          _ = _ := by ring
      by_cases h1 : v = p <;> by_cases h2 : v = s - p
      · have e1 : p = v := h1.symm
        have e2 : p = s - v := by rw [h2]; abel
        rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left e1, ite_eq_left e2]
        have := hA h1
        linarith
      · have e1 : p = v := h1.symm
        rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left e1]
        have := hA h1
        have h3 : (0 : ℝ) ≤ if p = s - v then B else 0 := by split_ifs <;> simp [hB0]
        linarith
      · have e2 : p = s - v := by rw [h2]; abel
        rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left e2]
        have := hA' h2
        have h3 : (0 : ℝ) ≤ if p = v then B else 0 := by split_ifs <;> simp [hB0]
        linarith
      · rw [ite_eq_right h1, ite_eq_right h2]
        have h3 : (0 : ℝ) ≤ if p = v then B else 0 := by split_ifs <;> simp [hB0]
        have h4 : (0 : ℝ) ≤ if p = s - v then B else 0 := by split_ifs <;> simp [hB0]
        linarith
    · simp only [h, ite_false, zero_mul]
      have h3 : (0 : ℝ) ≤ if p = v then B else 0 := by split_ifs <;> simp [hB0]
      have h4 : (0 : ℝ) ≤ if p = s - v then B else 0 := by split_ifs <;> simp [hB0]
      linarith
  have hsm := (S9_Tp'_summable V w s v BH hBH)
  calc ∑' p : Idx, S9_Tp' V w N kc s v p ≤
        ∑' p : Idx, ((if p = v then B else 0) + (if p = s - v then B else 0)) :=
        hsm.tsum_le_tsum key hs1.summable
    _ = B + B := hs1.tsum_eq
    _ = _ := by rw [hB]; ring

private lemma S9_summable_F {N : ℕ} {Ψ : Occ → ℂ} (hΨ : IsNState N Ψ) (P : Occ → Prop)
    [DecidablePred P] (v : Idx) :
    Summable fun α : Occ => if P α then (α v : ℝ) * ‖Ψ α‖ ^ 2 else 0 := by
  have : (fun α : Occ => if P α then (α v : ℝ) * ‖Ψ α‖ ^ 2 else 0) =
      fun α => (if P α then (α v : ℝ) else 0) * ‖Ψ α‖ ^ 2 := by
    funext α; split_ifs <;> simp
  rw [this]
  refine S9_summable_w hΨ _ N (fun α h => ?_)
  split_ifs
  · rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hΨ h v
  · simp

/-- Pointwise: the two signs of the asymmetry. -/
private lemma S9_pt_split {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) {α : Occ} {u : Idx}
    (hu : inPL ρ L u) {x : ℝ} (hx : 0 ≤ x) :
    (if InMuA ρ L kc N u α then x else 0) ≤
      (if InM ρ L kc N α ∧ α (-u) = α u + 1 then x else 0) +
      (if InM ρ L kc N α ∧ α (-(-u)) = α (-u) + 1 then x else 0) := by
  have h1 := S9_ite_nonneg (InM ρ L kc N α ∧ α (-u) = α u + 1) hx
  have h2 := S9_ite_nonneg (InM ρ L kc N α ∧ α (-(-u)) = α (-u) + 1) hx
  by_cases hA : InMuA ρ L kc N u α
  · rw [S9_ite_pos hA]
    have s1 := MStar_PL_star hρ hA.1 hu
    have s2 := MStar_PL_star hρ hA.1 (Regions_PL_neg.2 hu)
    simp only [alphaStar, neg_neg] at s1 s2
    have hne : α u ≠ α (-u) := hA.2
    by_cases hp : α (-u) = α u + 1
    · rw [S9_ite_pos (P := InM ρ L kc N α ∧ α (-u) = α u + 1) ⟨hA.1, hp⟩]
      linarith
    · have hp' : α (-(-u)) = α (-u) + 1 := by rw [neg_neg]; omega
      rw [S9_ite_pos (P := InM ρ L kc N α ∧ α (-(-u)) = α (-u) + 1) ⟨hA.1, hp'⟩]
      linarith
  · have : (if InMuA ρ L kc N u α then x else 0) = 0 := by simp [hA]
    rw [this]
    linarith

/-- The two signs of the asymmetry. -/
private lemma S9_prop91_split (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) {u : Idx}
    (hu : inPL (rhoN N) (LN N) u) (v : Idx) :
    (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
        (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      (∑' α : Occ, if InM (rhoN N) (LN N) kc N α ∧ α (-u) = α u + 1 then
        (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) +
      (∑' α : Occ, if InM (rhoN N) (LN N) kc N α ∧ α (-(-u)) = α (-u) + 1 then
        (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have hΨ := Normalization_isNState V w kc hN
  have hF₁s := S9_summable_F hΨ (fun α => InM (rhoN N) (LN N) kc N α ∧ α (-u) = α u + 1) v
  have hF₂s := S9_summable_F hΨ
    (fun α => InM (rhoN N) (LN N) kc N α ∧ α (-(-u)) = α (-u) + 1) v
  have hFs := S9_summable_F hΨ (fun α => InMuA (rhoN N) (LN N) kc N u α) v
  rw [← hF₁s.tsum_add hF₂s]
  exact hFs.tsum_le_tsum (fun α => S9_pt_split hρ hu (by positivity)) (hF₁s.add hF₂s)

/-- The product of the two factors of the soft creation bound. -/
private lemma S9_factor {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {v : Idx} (hv : inPH (rhoN N) (LN N) v) (BH : Finset Idx)
    (hBH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH) (s : Idx) :
    ((∑' β : Occ, (if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0) *
          ‖trialState V w kc N β‖ ^ 2) * (∑' p : Idx, S9_Tp V w N kc s p) +
        (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N s β then
          ‖trialState V w kc N β‖ ^ 2 else 0) * (∑' p : Idx, S9_Tp' V w N kc s v p)) ≤
      (C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) v| / epsP (rhoN N) ^ 2) *
          ((g0 V w / epsP (rhoN N) ^ 2) ^ 2 * BH.card) +
        2 * (|lam V w (rhoN N) (LN N) v| * (g0 V w / epsP (rhoN N) ^ 2)) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  set Ψ := trialState V w kc N with hΨdef
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have hsq : Summable fun α : Occ => ‖Ψ α‖ ^ 2 := hΨ.1.summable
  have hsm : Summable fun β : Occ => (if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0) *
      ‖Ψ β‖ ^ 2 := by
    refine S9_summable_w hΨ _ N (fun β hβ => ?_)
    split_ifs
    · rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hΨ hβ v
    · simp
  have hQs : Summable fun β : Occ => (β v : ℝ) * ‖Ψ β‖ ^ 2 :=
    S9_summable_w hΨ (fun β => (β v : ℝ)) N (fun β hβ => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hΨ hβ v)
  have h1 : ∑' β : Occ, (if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0) *
      ‖Ψ β‖ ^ 2 ≤ Expect.Q Ψ [v] := by
    rw [S9_Q1_eq]
    refine hsm.tsum_le_tsum (fun β => ?_) hQs
    by_cases hb : InMuS (rhoN N) (LN N) kc N s β
    · simp [hb]
    · simp only [hb, ite_false, zero_mul]; positivity
  have hQ : (∑' β : Occ, (if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0) *
      ‖Ψ β‖ ^ 2) ≤ C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) v| / epsP (rhoN N) ^ 2 := by
    refine h1.trans ((E.hQ1 kc v hv).trans ?_)
    have h3 : epsP (rhoN N) < ‖mom (LN N) v‖ := hv
    have h4 : epsP (rhoN N) ^ 2 ≤ ‖mom (LN N) v‖ ^ 2 := pow_le_pow_left₀ ht.le h3.le 2
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h4
  have hS1 : (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N s β then ‖Ψ β‖ ^ 2 else 0) ≤ 1 := by
    have := (S9_summable_ite hsq (fun _ => by positivity)
      (fun β => InMuS (rhoN N) (LN N) kc N s β)).tsum_le_tsum
      (fun β => by split_ifs <;> simp) hsq
    rw [hΨ.1.tsum_eq] at this
    exact this
  have hT := S9_T_sum_le E kc s BH hBH
  have hT' := S9_T'_sum_le E kc (s := s) (v := v) BH hBH
  have hT0 : 0 ≤ ∑' p : Idx, S9_Tp V w N kc s p := tsum_nonneg (S9_Tp_nonneg V w N kc s)
  have hQ0 : 0 ≤ ∑' β : Occ, (if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0) *
      ‖Ψ β‖ ^ 2 := tsum_nonneg (fun β => by split_ifs <;> positivity)
  have hS10 : 0 ≤ ∑' β : Occ, if InMuS (rhoN N) (LN N) kc N s β then ‖Ψ β‖ ^ 2 else 0 :=
    tsum_nonneg (fun β => by split_ifs <;> positivity)
  have hT'0 : 0 ≤ ∑' p : Idx, S9_Tp' V w N kc s v p := tsum_nonneg (S9_Tp'_nonneg V w N kc s v)
  have step1 : (∑' β : Occ, (if InMuS (rhoN N) (LN N) kc N s β then (β v : ℝ) else 0) *
      ‖Ψ β‖ ^ 2) * (∑' p : Idx, S9_Tp V w N kc s p) ≤
      (C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) v| / epsP (rhoN N) ^ 2) *
        ((g0 V w / epsP (rhoN N) ^ 2) ^ 2 * BH.card) :=
    mul_le_mul hQ hT hT0 (hQ0.trans hQ)
  have step2 : (∑' β : Occ, if InMuS (rhoN N) (LN N) kc N s β then ‖Ψ β‖ ^ 2 else 0) *
      (∑' p : Idx, S9_Tp' V w N kc s v p) ≤
      1 * (2 * (|lam V w (rhoN N) (LN N) v| * (g0 V w / epsP (rhoN N) ^ 2))) :=
    mul_le_mul hS1 hT' hT'0 zero_le_one
  linarith only [step1, step2]

/-- Proposition 9.1, (9.4) [temp8.119], the explicit bound: `u ∈ P_L`, `v ∈ P_H`. -/
private lemma S9_prop91_core {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {u v : Idx} (hu : inPL (rhoN N) (LN N) u) (hv : inPH (rhoN N) (LN N) v)
    (BH : Finset Idx) (hBH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH) :
    (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
        (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
      2 * (4 * rhoN N * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3 *
        ((C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) v| / epsP (rhoN N) ^ 2) *
          ((g0 V w / epsP (rhoN N) ^ 2) ^ 2 * BH.card) +
        2 * (|lam V w (rhoN N) (LN N) v| * (g0 V w / epsP (rhoN N) ^ 2)))) := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have hnu := Regions_PL_neg.2 hu
  have hc₀ : 0 ≤ 4 * rhoN N * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3 := by positivity
  have b1 := S9_soft_pos E kc hu hv BH hBH
  have b2 := S9_soft_pos E kc hnu hv BH hBH
  have c1 := S9_factor E hC kc hv BH hBH u
  have c2 := S9_factor E hC kc hv BH hBH (-u)
  have e1 := mul_le_mul_of_nonneg_left c1 hc₀
  have e2 := mul_le_mul_of_nonneg_left c2 hc₀
  refine (S9_prop91_split V w kc E.hN hu v).trans ?_
  refine (add_le_add b1 b2).trans ?_
  refine (add_le_add e1 e2).trans (le_of_eq ?_)
  ring

/-- The arithmetic of Proposition 9.1. -/
private lemma S9_arith91 (V w : R3 → ℝ) {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    {K a : ℝ} (hK : 1 ≤ K) (ha : 0 ≤ a) {cd : ℝ} (hcd0 : 0 ≤ cd)
    (hcd : cd ≤ 67 * (LN N ^ 3 * K ^ 3)) :
    2 * (4 * rhoN N * (⌈mc (rhoN N)⌉₊ : ℝ) / LN N ^ 3 *
        ((C * rhoN N ^ 2 * a / epsP (rhoN N) ^ 2) *
          ((g0 V w / epsP (rhoN N) ^ 2) ^ 2 * cd) +
        2 * (a * (g0 V w / epsP (rhoN N) ^ 2)))) ≤
      (1072 * C * g0 V w ^ 2) * K ^ 3 * a * epsP (rhoN N) ^ 593 +
        (32 * g0 V w) * a * epsP (rhoN N) ^ 197 / LN N ^ 3 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have ht1 := S9_eps_le_one hρ hρ1
  have hg := E.hg
  have hm := S9_ceil_le hρ hρ1
  have hm0 : (0 : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := Nat.cast_nonneg _
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  have hL3 : 0 < LN N ^ 3 := by positivity
  generalize (⌈mc (rhoN N)⌉₊ : ℝ) = m at hm hm0 ⊢
  generalize LN N ^ 3 = Λ at hL3 hcd ⊢
  generalize epsP (rhoN N) = t at ht hm hr ⊢
  rw [hr]
  have hK3 : 0 ≤ K ^ 3 := by positivity
  have hgt : 0 ≤ g0 V w / t ^ 2 := by positivity
  calc 2 * (4 * t ^ 200 * m / Λ * ((C * (t ^ 200) ^ 2 * a / t ^ 2) *
        ((g0 V w / t ^ 2) ^ 2 * cd) + 2 * (a * (g0 V w / t ^ 2))))
      ≤ 2 * (4 * t ^ 200 * (2 * t⁻¹) / Λ * ((C * (t ^ 200) ^ 2 * a / t ^ 2) *
        ((g0 V w / t ^ 2) ^ 2 * (67 * (Λ * K ^ 3))) + 2 * (a * (g0 V w / t ^ 2)))) := by
        gcongr
    _ = (1072 * C * g0 V w ^ 2) * K ^ 3 * a * t ^ 593 + (32 * g0 V w) * a * t ^ 197 / Λ := by
        field_simp
        ring

/-- Proposition 9.1, (9.4) [temp8.119] with the rate, for every real `k_c` (with
`max k_c 1`): `Σ_{M_u^a} α(v)|Ψ(α)|² ≤ C max(k_c,1)³ |λ_v| ε^{593} + C |λ_v| ε^{197} |Λ|⁻¹`. -/
private lemma S9_prop91_rate {V w : R3 → ℝ} (hV : PotentialHyp V)
    (hw : IsScatteringSolution V w) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, ∀ u v : Idx,
      inPL (rhoN N) (LN N) u → inPHc (rhoN N) (LN N) kc v →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
          (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C' * (max kc 1) ^ 3 * |lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 593 +
          C' * |lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 197 / LN N ^ 3 := by
  obtain ⟨C, hC, hev⟩ := S9_env hV hw
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  have hg := scat_g0_pos hV hw
  refine ⟨1072 * C * g0 V w ^ 2 + 32 * g0 V w, by positivity, N₀, fun N hN kc u v hu hv => ?_⟩
  have E := hN₀ N hN
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  set K := max kc 1 with hKdef
  have hK : 1 ≤ K := le_max_right _ _
  set BH := S9_ball (LN N) K with hBH
  have hmH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH := fun n hn =>
    S9_mem_ball hL (hn.2.trans (le_max_left _ _))
  have hcard := S9_card_PH E.hN K hK
  have hcore := S9_prop91_core E hC kc hu hv.1 BH hmH
  refine hcore.trans ((S9_arith91 V w E hC hK (abs_nonneg _) (Nat.cast_nonneg _) hcard).trans ?_)
  have h1 : 0 ≤ K ^ 3 * |lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 593 := by positivity
  have h2 : 0 ≤ |lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 197 / LN N ^ 3 := by positivity
  have hc1 : 1072 * C * g0 V w ^ 2 ≤ 1072 * C * g0 V w ^ 2 + 32 * g0 V w := by linarith
  have hc2 : 32 * g0 V w ≤ 1072 * C * g0 V w ^ 2 + 32 * g0 V w := by
    have : 0 ≤ 1072 * C * g0 V w ^ 2 := by positivity
    linarith
  calc 1072 * C * g0 V w ^ 2 * K ^ 3 * |lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 593 +
        32 * g0 V w * |lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 197 / LN N ^ 3
      = 1072 * C * g0 V w ^ 2 * (K ^ 3 * |lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 593) +
        32 * g0 V w * (|lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 197 / LN N ^ 3) := by ring
    _ ≤ (1072 * C * g0 V w ^ 2 + 32 * g0 V w) *
          (K ^ 3 * |lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 593) +
        (1072 * C * g0 V w ^ 2 + 32 * g0 V w) *
          (|lam V w (rhoN N) (LN N) v| * epsP (rhoN N) ^ 197 / LN N ^ 3) := by
        gcongr
    _ = _ := by ring

private lemma S9_rho_nonneg (N : ℕ) : 0 ≤ rhoN N := by unfold rhoN; positivity

/-! ### Class 3: one `P_L` and one `P_{H,c}` leg on each side -/

/-- `K ρ⁻¹ (g₀/ε²) / (N^j ℓ)`: the constant of the amplitude comparison in class 3. -/
private def S9_E (V w : R3 → ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  rhoN N ^ (-(1 / 10 : ℝ)) * ((rhoN N)⁻¹ * (g0 V w / epsP (rhoN N) ^ 2)) /
    ((N : ℝ) ^ j * (g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹))

private lemma S9_E_nonneg (V w : R3 → ℝ) {N : ℕ} (hN : 1 ≤ N) (hg : 0 < g0 V w) (j : ℕ) :
    0 ≤ S9_E V w N j := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have ht := S9_eps_pos hρ
  unfold S9_E
  have : 0 ≤ rhoN N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hρ.le _
  positivity

/-- `|λ_v| > 0` when some state with `α(v) ≥ 1` has nonzero amplitude, by (5.15). -/
private lemma S9_lam_pos {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {v : Idx} (hv : inPH (rhoN N) (LN N) v) {b : Occ} (hb : 1 ≤ b v)
    (hΨ : trialState V w kc N b ≠ 0) : 0 < |lam V w (rhoN N) (LN N) v| := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hN := Normalization_isNState V w kc E.hN
  have ht := S9_eps_pos hρ
  have hQs : Summable fun β : Occ => (β v : ℝ) * ‖trialState V w kc N β‖ ^ 2 :=
    S9_summable_w hN (fun β => (β v : ℝ)) N (fun β hβ => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hN hβ v)
  have h1 : (b v : ℝ) * ‖trialState V w kc N b‖ ^ 2 ≤ Expect.Q (trialState V w kc N) [v] := by
    rw [S9_Q1_eq]
    exact hQs.le_tsum b (fun j _ => by positivity)
  have h2 := E.hQ1 kc v hv
  have hb' : (1 : ℝ) ≤ b v := by exact_mod_cast hb
  have hpos : 0 < ‖trialState V w kc N b‖ ^ 2 := by
    have : 0 < ‖trialState V w kc N b‖ := norm_pos_iff.2 hΨ
    positivity
  by_contra hcon
  have h0 : |lam V w (rhoN N) (LN N) v| = 0 :=
    le_antisymm (not_lt.1 hcon) (abs_nonneg _)
  rw [h0] at h2
  simp at h2
  nlinarith

/-- A bound for `c` from `c² = p W`, `p ≤ m²`, `W ≥ 1`. -/
private lemma S9_c_le_W {c m p W : ℝ} (hm0 : 0 ≤ m) (hW1 : 1 ≤ W) (hp : p ≤ m * m)
    (hc : c ^ 2 = p * W) : c ≤ m * W := by
  apply S9_c_le (by positivity)
  rw [hc]
  calc p * W ≤ (m * m) * W := mul_le_mul_of_nonneg_right hp (by linarith)
    _ ≤ (m * m) * (W * W) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right (by linarith) hW1)
        (mul_nonneg hm0 hm0)
    _ = (m * W) ^ 2 := by ring

/-- The amplitude comparison of class 3, with the weight `|λ_{v₂}|` on the ket. -/
private lemma S9_amp3_bra {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N)
    {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁)
    (h₃ : inPL (rhoN N) (LN N) v₃) (h₄ : inPH (rhoN N) (LN N) v₄) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (j : ℕ) (hlam2 : 0 < |lam V w (rhoN N) (LN N) v₂|)
    (h : (N : ℝ) ^ j * (x * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (y * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|)) :
    x ≤ S9_E V w N j / |lam V w (rhoN N) (LN N) v₂| * y := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have l1 := S9_lamPL E h₁
  have l3 := S9_lamPL E h₃
  have l4 := E.hlamH v₄ h₄
  have hℓ : 0 < g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹ := by positivity
  have hK : 0 ≤ rhoN N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hρ.le _
  have hB : |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄| ≤
      (rhoN N)⁻¹ * (g0 V w / epsP (rhoN N) ^ 2) := by
    rw [abs_mul]; exact mul_le_mul l3.2 l4 (abs_nonneg _) (inv_pos.2 hρ).le
  have h' : (N : ℝ) ^ j * ((x * |lam V w (rhoN N) (LN N) v₂|) * |lam V w (rhoN N) (LN N) v₁|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (y * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|) := by
    rw [abs_mul] at h
    calc _ = (N : ℝ) ^ j * (x * (|lam V w (rhoN N) (LN N) v₁| *
          |lam V w (rhoN N) (LN N) v₂|)) := by ring
      _ ≤ _ := h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast E.hN
  have := S9_amp_ratio (M := (N : ℝ) ^ j) (by positivity) hℓ (by positivity) hy l1.1 hB hK h'
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam2]
  unfold S9_E
  exact this

/-- The amplitude comparison of class 3, with the weight `|λ_{v₄}|` on the bra. -/
private lemma S9_amp3_ket {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N)
    {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPH (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hlam4 : 0 < |lam V w (rhoN N) (LN N) v₄|)
    (h : (N : ℝ) ^ 2 * (y * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (x * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|)) :
    y ≤ S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄| * x := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have l1 := S9_lamPL E h₁
  have l3 := S9_lamPL E h₃
  have l2 := E.hlamH v₂ h₂
  have hℓ : 0 < g0 V w / 2 * epsP (rhoN N) ^ 2 * (rhoN N)⁻¹ := by positivity
  have hK : 0 ≤ rhoN N ^ (-(1 / 10 : ℝ)) := Real.rpow_nonneg hρ.le _
  have hB : |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂| ≤
      (rhoN N)⁻¹ * (g0 V w / epsP (rhoN N) ^ 2) := by
    rw [abs_mul]; exact mul_le_mul l1.2 l2 (abs_nonneg _) (inv_pos.2 hρ).le
  have h' : (N : ℝ) ^ 2 * ((y * |lam V w (rhoN N) (LN N) v₄|) * |lam V w (rhoN N) (LN N) v₃|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (x * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|) := by
    rw [abs_mul] at h
    calc _ = (N : ℝ) ^ 2 * (y * (|lam V w (rhoN N) (LN N) v₃| *
          |lam V w (rhoN N) (LN N) v₄|)) := by ring
      _ ≤ _ := h
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast E.hN
  have := S9_amp_ratio (M := (N : ℝ) ^ 2) (by positivity) hℓ (by positivity) hx l3.1 hB hK h'
  rw [div_mul_eq_mul_div, le_div_iff₀ hlam4]
  unfold S9_E
  exact this


/-- Class 3: the pointwise bound for a nonzero matrix element between two `M` states. -/
private lemma S9_pt3 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (kc : ℝ)
    {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPH (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) (h₄ : inPH (rhoN N) (LN N) v₄)
    (hGen : S9_Gen4 v₁ v₂ v₃ v₄) (κ : Occ) (hc : (a4 v₁ v₂ v₃ v₄ κ).1 ≠ 0) :
    S9_s (trialState V w kc N) v₁ v₂ v₃ v₄ κ ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) *
          Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|) *
          (((((a4 v₁ v₂ v₃ v₄ κ).2 v₄ : ℝ) + 1) * ((a4 v₁ v₂ v₃ v₄ κ).2 v₂ : ℝ)) *
            ‖trialState V w kc N (a4 v₁ v₂ v₃ v₄ κ).2‖ ^ 2) +
        (⌈mc (rhoN N)⌉₊ : ℝ) *
          Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|) *
          (((((a4 v₁ v₂ v₃ v₄ κ).2 v₄ : ℝ) + 1) * ((a4 v₁ v₂ v₃ v₄ κ).2 v₂ : ℝ)) *
            ((if InMuA (rhoN N) (LN N) kc N v₁ (a4 v₁ v₂ v₃ v₄ κ).2 then 1 else 0) +
              (if InMuA (rhoN N) (LN N) kc N v₃ (a4 v₁ v₂ v₃ v₄ κ).2 then 1 else 0)) *
            ‖trialState V w kc N (a4 v₁ v₂ v₃ v₄ κ).2‖ ^ 2) +
        (⌈mc (rhoN N)⌉₊ : ℝ) *
          Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|) *
          (((κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1)) * ‖trialState V w kc N κ‖ ^ 2) := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  set Ψ := trialState V w kc N with hΨ
  set b := (a4 v₁ v₂ v₃ v₄ κ).2 with hb
  set c := (a4 v₁ v₂ v₃ v₄ κ).1 with hcdef
  set m : ℝ := (⌈mc (rhoN N)⌉₊ : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hg := E.hg
  have ht := S9_eps_pos hρ
  have hxn : 0 ≤ ‖Ψ κ‖ ^ 2 := by positivity
  have hyn : 0 ≤ ‖Ψ b‖ ^ 2 := by positivity
  have hE2 := S9_E_nonneg V w E.hN hg 2
  have hE0 := S9_E_nonneg V w E.hN hg 0
  have hW1 : 0 ≤ (if InMuA (rhoN N) (LN N) kc N v₁ b then (1 : ℝ) else 0) +
      (if InMuA (rhoN N) (LN N) kc N v₃ b then (1 : ℝ) else 0) := by
    have := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N v₁ b) (zero_le_one' ℝ)
    have := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N v₃ b) (zero_le_one' ℝ)
    linarith
  have hbn : 0 ≤ ((b v₄ : ℝ) + 1) * (b v₂ : ℝ) := by positivity
  have hkn : 0 ≤ (κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1) := by positivity
  have s2 := Real.sqrt_nonneg (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|)
  have s0 := Real.sqrt_nonneg (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|)
  have s4 := Real.sqrt_nonneg (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|)
  have t1 : 0 ≤ m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|) *
          ((((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) * ‖Ψ b‖ ^ 2) := by positivity
  have t2 : 0 ≤ m * Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|) *
          ((((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) *
            ((if InMuA (rhoN N) (LN N) kc N v₁ b then 1 else 0) +
              (if InMuA (rhoN N) (LN N) kc N v₃ b then 1 else 0)) * ‖Ψ b‖ ^ 2) := by
    positivity
  have t3 : 0 ≤ m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|) *
          (((κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1)) * ‖Ψ κ‖ ^ 2) := by positivity
  by_cases hΨκ : Ψ κ = 0
  · have : S9_s Ψ v₁ v₂ v₃ v₄ κ = 0 := by rw [S9_s_eq, hΨκ]; simp
    rw [this]; linarith only [t1, t2, t3]
  by_cases hΨb : Ψ b = 0
  · have : S9_s Ψ v₁ v₂ v₃ v₄ κ = 0 := by rw [S9_s_eq, hΨb]; simp
    rw [this]; linarith only [t1, t2, t3]
  have hκM : InM (rhoN N) (LN N) kc N κ := S9_inM hΨκ
  have hbM : InM (rhoN N) (LN N) kc N b := S9_inM hΨb
  have hn2 : ¬ inPL (rhoN N) (LN N) v₂ := fun h => Regions_PL_PH hρ h h₂
  have hn4 : ¬ inPL (rhoN N) (LN N) v₄ := fun h => Regions_PL_PH hρ h h₄
  have h0 : ∀ i : Fin 4, ![v₁, v₂, v₃, v₄] i ≠ 0 := by
    intro i
    fin_cases i
    exacts [Regions_PL_ne_zero hρ h₁, Regions_PH_ne_zero hρ h₂, Regions_PL_ne_zero hρ h₃,
      Regions_PH_ne_zero hρ h₄]
  have hF := Lemma9_1_F hρ h0 hGen hbM hκM hc rfl
  rw [S9_card4] at hF
  simp only [h₁, h₃, hn2, hn4, ite_true, ite_false] at hF
  have hrat : ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ *
        (‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b *
        (‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|)) ∧
      ((N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b *
        (‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ * lam V w (rhoN N) (LN N) v₄|) ≤
      rhoN N ^ (-(1 / 10 : ℝ)) * (N : ℝ) ^ Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ *
        (‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ * lam V w (rhoN N) (LN N) v₂|)) :=
    E.hratio kc b κ ![v₁, v₂, v₃, v₄] h0 hGen hbM hκM hc rfl
  obtain ⟨p12, p13, p14, p23, p24, p34⟩ := (S9_Gen4_iff _ _ _ _).1 hGen
  obtain ⟨o1, o2, o3, o4, q3, q4, q1, q2, hsq⟩ :=
    S9_occ hc p12.1 p34.1 p13.1 p14.1 p23.1 p24.1
  have hc0 : 0 ≤ c := a4_fst_nonneg _ _ _ _ _
  have e1 : ((b v₁ : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (S9_occ_ceil hρ hbM h₁)
  have e3 : ((κ v₃ : ℕ) : ℝ) ≤ m := Nat.cast_le.2 (S9_occ_ceil hρ hκM h₃)
  have o2' : (b v₂ : ℝ) = (κ v₂ : ℝ) + 1 := by exact_mod_cast o2
  have o4' : ((κ v₄ : ℕ) : ℝ) = (b v₄ : ℝ) + 1 := by exact_mod_cast o4
  have hp0 : 0 ≤ (κ v₃ : ℝ) * (b v₁ : ℝ) := by positivity
  have hp : (κ v₃ : ℝ) * (b v₁ : ℝ) ≤ m * m := mul_le_mul e3 e1 (Nat.cast_nonneg _) hm0
  have hWb1 : (1 : ℝ) ≤ ((b v₄ : ℝ) + 1) * (b v₂ : ℝ) := by
    have a : (1 : ℝ) ≤ (b v₄ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (b v₄)]
    have b' : (1 : ℝ) ≤ (b v₂ : ℝ) := by exact_mod_cast q2
    exact one_le_mul_of_one_le_of_one_le a b'
  have hWk1 : (1 : ℝ) ≤ (κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1) := by
    have a : (1 : ℝ) ≤ (κ v₄ : ℝ) := by exact_mod_cast q4
    have b' : (1 : ℝ) ≤ (κ v₂ : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) (κ v₂)]
    exact one_le_mul_of_one_le_of_one_le a b'
  have hcb : c ≤ m * (((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) :=
    S9_c_le_W hm0 hWb1 hp (by rw [hsq, o4']; ring)
  have hck : c ≤ m * ((κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1)) :=
    S9_c_le_W hm0 hWk1 hp (by rw [hsq, o2']; ring)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast E.hN
  have hspos : S9_s Ψ v₁ v₂ v₃ v₄ κ = ‖Ψ b‖ * c * ‖Ψ κ‖ := S9_s_eq _ _ _ _ _ _
  have hp' : 0 ≤ ‖Ψ κ‖ := norm_nonneg _
  have hq' : 0 ≤ ‖Ψ b‖ := norm_nonneg _
  rcases (by omega : Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b = 0 ∨
      Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b = 1 ∨
      Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b = 2) with ha | ha | ha
  · -- bra, `F(β) = 0`
    have h1 := S9_pow_cancel hN1 (z := ‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ *
        lam V w (rhoN N) (LN N) v₂|) (z' := ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ *
        lam V w (rhoN N) (LN N) v₄|) (K := rhoN N ^ (-(1 / 10 : ℝ)))
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) 2
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ) (by positivity) (by omega)
      (by simpa only [mul_assoc] using hrat.1)
    have hl2 := S9_lam_pos E kc h₂ q2 hΨb
    have h2 := S9_amp3_bra E h₁ h₃ h₄ hxn hyn 2 hl2 h1
    have h3 : ‖Ψ κ‖ * ‖Ψ b‖ ≤ Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|) *
        ‖Ψ b‖ ^ 2 := S9_amp_sq hq' (div_nonneg hE2 hl2.le) h2
    have h4 : S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ m * Real.sqrt (S9_E V w N 2 /
        |lam V w (rhoN N) (LN N) v₂|) * ((((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) * ‖Ψ b‖ ^ 2) := by
      rw [hspos]
      calc ‖Ψ b‖ * c * ‖Ψ κ‖ = c * (‖Ψ κ‖ * ‖Ψ b‖) := by ring
        _ ≤ (m * (((b v₄ : ℝ) + 1) * (b v₂ : ℝ))) *
            (Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|) * ‖Ψ b‖ ^ 2) :=
          mul_le_mul hcb h3 (by positivity) (by positivity)
        _ = _ := by ring
    linarith only [h4, t2, t3]
  · -- bra, `F(β) = 1`
    have h1 := S9_pow_cancel hN1 (z := ‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ *
        lam V w (rhoN N) (LN N) v₂|) (z' := ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ *
        lam V w (rhoN N) (LN N) v₄|) (K := rhoN N ^ (-(1 / 10 : ℝ)))
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) 0
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ) (by positivity) (by omega)
      (by simpa only [mul_assoc] using hrat.1)
    have hl2 := S9_lam_pos E kc h₂ q2 hΨb
    have h2 := S9_amp3_bra E h₁ h₃ h₄ hxn hyn 0 hl2 h1
    have h3 : ‖Ψ κ‖ * ‖Ψ b‖ ≤ Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|) *
        ‖Ψ b‖ ^ 2 := S9_amp_sq hq' (div_nonneg hE0 hl2.le) h2
    -- one of the two `P_L` legs carries the asymmetry
    have hFb := ha
    rw [S9_Fal4] at hFb
    simp only [h₁, h₃, hn2, hn4, ite_true, ite_false] at hFb
    have hW1ge : (1 : ℝ) ≤ (if InMuA (rhoN N) (LN N) kc N v₁ b then 1 else 0) +
        (if InMuA (rhoN N) (LN N) kc N v₃ b then 1 else 0) := by
      have i1 := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N v₁ b) (zero_le_one' ℝ)
      have i3 := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N v₃ b) (zero_le_one' ℝ)
      rcases (by omega : Int.natAbs ((b v₁ : ℤ) - b (-v₁)) = 1 ∨
          Int.natAbs ((b v₃ : ℤ) - b (-v₃)) = 1) with k | k
      · rw [S9_ite_pos (P := InMuA (rhoN N) (LN N) kc N v₁ b) (S9_asym_one hbM k)]
        linarith
      · rw [S9_ite_pos (P := InMuA (rhoN N) (LN N) kc N v₃ b) (S9_asym_one hbM k)]
        linarith
    have h4 : S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ m * Real.sqrt (S9_E V w N 0 /
        |lam V w (rhoN N) (LN N) v₂|) * ((((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N v₁ b then 1 else 0) +
          (if InMuA (rhoN N) (LN N) kc N v₃ b then 1 else 0)) * ‖Ψ b‖ ^ 2) := by
      rw [hspos]
      have h5 : ‖Ψ b‖ ^ 2 ≤ ((if InMuA (rhoN N) (LN N) kc N v₁ b then 1 else 0) +
          (if InMuA (rhoN N) (LN N) kc N v₃ b then 1 else 0)) * ‖Ψ b‖ ^ 2 :=
        le_mul_of_one_le_left hyn hW1ge
      calc ‖Ψ b‖ * c * ‖Ψ κ‖ = c * (‖Ψ κ‖ * ‖Ψ b‖) := by ring
        _ ≤ (m * (((b v₄ : ℝ) + 1) * (b v₂ : ℝ))) *
            (Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|) * ‖Ψ b‖ ^ 2) :=
          mul_le_mul hcb h3 (by positivity) (by positivity)
        _ ≤ (m * (((b v₄ : ℝ) + 1) * (b v₂ : ℝ))) *
            (Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|) *
              (((if InMuA (rhoN N) (LN N) kc N v₁ b then 1 else 0) +
                (if InMuA (rhoN N) (LN N) kc N v₃ b then 1 else 0)) * ‖Ψ b‖ ^ 2)) := by
          gcongr
        _ = _ := by ring
    linarith only [h4, t1, t3]
  · -- ket, `F(β) = 2`
    have h1 := S9_pow_cancel hN1 (z := ‖Ψ b‖ ^ 2 * |lam V w (rhoN N) (LN N) v₃ *
        lam V w (rhoN N) (LN N) v₄|) (z' := ‖Ψ κ‖ ^ 2 * |lam V w (rhoN N) (LN N) v₁ *
        lam V w (rhoN N) (LN N) v₂|) (K := rhoN N ^ (-(1 / 10 : ℝ)))
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] κ) 2
      (Fal (rhoN N) (LN N) ![v₁, v₂, v₃, v₄] b) (by positivity) (by omega)
      (by simpa only [mul_assoc] using hrat.2)
    have hl4 := S9_lam_pos E kc h₄ q4 hΨκ
    have h2 := S9_amp3_ket E h₁ h₂ h₃ hxn hyn hl4 h1
    have h3 : ‖Ψ b‖ * ‖Ψ κ‖ ≤ Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|) *
        ‖Ψ κ‖ ^ 2 := S9_amp_sq hp' (div_nonneg hE2 hl4.le) h2
    have h4 : S9_s Ψ v₁ v₂ v₃ v₄ κ ≤ m * Real.sqrt (S9_E V w N 2 /
        |lam V w (rhoN N) (LN N) v₄|) * (((κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1)) * ‖Ψ κ‖ ^ 2) := by
      rw [hspos]
      calc ‖Ψ b‖ * c * ‖Ψ κ‖ = c * (‖Ψ b‖ * ‖Ψ κ‖) := by ring
        _ ≤ (m * ((κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1))) *
            (Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|) * ‖Ψ κ‖ ^ 2) :=
          mul_le_mul hck h3 (by positivity) (by positivity)
        _ = _ := by ring
    linarith only [h4, t1, t2]

/-- `√(E/λ) λ ≤ √(E G)` for `0 ≤ λ ≤ G`. -/
private lemma S9_sqrt_div_mul {E l G : ℝ} (hE : 0 ≤ E) (hl : 0 ≤ l) (hG : l ≤ G) :
    Real.sqrt (E / l) * l ≤ Real.sqrt (E * G) := by
  rcases hl.eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  have h1 : Real.sqrt (E / l) * l = Real.sqrt (E * l) := by
    have : Real.sqrt (E / l) * Real.sqrt (l * l) = Real.sqrt ((E / l) * (l * l)) :=
      (Real.sqrt_mul (div_nonneg hE hpos.le) _).symm
    rw [Real.sqrt_mul_self hpos.le] at this
    rw [this]
    congr 1
    field_simp
  rw [h1]
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hG hE)

/-- `Σ_α α(x)(α(y) + 1)|Ψ(α)|² ≤ |λ_x|(C (g₀/ε²) ρ⁴/ε⁴ + C ρ²/ε²)` on `P_H`, by (5.15) and
(5.42). -/
private lemma S9_Qsum {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {x y : Idx} (hx : inPH (rhoN N) (LN N) x) (hy : inPH (rhoN N) (LN N) y)
    (hxy : Legs_pm x y) :
    ∑' α : Occ, (((α x : ℝ)) * ((α y : ℝ) + 1)) * ‖trialState V w kc N α‖ ^ 2 ≤
      |lam V w (rhoN N) (LN N) x| * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4 + C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  rw [S9_sum_succ1 hΨ x y]
  have hQ2 := E.hQ2 kc x y hx hy hxy.1 (S9_ne_of_pm hxy)
  have hQ1 := E.hQ1 kc x hx
  have hly := E.hlamH y hy
  have h3 : epsP (rhoN N) < ‖mom (LN N) x‖ := hx
  have h4 : epsP (rhoN N) ^ 2 ≤ ‖mom (LN N) x‖ ^ 2 := pow_le_pow_left₀ ht.le h3.le 2
  have hQ1' : Expect.Q (trialState V w kc N) [x] ≤
      C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) x| / epsP (rhoN N) ^ 2 := by
    refine hQ1.trans ?_
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) h4
  have hQ2' : Expect.Q (trialState V w kc N) [x, y] ≤
      |lam V w (rhoN N) (LN N) x| * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4) := by
    refine hQ2.trans ?_
    rw [abs_mul]
    have : C * (|lam V w (rhoN N) (LN N) x| * |lam V w (rhoN N) (LN N) y|) * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4 = |lam V w (rhoN N) (LN N) x| * (C * |lam V w (rhoN N) (LN N) y| *
          rhoN N ^ 4 / epsP (rhoN N) ^ 4) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hly hC) (by positivity)
  calc Expect.Q (trialState V w kc N) [x, y] + Expect.Q (trialState V w kc N) [x]
      ≤ |lam V w (rhoN N) (LN N) x| * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4) + C * rhoN N ^ 2 * |lam V w (rhoN N) (LN N) x| /
          epsP (rhoN N) ^ 2 := add_le_add hQ2' hQ1'
    _ = _ := by ring


private lemma S9_ptW (X Y z : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hz : 0 ≤ z) (P Q : Prop)
    [Decidable P] [Decidable Q] :
    ((Y + 1) * X) * ((if P then (1 : ℝ) else 0) + (if Q then (1 : ℝ) else 0)) * z ≤
      2 * (X * Y * z) + (if P then X * z else 0) + (if Q then X * z else 0) := by
  have h1 : 0 ≤ X * Y * z := mul_nonneg (mul_nonneg hX hY) hz
  have h2 : 0 ≤ X * z := mul_nonneg hX hz
  split_ifs <;> nlinarith

/-- The weighted sum with the two asymmetry events of the `P_L` legs. -/
private lemma S9_QsumW {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {x y u₁ u₃ : Idx} (hx : inPH (rhoN N) (LN N) x) (hy : inPH (rhoN N) (LN N) y)
    (hxy : Legs_pm x y) {Pb : ℝ}
    (hP₁ : (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u₁ α then
        (α x : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤ Pb * |lam V w (rhoN N) (LN N) x|)
    (hP₃ : (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u₃ α then
        (α x : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤ Pb * |lam V w (rhoN N) (LN N) x|) :
    ∑' α : Occ, (((α y : ℝ) + 1) * (α x : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N u₁ α then (1 : ℝ) else 0) +
          (if InMuA (rhoN N) (LN N) kc N u₃ α then (1 : ℝ) else 0)) *
        ‖trialState V w kc N α‖ ^ 2 ≤
      |lam V w (rhoN N) (LN N) x| * (2 * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4) + 2 * Pb) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have bd : ∀ (f : Occ → ℝ) (B : ℝ), (∀ α, trialState V w kc N α ≠ 0 → |f α| ≤ B) →
      Summable fun α : Occ => f α * ‖trialState V w kc N α‖ ^ 2 :=
    fun f B h => S9_summable_w hΨ f B h
  have h3 : Summable fun α : Occ => (α x : ℝ) * α y * ‖trialState V w kc N α‖ ^ 2 :=
    bd _ (N * N) (fun α h => by
      rw [abs_of_nonneg (by positivity)]
      have a := S9_occ_le hΨ h x
      have b := S9_occ_le hΨ h y
      have : (α x : ℝ) ≤ N := by exact_mod_cast a
      have : (α y : ℝ) ≤ N := by exact_mod_cast b
      gcongr)
  have hF₁ := S9_summable_F hΨ (fun α => InMuA (rhoN N) (LN N) kc N u₁ α) x
  have hF₃ := S9_summable_F hΨ (fun α => InMuA (rhoN N) (LN N) kc N u₃ α) x
  have hL : Summable fun α : Occ => (((α y : ℝ) + 1) * (α x : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N u₁ α then (1 : ℝ) else 0) +
          (if InMuA (rhoN N) (LN N) kc N u₃ α then (1 : ℝ) else 0)) *
        ‖trialState V w kc N α‖ ^ 2 := by
    have : (fun α : Occ => (((α y : ℝ) + 1) * (α x : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N u₁ α then (1 : ℝ) else 0) +
          (if InMuA (rhoN N) (LN N) kc N u₃ α then (1 : ℝ) else 0)) *
        ‖trialState V w kc N α‖ ^ 2) = fun α => ((((α y : ℝ) + 1) * (α x : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N u₁ α then (1 : ℝ) else 0) +
          (if InMuA (rhoN N) (LN N) kc N u₃ α then (1 : ℝ) else 0))) *
        ‖trialState V w kc N α‖ ^ 2 := rfl
    rw [this]
    refine bd _ ((N + 1) * N * 2) (fun α h => ?_)
    have a := S9_occ_le hΨ h x
    have b := S9_occ_le hΨ h y
    have ha : (α x : ℝ) ≤ N := by exact_mod_cast a
    have hb : (α y : ℝ) ≤ N := by exact_mod_cast b
    have i1 : (if InMuA (rhoN N) (LN N) kc N u₁ α then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have i3 : (if InMuA (rhoN N) (LN N) kc N u₃ α then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have j1 := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N u₁ α) (zero_le_one' ℝ)
    have j3 := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N u₃ α) (zero_le_one' ℝ)
    rw [abs_of_nonneg (by positivity)]
    have hx0 : (0 : ℝ) ≤ α x := Nat.cast_nonneg _
    have hy0 : (0 : ℝ) ≤ α y := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul (by linarith) ha hx0 (by positivity)) (by linarith)
      (by linarith) (by positivity)
  set G : Occ → ℝ := fun α => 2 * ((α x : ℝ) * α y * ‖trialState V w kc N α‖ ^ 2) +
      (if InMuA (rhoN N) (LN N) kc N u₁ α then (α x : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) +
      (if InMuA (rhoN N) (LN N) kc N u₃ α then (α x : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0)
    with hG
  have hGs : Summable G := ((h3.mul_left 2).add hF₁).add hF₃
  have key : (∑' α : Occ, (((α y : ℝ) + 1) * (α x : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N u₁ α then (1 : ℝ) else 0) +
          (if InMuA (rhoN N) (LN N) kc N u₃ α then (1 : ℝ) else 0)) *
        ‖trialState V w kc N α‖ ^ 2) ≤ ∑' α, G α :=
    hL.tsum_le_tsum (fun α => S9_ptW _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by positivity) _ _) hGs
  refine key.trans ?_
  rw [hG, ((h3.mul_left 2).add hF₁).tsum_add hF₃, (h3.mul_left 2).tsum_add hF₁, tsum_mul_left,
    ← S9_Q2_eq]
  have hQ2 := E.hQ2 kc x y hx hy hxy.1 (S9_ne_of_pm hxy)
  have hly := E.hlamH y hy
  have hQ2' : Expect.Q (trialState V w kc N) [x, y] ≤
      |lam V w (rhoN N) (LN N) x| * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4) := by
    refine hQ2.trans ?_
    rw [abs_mul]
    have : C * (|lam V w (rhoN N) (LN N) x| * |lam V w (rhoN N) (LN N) y|) * rhoN N ^ 4 /
        epsP (rhoN N) ^ 4 = |lam V w (rhoN N) (LN N) x| * (C * |lam V w (rhoN N) (LN N) y| *
          rhoN N ^ 4 / epsP (rhoN N) ^ 4) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hly hC) (by positivity)
  linarith only [hQ2', hP₁, hP₃]

/-- Class 3, generic legs: the tuple sum. -/
private lemma S9_gen3 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPH (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) (h₄ : inPH (rhoN N) (LN N) v₄)
    (hGen : S9_Gen4 v₁ v₂ v₃ v₄) {Pb : ℝ} (hPb : 0 ≤ Pb)
    (hP₁ : (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N v₁ α then
        (α v₂ : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤ Pb * |lam V w (rhoN N) (LN N) v₂|)
    (hP₃ : (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N v₃ α then
        (α v₂ : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤ Pb * |lam V w (rhoN N) (LN N) v₂|) :
    S9_T (trialState V w kc N) v₁ v₂ v₃ v₄ ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
            C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 0 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (2 * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4) + 2 * Pb) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
            C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  set Ψ := trialState V w kc N with hΨdef
  set m : ℝ := (⌈mc (rhoN N)⌉₊ : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have hE2 := S9_E_nonneg V w E.hN hg 2
  have hE0 := S9_E_nonneg V w E.hN hg 0
  obtain ⟨p12, p13, p14, p23, p24, p34⟩ := (S9_Gen4_iff _ _ _ _).1 hGen
  have bd : ∀ (f : Occ → ℝ) (B : ℝ), (∀ α, Ψ α ≠ 0 → |f α| ≤ B) →
      Summable fun α : Occ => f α * ‖Ψ α‖ ^ 2 := fun f B h => S9_summable_w hΨ f B h
  have s2 := Real.sqrt_nonneg (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|)
  have s0 := Real.sqrt_nonneg (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|)
  have s4 := Real.sqrt_nonneg (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|)
  -- the three weights
  have hW0 : Summable fun b : Occ => (((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) * ‖Ψ b‖ ^ 2 :=
    bd _ ((N + 1 : ℝ) * N) (fun α h => by
      rw [abs_of_nonneg (by positivity)]
      have a := S9_occ_le hΨ h v₂
      have b := S9_occ_le hΨ h v₄
      have ha : (α v₂ : ℝ) ≤ N := by exact_mod_cast a
      have hb : (α v₄ : ℝ) ≤ N := by exact_mod_cast b
      exact mul_le_mul (by linarith) ha (Nat.cast_nonneg _) (by positivity))
  have hW1 : Summable fun b : Occ => (((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N v₁ b then (1 : ℝ) else 0) +
          (if InMuA (rhoN N) (LN N) kc N v₃ b then (1 : ℝ) else 0)) * ‖Ψ b‖ ^ 2 := by
    refine bd (fun b => (((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N v₁ b then (1 : ℝ) else 0) +
          (if InMuA (rhoN N) (LN N) kc N v₃ b then (1 : ℝ) else 0))) ((N + 1 : ℝ) * N * 2)
        (fun α h => ?_)
    have a := S9_occ_le hΨ h v₂
    have b := S9_occ_le hΨ h v₄
    have ha : (α v₂ : ℝ) ≤ N := by exact_mod_cast a
    have hb : (α v₄ : ℝ) ≤ N := by exact_mod_cast b
    have i1 : (if InMuA (rhoN N) (LN N) kc N v₁ α then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have i3 : (if InMuA (rhoN N) (LN N) kc N v₃ α then (1 : ℝ) else 0) ≤ 1 := by
      split_ifs <;> norm_num
    have j1 := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N v₁ α) (zero_le_one' ℝ)
    have j3 := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N v₃ α) (zero_le_one' ℝ)
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_mul (by linarith) ha (Nat.cast_nonneg _) (by positivity))
      (by linarith) (by linarith) (by positivity)
  have hW2 : Summable fun κ : Occ => ((κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1)) * ‖Ψ κ‖ ^ 2 :=
    bd _ ((N : ℝ) * (N + 1)) (fun α h => by
      rw [abs_of_nonneg (by positivity)]
      have a := S9_occ_le hΨ h v₂
      have b := S9_occ_le hΨ h v₄
      have ha : (α v₂ : ℝ) ≤ N := by exact_mod_cast a
      have hb : (α v₄ : ℝ) ≤ N := by exact_mod_cast b
      exact mul_le_mul hb (by linarith) (by positivity) (Nat.cast_nonneg _))
  have key := S9_T_le hΨ v₁ v₂ v₃ v₄
    (fun b => (m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|)) *
        ((((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) * ‖Ψ b‖ ^ 2) +
      (m * Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|)) *
        ((((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) *
          ((if InMuA (rhoN N) (LN N) kc N v₁ b then (1 : ℝ) else 0) +
            (if InMuA (rhoN N) (LN N) kc N v₃ b then (1 : ℝ) else 0)) * ‖Ψ b‖ ^ 2))
    (fun κ => (m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|)) *
        (((κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1)) * ‖Ψ κ‖ ^ 2))
    (fun b => by
      have := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N v₁ b) (zero_le_one' ℝ)
      have := S9_ite_nonneg (InMuA (rhoN N) (LN N) kc N v₃ b) (zero_le_one' ℝ)
      positivity)
    (fun κ => by positivity) (((hW0.mul_left _).add (hW1.mul_left _))) (hW2.mul_left _)
    (fun κ hc => S9_pt3 E kc h₁ h₂ h₃ h₄ hGen κ hc |>.trans_eq (by ring))
  refine key.trans ?_
  have hG0 : 0 ≤ g0 V w / epsP (rhoN N) ^ 2 := by positivity
  have hl2 := E.hlamH v₂ h₂
  have hl4 := E.hlamH v₄ h₄
  -- the three sums
  have eW0 : (fun b : Occ => (((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) * ‖Ψ b‖ ^ 2) =
      fun b : Occ => ((b v₂ : ℝ) * ((b v₄ : ℝ) + 1)) * ‖Ψ b‖ ^ 2 := by
    funext b; ring
  have q0 := S9_Qsum E hC kc h₂ h₄ p24
  have q2 := S9_Qsum E hC kc h₄ h₂ (S9_pm_symm p24)
  have q1 := S9_QsumW E hC kc h₂ h₄ p24 hP₁ hP₃
  have R0 : 0 ≤ C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
      C * rhoN N ^ 2 / epsP (rhoN N) ^ 2 := by positivity
  have R1 : 0 ≤ 2 * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4) +
      2 * Pb := by positivity
  have sd2 := S9_sqrt_div_mul hE2 (abs_nonneg (lam V w (rhoN N) (LN N) v₂)) hl2
  have sd0 := S9_sqrt_div_mul hE0 (abs_nonneg (lam V w (rhoN N) (LN N) v₂)) hl2
  have sd4 := S9_sqrt_div_mul hE2 (abs_nonneg (lam V w (rhoN N) (LN N) v₄)) hl4
  have f0 : (m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|)) *
      (∑' b : Occ, (((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) * ‖Ψ b‖ ^ 2) ≤
      m * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
        (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
          C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) := by
    rw [eW0]
    calc (m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|)) *
          (∑' b : Occ, ((b v₂ : ℝ) * ((b v₄ : ℝ) + 1)) * ‖Ψ b‖ ^ 2)
        ≤ (m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|)) *
          (|lam V w (rhoN N) (LN N) v₂| * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
            epsP (rhoN N) ^ 4 + C * rhoN N ^ 2 / epsP (rhoN N) ^ 2)) :=
          mul_le_mul_of_nonneg_left q0 (by positivity)
      _ = m * (Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₂|) *
          |lam V w (rhoN N) (LN N) v₂|) * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
            epsP (rhoN N) ^ 4 + C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) := by ring
      _ ≤ m * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
        (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
          C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sd2 hm0) R0
  have f1 : (m * Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|)) *
      (∑' b : Occ, (((b v₄ : ℝ) + 1) * (b v₂ : ℝ)) *
        ((if InMuA (rhoN N) (LN N) kc N v₁ b then (1 : ℝ) else 0) +
          (if InMuA (rhoN N) (LN N) kc N v₃ b then (1 : ℝ) else 0)) * ‖Ψ b‖ ^ 2) ≤
      m * Real.sqrt (S9_E V w N 0 * (g0 V w / epsP (rhoN N) ^ 2)) *
        (2 * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4) + 2 * Pb) := by
    calc _ ≤ (m * Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|)) *
          (|lam V w (rhoN N) (LN N) v₂| * (2 * (C * (g0 V w / epsP (rhoN N) ^ 2) *
            rhoN N ^ 4 / epsP (rhoN N) ^ 4) + 2 * Pb)) :=
          mul_le_mul_of_nonneg_left q1 (by positivity)
      _ = m * (Real.sqrt (S9_E V w N 0 / |lam V w (rhoN N) (LN N) v₂|) *
          |lam V w (rhoN N) (LN N) v₂|) * (2 * (C * (g0 V w / epsP (rhoN N) ^ 2) *
            rhoN N ^ 4 / epsP (rhoN N) ^ 4) + 2 * Pb) := by ring
      _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sd0 hm0) R1
  have f2 : (m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|)) *
      (∑' κ : Occ, ((κ v₄ : ℝ) * ((κ v₂ : ℝ) + 1)) * ‖Ψ κ‖ ^ 2) ≤
      m * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
        (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
          C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) := by
    calc _ ≤ (m * Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|)) *
          (|lam V w (rhoN N) (LN N) v₄| * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
            epsP (rhoN N) ^ 4 + C * rhoN N ^ 2 / epsP (rhoN N) ^ 2)) :=
          mul_le_mul_of_nonneg_left q2 (by positivity)
      _ = m * (Real.sqrt (S9_E V w N 2 / |lam V w (rhoN N) (LN N) v₄|) *
          |lam V w (rhoN N) (LN N) v₄|) * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 /
            epsP (rhoN N) ^ 4 + C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) := by ring
      _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left sd4 hm0) R0
  rw [(hW0.mul_left _).tsum_add (hW1.mul_left _), tsum_mul_left, tsum_mul_left, tsum_mul_left]
  linarith only [f0, f1, f2]


/-- `Σ_β w₂(x, y; β)|Ψ(β)|² ≤ ⌈m_c⌉ C ρ² (g₀/ε²)/ε²` for `x ∈ P_L`, `y ∈ P_H`. -/
private lemma S9_wsum_LH {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {x y : Idx} (hx : inPL (rhoN N) (LN N) x) (hy : inPH (rhoN N) (LN N) y) :
    ∑' β, S9_w2 x y β * ‖trialState V w kc N β‖ ^ 2 ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) /
        epsP (rhoN N) ^ 2) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  have hne : x ≠ y := (S9_PL_PH_ne hρ hx hy).1
  rw [S9_wsum_ne _ hne, S9_Q2_eq]
  have hQ := S9_Q1_bound E hC kc hy
  rw [S9_Q1_eq] at hQ
  have hs1 : Summable fun β : Occ => (β y : ℝ) * ‖trialState V w kc N β‖ ^ 2 :=
    S9_summable_w hΨ (fun β => (β y : ℝ)) N (fun β hβ => by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]; exact_mod_cast S9_occ_le hΨ hβ y)
  have hs2 : Summable fun β : Occ => (β x : ℝ) * β y * ‖trialState V w kc N β‖ ^ 2 :=
    S9_summable_w hΨ (fun β => (β x : ℝ) * β y) (N * N) (fun β hβ => by
      rw [abs_of_nonneg (by positivity)]
      have a : (β x : ℝ) ≤ N := by exact_mod_cast S9_occ_le hΨ hβ x
      have b : (β y : ℝ) ≤ N := by exact_mod_cast S9_occ_le hΨ hβ y
      gcongr)
  have h1 : ∑' β : Occ, (β x : ℝ) * β y * ‖trialState V w kc N β‖ ^ 2 ≤
      ∑' β : Occ, (⌈mc (rhoN N)⌉₊ : ℝ) * ((β y : ℝ) * ‖trialState V w kc N β‖ ^ 2) := by
    refine hs2.tsum_le_tsum (fun β => ?_) (hs1.mul_left _)
    by_cases hz : trialState V w kc N β = 0
    · simp [hz]
    · have hM := S9_inM hz
      have e : ((β x : ℕ) : ℝ) ≤ (⌈mc (rhoN N)⌉₊ : ℝ) := Nat.cast_le.2 (S9_occ_ceil hρ hM hx)
      calc (β x : ℝ) * β y * ‖trialState V w kc N β‖ ^ 2
          = ((β x : ℝ) * ((β y : ℝ) * ‖trialState V w kc N β‖ ^ 2)) := by ring
        _ ≤ (⌈mc (rhoN N)⌉₊ : ℝ) * ((β y : ℝ) * ‖trialState V w kc N β‖ ^ 2) :=
          mul_le_mul_of_nonneg_right e (by positivity)
  rw [tsum_mul_left] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left hQ (Nat.cast_nonneg _))

/-- Class 3, all tuples: `T ≤ ⌈m_c⌉ C ρ² (g₀/ε²)/ε²`. -/
private lemma S9_spec3 {V w : R3 → ℝ} {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    (kc : ℝ) {v₁ v₂ v₃ v₄ : Idx} (h₁ : inPL (rhoN N) (LN N) v₁) (h₂ : inPH (rhoN N) (LN N) v₂)
    (h₃ : inPL (rhoN N) (LN N) v₃) (h₄ : inPH (rhoN N) (LN N) v₄) :
    S9_T (trialState V w kc N) v₁ v₂ v₃ v₄ ≤
      (⌈mc (rhoN N)⌉₊ : ℝ) * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) /
        epsP (rhoN N) ^ 2) := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN E.hN
  have hΨ := Normalization_isNState V w kc E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have := S9_T_le_sch hΨ v₁ v₂ v₃ v₄ (S9_wsum_LH E hC kc h₁ h₂) (S9_wsum_LH E hC kc h₃ h₄)
  rwa [← Real.sqrt_mul (by positivity), Real.sqrt_mul_self (by positivity)] at this

/-- Class 3: the four placements of the `P_L` legs reduce to `v₁, v₃ ∈ P_L`, `v₂, v₄ ∈ P_{H,c}`
by exchanging the two created and the two annihilated momenta. -/
private lemma S9_normalize3 {ρ L kc : ℝ} {N : ℕ} {p q u : Idx} {α : Occ}
    (hm : FourLegs.Cls.mem ρ L kc N .three (p, q, u, α)) :
    ∃ w₁ w₂ w₃ w₄ : Idx, (∀ Ψ : Occ → ℂ, S9_T Ψ p q (p - u) (q + u) = S9_T Ψ w₁ w₂ w₃ w₄) ∧
      (S9_Gen4 p q (p - u) (q + u) → S9_Gen4 w₁ w₂ w₃ w₄) ∧
      inPL ρ L w₁ ∧ inPHc ρ L kc w₂ ∧ inPL ρ L w₃ ∧ inPHc ρ L kc w₄ := by
  obtain ⟨hA, hB⟩ := hm
  rcases hA with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rcases hB with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · exact ⟨p, q, p - u, q + u, fun _ => rfl, id, hp, hq, hr, hs⟩
  · exact ⟨p, q, q + u, p - u, fun Ψ => S9_T_swap34 Ψ _ _ _ _, S9_Gen4_swap34, hp, hq, hs, hr⟩
  · exact ⟨q, p, p - u, q + u, fun Ψ => S9_T_swap12 Ψ _ _ _ _, S9_Gen4_swap12, hq, hp, hr, hs⟩
  · refine ⟨q, p, q + u, p - u, fun Ψ => ?_, fun h => S9_Gen4_swap34 (S9_Gen4_swap12 h), hq, hp,
      hs, hr⟩
    rw [S9_T_swap12, S9_T_swap34]


/-- Class 3: a tuple with a coincidence of two legs lies in one of the two parametrized sets. -/
private lemma S9_not_gen3 {ρ L kc : ℝ} {N : ℕ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {p q u : Idx}
    (hm : FourLegs.Cls.mem ρ L kc N .three (p, q, u, 0))
    (hA : Decomp.Part.A2.mem p q u) (hGen : ¬ FourLegs.Gen (FourLegs.legs p q u))
    (BL BH : Finset Idx) (hmL : ∀ n, inPL ρ L n → n ∈ BL)
    (hmH : ∀ n, inPHc ρ L kc n → n ∈ BH) :
    (p, q, u) ∈ S9_sp BL BH ∪ S9_sp BH BL := by
  have hcases := S9_not_gen hA hGen
  obtain ⟨hA', hB'⟩ := hm
  have PH : ∀ n, inPHc ρ L kc n → inPH ρ L n := fun n h => h.1
  rcases hA' with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rcases hB' with ⟨hr, hs⟩ | ⟨hr, hs⟩
  · -- `p ∈ P_L, q ∈ P_H, p - u ∈ P_L, q + u ∈ P_H`
    rcases hcases with h | h | h | h | h | h
    · exact absurd h (S9_PL_PH_ne hρ hp (PH _ hq)).1
    · exact absurd h (S9_PL_PH_ne hρ hr (PH _ hs)).1
    · exact Finset.mem_union_left _ (S9_mem_sp3 (hmL _ hp) (hmH _ hq) h)
    · exact absurd h (S9_PL_PH_ne hρ hp (PH _ hs)).2
    · exact absurd (neg_eq_iff_eq_neg.mp h.symm) (S9_PL_PH_ne hρ hr (PH _ hq)).2
    · exfalso
      refine (S9_no_double hρ hρ1 hr hp (PH _ hq)).2.1 ?_
      funext i
      have := congr_fun h i
      simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
  · -- `p ∈ P_L, q ∈ P_H, p - u ∈ P_H, q + u ∈ P_L`
    rcases hcases with h | h | h | h | h | h
    · exact absurd h (S9_PL_PH_ne hρ hp (PH _ hq)).1
    · exact absurd h.symm (S9_PL_PH_ne hρ hs (PH _ hr)).1
    · exact absurd h (S9_PL_PH_ne hρ hp (PH _ hr)).2
    · exact Finset.mem_union_left _ (S9_mem_sp4 (hmL _ hp) (hmH _ hq) h)
    · exfalso
      refine (S9_no_double hρ hρ1 hs hp (PH _ hq)).2.1 ?_
      funext i
      have := congr_fun h i
      simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    · exact absurd (neg_eq_iff_eq_neg.mp h.symm) (S9_PL_PH_ne hρ hs (PH _ hq)).2
  · -- `p ∈ P_H, q ∈ P_L, p - u ∈ P_L, q + u ∈ P_H`
    rcases hcases with h | h | h | h | h | h
    · exact absurd h.symm (S9_PL_PH_ne hρ hq (PH _ hp)).1
    · exact absurd h (S9_PL_PH_ne hρ hr (PH _ hs)).1
    · exact absurd (neg_eq_iff_eq_neg.mp h.symm) (S9_PL_PH_ne hρ hr (PH _ hp)).2
    · exfalso
      refine (S9_no_double hρ hρ1 hr hq (PH _ hp)).2.1 ?_
      funext i
      have := congr_fun h i
      simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    · exact Finset.mem_union_right _ (S9_mem_sp5 (hmH _ hp) (hmL _ hq) h)
    · exact absurd h (S9_PL_PH_ne hρ hq (PH _ hs)).2
  · -- `p ∈ P_H, q ∈ P_L, p - u ∈ P_H, q + u ∈ P_L`
    rcases hcases with h | h | h | h | h | h
    · exact absurd h.symm (S9_PL_PH_ne hρ hq (PH _ hp)).1
    · exact absurd h.symm (S9_PL_PH_ne hρ hs (PH _ hr)).1
    · exfalso
      refine (S9_no_double hρ hρ1 hs hq (PH _ hp)).2.1 ?_
      funext i
      have := congr_fun h i
      simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    · exact absurd (neg_eq_iff_eq_neg.mp h.symm) (S9_PL_PH_ne hρ hs (PH _ hp)).2
    · exact absurd h (S9_PL_PH_ne hρ hq (PH _ hr)).2
    · exact Finset.mem_union_right _ (S9_mem_sp6 (hmH _ hp) (hmL _ hq) h)

/-- `E_j` in closed form. -/
private lemma S9_E_eq (V w : R3 → ℝ) {N : ℕ} (hN : 1 ≤ N) (hg : 0 < g0 V w) (j : ℕ) :
    S9_E V w N j = 2 * (epsP (rhoN N) ^ 24)⁻¹ / (N : ℝ) ^ j := by
  obtain ⟨-, hρ, -, -⟩ := Particles_rhoN_LN hN
  have ht := S9_eps_pos hρ
  have hK : rhoN N ^ (-(1 / 10 : ℝ)) = (epsP (rhoN N) ^ 20)⁻¹ :=
    S9_rpow_eps_neg hρ.le 20 (by norm_num)
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  have hn : (N : ℝ) ^ j ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    exact pow_ne_zero _ (by linarith)
  have hg' : g0 V w ≠ 0 := hg.ne'
  unfold S9_E
  rw [hK]
  generalize epsP (rhoN N) = t at ht hr ⊢
  rw [hr]
  field_simp

/-- The generic tuples of class 3: the exponent. -/
private lemma S9_arith3 (V w : R3 → ℝ) {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C)
    {K C' Pb : ℝ} (hK : 1 ≤ K) (hPb : 0 ≤ Pb)
    (hPb' : Pb ≤ 2 * C' * K ^ 3 * epsP (rhoN N) ^ 593) :
    (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
            C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 0 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (2 * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4) + 2 * Pb) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
            C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) ≤
      (Real.sqrt (2 * g0 V w) * (8 * C * g0 V w + 4 * C + 8 * C')) * K ^ 3 *
        epsP (rhoN N) ^ 579 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have ht1 := S9_eps_le_one hρ hρ1
  have hg := E.hg
  have hm := S9_ceil_le hρ hρ1
  have hm0 : (0 : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := Nat.cast_nonneg _
  have hN425 := S9_Nt E.hN
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  have hE2 := S9_E_eq V w E.hN hg 2
  have hE0 := S9_E_eq V w E.hN hg 0
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast E.hN
  rw [hE2, hE0]
  generalize (⌈mc (rhoN N)⌉₊ : ℝ) = m at hm hm0 ⊢
  generalize (N : ℝ) = n at hN425 hN1 ⊢
  generalize epsP (rhoN N) = t at ht ht1 hm hN425 hr hPb' ⊢
  have hn0 : 0 < n := by linarith
  have hg2 : 0 ≤ 2 * g0 V w := by positivity
  have e2 : 2 * (t ^ 24)⁻¹ / n ^ 2 * (g0 V w / t ^ 2) = 2 * g0 V w * (t ^ 412) ^ 2 := by
    have : 1 / n = t ^ 425 := by field_simp; linarith
    have h2 : 1 / n ^ 2 = (t ^ 425) ^ 2 := by rw [← this, one_div_pow]
    calc 2 * (t ^ 24)⁻¹ / n ^ 2 * (g0 V w / t ^ 2)
        = 2 * g0 V w * (t ^ 24)⁻¹ * (t ^ 2)⁻¹ * (1 / n ^ 2) := by field_simp
      _ = 2 * g0 V w * (t ^ 412) ^ 2 := by rw [h2]; field_simp
  have e0 : 2 * (t ^ 24)⁻¹ / n ^ 0 * (g0 V w / t ^ 2) = 2 * g0 V w * ((t ^ 13)⁻¹) ^ 2 := by
    simp only [pow_zero, div_one]
    field_simp
  have s2 : Real.sqrt (2 * (t ^ 24)⁻¹ / n ^ 2 * (g0 V w / t ^ 2)) =
      Real.sqrt (2 * g0 V w) * t ^ 412 := by
    rw [e2, Real.sqrt_mul hg2, Real.sqrt_sq (by positivity)]
  have s0 : Real.sqrt (2 * (t ^ 24)⁻¹ / n ^ 0 * (g0 V w / t ^ 2)) =
      Real.sqrt (2 * g0 V w) * (t ^ 13)⁻¹ := by
    rw [e0, Real.sqrt_mul hg2, Real.sqrt_sq (by positivity)]
  rw [s2, s0, hr]
  have hm2 : m ≤ 2 * t⁻¹ := hm
  have hsq := Real.sqrt_nonneg (2 * g0 V w)
  set sg := Real.sqrt (2 * g0 V w) with hsg
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK
  calc m * (sg * t ^ 412) * (C * (g0 V w / t ^ 2) * (t ^ 200) ^ 4 / t ^ 4 +
          C * (t ^ 200) ^ 2 / t ^ 2) +
        m * (sg * (t ^ 13)⁻¹) * (2 * (C * (g0 V w / t ^ 2) * (t ^ 200) ^ 4 / t ^ 4) + 2 * Pb) +
        m * (sg * t ^ 412) * (C * (g0 V w / t ^ 2) * (t ^ 200) ^ 4 / t ^ 4 +
          C * (t ^ 200) ^ 2 / t ^ 2)
      ≤ (2 * t⁻¹) * (sg * t ^ 412) * (C * (g0 V w / t ^ 2) * (t ^ 200) ^ 4 / t ^ 4 +
          C * (t ^ 200) ^ 2 / t ^ 2) +
        (2 * t⁻¹) * (sg * (t ^ 13)⁻¹) * (2 * (C * (g0 V w / t ^ 2) * (t ^ 200) ^ 4 / t ^ 4) +
          2 * (2 * C' * K ^ 3 * t ^ 593)) +
        (2 * t⁻¹) * (sg * t ^ 412) * (C * (g0 V w / t ^ 2) * (t ^ 200) ^ 4 / t ^ 4 +
          C * (t ^ 200) ^ 2 / t ^ 2) := by
        gcongr
    _ = sg * (4 * C * g0 V w * t ^ 1205 + 4 * C * t ^ 809 + 4 * C * g0 V w * t ^ 780 +
          8 * C' * K ^ 3 * t ^ 579) := by
        field_simp
        ring
    _ ≤ sg * (4 * C * g0 V w * t ^ 579 * K ^ 3 + 4 * C * t ^ 579 * K ^ 3 +
          4 * C * g0 V w * t ^ 579 * K ^ 3 + 8 * C' * K ^ 3 * t ^ 579) := by
        have a1 : t ^ 1205 ≤ t ^ 579 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
        have a2 : t ^ 809 ≤ t ^ 579 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
        have a3 : t ^ 780 ≤ t ^ 579 := pow_le_pow_of_le_one ht.le ht1 (by norm_num)
        have b1 : t ^ 579 ≤ t ^ 579 * K ^ 3 := le_mul_of_one_le_right (by positivity) hK3
        have c1 : 0 ≤ 4 * C * g0 V w := by positivity
        have c2 : 0 ≤ 4 * C := by positivity
        refine mul_le_mul_of_nonneg_left ?_ hsq
        have d1 : t ^ 1205 ≤ t ^ 579 * K ^ 3 := a1.trans b1
        have d2 : t ^ 809 ≤ t ^ 579 * K ^ 3 := a2.trans b1
        have d3 : t ^ 780 ≤ t ^ 579 * K ^ 3 := a3.trans b1
        nlinarith [mul_le_mul_of_nonneg_left d1 c1, mul_le_mul_of_nonneg_left d2 c2,
          mul_le_mul_of_nonneg_left d3 c1]
    _ = _ := by ring


/-- The special tuples of class 3: the exponent. -/
private lemma S9_arith3s (V w : R3 → ℝ) {C : ℝ} {N : ℕ} (E : S9_Env V w C N) (hC : 0 ≤ C) :
    (⌈mc (rhoN N)⌉₊ : ℝ) * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) /
        epsP (rhoN N) ^ 2) ≤ 2 * C * g0 V w * epsP (rhoN N) ^ 395 := by
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have hg := E.hg
  have hm := S9_ceil_le hρ hρ1
  have hm0 : (0 : ℝ) ≤ ⌈mc (rhoN N)⌉₊ := Nat.cast_nonneg _
  have hr : rhoN N = epsP (rhoN N) ^ 200 := S9_rho_eq hρ.le
  generalize (⌈mc (rhoN N)⌉₊ : ℝ) = m at hm hm0 ⊢
  generalize epsP (rhoN N) = t at ht hm hr ⊢
  rw [hr]
  calc m * (C * (t ^ 200) ^ 2 * (g0 V w / t ^ 2) / t ^ 2)
      ≤ (2 * t⁻¹) * (C * (t ^ 200) ^ 2 * (g0 V w / t ^ 2) / t ^ 2) := by gcongr
    _ = 2 * C * g0 V w * t ^ 395 := by
        field_simp

/-- The tuples of class 3, parametrized by three legs, one for each placement. -/
private def S9_S3 (BL BH : Finset Idx) : Finset (Idx × Idx × Idx) :=
  (BL ×ˢ BH ×ˢ BL).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2)) ∪
  (BL ×ˢ BH ×ˢ BL).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.2.2 - y.2.1)) ∪
  (BH ×ˢ BL ×ˢ BL).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2)) ∪
  (BH ×ˢ BL ×ˢ BL).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.2.2 - y.2.1))

private lemma S9_S3_card (BL BH : Finset Idx) :
    ((S9_S3 BL BH).card : ℝ) ≤ 4 * ((BL.card : ℝ) ^ 2 * BH.card) := by
  unfold S9_S3
  have a1 := S9_card3 BL BH BL (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2))
  have a2 := S9_card3 BL BH BL (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.2.2 - y.2.1))
  have a3 := S9_card3 BH BL BL (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2))
  have a4 := S9_card3 BH BL BL (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.2.2 - y.2.1))
  generalize ((BL ×ˢ BH ×ˢ BL).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2))) = I1
    at a1 ⊢
  generalize ((BL ×ˢ BH ×ˢ BL).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.2.2 - y.2.1)))
    = I2 at a2 ⊢
  generalize ((BH ×ˢ BL ×ˢ BL).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.1 - y.2.2))) = I3
    at a3 ⊢
  generalize ((BH ×ˢ BL ×ˢ BL).image (fun y : Idx × Idx × Idx => (y.1, y.2.1, y.2.2 - y.2.1)))
    = I4 at a4 ⊢
  have u1 : ((I1 ∪ I2).card : ℝ) ≤ I1.card + I2.card := by exact_mod_cast Finset.card_union_le I1 I2
  have u2 : ((I1 ∪ I2 ∪ I3).card : ℝ) ≤ (I1 ∪ I2).card + I3.card := by
    exact_mod_cast Finset.card_union_le (I1 ∪ I2) I3
  have u3 : ((I1 ∪ I2 ∪ I3 ∪ I4).card : ℝ) ≤ (I1 ∪ I2 ∪ I3).card + I4.card := by
    exact_mod_cast Finset.card_union_le (I1 ∪ I2 ∪ I3) I4
  have e1 : (BL.card : ℝ) * ((BH.card : ℝ) * BL.card) = (BL.card : ℝ) ^ 2 * BH.card := by ring
  have e2 : (BH.card : ℝ) * ((BL.card : ℝ) * BL.card) = (BL.card : ℝ) ^ 2 * BH.card := by ring
  linarith only [a1, a2, a3, a4, u1, u2, u3, e1, e2]


/-- Class 3 (case 3 of Lemma 9.1 [fourlegslemma1], all four placements of the `P_L` legs):
the rate `ε^4 = ρ^{1/50}`. -/
private lemma S9_class3 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc →
      FourLegs.absPart V w .three kc N ≤ C' * kc ^ 6 * epsP (rhoN N) ^ 4 := by
  obtain ⟨V₀, hV₀0, hV₀⟩ := S9_V0 hV
  obtain ⟨C, hC, hev⟩ := S9_env hV hw
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  obtain ⟨Cp, hCp, N₁, hrate⟩ := S9_prop91_rate hV hw
  have hg := scat_g0_pos hV hw
  refine ⟨V₀ * (4 * 67 ^ 3 * (Real.sqrt (2 * g0 V w) * (8 * C * g0 V w + 4 * C + 8 * Cp)) +
    12 * 67 ^ 2 * (2 * C * g0 V w)), by positivity, max N₀ N₁, fun N hN kc hkc => ?_⟩
  have E := hN₀ N (le_trans (le_max_left _ _) hN)
  have hr := hrate N (le_trans (le_max_right _ _) hN)
  obtain ⟨hNL, hρ, hρ1, hL⟩ := Particles_rhoN_LN E.hN
  have ht := S9_eps_pos hρ
  have ht1 := S9_eps_le_one hρ hρ1
  have hΨ := Normalization_isNState V w kc E.hN
  set BL := S9_ball (LN N) ((epsP (rhoN N))⁻¹ * rhoN N ^ (1 / 2 : ℝ)) with hBL
  set BH := S9_ball (LN N) kc with hBH
  have hmL : ∀ n, inPL (rhoN N) (LN N) n → n ∈ BL := fun n hn => S9_mem_ball hL hn.2
  have hmH : ∀ n, inPHc (rhoN N) (LN N) kc n → n ∈ BH := fun n hn => S9_mem_ball hL hn.2
  have hcL : (BL.card : ℝ) ≤ 67 * (LN N ^ 3 * epsP (rhoN N) ^ 297) := S9_card_PL E.hN
  have hcH : (BH.card : ℝ) ≤ 67 * (LN N ^ 3 * kc ^ 3) := S9_card_PH E.hN kc hkc
  -- the constant `Pb` of Proposition 9.1
  set Pb : ℝ := Cp * kc ^ 3 * epsP (rhoN N) ^ 593 + Cp * epsP (rhoN N) ^ 197 / LN N ^ 3
    with hPbdef
  have hL3 : 1 / LN N ^ 3 = epsP (rhoN N) ^ 625 := by
    have := S9_L3 E.hN
    have h0 : LN N ^ 3 ≠ 0 := by positivity
    field_simp
    linarith
  have hPb0 : 0 ≤ Pb := by positivity
  have hkc3 : 1 ≤ kc ^ 3 := one_le_pow₀ hkc
  have hPb' : Pb ≤ 2 * Cp * kc ^ 3 * epsP (rhoN N) ^ 593 := by
    have e3 : Cp * epsP (rhoN N) ^ 197 / LN N ^ 3 = Cp * epsP (rhoN N) ^ 822 := by
      rw [div_eq_mul_one_div, hL3]; ring
    have h1 : epsP (rhoN N) ^ 822 ≤ epsP (rhoN N) ^ 593 :=
      pow_le_pow_of_le_one ht.le ht1 (by norm_num)
    have h2 : epsP (rhoN N) ^ 593 ≤ kc ^ 3 * epsP (rhoN N) ^ 593 :=
      le_mul_of_one_le_left (by positivity) hkc3
    rw [hPbdef, e3]
    have h3 : Cp * epsP (rhoN N) ^ 822 ≤ Cp * kc ^ 3 * epsP (rhoN N) ^ 593 := by
      calc Cp * epsP (rhoN N) ^ 822 ≤ Cp * (kc ^ 3 * epsP (rhoN N) ^ 593) :=
            mul_le_mul_of_nonneg_left (h1.trans h2) hCp
        _ = Cp * kc ^ 3 * epsP (rhoN N) ^ 593 := by ring
    linarith only [h3]
  have hP : ∀ (u v : Idx), inPL (rhoN N) (LN N) u → inPHc (rhoN N) (LN N) kc v →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
        (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤ Pb * |lam V w (rhoN N) (LN N) v| := by
    intro u v hu hv
    have h1 := hr kc u v hu hv
    rw [max_eq_left hkc] at h1
    refine h1.trans (le_of_eq ?_)
    rw [hPbdef]; ring
  -- the canonical placement
  set Bg : ℝ := (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
            C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 0 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (2 * (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4) + 2 * Pb) +
        (⌈mc (rhoN N)⌉₊ : ℝ) * Real.sqrt (S9_E V w N 2 * (g0 V w / epsP (rhoN N) ^ 2)) *
          (C * (g0 V w / epsP (rhoN N) ^ 2) * rhoN N ^ 4 / epsP (rhoN N) ^ 4 +
            C * rhoN N ^ 2 / epsP (rhoN N) ^ 2) with hBgdef
  set Bs : ℝ := (⌈mc (rhoN N)⌉₊ : ℝ) * (C * rhoN N ^ 2 * (g0 V w / epsP (rhoN N) ^ 2) /
        epsP (rhoN N) ^ 2) with hBsdef
  have hBg0 : 0 ≤ Bg := by
    have := S9_E_nonneg V w E.hN hg 2
    have := S9_E_nonneg V w E.hN hg 0
    positivity
  have hBs0 : 0 ≤ Bs := by positivity
  have hcanon : ∀ w₁ w₂ w₃ w₄ : Idx, inPL (rhoN N) (LN N) w₁ → inPHc (rhoN N) (LN N) kc w₂ →
      inPL (rhoN N) (LN N) w₃ → inPHc (rhoN N) (LN N) kc w₄ →
      (S9_Gen4 w₁ w₂ w₃ w₄ → S9_T (trialState V w kc N) w₁ w₂ w₃ w₄ ≤ Bg) ∧
        S9_T (trialState V w kc N) w₁ w₂ w₃ w₄ ≤ Bs := fun w₁ w₂ w₃ w₄ h₁ h₂ h₃ h₄ =>
    ⟨fun hGen => S9_gen3 E hC kc h₁ h₂.1 h₃ h₄.1 hGen hPb0 (hP w₁ w₂ h₁ h₂) (hP w₃ w₂ h₃ h₂),
      S9_spec3 E hC kc h₁ h₂.1 h₃ h₄.1⟩
  have hmain := S9_assemble V w kc E.hN (c := .three) (Or.inr (Or.inr (Or.inr rfl))) hV₀ hV₀0
    (S9_S3 BL BH) (S9_sp BL BH ∪ S9_sp BH BL) (by
      rintro ⟨p, q, u⟩ hm -
      obtain ⟨hA, hB⟩ := hm
      unfold S9_S3
      rcases hA with ⟨hp, hq⟩ | ⟨hp, hq⟩ <;> rcases hB with ⟨hr, hs⟩ | ⟨hr, hs⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
        rw [Finset.mem_image]
        exact ⟨(p, q, p - u), Finset.mem_product.2 ⟨hmL _ hp, Finset.mem_product.2
          ⟨hmH _ hq, hmL _ hr⟩⟩, by simp⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
        rw [Finset.mem_image]
        exact ⟨(p, q, q + u), Finset.mem_product.2 ⟨hmL _ hp, Finset.mem_product.2
          ⟨hmH _ hq, hmL _ hs⟩⟩, by simp⟩
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [Finset.mem_image]
        exact ⟨(p, q, p - u), Finset.mem_product.2 ⟨hmH _ hp, Finset.mem_product.2
          ⟨hmL _ hq, hmL _ hr⟩⟩, by simp⟩
      · refine Finset.mem_union_right _ ?_
        rw [Finset.mem_image]
        exact ⟨(p, q, q + u), Finset.mem_product.2 ⟨hmH _ hp, Finset.mem_product.2
          ⟨hmL _ hq, hmL _ hs⟩⟩, by simp⟩) hBg0 hBs0
    (fun x _ hP hGen => by
      obtain ⟨p, q, u⟩ := x
      obtain ⟨w₁, w₂, w₃, w₄, hT, hGw, h₁, h₂, h₃, h₄⟩ := S9_normalize3 hP.1
      rw [hT]
      exact (hcanon w₁ w₂ w₃ w₄ h₁ h₂ h₃ h₄).1 (hGw hGen))
    (fun x _ hP => by
      obtain ⟨p, q, u⟩ := x
      obtain ⟨w₁, w₂, w₃, w₄, hT, hGw, h₁, h₂, h₃, h₄⟩ := S9_normalize3 hP.1
      rw [hT]
      exact (hcanon w₁ w₂ w₃ w₄ h₁ h₂ h₃ h₄).2)
    (by
      rintro ⟨p, q, u⟩ - hP hGen
      exact S9_not_gen3 hρ hρ1 hP.1 hP.2 hGen BL BH hmL hmH)
  refine hmain.trans ?_
  have hnS : ((S9_S3 BL BH).card : ℝ) ≤
      4 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 2 * (67 * (LN N ^ 3 * kc ^ 3))) := by
    refine (S9_S3_card BL BH).trans ?_
    gcongr
  have hnT : (((S9_sp BL BH ∪ S9_sp BH BL).card : ℕ) : ℝ) ≤
      12 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * (67 * (LN N ^ 3 * kc ^ 3))) := by
    have u := Finset.card_union_le (S9_sp BL BH) (S9_sp BH BL)
    have u' : (((S9_sp BL BH ∪ S9_sp BH BL).card : ℕ) : ℝ) ≤
        (S9_sp BL BH).card + (S9_sp BH BL).card := by exact_mod_cast u
    have c1 := S9_sp_card BL BH
    have c2 := S9_sp_card BH BL
    have e : (BH.card : ℝ) * BL.card = (BL.card : ℝ) * BH.card := by ring
    have h4 : (BL.card : ℝ) * BH.card ≤
        (67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * (67 * (LN N ^ 3 * kc ^ 3)) := by gcongr
    linarith only [u', c1, c2, e, h4]
  refine (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hnS hBg0)
    (mul_le_mul_of_nonneg_right hnT hBs0)) (by positivity)).trans ?_
  rw [S9_pref E.hN V₀]
  have hL3' := S9_L3 E.hN
  have hnS' : 4 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 2 * (67 * (LN N ^ 3 * kc ^ 3))) *
      epsP (rhoN N) ^ 1281 ≤ 4 * 67 ^ 3 * kc ^ 3 := by
    calc 4 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) ^ 2 * (67 * (LN N ^ 3 * kc ^ 3))) *
          epsP (rhoN N) ^ 1281
        = 4 * 67 ^ 3 * (LN N ^ 3 * epsP (rhoN N) ^ 625) ^ 3 * kc ^ 3 := by ring
      _ ≤ 4 * 67 ^ 3 * kc ^ 3 := by rw [hL3']; norm_num
  have hnT' : 12 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * (67 * (LN N ^ 3 * kc ^ 3))) *
      epsP (rhoN N) ^ 953 ≤ 12 * 67 ^ 2 * kc ^ 3 := by
    calc 12 * ((67 * (LN N ^ 3 * epsP (rhoN N) ^ 297)) * (67 * (LN N ^ 3 * kc ^ 3))) *
          epsP (rhoN N) ^ 953
        = 12 * 67 ^ 2 * (LN N ^ 3 * epsP (rhoN N) ^ 625) ^ 2 * kc ^ 3 := by ring
      _ ≤ 12 * 67 ^ 2 * kc ^ 3 := by rw [hL3']; norm_num
  have hBgle := S9_arith3 V w E hC (K := kc) (C' := Cp) (Pb := Pb) hkc hPb0 hPb'
  have hBsle := S9_arith3s V w E hC
  have hcl := S9_close (t := epsP (rhoN N)) (V₀ := V₀) (P := 750) (a := 1281) (b := 953)
    (e := 579) (f := 0) (f' := 395) (k := 4)
    (cS := 4 * 67 ^ 3 * kc ^ 3) (cT := 12 * 67 ^ 2 * kc ^ 3)
    (cg := (Real.sqrt (2 * g0 V w) * (8 * C * g0 V w + 4 * C + 8 * Cp)) * kc ^ 3)
    (cs := 2 * C * g0 V w) ht ht1 hV₀0 (by positivity) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity) hnS' hnT' hBgle
    (by simpa using hBsle) (by norm_num) (by norm_num)
  refine hcl.trans ?_
  have hk6 : kc ^ 3 ≤ kc ^ 6 := pow_le_pow_right₀ hkc (by norm_num)
  have hA : 0 ≤ 12 * 67 ^ 2 * (2 * C * g0 V w) := by positivity
  calc V₀ * (4 * 67 ^ 3 * kc ^ 3 * ((Real.sqrt (2 * g0 V w) * (8 * C * g0 V w + 4 * C + 8 * Cp)) *
        kc ^ 3) + 12 * 67 ^ 2 * kc ^ 3 * (2 * C * g0 V w)) * epsP (rhoN N) ^ 4
      = V₀ * (4 * 67 ^ 3 * (Real.sqrt (2 * g0 V w) * (8 * C * g0 V w + 4 * C + 8 * Cp)) * kc ^ 6 +
        12 * 67 ^ 2 * (2 * C * g0 V w) * kc ^ 3) * epsP (rhoN N) ^ 4 := by ring
    _ ≤ V₀ * (4 * 67 ^ 3 * (Real.sqrt (2 * g0 V w) * (8 * C * g0 V w + 4 * C + 8 * Cp)) * kc ^ 6 +
        12 * 67 ^ 2 * (2 * C * g0 V w) * kc ^ 6) * epsP (rhoN N) ^ 4 := by gcongr
    _ = _ := by ring

/-- Proposition 9.1, (9.4) [temp8.119], with the rate `C k_c³ |λ_v| ρ^{3-7η} + C |λ_v| ρ^{1-3η} |Λ|⁻¹`
uniform in `k_c ≥ 1`, `u ∈ P_L`, `v ∈ P_{H,c}`. -/
theorem Prop9_1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc → ∀ u v : Idx,
      inPL (rhoN N) (LN N) u → inPHc (rhoN N) (LN N) kc v →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
          (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        C * kc ^ 3 * |lam V w (rhoN N) (LN N) v| * rhoN N ^ (3 - 7/200 : ℝ) +
          C * |lam V w (rhoN N) (LN N) v| * rhoN N ^ (1 - 3/200 : ℝ) / LN N ^ 3 := by
  obtain ⟨C, hC, N₀, h⟩ := S9_prop91_rate hV hw
  refine ⟨C, hC, N₀, fun N hN kc hkc u v hu hv => ?_⟩
  have h1 := h N hN kc u v hu hv
  rw [max_eq_left hkc] at h1
  rw [S9_rpow_eps (S9_rho_nonneg N) 593 (x := 3 - 7 / 200) (by norm_num),
    S9_rpow_eps (S9_rho_nonneg N) 197 (x := 1 - 3 / 200) (by norm_num)]
  exact h1

/-- Proposition 9.1, (9.4) [temp8.119]: for every `k_c`, eventually in `N`,
`Σ_{α ∈ M_u^a} α(v) |Ψ(α)|² ≤ |λ_v| ρ^{3 - 1/10}` for `u ∈ P_L`, `v ∈ P_{H,c}`. -/
theorem Prop9_1_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ kc : ℝ, ∀ᶠ N in atTop, ∀ u v : Idx,
      inPL (rhoN N) (LN N) u → inPHc (rhoN N) (LN N) kc v →
      (∑' α : Occ, if InMuA (rhoN N) (LN N) kc N u α then
          (α v : ℝ) * ‖trialState V w kc N α‖ ^ 2 else 0) ≤
        |lam V w (rhoN N) (LN N) v| * rhoN N ^ (3 - 1/10 : ℝ) := by
  intro kc
  obtain ⟨C, hC, N₀, h⟩ := S9_prop91_rate hV hw
  set K := max kc 1 with hK
  have hK0 : 0 ≤ K := le_trans zero_le_one (le_max_right _ _)
  have t1 : Tendsto (fun N : ℕ => epsP (rhoN N)) atTop (𝓝 0) := S9_tendsto_rpow (a := 1 / 200)
    (by norm_num)
  have e1 : Tendsto (fun N : ℕ => C * K ^ 3 * epsP (rhoN N) ^ 13) atTop (𝓝 0) := by
    simpa using (t1.pow 13).const_mul (C * K ^ 3)
  have e2 : Tendsto (fun N : ℕ => C * epsP (rhoN N) ^ 242) atTop (𝓝 0) := by
    simpa using (t1.pow 242).const_mul C
  filter_upwards [eventually_ge_atTop (max N₀ 1), e1.eventually_le_const (u := 1 / 2) (by norm_num),
    e2.eventually_le_const (u := 1 / 2) (by norm_num)] with N hN hN1 hN2 u v hu hv
  have hN' : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1' : 1 ≤ N := le_trans (le_max_right _ _) hN
  have h1 := h N hN' kc u v hu hv
  obtain ⟨-, hρ, hρ1, hL⟩ := Particles_rhoN_LN hN1'
  have ht := S9_eps_pos hρ
  have hL3 : 1 / LN N ^ 3 = epsP (rhoN N) ^ 625 := by
    have := S9_L3 hN1'
    have h0 : LN N ^ 3 ≠ 0 := by positivity
    field_simp
    linarith
  rw [S9_rpow_eps (S9_rho_nonneg N) 580 (x := 3 - 1 / 10) (by norm_num)]
  refine h1.trans ?_
  set a := |lam V w (rhoN N) (LN N) v| with ha
  have ha0 : 0 ≤ a := abs_nonneg _
  have e3 : C * a * epsP (rhoN N) ^ 197 / LN N ^ 3 = C * a * epsP (rhoN N) ^ 822 := by
    rw [div_eq_mul_one_div, hL3]; ring
  rw [e3]
  have h4 : C * K ^ 3 * a * epsP (rhoN N) ^ 593 + C * a * epsP (rhoN N) ^ 822 =
      a * epsP (rhoN N) ^ 580 * (C * K ^ 3 * epsP (rhoN N) ^ 13 + C * epsP (rhoN N) ^ 242) := by
    ring
  rw [h4]
  have h5 : C * K ^ 3 * epsP (rhoN N) ^ 13 + C * epsP (rhoN N) ^ 242 ≤ 1 := by linarith
  have h6 : 0 ≤ a * epsP (rhoN N) ^ 580 := by positivity
  calc a * epsP (rhoN N) ^ 580 * (C * K ^ 3 * epsP (rhoN N) ^ 13 + C * epsP (rhoN N) ^ 242)
      ≤ a * epsP (rhoN N) ^ 580 * 1 := mul_le_mul_of_nonneg_left h5 h6
    _ = _ := by ring

/-- Lemma 9.2, (9.8) [resultasymno24L] with a rate: case 1 of Lemma 9.1 [fourlegslemma1]. -/
theorem Lemma9_2_case1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ,
      FourLegs.absPart V w .one kc N ≤ C * rhoN N ^ (2/5 : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := S9_class1 hV hw
  refine ⟨C, hC, N₀, fun N hN kc => ?_⟩
  rw [S9_rpow_eps (S9_rho_nonneg N) 80 (x := 2 / 5) (by norm_num)]
  exact h N hN kc

/-- Lemma 9.2, (9.9) [resultasymno22L2H1] with a rate: case 2 of Lemma 9.1 [fourlegslemma1]
and the same case with `(v₁, v₂)` and `(v₃, v₄)` exchanged. -/
theorem Lemma9_2_case2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc →
      FourLegs.absPart V w .two kc N ≤ C * kc ^ 3 * rhoN N ^ (1/20 : ℝ) ∧
        FourLegs.absPart V w .twoAdj kc N ≤ C * kc ^ 3 * rhoN N ^ (1/20 : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := S9_class2 hV hw
  refine ⟨C, hC, N₀, fun N hN kc hkc => ?_⟩
  rw [S9_rpow_eps (S9_rho_nonneg N) 10 (x := 1 / 20) (by norm_num)]
  exact h N hN kc hkc

/-- Lemma 9.2, (9.10) [resultasymno22L2H2] with a rate: case 3 of Lemma 9.1 [fourlegslemma1],
all four placements of the `P_L` legs. -/
theorem Lemma9_2_case3 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ kc : ℝ, 1 ≤ kc →
      FourLegs.absPart V w .three kc N ≤ C * kc ^ 6 * rhoN N ^ (1/50 : ℝ) := by
  obtain ⟨C, hC, N₀, h⟩ := S9_class3 hV hw
  refine ⟨C, hC, N₀, fun N hN kc hkc => ?_⟩
  rw [S9_rpow_eps (S9_rho_nonneg N) 4 (x := 1 / 50) (by norm_num)]
  exact h N hN kc hkc

private lemma S9_absPart_nonneg (V w : R3 → ℝ) (c : FourLegs.Cls) (kc : ℝ) (N : ℕ) :
    0 ≤ FourLegs.absPart V w c kc N := by
  unfold FourLegs.absPart
  refine div_nonneg (tsum_nonneg fun i => ?_) ?_
  · split_ifs <;> positivity
  · have : 0 ≤ LN N := Real.rpow_nonneg (S9_rho_nonneg N) _
    have : 0 ≤ rhoN N ^ (5 / 2 : ℝ) := Real.rpow_nonneg (S9_rho_nonneg N) _
    positivity

/-- Lemma 9.2, (9.8)–(9.10), as limits in `N` for each `k_c ≥ 1`. -/
theorem Lemma9_2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∀ kc : ℝ, 1 ≤ kc →
      Tendsto (fun N => FourLegs.absPart V w .one kc N) atTop (𝓝 0) ∧
      Tendsto (fun N => FourLegs.absPart V w .two kc N + FourLegs.absPart V w .twoAdj kc N)
        atTop (𝓝 0) ∧
      Tendsto (fun N => FourLegs.absPart V w .three kc N) atTop (𝓝 0) := by
  intro kc hkc
  obtain ⟨C₁, hC₁, N₁, h₁⟩ := Lemma9_2_case1 hV hw
  obtain ⟨C₂, hC₂, N₂, h₂⟩ := Lemma9_2_case2 hV hw
  obtain ⟨C₃, hC₃, N₃, h₃⟩ := Lemma9_2_case3 hV hw
  have t1 : ∀ a : ℝ, 0 < a → Tendsto (fun N : ℕ => rhoN N ^ a) atTop (𝓝 0) :=
    fun a ha => S9_tendsto_rpow ha
  refine ⟨?_, ?_, ?_⟩
  · refine squeeze_zero' (Filter.Eventually.of_forall fun N => S9_absPart_nonneg V w _ kc N)
      ((eventually_ge_atTop N₁).mono fun N hN => h₁ N hN kc) ?_
    simpa using (t1 (2 / 5) (by norm_num)).const_mul C₁
  · refine squeeze_zero' (g := fun N : ℕ => 2 * (C₂ * kc ^ 3) * rhoN N ^ (1 / 20 : ℝ))
      (Filter.Eventually.of_forall fun N =>
      add_nonneg (S9_absPart_nonneg V w _ kc N) (S9_absPart_nonneg V w _ kc N))
      ((eventually_ge_atTop N₂).mono fun N hN => (add_le_add (h₂ N hN kc hkc).1
        (h₂ N hN kc hkc).2).trans_eq (by ring)) ?_
    simpa using (t1 (1 / 20) (by norm_num)).const_mul (2 * (C₂ * kc ^ 3))
  · refine squeeze_zero' (Filter.Eventually.of_forall fun N => S9_absPart_nonneg V w _ kc N)
      ((eventually_ge_atTop N₃).mono fun N hN => h₃ N hN kc hkc) ?_
    simpa using (t1 (1 / 50) (by norm_num)).const_mul (C₃ * kc ^ 6)

end LHYUpper
