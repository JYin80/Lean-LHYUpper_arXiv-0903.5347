module

public import LHYUpper.Fock.Decomp
public import LHYUpper.Riemann.Cells
public import LHYUpper.Scattering.Solution
public import LHYUpper.TrialState.Legs
public import LHYUpper.TrialState.Normalization

@[expose] public section

open MeasureTheory Filter Topology Real
open scoped BigOperators ComplexConjugate

noncomputable section
open Classical

namespace LHYUpper

/-- `⟨Ψ, a†_0 a†_{v₁} a_{v₂} a_{v₃} Ψ⟩ = Σ_β conj(Ψ(α)) ⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ Ψ(β)`
with `α = T(β)`, Lemma 7.1 [id4a]. -/
def OneLeg_expA (Ψ : Occ → ℂ) (v₁ v₂ v₃ : Idx) : ℂ :=
  ∑' β : Occ, conj (Ψ (a4 0 v₁ v₂ v₃ β).2) * ((a4 0 v₁ v₂ v₃ β).1 : ℂ) * Ψ β

/-- `Σ_β |Ψ(α)| ⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ |Ψ(β)|` with `α = T(β)`: the bound for
`|⟨a†_0 a†_{v₁} a_{v₂} a_{v₃}⟩_Ψ|` in (8.30)–(8.34). -/
def OneLeg_absA (Ψ : Occ → ℂ) (v₁ v₂ v₃ : Idx) : ℝ :=
  ∑' β : Occ, ‖Ψ (a4 0 v₁ v₂ v₃ β).2‖ * (a4 0 v₁ v₂ v₃ β).1 * ‖Ψ β‖

/-- The summand `V_{v₂} conj(Ψ(α)) ⟨α| a†_0 a†_{v₁} a_{v₂} a_{v₃} |β⟩ Ψ(β)` of the first half
of (4.6), `v₃ = v₁ - v₂`, at the index `(v₁, v₂, β)`; zero unless `v₁, v₂, v₃ ≠ 0`. -/
def OneLeg_term (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Occ) : ℂ :=
  if i.1 ≠ 0 ∧ i.2.1 ≠ 0 ∧ i.1 - i.2.1 ≠ 0 then
    ft V (mom L i.2.1) * conj (Ψ (a4 0 i.1 i.2.1 (i.1 - i.2.1) i.2.2).2) *
      ((a4 0 i.1 i.2.1 (i.1 - i.2.1) i.2.2).1 : ℂ) * Ψ i.2.2
  else 0

/-- Case (8.2) [one0firstcase] of Lemma 8.1 [posscombone0] for `(v₁, v₂, v₁ - v₂)`. -/
def OneLeg_case1 (ρ L kc : ℝ) (v₁ v₂ : Idx) : Prop :=
  inPL ρ L v₁ ∧ inPHc ρ L kc v₂ ∧ inPHc ρ L kc (v₁ - v₂)

/-- Case (8.3) [one0secondcase] of Lemma 8.1 [posscombone0] for `(v₁, v₂, v₁ - v₂)`, both
orderings. -/
def OneLeg_case2 (ρ L kc : ℝ) (v₁ v₂ : Idx) : Prop :=
  (inPHc ρ L kc v₁ ∧ inPL ρ L v₂ ∧ inPHc ρ L kc (v₁ - v₂)) ∨
    (inPHc ρ L kc v₁ ∧ inPHc ρ L kc v₂ ∧ inPL ρ L (v₁ - v₂))

/-- Case (8.4) [one0thirdcase] of Lemma 8.1 [posscombone0] for `(v₁, v₂, v₁ - v₂)`. -/
def OneLeg_case3 (ρ L : ℝ) (v₁ v₂ : Idx) : Prop :=
  inPL ρ L v₁ ∧ inPL ρ L v₂ ∧ inPL ρ L (v₁ - v₂)

/-! ### The adjoint involution and the restrictions of the interaction summands -/

private theorem Forms_mom_neg (L : ℝ) (u : Idx) : mom L (-u) = -mom L u := by
  ext k
  simp [mom]

private theorem Forms_mom_zero (u : Idx) : mom 0 u = 0 := by
  ext k
  simp [mom]

/-- `conj(V_p) = V_{-p}` for real `V`. -/
private theorem Forms_ft_conj (V : R3 → ℝ) (x : R3) : conj (ft V x) = ft V (-x) := by
  unfold ft
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I,
    inner_neg_left]
  push_cast
  ring_nf

/-- `V_{-p} = V_p` for even `V`. -/
private theorem Forms_ft_neg {V : R3 → ℝ} (heven : ∀ x, V (-x) = V x) (x : R3) :
    ft V (-x) = ft V x := by
  have h := integral_neg_eq_self
    (fun y : R3 => Complex.exp (-(Complex.I * ((inner ℝ (-x) y : ℝ) : ℂ))) * (V y : ℂ)) volume
  unfold ft
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [inner_neg_left, inner_neg_right, heven]

/-- The involution `(p, q, u, α) ↦ (p - u, q + u, -u, T(α))` of the interaction index set of
(2.1) [ham], which pairs each term with the term of its adjoint. -/
private def Forms_inv (i : Idx × Idx × Idx × Occ) : Idx × Idx × Idx × Occ :=
  (i.1 - i.2.2.1, i.2.1 + i.2.2.1, -i.2.2.1,
    (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).2)

/-- Coefficient of `a4` at the index `i`. -/
private def Forms_coef (i : Idx × Idx × Idx × Occ) : ℝ :=
  (a4 i.1 i.2.1 (i.1 - i.2.2.1) (i.2.1 + i.2.2.1) i.2.2.2).1

private theorem Forms_a4_inv (i : Idx × Idx × Idx × Occ) (h : Forms_coef i ≠ 0) :
    a4 (Forms_inv i).1 (Forms_inv i).2.1 ((Forms_inv i).1 - (Forms_inv i).2.2.1)
      ((Forms_inv i).2.1 + (Forms_inv i).2.2.1) (Forms_inv i).2.2.2 = (Forms_coef i, i.2.2.2) := by
  obtain ⟨p, q, u, α⟩ := i
  simp only [Forms_inv, Forms_coef] at h ⊢
  rw [sub_neg_eq_add, sub_add_cancel, add_neg_cancel_right, a4_comm]
  exact a4_adjoint p q (p - u) (q + u) α h

private theorem Forms_inv_inv (i : Idx × Idx × Idx × Occ) (h : Forms_coef i ≠ 0) :
    Forms_inv (Forms_inv i) = i := by
  have h4 := Forms_a4_inv i h
  obtain ⟨p, q, u, α⟩ := i
  simp only [Forms_inv] at h4 ⊢
  rw [h4]
  simp only [sub_neg_eq_add, sub_add_cancel, add_neg_cancel_right, neg_neg]

private theorem Forms_intTerm_inv (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ)
    (i : Idx × Idx × Idx × Occ) (h : Forms_coef i ≠ 0) :
    intTerm L V Ψ (Forms_inv i) = conj (intTerm L V Ψ i) := by
  have h4 := Forms_a4_inv i h
  obtain ⟨p, q, u, α⟩ := i
  simp only [intTerm] at h4 ⊢
  rw [h4]
  simp only [Forms_inv, Forms_coef, map_mul, Complex.conj_ofReal,
    Complex.conj_conj, Forms_ft_conj, Forms_mom_neg]
  ring

private theorem Forms_coef_ne_zero {L : ℝ} {V : R3 → ℝ} {Ψ : Occ → ℂ}
    {i : Idx × Idx × Idx × Occ} (h : intTerm L V Ψ i ≠ 0) : Forms_coef i ≠ 0 := by
  intro h0
  apply h
  simp only [intTerm]
  simp only [Forms_coef] at h0
  rw [h0]
  simp

/-- The interaction summands of (2.1) [ham] restricted to the `(p, q, u)` with `P p q u`. -/
private def Forms_res (P : Idx → Idx → Idx → Prop) (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ)
    (i : Idx × Idx × Idx × Occ) : ℂ :=
  if P i.1 i.2.1 i.2.2.1 then intTerm L V Ψ i else 0

/-- The adjoint involution maps the restriction to `P` onto the restriction to
`(p, q, u) ↦ P (p - u) (q + u) (-u)` and conjugates the summands. -/
private theorem Forms_res_conj (P : Idx → Idx → Idx → Prop) (L : ℝ) (V : R3 → ℝ)
    (Ψ : Occ → ℂ) (X : ℂ) (h : HasSum (Forms_res P L V Ψ) X) :
    HasSum (Forms_res (fun p q u => P (p - u) (q + u) (-u)) L V Ψ) (conj X) := by
  have hc : ∀ x, Forms_res P L V Ψ x ≠ 0 → P x.1 x.2.1 x.2.2.1 ∧ Forms_coef x ≠ 0 := by
    intro x hx
    unfold Forms_res at hx
    by_cases hP : P x.1 x.2.1 x.2.2.1
    · simp only [hP, ↓reduceIte] at hx
      exact ⟨hP, Forms_coef_ne_zero hx⟩
    · simp only [hP, ↓reduceIte] at hx
      exact absurd rfl hx
  have hsupp : ∀ x : Function.support (fun x => conj (Forms_res P L V Ψ x)),
      Forms_res P L V Ψ x.1 ≠ 0 := fun x hx => x.2 (by simp [hx])
  refine (hasSum_iff_hasSum_of_ne_zero_bij (g := fun x => conj (Forms_res P L V Ψ x))
    (fun x => Forms_inv x.1) ?_ ?_ ?_).mpr (Complex.hasSum_conj'.mpr h)
  · intro x y hxy
    apply Subtype.ext
    have := congrArg Forms_inv hxy
    simp only at this
    rwa [Forms_inv_inv _ (hc _ (hsupp x)).2, Forms_inv_inv _ (hc _ (hsupp y)).2] at this
  · intro y hy
    have hy' : Forms_res (fun p q u => P (p - u) (q + u) (-u)) L V Ψ y ≠ 0 := hy
    obtain ⟨p, q, u, α⟩ := y
    unfold Forms_res at hy'
    by_cases hP : P (p - u) (q + u) (-u)
    · simp only [hP, ↓reduceIte] at hy'
      have hco := Forms_coef_ne_zero hy'
      refine ⟨⟨Forms_inv (p, q, u, α), ?_⟩, Forms_inv_inv _ hco⟩
      simp only [Function.mem_support, Forms_res, Forms_inv]
      rw [ne_eq, map_eq_zero]
      simp only [hP, ↓reduceIte]
      have := Forms_intTerm_inv L V Ψ (p, q, u, α) hco
      simp only [Forms_inv] at this
      rw [this, map_eq_zero]
      exact hy'
    · simp only [hP, ↓reduceIte] at hy'
      exact absurd rfl hy'
  · rintro ⟨⟨p, q, u, α⟩, hx⟩
    obtain ⟨hP, hco⟩ := hc (p, q, u, α) (hsupp ⟨_, hx⟩)
    simp only at hP
    have hP' : P (p - u - -u) (q + u + -u) (- -u) := by
      simpa only [sub_neg_eq_add, sub_add_cancel, add_neg_cancel_right, neg_neg] using hP
    have := Forms_intTerm_inv L V Ψ (p, q, u, α) hco
    simp only [Forms_res, Forms_inv] at this ⊢
    simp only [hP', hP, ↓reduceIte, this]

/-- The family `p = 0` of `H_{A1}`: `a†_0 a†_q a_{-u} a_{q+u}`. -/
private def Forms_Fp (p q u : Idx) : Prop := p = 0 ∧ q ≠ 0 ∧ p - u ≠ 0 ∧ q + u ≠ 0

/-- The family `q = 0` of `H_{A1}`: `a†_p a†_0 a_{p-u} a_u`. -/
private def Forms_Fq (p q u : Idx) : Prop := p ≠ 0 ∧ q = 0 ∧ p - u ≠ 0 ∧ q + u ≠ 0

/-- The embedding `(v₁, v₂, β) ↦ (0, v₁, -v₂, β)` onto the family `p = 0`. -/
private def Forms_e1 (i : Idx × Idx × Occ) : Idx × Idx × Idx × Occ := (0, i.1, -i.2.1, i.2.2)

/-- The embedding `(v₁, v₂, β) ↦ (v₁, 0, v₂, β)` onto the family `q = 0`. -/
private def Forms_e2 (i : Idx × Idx × Occ) : Idx × Idx × Idx × Occ := (i.1, 0, i.2.1, i.2.2)

private theorem Forms_e1_inj : Function.Injective Forms_e1 := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Forms_e1, Prod.mk.injEq, true_and, neg_inj] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

private theorem Forms_e2_inj : Function.Injective Forms_e2 := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [Forms_e2, Prod.mk.injEq, true_and] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- On the family `p = 0`, the summand of (2.1) [ham] is `|Λ|⁻¹` times the summand of (4.6),
for even `V`. -/
private theorem Forms_res_e1 (L : ℝ) {V : R3 → ℝ} (heven : ∀ x, V (-x) = V x) (Ψ : Occ → ℂ)
    (i : Idx × Idx × Occ) :
    Forms_res Forms_Fp L V Ψ (Forms_e1 i) = ((L : ℂ) ^ 3)⁻¹ * OneLeg_term L V Ψ i := by
  obtain ⟨v₁, v₂, β⟩ := i
  simp only [Forms_res, Forms_Fp, Forms_e1, OneLeg_term, intTerm, zero_sub, neg_neg,
    ← sub_eq_add_neg, Forms_mom_neg, Forms_ft_neg heven, true_and]
  split_ifs <;> push_cast <;> ring

/-- On the family `q = 0`, the summand of (2.1) [ham] is `|Λ|⁻¹` times the summand of (4.6). -/
private theorem Forms_res_e2 (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (i : Idx × Idx × Occ) :
    Forms_res Forms_Fq L V Ψ (Forms_e2 i) = ((L : ℂ) ^ 3)⁻¹ * OneLeg_term L V Ψ i := by
  obtain ⟨v₁, v₂, β⟩ := i
  simp only [Forms_res, Forms_Fq, Forms_e2, OneLeg_term, intTerm, zero_add, true_and,
    a4_comm v₁ 0 (v₁ - v₂) v₂]
  by_cases h : v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ - v₂ ≠ 0
  · have h' : v₁ ≠ 0 ∧ v₁ - v₂ ≠ 0 ∧ v₂ ≠ 0 := ⟨h.1, h.2.2, h.2.1⟩
    rw [ite_eq_left h', ite_eq_left h]
    push_cast
    ring
  · have h' : ¬(v₁ ≠ 0 ∧ v₁ - v₂ ≠ 0 ∧ v₂ ≠ 0) := fun h' => h ⟨h'.1, h'.2.2, h'.2.1⟩
    rw [ite_eq_right h', ite_eq_right h, mul_zero]

/-- The number of zero momenta among `p, q, p - u, q + u`. -/
private theorem Forms_zeros (p q u : Idx) :
    Decomp.zeros p q u = (if p = 0 then 1 else 0) + (if q = 0 then 1 else 0) +
      (if p - u = 0 then 1 else 0) + (if q + u = 0 then 1 else 0) := rfl

/-- `H_{A1}` is the sum of the four families `p = 0`, `q = 0`, `p - u = 0`, `q + u = 0`. -/
private theorem Forms_partTerm_A1 (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) :
    Decomp.partTerm .A1 L V Ψ =
      Forms_res Forms_Fp L V Ψ + Forms_res Forms_Fq L V Ψ +
        Forms_res (fun p q u => Forms_Fp (p - u) (q + u) (-u)) L V Ψ +
        Forms_res (fun p q u => Forms_Fq (p - u) (q + u) (-u)) L V Ψ := by
  funext ⟨p, q, u, α⟩
  simp only [Decomp.partTerm, Decomp.Part.mem, Forms_zeros, Forms_res, Forms_Fp, Forms_Fq,
    Pi.add_apply, sub_neg_eq_add, sub_add_cancel, add_neg_cancel_right, ne_eq]
  by_cases hr : p - u = 0 <;> by_cases hs : q + u = 0 <;> simp only [hr, hs] <;>
    by_cases hp : p = 0 <;> by_cases hq : q = 0 <;> simp [hp, hq]

/-- `Σ_{u ∈ Λ*} |V_u| < ∞` on the torus of side `L ≥ 2π`. -/
theorem OneLeg_summable_V {V : R3 → ℝ} (hV : PotentialHyp V) {L : ℝ} (hL : 2 * π ≤ L) :
    Summable fun u : Idx => ‖ft V (mom L u)‖ := by
  obtain ⟨C, hC⟩ := scat_lattice_V hV
  exact (hC L (by nlinarith [Real.pi_gt_three])).1

/-- The summands of the first half of (4.6) are absolutely summable for a normalized
`N`-particle state. -/
theorem OneLeg_summable (L : ℝ) (V : R3 → ℝ) (N : ℕ) (Ψ : Occ → ℂ)
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (hΨ : IsNState N Ψ) :
    Summable fun i => ‖OneLeg_term L V Ψ i‖ := by
  by_cases hL : L = 0
  · subst hL
    have h0 : ft V 0 = 0 := by
      have h := hV
      simp only [Forms_mom_zero] at h
      exact norm_eq_zero.mp ((summable_const_iff _).mp h)
    have hz : ∀ i, OneLeg_term 0 V Ψ i = 0 := fun i => by
      simp [OneLeg_term, Forms_mom_zero, h0]
    simp only [hz, norm_zero]
    exact summable_zero
  have hs := ((Decomp.intTerm_summable_norm L V N Ψ hV hΨ).comp_injective Forms_e2_inj).mul_left
    (|L| ^ 3)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_) hs
  have h := Forms_res_e2 L V Ψ i
  have hle : ‖Forms_res Forms_Fq L V Ψ (Forms_e2 i)‖ ≤ ‖intTerm L V Ψ (Forms_e2 i)‖ := by
    unfold Forms_res
    split_ifs
    · exact le_rfl
    · simp
  have hL3 : (0 : ℝ) < |L| ^ 3 := by positivity
  have heq : ‖OneLeg_term L V Ψ i‖ = |L| ^ 3 * ‖Forms_res Forms_Fq L V Ψ (Forms_e2 i)‖ := by
    rw [h, norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← mul_assoc,
      mul_inv_cancel₀ hL3.ne', one_mul]
  rw [heq, Function.comp_apply]
  exact mul_le_mul_of_nonneg_left hle hL3.le

/-- (4.6): for an even `V` and a normalized `N`-particle state, the part `H_{A1}` of (2.1) [ham]
has the sum `4 |Λ|⁻¹ Re Σ_{v₁ = v₂ + v₃} V_{v₂} ⟨a†_0 a†_{v₁} a_{v₂} a_{v₃}⟩_Ψ`. -/
theorem OneLeg_hasSum_A1 (L : ℝ) (V : R3 → ℝ) (N : ℕ) (Ψ : Occ → ℂ)
    (hV : Summable fun u : Idx => ‖ft V (mom L u)‖) (heven : ∀ x, V (-x) = V x)
    (hΨ : IsNState N Ψ) :
    HasSum (Decomp.partTerm .A1 L V Ψ)
      ((4 * (L ^ 3)⁻¹ * (∑' i, OneLeg_term L V Ψ i).re : ℝ) : ℂ) := by
  have hT := (Summable.of_norm (OneLeg_summable L V N Ψ hV hΨ)).hasSum
  set T := ∑' i, OneLeg_term L V Ψ i
  set c : ℂ := ((L : ℂ) ^ 3)⁻¹
  have hp : HasSum (Forms_res Forms_Fp L V Ψ) (c * T) := by
    refine (Forms_e1_inj.hasSum_iff fun x hx => ?_).mp ?_
    · obtain ⟨p, q, u, α⟩ := x
      unfold Forms_res
      split_ifs with h
      · exfalso
        obtain ⟨rfl, -⟩ := h
        exact hx ⟨(q, -u, α), by simp [Forms_e1]⟩
      · rfl
    · have : Forms_res Forms_Fp L V Ψ ∘ Forms_e1 = fun i => c * OneLeg_term L V Ψ i :=
        funext fun i => Forms_res_e1 L heven Ψ i
      rw [this]
      exact hT.mul_left c
  have hq : HasSum (Forms_res Forms_Fq L V Ψ) (c * T) := by
    refine (Forms_e2_inj.hasSum_iff fun x hx => ?_).mp ?_
    · obtain ⟨p, q, u, α⟩ := x
      unfold Forms_res
      split_ifs with h
      · exfalso
        obtain ⟨-, rfl, -⟩ := h
        exact hx ⟨(p, u, α), by simp [Forms_e2]⟩
      · rfl
    · have : Forms_res Forms_Fq L V Ψ ∘ Forms_e2 = fun i => c * OneLeg_term L V Ψ i :=
        funext fun i => Forms_res_e2 L V Ψ i
      rw [this]
      exact hT.mul_left c
  have h := ((hp.add hq).add (Forms_res_conj _ L V Ψ _ hp)).add (Forms_res_conj _ L V Ψ _ hq)
  rw [Forms_partTerm_A1]
  convert h using 1
  have hc : c = (((L ^ 3)⁻¹ : ℝ) : ℂ) := by simp [c]
  rw [hc]
  apply Complex.ext <;> simp <;> ring

/-- Lemma 8.1 [posscombone0] for the summands of the trial state: each summand lies in exactly
one of the cases (8.2)–(8.4) or vanishes. -/
theorem OneLeg_split (V w : R3 → ℝ) (kc : ℝ) {N : ℕ} (hN : 1 ≤ N) (i : Idx × Idx × Occ) :
    OneLeg_term (LN N) V (trialState V w kc N) i =
      (if OneLeg_case1 (rhoN N) (LN N) kc i.1 i.2.1 then
          OneLeg_term (LN N) V (trialState V w kc N) i else 0) +
        (if OneLeg_case2 (rhoN N) (LN N) kc i.1 i.2.1 then
          OneLeg_term (LN N) V (trialState V w kc N) i else 0) +
        (if OneLeg_case3 (rhoN N) (LN N) i.1 i.2.1 then
          OneLeg_term (LN N) V (trialState V w kc N) i else 0) := by
  have hρ : 0 < rhoN N := Real.rpow_pos_of_pos (by exact_mod_cast hN) _
  set Ψ := trialState V w kc N with hΨdef
  obtain ⟨v₁, v₂, β⟩ := i
  by_cases ht : OneLeg_term (LN N) V Ψ (v₁, v₂, β) = 0
  · rw [ht]
    simp
  have hM : ∀ α, Ψ α ≠ 0 → InM (rhoN N) (LN N) kc N α := fun α hα => by
    by_contra h
    exact hα (by simp [hΨdef, trialState, h])
  have ht' := ht
  unfold OneLeg_term at ht'
  simp only at ht'
  split_ifs at ht' with hcond
  · obtain ⟨h1, h2, h3⟩ := hcond
    simp only [mul_eq_zero, map_eq_zero, Complex.ofReal_eq_zero, not_or] at ht'
    obtain ⟨⟨⟨-, hα⟩, hc⟩, hβ⟩ := ht'
    have hcase := Lemma8_1 hρ h1 h2 h3 (hM _ hα) (hM _ hβ) hc rfl
    rcases hcase with ⟨hL1, hH2, hH3, -⟩ | ⟨hH1, -⟩ | ⟨hL1, hL2, hL3⟩
    · have n2 : ¬ OneLeg_case2 (rhoN N) (LN N) kc v₁ v₂ := by
        rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact Regions_PL_PH hρ hL1 h.1
      have n3 : ¬ OneLeg_case3 (rhoN N) (LN N) v₁ v₂ := fun h =>
        Regions_PL_PH hρ h.2.1 hH2.1
      have y1 : OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂ := ⟨hL1, hH2, hH3⟩
      simp only [y1, n2, n3, ↓reduceIte]
      ring
    · have hH1' : inPHc (rhoN N) (LN N) kc v₁ := by rcases hH1 with h | h <;> exact h.1
      have n1 : ¬ OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂ := fun h =>
        Regions_PL_PH hρ h.1 hH1'.1
      have n3 : ¬ OneLeg_case3 (rhoN N) (LN N) v₁ v₂ := fun h =>
        Regions_PL_PH hρ h.1 hH1'.1
      have y2 : OneLeg_case2 (rhoN N) (LN N) kc v₁ v₂ := hH1
      simp only [n1, y2, n3, ↓reduceIte]
      ring
    · have n1 : ¬ OneLeg_case1 (rhoN N) (LN N) kc v₁ v₂ := fun h =>
        Regions_PL_PH hρ hL2 h.2.1.1
      have n2 : ¬ OneLeg_case2 (rhoN N) (LN N) kc v₁ v₂ := by
        rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact Regions_PL_PH hρ hL1 h.1
      have y3 : OneLeg_case3 (rhoN N) (LN N) v₁ v₂ := ⟨hL1, hL2, hL3⟩
      simp only [n1, n2, y3, ↓reduceIte]
      ring
  · exact absurd rfl ht'

end LHYUpper
