# The paper and the Lean code

This document states what the Lean code in `LHYUpper/` proves, and how its statements relate to the results of

> H.-T. Yau and J. Yin, *The Second Order Upper Bound for the Ground Energy of a Bose Gas*, arXiv:0903.5347.

Theorem, lemma, proposition, section and equation numbers are those of the compiled paper. The final version of the paper in `paper/` keeps this numbering; it adds §12.1, §12.2 and Appendix A, and corrects the arXiv version as described in §3 (b). The theorem-like environments have separate counters within each section, so Theorem 2.1 and Lemma 2.1 are different items. The TeX label of an item is given in brackets the first time it appears, for example Theorem 2.1 [mainthm] and Lemma 2.1 [thm1].

All declarations lie in `namespace LHYUpper`; names are written below without this prefix. The library is `LHYUpper.lean` with the modules under `LHYUpper/`. The Lean code blocks are copied verbatim from the source files, with the docstring; for theorems the proof after := is omitted, definitions are quoted whole.

## 1. What is proved

### Common objects

**The model.** The box is Λ = [0, L]³ with periodic boundary condition and dual lattice Λ* = (2π/L)ℤ³. `R3` is ℝ³, `Idx` is ℤ³, and `mom` L n is the momentum (2π/L)n. `ft` is the Fourier transform W_p = ∫_{ℝ³} e^{−ipx} W(x) dx of §2. The bosonic Fock space is described in the occupation-number basis |α⟩: `Occ` is the type of finitely supported α : ℤ³ → ℕ and `Occ.num` is the particle number Σ_k α(k). A state is a function Ψ : `Occ` → ℂ; `IsNState` N Ψ says that Σ_α |Ψ(α)|² = 1 and that Ψ vanishes off {Σ α = N}, so Ψ is a normalized element of 𝓗_N. `a4` p q r s α is the action of a†_p a†_q a_r a_s on |α⟩ under [a_p, a†_q] = δ_{pq} (coefficient and resulting occupation). `kinTerm` and `intTerm` are the summands of ⟨Ψ, HΨ⟩ for the Hamiltonian (2.1) [ham], H = Σ_p p² a†_p a_p + |Λ|⁻¹ Σ_{p,q,u} V_u a†_p a†_q a_{p−u} a_{q+u}, indexed by α and by (p, q, u, α). `HasEnergy` L V Ψ E says that both series converge unconditionally and add up to E; `e0P` L V N is e₀^P, the infimum in `EReal` of E/N over finitely supported normalized N-particle states with energy E.

For the Dirichlet side, `Conf` N is (ℝ³)^N; `IsDirichletTrial` L N Ψ says that Ψ is smooth, compactly supported in the open box (0, L)^{3N}, symmetric under permutations of the particles and normalized; `energyD` V Ψ is ∫ Σ_i |∇_i Ψ|² + Σ_{i≠j} V(x_i − x_j)|Ψ|²; `e0D` L V N is e₀^D, the infimum of `energyD` V Ψ / N over this class.

```lean
/-- `Ψ` has energy `E = ⟨Ψ, H Ψ⟩` for (2.1) [ham] on the torus of side `L`: the kinetic and
the interaction series converge unconditionally and add up to `E`. -/
def HasEnergy (L : ℝ) (V : R3 → ℝ) (Ψ : Occ → ℂ) (E : ℝ) : Prop :=
  ∃ K : ℝ, ∃ I : ℂ, HasSum (kinTerm L Ψ) K ∧ HasSum (intTerm L V Ψ) I ∧ (E : ℂ) = K + I
```

```lean
/-- The ground state energy per particle `e₀^P(ρ, Λ)` for (2.1) [ham] on `Λ = [0,L]³` with
periodic boundary condition (§2), as the infimum of `⟨Ψ, HΨ⟩ / N` over finitely supported
normalized `Ψ ∈ 𝓗_N`. -/
def e0P (L : ℝ) (V : R3 → ℝ) (N : ℕ) : EReal :=
  ⨅ (Ψ : Occ →₀ ℂ) (E : ℝ) (_ : IsNState N Ψ ∧ HasEnergy L V Ψ E), ((E / N : ℝ) : EReal)
```

**The hypotheses.** `PotentialHyp` V collects the hypotheses of Theorem 2.1 on V, and `IsScatteringSolution` V w says that 1 − w is the zero-energy scattering solution of §2. `gfun` V w = V(1 − w) is g of (3.12) [gdef] and `g0` V w = ∫ V(1 − w) is g₀ = 4πa.

```lean
/-- Hypotheses of Theorem 2.1 [mainthm] on the potential (§2): smooth and of fast decay, read
as `V` being a Schwartz function; symmetric, read as even; nonnegative; not identically zero,
so that `g₀ > 0`; small enough that the Born series converges, in the sufficient form
`sup_x ∫ V(y) / (4π|x-y|) dy < 1`. -/
structure PotentialHyp (V : R3 → ℝ) : Prop where
  schwartz : ∃ S : SchwartzMap R3 ℝ, (S : R3 → ℝ) = V
  even : ∀ x, V (-x) = V x
  nonneg : ∀ x, 0 ≤ V x
  ne_zero : ∃ x, V x ≠ 0
  born : ∃ c < 1, ∀ x, ∫ y, V y / (4 * π * ‖x - y‖) ≤ c
```

```lean
/-- `1 - w` is the zero-energy scattering solution: `-Δ(1-w) + V(1-w) = 0`, `0 ≤ w < 1`,
`w(x) → 0` as `|x| → ∞` (§2). -/
structure IsScatteringSolution (V w : R3 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 w
  eqn : ∀ x, -(Laplacian.laplacian (fun y => 1 - w y) x) + V x * (1 - w x) = 0
  nonneg : ∀ x, 0 ≤ w x
  lt_one : ∀ x, w x < 1
  tendsto_zero : Tendsto w (cocompact R3) (𝓝 0)
```

**The limits.** `ratio` g ρ e is (e − gρ)/(g^{5/2}ρ^{3/2}) in `EReal`, `cLHY` is 16/(15π²), and `thermo` ρ is the filter on pairs (N, L) ∈ ℕ × ℝ of the thermodynamic limit L → ∞, N/L³ → ρ. The small boxes of Sections 2 and 3 are indexed by N: `rhoN` N = N^{−8/17} is ρ_N, `LN` N = ρ_N^{−25/24} = N^{25/51} is L_N, so that ρ_N L_N³ = N; `LtN` N = L_N(1 + 2ρ_N^{25/48}) and `rhotN` N = N/L̃_N³ are L̃ and ρ̃ of Lemma 2.2 [lemma1].

```lean
/-- The ratio `(e - g₀ρ) / (g₀^{5/2} ρ^{3/2})` of Theorem 2.1 [mainthm], in `[-∞, ∞]`. -/
def ratio (g : ℝ) (ρ : ℝ) (e : EReal) : EReal :=
  (e - ((g * ρ : ℝ) : EReal)) * (((g ^ (5/2 : ℝ) * ρ ^ (3/2 : ℝ))⁻¹ : ℝ) : EReal)
```

```lean
/-- The constant `16/(15π²)` of Theorem 2.1 [mainthm]. -/
def cLHY : ℝ := 16 / (15 * π ^ 2)
```

```lean
/-- The filter `L → ∞, N/L³ → ρ` on pairs `(N, L)` (§2). -/
def thermo (ρ : ℝ) : Filter (ℕ × ℝ) :=
  comap (fun x : ℕ × ℝ => x.2) atTop ⊓ comap (fun x : ℕ × ℝ => (x.1 : ℝ) / x.2 ^ 3) (𝓝 ρ)
```

### The main theorem

File `LHYUpper/Statements.lean` (the statement) and `LHYUpper/Thermo/Duplication.lean` (the proof).

```lean
/-- Statement of Theorem 2.1 [mainthm]: the upper limit, first over `L → ∞` with
`N/L³ → ρ` and then over `ρ → 0`, of the ratio for `e₀^P` is at most `16/(15π²)`. -/
def MainTheorem (V w : R3 → ℝ) : Prop :=
  limsup (fun ρ : ℝ => limsup (fun x : ℕ × ℝ => ratio (g0 V w) ρ (e0P x.2 V x.1))
    (thermo ρ)) (𝓝[>] 0) ≤ (cLHY : EReal)
```

```lean
/-- Theorem 2.1 [mainthm]: under the hypotheses on `V` (§2), with `1 - w` the zero-energy
scattering solution, the upper bound (2.2) holds. -/
theorem mainTheorem {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.MainTheorem V w :=
```

For every potential V satisfying the hypotheses of the paper and the zero-energy scattering solution 1 − w, the upper limit as ρ → 0⁺ of the upper limit as L → ∞ with N/L³ → ρ of (e₀^P(ρ, Λ) − g₀ρ)/(g₀^{5/2}ρ^{3/2}) is at most 16/(15π²). This is (2.2), the display of Theorem 2.1 [mainthm], with g₀ = 4πa = ∫ V(1 − w), the outer limit over ρ → 0⁺ (`𝓝[>] 0`), the inner one over the filter `thermo` ρ, and the ratio taken with the limiting density ρ, as in the paper.

### The chain

The proof goes through the results of the paper in the order of §2: Theorem 3.1 [lemma2.1] ⇒ Theorem 2.2 [lemma2] ⇒ (with the variational principle) the hypothesis of Lemma 2.2 [lemma1] ⇒ Lemma 2.1 [thm1] ⇒ (duplication) Theorem 2.1. Each step is a `Prop`-valued definition with the prefix Stmt in `LHYUpper/Statements.lean`, together with the theorem that proves it. Each of these theorems has the hypotheses `PotentialHyp` V and, where w occurs, `IsScatteringSolution` V w, and no other.

**Theorem 3.1 [lemma2.1]** (`LHYUpper/Assembly/Final.lean`).

```lean
/-- Statement of Theorem 3.1 [lemma2.1]: the trial state (3.18) [deffal] on the torus of side
`L = ρ^{-25/24}`, `ρ = ρ_N`, is normalized and has finite energy for every `k_c` and all
large `N`, and `limsup_{k_c → ∞} limsup_{ρ → 0}` of the ratio is at most `16/(15π²)`. -/
def Theorem3_1 (V w : R3 → ℝ) : Prop :=
  ∃ E : ℝ → ℕ → ℝ,
    (∀ kc : ℝ, ∀ᶠ N in atTop, IsNState N (trialState V w kc N) ∧
      HasEnergy (LN N) V (trialState V w kc N) (E kc N)) ∧
    limsup (fun kc : ℝ => limsup (fun N : ℕ =>
      ratio (g0 V w) (rhoN N) ((E kc N / N : ℝ) : EReal)) atTop) atTop ≤ (cLHY : EReal)
```

```lean
/-- Theorem 3.1 [lemma2.1]. -/
theorem Theorem3_1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Theorem3_1 V w :=
```

There is an energy E(k_c, N) such that for every cutoff k_c and all large N the trial state `trialState` V w k_c N, which is Ψ of (3.18) [deffal] at ρ = ρ_N, L = L_N, is a normalized N-particle state with energy E(k_c, N), and the upper limit over k_c → ∞ of the upper limit over N → ∞ of the ratio of E(k_c, N)/N is at most 16/(15π²). The producer is assembled by `Theorem31.theorem3_1_of_lemmas` from Lemma 4.1 [lemkinetic], Lemma 4.2 [lemHS1], Lemma 4.3 [lemHS2], Lemma 4.4 [lemHS3], Lemma 4.5 [lemHAS1] and Lemma 4.6 [lemHAS2] (`lemma4_1`, `Lemma4_2`, `Lemma4_3`, `Lemma4_4`, `lemma4_5`, `Lemma4_6`), the two identities at the end of §4 (`Final_I1`, `Final_I2`) and the normalization of (3.18) (`Normalization_eventually`).

**Theorem 2.2 [lemma2]** (`LHYUpper/Assembly/Final.lean`).

```lean
/-- Statement of Theorem 2.2 [lemma2]: a periodic trial state of `N` particles on
`[0, L_N]³` for each `N`, with upper limit of the ratio at most `16/(15π²)`. -/
def Theorem2_2 (V w : R3 → ℝ) : Prop :=
  ∃ Ψ : ℕ → Occ → ℂ, ∃ E : ℕ → ℝ,
    (∀ᶠ N in atTop, IsNState N (Ψ N) ∧ HasEnergy (LN N) V (Ψ N) (E N)) ∧
    limsup (fun N : ℕ => ratio (g0 V w) (rhoN N) ((E N / N : ℝ) : EReal)) atTop
      ≤ (cLHY : EReal)
```

```lean
/-- Theorem 2.2 [lemma2]. -/
theorem Theorem2_2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Theorem2_2 V w :=
```

There is, for every large N, a normalized N-particle state on the torus [0, L_N]³ with energy E_N such that the upper limit of the ratio of E_N/N at density ρ_N is at most 16/(15π²). It follows from Theorem 3.1 by a diagonal choice k_c(N) (`Theorem31.theorem2_2_of_theorem3_1`).

**Lemma 2.2 [lemma1]** (`LHYUpper/Position/Lemma22.lean`).

```lean
/-- Statement of Lemma 2.2 [lemma1]: the periodic bound on `[0, L_N]³` gives the Dirichlet
bound on `[0, L̃_N]³` at density `ρ̃_N`. -/
def Lemma2_2 (V w : R3 → ℝ) : Prop :=
  limsup (fun N : ℕ => ratio (g0 V w) (rhoN N) (e0P (LN N) V N)) atTop ≤ (cLHY : EReal) →
    limsup (fun N : ℕ => ratio (g0 V w) (rhotN N) (e0D (LtN N) V N)) atTop ≤ (cLHY : EReal)
```

```lean
/-- Lemma 2.2 [lemma1]. -/
theorem Lemma2_2 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma2_2 V w :=
```

If the upper limit of the ratio of e₀^P on [0, L_N]³ at density ρ_N is at most 16/(15π²), then so is the upper limit of the ratio of e₀^D on [0, L̃_N]³ at density ρ̃_N. The hypothesis is proved by `e0P_limsup_le` (`LHYUpper/Assembly/Final.lean`), from Theorem 2.2 and the variational principle (`Theorem31.limsup_ratio_e0P_le`).

**Lemma 2.1 [thm1]** (`LHYUpper/Position/Lemma21.lean`).

```lean
/-- Statement of Lemma 2.1 [thm1], for each `N`: a Dirichlet trial state of `N` particles on
`[0, L̃_N]³`, with upper limit of the ratio at density `ρ̃_N` at most `16/(15π²)`. -/
def Lemma2_1 (V w : R3 → ℝ) : Prop :=
  ∃ Ψ : (N : ℕ) → Conf N → ℂ,
    (∀ᶠ N in atTop, IsDirichletTrial (LtN N) N (Ψ N)) ∧
    limsup (fun N : ℕ => ratio (g0 V w) (rhotN N) ((energyD V (Ψ N) / N : ℝ) : EReal))
      atTop ≤ (cLHY : EReal)
```

```lean
/-- Lemma 2.1 [thm1], for each `N`: a Dirichlet trial state on `[0, L̃_N]³` at density `ρ̃_N`. -/
theorem Lemma2_1 {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.Lemma2_1 V w :=
```

For every large N there is a Dirichlet trial state of N particles on [0, L̃_N]³ whose energy per particle has ratio at density ρ̃_N with upper limit at most 16/(15π²). It is obtained from Lemma 2.2 and its hypothesis by taking, for each N, a trial state within ρ̃_N² of e₀^D (`exists_lt_e0D`). The paper's own form of the lemma is also proved:

```lean
/-- Lemma 2.1 [thm1] in the paper's form: for `ρ` small enough there are a box side
`L(ρ)` with `L(ρ) ρ^{25/24} → 1` and a Dirichlet trial state of `N(ρ) = ρ L(ρ)³` particles on
`[0, L(ρ)]³` whose ratio has upper limit at most `16/(15π²)` as `ρ → 0`. -/
theorem Lemma2_1_paper {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∃ Nρ : ℝ → ℕ, ∃ Lρ : ℝ → ℝ, ∃ Ψ : (ρ : ℝ) → Conf (Nρ ρ) → ℂ,
      (∀ ρ ∈ Set.Ioo 0 ρ₀, 0 < Lρ ρ ∧ (Nρ ρ : ℝ) = ρ * Lρ ρ ^ 3 ∧
        IsDirichletTrial (Lρ ρ) (Nρ ρ) (Ψ ρ)) ∧
      Tendsto (fun ρ => Lρ ρ * ρ ^ (25 / 24 : ℝ)) (𝓝[>] 0) (𝓝 1) ∧
      limsup (fun ρ => ratio (g0 V w) ρ ((energyD V (Ψ ρ) / Nρ ρ : ℝ) : EReal)) (𝓝[>] 0)
        ≤ (cLHY : EReal) :=
```

There are ρ₀ > 0, a particle number N(ρ), a box side L(ρ) and, for every ρ ∈ (0, ρ₀), a Dirichlet trial state of N(ρ) = ρL(ρ)³ particles on [0, L(ρ)]³, such that L(ρ)ρ^{25/24} → 1 and the upper limit of the ratio as ρ → 0⁺ is at most 16/(15π²).

**The duplication step after Lemma 2.1** (`LHYUpper/Thermo/Duplication.lean`).

```lean
/-- Statement of the duplication step after Lemma 2.1 [thm1] (§2.1): the Dirichlet small-box
bound gives Theorem 2.1 [mainthm]. -/
def DuplicationStep (V w : R3 → ℝ) : Prop := Lemma2_1 V w → MainTheorem V w
```

```lean
/-- The duplication step after Lemma 2.1 [thm1] (§2.1), under the hypotheses of
Theorem 2.1 [mainthm]: Lemma 2.1 [thm1] implies Theorem 2.1 [mainthm]. -/
theorem duplicationStep {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.DuplicationStep V w :=
```

Lemma 2.1 in the N-family form implies Theorem 2.1. This is the sentence of §2.1 "we can duplicate it so that a trial state can be constructed for cubes with linear dimension ≫ ρ^{−25/24}"; the hypotheses on V are used for g₀ > 0 and for the decay of V (see §3 (d)).

**The variational principle** (`LHYUpper/Fock/Variational.lean`).

```lean
/-- Variational principle for `e₀^P`: every normalized `N`-particle state with finite energy
bounds `e₀^P` from above. -/
def VariationalPrinciple (V : R3 → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∀ (N : ℕ) (Ψ : Occ → ℂ) (E : ℝ), IsNState N Ψ → HasEnergy L V Ψ E →
    e0P L V N ≤ ((E / N : ℝ) : EReal)
```

```lean
theorem variational_principle (V : R3 → ℝ) (hV : PotentialHyp V) :
    Stmt.VariationalPrinciple V :=
```

Every normalized N-particle state with energy E, not necessarily finitely supported, gives e₀^P ≤ E/N. The trial state (3.18) is supported on the infinite set M of Definition 3.4 [M], so this is the step that turns Theorem 2.2 into a bound on `e0P`. It is proved by truncation (`Variational.exists_finsupp_tendsto`).

**Nonnegativity of the Hamiltonian** (`LHYUpper/Position/Energy.lean`).

```lean
/-- The Hamiltonian (2.1) [ham] is nonnegative on finitely supported states. -/
def HamiltonianNonneg (V : R3 → ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∀ (Ψ : Occ →₀ ℂ) (E : ℝ), HasEnergy L V Ψ E → 0 ≤ E
```

```lean
/-- The Hamiltonian (2.1) [ham] is nonnegative on finitely supported states. -/
theorem hamiltonianNonneg {V : R3 → ℝ} (hV : PotentialHyp V) : Stmt.HamiltonianNonneg V :=
```

Every finitely supported state with an energy E has E ≥ 0. The proof writes the energy in position space, ∫ Σ_i |∇_i Φ|² + Σ_{i≠j} V^P(x_i − x_j)|Φ|² over the torus (`stateFn_kin_hasSum`, `stateFn_pot_hasSum`), where both terms are nonnegative because V ≥ 0.

**The scattering solution** (`LHYUpper/Scattering/Solution.lean`).

```lean
/-- Existence and uniqueness of the zero-energy scattering solution (§2). -/
def ScatteringSolutionExistsUnique (V : R3 → ℝ) : Prop :=
  ∃ w, IsScatteringSolution V w ∧ ∀ w', IsScatteringSolution V w' → w' = w
```

```lean
/-- Existence and uniqueness of the zero-energy scattering solution of §2 under the hypotheses of
Theorem 2.1 [mainthm]. -/
theorem scattering_exists_unique (V : R3 → ℝ) (hV : PotentialHyp V) :
    Stmt.ScatteringSolutionExistsUnique V :=
```

For every V satisfying `PotentialHyp` there is exactly one w satisfying `IsScatteringSolution` V w. So the hypothesis `IsScatteringSolution` V w of `mainTheorem` only names the solution that the paper calls 1 − w.

## 2. Index of the paper's results

Every public theorem whose docstring begins with `Lemma n.m`, `Theorem n.m`, `Proposition n.m`, `Corollary n.m` or a displayed-equation number (n.m), sorted by paper number (the first column is the beginning of the docstring). The table is generated from the source. Several Lean statements may belong to one item: a rate form and a limit form (§3 (c)), or the parts of an item. The duplication step and the variational principle are not numbered in the paper and are not in the table; they are in §1. Lemma 5.1 [f], Lemma 5.2 [lem-l], Lemma 5.4 [lem1], Lemma 5.5, Lemma 6.1 [boundspsiu], Lemma 7.2 [symno20], Lemma 7.4 [u-uv-vPsi] and Proposition 5.4 [particlebound] appear through their displayed equations, Lemma 8.2 [FalFbe0] through (8.10) [fab=no] and (8.11) [relationalbe].

| Paper item | Lean name | File |
|---|---|---|
| Theorem 2.1 [mainthm] | `mainTheorem` | `LHYUpper/Thermo/Duplication.lean` |
| Lemma 2.1 [thm1] | `Lemma2_1` | `LHYUpper/Position/Lemma21.lean` |
| Lemma 2.1 [thm1] | `Lemma2_1_paper` | `LHYUpper/Position/Lemma21.lean` |
| Theorem 2.2 [lemma2] | `Theorem2_2` | `LHYUpper/Assembly/Final.lean` |
| Theorem 2.2 [lemma2] | `Theorem31.limsup_ratio_e0P_le` | `LHYUpper/Assembly/Theorem31.lean` |
| Lemma 2.2 [lemma1] | `Lemma2_2` | `LHYUpper/Position/Lemma22.lean` |
| Theorem 3.1 [lemma2.1] | `Theorem31.theorem2_2_of_theorem3_1` | `LHYUpper/Assembly/Theorem31.lean` |
| Theorem 3.1 [lemma2.1] | `Theorem3_1` | `LHYUpper/Assembly/Final.lean` |
| (3.4) [number] | `a4_diag_fst` | `LHYUpper/Fock/A4.lean` |
| (3.11) [av] | `scat_av` | `LHYUpper/Scattering/WMomentum.lean` |
| (3.13) [gp] | `scat_gp` | `LHYUpper/Scattering/WMomentum.lean` |
| Lemma 4.1 [lemkinetic] | `Kinetic_rate` | `LHYUpper/Kinetic/Lemma41.lean` |
| Lemma 4.1 [lemkinetic] | `lemma4_1` | `LHYUpper/Kinetic/Lemma41.lean` |
| Lemma 4.2 [lemHS1] | `Lemma4_2` | `LHYUpper/Pair/S1S2.lean` |
| Lemma 4.3 [lemHS2] | `Lemma4_3` | `LHYUpper/Pair/S1S2.lean` |
| Lemma 4.4 [lemHS3] | `Lemma4_4` | `LHYUpper/Pair/S3.lean` |
| Lemma 4.5 [lemHAS1] | `OneLeg_rate` | `LHYUpper/OneLeg/Lemma45.lean` |
| Lemma 4.5 [lemHAS1] | `lemma4_5` | `LHYUpper/OneLeg/Lemma45.lean` |
| Lemma 4.6 [lemHAS2] | `Lemma4_6` | `LHYUpper/FourLegs/HardAssembly.lean` |
| Lemma 4.6 [lemHAS2] | `Lemma4_6_of_Lemma11_1` | `LHYUpper/FourLegs/Assembly.lean` |
| (4.6) | `OneLeg_hasSum_A1` | `LHYUpper/OneLeg/Forms.lean` |
| Theorem 5.1 [thmA] | `Thm5_1` | `LHYUpper/Particles/Lower.lean` |
| Theorem 5.1 [thmA] | `Thm5_1_lim` | `LHYUpper/Particles/PaperForms.lean` |
| Proposition 5.1 [prop5] | `Prop5_1` | `LHYUpper/Particles/Ratios.lean` |
| Proposition 5.2 [prop1] | `Prop5_2` | `LHYUpper/TrialState/Reorder.lean` |
| Proposition 5.3 [prop2] | `Prop5_3` | `LHYUpper/TrialState/Reorder.lean` |
| Lemma 5.3 [boundspsi0] | `Lemma5_3` | `LHYUpper/Particles/Lower.lean` |
| Lemma 5.3 [boundspsi0] | `Lemma5_3_paper` | `LHYUpper/Particles/PaperForms.lean` |
| (5.4) [properf1] | `Lemma5_1_properf1` | `LHYUpper/TrialState/FIdentities.lean` |
| Proposition 5.5 [prop6] | `Prop5_5` | `LHYUpper/Particles/Prop55.lean` |
| (5.5) [properf2] | `Lemma5_1_properf2` | `LHYUpper/TrialState/FIdentities.lean` |
| Lemma 5.6 [boundspsi02] | `Lemma5_6` | `LHYUpper/Particles/Lemma55.lean` |
| Lemma 5.6 [boundspsi02] | `Lemma5_6_paper` | `LHYUpper/Particles/PaperForms.lean` |
| (5.6) [properf3] | `Lemma5_1_properf3` | `LHYUpper/TrialState/FIdentities.lean` |
| (5.7) [properf4] | `Lemma5_1_properf4` | `LHYUpper/TrialState/FIdentities.lean` |
| (5.8) [properf5] | `Lemma5_1_properf5` | `LHYUpper/TrialState/FIdentities.lean` |
| (5.8) [properf5] | `Lemma5_1_properf5_mul` | `LHYUpper/TrialState/FIdentities.lean` |
| (5.9) [ublambda] | `scat_lam_abs_le` | `LHYUpper/Scattering/Lambda.lean` |
| (5.9) [ublambda] | `scat_rho_lam_le` | `LHYUpper/Scattering/Lambda.lean` |
| (5.10) [lublambdaPL0] | `scat_lam_PL_le` | `LHYUpper/Scattering/Lambda.lean` |
| (5.11) [ublambdaPH0] | `scat_lam_PH` | `LHYUpper/Scattering/Lambda.lean` |
| (5.13) [ubpsiuroughPM] | `Lemma5_4_PI` | `LHYUpper/Particles/UpperIH.lean` |
| (5.14) [ubpsiuroughPL] | `Lemma5_4_PL` | `LHYUpper/Particles/UpperL.lean` |
| (5.15) [ubpsiuroughPH] | `Lemma5_4_PH` | `LHYUpper/Particles/UpperIH.lean` |
| (5.19)–(5.21) | `Particles_softCreation` | `LHYUpper/Particles/Ratios.lean` |
| (5.22) [ubpsiuroughPL1] | `Eq5_22` | `LHYUpper/Particles/UpperL.lean` |
| (5.22) [ubpsiuroughPL1] | `Eq5_22_weighted` | `LHYUpper/Particles/UpperL.lean` |
| (5.23) [boundMa] | `Eq5_23` | `LHYUpper/Particles/UpperL.lean` |
| (5.24) [boundMaMa] | `Eq5_24` | `LHYUpper/Particles/UpperL.lean` |
| (5.26) [pubrho3] | `Eq5_26` | `LHYUpper/Particles/Ratios.lean` |
| (5.27) [4.1] | `Eq5_27` | `LHYUpper/Particles/Ratios.lean` |
| (5.27) [4.1] | `Eq5_27_sum` | `LHYUpper/Particles/Ratios.lean` |
| (5.28) [temp6.29] | `Eq5_28` | `LHYUpper/Particles/UpperIH.lean` |
| (5.29) [temp4.17] | `Prop5_4_PI` | `LHYUpper/Particles/Totals.lean` |
| (5.30) [4.18] | `Prop5_4_PH` | `LHYUpper/Particles/Totals.lean` |
| (5.30) [4.18] | `Prop5_4_PH_paper` | `LHYUpper/Particles/Totals.lean` |
| (5.31) [4.19] | `Prop5_4_PL` | `LHYUpper/Particles/Totals.lean` |
| (5.32) [resultlbpsi0] | `Eq5_32` | `LHYUpper/Particles/Totals.lean` |
| (5.35)–(5.36) [3.1, sum] | `sum_PL_occ` | `LHYUpper/Riemann/ScaledLimits.lean` |
| (5.40) [temp5.19] | `Eq5_40` | `LHYUpper/Particles/UpperIH.lean` |
| (5.41) [boundpsiuvmn] | `Eq5_41` | `LHYUpper/Particles/UpperIH.lean` |
| (5.42) [boundpsifixeduv] | `Eq5_42` | `LHYUpper/Particles/UpperIH.lean` |
| (5.43) [upt01] | `Eq5_43` | `LHYUpper/Particles/Lower.lean` |
| (5.45) [mcmlbum0] | `Eq5_45` | `LHYUpper/Particles/Prop55.lean` |
| (5.46) [mcmlbum1] | `Eq5_46` | `LHYUpper/Particles/Prop55.lean` |
| (5.48)–(5.49) | `Particles_iterate` | `LHYUpper/Particles/Lower.lean` |
| (5.56) [ubpsiuPL] | `Eq5_56` | `LHYUpper/Particles/Lower.lean` |
| (5.57) [ubpsiuPLmc] | `Eq5_57` | `LHYUpper/Particles/Lemma55.lean` |
| (5.58) [lbpsiuPL0] | `Eq5_58` | `LHYUpper/Particles/Lemma55.lean` |
| (5.64) [temp6.58] | `Eq6_1` | `LHYUpper/Particles/Lemma55.lean` |
| (6.2) [boundspsiu2PMtotal] | `Eq6_2` | `LHYUpper/Kinetic/LowMid.lean` |
| (6.2) [boundspsiu2PMtotal] | `Eq6_2_paper` | `LHYUpper/Kinetic/LowMid.lean` |
| (6.3) [boundspsiu2PLtotal] | `Eq6_3` | `LHYUpper/Kinetic/LowMid.lean` |
| (6.3) [boundspsiu2PLtotal] | `Eq6_3_paper` | `LHYUpper/Kinetic/LowMid.lean` |
| (6.3) [boundspsiu2PLtotal] | `sum_PL_kin` | `LHYUpper/Riemann/ScaledLimits.lean` |
| (6.4) [boundspsiu2PHtotal] | `Eq6_4` | `LHYUpper/Kinetic/Lemma41.lean` |
| (6.7) | `Eq6_7` | `LHYUpper/Kinetic/LowMid.lean` |
| (6.11) [temp7.16] | `Eq6_11` | `LHYUpper/Kinetic/Lemma41.lean` |
| (6.16) [temp7.20] | `Eq6_16` | `LHYUpper/Kinetic/Lemma41.lean` |
| Lemma 7.1 [id4a] | `Lemma7_1` | `LHYUpper/Pair/Identities.lean` |
| (7.1)–(7.2) | `Eq7_2` | `LHYUpper/Pair/Identities.lean` |
| Lemma 7.3 [id4a2] | `Lemma7_3` | `LHYUpper/Pair/Id4a2.lean` |
| Lemma 7.3 [id4a2] | `Lemma7_3_PH` | `LHYUpper/Pair/Id4a2.lean` |
| (7.7) [u-uPMH] | `Eq7_7` | `LHYUpper/Pair/S1S2.lean` |
| (7.7) [u-uPMH] | `Pair_S2_total` | `LHYUpper/Pair/S1S2.lean` |
| (7.8) [u-uPL] | `Eq7_8` | `LHYUpper/Pair/S1S2.lean` |
| (7.9) [prle81] | `Eq7_10` | `LHYUpper/Pair/S2Exact.lean` |
| (7.11) [temp8.16] | `Eq7_12` | `LHYUpper/Pair/S2Exact.lean` |
| (7.13)–(7.15) [temp8.23] | `Eq7_15` | `LHYUpper/Pair/S2Exact.lean` |
| (7.16) [temp8.24] | `Eq7_17` | `LHYUpper/Pair/S2Exact.lean` |
| (7.23)–(7.24) | `Pair_sum_PL_pot` | `LHYUpper/Pair/Sums.lean` |
| (7.44) [u-uv-vPMH] | `Eq7_44` | `LHYUpper/Pair/UUVV.lean` |
| (7.45) [u-uv-vPLMH] | `Eq7_45` | `LHYUpper/Pair/UUVV.lean` |
| (7.45) [u-uv-vPLMH] | `Eq7_45_paper` | `LHYUpper/Pair/UUVV.lean` |
| (7.46) [u-uv-vPL] | `Eq7_46` | `LHYUpper/Pair/UUVV.lean` |
| (7.46) [u-uv-vPL] | `Eq7_46_paper` | `LHYUpper/Pair/UUVV.lean` |
| (7.57) [8.2] | `Eq7_57` | `LHYUpper/Pair/UUVV.lean` |
| (7.62)–(7.63) [longexpression1] | `Eq7_62` | `LHYUpper/Pair/S3Bound.lean` |
| (7.65) [temp8.73] | `Eq7_65` | `LHYUpper/Pair/S3.lean` |
| (7.66)–(7.68) | `Eq7_67` | `LHYUpper/Pair/S3.lean` |
| (7.67) [temp8.75] | `Pair_sum_Vshift_P` | `LHYUpper/Pair/Sums.lean` |
| Lemma 8.1 [posscombone0] | `Lemma8_1` | `LHYUpper/TrialState/Legs.lean` |
| Lemma 8.1 [posscombone0] | `OneLeg_split` | `LHYUpper/OneLeg/Forms.lean` |
| Lemma 8.3 | `Lemma8_3_paper` | `LHYUpper/OneLeg/Lemma45.lean` |
| (8.10) [fab=no] | `Lemma8_2_F` | `LHYUpper/TrialState/Legs.lean` |
| (8.11) [relationalbe] | `Lemma8_2_paper` | `LHYUpper/OneLeg/Ratio.lean` |
| (8.11) [relationalbe] | `Lemma8_2_ratio` | `LHYUpper/TrialState/FRatio.lean` |
| (8.12) [fal0] | `Eq8_12` | `LHYUpper/OneLeg/Ratio.lean` |
| (8.13) [fbe0] | `Eq8_13` | `LHYUpper/OneLeg/Ratio.lean` |
| (8.14) [0resultfirstcase] | `Lemma8_3_first` | `LHYUpper/OneLeg/Sums.lean` |
| (8.15) [0resultsecondcase] | `Lemma8_3_second` | `LHYUpper/OneLeg/Sums.lean` |
| (8.16) [0resultthirdcase] | `Lemma8_3_third` | `LHYUpper/OneLeg/Sums.lean` |
| (8.17)–(8.26) | `OneLeg_pair_first` | `LHYUpper/OneLeg/FirstPair.lean` |
| (8.25) | `OneLeg_lam_sub` | `LHYUpper/OneLeg/FirstPair.lean` |
| (8.28)–(8.29) [sum0PL] | `Eq8_29` | `LHYUpper/OneLeg/Sums.lean` |
| (8.30)–(8.31) | `Eq8_31` | `LHYUpper/OneLeg/Ratio.lean` |
| (8.33)–(8.34) | `Eq8_34` | `LHYUpper/OneLeg/Ratio.lean` |
| Proposition 9.1 | `Prop9_1` | `LHYUpper/FourLegs/Section9.lean` |
| Proposition 9.1 | `Prop9_1_paper` | `LHYUpper/FourLegs/Section9.lean` |
| Lemma 9.1 [fourlegslemma1] | `Lemma9_1` | `LHYUpper/TrialState/Legs.lean` |
| Lemma 9.1 [fourlegslemma1] | `Lemma9_1_ratio_rho` | `LHYUpper/FourLegs/Classes.lean` |
| Lemma 9.2 | `Lemma9_2` | `LHYUpper/FourLegs/Section9.lean` |
| Lemma 9.2 | `Lemma9_2_case1` | `LHYUpper/FourLegs/Section9.lean` |
| Lemma 9.2 | `Lemma9_2_case2` | `LHYUpper/FourLegs/Section9.lean` |
| Lemma 9.2 | `Lemma9_2_case3` | `LHYUpper/FourLegs/Section9.lean` |
| Lemma 10.1 | `Lemma10_1` | `LHYUpper/FourLegs/HighLegs.lean` |
| Lemma 10.2 [101] | `Lemma10_2` | `LHYUpper/FourLegs/MainTerm.lean` |
| Lemma 10.2 [101] | `Lemma10_2_rate` | `LHYUpper/FourLegs/MainTerm.lean` |
| (10.9) [11.1] | `Eq10_9` | `LHYUpper/TrialState/Legs.lean` |
| (10.11) [temp8.140] | `Eq10_11` | `LHYUpper/FourLegs/HighLegs.lean` |
| (10.20) [temp8.150] | `Eq10_20` | `LHYUpper/FourLegs/MainTerm.lean` |
| Proposition 11.1 [propchi] | `Prop11_1` | `LHYUpper/TrialState/Chi.lean` |
| Lemma 11.1 [113] | `Lemma11_1` | `LHYUpper/FourLegs/HardAssembly.lean` |
| Lemma 11.1 [113] | `Lemma11_1_of_Lemma11_2` | `LHYUpper/FourLegs/HighLegs.lean` |
| Lemma 11.2 [thehardestlemma] | `HardJoint_rep` | `LHYUpper/FourLegs/HardJoint.lean` |
| Lemma 11.2 [thehardestlemma] | `Lemma11_2` | `LHYUpper/FourLegs/HardAssembly.lean` |
| Lemma 11.2 [thehardestlemma] | `Lemma11_2_rate` | `LHYUpper/FourLegs/HardAssembly.lean` |
| Lemma 11.3 [lem11.1] | `HardGraph_count` | `LHYUpper/FourLegs/HardGraph.lean` |
| Lemma 11.3 [lem11.1] | `HardJoint_count` | `LHYUpper/FourLegs/HardJoint.lean` |
| Lemma 11.3 [lem11.1] | `Lemma11_3_paper` | `LHYUpper/FourLegs/HardJoint.lean` |
| (11.13) | `HardRep_weight` | `LHYUpper/FourLegs/HardRep.lean` |
| (12.5)–(12.7) | `exists_dirichlet_of_periodic` | `LHYUpper/Position/Lemma22.lean` |
| (12.7) | `e0D_le_e0P` | `LHYUpper/Position/Lemma22.lean` |

## 3. Differences from the printed statements

### (a) Model and endpoint

1. **Momentum space and e₀^P.** Paper: E₀^P(ρ, Λ) = inf spec H on 𝓗_N and e₀^P = E₀^P/N. Lean: `e0P` is the infimum of ⟨Ψ, HΨ⟩/N over finitely supported normalized N-particle states in the occupation-number basis, with values in `EReal`; ⟨Ψ, HΨ⟩ is the sum of the two unconditionally convergent series of `HasEnergy`. Why: these states lie in the form domain of H, so `e0P` ≥ inf spec H/N, and an upper bound for `e0P` implies the same upper bound for the paper's e₀^P; the bound proved is therefore at least as strong as the paper's. The equality of the two is not proved (§7). Likewise `e0D` is an infimum over smooth compactly supported symmetric functions. `variational_principle` extends the bound to normalized states of infinite support with finite energy, such as (3.18).
2. **The interaction and the factor in (2.1).** Paper: (2.1) [ham] with V_u the Fourier transform of V on ℝ³ and the sum over p, q, u ∈ Λ*. Lean: `intTerm` uses `ft` V at the lattice momenta, which is (2.1) as printed. In position space this is the interaction Σ_{i≠j} V^P(x_i − x_j) with the periodization V^P(x) = Σ_{n∈ℤ³} V(x + nL) (`periodize`; its Fourier coefficients on [0, L]³ are the V_u, `periodize_fourier`; `torusEnergy`, `stateFn_norm_energy`). The sketch of §12 extends V by the nearest image, V^P(x − y) = V([x − y]_P); with that reading the inequality V(x − y) ≤ V^P(x − y) used there holds only for radially nonincreasing V, while for the lattice sum it holds for every V ≥ 0 (`localize_pot`). (2.1) has no factor 1/2 in front of the interaction, so each pair is counted twice, and `energyD` uses Σ_{i≠j} in the same way. This goes with the scattering equation −Δ(1 − w) + V(1 − w) = 0 and g₀ = ∫ V(1 − w) = 4πa, and then 4πaρ·(128/(15√π))(ρa³)^{1/2} = (16/(15π²))g₀^{5/2}ρ^{3/2}: `cLHY` is the Lee–Huang–Yang constant of (1.1) [nextorder] in the paper's normalization.
3. **The hypotheses on V.** Paper: V smooth, symmetric (V_u = V_{−u} = V̄_u), nonnegative, of fast decay, and small enough that the Born series converges. Lean: `PotentialHyp`.
   - *Schwartz* is the reading of "smooth with fast decay". It gives the Fourier analysis on ℝ³, the regularity and decay of w and g, and the decay of order 8 used in the duplication (`decayConst8_spec`).
   - *Even*, V(−x) = V(x), is the reading of "symmetric", stated in the paper as V_u = V_{−u} = V̄_u: for real V it is equivalent to real Fourier coefficients V_u = V_{−u}. It makes w, g and λ even (`scat_w_even`, `scat_g_even`).
   - *Nonnegative* is the paper's hypothesis; it is used for the uniqueness of w (maximum principle, `scat_solution_unique`), in §12 (`localize_pot`) and for E ≥ 0 (`hamiltonianNonneg`).
   - *Not identically zero* makes g₀ > 0 (`scat_g0_pos`). The ratio divides by g₀^{5/2}; for V = 0 one has g₀ = 0, and the statement would carry no information.
   - *The Born condition* sup_x ∫ V(y)/(4π|x − y|) dy < 1 is the standard sufficient condition for the convergence of the Born series: the operator f ↦ ∫ V(y) f(y)/(4π|x − y|) dy then has norm < 1 on bounded functions. It is used only to construct the scattering solution (`bornSol`).
4. **The scattering solution.** Paper: "let 1 − w be the zero energy scattering solution", with 0 ≤ w < 1 and w → 0. Lean: the hypothesis `IsScatteringSolution` V w, with the equation pointwise for a C² function w; `scattering_exists_unique` proves that it has exactly one solution for every V satisfying `PotentialHyp`.
5. **The small box and the limits.** Paper: L = ρ^{−25/24}, N = ρL³ and lim sup_{ρ→0} in Theorem 3.1, Theorem 2.2 and Lemma 2.2. N = ρL³ = ρ^{−17/8} is an integer only for ρ = N^{−8/17}, so the Lean statements run along ρ_N = N^{−8/17}, L_N = N^{25/51} (`rhoN`, `LN`) as N → ∞. All upper limits are taken in `EReal`, where they always exist. In Theorem 3.1 the cutoff k_c is a real parameter and the limit k_c → ∞ is the outer one, as in the paper; from Theorem 3.1 to Theorem 2.2 the library chooses k_c(N) diagonally (`Theorem31.theorem2_2_of_theorem3_1`).
6. **Lemma 2.1 [thm1].** Paper: for ρ small there are L ∼ ρ^{−25/24} and a Dirichlet trial state of N = ρL³ particles on [0, L]³ whose ratio has lim sup ≤ 16/(15π²) as ρ → 0. Lean: `Stmt.Lemma2_1` is the N-family on [0, L̃_N]³ at density ρ̃_N, the form used by the duplication; `Lemma2_1_paper` is the paper's form, with "L ∼ ρ^{−25/24}" read as L(ρ)ρ^{25/24} → 1, N(ρ) chosen from the strictly decreasing sequence ρ̃_N (`rhotN_strictAntiOn`) and L(ρ) = (N(ρ)/ρ)^{1/3}.
7. **The trial state (3.18) [deffal].** Paper: C_N is chosen so that Ψ is normalized, and ⟨H_N⟩_Ψ is used as a number. Lean: `Stmt.Theorem3_1` asserts in its conclusion that `trialState` is a normalized N-particle state with an energy (`IsNState`, `HasEnergy`) for every k_c and all large N; the normalization 0 < Σ_{α∈M} |f(α)|² < ∞ is proved (`Normalization_eventually`), and C_N is the positive square root.

### (b) Corrections of the paper

The final version of the paper in `paper/` corrects the arXiv version; the Lean statements are the corrected ones. None of these corrections changes Theorem 2.1, Theorem 2.2, Theorem 3.1, Lemma 2.1 or Lemma 2.2. Equation, theorem and section numbers are unchanged.

**Corrected intermediate statements.** The main ones:

- S1. **(4.5) and (4.6)–(4.7).** H_{S3} is summed over u ≠ v, so the terms v = −u, which are already in H_{S1}, are counted twice. The final version sums over u ≠ ±v; H_{A1} and H_{A2} carry the momentum conservation of (2.1). Names: `Lemma4_4`.
- S2. **Lemma 5.2 [lem-l].** "λ_k depends only on |k|" needs V radial, while the paper assumes V symmetric; the proofs only use evenness, λ_{−k} = λ_k. The bound |λ_k| ≤ g_k|k|⁻² must read |g_k| (g_k can be negative on P_H), and (5.10) holds for ρ small depending on g₀. Names: `scat_lam_PL_le`.
- S3. **Before (5.35) [3.1].** "For any continuous F, L^{−3} Σ_p F(p) → ∫ F(p) d³p/(2π)³" is false as stated (F ≡ 1). The final version states a quantitative Riemann-sum bound, (5.34′), with an error rate, for integrands with a singularity at the origin on regions that depend on L and ρ. Names: `riemann_shell`.
- S4. **(5.19)–(5.21) and Proposition 9.1.** A state of M_u^a comes from M_u^s by the soft pair creation 𝒜^{u,k} only when α(−u) = α(u) + 1; when α(u) = α(−u) + 1 it comes by 𝒜^{−u,k}. The sums run over both, which doubles a constant. Names: `Particles_softCreation`, `Prop9_1`.
- S5. **m_c = ρ^{−1/200} is not an integer.** Rule 3 of Definition 3.4 [M] can raise α*(u) to ⌈m_c⌉, so "at most m_c particles", Σ_{i=0}^{m_c} and the ranges in (5.48)–(5.54), (7.17) and Lemma 10.2 are read with ⌈m_c⌉; the bounds only use m ≤ m_c + 1 ≤ 2m_c.
- S6. **(5.41) [boundpsiuvmn] and (5.42) [boundpsifixeduv].** Under the printed condition u + v ≠ 0 both fail for u = v. The condition is u ≠ ±v, which holds at every use. Names: `Eq5_41`, `Eq5_42`.
- S7. **(5.48)–(5.56).** The range β(u) ≤ m_c − m contains states for which 𝒜^u cannot be applied m times inside M, and (β(0) − 2m)^{2m} must be its positive part. The sum is restricted accordingly; (5.56) changes only by the constant in front of ρ^{η/2}. Names: `Particles_iterate`, `Eq5_56`.
- S8. **Complex conjugates.** f can take imaginary values (soft pairs), so f(γ)² ≠ |f(γ)|². (7.25) [defPuv] and the proofs of (8.14) and Lemma 10.2 carry the conjugate of Lemma 7.1, and (8.14) [0resultfirstcase] is stated for the real part, the only part that enters through the C.C. of (4.6). Names: `Lemma7_1`, `Lemma8_3_first`.
- S9. **(7.12).** The left side lacks the factor |Λ|^{−2}, and the right side as printed does not give o(ρ^{5/2}|Λ|). The final version has the two-sided bound with V₀ρ Σ_u Q_Ψ(u) on the right, using ρ|λ_u| ≤ 1.
- S10. **Lemma 9.1 [fourlegslemma1].** "Exactly four cases" misses the adjoint of case 2 (v₁, v₂ ∈ P_{H,c}, v₃, v₄ ∈ P_L); there are explicit counterexamples. The final version lists it as case 2′, and Lemma 9.2 treats it by complex conjugation. The hypothesis "v₁ ≠ v₃ or v₄" means v₁ ≠ v₃ and v₁ ≠ v₄. Names: `Lemma9_1`, `Lemma9_2`.
- S11. **(11.19) [0.025] in Lemma 11.3 [lem11.1].** The count of nontrivial loops in (11.29) [alstvlm] counts the two chains as loops; the correct count gives t^{t/2+1} in place of t^{t/2}, and absorbing (Ck_c³)^{(s+t)/2+1} needs ρ small depending on k_c. The use in (11.18) is inside the limit in k_c and ρ and is not affected. Names: `HardJoint_count`, `Lemma11_3_paper`.
- S12. **Iterated limits.** The joint upper limits lim sup_{k_c,ρ} and lim sup_{m_c,ρ} in Lemmas 4.1–4.6, 7.2, 8.3, 9.2, 10.2 and 11.1 are not defined; they are iterated upper limits, k_c → ∞ outside and ρ → 0 inside (see (c)).

A few further statements get a condition or a range that their proofs already use (case (B) of Proposition 5.3 [prop2] with β(u) = m − 1; Proposition 5.5 [prop6] for u ∈ P_L; the sums of (5.38)–(5.39) over P_L).

**Steps of proofs.** The items below are places where the printed statement holds and a step of its proof fails, is missing, or is only sketched; the Lean proof does the step as described, and so does the final version of the paper. None of them changes the conclusion of Theorem 2.1 [mainthm], Theorem 2.2 [lemma2], Theorem 3.1 [lemma2.1], Lemma 2.1 or Lemma 2.2. Obvious misprints are corrected silently and are not listed.

1. **§12, proof of Lemma 2.2 [lemma1]: the periodic potential.** Step: V^P(x − y) = V([x − y]_P) (nearest image) and "V(x − y) ≤ V^P(x − y) since V is nonnegative and has fast decay". With the nearest image this needs V radially nonincreasing, and the folded potential has more than one image. Lean: V^P = Σ_n V(· + nL), which is the position form of (2.1); then V ≤ V^P for V ≥ 0. Names: `periodize`, `periodize_fourier`, `localize_pot`.
2. **Lemma 7.3 [id4a2], (7.28) [id4a21] and (7.31) [gammaualu].** Step: the proof assumes only u ≠ v; for u = −v the coefficient in (7.28) is not a matrix element and (7.31) does not hold. Lean: (7.26) [resultid4a2] and (7.27) [resultid4a2o] are proved without using u ≠ −v; the statements keep the hypotheses u ≠ v and u + v ≠ 0, which their proofs do not use. Names: `Lemma7_3`, `Lemma7_3_PH`.
3. **Proposition 5.4 [particlebound], proof of (5.29) [temp4.17].** Step: for u ∈ P_I one has λ_u = −w_u, and the summand is y²/(1 − y²) with y = ρw_u, not (h − 1)²/(4h); the pointwise inequality written there does not hold, and the comparison of limits gives no rate ρ^{3/2+η}. Lean: y²/(1 − y²) ≤ 2y² for y ≤ 1/2 and the lattice bound |Λ|⁻¹ Σ_{|u|>R} |u|⁻⁴ ≤ K/R give 2Kg₀²ρ^{3/2+η}. Names: `sum_PI_occ`, `Prop5_4_PI`.
4. **Proof of Lemma 10.2 [101], between (10.17) [temp8.147] and (10.20) [temp8.150].** Step: |λ_p − λ_q| ≤ ρ^{3/4} for p, q ∈ P_{H,c} with p + q ∈ P_L. Lean: |λ_p − λ_q| ≤ Cε_H^{−3}|p + q| ≤ Cρ^{1/2−4η}, using that λ is even; the error of (10.20) is then a smaller power of ρ, and Lemma 10.2 is unchanged. Names: `scat_lam_sub_le`, `Eq10_20`, `Lemma10_2`.
5. **Steps that the arXiv version does not write out:** the duplication after Lemma 2.1 [thm1], the passage from Theorem 3.1 to Theorem 2.2 (the choice of k_c), and the near-minimizers of e₀^D in Lemma 2.1. The final version of the paper writes them out (see (d)). Lean: written out as described in (d) below; the duplication needs V to decay faster than |x|^{−29/4}, and the library uses decay of order 8. Names: `duplicationStep`, `Theorem31.theorem2_2_of_theorem3_1`, `exists_lt_e0D`, `decayConst8`.
6. **(5.41) [boundpsiuvmn], "using similar method".** Step: following the proof of (5.28) [temp6.29] does not work: when Proposition 5.3 [prop2] (B) removes one particle at u, the partner momentum may be v itself (u and v soft-created from u + v ∈ P_L), and the event {α(v) = n} is not preserved. Lean: the recursion a_{m,n} ≤ b_u a_{m−1,n} + b_u b_v a_{m−1,n−1} with b_u = Aρ²|λ_u|ε_H^{−2}, which gives a_{m,n} ≤ (2b_u)^m b_v^n and then (5.41) and (5.42) [boundpsifixeduv]. Names: `Eq5_41`, `Eq5_42`.
7. **Proposition 11.1 [propchi], proof.** Step: "by definition of M" writes χ as (11.7) [temp8.164] without checking that α = ∏_j (𝒜_{u_j,−u_j})^{n_j}|N⟩ belongs to M (moving the strict P_L steps before the soft steps keeps rule 3), nor that the operators of (11.5) [elementform2] do not annihilate the state (α(0) ≥ 2s + t, α(v_i) ≥ 1). Lean: these invariants are part of the conclusion of `Prop11_1` (α symmetric, α = 0 on P_{H,c}, the v_i pairwise different up to sign, α(v_i) ≥ 1, enough particles at 0). Names: `Prop11_1`.
8. **Lemma 4.1 [lemkinetic], "follows immediately from summing (6.2)–(6.4)".** Step: after the sum one still has to turn ρ₀²|Λ|⁻¹ Σ_{P_L∪P_I∪P_H} u²w_u² and the ρ₀^{5/2} term on P_H into ‖∇w‖₂² and g₀^{3/2} (Parseval and Riemann sums, with rate ρ^η), and to use Q_Ψ(u) = 0 on the gap 0 < |u| < ε_Lρ^{1/2}. Lean: these steps are separate statements. Names: `Kinetic_hasSum_iff`, `Kinetic_split`, `Kinetic_parseval`, `Kinetic_sum_w2`, `Kinetic_sum_PH_w2`.
9. **(7.18), proof of Lemma 7.2 [symno20].** Step: the tail Σ_{u∈P_L} Σ_i |λ_u|ρ²Q_Ψ({u, i}) is bounded "using (5.45) [mcmlbum0]", but monotonicity only gives Q_Ψ({u, i}) ≤ 1/(i + 1) and a total of order ρ^{5/2}|Λ|. Lean: the bound (5.57) [ubpsiuPLmc], itself derived from (5.45), gives ρ^{η/2}x_u/(1 − x_u) for each u and a total o(ρ^{5/2}|Λ|). Names: `Eq7_17`, `Eq5_57`.
10. **Proof of (8.14) [0resultfirstcase] in Lemma 8.3, (8.19) [temp8.96], (8.22) and (8.25).** Step: A₁ = Σ √(α(0)α(v₁)) f(α)f(β) lacks the complex conjugate of f(α) (Lemma 7.1 [id4a]); (8.22) writes √λ_{v₂} √λ_{v₃} (square roots of Definition 3.6) as √(λ_{v₂}λ_{v₃}), which differ in sign when both are negative, and only the former gives the sign of (8.26). Lean: conj f(α), the product of the two square roots, and in place of (8.25) the bound |√x √y − x| ≤ 2|x − y|. Names: `OneLeg_csqrt_mul_sub`, `OneLeg_pair_first`, `Lemma8_3_first`.
11. **Lemma 9.2, proof of (9.9) [resultasymno22L2H1].** Step: "by the Schwarz inequality the first term on the right is o(ρ⁴)" is not derived: the bound gives N⁻¹ρ^{9/10}(1 + Q(v₃) + Q(v₄)) per tuple, and the sum over α with F(α) = 0, α(v₁), α(v₂) ≥ 1 is of order 1 near the inner edge of P_L. Lean: this term is bounded by 3ρ³, which suffices for the conclusion ≤ ρ^{11/4}. Names: `Lemma9_2_case2`, `Lemma9_2`.
12. **Lemma 10.1, (10.2) [4kspecialresult1].** Step: "Σ_{k₁} Q(k₁, k₃, k₄) ≤ NQ(k₃, k₄)" sums over k₁ for fixed k₃, k₄, but in (10.2) k₁ = k₂ = (k₃ + k₄)/2 is determined by them; the bound used tuple by tuple gives k_c⁶ρ^{−3/4} after normalization, which does not tend to 0. Lean: the Schwarz inequality |⟨a†_{k₁}a†_{k₁}a_{k₃}a_{k₄}⟩| ≤ (Σ_α α(k₁)(α(k₁) − 1)|Ψ(α)|²)^{1/2} Q(k₃, k₄)^{1/2} ≤ Cρ^{4−8η} by (5.40) [temp5.19] and (5.42), with two free momenta, gives Ck_c⁶ρ^{3/2−8η}; the same proof covers (10.3) [4kspecialresult2] and all other coincidences k_i = ±k_j. Names: `Lemma10_1`.
13. **Proof of Lemma 10.2 [101], (10.11) [temp8.140].** Step: f(β)f(γ) and ∏ √λ_{k_i} lack the complex conjugate of Lemma 7.1; when the λ_{k_i} have different signs, ∏ √λ_{k_i} differs from conj(√λ_{k₁}√λ_{k₂})√λ_{k₃}√λ_{k₄}. Lean: (10.11) with the conjugate, and |conj(√a √b) − a| ≤ 2|a − b| for (10.20). Names: `Eq10_11`, `Eq10_20`.
14. **Proof of Lemma 11.2 [thehardestlemma], (11.26) [uboundl].** Step: the bound l ≤ (s + t)/2 + 1 uses that the chain from k₃ to k₄ contains an edge of β (0 < m₁ < m₂), which is not proved. Lean: for β ∉ M(k₁, k₂), neither {k₁, k₂} is a pair of β nor {k₃, k₄} a pair of γ. Names: `HardJoint_graph`.
15. **Proof of Lemma 11.2 [thehardestlemma]: "α is the same for β and γ".** Step: not proved; the minimal α used from (11.10) [stst] on is not provided by the proof of Proposition 11.1. Lean: (i) the base α of Proposition 11.1 is determined by χ off P_{H,c}, and β = γ off P_{H,c}; (ii) the common pairs of the two operator sequences can be absorbed into α, which stays a base in M for the remaining factors; the minimality (11.10) is replaced by the condition "no common pair". Names: `HardRep_same`, `HardRep_split`, `HardJoint_rep`.
16. **(11.11) [stgeq2].** Step: the reason given for excluding t = 0 does not apply (the set M(k₁, k₂) requires a soft pair (k₁, k₂)). The right reason: if all edges are strict, the chain from k₁ ends at ±k₁, which contradicts (10.7) [conditionk2]. (11.11) itself holds. Names: `HardGraph_count`, `HardJoint_count` (no configuration for s + t ≤ 1).
17. **Proof of Lemma 11.1 [113], (11.31) [temp8.162].** Step: the tail β(k₁) > 3 is bounded by citing only (5.40) [temp5.19], but the bound carries the factor |λ_{k₁}λ_{k₂}|^{−1/2}, which has no uniform bound on P_{H,c}. Lean: (5.41) [boundpsiuvmn] with m = β(k₁) ≥ 4 and n = β(k₂) ≥ 1, whose factor |λ_{k₁}|^m|λ_{k₂}|^n absorbs |λ_{k₁}λ_{k₂}|^{−1/2}, together with (5.42) tuple by tuple. Names: `Lemma11_1_of_Lemma11_2`.
18. **Proof of Lemma 4.4 [lemHS3], (7.65) [temp8.73].** Step: "|w_uρ| ≤ const ρ|u|⁻² ≤ ε_L⁻², hence A₃ ≤ o(ρ^{5/2})" does not follow: this bound only gives |λ_u + w_u|ρ = O(1) and A₃ = O(ρ²). Lean: the additional estimate |Λ|⁻¹ Σ_{u∈P_L} |λ_u + w_u| ≤ Cρ^{1/2}, from the Riemann sums for λ_u and w_u on P_L. Names: `Eq7_65`, `sum_PL_pot`, `sum_PL_occ`.

### (c) Rate forms and paper forms

Many limits of §5–§10 are proved as explicit rate bounds, uniform in k_c and in the momenta, of the form "there are C and N₀ such that for all N ≥ N₀ …"; the paper's limit form, along ρ = ρ_N, is then a corollary. Where the library has both under the names X and X_paper or X_lim, they are listed below (generated from the source). The first column is the rate form, except for `Lemma2_1` (the N-family form of §3 (a) 6) and `thermo_interBox` (the interaction estimate of the duplication for a general interaction W, with the paper's hypotheses in the second form).

| Rate form | Paper or limit form | File |
|---|---|---|
| `Eq6_2` | `Eq6_2_paper` | `LHYUpper/Kinetic/LowMid.lean` |
| `Eq6_3` | `Eq6_3_paper` | `LHYUpper/Kinetic/LowMid.lean` |
| `Eq7_45` | `Eq7_45_paper` | `LHYUpper/Pair/UUVV.lean` |
| `Eq7_46` | `Eq7_46_paper` | `LHYUpper/Pair/UUVV.lean` |
| `Lemma2_1` | `Lemma2_1_paper` | `LHYUpper/Position/Lemma21.lean` |
| `Lemma5_3` | `Lemma5_3_paper` | `LHYUpper/Particles/PaperForms.lean` |
| `Lemma5_6` | `Lemma5_6_paper` | `LHYUpper/Particles/PaperForms.lean` |
| `Prop5_4_PH` | `Prop5_4_PH_paper` | `LHYUpper/Particles/Totals.lean` |
| `Prop9_1` | `Prop9_1_paper` | `LHYUpper/FourLegs/Section9.lean` |
| `Thm5_1` | `Thm5_1_lim` | `LHYUpper/Particles/PaperForms.lean` |
| `thermo_interBox` | `thermo_interBox_paper` | `LHYUpper/Thermo/InterBox.lean` |

The same relation holds under other names for `Kinetic_rate` and `lemma4_1` (Lemma 4.1), `OneLeg_rate` and `lemma4_5` (Lemma 4.5), `Lemma8_3_first` and `Lemma8_3_paper` (Lemma 8.3), `Lemma9_2_case1`, `Lemma9_2_case2`, `Lemma9_2_case3` and `Lemma9_2` (Lemma 9.2), `Lemma10_2_rate` and `Lemma10_2` (Lemma 10.2), `Lemma11_2_rate` and `Lemma11_2` (Lemma 11.2). In these limit forms the paper's lim sup_{k_c,ρ} is read as the upper limit in `EReal` over k_c → ∞ of the upper limit over N → ∞.

### (d) Steps the paper sketches, completed in the library

The arXiv version only sketches the following steps or leaves them out. The final version of the paper writes them out, about nine pages: the end of §4 (Theorem 3.1 ⇒ Theorem 2.2), §12 (the proof of Lemma 2.2), §12.1 (Lemma 2.1 from Theorem 2.2 and Lemma 2.2), §12.2 (the duplication, which proves Theorem 2.1) and Appendix A (the proofs of Propositions 5.2 and 5.3). The library follows the same route.

- **Theorem 3.1 ⇒ Theorem 2.2.** §4 proves (4.1) [Maindesired], which is Theorem 3.1. The library chooses k_c(N) → ∞ slowly enough that the bounds of Theorem 3.1 hold along the sequence (`Theorem31.theorem2_2_of_theorem3_1`), and turns Theorem 2.2 into the hypothesis of Lemma 2.2 with the variational principle (`Theorem31.limsup_ratio_e0P_le`).
- **The periodic-to-Dirichlet step of §12 (Lemma 2.2).** The cutoff q of (12.1) is only Lipschitz and the support of h reaches the boundary of the Dirichlet box; the library uses the smooth profile `prof` built from the ramp `ramp`, with (12.2) [proh1] unchanged (`localize_norm`); the constant of (12.7) becomes `cutConst` = 3π²C_s/8, with C_s = `rampConst` the energy of the ramp. (12.3) is proved as an identity with a periodized weight (`localize_kin`, `integral_profW`); the potential term is `localize_pot`; the averaging over u, (12.5)–(12.7), is `exists_dirichlet_of_periodic`, stated for finitely supported states (the class of `e0P`), and gives `e0D_le_e0P`. The proof of Lemma 2.2 then adds the change of density ρ → ρ̃ and the choice ℓ = ρ^{−25/48} of (12.8) [temp2.2] (which needs 2ℓ < L, true for N ≥ 17). Lemma 2.1 takes near-minimizers of e₀^D (`exists_lt_e0D`).
- **The duplication after Lemma 2.1.** The torus [0, L]³ is tiled by K³ cells of side ((N₀ + 1/2)/ρ)^{1/3} stretched to L/K, each holding a copy of the small-box state of Lemma 2.1 with N₀ or N₀ + 1 particles (`thermo_counts`, `thermo_scales`), separated by corridors of width d = ρ^{−1/2}. The symmetrized product is a Dirichlet trial state (`thermo_product`); the interaction between different cubes and with periodic images is at most 27 decayConst8(V)(N₀ + 1)/(2d)⁸ per particle (`thermo_interBox_paper`, with `decayConst8` = sup |V(z)||z|⁸). A Dirichlet trial state on [0, L]³ bounds e₀^P on the torus of side L through the periodized potential (`e0P_le_energyD_periodize`), and the three limits of (2.2) are then taken in `duplicationStep`. The reduction (2.3) [resultpro1] of §2.1 enters in this form, with its lim_{Λ→∞} read as the upper limit along `thermo` ρ.
- **Proposition 5.2 [prop1] and Proposition 5.3 [prop2].** Their proofs are in an appendix that the arXiv version does not compile; the final version prints it as Appendix A. The library proves them (`Prop5_2`, `Prop5_3`), with the reordering of the operators done by induction on the last step, and records in the conclusions some facts used later (for example β(0) ≥ 2).
- **The facts the paper calls standard or takes as known.** See §5.

## 4. Consistency of the hypotheses

The hypotheses of the statements of §1 can hold together, and the conclusion is not trivially true.

- **A potential satisfying `PotentialHyp`.** `scat_gaussian_potentialHyp` (`LHYUpper/Scattering/Gaussian.lean`) proves that the Gaussian V(x) = e^{−|x|²} satisfies `PotentialHyp`: it is a Schwartz function, even, nonnegative, equal to 1 at 0, and its Born constant is at most 1/2 + π^{3/2}/(4π) ≈ 0.943 < 1. So `PotentialHyp` is satisfiable and excludes V = 0.

```lean
/-- The Gaussian potential `V(x) = e^{-|x|²}` satisfies the hypotheses of Theorem 2.1 [mainthm]:
Schwartz, even, nonnegative, not identically zero, and `sup_x ∫ V(y)/(4π|x - y|) dy < 1`. -/
theorem scat_gaussian_potentialHyp : PotentialHyp (fun x : R3 => Real.exp (-‖x‖ ^ 2)) :=
```

- **Compiled instances.** At the end of `LHYUpper/Thermo/Duplication.lean` and of `LHYUpper/Assembly/Final.lean`, a section of checks defines, by private auxiliary definitions, the Gaussian potential and its scattering solution, taken as the solution given by `scattering_exists_unique` (not an ad hoc witness), and applies the statements of §1 to them. In `LHYUpper/Thermo/Duplication.lean` the duplication estimate is also applied at the density ρ = 1/1000 with corridor d = 1 and cells of N₀ = 1 or 2 particles:

```lean
/-- Duplication at `ρ = 1/1000`, `d = 1`, `N₀ = 1` for the Gaussian potential. -/
example := thermo_e0P_le_dup scat_gaussian_potentialHyp (ρ := 1/1000) (d := 1) (N₀ := 1)
  (by norm_num) (by norm_num) Duplication_fit Duplication_ψ₀_trial Duplication_ψ₁_trial
  Duplication_he₀ Duplication_he₁

/-- The duplication step for the Gaussian potential. -/
example := duplicationStep scat_gaussian_potentialHyp Duplication_Qw_spec

/-- Theorem 2.1 [mainthm] for the Gaussian potential. -/
example := mainTheorem scat_gaussian_potentialHyp Duplication_Qw_spec
```

  In `LHYUpper/Assembly/Final.lean`, the two identities at the end of §4, Theorem 3.1, Theorem 2.2 and the hypothesis of Lemma 2.2:

```lean
/-- The first identity at the end of §4 at the Gaussian potential. -/
example := Final_I1 scat_gaussian_potentialHyp Pw_spec

/-- The second identity at the end of §4 at the Gaussian potential. -/
example := Final_I2 scat_gaussian_potentialHyp Pw_spec

/-- Theorem 3.1 [lemma2.1] at the Gaussian potential. -/
example := Theorem3_1 scat_gaussian_potentialHyp Pw_spec

/-- Theorem 2.2 [lemma2] at the Gaussian potential. -/
example := Theorem2_2 scat_gaussian_potentialHyp Pw_spec

/-- The hypothesis of Lemma 2.2 [lemma1] at the Gaussian potential. -/
example := e0P_limsup_le scat_gaussian_potentialHyp Pw_spec
```

  In `LHYUpper/Model/Fock.lean`, the free condensate |N, 0, 0, …⟩ is a normalized N-particle state and has energy V₀N(N − 1)/|Λ| for (2.1), as it should; this checks that `HasEnergy` is the intended form of (2.1):

```lean
/-- The free condensate `|N, 0, 0, …⟩` is a normalized state of `𝓗_N`. -/
example (N : ℕ) : IsNState N (Finsupp.single (Finsupp.single (0 : Idx) N) (1 : ℂ)) :=
```

```lean
/-- The free condensate has energy `V₀ N (N - 1) / |Λ|` for (2.1) [ham]. -/
example (L : ℝ) (V : R3 → ℝ) (N : ℕ) :
    HasEnergy L V (Finsupp.single (Finsupp.single (0 : Idx) N) (1 : ℂ))
      ((ft V 0).re * N * ((N : ℝ) - 1) / L ^ 3) :=
```

- **No vacuity in the endpoint.**
  - `e0P` is an infimum over finitely supported normalized states, hence at least inf spec H/N (§3 (a) 1), so the Lean bound implies the paper's.
  - `e0P` cannot be trivially −∞: `HasEnergy` determines E (the sums of unconditionally convergent series are unique), and `hamiltonianNonneg` gives E ≥ 0.
  - The inner upper limit is not over the empty filter: `thermo` ρ is proper for every ρ > 0 (`thermo_neBot`), and `𝓝[>] 0` is proper.
  - `ratio` multiplies by the positive real (g₀^{5/2}ρ^{3/2})⁻¹ for ρ > 0, since g₀ > 0 (`scat_g0_pos`), so there is no sign or 0·∞ accident in `EReal`. In `scat_g0_pos` the potential and the solution are the implicit variables V, w of the section.

```lean
/-- The filter `thermo ρ` of §2 is proper for every `ρ > 0`: the pairs `(⌊ρ n³⌋₊, n)` tend to it,
so the lim sup in Theorem 2.1 [mainthm] is not taken over the empty filter. -/
theorem thermo_neBot {ρ : ℝ} (hρ : 0 < ρ) : (thermo ρ).NeBot :=
```

```lean
example : (thermo (7/2 : ℝ)).NeBot := thermo_neBot (by norm_num)
```

```lean
/-- `g₀ = 4πa > 0`. -/
theorem scat_g0_pos (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    0 < g0 V w :=
```

## 5. External inputs

None. The Lean code uses Mathlib and nothing else, and no hypothesis of a statement of §1 stands for a result of another work. The paper takes the following as known or standard; each is proved in the library:

- **Zero-energy scattering theory.** Existence and uniqueness of the solution 1 − w with 0 ≤ w < 1 and w → 0: `scattering_exists_unique`, through the solution of the Born equation `bornSol`, `scat_eq_bornSol`, and uniqueness by the maximum principle, `scat_solution_unique`. Properties: `scat_w_even`, `scat_g_nonneg`, `scat_g_le`, `scat_g_even`, `scat_g0_pos`, `scat_g0_le`. The scattering equation in momentum space (3.11) [av] and g_p = p²w_p (3.13) [gp]: `scat_av`, `scat_gp`, with the Fourier inversion `scat_w_inversion`. The identities at the end of §4, ‖∇w‖₂² − ‖Vw‖₁ + ‖Vw²‖₁ = 0 and V₀ − ‖Vw‖₁ = g₀: `scat_I2`, `scat_I1`, in the form used by the assembly `Final_I1`, `Final_I2`.
- **Fourier analysis on ℝ³ and Riemann sums on Λ*.** The lattice sums |Λ|⁻¹ Σ_{p∈Λ*} F(p) and their limits (2π)⁻³ ∫ F: the quantitative Riemann-sum lemma `riemann_shell` (integrands with a singularity |p|^{−a}, a < 3, at the origin and decay |p|^{−b}, b > 3, on shells, error K·C·E_a(2π/L) with `riemannRate`), the bound `latSum_abs_le`, and Parseval, `Kinetic_parseval`. The constants such as 16/(15π²) come from explicit integrals in `LHYUpper/Riemann/`.
- **Second quantization and the variational principle.** The action of a†a†aa on |α⟩ (`a4`, Lemma 7.1 [id4a] as `Lemma7_1`), the variational principle (`variational_principle`), and the position form of (2.1) on the torus: the symmetrized plane waves Φ_α (`symWave`, orthonormal by `symWave_orthonormal`) and `stateFn_norm_energy`.
- **The estimates of §12.** (12.2) `localize_norm`, (12.3) `localize_kin`, the potential term `localize_pot`, (12.5)–(12.7) `exists_dirichlet_of_periodic` and `e0D_le_e0P`; existence of Dirichlet trial states and of near-minimizers, `isDirichletTrial_nonempty`, `exists_lt_e0D`.

## 6. Proof route

The Lean proof follows the sections of the paper.

- **Theorem 3.1, §3–§11.** The trial state (3.18) is `trialState`, built from the set M of Definition 3.4 (`InM`), the weight `f0` and the square root convention `csqrt` of Definition 3.6. §5 (estimates on the numbers of particles) is in `LHYUpper/Particles/` and `LHYUpper/TrialState/`, §6 (kinetic energy, Lemma 4.1) in `LHYUpper/Kinetic/`, §7 (Lemmas 4.2–4.4) in `LHYUpper/Pair/`, §8 (Lemma 4.5) in `LHYUpper/OneLeg/`, §9–§11 (Lemma 4.6) in `LHYUpper/FourLegs/`, the scattering theory in `LHYUpper/Scattering/` and the lattice sums in `LHYUpper/Riemann/`. The six lemmas of §4 are summed in `Theorem31.theorem3_1_of_lemmas` (`LHYUpper/Assembly/`), as in the proof of §4.
- **Lemma 2.2 and Lemma 2.1, §12.** `LHYUpper/Position/`, following the sketch of §12 with the completions of §3 (d).
- **The duplication.** `LHYUpper/Thermo/`, as in §3 (d).

Where the route differs from the paper:

- The whole of §3–§11 is done in momentum space, in the occupation-number basis, as in the paper. Position space is used only in §12 and in the duplication. The bridge between the two descriptions is the map from occupation states to symmetrized plane waves (`symWave`, `stateFn`; `stateFn_norm_energy`) and back, by truncated plane-wave coefficients (`coeffState`, `coeffState_tendsto_norm`, `coeffState_tendsto_kin`), which gives `e0P_le_energyD_periodize`.
- In place of the limit statement before (5.35) [3.1], that L^{−3} Σ_p F(p) tends to ∫ F(p) d³p/(2π)³, the library proves the quantitative lemma `riemann_shell`, with an explicit rate and for integrands singular at the origin on regions that depend on L and ρ, and uses it for all lattice sums of §5–§10 (rescaled forms in `LHYUpper/Riemann/ScaledLimits.lean`). The limits of §5–§10 are therefore proved with rates (§3 (c)).
- The rest follows the paper's arguments, with the corrections of §3 (b).

## 7. Not formalized

- The remark after Theorem 2.1 that the result holds also for the Dirichlet boundary condition. The library proves the Dirichlet bound only in the small box (Lemma 2.1), not in the thermodynamic limit. The final version of the paper gives the argument at the end of §12.2.
- The remark after Theorem 2.1 that an error bound is available from the proof: Theorem 2.1 is stated as a limit. Many intermediate steps are proved with explicit rates (§3 (c)), but no rate for (2.2) is stated.
- The equality of `e0P` with inf spec H/N, and of `e0D` with the infimum over the Dirichlet form domain. The Lean bounds are at least as strong as the paper's without it (§3 (a) 1).
- Corollary 5.1, (5.38) [tail], as an iterated limit lim_{n→∞} lim_{ρ→0}. Its content enters the proof as the uniform tail bound `sum_PL_tail`.
- The Lee–Yang formula (1.1) [nextorder], the bound (1.2) [E-1] of the earlier work quoted in the introduction, the states (1.3) [trialstate0], (1.4) [trialstate00] and the heuristic derivation of the trial state in §3.1: background and motivation, not results of the paper.

## 8. Axioms and build

The main theorem, the theorems of the chain of §1 and the theorems of §4 depend only on the three standard axioms `propext`, `Classical.choice` and `Quot.sound`. To reproduce the check, build the library with `lake build` and run `lake env lean` on a scratch file outside the source tree:

```
import LHYUpper

#print axioms LHYUpper.mainTheorem
#print axioms LHYUpper.duplicationStep
#print axioms LHYUpper.Lemma2_1
#print axioms LHYUpper.Lemma2_1_paper
#print axioms LHYUpper.Lemma2_2
#print axioms LHYUpper.Theorem2_2
#print axioms LHYUpper.Theorem3_1
#print axioms LHYUpper.variational_principle
#print axioms LHYUpper.hamiltonianNonneg
#print axioms LHYUpper.scattering_exists_unique
#print axioms LHYUpper.scat_gaussian_potentialHyp
#print axioms LHYUpper.thermo_neBot
#print axioms LHYUpper.scat_g0_pos
```

Each line prints `'LHYUpper.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`.
