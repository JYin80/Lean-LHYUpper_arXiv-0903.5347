# Lean formalization of Yau–Yin, "The Second Order Upper Bound for the Ground Energy of a Bose Gas"

This repository contains a Lean 4 / Mathlib proof of the main result of

> Horng-Tzer Yau and Jun Yin, *The Second Order Upper Bound for the Ground Energy of a Bose Gas*,
> [arXiv:0903.5347](https://arxiv.org/abs/0903.5347).

The version of the paper that the Lean code follows is
[`paper/YauYin_LHYUpper_Lean_version.pdf`](paper/YauYin_LHYUpper_Lean_version.pdf) (LaTeX source in `paper/tex/`).
It keeps the numbering of the arXiv version, corrects a number of details of its arguments, and writes out the steps
that the arXiv version only sketches (§12, with the new §12.1 and §12.2, and Appendix A); the main result is
unchanged. Equation and theorem numbers in `docs/PAPER-VS-LEAN.md` refer to this PDF.

## Main result

Theorem 2.1 of the paper, the Lee–Huang–Yang upper bound for the ground state energy per particle of a dilute Bose gas
with periodic boundary condition in the thermodynamic limit:

```lean
/-- Theorem 2.1 [mainthm]: under the hypotheses on `V` (§2), with `1 - w` the zero-energy
scattering solution, the upper bound (2.2) holds. -/
theorem mainTheorem {V w : R3 → ℝ} (hV : PotentialHyp V) (hw : IsScatteringSolution V w) :
    Stmt.MainTheorem V w :=
```

in [`LHYUpper/Thermo/Duplication.lean`](LHYUpper/Thermo/Duplication.lean), with the statement

```lean
/-- Statement of Theorem 2.1 [mainthm]: the upper limit, first over `L → ∞` with
`N/L³ → ρ` and then over `ρ → 0`, of the ratio for `e₀^P` is at most `16/(15π²)`. -/
def MainTheorem (V w : R3 → ℝ) : Prop :=
  limsup (fun ρ : ℝ => limsup (fun x : ℕ × ℝ => ratio (g0 V w) ρ (e0P x.2 V x.1))
    (thermo ρ)) (𝓝[>] 0) ≤ (cLHY : EReal)
```

in [`LHYUpper/Statements.lean`](LHYUpper/Statements.lean): the upper limit as ρ → 0⁺ of the upper limit as
L → ∞ with N/L³ → ρ of (e₀^P(ρ, Λ) − g₀ρ)/(g₀^{5/2}ρ^{3/2}) is at most 16/(15π²), where g₀ = 4πa = ∫ V(1 − w).
All declarations lie in `namespace LHYUpper`.

The proof goes through the results of the paper in the order of its §2; each step is a statement in
`LHYUpper/Statements.lean` with the theorem that proves it.

| Paper | Lean theorem | File |
|---|---|---|
| Theorem 3.1 (the trial state on the small torus, for each cutoff k_c) | `Theorem3_1` | `LHYUpper/Assembly/Final.lean` |
| Theorem 2.2 (a periodic trial state on the small torus) | `Theorem2_2` | `LHYUpper/Assembly/Final.lean` |
| Lemma 2.2 (periodic to Dirichlet) | `Lemma2_2` | `LHYUpper/Position/Lemma22.lean` |
| Lemma 2.1 (a Dirichlet trial state in a small box) | `Lemma2_1`, `Lemma2_1_paper` | `LHYUpper/Position/Lemma21.lean` |
| Duplication to the thermodynamic limit | `duplicationStep` | `LHYUpper/Thermo/Duplication.lean` |
| Theorem 2.1 | `mainTheorem` | `LHYUpper/Thermo/Duplication.lean` |

## Hypotheses and external inputs

`PotentialHyp V` collects the paper's hypotheses on the potential: V is a Schwartz function (the reading of "smooth
with fast decay"), even ("symmetric"), nonnegative, not identically zero (so that g₀ > 0), and small enough that the
Born series converges, in the standard sufficient form sup_x ∫ V(y)/(4π|x − y|) dy < 1. `IsScatteringSolution V w`
says that 1 − w is the zero-energy scattering solution; `scattering_exists_unique` proves that it exists and is unique
for every such V.

There are no external inputs: the Lean code uses Mathlib and nothing else, and every fact the paper takes as known
(scattering theory, Riemann sums, the variational principle, the estimates of §12) is proved in the library
(`docs/PAPER-VS-LEAN.md` §5).

## Axioms

Every declaration of the library depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`. There is
no `sorry` and no declared `axiom`. `docs/PAPER-VS-LEAN.md` §8 lists the `#print axioms` commands that check this for
the main theorem and the theorems of the chain.

## Build

The toolchain is `leanprover/lean4:v4.36.0` (file `lean-toolchain`) with Mathlib `v4.36.0`.

```
lake exe cache get
lake build
```

`lake exe cache get` downloads the compiled Mathlib; `lake build` builds the whole library.

All source files use Lean's module system. `lake build` also builds `Challenge.lean`, which states the main
result with `sorry` (one warning, by design), and `Solution.lean`, which proves the same statement from the library.

## Palomar

The repository is laid out for the [Palomar registry](https://palomar-registry.org/) of Lean-verified mathematics:
[`Challenge.lean`](Challenge.lean) is the statement to audit (it imports Mathlib only and repeats verbatim the
definitions of `LHYUpper/Model/Basic.lean` and `LHYUpper/Model/Fock.lean`), [`Solution.lean`](Solution.lean) proves it,
[`comparator.json`](comparator.json) names the compared theorem and [`formalization.yaml`](formalization.yaml) holds
the metadata. `python3 scripts/check-lean-sources.py` and `./scripts/verify-comparator.sh` (Linux, needs `bwrap`) run
the checks locally; submissions go to <https://submit.palomar-registry.org/>.

The hypotheses of the theorems can be satisfied: `scat_gaussian_potentialHyp`
(`LHYUpper/Scattering/Gaussian.lean`) proves that the Gaussian V(x) = e^{−|x|²} satisfies `PotentialHyp`, and compiled
examples at the end of `LHYUpper/Thermo/Duplication.lean` and `LHYUpper/Assembly/Final.lean` apply the main theorem
and the theorems of the chain to it, with its scattering solution given by `scattering_exists_unique`.

## Map of the library

Section numbers refer to the paper in `paper/`.

- `LHYUpper/Model/`, `LHYUpper/Fock/`: the momentum-space Hamiltonian (2.1) on the torus, occupation-number states,
  the energy, and the variational principle.
- `LHYUpper/Scattering/`: the zero-energy scattering solution, w, g and λ (§2, §3).
- `LHYUpper/Riemann/`: quantitative Riemann sums on the dual lattice and the explicit integrals.
- `LHYUpper/TrialState/`: the set M of Definition 3.4, the trial state (3.18) and its normalization (§3).
- `LHYUpper/Particles/`: the estimates on the numbers of particles (§5).
- `LHYUpper/Kinetic/`: the kinetic energy, Lemma 4.1 (§6).
- `LHYUpper/Pair/`: the pair interaction energies, Lemmas 4.2–4.4 (§7).
- `LHYUpper/OneLeg/`: Lemma 4.5 (§8).
- `LHYUpper/FourLegs/`: the terms with four nonzero momenta, Lemma 4.6 (§9–§11).
- `LHYUpper/Assembly/`: Theorem 3.1 and Theorem 2.2 (§4).
- `LHYUpper/Position/`: position space, Lemma 2.2 and Lemma 2.1 (§12).
- `LHYUpper/Thermo/`: the duplication and Theorem 2.1 (§12.2).
- `LHYUpper/Statements.lean`: the statements of the chain.

## `docs/PAPER-VS-LEAN.md`

[`docs/PAPER-VS-LEAN.md`](docs/PAPER-VS-LEAN.md) compares the paper and the Lean proof in detail: what is proved,
every difference between the Lean statements and the printed ones, the corrections of the arXiv version, the
consistency of the hypotheses, and where the Lean proof takes a different route from the paper.

## License and authors

The code is released under the Apache License 2.0; see [`LICENSE`](LICENSE).

Paper: Horng-Tzer Yau and Jun Yin. Lean formalization: Jun Yin.
