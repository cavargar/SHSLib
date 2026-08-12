# Module group: Bujorianu2006 — general stochastic hybrid systems

**Files:** 8 modules under `SHSLib/Bujorianu2006/` (1,863 lines)
**Layer:** Bujorianu2006
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `6cbbd3ec`, adopted 2026-08-12

A formalization of M. L. Bujorianu and J. Lygeros, *Toward a general theory of
stochastic hybrid systems* (LNCIS 337, Springer, 2006). A GSHS is a hybrid process
whose continuous part is a diffusion in each mode and whose discrete transitions are
driven both by a spontaneous jump rate and by forced jumps at the boundary; the
paper's programme is to build such a process as a **Markov string** — a concatenation
of killed diffusions glued by a renewal kernel — and to identify its extended
generator.

| Module | Contents |
|--------|----------|
| `HybridSpace` | The hybrid state space $\bigcup_i \{i\}\times X^i$, its closure and boundary, and the measurable-embedding facts that make it a Borel space |
| `MarkovString` | Jump times and their monotonicity, translation operators and the shift semigroup, càdlàg paths, the Markov property |
| `TerminalTimes` | Additive and multiplicative functionals, terminal times, and their composition laws |
| `JumpMeasure` | The jump counting measures $p$, $p^*$; boundary jump counts; monotonicity in time and in the target set |
| `Resolvent` | The semigroup, the resolvent $U_p$, $p$-excessive functions, and the strong Markov property expressed through them |
| `Martingale` | The strong generator and its uniqueness, differentiability of the semigroup, and **Dynkin's formula** |
| `Generator` | The extended generator: Hessian and diffusion matrices, the continuous part $\mathcal{L}_b f + \tfrac12\mathrm{Tr}(\sigma\sigma^{\!\top}\mathbb{H}^f)$, and the jump part |
| `GSHSProperties` | Sojourn times as terminal times, shift-invariance of the renewal kernel, and GSHS executions |

## Substance

This layer is self-contained — it imports nothing from the rest of SHSLib — and
carries 71 theorems with no `:= True` placeholders and no `axiom` declarations.
Results such as `strongGenerator_unique`, `hasDerivWithinAt_semigroup`,
`resolvent_excessive` and `dynkin_formula` are proved analysis, not statements
parameterized by their own conclusions.

## Related

`FPK` — Bect's treatment of the same class of systems, organised around the
measure-valued FPK equation rather than the process construction. The two are
complementary: Bect assumes the process and derives its forward equation, while this
layer builds the process and identifies its generator.
