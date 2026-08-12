# Module group: Ullah — the dCKE via region splitting

**Files:** 4 modules under `SHSLib/Ullah/` + the `SHSLib/Ullah.lean` index
**Layer:** Ullah
**Status:** ✅ 0 sorries (all standard axioms)
**Origin:** Aristotle project `9bb78578`

A formalization of §8.2 of M. Ullah and O. Wolkenhauer, *Stochastic Approaches for
Systems Biology*. It reaches the same differential Chapman–Kolmogorov equation as
[Gardiner](Gardiner.md), but by a different route: the gain–loss flux is split into
a near region $\|q\| < \varepsilon$ and a far region, each limit is taken separately,
and the drift/diffusion terms emerge from a Taylor expansion in the near region
**without integration by parts**.

| Module | Contents |
|--------|----------|
| `Basic` | Time difference quotient (8.4), gain–loss flux (8.5), the near/far splitting (8.6) |
| `Near` | Change of variables $y - y' = q$ (8.7), Taylor expansion, conditional moments $\langle \Delta Y_i\rangle_y$ and $\langle \Delta Y_i \Delta Y_j\rangle_y$, vanishing of $C_{ijk}$ |
| `Limits` | The limits (8.11) of the near region and (8.12) of the far region |
| `DCKE` | The dCKE (8.13), derived from the density |

`SHSLib/Ullah.lean` carries the full (8.x) → Lean-name correspondence table.

## Relation to Gardiner

The differentiability conditions (8.8) and (8.9) are conditions (ii) and (iii) of
Gardiner's §3.4. `Ullah.condDrift_iff_mom` and `Ullah.condDiffusion_iff_mom` prove
the identification, so the two derivations are formally connected rather than merely
parallel. `Ullah/` depends on `Gardiner/`.

## Related

`Gardiner` · `FPK`
