# examples

Programs verified against the CPHL calculus in `../CPHL.v`. Build everything
from the repository root with `make`; artifacts land flat in `../build/`.

Every result here is of the form **"this triple is derivable in CPHL"**.
There is no command semantics and no soundness theorem, so none of these is
a claim about what a program actually does when run — see `../flags/FLAGS.md`
F7. Known defects and gaps found while writing these files are catalogued
there; individual files point at the relevant flag.

Nothing is `Admitted`; the one deliberately-unproved statement
(`t2_prog_target`) is a `Definition ... : Prop`, not a hole.

---

## The while-fragment probes

Written to map the boundary of what `HWhile` can reach. Read them in this
order — each one adds exactly one difficulty.

| File | Program | Headline | Notes |
|---|---|---|---|
| [SampleBeforeLoop.v](SampleBeforeLoop.v) (417) | sample once, then a fair-coin loop | `t1_correct` — `Pr[b] = y` | smallest program combining `HRealSample` + `HBoolAssign` + `HWhile`; the loop is forced to be independent of `x` |
| [PersistentSampleLoop.v](PersistentSampleLoop.v) (603) | loop body branches on a **persistent** sample | `t2_loop_derivable` ✓ · `t2_prog_target` ✗ | the obstruction is itself proved (`t2_split_blocks_entry`) — **FLAGS F2** |
| [HalfLaplaceRejection.v](HalfLaplaceRejection.v) (356) | resample until `0 <= x` | `t3_correct` — `Pr[t <= x ∧ ¬retry] = exp(-t/b)·y` | fresh in-body sampling is the *easy* case — **FLAGS F11** |
| [TruncatedLaplaceRejection.v](TruncatedLaplaceRejection.v) (514) | resample until `x ∈ [a,c)` | `t4_correct` — `(F t − F a)/(F c − F a)·y` | first genuine normalization; `t = a` unreachable — **FLAGS F1** |
| [NoisyThresholdMonitor.v](NoisyThresholdMonitor.v) (744) | resample until the reading leaves a band, report which side | `ntm_left_probability`, `ntm_right_probability`, `ntm_exhaustive` | two exit events from **one** certificate, differing only in `q` |

`SampleBeforeLoop.v` and `HalfLaplaceRejection.v` double as the shared-helper
modules — several later files import them for lemmas (`psatisfies_p_eq`,
`rpv_eq_dec_refl`, `t3_expect_const`, `laplace_cdf_centre`, …) rather than for
their theorems.

### Where the sequence stops

[AlternatingModeLoop.v](AlternatingModeLoop.v) (342) sits outside the order
above, because it adds no difficulty — it records why the next step cannot be
taken. The program flips a mode bit every iteration:

    done := ff; mode := ff;
    while ~done do
      x    <- sample(Laplace(0, b));
      done := (0 <= x);
      mode := ~mode
    end

which looks like it wants a two-region certificate indexed by `mode`. It does
not. Nothing reads `mode` — not the guard, not the acceptance test — so the
exit rate is 1/2 whatever the mode is, the chain lumps, and `am_terminates`
(`Pr[done] = y`) goes through with a **single** region; `mode := ~mode` costs
one extra `HBoolAssign` and nothing else. Making the mode matter needs a
per-mode threshold, whose post-sample integrand is a sum of scaled indicators.
That sum cannot be split. **FLAGS F3.**

## Privacy mechanisms

Is a point inside the unit circle, decided privately: the exact squared
distance is computed first, then a single Laplace draw perturbs that one
scalar, then it is compared against the radius. Two variants of the same
mechanism, proved to have identical output distributions.

| File | Main triple | Noise written as |
|---|---|---|
| [PointInDiskInPlace.v](PrivatePointInDisk/PointInDiskInPlace.v) | `pdi_correct`, `0 < b` — `{ Pr[tt] = 1 } pdi_prog px py cx cy b { Pr[inside] = laplace_cdf D b 1 }` | `d sample laplace(d, b)` — re-centre in place; first `Term`-valued distribution location in the repo |
| [PointInDiskAdditive.v](PrivatePointInDisk/PointInDiskAdditive.v) | `pda_correct`, same triple | `n sample laplace(0,b); d := d + n` — the idiomatic Laplace-mechanism shape, and the one to extend towards DP |
| [LaplaceConvolution.v](PrivatePointInDisk/LaplaceConvolution.v) | **no triple** — analytic support | `lc_convolution`: a sum/difference of two Laplace(0,b) has density `(1/4b)(1+\|z\|/b)e^{−\|z\|/b}`; `lc_difference_not_laplace` proves no Laplace matches it |
| [OneDimensional/OneDimDistance.v](PrivatePointInDisk/OneDimensional/OneDimDistance.v) | `od_correct` — `{ Pr[tt]=1 } od_prog p c b { Pr[inside] = F(1−D) − F(−1−D) }` | 1-D, noise on the **difference** |
| [OneDimensional/OneDimPoints.v](PrivatePointInDisk/OneDimensional/OneDimPoints.v) | `op_correct` — `{ Pr[tt]=1 } op_prog p c b { Pr[inside] = G(D+1) − G(D−1) }` | 1-D, the two **points** perturbed independently — two nested integrals |
| [OneDimensional/LaplaceCdfConvolution.v](PrivatePointInDisk/OneDimensional/LaplaceCdfConvolution.v) | **no triple** — analytic support | `lcc_convolution_cdf`: the CDF `G` of a difference of two Laplace(0,b) |

| [NormalSampling/NormalDisk.v](PrivatePointInDisk/NormalSampling/NormalDisk.v) | `nd_combined_noise`, `nd_four_noise_derivable` | the four-noise disk with **normal** noise: the two noises per coordinate provably collapse into one `Gaussian(0, b√2)` |
| [NormalSampling/NormalDistance.v](PrivatePointInDisk/NormalSampling/NormalDistance.v) | `nrm_correct` — `{ Pr[tt]=1 } nrm_prog { Pr[inside] = nrm_cdf b (1−D) }` | normal noise on the scalar **distance**; unconditional, and needs no Gaussian axiom at all |
| [NormalSampling/NormalDistanceL1.v](PrivatePointInDisk/NormalSampling/NormalDistanceL1.v) | `nl_correct` — same shape with the **L1** distance `Σ\|xi−yi\|` | abs computed by a real `CIf` gadget, crossed with the conditional rule |
| [NormalSampling/NormalBallL1.v](PrivatePointInDisk/NormalSampling/NormalBallL1.v) | **no triple** — `nb_target` stated, open | L1 ball with the two **points** perturbed |

**The one-dimensional pair settles what blocks the disk.** `OneDimPoints.v`
perturbs both operands independently — the very shape that is unreachable in
two dimensions — and it goes through, because in 1-D "inside the unit ball"
is an *interval* with constant endpoints rather than a disk with
square-root sections. So independent double perturbation is not the
obstruction; the disk is. `op_less_accurate_than_od` also proves the cost of
the extra noise: at the centre the double-perturbation mechanism is worse by
exactly `exp(−1/b)/(2b)`.

**`NormalSampling/` answers the obvious follow-up: does switching to normal
noise help?** Partly, and not where you would guess.

- It does **not** unblock the 4→2 reduction — that is F15, and it is
  distribution-independent. `nd_combined_noise` proves the analytic content
  (the per-coordinate noises collapse to one `Gaussian(0, b√2)`), and the
  reorganisation is still unavailable.
- It **does** make the *central* disk probability elementary,
  `1 − exp(−1/(4b²))`, because the bivariate normal is rotationally
  symmetric. Laplace has no closed form at any offset. But reaching it needs
  **polar coordinates**, a 2-D change of variables — a strictly stronger
  missing law than F15's 1-D ones. Stated as `nd_central_target`, unproved.
- Off-centre it is a Marcum Q-function, not elementary.
- And normals are **worse** in 1-D: the Laplace CDF is elementary and CPHL
  evaluates it, so `OneDimensional/` closes completely; the normal CDF is
  `erf`, so the same 1-D test is out of reach.

The mechanisms line up as: noise on the **distance** closes for either
distribution and either metric (`PointInDiskAdditive.v`,
`NormalSampling/NormalDistance.v`, `NormalSampling/NormalDistanceL1.v`),
noise on the **points** closes for none (`TODO/FourNoiseDisk.v`,
`NormalSampling/NormalDisk.v`, `NormalSampling/NormalBallL1.v`). Collapsing
to a scalar before adding noise is what makes a mechanism reachable.

**The L1 files add two findings.** Computing `|·|` needs a real `CIf`, and
CPHL's conditional rules only conclude with an *indicator* postcondition —
so a branch can only be crossed when no sampling remains after it. Drawing
the noise first fixes that. And geometrically, the L1 ball's sections are
`|v| < 1 − |u|`, with **piecewise-linear** endpoints, where the L2 disk's are
`|v| < √(1−u²)`. That is exactly the polynomial-endpoint criterion, so
**L1 + Laplace looks genuinely reachable** and is blocked only by F15 — the
most promising unbuilt mechanism here.

Both have the first polynomial `CRealAssign` (`d := (px−cx)² + (py−cy)²`),
and in both the opening assignment is what makes the integral
state-independent — it closes the noise *location* in the first and the
indicator's *guard* in the second. Neither proves a DP bound, only the
output probability; see `../flags/FLAGS.md` F14, which also records why
perturbing the four coordinates separately is **not** derivable.

`SVT.v` below is the other privacy mechanism here.

`PrivatePointInDisk/TODO/` holds `FourNoiseDisk.v`: the four-noise variant
that perturbs both points, written out as an open problem — program, triple,
the explicit value it would need, and the two reasons it is stuck. That
directory is deliberately **not** in the Makefile's `SUBDIRS`, so an
in-progress attempt can live there without breaking `make`.

## Distribution constructions

| Directory | Builds | See |
|---|---|---|
| [UniformConstructions/](UniformConstructions/) | Exp-free laws from `Uniform(0,1)` draws: a `1/3` rejection sampler, the triangular/Beta(2,1) law two independent ways, plus the uniform integral axioms | [its README](UniformConstructions/README.md) |
| [ExponentialLaplace/](ExponentialLaplace/) | exponential ⇄ Laplace, both directions | [its README](ExponentialLaplace/README.md) |

`UniformConstructions/SamplingFromUniform.md` is the survey that motivated
that directory — candidate uniform-to-X constructions, which ones this
framework can reach, and citations. Items (b) and (d) there are catalogued
but not implemented.

## Closure properties of distribution families

| File | Main result | Notes |
|---|---|---|
| [GaussianDifference.v](GaussianDifference.v) | `gc_difference` — `∫ φ(m1,s1)(u)·φ(m2,s2)(u−z) du = φ(m1−m2, √(s1²+s2²))(z)` | the difference of two normals **is** normal. Adds one axiom, the Gauss integral `∫exp(−(u−m)²/2v)du = √(2πv)` — CPHL has the `Gaussian` constructor but no law to evaluate it |

Read against `PrivatePointInDisk/LaplaceConvolution.v`, which proves the
*opposite* for Laplace: the difference has density
`(1/4b)(1+|w|/b)e^{−|w|/b}`, and `lc_difference_not_laplace` shows no Laplace
density matches it. Normals are closed under differences; Laplaces are not.

`gc_program_target` states the corresponding fact about *programs* — that
sampling twice and subtracting is interchangeable with one combined sample —
and is deliberately **not** proved. It is blocked by `../flags/FLAGS.md` F15,
and it is the sharpest witness for that flag: unlike the disk case, the
analytic value here is a clean closed form that *is* proved, so missing
integral structure is the only thing in the way.

## Larger developments (collaborator's, via Codex)

| File | Subject |
|---|---|
| [SVT.v](SVT.v) (1569) | Two-query **Sparse Vector Technique**, the motivating example of *"Deciding Differential Privacy for Programs with Finite Inputs and Outputs"*. Top results: `svt_symbolic_hoare`, `svt_symbolic_concrete_hoare`, `svt_01_bot_top_probability` |
| [MonteCarloEst.v](MonteCarloEst.v) (4981) | Fixed-horizon **Monte Carlo estimator** for the area of a quarter disk. Top result: `monte_carlo_estimator_probability` |

**`SVT.v` is also a library.** `svt_if_constants` — the exact conditional
rule, where rigid variables record the two branch masses and `HIfEq` adds
them — is used by `PersistentSampleLoop.v` and both `ExponentialLaplace`
files. Moving or renaming `SVT.v` breaks those.

There was a second, notation-only presentation of the same development,
`SVT_notation.v`. Now that `SVT.v` itself uses the notations it was
redundant, and it has been retired to `../backup_pre_notation/`. **It was
not a pure duplicate**: it also carried 24 items for the `[1,1]` input
vector (`run_11`, `path_integral_11`, `symbolic_concrete_hoare_11`, …) that
`SVT.v` has no counterpart for. Those are preserved in the backup but are no
longer compiled by `make`. Porting them into `SVT.v` would put the `[1,1]`
case back under CI.

Note the scale/rate convention: the SVT paper writes `Lap(rate, location)`
while `CPHL.Laplace` stores `(location, scale)`, so rates `ε/2` and `ε/4`
appear as scales `2/ε` and `4/ε`.

---

## Layout and naming

All modules share the **root logical path**, so `.vo` files stay flat in
`../build/` no matter which directory the source sits in and every
`Require Import Foo` is a bare name. Two consequences:

- **Module basenames must be unique across the whole tree.**
- `-Q` is recursive, so each directory is listed separately in the root
  `Makefile`'s `SUBDIRS`; `-Q examples ""` alone would name a nested module
  `UniformConstructions.Foo` rather than `Foo`.

`../backup_pre_notation/` holds pre-notation copies of ten of these files and
is deliberately untouched — `diff -r` against it is the revert path if a
notation translation ever looks wrong.
