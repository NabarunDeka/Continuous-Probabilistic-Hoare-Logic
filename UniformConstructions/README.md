# UniformConstructions

Examples that build a **new distribution out of `Uniform(0,1)` draws** and prove
the resulting law inside CPHL, plus the analytic axioms those proofs need.

Everything here is a closed cluster: no file outside this directory depends on
any file in it. The dependencies point the other way — these files import
`CPHL`, `SampleBeforeLoop`, `PersistentSampleLoop`, and `HalfLaplaceRejection`
from the parent directory.

| File | Constructs | Headline result |
|---|---|---|
| `UniformAxiomsAdditional.v` | — (support) | 2 + 1 axioms for uniform integrals, and the CDF machinery derived from them |
| `UniformRejectionSampling.v` | conditional law on an accepted quadrant | `ur_one_third` — probability exactly `1/3` |
| `TriangularRejection.v` | **triangular / Beta(2,1)**, density `2x` on `[0,1]` | `ta_correct` — CDF `t²`, for `0 < t ≤ 1` |
| `MaxOfTwoUniforms.v` | **max of two uniforms** = the same Beta(2,1) | `mx_correct` — CDF `t²`, for `0 ≤ t ≤ 1` |

`SamplingFromUniform.md` (moved in with them) is the survey that motivated these:
candidate uniform-to-X constructions, which ones this framework can reach, and
citations. Items (b) and (d) there are catalogued but not implemented.

---

## Why a separate axiom file at all

`CPHL.v` gives closed forms for **exponential** region integrals, which covers
every Laplace calculation in `examples/`. For `Uniform` it gives the
constructor, the density, and the validity condition — but **no lemma that
evaluates a uniform integral**. So none of the examples below could even start.

`UniformAxiomsAdditional.v` adds the missing laws. After the constant
`1/(u-l)` is pulled out, a uniform integrand is just the indicator of a bounded
interval, so one law does nearly all the work:

```coq
Axiom real_integral_between_length :          (* interval length *)
  forall a b, a <= b -> real_integral_between a b (fun _ => 1) = b - a.

Axiom real_integral_point_null :              (* endpoint has zero mass *)
  forall c f, real_integral (fun z => real_indicator (z = c) * f z) = 0.

Axiom real_integral_between_linear :          (* first moment *)
  forall a b, a <= b -> real_integral_between a b (fun x => x) = (b*b - a*a)/2.
```

Derived from them, and used by the examples: `uniform_density_R`,
`uniform_cdf`, `uniform_integral_strict_cdf`, `uniform_density_total`,
`uniform_integral_survival`, `uniform_cdf_bounds`, `uniform_cdf_unit`,
`real_integral_indicator_interval`, `real_integral_indicator_linear`,
`real_integral_minus`.

**The second axiom is an artefact, not mathematics.** CPHL's region operators
use *half-open* intervals — a comment in `CPHL.v` says this was chosen
specifically to "avoid requiring a separate zero-mass-at-an-endpoint axiom".
But the uniform density is written over a *closed* interval,
`real_indicator (l <= z /\ z <= u) / (u - l)`, so the axiom that design avoided
becomes unavoidable the moment that density is integrated. It bites in exactly
two places: total mass, and the CDF above the top of the support. Strictly
inside the support, `[l, t)` is already half-open and the length law alone
suffices. **Changing the density to `l <= z < u` would remove the need for
`real_integral_point_null` entirely** — that is an edit to `CPHL.v` rather than
an addition here, so it was not taken.

**Consistency note.** These are linearity/evaluation laws only. Adding
unrestricted *monotonicity* of a total `real_integral` would be inconsistent:
the indicator of `[0,n]` versus the constant `1` forces `∫1 ≥ n` for every `n`.

---

## `UniformRejectionSampling.v` — the continuous rejection sampler

The continuous analogue of `Probabilistic-Hoare-Logic/RejectionSampling.v`,
which tosses two fair coins and retries while both come up true. Each toss
becomes a uniform draw, and "true" becomes "landed in the lower half".

```coq
retry := true;
while retry do
  x     <- sample(Uniform(0,1));
  y     <- sample(Uniform(0,1));
  retry := (x < 1/2 /\ y < 1/2)
end
```

**Triple** (`ur_one_third`):

```coq
{{ Pr[true] = ur_w }}
  $(ur_prog)
{{ E[$(condition_pconstruct ur_q (c_not ur_guard))] = $(1 / 3) * ur_w }}
```

i.e. `Pr[x < 1/2  /\  1/2 <= y  /\  ¬retry] = (1/3)·w`. The loop equation is the
same fixed point as the discrete original:

```
s = (1/4)·s + 1/4      ⟹      s = 1/3
```

Reject mass `1/4` (lower-left quadrant), target exit mass `1/4` (upper-left),
total exit mass `3/4`, so the conditional answer is `(1/4)/(3/4) = 1/3`.

**What came out of the proof.** Two samples per iteration means the weakest
precondition carries a **doubly nested `QIntegral`**. It stays tractable only
because the event *factors* into an x-part and a y-part: the inner integral
collapses to a constant times an indicator on the outer variable, which
`real_integral_scale` lifts straight out. No genuinely two-dimensional
reasoning happens anywhere. That observation is what makes the next file
interesting.

---

## `TriangularRejection.v` — rejection under a non-constant envelope

```coq
retry := true;
while retry do
  x     <- sample(Uniform(0,1));
  y     <- sample(Uniform(0,1));
  retry := (x <= y)              (* accept iff y < x *)
end
```

**Triple** (`ta_correct`, for `0 < t <= 1`):

```coq
{{ Pr[true] = ta_w }}
  $(ta_prog)
{{ E[$(condition_pconstruct (ta_q t) (c_not ta_guard))] = $(t * t) * ta_w }}
```

**The distribution.** The accepted `x` has density `2x` on `[0,1]` and CDF `t²`
— the triangular law, i.e. Beta(2,1), equivalently the maximum of two
independent uniforms. Loop equation:

```
s = (1/2)·s + t²/2      ⟹      s = t²
```

This is von Neumann's rejection method (1951) with a polynomial envelope.

**What came out of the proof — the first non-factoring accept condition.**
Every earlier example (Laplace ones included) has an accept condition that
factors, so the inner integral collapses to a *constant*. Here `y < x` couples
the two draws: the inner integral over `y` returns `uniform_cdf 0 1 k`, a
**function of the outer variable**. The outer integral is therefore a genuine
polynomial integral — and that, precisely, is what
`real_integral_between_linear` was added to supply. The moment axiom is not
decoration; it is the price of the first coupled event.

**This also delimits the reachable class.** From uniform draws, this framework
reaches exactly those accept regions whose sections are intervals with
**polynomial** endpoints in the outer variable. Marsaglia's polar method fails
*not* because it is two-dimensional — its sections are intervals too — but
because their length `2·√(1-k²)` is not polynomial.

**Boundary.** `0 < t` is required *strictly*. At `t = 0` the true answer is `0`,
but `while_progress` demands positive **target** exit mass and `t²/2` vanishes
there. This is the third independent witness to that defect, after
`TruncatedLaplaceRejection.v` (at `t = a`) and the zero-probability regions in
`NoisyThresholdMonitor.v`.

---

## `MaxOfTwoUniforms.v` — the same law, and a check on the axiom

```coq
x <- sample(Uniform(0,1));
y <- sample(Uniform(0,1))
```

**Triple** (`mx_correct`, for `0 <= t <= 1`):

```coq
{{ Pr[true] = mx_w }}
  $(mx_prog)
{{ Pr[$(mx_event t)] = $(t * t) * mx_w }}
```

`x < t /\ y < t` *is* `max(x,y) < t`, so this is the CDF of the maximum of two
independent uniforms — the same `t²` that `TriangularRejection.v` obtains by
rejection, reached with no loop and by a different analytic route.

**Why it earns its place: it is an independent check on the moment axiom.**
Here the event *does* factor, so the inner integral collapses to the constant
`uniform_cdf 0 1 t` and the outer is another CDF. The answer is a product of two
CDFs and needs no moment law at all. If `real_integral_between_linear` were
wrong, the two files would disagree on `t²`.

Verified with `Print Assumptions` against the current build:

| | `real_integral_between_length` | `real_integral_point_null` | `real_integral_between_linear` |
|---|---|---|---|
| `ur_one_third` | uses | uses | **free** |
| `ta_correct`   | uses | uses | uses |
| `mx_correct`   | uses | uses | **free** |

`mx_correct` is genuinely free of the moment axiom and still yields `t²`.

**One more difference.** No loop here means no `while_progress`, so `t = 0` *is*
allowed — and correctly gives probability `0`. `TriangularRejection.v` cannot
reach `t = 0` at all. The gap there is a property of the **while rule**, not of
the mathematics, and this file is the evidence for that claim.

---

## Notes

- All four files use CPHL's notations (`<{ … }>`, `[[ … ]]`, `{{ … }} … {{ … }}`).
  Real-valued arguments are wrapped in `$( )`: inside `cphl_prob`, a bare
  `t * t` parses as `PMul (PConst t) (PConst t)`, whereas `$(t * t)` gives the
  intended `PConst (t * t)`.
- Modules all sit in the **root logical path**, so `Require Import
  UniformAxiomsAdditional` works unchanged from anywhere in the project and
  `.vo` files stay flat in `build/`. The root `Makefile` picks this directory
  up via `SUBDIRS`; `coqdep` gets the extra `-Q examples/UniformConstructions ""` it
  needs to resolve requires on a clean build, while `coqc` keeps loading
  compiled `.vo` out of `build/` only.
- Build from the repository root with `make` (full clean rebuild ≈ 16s).
- No `Admitted`, no holes: the three axioms above plus `CPHL.v`'s trusted base
  are the entire trusted surface.
