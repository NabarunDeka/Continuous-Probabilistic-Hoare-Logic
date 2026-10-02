# ExponentialLaplace

Two programs that convert between the **exponential** and **Laplace** laws,
in both directions.

| File | Program | Constructs | Headline result |
|---|---|---|---|
| `ExponentialFromLaplace.v` | fold a Laplace draw onto its absolute value | **Exp(1/b)** from Laplace(0,b) | `ef_correct` — CDF `1 - exp(-t/b)`, for `0 <= t` |
| `LaplaceFromExponential.v` | attach a fair random sign | **Laplace(0,b)** from Exp(1/b) | `lp_laplace_from_exponential` — CDF `laplace_cdf 0 b t`, all `t` |

Both import `CPHL` from the repository root and `SampleBeforeLoop`,
`PersistentSampleLoop`, `HalfLaplaceRejection` and `SVT` from `examples/` one
level up; `ExponentialFromLaplace.v` additionally uses `real_integral_minus`
from `TruncatedLaplaceRejection`. Nothing outside this directory depends on
either file.

---

## What the language forces

Three limits in `CPHL.v` shaped both designs, and they are the most
transferable thing in this directory:

1. **There is no `Exponential` distribution.** `Distribution` is exactly
   `Uniform | Laplace | Gaussian`. An exponential variate can only be
   *derived*, never sampled.
2. **`Term` is a polynomial algebra** — `TProgVar | TLogicVar | TConst |
   TAdd | TMul`. No `ln`, so the inverse-CDF route `e := -ln(u)/lambda` is
   not expressible. No `Rabs`, so `e := |x|` is not expressible either.
3. **Negation is expressible**, as `TMul (TConst (-1)) _`. That single
   escape hatch is what makes both programs possible at all.

Together these mean: the fold must branch on the sign rather than call
`Rabs`, and the exponential *source* in the reverse direction has to enter
as a hypothesis on the incoming measure rather than as a sampling command.

---

## `ExponentialFromLaplace.v` — fold a Laplace onto |x|

```coq
x   <- sample(Laplace(0,b));
neg := (x < 0);
if neg then e := (-1) * x else e := x end      (* e = |x| *)
```

**Triple** (`ef_correct`, for `0 <= t` and `0 < b`):

```coq
{{ Pr[true] = 1 }}
  $(ef_prog b)
{{ Pr[$(ef_out t)] = $(1 - exp (- t / b)) }}
```

`1 - exp(-t/b)` is the Exp(1/b) CDF, so the folded variable is exponential
with rate `1/b`.

### What came out of the proof — an atom that will not cancel

Folding sends the two halves of the line onto `[0,t)`:

```
then-branch:   { -t < x < 0 }     OPEN at -t
else-branch:   {  0 <= x < t }    half-open
```

The **else** half is a difference of two strict CDFs and evaluates exactly:
`1_[0,t) = 1_{z<t} - 1_{z<0}`, pointwise, no correction.

The **then** half is not. Negation flips `<` into `>`, so its left endpoint
is open — but CPHL's closed forms come in only two shapes,
`laplace_integral_strict_cdf` for `z < c` and `laplace_integral_survival`
for `c <= z`. Neither produces an open left endpoint. The identity one
would like,

```
1_(-t,0) = 1_{z<0} - 1_{z<-t} - 1_{z=-t}
```

is **false at `t = 0`, `z = 0`** (it gives `-1` where the answer is `0`).
The repair is to move the atom to the other side, where it is correct for
every `t >= 0`:

```
1_(-t,0) + 1_{z=-t} * 1_{z<0}  =  1_{z<0} - 1_{z<-t}
```

and then kill it with `real_integral_singleton_zero`. That axiom is
**already in `CPHL.v`'s trusted base** — it was added there for `Uniform`'s
closed support — so nothing new is assumed. But this is the first place a
*Laplace* calculation has needed it.

**Suggested addition to `CPHL.v`:** a `laplace_integral_closed_cdf`
companion (`∫ dens · 1_{z <= c} = laplace_cdf c`) alongside the two existing
closed forms would remove the detour entirely. The gap is not in the
mathematics; it is that the closed-form family has two of the four endpoint
conventions.

---

## `LaplaceFromExponential.v` — attach a fair random sign

```coq
s := toss(1/2);
if s then z := e else z := (-1) * e end
```

**Triple** (`lp_laplace_from_exponential`, for `0 < b`, every `t`):

```coq
{{ (Pr[$(lp_src_below t)] = $(exp_cdf b t))
   /\ (Pr[$(lp_src_above t)] = $(exp_survival b t)) }}
  $(lp_prog)
{{ Pr[$(lp_below t)] = $(laplace_cdf 0 b t) }}
```

The source is a **hypothesis**, for the reason in §1: there is no
`Exponential` to sample and no `ln` to build one. `lp_src_above t` is
written `-e < t`; `lp_src_above_spec` proves that on the state this is the
event `e > -t`, so the second hypothesis really is the source's survival
function read at `-t`.

### What came out of the proof — separating the program from the arithmetic

The content is the **distribution-agnostic** mixture lemma, in which nothing
exponential appears:

```coq
Theorem lp_sign_mixture : forall fe se t : R,
  {{ (Pr[$(lp_src_below t)] = $(fe)) /\ (Pr[$(lp_src_above t)] = $(se)) }}
    $(lp_prog)
  {{ Pr[$(lp_below t)] = $((fe + se) / 2) }}.
```

A fair sign averages the source's lower tail with its reflected upper tail,
for **arbitrary** `fe` and `se`. The exponential answer is then a single
arithmetic instantiation (`lp_mixture_is_laplace`), and that is where the
`t < 0` / `t = 0` / `t > 0` case split lives — all three cases, one `lra`
each.

Keeping the two apart is what makes this file short: **the program reasoning
never sees a case split, and the case split never sees the program.** The
same split done inline would have tripled the Hoare-logic work for no gain.

### A lexing hazard worth recording

Opening `cphl_scope` makes `[[` a token (the `cphl_prob` delimiter). The
ordinary Rocq intro pattern

```coq
destruct (total_order_T z (- t)) as [[Hlt | Heq] | Hgt].   (* parse error *)
destruct (total_order_T z (- t)) as [ [Hlt | Heq] | Hgt].  (* fine *)
```

fails with a confusing `[or_and_intropattern_loc] expected`. A space fixes
it. This will bite any file that uses the notations and nested destructs.

---

## Axiom audit

Verified with `Print Assumptions` against the current build:

| | `real_integral_exp_*` | `real_integral_singleton_zero` |
|---|---|---|
| `ef_correct` | uses (below, between) | **uses** |
| `lp_sign_mixture` | none | none |
| `lp_laplace_from_exponential` | none | none |

The reverse direction touches **no integral closed form at all** — because
the source law is a hypothesis, no integral is ever evaluated. All the
analytic content sits in the forward direction. Neither file adds an axiom
of its own; both stay inside `CPHL.v`'s trusted base.

No `Admitted`, no holes.

---

## Status of the round trip

The two files are converses, but they do **not** yet compose into a
Rocq-checked loop. `LaplaceFromExponential.v` assumes two things about its
source; `ef_correct` supplies the first, and only for `0 <= t`. Still
missing:

- `Pr[e < t] = 0` for `t < 0` — both fold regions are empty there, so the
  same proof shape works with both integrals evaluating to `0`;
- `Pr[-e < t] = exp_survival b t`, which needs `0 <= e` almost surely and is
  not an instance of anything proved here.

Neither is deep. Until they are proved, "Laplace → Exp → Laplace" is a claim
about the mathematics, not a checked composition.

---

## Notes

- Both files use CPHL's notations. Real-valued arguments are wrapped in
  `$( )`: inside `cphl_prob`, a bare `t * t` parses as `PMul (PConst t)
  (PConst t)`, whereas `$(t * t)` gives the intended `PConst (t * t)`.
- The conditional in both programs goes through `svt_if_constants` from
  `SVT.v` — the exact conditional rule, where rigid variables record the two
  branch masses and `HIfEq` adds them.
- Modules sit in the **root logical path**, so `.vo` files stay flat in
  `build/` and `Require Import` works unchanged. The root `Makefile` picks
  this directory up via `SUBDIRS`.
- Build from the repository root with `make` (full clean rebuild ≈ 16s).
