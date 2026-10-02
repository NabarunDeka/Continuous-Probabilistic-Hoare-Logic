# Simulating distributions from a uniform source

Candidate programs for the next round of examples, together with what each
one costs in new axioms and which classical algorithms are out of reach.

Everything here targets the existing `HWhile` / `HRealSample` machinery and
the uniform integral laws now in `CPHL.v`
(`real_integral_between_one`, `real_integral_singleton_zero`).

> **Citations below are from memory and unverified.** Check every one before
> it reaches the paper.

---

## The structural limit

From uniform draws alone, this framework can reach **bounded-support
densities that are piecewise polynomial, and nothing else.**

Two independent reasons:

1. **`Term` is a polynomial algebra** — `TProgVar | TLogicVar | TConst |
   TAdd | TMul`. No division, `exp`, `log`, `sqrt` or `cos`. So no inverse
   CDF that is not a polynomial can be written down at all.
2. **Unbounded support needs an unbounded counter**, which gives an infinite
   region partition, which `HWhile` cannot have (it needs finite `m`).

This is why `HalfLaplaceRejection.v` works: it obtains Exponential by
*conditioning a primitive Laplace*, not by *building* an unbounded law out
of uniforms.

The reachable family is exactly **von Neumann rejection under a polynomial
envelope**: if the accept region's sections are intervals with polynomial
endpoints, the inner integral is a polynomial in the outer variable and the
outer integral is a polynomial integral.

---

## Programs to build

### (a) Triangular / Beta(2,1) — recommended first

```
retry := tt;
while retry do
  x     <- sample(Uniform(0,1));
  y     <- sample(Uniform(0,1));
  retry := (x <= y)                 (* accept iff y < x *)
end
```

**Triple**, for `0 < t <= 1`:

```
{ E[1_tt] = w }   prog   { Pr[x < t  /\  ~retry]  =  t^2 * w }
```

The accepted `x` has density `2x` on `[0,1]` — the triangular law, i.e.
Beta(2,1). Equivalently: `x` is distributed as the maximum of two uniforms.

- one-step retry mass `Pr[x <= y] = 1/2`
- one-step target mass `Pr[y < x /\ x < t] = t^2/2`
- fixed point `s = (1/2) s + t^2/2`, so `s = t^2`

**Cost:** one new axiom, the first moment.

```coq
Axiom real_integral_between_linear :
  forall a b : R, (a <= b)%R ->
    real_integral_between a b (fun x => x) = ((b*b - a*a) / 2)%R.
```

**Why this one.** It is the first example here whose accept condition does
**not factor**: the inner integral over `y` returns `k`, a *function* of the
outer variable, rather than a constant. Every existing example collapses the
inner integral to a constant, so this exercises genuinely new machinery.

**Expect a boundary failure at `t = 0`.** The target mass is then `0` and
`while_progress` demands it be positive, exactly as in
`TruncatedLaplaceRejection.v`. That would be the third independent witness
to the `q`-dependent progress defect.

---

### (c) Maximum of two uniforms — the free cross-check

```
x <- sample(Uniform(0,1));
y <- sample(Uniform(0,1))
```

**Triple**, for `0 <= t <= 1`:

```
{ E[1_tt] = w }   prog   { Pr[x <= t  /\  y <= t]  =  t^2 * w }
```

Same law as (a), reached by a completely different route: the event
**factors** into an `x`-part and a `y`-part, so it is `t * t` by two
independent applications of the uniform CDF.

**Cost: zero new axioms.** Loop-free — no `HWhile` at all.

This is worth building *alongside* (a) rather than instead of it: it proves
the same constant `t^2` without the new axiom, so it is a real check on the
axiom (a) introduces.

An explicit `m := max(x,y)` would need a `CIf`; the event form above avoids
that and says the same thing.

---

### (b) Beta(3,1) — the obvious follow-on

```
retry := tt;
while retry do
  x     <- sample(Uniform(0,1));
  y     <- sample(Uniform(0,1));
  retry := (y <= x*x)               (* accept iff x*x < y is FALSE; see note *)
end
```

> Note: written to accept iff `y < x*x`, so `retry := (x*x <= y)`.

**Triple**, for `0 < t <= 1`:

```
{ E[1_tt] = w }   prog   { Pr[x < t  /\  ~retry]  =  t^3 * w }
```

- accept mass `Pr[y < x*x] = 1/3`
- target mass `Pr[y < x*x /\ x < t] = t^3/3`
- fixed point `s = (2/3) s + t^3/3`, so `s = t^3`

**Cost:** the quadratic moment, `∫_a^b x^2 = (b^3 - a^3)/3`, on top of (a)'s.

The general family is `∫_a^b x^n = (b^(n+1) - a^(n+1))/(n+1)`, but adding
them one at a time avoids fighting `pow` and induction for no present gain.

---

### (d) Irwin–Hall, n = 2

```
x <- sample(Uniform(0,1));
y <- sample(Uniform(0,1));
s := x + y
```

**Triple**, for `0 <= t <= 1`:

```
{ E[1_tt] = w }   prog   { Pr[s <= t]  =  (t^2 / 2) * w }
```

Non-factoring, but the section at `x = k` is `[0, t-k]`, whose length is
linear in `k`, so the outer integrand is linear.

**Cost:** reuses (a)'s first-moment axiom. Loop-free, so it exercises the
new integration without `HWhile`.

---

## Out of reach, and why

| Algorithm | Target | Blocker |
|---|---|---|
| Inversion, `X := F^-1(U)` | any | `F^-1` is not a polynomial for exp/normal |
| Box–Muller | Normal | needs `sqrt`, `log`, `cos` |
| Marsaglia polar | Normal | needs `sqrt`, `log`; and the section length `2*sqrt(1-k^2)` is not polynomial |
| von Neumann exponential | Exp(1) | carried continuous state + unbounded counter |
| Geometric by repeated Bernoulli | Geometric | unbounded counter, infinite region partition |
| Jöhnk's Beta | Beta(a,b) | needs `U^(1/a)`, i.e. roots |

### The one worth knowing about

von Neumann's 1951 paper gives an exponential sampler that uses **only
uniform draws and comparisons** — no transcendental function anywhere:

> Draw `U_0, U_1, U_2, ...` and find the first ascent, i.e. the least
> `k >= 1` with `U_(k-1) < U_k`. Given `U_0 = u`, that run has odd length
> with probability exactly `e^(-u)`. If odd, output `n + U_0`; otherwise
> increment `n` and restart.

`e` appears in the *answer*, never in the program. This is the exact
analogue of "Exponential from Laplace" but from uniforms, and it fails here
for two independent reasons: the run loop carries the previous `U` as
continuous state, so one-step transition probabilities are not constants and
`HWhile`'s body premise cannot be discharged; and `n` is unbounded, so there
is no finite region partition.

It is the cleanest motivating example for the **parametric `R(theta)`**
while rule — transitions depending measurably on retained continuous state,
solved pointwise and then integrated.

---

## References

Unverified; check before citing.

- **Devroye, L. (1986).** *Non-Uniform Random Variate Generation.* Springer.
  The standard monograph on exactly this question; freely available from the
  author. Early chapters cover inversion, rejection and composition; later
  ones go distribution by distribution.
- **von Neumann, J. (1951).** "Various techniques used in connection with
  random digits." In *Monte Carlo Method*, National Bureau of Standards
  Applied Mathematics Series 12. Source of both the rejection method and the
  comparison-only exponential sampler above.
- **Box, G. E. P. & Muller, M. E. (1958).** "A Note on the Generation of
  Random Normal Deviates." *Annals of Mathematical Statistics* 29(2).
- **Marsaglia, G. & Bray, T. A. (1964).** "A Convenient Method for
  Generating Normal Variables." *SIAM Review* 6(3).
- **Knuth, D. E.** *The Art of Computer Programming, Vol. 2: Seminumerical
  Algorithms*, section 3.4.1. Compact standard reference.

---

## Suggested order

1. **(c)** — zero axioms, loop-free, establishes `t^2` independently.
2. **(a)** — add the first moment; check it reproduces (c)'s constant.
3. **(d)** — reuses (a)'s axiom, no loop.
4. **(b)** — add the quadratic moment only if the family is wanted.
