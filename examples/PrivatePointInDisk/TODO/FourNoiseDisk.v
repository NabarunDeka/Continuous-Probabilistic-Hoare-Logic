
  FourNoiseDisk.v -- OPEN PROBLEM.  The program and the triple that CPHL
  cannot currently prove.

  NO ROCQ CONTENT: this file is a single comment, and this directory is NOT
  in the Makefile's SUBDIRS, so nothing here is built.  That is deliberate --
  TODO/ is where an in-progress attempt can live without breaking `make`.

  Everything below is EXPRESSIBLE in CPHL.  The program is a well-formed
  [Cmd], the postcondition a well-formed [PFormula], and the weakest
  precondition a well-formed [PConstruct].  What is missing is the value of
  one integral.  See flags/FLAGS.md F14 and F15.

  ====================================================================
  THE PROGRAM
  ====================================================================

  Perturb the point AND the centre, each coordinate with its own
  independent Laplace draw, then test whether the perturbed point lies in
  the perturbed unit-radius disk.

  In CPHL notation, with [px py cx cy b : R] as Rocq parameters (so the
  coordinates are closed terms, exactly as in PointInDiskAdditive.v):

      Definition fn_noise (b : R) : Distribution := <{ laplace(0, b) }>.

      Definition fn_dx (px cx : R) : Term :=
        <{ ($(px) + fn_n1) + $(TConst (-1)) * ($(cx) + fn_n3) }>.
      Definition fn_dy (py cy : R) : Term :=
        <{ ($(py) + fn_n2) + $(TConst (-1)) * ($(cy) + fn_n4) }>.

      Definition fn_disk (px py cx cy : R) : CFormula :=
        <{ ($(fn_dx px cx) * $(fn_dx px cx))
           + ($(fn_dy py cy) * $(fn_dy py cy)) < 1 }>.

      Definition fn_prog (px py cx cy b : R) : Cmd :=
        <{ fn_n1 sample $(fn_noise b);
           fn_n3 sample $(fn_noise b);
           fn_n2 sample $(fn_noise b);
           fn_n4 sample $(fn_noise b);
           fn_inside b= $(fn_disk px py cx cy) }>.

  (The sample order pairs each coordinate's two noises adjacently, which is
  the order a future reduction would want.)

  ====================================================================
  THE TRIPLE WE CANNOT PROVE
  ====================================================================

      Theorem fn_correct :
        forall px py cx cy b : R,
          (0 < b)%R ->
          {{ Pr[true] = 1 }}
            $(fn_prog px py cx cy b)
          {{ Pr[fn_inside] = $(fn_P b (px - cx) (py - cy)) }}.

  where [fn_P] is the value described below.  Note the shape is identical to
  the triples that DO go through in this directory -- only the constant on
  the right is unavailable.

  ====================================================================
  THE VALUE
  ====================================================================

  Write dx = px - cx, dy = py - cy.  The event depends on the four noises
  only through the two differences W1 = n1 - n3 and W2 = n2 - n4, which are
  independent.  Each has the density (proved: LaplaceConvolution.v,
  [lc_convolution])

      g_b(w) = (1 / (4b)) * (1 + |w|/b) * exp(-|w|/b)

  with CDF (proved: OneDimensional/LaplaceCdfConvolution.v,
  [lcc_convolution_cdf])

      G_b(t) = (1/4) * (2 - t/b) * exp(t/b)         for t <= 0
      G_b(t) = 1 - (1/4) * (2 + t/b) * exp(-t/b)    for t >= 0.

  Hence, doing the inner integral over the disk section
  ( -sqrt(1-s^2), sqrt(1-s^2) ):

      fn_P(b, dx, dy)
        = INT_{-1}^{1}  g_b(s - dx)
                        * [ G_b( sqrt(1-s^2) - dy)
                          - G_b(-sqrt(1-s^2) - dy) ]  ds.            (* *)

  This is fully explicit -- finite range, elementary integrand, every
  ingredient in closed form.

  ====================================================================
  WHY IT IS STUCK -- TWO SEPARATE BLOCKERS
  ====================================================================

  (1) CPHL cannot get from the weakest precondition to (* *) at all.  The wp
      is four nested [QIntegral]s, and collapsing them to two requires
      Fubini plus translation invariance.  [real_integral]'s entire
      structural toolkit is extensionality, additivity, scaling and five
      closed forms -- no substitution, no Fubini, not even translation.
      That is flags/FLAGS.md F15, and the honest repair needs an
      integrability predicate first, since Fubini for a TOTAL integral is
      false as stated.

  (2) Even granted (1), (*) has no elementary closed form.  Substituting
      s = sin(th) turns the integrand into

          exp(+/- cos(th)/b) * exp(-|sin(th) - dx|/b) * (polys) * cos(th),

      whose core INT exp(a cos th) cos th d(th) is a modified Bessel
      integral (pi*I_1(a) over a full period) and, over the partial range
      needed here, an incomplete-Bessel / modified-Struve value.  So there
      is no missing lemma to find: fn_P is a Bessel-type transcendental in
      (b, dx, dy).

  Blocker (2) is why this must NOT be closed by adding an axiom.  Unlike
  [CPHL.real_integral_unit_square_quarter_disk], whose value is the single
  constant PI/4, an axiom here would be a three-parameter opaque constant --
  postulating the answer rather than supplying an analytic law.

  ====================================================================
  ACCEPTANCE TESTS FOR ANY FUTURE SOLUTION
  ====================================================================

  Values of (*) by quadrature, cross-checked against a direct four-noise
  Monte Carlo (4e6 samples, agreement within about 2e-4):

      dx     dy     b      fn_P from (*)   4-noise Monte Carlo
      ----   ----   ----   -------------   -------------------
      0.0    0.0    0.5       0.46980            0.46958
      0.0    0.0    1.0       0.16540            0.16547
      0.5    0.3    0.5       0.39856            0.39832
      1.2    0.0    0.5       0.22612            0.22578

  Note the last row: the true point is OUTSIDE the disk (dx = 1.2 > 1), yet
  the mechanism answers "inside" 22.6% of the time.  Any proposed closed
  form must reproduce that.

  ====================================================================
  WHAT WORKS INSTEAD
  ====================================================================

  Three nearby mechanisms are fully proved and can be used in its place:

    ../PointInDiskAdditive.v   2-D, noise on the scalar squared distance.
    ../PointInDiskInPlace.v    the same, perturb-in-place.
    ../OneDimensional/         1-D, BOTH perturbation styles -- including
                               OneDimPoints.v, which perturbs the two points
                               independently and DOES close, because in one
                               dimension the region is an interval rather
                               than a disk.

  That last file is the point: independent double perturbation is not what
  blocks this problem.  The disk is.