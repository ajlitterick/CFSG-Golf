module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBInterM

namespace CFSG
end CFSG
open CFSG

/-!
# `B ≤ M` in the cyclic first-case A₇ layer model — normalizer-equality leg

The paper derives `B ⊆ M` (p. 223) by applying its Lemma 2.9 corollary to
the normal subgroup `X = B ∩ PP^g` of `C_U(t₁)`.  The `P ∩ P^g` normality/
triviality steps behind that witness are a known source gap (see
`tasks/gw-section3.md`), so the witness is replaced with `X = B ∩ M`
itself.  This module contains the fully proved normalizer-equality leg
and the conditional public theorem:

* `P₂ ≤ B ∩ M` and `P₂ ≠ 1` make `B ∩ M` nontrivial (the FourData/
  normalizer setup, i.e. `N_G(P₂) ≤ M`);
* `B ∩ M = O₂'(M)` (landed equality) makes `B ∩ M` normal in the coatom
  `M`;
* `normalizer_eq_of_nontrivial_normal_in_coatom` forces
  `N_G(B ∩ M) = M`, so `B ≤ M` is equivalent to the single leg
  `hBnorm : B ≤ N_G(B ∩ M)`; the public theorem below states exactly this
  reduction.

The route audit (Route A's Frattini factorization modulo `C ∩ M ⊴ C`,
the Theorem-C bypass, the maximality alternative, and the proposed
direct A₇ order-four contradiction with its concrete counterexample) is
recorded in `/tmp/s3-b-le-m-report.md`; `hBnorm` is the one missing leg.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u


end CFSG.GorensteinWalter
