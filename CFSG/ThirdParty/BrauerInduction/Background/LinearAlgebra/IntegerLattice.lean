module

public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.RingTheory.Finiteness.Cofinite

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Local-to-global membership in integer lattices

This file proves an elementwise form of Bernstein's lattice lemma.

If `L` is a finitely generated `ℤ`-module, `A ≤ L`, and an element `x` is
congruent modulo `A` to a multiple of `p ^ N` for every prime `p` and every
`N`, then `x ∈ A`.

The proof passes to `L ⧸ A` and uses the structure theorem for finitely
generated abelian groups.
-/

universe u

namespace Int


end Int

namespace ZMod


end ZMod

namespace AddCommGroup


end AddCommGroup

namespace Submodule


end Submodule
