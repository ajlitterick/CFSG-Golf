module


public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Character.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.SimpleDecomposition

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Spans of irreducible characters

This file proves that characters of finite-dimensional representations are
integer linear combinations of characters of simple representations.

Under the hypothesis that the order of the finite group is nonzero in the
coefficient field, Maschke's theorem decomposes every representation as a
finite biproduct of simple representations. Taking characters gives the
corresponding decomposition into a finite sum of irreducible characters.
Consequently, every virtual character lies in their `ℤ`-linear span.
-/

universe u v

namespace CFSG.ClassFun

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

variable {k : Type u} {G : Type u}
variable [Field k] [Group G]

/--
The character of a finite-dimensional representation is a finite sum of
characters of simple representations.
-/
theorem char_eq_sum_simples
    [Finite G] [NeZero (Nat.card G : k)]
    (V : FDRep k G) :
    ∃ (ι : Type) (S : ι → FDRep k G)
      (_ : Fintype ι) (_ : ∀ i, Simple (S i)),
      ClassFun.character V =
        ∑ i : ι, ClassFun.character (S i) := by

  obtain ⟨ι, S, hι, hSimple, ⟨e⟩⟩ :=
    FDRep.exists_simple_decomposition V

  letI : Fintype ι := hι

  refine ⟨ι, S, inferInstance, hSimple, ?_⟩

  calc
    ClassFun.character V
        = ClassFun.character (Limits.biproduct S) :=
          ClassFun.char_eq_of_iso e
    _ = ∑ i : ι, ClassFun.character (S i) :=
          ClassFun.char_biproduct S

/--
The set of characters of simple finite-dimensional representations of `G`
over `k`.
-/
@[expose] def irreducibleCharacterSet
    (k : Type u) [Field k]
    (G : Type v) [Group G] :
    Set (ClassFun k G) :=
  { ψ : ClassFun k G |
    ∃ (S : FDRep k G)
      (_ : Simple S),
      ψ = ClassFun.character S }


end CFSG.ClassFun
