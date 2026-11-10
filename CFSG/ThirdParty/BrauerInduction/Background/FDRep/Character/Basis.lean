module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.SimpleDecomposition
public import CFSG.ThirdParty.BrauerInduction.Background.Fintype.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

universe u v w

namespace FDRep

variable {k : Type u} {G : Type u}
variable [Field k] [Group G]


/--
A family of finite-dimensional representations containing exactly one
representative of every simple isomorphism class.
-/
structure IsCompleteSetOfSimples
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    {ι : Type*}
    (S : ι → FDRep k G) : Prop where
  is_simple : ∀ i, CategoryTheory.Simple (S i)
  is_distinct : ∀ i j, Nonempty (S i ≅ S j) → i = j
  is_exhaustive :
    ∀ T : FDRep k G,
      CategoryTheory.Simple T → ∃ i, Nonempty (T ≅ S i)

namespace IsCompleteSetOfSimples

/-- Distinct members of a complete set of simples are not isomorphic. -/
lemma isEmpty_iso_of_ne
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    {ι : Type*}
    {S : ι → FDRep k G}
    (hS : FDRep.IsCompleteSetOfSimples S)
    {i j : ι}
    (hij : i ≠ j) :
    IsEmpty (S i ≅ S j) := by
  refine ⟨?_⟩
  intro e
  exact hij (hS.is_distinct i j ⟨e⟩)


end IsCompleteSetOfSimples

end FDRep
