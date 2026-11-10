module

public import CFSG.GH74.GLS.IVK.Lifted.SL2KGroup
public import CFSG.Milestones.ASVolI.C5Blocks
public import CFSG.Quasithin.EmptyFaithful.SBc15WDefs

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC CFSG.Quasithin.S152N

noncomputable local instance burnsideC56_instFintypeW3 : Fintype W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

local instance burnsideC56_instDecEqW3 : DecidableEq W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

local instance burnsideC56_instDecN0 : DecidablePred (· ∈ W3.N0) := fun a =>
  inferInstanceAs (Decidable (a.right = 1 ∧ ∀ q, a.left q * a.left q * a.left q = 1))


end CFSG.ASVolI
