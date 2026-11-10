module

public import CFSG.Quasithin.Background.SmithB45MatM12
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case0M12Rep

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
  CFSG.Quasithin.Vol2.Ch10.SecA.C10P01 CFSG.Quasithin.B45Mat.M12 CFSG.Quasithin.B45Mat Matrix
  CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds


abbrev Q12 : Type :=
  ↥(G6.coreMod 12) ⧸ (Subgroup.zpowers (G6.allOnes 12)).subgroupOf (G6.coreMod 12)

structure NativeCoords {V : Type*} [CommGroup V] (L : Subgroup (MulAut V)) where
  π : ↥CFSG.Blueprint.NativeSporadic.M12 →* ↥L
  ψ : V ≃* Q12
  surj : Function.Surjective π
  equivariant : ∀ (γ : ↥CFSG.Blueprint.NativeSporadic.M12) (v : V) (m : ↥(G6.coreMod 12)),
    ψ v = QuotientGroup.mk m →
      ψ ((π γ : MulAut V) v) =
        QuotientGroup.mk (G6.coreAct 12 (γ : Equiv.Perm (Fin 12)) m)

section Bridge


end Bridge

end CFSG.Quasithin.AppendixH.H11
