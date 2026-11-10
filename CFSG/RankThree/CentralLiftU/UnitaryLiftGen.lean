module

public import CFSG.RankThree.CentralLiftU.UnitaryLift

public section

namespace CFSG.RankThree.CentralLiftU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.CentralExt (sl2Lift comp_sl2Lift_of_exists)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (sl2Diag sl2W sl2ConjDiag
  coe_sl2Diag coe_sl2W coe_sl2ConjDiag sl2W_mul_sl2W sl2ConjDiag_inv_sl2W
  sl2ConjDiag_neg_one_sl2W)
open CFSG.RankThree.CentralLift.LinearRoots (swapSL sl2ConjDiag_sl2Diag swapSL_sl2Diag
  sl2ConjDiag_one)
open CFSG.LieType.Steinberg (perfectLift comp_perfectLift_of_exists)
open scoped Matrix

section Unique

variable {E G : Type*} [Group E] [Group G] {π : E →* G}


variable {H : Type*} [Group H]


end Unique

namespace Gen

variable {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) {r ε : ℕ}

structure LiftHyp {R : Type*} [Group R] (π : R →* hypSU h r ε) : Prop where
  sl2K : ∀ α : SpecialLinearGroup (Fin 2) K →* hypSU h r ε,
    ∃! β : SpecialLinearGroup (Fin 2) K →* R, π.comp β = α
  sl2F : ∀ α : SpecialLinearGroup (Fin 2) h.fixedField →* hypSU h r ε,
    ∃! β : SpecialLinearGroup (Fin 2) h.fixedField →* R, π.comp β = α
  su3 : ∀ α : gramSU h (gramJ3 K) →* hypSU h r ε,
    ∃! β : gramSU h (gramJ3 K) →* R, π.comp β = α

section Basic


end Basic

section Diag


end Diag

section Weyl


end Weyl


section Odd


end Odd

end Gen

end CFSG.RankThree.CentralLiftU
