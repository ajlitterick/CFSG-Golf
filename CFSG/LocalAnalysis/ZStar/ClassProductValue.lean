module

public import CFSG.LocalAnalysis.ZStar.ClassSums

public section

namespace CFSG

namespace ZStar.ClassProductValue

open ZStar.ClassSums

noncomputable section

universe u v w

variable {G : Type u} [Group G] [Fintype G]

local instance : DecidableEq G := Classical.decEq G

@[expose] noncomputable def coefficientAugmentation (R : Type v) [CommSemiring R] :
    MonoidAlgebra R G →ₐ[R] R :=
  (MonoidAlgebra.lift R R G) (1 : G →* R)

@[simp]
theorem coefficientAugmentation_single (R : Type v) [CommSemiring R]
    (g : G) (r : R) :
    coefficientAugmentation (G := G) R (MonoidAlgebra.single g r) = r := by
  simp [coefficientAugmentation]

@[simp]
theorem coefficientAugmentation_classSum (R : Type v) [CommSemiring R]
    (C : ConjClasses G) :
    coefficientAugmentation (G := G) R (classSum R C) = (classSize C : R) := by
  simp [classSum, classSize]

theorem sum_structureConstant_mul_classSize (C D : ConjClasses G) :
    (∑ E : ConjClasses G, structureConstant C D E * classSize E) =
      classSize C * classSize D := by
  have h := congrArg (coefficientAugmentation (G := G) ℕ) (classSum_mul ℕ C D)
  simpa [map_mul, map_sum, map_smul, nsmul_eq_mul] using h.symm

section Character


end Character

end

end ZStar.ClassProductValue

end CFSG
