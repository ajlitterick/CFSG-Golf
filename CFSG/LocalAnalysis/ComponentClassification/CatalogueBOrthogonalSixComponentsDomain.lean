module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsUnitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingIsometryComponents

public noncomputable section

namespace CFSG.ComponentClassification.CatalogueBOrthogonalSix

open Matrix CatalogueBOrthogonalFourNonsplit

universe u

variable {K : Type u} [Field K] [Finite K] (delta : K)

instance sixExtensionFinite : Finite (extension delta) :=
  Finite.of_equiv (K × K) (QuadraticAlgebra.equivProd delta 0).symm

instance sixSpecialUnitaryFinite : Finite (sixSpecialUnitary delta) :=
  Finite.of_injective (fun g : sixSpecialUnitary delta => g.val.val)
    (Units.val_injective.comp Subtype.val_injective)

instance sixIsometriesFinite : Finite (SixIsometries delta) := by
  apply Finite.of_injective
    (fun g : SixIsometries delta => (g.val : sixSubmodule delta → sixSubmodule delta))
  intro g h heq
  apply Subtype.ext
  apply LinearEquiv.ext
  intro X
  exact congrFun heq X


end CFSG.ComponentClassification.CatalogueBOrthogonalSix
