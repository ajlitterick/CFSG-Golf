module

public import CFSG.LocalAnalysis.LargeEvenClassification.BinaryRank
public import CFSG.LocalAnalysis.LargeEvenClassification.AbelianIrreducible
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LargeEvenClassification.Helpers

universe fieldUniverse groupUniverse spaceUniverse

@[expose] noncomputable def groupAlgebraModuleAction {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type groupUniverse} [Group Acting] (Space : Type spaceUniverse)
    [AddCommGroup Space] [Module ScalarField Space]
    [Module (MonoidAlgebra ScalarField Acting) Space]
    [IsScalarTower ScalarField (MonoidAlgebra ScalarField Acting) Space] :
    Acting →* (Space ≃ₗ[ScalarField] Space) where
  toFun element :=
    { toFun := fun vector => (MonoidAlgebra.of ScalarField Acting) element • vector
      invFun := fun vector => (MonoidAlgebra.of ScalarField Acting) element⁻¹ • vector
      left_inv := by
        intro vector
        dsimp only
        rw [smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      right_inv := by
        intro vector
        dsimp only
        rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
      map_add' := smul_add _
      map_smul' := by
        intro scalar vector
        exact smul_comm _ _ _ }
  map_one' := by
    ext vector
    change (MonoidAlgebra.of ScalarField Acting) 1 • vector = vector
    rw [map_one, one_smul]
  map_mul' := by
    intro first second
    ext vector
    change (MonoidAlgebra.of ScalarField Acting) (first * second) • vector =
      (MonoidAlgebra.of ScalarField Acting) first •
        (MonoidAlgebra.of ScalarField Acting) second • vector
    rw [map_mul, mul_smul]

theorem simple_groupAlgebra_action_cyclic {ScalarField : Type fieldUniverse} [Field ScalarField]
    {Acting : Type groupUniverse} [CommGroup Acting] [Finite Acting]
    (Space : Type spaceUniverse) [AddCommGroup Space] [Module ScalarField Space]
    [Module (MonoidAlgebra ScalarField Acting) Space]
    [IsScalarTower ScalarField (MonoidAlgebra ScalarField Acting) Space]
    [IsSimpleModule (MonoidAlgebra ScalarField Acting) Space] :
    IsCyclic (groupAlgebraModuleAction (ScalarField := ScalarField) (Acting := Acting) Space).range := by
  let annihilator := Module.annihilator (MonoidAlgebra ScalarField Acting) Space
  let : annihilator.IsMaximal := IsSimpleModule.annihilator_isMaximal
    (R := MonoidAlgebra ScalarField Acting) (M := Space)
  let : Field ((MonoidAlgebra ScalarField Acting) ⧸ annihilator) := Ideal.Quotient.field annihilator
  let scalarAction := ((Ideal.Quotient.mk annihilator).toMonoidHom.comp
    (MonoidAlgebra.of ScalarField Acting)).toHomUnits
  let action := groupAlgebraModuleAction (ScalarField := ScalarField) (Acting := Acting) Space
  have hkernel : scalarAction.ker = action.ker := by
    rw [MonoidHom.ker_toHomUnits]
    ext element
    change Ideal.Quotient.mk annihilator ((MonoidAlgebra.of ScalarField Acting) element) = 1 ↔
      action element = 1
    rw [← map_one (Ideal.Quotient.mk annihilator), Ideal.Quotient.eq, Module.mem_annihilator]
    constructor
    · intro hzero
      ext vector
      change (MonoidAlgebra.of ScalarField Acting) element • vector = vector
      exact sub_eq_zero.mp (by simpa only [sub_smul, one_smul] using hzero vector)
    · intro hzero vector
      have hfixed := congrArg (fun automorphism : Space ≃ₗ[ScalarField] Space =>
        automorphism vector) hzero
      change (MonoidAlgebra.of ScalarField Acting) element • vector = vector at hfixed
      simpa only [sub_smul, one_smul] using sub_eq_zero.mpr hfixed
  let equivalence := QuotientGroup.quotientMulEquivOfEq hkernel.symm
  let embedding := ((Units.coeHom ((MonoidAlgebra ScalarField Acting) ⧸ annihilator)).comp
    (QuotientGroup.kerLift scalarAction)).comp equivalence.toMonoidHom
  have hinjective : Function.Injective embedding :=
    Units.val_injective.comp
      ((QuotientGroup.kerLift_injective scalarAction).comp equivalence.injective)
  let : IsCyclic (Acting ⧸ action.ker) := isCyclic_of_injective_ringHom embedding hinjective
  exact isCyclic_of_surjective (QuotientGroup.quotientKerEquivRange action).toMonoidHom
    (QuotientGroup.quotientKerEquivRange action).surjective


theorem cyclic_action_card_dvd_exponent {Acting : Type groupUniverse} [Group Acting]
    {Target : Type spaceUniverse} [Group Target] (action : Acting →* Target)
    [IsCyclic action.range] {exponent : ℕ} (hexponent : ∀ element : Acting, element ^ exponent = 1) :
    Nat.card action.range ∣ exponent := by
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro element
  obtain ⟨source, hsource⟩ := element.property
  apply Subtype.ext
  change (element : Target) ^ exponent = 1
  rw [← hsource, ← map_pow, hexponent source, map_one]


end CFSG.LargeEvenClassification.Helpers
