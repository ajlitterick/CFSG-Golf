module

public import CFSG.LocalAnalysis.LargeEvenClassification.DeepAutomorphisms
public import CFSG.LocalAnalysis.LargeEvenClassification.RankTwoResidualMap

public section

namespace CFSG.LargeEvenClassification.Helpers

universe sourceUniverse targetUniverse

@[expose] def addEndCoordinateTransport {Source : Type sourceUniverse} {Target : Type targetUniverse}
    [AddCommGroup Source] [AddCommGroup Target] (coordinates : Source ≃+ Target) :
    AddMonoid.End Source ≃+* AddMonoid.End Target where
  toFun := fun operator => (AddMonoid.End.equiv Target).symm
    (coordinates.toAddMonoidHom.comp ((AddMonoid.End.equiv Source operator).comp
      coordinates.symm.toAddMonoidHom))
  invFun := fun operator => (AddMonoid.End.equiv Source).symm
    (coordinates.symm.toAddMonoidHom.comp ((AddMonoid.End.equiv Target operator).comp
      coordinates.toAddMonoidHom))
  left_inv := by
    intro operator
    apply AddMonoid.End.ext
    intro element
    change coordinates.symm (coordinates (operator (coordinates.symm (coordinates element)))) = _
    rw [coordinates.symm_apply_apply, coordinates.symm_apply_apply]
  right_inv := by
    intro operator
    apply AddMonoid.End.ext
    intro element
    change coordinates (coordinates.symm (operator (coordinates (coordinates.symm element)))) = _
    rw [coordinates.apply_symm_apply, coordinates.apply_symm_apply]
  map_add' := by
    intro first second
    apply AddMonoid.End.ext
    intro element
    exact map_add coordinates _ _
  map_mul' := by
    intro first second
    apply AddMonoid.End.ext
    intro element
    change coordinates (first (second (coordinates.symm element))) =
      coordinates (first (coordinates.symm (coordinates (second (coordinates.symm element)))))
    rw [coordinates.symm_apply_apply]


theorem addEndCoordinateTransport_principal_iff {Source : Type sourceUniverse}
    {Target : Type targetUniverse} [AddCommGroup Source] [AddCommGroup Target]
    (coordinates : Source ≃+ Target) (unit : (AddMonoid.End Source)ˣ) :
    Units.map (addEndCoordinateTransport coordinates).toMonoidHom unit ∈
      principalFourSubgroup (AddMonoid.End Target) ↔
        unit ∈ principalFourSubgroup (AddMonoid.End Source) := by
  let transport := addEndCoordinateTransport coordinates
  change (∃ operator : AddMonoid.End Target, transport unit.val = 1 + 4 * operator) ↔
    ∃ operator : AddMonoid.End Source, unit.val = 1 + 4 * operator
  constructor
  · rintro ⟨operator, hoperator⟩
    refine ⟨transport.symm operator, ?_⟩
    have heq := congrArg transport.symm hoperator
    simpa only [transport.symm_apply_apply, map_add, map_one, map_mul, map_ofNat] using heq
  · rintro ⟨operator, hoperator⟩
    refine ⟨transport operator, ?_⟩
    rw [hoperator, map_add, map_one, map_mul, map_ofNat]


section Action

variable {Abelian : Type sourceUniverse} [CommGroup Abelian]


end Action

end CFSG.LargeEvenClassification.Helpers
