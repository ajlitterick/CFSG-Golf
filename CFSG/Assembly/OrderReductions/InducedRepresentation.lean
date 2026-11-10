module

public import CFSG.Assembly.OrderReductions.TIClassFunctionInduction

public section

namespace CFSG.OrderReductions.InducedRepresentation

open CFSG.OrderReductions.TIClassFunctionInduction
open scoped Classical

@[expose] def rightTranslation {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] : Representation field group (group → vector) where
  toFun actor :=
    { toFun := fun function element => function (element * actor)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext function element
    simp
  map_mul' := by
    intro first second
    ext function element
    simp [mul_assoc]

@[expose] def leftTwist {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) :
    Representation field subgroup (group → vector) where
  toFun actor :=
    { toFun := fun function element => representation actor (function (actor.val⁻¹ * element))
      map_add' := by
        intro first second
        funext element
        exact map_add (representation actor) _ _
      map_smul' := by
        intro scalar function
        funext element
        exact map_smul (representation actor) _ _ }
  map_one' := by
    ext function element
    simp
  map_mul' := by
    intro first second
    ext function element
    simp [map_mul, mul_inv_rev, mul_assoc]

theorem translation_twist_commute {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) (actor : group) (local_actor : subgroup) :
    rightTranslation (field := field) (vector := vector) actor * leftTwist subgroup representation local_actor =
      leftTwist subgroup representation local_actor * rightTranslation actor := by
  ext function element
  change representation local_actor (function (local_actor.val⁻¹ * (element * actor))) =
    representation local_actor (function (local_actor.val⁻¹ * element * actor))
  congr 2
  exact (mul_assoc _ _ _).symm

theorem translation_preserves_invariants {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) (actor : group) :
    (leftTwist subgroup representation).invariants ≤
      (leftTwist subgroup representation).invariants.comap (rightTranslation actor) := by
  intro function invariant
  apply ((leftTwist subgroup representation).mem_invariants _).mpr
  intro local_actor
  have commutes := translation_twist_commute subgroup representation actor local_actor
  have applied := congrArg (fun operator => operator function) commutes
  simpa only [Module.End.mul_apply,
    ((leftTwist subgroup representation).mem_invariants _).mp invariant local_actor] using applied.symm

@[expose] noncomputable def induced {field group vector : Type*} [Field field] [Group group]
    [AddCommGroup vector] [Module field vector] (subgroup : Subgroup group)
    (representation : Representation field subgroup vector) :
    Representation field group (leftTwist subgroup representation).invariants :=
  rightTranslation.subrepresentation (leftTwist subgroup representation).invariants
    (translation_preserves_invariants subgroup representation)


end CFSG.OrderReductions.InducedRepresentation
