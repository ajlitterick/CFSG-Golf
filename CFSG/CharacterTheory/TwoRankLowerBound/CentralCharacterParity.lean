module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuaternionEightCentralizer

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem irreducible_central_element_is_scalar {G vector : Type*} [Group G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) [representation.IsIrreducible]
    (element : G) (hcentral : element ∈ Subgroup.center G) :
    ∃ scalar : ℂ, representation element = scalar • (1 : Module.End ℂ vector) := by
  let intertwiner : representation.IntertwiningMap representation :=
    { toLinearMap := representation element
      isIntertwining' := by
        intro member
        change representation element * representation member =
          representation member * representation element
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcentral member] }
  obtain ⟨scalar, hscalar⟩ :=
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 intertwiner
  refine ⟨scalar, ?_⟩
  have hequal := congrArg Representation.IntertwiningMap.toLinearMap hscalar
  rw [Representation.IntertwiningMap.algebraMap_apply,
    Representation.IntertwiningMap.toLinearMap_smul] at hequal
  have hone : (1 : representation.IntertwiningMap representation).toLinearMap =
      (1 : Module.End ℂ vector) := by
    ext member
    exact congrFun (Representation.IntertwiningMap.coe_one representation) member
  rw [hone] at hequal
  exact hequal.symm

theorem irreducible_central_involution_parity {G vector : Type*} [Group G]
    [AddCommGroup vector] [Module ℂ vector] [FiniteDimensional ℂ vector]
    (representation : Representation ℂ G vector) [representation.IsIrreducible]
    (involution : G) (hcentral : involution ∈ Subgroup.center G)
    (hsquare : involution ^ 2 = 1) :
    ∃ parity : ℂ, (parity = 1 ∨ parity = -1) ∧
      representation involution = parity • (1 : Module.End ℂ vector) ∧
      ∀ element : G, representation.character (element * involution) =
        parity * representation.character element := by
  obtain ⟨parity, hscalar⟩ := irreducible_central_element_is_scalar representation involution hcentral
  let : Nontrivial representation.asModule :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) representation.asModule
  let : Nontrivial vector := representation.asModuleEquiv.symm.toEquiv.nontrivial
  have hparitySquare : parity * parity = 1 := by
    apply smul_left_injective ℂ (show (1 : Module.End ℂ vector) ≠ 0 from one_ne_zero)
    calc
      (parity * parity) • (1 : Module.End ℂ vector) =
          representation involution * representation involution := by
        rw [hscalar, smul_mul_smul_comm, one_mul]
      _ = 1 := by rw [← map_mul, ← pow_two, hsquare, map_one]
      _ = (1 : ℂ) • (1 : Module.End ℂ vector) := (one_smul _ _).symm
  refine ⟨parity, mul_self_eq_one_iff.mp hparitySquare, hscalar, ?_⟩
  intro element
  change LinearMap.trace ℂ vector (representation (element * involution)) =
    parity * LinearMap.trace ℂ vector (representation element)
  rw [map_mul, hscalar, mul_smul_comm, mul_one, map_smul, smul_eq_mul]

theorem irreducible_character_central_involution_parity {G : Type*} [Group G]
    (data : FiniteComplexRepresentation G) (hirreducible : data.IsIrreducible)
    (involution : G) (hcentral : involution ∈ Subgroup.center G)
    (hsquare : involution ^ 2 = 1) :
    ∃ parity : ℂ, (parity = 1 ∨ parity = -1) ∧
      data.character involution = parity * data.character 1 ∧
      ∀ element : G, data.character (element * involution) = parity * data.character element := by
  let : data.representation.IsIrreducible := hirreducible
  obtain ⟨parity, hsign, _, hvalues⟩ :=
    irreducible_central_involution_parity data.representation involution hcentral hsquare
  exact ⟨parity, hsign, by simpa only [one_mul] using hvalues 1, hvalues⟩


end CFSG.TwoRankLowerBound.Helpers
