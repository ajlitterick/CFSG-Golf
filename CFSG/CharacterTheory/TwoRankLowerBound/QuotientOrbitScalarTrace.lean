module

public import CFSG.CharacterTheory.TwoRankLowerBound.QuotientGroupAlgebraEndomorphisms
public import CFSG.CharacterTheory.TwoRankLowerBound.PeriodicSummandTrace

public section

open scoped BigOperators Classical

namespace CFSG.TwoRankLowerBound.Helpers

theorem groupAlgebra_quotient_scalarTower {ring source target : Type*} [CommRing ring]
    [Group source] [CommGroup target] (quotient : source →* target) :
    letI := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
    IsScalarTower ring (MonoidAlgebra ring source) (MonoidAlgebra ring target) := by
  let := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
  apply IsScalarTower.of_algebraMap_smul
  intro coefficient value
  change MonoidAlgebra.mapDomainRingHom ring quotient
    (algebraMap ring (MonoidAlgebra ring source) coefficient) * value = coefficient • value
  have hequal := congrArg (fun homomorphism : ring →+* MonoidAlgebra ring target => homomorphism coefficient)
    (MonoidAlgebra.mapDomainRingHom_comp_algebraMap (R := ring) (A := ring) quotient)
  change MonoidAlgebra.mapDomainRingHom ring quotient
    (algebraMap ring (MonoidAlgebra ring source) coefficient) =
      algebraMap ring (MonoidAlgebra ring target) coefficient at hequal
  rw [hequal, Algebra.smul_def]

theorem quotientGroupAlgebra_nonidentity_scalar_trace {ring source target : Type*}
    [CommRing ring] [Group source] [CommGroup target] [Finite target]
    (quotient : source →* target) (element : source) (hnonidentity : quotient element ≠ 1) :
    letI := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
    letI := groupAlgebra_quotient_scalarTower (ring := ring) quotient
    LinearMap.trace ring (MonoidAlgebra ring target)
      (scalarActionEndomorphism ring (MonoidAlgebra.single element 1 : MonoidAlgebra ring source)) = 0 := by
  let := Module.compHom (MonoidAlgebra ring target) (MonoidAlgebra.mapDomainRingHom ring quotient)
  let := groupAlgebra_quotient_scalarTower (ring := ring) quotient
  have hoperator : scalarActionEndomorphism ring
      (MonoidAlgebra.single element 1 : MonoidAlgebra ring source) =
      Algebra.lmul ring (MonoidAlgebra ring target) (MonoidAlgebra.single (quotient element) 1) := by
    apply LinearMap.ext
    intro value
    change MonoidAlgebra.mapDomainRingHom ring quotient (MonoidAlgebra.single element 1) * value = _
    simp only [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
    rfl
  rw [hoperator]
  exact groupAlgebra_nonidentity_translation_trace _ hnonidentity


end CFSG.TwoRankLowerBound.Helpers
