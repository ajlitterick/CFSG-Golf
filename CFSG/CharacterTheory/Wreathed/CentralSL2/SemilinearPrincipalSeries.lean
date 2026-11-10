module

public import CFSG.CharacterTheory.Wreathed.CentralSL2.SemilinearPrincipalSum

public section

open scoped BigOperators Classical ComplexOrder

namespace CFSG.Wreathed.CentralSL2

open Matrix CFSG.Wreathed.CyclicCentralSL2Extension
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.Wreathed.CentralSL2Abelianization
open TwoRankLowerBound.Helpers

section Small

variable {F : Type} [Field F] {b : Fˣ} {m : ℕ}
  {Sigma : Subgroup (F ≃+* F)} (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)

theorem mem_parameterStabilizer_iff' (P : PrincipalSeriesParameter F b m) (σ : Sigma) :
    σ ∈ parameterStabilizer hSigma P ↔
      P.1.1.comp (Units.map ((σ⁻¹ : Sigma) : F ≃+* F).toRingHom.toMonoidHom) = P.1.1 := by
  rw [mem_parameterStabilizer_iff]
  constructor
  · intro h
    exact congrArg (fun Q : PrincipalSeriesParameter F b m => Q.1.1) h
  · intro h
    apply Subtype.ext
    exact Prod.ext h rfl

theorem ringEquiv_eq_one_of_card_prime [Fintype F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (h : Fintype.card F = p) (σ : F ≃+* F) : σ = 1 := by
  have hbij := ZMod.castHom_bijective F h
  refine RingEquiv.ext fun x => ?_
  obtain ⟨a, rfl⟩ := hbij.2 x
  have h1 := RingHom.ext_zmod (σ.toRingHom.comp (ZMod.castHom (dvd_refl p) F))
    (ZMod.castHom (dvd_refl p) F)
  exact DFunLike.congr_fun h1 a


end Small


end CFSG.Wreathed.CentralSL2
