module

public import CFSG.Goldschmidt.Basic

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type*} [Group G]


theorem conjSub_centralizer_singleton (s t : G) :
    conjSub s (centralizer ({t} : Set G)) = centralizer ({s⁻¹ * t * s} : Set G) := by
  ext x
  rw [mem_conjSub, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc x * (s⁻¹ * t * s) = s⁻¹ * (s * x * s⁻¹ * t) * s := by group
      _ = s⁻¹ * (t * (s * x * s⁻¹)) * s := by rw [h]
      _ = s⁻¹ * t * s * x := by group
  · intro h
    calc s * x * s⁻¹ * t = s * (x * (s⁻¹ * t * s)) * s⁻¹ := by group
      _ = s * (s⁻¹ * t * s * x) * s⁻¹ := by rw [h]
      _ = t * (s * x * s⁻¹) := by group


theorem conjSub_inf (s : G) (A B : Subgroup G) :
    conjSub s (A ⊓ B) = conjSub s A ⊓ conjSub s B :=
  Subgroup.map_inf_eq _ _ _ (MulAut.conj s⁻¹).injective

theorem conjSub_sup (s : G) (A B : Subgroup G) :
    conjSub s (A ⊔ B) = conjSub s A ⊔ conjSub s B :=
  Subgroup.map_sup _ _ _

theorem conjSub_oddCoreOf (s : G) (H : Subgroup G) :
    conjSub s (oddCoreOf H) = oddCoreOf (conjSub s H) := by
  set φ : H ≃* (conjSub s H : Subgroup G) := H.equivMapOfInjective _ (MulAut.conj s⁻¹).injective
  have h1 : (goldschmidtOddCore H).map φ.toMonoidHom = goldschmidtOddCore (conjSub s H) := by
    rw [goldschmidtOddCore_eq_pPrimeCore, goldschmidtOddCore_eq_pPrimeCore]
    exact CFSG.pPrimeCore_map_iso 2 φ
  unfold oddCoreOf
  rw [← h1, Subgroup.map_map]
  unfold conjSub
  rw [Subgroup.map_map]
  rfl

end CFSG.Goldschmidt75
