module

public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.CharacterTheory.Semidihedral.ProjectiveNonsquareInvolutions
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2KleinFourSelfCentralizer
public import CFSG.Foundations.Basic

public section

namespace CFSG.LinearGroups

noncomputable section

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.GorensteinWalter Matrix
open CFSG.Semidihedral.MatrixCoverData CFSG.Semidihedral.ProjectiveNonsquareInvolutions

universe u

variable {K : Type u} [Field K]


theorem coordinateGLAction_eq_one_iff [Finite K] (g : GL (Fin 2) K) :
    coordinateGLAction K g = 1 ↔ g ∈ Subgroup.center (GL (Fin 2) K) := by
  rw [← ProjGenLinGroup.mk_eq_one]
  exact map_eq_one_iff _ (coordinatePGLAction_injective K)

theorem coordinateGLAction_eq_iff [Finite K] {g h : GL (Fin 2) K} :
    coordinateGLAction K g = coordinateGLAction K h ↔
      ∃ u : Kˣ, g * GeneralLinearGroup.scalar (Fin 2) u = h := by
  rw [← ProjGenLinGroup.mk_eq_mk_iff]
  exact (coordinatePGLAction_injective K).eq_iff


theorem isKleinFour_of_card_eq_four {H : Type*} [Group H] (h4 : Nat.card H = 4)
    (hsq : ∀ x : H, x ^ 2 = 1) : IsKleinFour H := by
  refine ⟨h4, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton H := Monoid.exp_eq_one_iff.mp h
    have := Nat.card_of_subsingleton (1 : H)
    omega
  · exact h


theorem card_le_four_of_isElementaryAbelian
    [Finite K] (hK : IsOddPrimePower (Nat.card K))
    (E : Subgroup (coordinateD K)) [IsElementaryAbelian 2 E] : Nat.card E ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PGL2 K) := Finite.of_injective _ (pglEquivCoordinateD K).injective
  by_contra hlt
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (IsElementaryAbelian.isPGroup 2 E)
  have h4 : 2 ^ 2 ∣ Nat.card E := by
    rw [hn]
    refine pow_dvd_pow 2 ?_
    by_contra h
    rw [hn] at hlt
    interval_cases n <;> simp_all
  obtain ⟨W, hW⟩ := Sylow.exists_subgroup_card_pow_prime 2 h4
  let ψ : E →* PGL2 K := (pglEquivCoordinateD K).symm.toMonoidHom.comp E.subtype
  have hψ : Function.Injective ψ :=
    (pglEquivCoordinateD K).symm.injective.comp E.subtype_injective
  have hcard : Nat.card (W.map ψ) = 4 := by
    rw [Subgroup.card_map_of_injective hψ, hW]
    norm_num
  have hsq (x : W.map ψ) : x ^ 2 = 1 := by
    obtain ⟨w, -, hw⟩ := x.2
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hw, ← map_pow,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 E) w,
      map_one]
  have hC := pgl2_kleinFour_centralizer_eq_self K hK _ (isKleinFour_of_card_eq_four hcard hsq)
  have hle : ψ.range ≤ W.map ψ := by
    rw [← hC]
    rintro _ ⟨a, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨w, -, rfl⟩
    rw [← map_mul, ← map_mul, (inferInstance : IsMulCommutative E).is_comm.comm]
  have := Subgroup.card_le_of_le hle
  rw [hcard, ← Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv] at this
  omega

theorem isOddPrimePower_card_of_ringChar_ne_two [Finite K] (hK : ringChar K ≠ 2) :
    IsOddPrimePower (Nat.card K) := by
  have := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  exact ⟨ringChar K, n, hp, hp.odd_of_ne_two hK, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩


end

end CFSG.LinearGroups
