module

public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorFixedSets

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator

open CFSG.Open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

@[expose] def internalCentralizerEquiv (L : Subgroup G) (x : G) (hxL : x ∈ L) :
    (L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) ≃*
      Subgroup.centralizer ({(⟨x, hxL⟩ : L)} : Set L) where
  toFun y := ⟨⟨y, y.property.1⟩, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp y.property.2))⟩
  invFun y := ⟨(y : L), ⟨y.val.property, Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp y.property))⟩⟩
  left_inv y := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' y z := by ext; rfl

@[expose] def elementCentralizerEquiv {F : Type*} [Group F] (e : G ≃* F) (x : G) :
    Subgroup.centralizer ({x} : Set G) ≃* Subgroup.centralizer ({e x} : Set F) where
  toFun y := ⟨e y.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e
      (Subgroup.mem_centralizer_singleton_iff.mp y.property))⟩
  invFun y := ⟨e.symm y.val, Subgroup.mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul, e.symm_apply_apply] using congrArg e.symm
      (Subgroup.mem_centralizer_singleton_iff.mp y.property))⟩
  left_inv y := by ext; simp
  right_inv y := by ext; simp
  map_mul' y z := by ext; simp


variable [Finite G]

theorem odd_element_full_centralizer_odd (x : G) (hx : x ≠ 1)
    (hodd : Odd (orderOf x))
    (hCtwo : ∀ t : G, orderOf t = 2 → IsPGroup 2 (Subgroup.centralizer ({t} : Set G))) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := Subgroup.centralizer ({x} : Set G)) 2 (even_iff_two_dvd.mp heven)
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  let y : Subgroup.centralizer ({(t : G)} : Set G) :=
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp t.property).symm⟩
  have hyodd : Odd (orderOf y) := (Subgroup.orderOf_coe y).symm ▸ hodd
  have hcop := (hCtwo t htG).orderOf_coprime hyodd.coprime_two_left y
  have hyorder : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  exact hx (congrArg Subtype.val (orderOf_eq_one_iff.mp hyorder))

theorem pair_full_centralizer_eq (H : Subgroup G)
    (a b : pointRightCosetSpace H) (hab : a ≠ b) (L : Subgroup G)
    (hcomm : IsMulCommutative (L ⊓
      (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) : Subgroup G))
    (x : G) (hxW : x ∈ L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b))
    (hfix : elementFixedSet H x = {a, b})
    (hCodd : Odd (Nat.card (L ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G))) :
    L ⊓ Subgroup.centralizer ({x} : Set G) =
      L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b) := by
  let W := L ⊓ (rightCosetStabilizer H a ⊓ rightCosetStabilizer H b)
  let C := L ⊓ Subgroup.centralizer ({x} : Set G)
  have hCN : C ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    intro c hc
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    have hcx : Commute c x := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    have heq : (MulAut.conj c) x = x := by
      simp only [MulAut.conj_apply, hcx.eq, mul_inv_cancel_right]
    change Subgroup.zpowers ((MulAut.conj c) x) = Subgroup.zpowers x
    rw [heq]
  have hCD : C ≤ rightCosetStabilizer H a ⊓ rightCosetStabilizer H b :=
    odd_normalizer_fixes_pair H (Subgroup.zpowers x) C hCodd hCN a b hab
      ((pointFixedSet_zpowers_eq H x).trans hfix)
  apply le_antisymm
  · exact fun c hc => ⟨hc.1, hCD hc⟩
  · intro c hc
    refine ⟨hc.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val ((@IsMulCommutative.is_comm W _ hcomm).comm
      (⟨c, hc⟩ : W) (⟨x, hxW⟩ : W))


end CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator
