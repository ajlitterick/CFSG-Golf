module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.HallSubgroups.Conjugacy
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem normal_subgroup_conjugate_map_subtype (M : Subgroup G) [M.Normal]
    (D : Subgroup M) (g : G) :
    (D.map (MulAut.conjNormal g).toMonoidHom).map M.subtype =
      (D.map M.subtype).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1


theorem hall_normalizer_intersection_odd (Q R D : Subgroup G)
    (hcontain : ∀ x ∈ Q, orderOf x = 2 → x ∈ R)
    (hdisjoint : Disjoint R (Subgroup.normalizer (D : Set G))) :
    Odd (Nat.card (Q ⊓ Subgroup.normalizer (D : Set G) : Subgroup G)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  let N := Subgroup.normalizer (D : Set G)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Q ⊓ N)) 2 heven.two_dvd
  have hxG : orderOf (x : G) = 2 := (Subgroup.orderOf_coe x).trans hx
  have hxR : (x : G) ∈ R := hcontain x x.property.1 hxG
  have hxone : (x : G) = 1 :=
    Subgroup.disjoint_def.mp hdisjoint hxR x.property.2
  have hxone' : x = 1 := Subtype.ext hxone
  rw [hxone', orderOf_one] at hx
  norm_num at hx


end CFSG.ComponentClassification.AschbacherTightEmbedding
