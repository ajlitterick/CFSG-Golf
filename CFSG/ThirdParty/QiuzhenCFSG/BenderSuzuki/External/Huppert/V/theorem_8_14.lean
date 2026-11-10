module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_6_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.ComplementTransfer
import CFSG.StronglyEmbedded.SteinbergBSPrimeFixedPointFreeNilpotent

namespace CFSG
end CFSG
open CFSG

/-!
# Thompson fixed-point-free nilpotence interfaces

This file records statement-only external theorem interfaces for Thompson's
fixed-point-free automorphism theorem as used in Peterfalvi, Part II, Chapter I.

Source guide: `docs/PFpart2/ref/PFpart2_external_formalization_guides.md`,
item `ThompsonFixedPointFreeNilpotence`; Huppert, *Endliche Gruppen I*,
V.8.14.
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

attribute [local instance] commutatorElement

universe u v

set_option maxHeartbeats 0


/--
Thompson's fixed-point-free automorphism theorem, in the prime-order form:
if a finite group admits a fixed-point-free automorphism of prime order, then
the group is nilpotent.
-/
public theorem thompson_prime_order_fixedPointFree_automorphism_nilpotent
    {Q : Type u} [Group Q] [Finite Q] (φ : MulAut Q)
    (hprime : Nat.Prime (orderOf φ))
    (hfixed : ∀ q : Q, φ q = q → q = 1) :
    Group.IsNilpotent Q :=
  CFSG.StronglyEmbedded.prime_order_fixed_point_free_automorphism_nilpotent φ hprime rfl hfixed

/--
The subgroup-of-automorphisms version used after extracting a prime-order
element from a nontrivial fixed-point-free automorphism group.
-/
public theorem thompson_fixedPointFree_automorphism_subgroup_nilpotent
    {Q : Type u} [Group Q] [Finite Q] (A : Subgroup (MulAut Q))
    (hA_nontrivial : ∃ φ : A, φ ≠ 1)
    (hfixed : ∀ φ : A, φ ≠ 1 → ∀ q : Q, (φ : MulAut Q) q = q → q = 1) :
    Group.IsNilpotent Q := by
  classical
  haveI : Finite A := inferInstance
  by_cases hcard : Nat.card A = 1
  · have hsub : Subsingleton A := (Nat.card_eq_one_iff_unique.mp hcard).1
    rcases hA_nontrivial with ⟨φ, hφ⟩
    exact False.elim (hφ (Subsingleton.elim φ 1))
  · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    obtain ⟨φ, hφorder⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpdvd
    have hφneA : φ ≠ 1 := by
      intro hφeq
      have hp_one : p = 1 := by
        simpa [hφeq] using hφorder.symm
      exact hp.ne_one hp_one
    have hφfixed : ∀ q : Q, (φ : MulAut Q) q = q → q = 1 := by
      intro q hq
      exact hfixed φ hφneA q hq
    have hprime : Nat.Prime (orderOf (φ : MulAut Q)) := by
      have horder : orderOf (φ : MulAut Q) = p := by
        simpa [Subgroup.orderOf_coe] using hφorder
      simpa [horder] using hp
    exact
      thompson_prime_order_fixedPointFree_automorphism_nilpotent
        (Q := Q) (φ := (φ : MulAut Q)) hprime hφfixed

/--
Peterfalvi-shaped conjugation version: a nontrivial subgroup `K` normalizes a
finite subgroup `Q`, and every nonidentity element of `K` centralizes only the
identity element of `Q`; hence `Q` is nilpotent.
-/
public theorem thompson_fixedPointFree_conjugation_nilpotent_subgroup
    {G : Type u} [Group G] [Finite G] (Q K : Subgroup G)
    (hK_norm_Q : K ≤ Subgroup.normalizer Q)
    (hK_nontrivial : ∃ x : G, x ∈ K ∧ x ≠ 1)
    (hfixed : ∀ x : G, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ Q = ⊥) :
    Group.IsNilpotent Q := by
  classical
  by_cases hQsub : Subsingleton Q
  · exact Group.isNilpotent_of_subsingleton
  let conjHom : K →* MulAut Q :=
    Q.normalizerMonoidHom.comp (Subgroup.inclusion hK_norm_Q)
  let A : Subgroup (MulAut Q) := Subgroup.map conjHom ⊤
  have hA_nontrivial : ∃ φ : A, φ ≠ 1 := by
    rcases hK_nontrivial with ⟨x, hxK, hxne⟩
    let xK : K := ⟨x, hxK⟩
    have hxconj_ne : conjHom xK ≠ 1 := by
      intro hxconj
      have hsub : Subsingleton Q := by
        refine ⟨fun q r => ?_⟩
        have h_eq_one : ∀ q : Q, q = 1 := by
          intro q
          have hcomm : x * (q : G) = (q : G) * x := by
            have hfixq : conjHom xK q = q := by
              simp [hxconj]
            have hcoe : (x : G) * (q : G) * x⁻¹ = (q : G) := by
              simpa [conjHom, xK] using congrArg (fun z : Q => (z : G)) hfixq
            calc
              x * (q : G) = (x * (q : G) * x⁻¹) * x := by simp [mul_assoc]
              _ = (q : G) * x := by rw [hcoe]
          have hmemCentral :
              (q : G) ∈ Subgroup.centralizer ({x} : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            rw [Set.mem_singleton_iff.mp hy]
            exact hcomm
          have hmemInf :
              (q : G) ∈ Subgroup.centralizer ({x} : Set G) ⊓ Q :=
            ⟨hmemCentral, q.2⟩
          have hbot : (q : G) ∈ (⊥ : Subgroup G) := by
            simpa [hfixed x hxK hxne] using hmemInf
          exact Subtype.ext (by simpa using hbot)
        exact (h_eq_one q).trans (h_eq_one r).symm
      exact hQsub hsub
    refine ⟨⟨conjHom xK, ?_⟩, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨xK, by simp, rfl⟩
    · intro hφ
      exact hxconj_ne (Subtype.ext_iff.mp hφ)
  have hA_fixed :
      ∀ φ : A, φ ≠ 1 → ∀ q : Q, (φ : MulAut Q) q = q → q = 1 := by
    intro φ hφne q hφq
    rcases Subgroup.mem_map.mp φ.2 with ⟨xK, _hxTop, hxφ⟩
    have hxne : (xK : G) ≠ 1 := by
      intro hxone
      have hφone_val : (φ : MulAut Q) = 1 := by
        rw [← hxφ]
        ext q
        simp [conjHom, hxone]
      exact hφne (Subtype.ext hφone_val)
    have hcomm : (xK : G) * (q : G) = (q : G) * (xK : G) := by
      have hfixq : conjHom xK q = q := by
        simpa [hxφ] using hφq
      have hcoe : (xK : G) * (q : G) * (xK : G)⁻¹ = (q : G) := by
        simpa [conjHom] using congrArg (fun z : Q => (z : G)) hfixq
      calc
        (xK : G) * (q : G) =
            ((xK : G) * (q : G) * (xK : G)⁻¹) * (xK : G) := by
          simp [mul_assoc]
        _ = (q : G) * (xK : G) := by rw [hcoe]
    have hmemCentral :
        (q : G) ∈ Subgroup.centralizer ({(xK : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hcomm
    have hmemInf :
        (q : G) ∈ Subgroup.centralizer ({(xK : G)} : Set G) ⊓ Q :=
      ⟨hmemCentral, q.2⟩
    have hbot : (q : G) ∈ (⊥ : Subgroup G) := by
      simpa [hfixed (xK : G) xK.2 hxne] using hmemInf
    exact Subtype.ext (by simpa using hbot)
  exact thompson_fixedPointFree_automorphism_subgroup_nilpotent A hA_nontrivial hA_fixed


/-- Huppert V.8.14, Peterfalvi/Suzuki-shaped conjugation interface. -/
public theorem huppert_V_8_14_thompson_fixedPointFree_conjugation_nilpotent_subgroup
    {G : Type u} [Group G] [Finite G] (Q K : Subgroup G)
    (hK_norm_Q : K ≤ Subgroup.normalizer Q)
    (hK_nontrivial : ∃ x : G, x ∈ K ∧ x ≠ 1)
    (hfixed : ∀ x : G, x ∈ K → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ Q = ⊥) :
    Group.IsNilpotent Q :=
  thompson_fixedPointFree_conjugation_nilpotent_subgroup
    (G := G) Q K hK_norm_Q hK_nontrivial hfixed

end External
end CFSG.BenderSuzuki
