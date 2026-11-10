module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Complement
public meta import Mathlib.Data.Fintype.Perm
public meta import Mathlib.Algebra.Group.End
public meta import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Transporting the Klein-four centralizer argument under conjugation

The abstract no-Klein-four dihedral endpoint is transported along an
inner automorphism to a conjugate splitting/nonsplitting torus.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open scoped Pointwise

public theorem isKleinFour_map_mulEquiv
    {G : Type u} [Group G] [Finite G]
    (V : Subgroup G) (hV : IsKleinFour V) (e : G ≃* G) :
    IsKleinFour (V.map e.toMonoidHom) := by
  let eV : V ≃* V.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective V e.toMonoidHom e.injective
  exact {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV.symm).trans hV.exponent_two
  }

public theorem isKleinFour_map_mulEquiv_cross
    {G H : Type*} [Group G] [Group H]
    (V : Subgroup G) (hV : IsKleinFour V) (e : G ≃* H) :
    IsKleinFour (V.map e.toMonoidHom) := by
  let eV : V ≃* V.map e.toMonoidHom :=
    Subgroup.equivMapOfInjective V e.toMonoidHom e.injective
  exact {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eV.symm).trans hV.exponent_two
  }

public theorem centralizer_map_le_of_conj
    {G : Type u} [Group G]
    (A V : Subgroup G) (g : G)
    (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    (V.map (MulAut.conj g⁻¹).toMonoidHom) ≤
      Subgroup.centralizer
        ((A.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rcases Subgroup.mem_map.mp hy with ⟨v, hv, hvy⟩
  rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, hqa⟩
  rw [← hvy, ← hqa]
  change (MulAut.conj g⁻¹) a0 * (MulAut.conj g⁻¹) v =
    (MulAut.conj g⁻¹) v * (MulAut.conj g⁻¹) a0
  have hvcomm : v * a0 = a0 * v :=
    ((Subgroup.mem_centralizer_iff.mp (hVleC hv)) a0 ha0).symm
  calc
    (MulAut.conj g⁻¹) a0 * (MulAut.conj g⁻¹) v =
        (MulAut.conj g⁻¹) (a0 * v) := by
          simp only [MulAut.conj_apply]
          group
    _ = (MulAut.conj g⁻¹) (v * a0) := by rw [hvcomm]
    _ = (MulAut.conj g⁻¹) v * (MulAut.conj g⁻¹) a0 := by
          simp only [MulAut.conj_apply]
          group

public theorem centralizer_map_le_of_mulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (A V : Subgroup G) (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    V.map e.toMonoidHom ≤
      Subgroup.centralizer ((A.map e.toMonoidHom : Subgroup H) : Set H) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  rcases Subgroup.mem_map.mp hy with ⟨v, hv, hvy⟩
  rcases Subgroup.mem_map.mp ha with ⟨a0, ha0, hqa⟩
  rw [← hvy, ← hqa]
  have hvcomm : a0 * v = v * a0 :=
    (Subgroup.mem_centralizer_iff.mp (hVleC hv)) a0 ha0
  simpa [e.map_mul] using congrArg e hvcomm

public theorem no_kleinFour_centralizes_odd_cyclic_of_conjugate_torus
    {G : Type u} [Group G] [Finite G]
    (A V : Subgroup G) (g : G) (U : Subgroup G) (w : G)
    (hAne : A ≠ ⊥)
    (hAodd : ∀ a : G, a ∈ A → Odd (orderOf a))
    (hAt : A ≤ U.map (MulAut.conj g).toMonoidHom)
    (hUcyc : IsCyclic U) (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hN : Subgroup.normalizer
      ((A.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) : Set G) =
        U ⊔ Subgroup.zpowers w)
    (hVK : IsKleinFour V) (hVleC : V ≤ Subgroup.centralizer (A : Set G)) :
    False := by
  let A0 : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom
  let V0 : Subgroup G := V.map (MulAut.conj g⁻¹).toMonoidHom
  let eA : A ≃* A0 :=
    Subgroup.equivMapOfInjective A (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective
  have hA0ne : A0 ≠ ⊥ := by
    intro hbot
    have hcardA : Nat.card A = Nat.card A0 := Nat.card_congr eA.toEquiv
    have hone : Nat.card A = 1 := by
      rw [hcardA, hbot]
      simp
    have hgt : 1 < Nat.card A :=
      (Subgroup.one_lt_card_iff_ne_bot A).mpr hAne
    omega
  have hA0rot : A0 ≤ U := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
    have haT : a ∈ U.map (MulAut.conj g).toMonoidHom := hAt ha
    rcases Subgroup.mem_map.mp haT with ⟨u, hu, hua⟩
    rw [← hua]
    simpa [MulAut.conj_apply, mul_assoc, inv_mul_cancel] using hu
  have hA0odd : ∀ x : G, x ∈ A0 → Odd (orderOf x) := by
    intro x hx
    obtain ⟨a, ha_eq⟩ := eA.surjective ⟨x, hx⟩
    have hax : (MulAut.conj g⁻¹) (a : G) = x :=
      congrArg Subtype.val ha_eq
    have hordA : Odd (orderOf (a : G)) := hAodd (a : G) a.2
    have hsc : SemiconjBy (g⁻¹) (a : G) x := by
      change g⁻¹ * (a : G) = x * g⁻¹
      rw [← hax]
      simp [MulAut.conj_apply, mul_assoc]
    have hord_eq : orderOf x = orderOf (a : G) :=
      (SemiconjBy.orderOf_eq (g⁻¹) (x := (a : G)) (y := x) hsc).symm
    simpa [hord_eq] using hordA
  have hV0K : IsKleinFour V0 :=
    isKleinFour_map_mulEquiv V hVK (MulAut.conj g⁻¹)
  have hV0leC : V0 ≤ Subgroup.centralizer (A0 : Set G) := by
    simpa [A0, V0] using centralizer_map_le_of_conj A V g hVleC
  exact no_kleinFour_centralizes_odd_rotation_of_normalizer
    U A0 V0 w hA0ne hA0rot hA0odd hUcyc hwU hwsq hwinv hN hV0K hV0leC


public theorem no_kleinFour_of_isPGroup_odd
    {G : Type u} [Group G] [Finite G]
    (V : Subgroup G) (hVK : IsKleinFour V)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hVp : IsPGroup p V) :
    False := by
  rcases hVp.exists_card_eq with ⟨n, hn⟩
  have h4 : Nat.card V = 4 := hVK.card_four
  rw [h4] at hn
  have hp_dvd4 : p ∣ 4 := by
    cases n with
    | zero => simp at hn
    | succ n =>
        exact ⟨p ^ n, by
          rw [hn, pow_succ, Nat.mul_comm]⟩
  have hp_le4 : p ≤ 4 := Nat.le_of_dvd (by norm_num) hp_dvd4
  have hp_ge2 : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
  interval_cases p <;> norm_num at *


/-- In a complement `N ⋊ C` with `p` coprime to `|C|`, a Klein four that
centralizes a nontrivial `p`-subgroup and lies inside the kernel `N` is
impossible. -/
public theorem no_kleinFour_of_pGroup_subgroup
    {M : Type u} [Group M] [Finite M]
    (N V : Subgroup M)
    {p : ℕ} [Fact p.Prime]
    (hNp : IsPGroup p N)
    (hpodd : Odd p)
    (hVleN : V ≤ N) (hVK : IsKleinFour V) :
    False := by
  let VN : Subgroup N := V.subgroupOf N
  have hVNp : IsPGroup p VN := hNp.to_subgroup VN
  have hVp : IsPGroup p V :=
    hVNp.of_equiv (Subgroup.subgroupOfEquivOfLe hVleN)
  exact no_kleinFour_of_isPGroup_odd V hVK hpodd hVp

public theorem no_kleinFour_subgroup_of_isCyclic
    {G : Type u} [Group G]
    (M V : Subgroup G) (hVK : IsKleinFour V) (hVM : V ≤ M)
    (hMcyc : IsCyclic M) :
    False := by
  let : IsCyclic M := hMcyc
  have hnot : ¬ IsCyclic (↥V) :=
    @IsKleinFour.not_isCyclic (↥V) _ hVK
  exact hnot (Subgroup.isCyclic_of_le hVM)

public theorem no_kleinFour_subgroup_of_dihedral_odd
    {G : Type u} [Group G] [Finite G]
    (M V : Subgroup G) (z : ℕ)
    (hVK : IsKleinFour V) (hVM : V ≤ M)
    (hMdihedral : Nonempty (M ≃* DihedralGroup z)) (hzodd : Odd z) :
    False := by
  have hMcard : Nat.card M = 2 * z := by
    have h := Nat.card_congr (hMdihedral.some.toEquiv)
    rw [DihedralGroup.nat_card] at h
    exact h
  have hdvd : Nat.card V ∣ Nat.card M := Subgroup.card_dvd_of_le hVM
  rw [hVK.card_four, hMcard] at hdvd
  rcases hzodd with ⟨k, hk⟩
  rw [hk] at hdvd
  omega


end CFSG.GorensteinWalter
