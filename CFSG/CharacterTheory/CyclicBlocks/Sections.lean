module

public import CFSG.CharacterTheory.CyclicBlocks.Fusion
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientRegular
public import CFSG.CharacterTheory.Semidihedral.Principal.FourierSupport

public section

open scoped BigOperators Classical

namespace CFSG.CyclicBlocks

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes CFSG.Semidihedral.Principal

variable {G : Type*} [Group G]

theorem mem_of_coprime_orderOf_of_isPGroup_quotient {H : Type*} [Group H] {p : ℕ}
    (R : Subgroup H) [R.Normal] (hquot : IsPGroup p (H ⧸ R)) {y : H}
    (hy : Nat.Coprime p (orderOf y)) : y ∈ R := by
  rw [← QuotientGroup.eq_one_iff]
  obtain ⟨k, hk⟩ := hquot (QuotientGroup.mk y)
  have h1 := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (QuotientGroup.mk (s := R) y) ∣ orderOf y :=
    orderOf_map_dvd (QuotientGroup.mk' R) y
  have hcop : Nat.Coprime (p ^ k) (orderOf y) := hy.pow_left k
  exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hcop).eq_one_of_dvd h2)


variable [Fintype G]


section Sections

variable (basis : FiniteIrreducibleCharacterBasis G) (ideal : Ideal ComplexAlgebraicIntegers)
  [ideal.IsMaximal] (p : ℕ) [Fact p.Prime] [CharP (ComplexAlgebraicIntegers ⧸ ideal) p]

theorem principal_section_constant (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) {u : G}
    (hPu : (P : Subgroup G) = Subgroup.zpowers u)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {x : G} (hx : x ∈ Subgroup.zpowers u) (hx1 : x ≠ 1) {y : G} (hxy : Commute x y)
    (hy : ¬ p ∣ orderOf y) {θ : basis.index}
    (hθ : θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal) :
    (basis.representation θ).character (x * y) = (basis.representation θ).character x := by
  have hp : p.Prime := Fact.out
  have hxord : orderOf x ∣ p ^ (Nat.card G).factorization p :=
    (orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_sylow_eq_zpowers P hPu)
  obtain ⟨R, hR, hcop, hquot⟩ := exists_normal_complement_centralizer hp2 P hPu hindex hx hx1
  have hyC : y ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    CFSG.LyonsUnitaryFour.mem_centralizer_zpowers_of_commute hxy
  have hyR : (⟨y, hyC⟩ : Subgroup.centralizer (Subgroup.zpowers x : Set G)) ∈ R := by
    apply mem_of_coprime_orderOf_of_isPGroup_quotient R hquot
    rw [Subgroup.orderOf_mk]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hy
  exact principal_character_section_constant_of_normal_complement basis ideal p principal
    hprincipal hxord R hcop hquot hθ hyR

theorem principal_column_norm (hp2 : p ≠ 2) (principal : basis.index)
    (hprincipal : (basis.representation principal).character = 1) (P : Sylow p G) {u : G}
    (hPu : (P : Subgroup G) = Subgroup.zpowers u)
    (hindex : (Subgroup.centralizer (Subgroup.zpowers u : Set G)).relIndex
      (Subgroup.normalizer (Subgroup.zpowers u : Set G)) = 2)
    {x : G} (hx : x ∈ Subgroup.zpowers u) (hx1 : x ≠ 1) :
    ∑ θ ∈ coefficientBlock basis (localizedComplexIntegerRing ideal) principal,
        (basis.representation θ).character x *
          starRingEnd ℂ ((basis.representation θ).character x) = Nat.card P := by
  have hxord : orderOf x ∣ p ^ (Nat.card G).factorization p :=
    (orderOf_dvd_of_mem_zpowers hx).trans (orderOf_dvd_of_sylow_eq_zpowers P hPu)
  obtain ⟨R, hR, hcop, hquot⟩ := exists_normal_complement_centralizer hp2 P hPu hindex hx hx1
  obtain ⟨localBasis⟩ := finiteIrreducibleCharacterBasis_exists
    (G := Subgroup.centralizer (Subgroup.zpowers x : Set G))
  obtain ⟨localPrincipal, hlocalPrincipal⟩ := finiteIrreducibleCharacterBasis_contains_irreducible
    localBasis (principalFiniteComplexRepresentation _)
    (principalFiniteComplexRepresentation_isIrreducible _)
  rw [principalFiniteComplexRepresentation_character] at hlocalPrincipal
  obtain ⟨hcolumn, hdegrees, hsylow⟩ :=
    principal_primary_column_centralizer_norm_of_normal_complement basis ideal p principal
      hprincipal x _ hxord localBasis localPrincipal hlocalPrincipal R hcop hquot
  have hle : (P : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
    hPu ▸ zpowers_le_centralizer_zpowers hx
  rw [hcolumn, hdegrees, hsylow (P.subtype hle), Sylow.coe_subtype,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]


end Sections

end CFSG.CyclicBlocks
