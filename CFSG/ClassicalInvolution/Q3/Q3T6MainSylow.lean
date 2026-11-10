module

public import CFSG.ClassicalInvolution.Q3.Q3T6MainData
public import CFSG.ClassicalInvolution.Q3.Q3T6LinMember
public import CFSG.ClassicalInvolution.AschTight.S1916CSR

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T6

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups

section Basic


variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


namespace TightStd3

theorem isUniqueInvolution (ht : TightStd3 K z) : IsUniqueInvolution K z :=
  ht.member.isUniqueInvolution (MemberType.cert_sl2 3 1)

theorem le_centralizer (ht : TightStd3 K z) : K ≤ Subgroup.centralizer ({z} : Set G) :=
  isSubnormal_le ht.member.subnormal

theorem centralizer_le_normalizer (ht : TightStd3 K z) :
    Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
  ht.normEq.ge

theorem centralizer_le_normalizer_member (ht : TightStd3 K z) {J : Subgroup G}
    (hJ : J ∈ CoreAssembly.conjClass K) {u : G} (hu : IsUniqueInvolution J u) :
    Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (J : Set G) := by
  obtain ⟨a, rfl⟩ := hJ
  have hu' : a * z * a⁻¹ = u := (ht.isUniqueInvolution.conj a).eq hu
  intro v hv
  have hv' : v * u = u * v := Subgroup.mem_centralizer_singleton_iff.mp hv
  have hva : a⁻¹ * v * a ∈ Subgroup.normalizer (K : Set G) := by
    rw [ht.normEq, Subgroup.mem_centralizer_singleton_iff]
    calc a⁻¹ * v * a * z = a⁻¹ * (v * (a * z * a⁻¹)) * a := by group
      _ = a⁻¹ * (v * u) * a := by rw [hu']
      _ = a⁻¹ * (u * v) * a := by rw [hv']
      _ = a⁻¹ * ((a * z * a⁻¹) * v) * a := by rw [hu']
      _ = z * (a⁻¹ * v * a) := by group
  rw [mem_normalizer_iff_conjSub_eq, ← conjSub_mul, show v * a = a * (a⁻¹ * v * a) by group,
    conjSub_mul, conjSub_eq_of_mem_normalizer hva]


end TightStd3

namespace TightStd3

theorem natCard_rSet (ht : TightStd3 K z) {R : Subgroup G}
    (hR : R ∈ RSet (CoreAssembly.conjClass K)) : Nat.card R = 8 := by
  obtain ⟨J, hJ, P, rfl⟩ := hR
  obtain ⟨g, rfl⟩ := hJ
  have hJm : Q3.IsClassicalMember3 (conjSub g K) (g * z * g⁻¹) :=
    (ht.member.conj g).toQ3 (by norm_num)
  obtain ⟨e⟩ := quaternion_sylow_of_isClassicalMember3 hJm P
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), Nat.card_congr e.toEquiv,
    Nat.card_eq_fintype_card, QuaternionGroup.card]

end TightStd3

namespace Sec19Data3

variable {S : Sylow 2 G} {W : Subgroup G} (hd : Sec19Data3 K z S W)
include hd

theorem hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K : Set G) :=
  hd.hSz.trans hd.tight.centralizer_le_normalizer

theorem isSylow2In_inf : IsSylow2In ((S : Subgroup G) ⊓ K) K :=
  S1916.isSylow2In_inf S hd.hSz hd.tight.le_centralizer hd.tight.centralizer_le_normalizer

theorem inf_mem_rSet : (S : Subgroup G) ⊓ K ∈ RSet (CoreAssembly.conjClass K) :=
  mem_RSet_of_isSylow2In (CoreAssembly.mem_conjClass_self K) hd.isSylow2In_inf


theorem mem_S : z ∈ (S : Subgroup G) := by
  have hzK := hd.tight.isUniqueInvolution
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    isPGroup_zpowers_of_mul_self_eq_one hzK.sq hzK.ne_one
  have hSN' : (S : Subgroup G) ≤ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) :=
    fun s hs => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun y hy => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
        exact ((Commute.zpow_left
          (Subgroup.mem_centralizer_singleton_iff.mp (hd.hSz hs)).symm k).eq))
  have h2 : IsPGroup 2 ↥((S : Subgroup G) ⊔ Subgroup.zpowers z) :=
    S.isPGroup'.to_sup_of_normal_right' hz2 hSN'
  have h3 := S.is_maximal' h2 le_sup_left
  exact h3 ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z)

theorem mem_inf : z ∈ (S : Subgroup G) ⊓ K := ⟨hd.mem_S, hd.tight.isUniqueInvolution.mem⟩


end Sec19Data3

namespace Sec19DataT3

variable {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}
  (hd : Sec19DataT3 K z S W L t V)
include hd


theorem htS : t ∈ (S : Subgroup G) := hd.hWS (hd.leW hd.memT)


theorem htN : t ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) := by
  have hN := hd.hSN hd.htS
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro y
  simp only [Subgroup.mem_inf]
  rw [hN y]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hd.htS h1)
      ((S : Subgroup G).inv_mem hd.htS), h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem ((S : Subgroup G).inv_mem hd.htS) h1)
      hd.htS
    simpa [mul_assoc] using this


end Sec19DataT3

end Basic

end CFSG.ClassicalInvolution.Q3.Q3T6
