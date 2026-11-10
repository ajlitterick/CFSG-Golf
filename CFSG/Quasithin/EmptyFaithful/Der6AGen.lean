module

public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Der6A

variable {G : Type} [Group G]

theorem oTwoUpper_le_of_normal_sup [Finite G] {H N S : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hS : IsPGroup 2 S) (hSH : S ≤ H) (hH : H ≤ N ⊔ S) :
    oTwoUpper H ≤ N := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hsup : N.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNH hSH]
    exact Subgroup.subgroupOf_eq_top.mpr hH
  have hx' : (⟨x, hx⟩ : ↥H) ∈ N.subgroupOf H ⊔ S.subgroupOf H := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, s, hs, hns⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨k, hk⟩ := hS' ⟨s, hs⟩
  refine ⟨k, ?_⟩
  have hs1 : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) = QuotientGroup.mk s := by
    rw [← hns, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have h2 : (QuotientGroup.mk ((⟨x, hx⟩ : ↥H) ^ 2 ^ k) : ↥H ⧸ N.subgroupOf H) = 1 := by
    rw [QuotientGroup.mk_pow, h1, ← QuotientGroup.mk_pow, hs1, QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff] at h2
  simpa using Subgroup.mem_subgroupOf.mp h2


variable {X : Subgroup G}

noncomputable def piS3 (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) : ↥X →* Equiv.Perm (Fin 3) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))

theorem piS3_surjective (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    Function.Surjective (piS3 e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piS3_eq_one_iff (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {x : G} (hx : x ∈ X) :
    piS3 e ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 X := by
  have h1 : piS3 e ⟨x, hx⟩ = 1 ↔ (QuotientGroup.mk (⟨x, hx⟩ : ↥X) : OTwoQuot X) = 1 :=
    e.map_eq_one_iff
  rw [h1, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy

theorem piS3_sq_eq_one (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {a : G} (ha : a ∈ X)
    (ha2 : a ^ 2 = 1) : piS3 e ⟨a, ha⟩ * piS3 e ⟨a, ha⟩ = 1 := by
  rw [← map_mul]
  have : (⟨a, ha⟩ : ↥X) * ⟨a, ha⟩ = 1 := Subtype.ext (by simpa [pow_two] using ha2)
  rw [this, map_one]


end Der6A

end CFSG.Quasithin
