module

public import CFSG.Quasithin.Vol2.Ch11SecBNPCaseL
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.Quasithin.Background.C1PackS15212A
public import CFSG.Quasithin.Vol2.Ch11SecBNPCasesC
public import CFSG.Quasithin.Vol2.Ch11SecBNPLie
public import CFSG.Quasithin.Vol2.Ch11SecBTCStar

public section

namespace CFSG.Quasithin.E2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecB

namespace E22A

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem one_le_nParam {H T M : Subgroup Γ} (hmin : MinParabolic H T M) : 1 ≤ E1.nParam H := by
  have heven : ¬ Odd (Nat.card H) := by
    intro hodd
    have hT1 : T = ⊥ := E1.eq_bot_of_isSylowIn_odd
      ⟨hmin.isSylow.1, hmin.isSylow.2.1, hmin.isSylow.2.2⟩ hodd
    apply hmin.not_normal
    rw [hT1, show Subgroup.normalizer ((⊥ : Subgroup Γ) : Set Γ) = ⊤ from
      Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  unfold E1.nParam
  split_ifs
  exact le_iInf₂ fun i hi => by exact_mod_cast hi.1

theorem generalizedFitting_star {H T M K : Subgroup Γ} (hmin : MinParabolic H T M)
    (hKc : K ∈ cComp H) (hHK : H = K ⊔ T) (hTK : T ≤ Subgroup.normalizer (K : Set Γ))
    (hJs : Group.IsSolvable ↥(kerIn M H)) (hKs : IsSimpleGroup ↥(star M H K))
    (hnab : ∃ a b : ↥(star M H K), a * b ≠ b * a) :
    CFSG.generalizedFitting (StarQuot M H) = star M H K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (StarQuot M H) := E2P.finite_starQuot M H
  set π := QuotientGroup.mk' ((kerIn M H).subgroupOf H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hmin.isSylow.1
  have hT2 : IsPGroup 2 T := hmin.isSylow.2.1
  have hMH : M ≤ H := hmin.maximal.1.le
  have hns : ¬ Group.IsSolvable ↥H := fun hsol => not_isSolvable_of_mem_cComp hKc
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKH)
      (Subgroup.inclusion_injective hKH))
  have hRJ := solvRad_le_kerIn hmin.uniqueMax hT2 hns
  have hcomp := isComponent_star hMH hJs hRJ hKc
  have hHN : H ≤ Subgroup.normalizer (K : Set Γ) := hHK ▸ sup_le Subgroup.le_normalizer hTK
  have hKn : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHN
  have hKsn : (star M H K).Normal := hKn.map π hπs
  set Ts := (T.subgroupOf H).map π with hTs
  have hTs2 : IsPGroup 2 ↥Ts :=
    (hT2.comap_of_injective H.subtype H.subtype_injective).map π
  have hKT : star M H K ⊔ Ts = ⊤ := by
    have h1 : K.subgroupOf H ⊔ T.subgroupOf H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hKH hTH, ← hHK, Subgroup.subgroupOf_self]
    rw [star, hTs, ← Subgroup.map_sup, h1, Subgroup.map_top_of_surjective π hπs]
  set C := Subgroup.centralizer ((star M H K : Subgroup (StarQuot M H)) : Set (StarQuot M H))
    with hC
  have hZ : Subgroup.center ↥(star M H K) = ⊥ := center_eq_bot_of_nonabelian' hnab
  have hCK : ∀ c ∈ C, c ∈ star M H K → c = 1 := by
    intro c hc hcK
    have : (⟨c, hcK⟩ : ↥(star M H K)) ∈ Subgroup.center ↥(star M H K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hc) y y.2)
    rw [hZ, Subgroup.mem_bot] at this
    exact congrArg Subtype.val this
  have hC2 : IsPGroup 2 ↥C := by
    intro c
    obtain ⟨e, he⟩ := pow_mem_of_mem_sup_normal hTs2 (c : StarQuot M H)
      (hKT ▸ Subgroup.mem_top _)
    refine ⟨e, Subtype.ext ?_⟩
    simpa using hCK _ (C.pow_mem c.2 _) he
  have hCO : C ≤ CFSG.Open.pCore 2 (StarQuot M H) :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hC2
  have hO : CFSG.Open.pCore 2 (StarQuot M H) = ⊥ := by
    have h1 := (E2P.minParabolic_star hmin).pCore_le_kerIn
    rwa [E2P.kerIn_star, le_bot_iff] at h1
  have hCb : C = ⊥ := le_bot_iff.mp (hO ▸ hCO)
  exact generalizedFitting_eq_of_component _ hcomp hCb

end E22A


end CFSG.Quasithin.E2
