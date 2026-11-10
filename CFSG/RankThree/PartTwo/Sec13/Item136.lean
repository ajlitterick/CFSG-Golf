module

public import CFSG.RankThree.PartTwo.Sec17.Item1729
public import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item136E
import CFSG.RankThree.PartTwo.Sec13.Naturality

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Assembly

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem case7_of_mem (h131 : Item131) (hspor : SporadicModels131) (h : Sec13Data G A c L)
    (hcL : c ∈ L) :
    (Sec4.IsSLThreePiTwo (lBarA c L A) ∨
        (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
          (Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
            Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
            Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L)
              CFSG.Blueprint.NativeSporadic.M22))) ∧
      (Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) →
          Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
      ∀ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) →
        CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
        ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) →
        ¬ IsCyclic (E ⊓ L : Subgroup G) →
          E ∈ partTwoF G ∧ (E ∉ partTwoT G →
            Sec4.IsHeisCentral (lBarA c L A) (L ⧸ aschbacherSolvableCore 3 L) ∧
            (∃ K ∈ thetaComponentsAt 3 c, A ≤ L ⊔ K ∧
              Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) (alternatingGroup (Fin 6))) ∧
            ∃ e ∈ E ⊓ L, e ∉ Subgroup.zpowers c ∧
              omegaA E = orbitIn A (Subgroup.zpowers e) ∧
              ∃ I : Subgroup G, lA E e = {I} ∧
                Nonempty (I ⧸ CFSG.pCore 2 I ≃* CFSG.Blueprint.NativeSporadic.J2)) := by
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
  rcases h131 G A c L h with ⟨hL3, -⟩ | ⟨hPGL, -, -⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ |
      ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩ | h7
  · exfalso
    obtain ⟨p, e, hp, he, hcase⟩ := hL3
    rcases hcase with ⟨hq, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
    · obtain ⟨hS, hZ⟩ := isPerfect_center_projSL p e he hq
      exact (facts_of_prod h hS hZ φ).1 hcL
    · by_cases hq2 : 2 < p ^ e
      · obtain ⟨hS, hZ⟩ := isPerfect_center_projSU p e he hq hq2
        exact (facts_of_prod h hS hZ φ).1 hcL
      · have h2 : p ^ e = 2 := by
          have : 2 ≤ p ^ e := le_trans hp.out.two_le (Nat.le_self_pow (by omega) _)
          omega
        obtain ⟨rfl, rfl⟩ := eq_two_one_of_pow_eq_two hp.out h2
        exact false_of_isSolvable h isSolvable_projSU_two φ
  · exfalso
    obtain ⟨π, p, f, K, _, hK, hq, ⟨φ⟩⟩ := hPGL
    by_cases hq2 : 2 < p ^ f
    · exact not_mem_of_center_inf_commutator h φ
        (by rw [center_projImage_glPi hK hq hq2, bot_inf_eq]) hcL
    · have h2 : p ^ f = 2 := by
        have hf : f ≠ 0 := by have := hK.one_le; omega
        have : 2 ≤ p ^ f := le_trans hK.prime.two_le (Nat.le_self_pow hf _)
        omega
      cases π
      · exact false_of_isSolvable h (isSolvable_projImage_glPi_two hK h2) φ
      · change p ^ f % 3 = 1 at hq
        omega
  · exact absurd hcL (facts_of_prod h isPerfect_center_alt7.1 isPerfect_center_alt7.2 φ).1
  · exact absurd hcL (facts_of_prod h hM22p hM22z φ).1
  · exact absurd hcL (facts_of_prod h hM12p hM12z φ).1
  · exact absurd hcL (facts_of_prod h hJ2p hJ2z φ).1
  · exact h7

theorem theta_eq_pCore_two {I : Type*} [Group I] [Finite I] {S : Type*} [Group S]
    (hS : IsSimpleGroup S) (hSp : Group.IsPerfect S) (φ : I ⧸ CFSG.pCore 2 I ≃* S) :
    aschbacherSolvableCore 3 I = CFSG.pCore 2 I := by
  have : (CFSG.pCore 2 I).Normal := CFSG.pCore_normal
  have hθ := solvable_prime_complement_core_characterization (H := I) Nat.prime_three
  apply le_antisymm
  · set f := QuotientGroup.mk' (CFSG.pCore 2 I) with hf
    set N := (aschbacherSolvableCore 3 I).map f with hN
    have : (aschbacherSolvableCore 3 I).Normal := by
      have := hθ.2.1
      infer_instance
    have hNn : N.Normal := Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
    have hθs := hθ.1
    have hNs : Group.IsSolvable N :=
      Group.isSolvable_of_surjective (f.subgroupMap_surjective (aschbacherSolvableCore 3 I))
    have hφN : (N.map φ.toMonoidHom).Normal := Subgroup.Normal.map hNn _ φ.surjective
    rcases hS.eq_bot_or_eq_top_of_normal (N.map φ.toMonoidHom) with hb | ht
    · have hN' : N = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hb
      intro x hx
      have h1 : f x ∈ N := Subgroup.mem_map_of_mem f hx
      rw [hN', Subgroup.mem_bot, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    · exfalso
      have h1 : Group.IsSolvable (N.map φ.toMonoidHom) :=
        Group.isSolvable_of_surjective (φ.toMonoidHom.subgroupMap_surjective N)
      rw [ht] at h1
      have : Group.IsSolvable S :=
        Group.isSolvable_of_surjective
          (f := ((Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S) : (⊤ : Subgroup S) →* S))
          Subgroup.topEquiv.surjective
      have : Nontrivial S := hS.toNontrivial
      exact Group.IsPerfect.not_isSolvable S inferInstance
  · exact hθ.2.2.2.2.2.2 2 Nat.prime_two (by norm_num)

theorem chosen136_of_forall_not_mem (h131 : Item131) (hspor : SporadicModels131)
    (hSLC : SLTwoCenter) (hD : Sec13Data G A c L)
    (hgood : ∀ c' : G, Subgroup.zpowers c' ∈ omegaA A → ∀ L' ∈ lA A c', c' ∉ L') :
    Chosen136 A := by
  refine ⟨hD.mem_partTwoF, fun c' hc' L' hL' => ?_⟩
  have hD' : Sec13Data G A c' L' :=
    { hD.toPartTwoStanding with
      partTwoS_eq := hD.partTwoS_eq, mem_partTwoF := hD.mem_partTwoF,
      not_mem_partTwoT := hD.not_mem_partTwoT, zpowers_mem_omegaA := hc', mem_lA := hL' }
  exact ⟨(facts_of_not_mem h131 hspor hSLC hD' (hgood c' hc' L' hL')).1,
    moreover_of_not_mem h131 hspor hSLC hD' (hgood c' hc' L' hL')⟩


end Assembly

end CFSG.RankThree.PartTwo.Sec13
