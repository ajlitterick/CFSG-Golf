module

public import CFSG.LocalAnalysis.UniquenessCase.UCKQSDispatch
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureFinal
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LieType.Chevalley.EvenDiagramRootParameters
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.Monster.Existence.Census.FusionGens
public import CFSG.Monster.Existence.Compat.Main
public import CFSG.Monster.Existence.EbCase2
public import CFSG.Monster.Existence.EbFrame
public import CFSG.Monster.Existence.StdOdd.Cert.Base
public import CFSG.Monster.Existence.StdOdd.Cert.SylowThreeExt
public import CFSG.Monster.Existence.StdOdd.Defs
public import CFSG.Monster.Existence.TwoPoint.Fi23ConjBase
public import CFSG.Monster.Existence.TwoPoint.Fi23MiscBase
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels0Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels1Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels2Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels3Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels4Base
public import CFSG.Monster.Existence.TwoPoint.Fi23Rels5Base
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongADBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongJBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongMBase
public import CFSG.Monster.Existence.TwoPoint.Fi23RelsLongPBase
public import CFSG.Monster.Existence.TwoPoint.LeechMG
public import CFSG.Monster.Existence.TwoPoint.LeechShape
public import CFSG.Monster.GMS.CoTwoMain
public import CFSG.Monster.GMS.CoTwoModule
public import CFSG.Monster.GMS.CoTwoPerfectGen
public import CFSG.Monster.GMS.EdgeSqFact
public import CFSG.Monster.GMS.F1Basic
public import CFSG.Monster.GMS.NotConj
public import CFSG.Monster.GMS.S365CentDefs
public import CFSG.Monster.GMS.S365CentPathSpec
public import CFSG.Monster.GMS.S365CentRootSpec
public import CFSG.Monster.GMS.U6OddSylow
public import CFSG.Monster.Tri.LeechCover
public import CFSG.Monster.Tri.LeechModelTrace
public import CFSG.Sporadic.Co1.Module.CoTwoNortonData
public import CFSG.Sporadic.Co1.Module.TwoB
public import CFSG.Sporadic.Co1.Module.U6OddForest
public import CFSG.Sporadic.Co1.Module.U6OddProg
public import CFSG.Sporadic.Co1.Module.U6OddTuple
public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import Certificates.Data.CFSGNative.Chevalley.C2E6CertLie

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup CFSG.ABGLocalTools
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)

theorem kqs_centralizer_top_eq_bot {J : Type} [Group J] [IsSimpleGroup J] (hnab : ∃ a b : J, a * b ≠ b * a) :
    Subgroup.centralizer ((⊤ : Subgroup J) : Set J) = ⊥ := by
  rw [Subgroup.coe_top, Subgroup.centralizer_univ]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have hb : b ∈ Subgroup.center J := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

section Abelian

theorem kqs_of_abelian : ∀ (J : Type) [Group J] [Finite J], IsSimpleGroup J → CFSG.Open.IsKGroup J →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ T : Subgroup J, IsSylowOf p T ⊤ →
    IsMulCommutative T → ∀ Z : Subgroup J, Z ≤ T → Nat.card Z = p → IsWeaklyClosedIn Z T → IsCyclic T := by
  intro J _ _ hs hK p hp h5 T hT hab Z hZT hZ hWC
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨-, hTp, hTi⟩ := (isSylowOf_iff (p := p)).1 hT
  rw [Subgroup.relIndex_top_right] at hTi
  by_cases hrk : CFSG.Open.pRank p T ≤ 1
  · exact PCentralAbelianAt.pca_isCyclic_of_pRank_le_one hp2 hTp hrk
  · exfalso
    by_cases hc : ∀ a b : J, a * b = b * a
    ·
      letI : CommGroup J := { (inferInstance : Group J) with mul_comm := hc }
      have hprime : (Nat.card J).Prime := IsSimpleGroup.prime_card
      obtain ⟨E, -, -, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt T
      have hdvd : p ^ CFSG.Open.pRank p T ∣ Nat.card J := hEc ▸ Subgroup.card_subgroup_dvd_card E
      have h2 : p ^ 2 ∣ Nat.card J := (pow_dvd_pow p (by omega)).trans hdvd
      rcases (Nat.dvd_prime hprime).1 h2 with h | h
      · have : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      · have hpq : p ∣ Nat.card J := (dvd_pow_self p two_ne_zero).trans h2
        rcases (Nat.dvd_prime hprime).1 hpq with h' | h'
        · exact hp.one_lt.ne' h'
        · have h3 : p ^ 2 = p := h.trans h'.symm
          have h4 : p * p = p * 1 := by rw [← pow_two, h3, mul_one]
          exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hp.pos h4)
    · push Not at hc
      haveI hsT : IsSimpleGroup ↥(⊤ : Subgroup J) :=
        (Subgroup.topEquiv (G := J)).isSimpleGroup_congr.mpr hs
      have hcT : ∃ a b : ↥(⊤ : Subgroup J), a * b ≠ b * a := by
        obtain ⟨a, b, hab'⟩ := hc
        exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩, fun h => hab' (congrArg Subtype.val h)⟩
      have hcat : CFSG.Open.IsCatalogGroup ↥(⊤ : Subgroup J) :=
        hK.isCatalogGroup_of_surjective ⊤ hcT (MonoidHom.id _) Function.surjective_id
      have h2 : 2 ≤ CFSG.Open.pRank p T := by omega
      have hpT : p ∣ Nat.card T := by
        obtain ⟨E, hET, -, hEc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt T
        have : p ∣ Nat.card E := hEc ▸ dvd_pow_self p (by omega)
        exact this.trans (Subgroup.card_dvd_of_le hET)
      have hpJ : p ∣ Nat.card ↥(⊤ : Subgroup J) := by
        rw [Subgroup.card_top]
        exact hpT.trans (Subgroup.card_subgroup_dvd_card T)
      obtain ⟨g, hg1, hg2⟩ :=
        CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.kFactWeakClosure_holds
          p hp hp2 J ⊤ inferInstance hsT hcT hcat (kqs_centralizer_top_eq_bot hc) hpJ (hTp.toSylow hTi)
          (top_sup_eq _) (by rw [IsPGroup.toSylow_coe]; exact hab)
          (by rw [IsPGroup.toSylow_coe, inf_top_eq]; exact h2) Z (by rw [IsPGroup.toSylow_coe]; exact hZT) hZ
      rw [IsPGroup.toSylow_coe] at hg1
      have := hWC g⁻¹ (by unfold CFSG.conjugate; rw [inv_inv]; exact hg1)
      unfold CFSG.conjugate at this
      rw [inv_inv] at this
      exact hg2 this

theorem kqs_of_pca (h : PCentralAbelian) : UCK.KQS := by
  intro J _ _ hs hK p hp h5 T hT hcen hrk Z hZT hZ hWC
  haveI : Fact p.Prime := ⟨hp⟩
  refine kqs_of_abelian J hs hK p hp h5 T hT ?_ Z hZT hZ hWC
  by_cases hc : ∀ a b : J, a * b = b * a
  · rw [isMulCommutative_iff]
    exact fun a b => Subtype.ext (hc a b)
  push Not at hc
  by_cases hpJ : p ∣ Nat.card J
  · haveI hsT : IsSimpleGroup ↥(⊤ : Subgroup J) :=
      (Subgroup.topEquiv (G := J)).isSimpleGroup_congr.mpr hs
    have hcT : ∃ a b : ↥(⊤ : Subgroup J), a * b ≠ b * a := by
      obtain ⟨a, b, hab'⟩ := hc
      exact ⟨⟨a, Subgroup.mem_top a⟩, ⟨b, Subgroup.mem_top b⟩, fun h => hab' (congrArg Subtype.val h)⟩
    have hcat : CFSG.Open.IsCatalogGroup ↥(⊤ : Subgroup J) :=
      hK.isCatalogGroup_of_surjective ⊤ hcT (MonoidHom.id _) Function.surjective_id
    have hpT : p ∣ Nat.card ↥(⊤ : Subgroup J) := by rwa [Subgroup.card_top]
    exact PCentralAbelianAt.of_mulEquiv (Subgroup.topEquiv (G := J)).symm
      (h _ hsT hcT hcat p hp h5 hpT) T hT hcen hrk
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT.isPGroup
    have hk0 : k = 0 := by
      by_contra hk0
      exact hpJ ((dvd_pow_self p hk0).trans (hk ▸ Subgroup.card_subgroup_dvd_card T))
    have h1 : Nat.card T = 1 := by rw [hk, hk0, pow_zero]
    haveI := (Nat.card_eq_one_iff_unique.mp h1).1
    rw [isMulCommutative_iff]
    exact fun a b => Subsingleton.elim _ _

end Abelian

end CFSG.LocalAnalysis.UniquenessCase.UCK
