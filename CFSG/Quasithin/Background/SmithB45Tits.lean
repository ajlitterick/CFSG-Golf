module

public import CFSG.Quasithin.Background.SmithB45F4
public import CFSG.Quasithin.Background.SmithB45TorTits
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

open B42Tits CFSG.Sporadic.Schreier.Tits in
theorem asB45Tits_holds :
    AsB45No2FFor B42TypeTits := by
  refine B45Tor.asB45No2FFor_of_classTests fun V _ _ hV L hq hirr hX => ?_
  obtain ⟨e⟩ := titsModelEquiv (↥L ⧸ Subgroup.center ↥L) 2 1 hX
  have hZL : Subgroup.center ↥L = ⊥ := by
    have : Group.IsPerfect ↥L := hq.1
    have : Finite (MulAut V) := B42Disp.finite_mulAut
    obtain ⟨K, _, _, _, hK, ⟨e'⟩⟩ := CFSG.SectionRank.exists_mulEquiv_titsGroup_of_model hX
    set π := e'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L)) with hπ
    have hker : π.ker = Subgroup.center ↥L := by
      ext l
      simp only [MonoidHom.mem_ker, hπ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
    have h0 := CFSG.SectionRank.Tits_perfect_odd_cover_trivial (K := K) hK π
      (e'.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le
      (by rw [hker]; exact B45Disp.odd_card_center_of_isIrrSec hV hirr)
    rwa [hker] at h0
  exact ⟨hZL, titsD, inferInstance, e, _, _, _, _,
    B45Tor.classTests_titsD (fun v => by rw [← pow_two]; exact hV v) L hZL e⟩

theorem asB45ReeF4_holds :
    AsB45ReeF4 :=
  AsB45No2FFor.or asB45ReeF4Large_holds asB45Tits_holds

end CFSG.Quasithin
