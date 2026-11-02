module

public import CFSG.RankThree.PartOne.KP.MSection
public import CFSG.Monster.SteinbergMY443NativeSurjective
public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Sporadic.Bridge.MonsterModels
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.KP.MReduction
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace CFSG.RankThree.PartOne

open CFSG.Open CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.Existence CFSG.YGroups.Y443

theorem simplePresentationMHasBSection_holds : SimplePresentationMHasBSection := by
  intro T _ _ _ _ ⟨e⟩
  have eM : T ≃* MonsterY443Derived :=
    e.trans CFSG.Blueprint.NativeSporadic.MonsterModel.y443DerivedEquivOpen
  have hsimple : IsSimpleGroup MonsterY443Derived := MulEquiv.isSimpleGroup eM.symm
  have hinj : Function.Injective fM := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fM.ker) with h | h
    · exact h
    · exact absurd h fM_ker_ne_top
  have hsurj : Function.Surjective fM :=
    ((y443_native_surjective_homomorphism).1 fM fM_isFM).1
  exact exists_section_of_equiv_of_le Gmat (eM.trans (MulEquiv.ofBijective fM ⟨hinj, hsurj⟩))
    Cgen Cgen_le_Gmat Zstar phiB

end CFSG.RankThree.PartOne
