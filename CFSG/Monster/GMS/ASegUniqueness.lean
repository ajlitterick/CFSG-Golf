module

public import CFSG.Monster.GMS.ASegSimple
public import CFSG.Monster.GMS.ASegConnH87
public import CFSG.Monster.GMS.ASegTwoA
public import CFSG.Monster.GMS.CoTwoAutMain
public import CFSG.Monster.GMS.InterfacesOf
public import CFSG.Sporadic.Co1.Cover.Final
public import CFSG.Monster.GMS.BabyReduce

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic CFSG.Monster.B.Recog

structure ASegLiterature : Prop where
  tableV : TableVStatement
  tableIII : BabyTableIII
  tableIV : BabyTableIV
  threeSwap : BabyThreeSwap
  twoBabyUnique : TwoBabyUnique
  twoAAutInner : BabyTwoAAutInner

theorem ASegLiterature.interfaces
    {d₀ : B} (L : ASegLiterature) (hS : SLSStatement d₀)
    (G : Type) [Group G] [Finite G] : GMSInterfaces d₀ G :=
  .of_babyFacts hS L.tableV.inG L.tableIII L.tableIV L.threeSwap

theorem nonempty_mulEquiv_of_aseg_simple
    {G G' : Type} [Group G] [Group G'] [Finite G]
    [Finite G'] {d₀ d₀' : B} (L : ASegLiterature) (hS : SLSStatement d₀)
    (hS' : SLSStatement d₀') {a z₀ : G} {a' z₀' : G'} (hG : GMSF1Type d₀ a z₀)
    (hG' : GMSF1Type d₀' a' z₀') (hΓ' : Triangulable (twoAGraph a'))
    (hsimple : IsSimpleGroup G') : Nonempty (G ≃* G') := by
  have I : GMSInterfaces d₀ G := L.interfaces hS G
  have I' : GMSInterfaces d₀' G' := L.interfaces hS' G'
  exact nonempty_mulEquiv_of_triangulable_simple I I' hG hG' L.twoBabyUnique
    CFSG.Sporadic.Co1.Cover.co1DoubleCoverTwoB
    (twoAGraph_preconnected I hG) (twoAGraph_preconnected I' hG') hΓ' hsimple
    (kAutRigid_of_twoA I hG (centInvAutInnerTwoA_of_baby I hG L.twoAAutInner))
    (centInvAutInnerTwoAB_of I hG)

end CFSG.Monster.GMS
