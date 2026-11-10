module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.BorelQuotient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneTorus
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneParab
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCardPar
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.LiftedSchreierData
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCtx
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.LeviTransport
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.Monster.AxisCount.HSIdentBaby
public import CFSG.Monster.AxisCount.HSIdentRec0
public import CFSG.Monster.AxisCount.HSIdentRec1
public import CFSG.Monster.AxisCount.HSIdentRec2
public import CFSG.Monster.AxisCount.HSIdentRec3
public import CFSG.Monster.AxisCount.HSIdentRec4
public import CFSG.Monster.AxisCount.HSIdentRec5
public import CFSG.Monster.AxisCount.HSIdentRec6
public import CFSG.Monster.AxisCount.HSIdentRec7
public import CFSG.Monster.AxisCount.HSIdentSmall
public import CFSG.Open.SplitBNPair
public import CFSG.Quasithin.H13.StatementsL1
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch10StatementsInputs
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.PartTwo.Late.Item2010
public import CFSG.RankThree.PartTwo.Sec11.Data
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item143N
public import CFSG.RankThree.PartTwo.Sec15.Item157
public import CFSG.RankThree.PartTwo.Sec16.Item163ProofR
public import CFSG.RankThree.PartTwo.Sec16.Item164Proof
public import CFSG.RankThree.PartTwo.Sec16.Item169HJ
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail22
public import CFSG.RankThree.PartTwo.Sec17.Item1724Two
public import CFSG.RankThree.PartTwo.Sec17.Item17TailSteps
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
public import CFSG.RankThree.PartTwo.Sec20.Item20ResProofCases
public import CFSG.RankThree.PartTwo.Sec20.Step204RestProof
public import CFSG.RankThree.PartTwo.Sec20.Step2051Proof
public import CFSG.RankThree.PartTwo.Sec20.Step2051SylowProof
public import CFSG.RankThree.PartTwo.Sec20.Step2053Proof
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec6.Statements
public import CFSG.RankThree.PartTwo.Toolkit.M12Local
public import CFSG.RankThree.S4Free.SuzukiEight
public import CFSG.Sporadic.Bridge.Catalogue
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.RuLOdd
public import CFSG.Sporadic.Schreier.RuZClass
public import CFSG.YGroups.DCE.B433Check
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {K G : Type} [Group K] [Finite K] [Group G] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* G} {M : ℕ}

theorem degree_eq_one_iff_of_path {m : ℕ} (hm : 2 ≤ m) {A : Matrix (Fin m) (Fin m) ℤ}
    (hA : TauCeti.IsFiniteType A)
    (hpath : ∀ i j : Fin m, i ≠ j → (A i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val))
    (i : Fin m) :
    (TauCeti.diagramGraph A).degree i = 1 ↔ i.val = 0 ∨ i.val + 1 = m := by
  have hmem : ∀ x : Fin m, x ∈ (TauCeti.diagramGraph A).neighborFinset i ↔
      i.val + 1 = x.val ∨ x.val + 1 = i.val := by
    intro x
    rw [SimpleGraph.mem_neighborFinset, hA.diagramGraph_adj_iff]
    constructor
    · rintro ⟨hne, h0⟩
      exact (hpath i x hne).1 h0
    · intro h
      have hne : i ≠ x := by
        rintro rfl
        omega
      exact ⟨hne, (hpath i x hne).2 h⟩
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hi : i.val < m := i.isLt
  constructor
  · intro hcard
    by_contra h
    rw [not_or] at h
    obtain ⟨h0, hlast⟩ := h
    have hx : (⟨i.val - 1, by omega⟩ : Fin m) ∈ (TauCeti.diagramGraph A).neighborFinset i := by
      rw [hmem]
      exact Or.inr (by dsimp only; omega)
    have hy : (⟨i.val + 1, by omega⟩ : Fin m) ∈ (TauCeti.diagramGraph A).neighborFinset i := by
      rw [hmem]
      exact Or.inl rfl
    have hne : (⟨i.val - 1, by omega⟩ : Fin m) ≠ ⟨i.val + 1, by omega⟩ := by
      intro heq
      have hval := congrArg Fin.val heq
      dsimp only at hval
      omega
    have := Finset.one_lt_card.2 ⟨_, hx, _, hy, hne⟩
    omega
  · rintro (h0 | hlast)
    · have hsingle : (TauCeti.diagramGraph A).neighborFinset i = {⟨1, by omega⟩} := by
        ext x
        rw [hmem, Finset.mem_singleton]
        constructor
        · rintro (h1 | h1)
          · refine Fin.ext ?_
            dsimp only
            omega
          · exfalso
            omega
        · rintro rfl
          exact Or.inl (by dsimp only; omega)
      rw [hsingle, Finset.card_singleton]
    · have hsingle : (TauCeti.diagramGraph A).neighborFinset i = {⟨m - 2, by omega⟩} := by
        ext x
        rw [hmem, Finset.mem_singleton]
        constructor
        · rintro (h1 | h1)
          · exfalso
            omega
          · refine Fin.ext ?_
            dsimp only
            omega
        · rintro rfl
          exact Or.inr (by dsimp only; omega)
      rw [hsingle, Finset.card_singleton]

theorem card_le_card_rootGroup_of_hasTorusSL2 {s : Fin D.rank} {F : Type} [Field F] [Finite F]
    (hs : HasTorusSL2 D H s F) : Nat.card F ≤ Nat.card ↥(D.rootGroup (Pi.single s 1)) := by
  obtain ⟨φ, hinj, hU, -⟩ := hs
  have hsl2 : Function.Injective (sl2Upper (k := F)) := by
    intro c d h
    have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      ((g : Matrix (Fin 2) (Fin 2) F)) 0 1) h
    simpa [coe_sl2Upper] using h1
  refine Nat.card_le_card_of_injective (fun c : F =>
    (⟨φ (sl2Upper c), hU c⟩ : ↥(D.rootGroup (Pi.single s 1)))) ?_
  intro c d hcd
  exact hsl2 (hinj (Subtype.ext_iff.1 hcd))

theorem endNodesThree_eq_of_path (h : BorelQuotient D n H π M) (hr : 2 ≤ D.rank)
    (hpath : ∀ i j : Fin D.rank, i ≠ j →
      (D.cartan i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val))
    {a b : Fin D.rank} (hab : a.val = 0 ∧ b.val + 1 = D.rank ∨ b.val = 0 ∧ a.val + 1 = D.rank)
    (h6 : Nat.card (rankOne D.rootGroup a) = 6 ∧
      ∃ x ∈ rankOne D.rootGroup a, ∃ y ∈ rankOne D.rootGroup a, x * y ≠ y * x)
    (hb : 2 < Nat.card ↥(D.rootGroup (Pi.single b 1))) :
    endNodesThree D H = {a} := by
  have hdeg : ∀ j : Fin D.rank, (TauCeti.diagramGraph D.cartan).degree j = 1 ↔
      j.val = 0 ∨ j.val + 1 = D.rank :=
    fun j => degree_eq_one_iff_of_path hr D.isFiniteType hpath j
  have hpar : ∀ j : Fin D.rank, parJ D H {j} = borel D H ⊔ rankOne D.rootGroup j := by
    intro j
    show borel D H ⊔ ⨆ i ∈ ({j} : Set (Fin D.rank)), rankOne D.rootGroup i = _
    rw [iSup_singleton]
  have hamem : a ∈ endNodesThree D H := by
    refine ⟨(hdeg a).2 ?_, ?_⟩
    · rcases hab with ⟨ha0, -⟩ | ⟨-, haend⟩
      · exact Or.inl ha0
      · exact Or.inr haend
    · rw [hpar a]
      exact card_borel_sup_rankOne_of_torus h a h6.1 h6.2
  have hbnot : b ∉ endNodesThree D H := by
    rintro ⟨-, hbc⟩
    have hcard := CFSG.AGLEmbeddingD2.Tits.GN516.CardPar.card_parJ_singleton h.ct h.extras b
    rw [hcard] at hbc
    have hpos : 0 < Nat.card ↥(borel D H) := Nat.card_pos
    have h3 : 1 + Nat.card ↥(D.rootGroup (Pi.single b 1)) = 3 := by
      refine Nat.mul_left_cancel hpos ?_
      rw [hbc, mul_comm 3]
    omega
  have hend : ∀ j : Fin D.rank, (TauCeti.diagramGraph D.cartan).degree j = 1 → j = a ∨ j = b := by
    intro j hj
    rcases (hdeg j).1 hj with hj0 | hjend
    · rcases hab with ⟨ha0, -⟩ | ⟨hb0, -⟩
      · exact Or.inl (Fin.ext (by rw [hj0, ha0]))
      · exact Or.inr (Fin.ext (by rw [hj0, hb0]))
    · rcases hab with ⟨-, hbend⟩ | ⟨-, haend⟩
      · exact Or.inr (Fin.ext (by omega))
      · exact Or.inl (Fin.ext (by omega))
  ext j
  constructor
  · rintro ⟨hjdeg, hjcard⟩
    rcases hend j hjdeg with h | h
    · simpa using h
    · rw [h] at hjdeg hjcard
      exact absurd ⟨hjdeg, hjcard⟩ hbnot
  · rintro rfl
    exact hamem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
