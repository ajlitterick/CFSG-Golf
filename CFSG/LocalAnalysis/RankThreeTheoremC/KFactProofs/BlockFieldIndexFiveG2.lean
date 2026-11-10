module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveLevi
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexFiveTower
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFieldIndexG2
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGTwoBlock
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP

open Matrix CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.CurtisTits
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndex
open scoped commutatorElement

theorem blockOK_innerActOnP (p : ℕ) {G : Type*} [Group G] (S : Subgroup G) :
    BlockOKP p (innerActOn S) S :=
  fun _ hg _ _ _ => Or.inl hg

section LeviOneNode


end LeviOneNode


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.FieldIndexP
