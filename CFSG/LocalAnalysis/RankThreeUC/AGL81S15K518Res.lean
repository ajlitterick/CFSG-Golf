module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.Engine
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K518Cen
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15YstarNormalOthers
import CFSG.Certificates.Kernel.LocalCompTits.Span
import Certificates.Kernel.J4Count.FixCE
import Certificates.Kernel.J4Count.FixCPairBase1

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN

@[expose] def K518Y : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T T₁ T₂ : Subgroup X), GNSetting X T → GNGood T T₁ T₂ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X),
      GNYComponent T T₁ T₂ Ls → LiftOf T L Ls →
      gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)) →
      mS T T₁ p Ls = 1 → mS T T₂ p Ls = 1 → mN T₁ p = 1 → mN T₂ p = 1 →
      ¬ p ∣ Nat.card (gnC T) →
      (∀ Is, GNYComponent T T₁ T₂ Is → Is ≠ Ls → ¬ p ∣ Nat.card ↥Is) → Ls.Normal →
        pElementSubgroup p (⊤ : Subgroup X) ≤ Ls.comap (toStar T)

theorem K518_of_residue (hG : KFactChevGenCentre) (hKSMAlt : KSMAlt) (h : K518Y) : K518 := by
  intro X _ _ T T₁ T₂ hX hg p hp hp2 Ls L hLs hL hinv m1 m2 n1 n2
  have hC := not_dvd_card_gnC_of_lift hG hKSMAlt hX hg hp hp2 hLs hL hinv m1 m2 n1
  exact ⟨hC, fun hoth => h X T T₁ T₂ hX hg p hp hp2 Ls L hLs hL hinv m1 m2 n1 n2 hC hoth
    (normal_of_k518Y_hyps hX hg hp hp2 hLs hinv m1 m2 n1 n2 hoth)⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
