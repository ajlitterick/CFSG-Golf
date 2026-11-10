module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSmall
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKBender
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSp4Odd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKMathieu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKL3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKOdd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKL5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKJ2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHS
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKSporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKG2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKTits
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKD4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKF4
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3S23
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint

theorem examExcludes_sporadic_rank
    (s : TauCeti.SporadicName) (hs : s = .J2 ∨ s = .HS) :
    ExamExcludes (FamSporadic s) := by
  rintro G _ _ K B B' P R m h ⟨e⟩
  obtain ⟨Ab, hAb, hcard⟩ := h.exists_bar_elem_big
  have hAb' : IsElemAbelian 2 (Ab.map e.toMonoidHom) := isElemAbelian_map' hAb _
  have hc : Nat.card (Ab.map e.toMonoidHom) = Nat.card Ab :=
    card_map_of_inf_ker_eq_bot Ab _ fun x _ hx => (e.map_eq_one_iff).mp hx
  rcases hs with rfl | rfl
  · have h1 := j2_native_rank _ hAb'
    rw [hc] at h1
    omega
  · have h1 := hs_native_rank _ hAb'
    rw [hc] at h1
    omega

theorem examExcludes_evenL3 : ExamExcludes FamEvenL3 := by
  rintro G _ _ K B B' P R m hcfg ⟨f, hf1, hmodel⟩
  by_cases hf : f ≤ 2
  · exact examExcludes_evenL3_small G K B B' P R m hcfg f hf hf1 hmodel
  · exact examExcludes_evenL3_large G K B B' P R m hcfg ⟨f, by omega, hmodel⟩

theorem lemma2_4_23_five_examK_proved
    : Lemma2_4_23_five_examK :=
  examK_of_families
    { alt := examExcludes_alt
      oddL2 := examExcludes_oddL2
      oddL3 := examExcludes_oddL3
      oddU3 := examExcludes_oddU3
      evenL2 := examExcludes_evenL2
      evenL3 := examExcludes_evenL3
      evenU3 := examExcludes_evenU3
      sp4 := examSp4 sp4OddMultiplierTrivial
      g2 := examExcludes_g2
      d4 := examExcludes_d4
      f4 := examExcludes_f4
      sz := examExcludes_sz
      tits := examExcludes_tits
      l4 := examExcludes_l4
      l5 := examExcludes_l5
      sporadic := fun s hs => by
        by_cases hsmall : s = .M11 ∨ s = .M12 ∨ s = .J1
        · exact examExcludes_sporadic_small s hsmall
        · by_cases hmat : s = .M22 ∨ s = .M23
          · exact examExcludes_sporadic_M2x s hmat
          · by_cases hrank : s = .J2 ∨ s = .HS
            · exact examExcludes_sporadic_rank s hrank
            · by_cases hfus : s = .M24 ∨ s = .He ∨ s = .Ru ∨ s = .J4
              · exact examExcludes_sporadic_fusion s hfus
              · exfalso
                rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
                  simp at hsmall hmat hrank hfus }

end CFSG.QuasithinUnique.Lin2
