module

public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspB1
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspB2
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.SectionRank.QTK.FactJ4Of
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA3
public import CFSG.LocalAnalysis.SectionRank.QTK.J4InspA5

public section

open scoped IsMulCommutative

namespace CFSG.SectionRank.QTK

open CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def OddCharSectionalTwoRankQTK : Prop :=
  ∀ (S : Type) [Group S] [Finite S], OddCharList S → CFSG.GH74.SectionalTwoRankLE S 8


theorem two_pow_nine_le_card_frattini (hFM : FaithfulL34ModDim) {L : Type} [Group L] [Finite L]
    (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup 2 ↥Q)
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hPSL : CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) :
    2 ^ 9 ≤ Nat.card (↥Q ⧸ frattini ↥Q) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp : IsSimpleGroup (L ⧸ Q) := CFSG.Quasithin.H13.A5.isSimpleGroup_of_isPSL34 hPSL
  have hfe := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) (P := ↥Q) hQ
  have hcomm : IsMulCommutative (↥Q ⧸ frattini ↥Q) := hfe.2.1
  have hexp : ∀ v : ↥Q ⧸ frattini ↥Q, v ^ 2 = 1 := hfe.2.2.1
  haveI := hcomm
  have hQC : Q ≤ (frattiniConjAct Q).ker := by
    intro q hq
    exact MonoidHom.mem_ker.mpr (frattiniConjAct_of_mem Q hQ ⟨q, hq⟩)
  let ψ : L ⧸ Q →* MulAut (↥Q ⧸ frattini ↥Q) := QuotientGroup.lift Q (frattiniConjAct Q) hQC
  have hψ : ∀ x : L, ψ (QuotientGroup.mk' Q x) = frattiniConjAct Q x := fun x => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q a
    rw [hψ] at ha
    have hx : x ∈ Q := frattini_kernel_le Q hQ hperf hsimp hnt x ha
    exact (QuotientGroup.eq_one_iff x).mpr hx
  have hPSLX : CFSG.Quasithin.IsPSL 3 2 2 ↥ψ.range :=
    isPSL_of_mulEquiv (MonoidHom.ofInjective hinj) hPSL
  exact hFM (↥Q ⧸ frattini ↥Q) hexp ψ.range hPSLX

theorem odd_branch_false_of_sectional (hSec : OddCharSectionalTwoRankQTK) (hFM : FaithfulL34ModDim)
    {S : Type} [Group S] [Finite S] (hB : OddCharList S)
    {L : Type} [Group L] [Finite L] (j : L →* S) (hj : Function.Injective j)
    (Q : Subgroup L) [Q.Normal] (hQ : IsPGroup 2 ↥Q)
    (hperf : ⁅(⊤ : Subgroup L), (⊤ : Subgroup L)⁆ = ⊤)
    (hPSL : CFSG.Quasithin.IsPSL 3 2 2 (L ⧸ Q)) (hnt : ⁅Q, (⊤ : Subgroup L)⁆ ≠ ⊥) : False := by
  have h9 := two_pow_nine_le_card_frattini hFM Q hQ hperf hPSL hnt
  have hsec : CFSG.GH74.SectionalTwoRankLE ↥Q 8 :=
    (CFSG.GH74.SectionalTwoRankLE.of_injective j hj (hSec S hB)).subgroup Q
  have hquot : CFSG.GH74.SectionalTwoRankLE (↥Q ⧸ frattini ↥Q) 8 :=
    hsec.quotient (frattini ↥Q)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfe := CFSG.GroupTheory.frattini_elementary_quotient (p := 2) (P := ↥Q) hQ
  have hEab : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup (↥Q ⧸ frattini ↥Q)) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · exact Subtype.ext
        (hfe.2.1.is_comm.comm (a : ↥Q ⧸ frattini ↥Q) (b : ↥Q ⧸ frattini ↥Q))
    · intro x _
      exact hfe.2.2.1 x
  have hcard : Nat.card (↥Q ⧸ frattini ↥Q) ≤ 2 ^ 8 := by
    have h := hquot.card_le_of_elementary (⊤ : Subgroup (↥Q ⧸ frattini ↥Q)) hEab
    rwa [Subgroup.card_top] at h
  norm_num at h9 hcard
  omega


end CFSG.SectionRank.QTK

end
