module

public import CFSG.Quasithin.Vol2.Ch3Sec3Close
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7Base
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3328

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.H13.Lem3328
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

@[expose] def Stmt3_3_28G2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsG2Block L → tC L T = ⊥ ∧ qL L T = vPlus L T

@[expose] def Stmt3_3_28G2TC : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    IsG2Block L → tC L T = ⊥

@[expose] def Insp3_3_30 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G), Setup331 G T M L →
    IsG2Block L → T ≤ Subgroup.normalizer (L : Set G) → tC L T = ⊥ → qL L T = vPlus L T →
    (∀ B : Subgroup G, B ≤ T → IsElemAbelian 2 B → Nat.card ↥B ≤ Nat.card ↥(vPlus L T)) ∧
    (∀ B : Subgroup G, IsMaxElemAbelian T B → T ≤ Subgroup.normalizer (B : Set G) →
      ¬ B ≤ vPlus L T → ∃ b ∈ B, vPlus L T ⊓ Subgroup.centralizer (B : Set G) =
        vPlus L T ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    ∀ B B' : Subgroup G, IsMaxElemAbelian T B → IsMaxElemAbelian T B' →
      T ≤ Subgroup.normalizer (B : Set G) → T ≤ Subgroup.normalizer (B' : Set G) →
      ¬ B ≤ vPlus L T → ¬ B' ≤ vPlus L T → B ⊔ vPlus L T = B' ⊔ vPlus L T

variable {G : Type} [Group G] [Finite G] {T M L D : Subgroup G}

namespace Hyp331

theorem card_autOn_dvd (h : Hyp331 G T M L D) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(autOn L (vPlus L T)) ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hred := vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hle : CFSG.pCore 2 ↥L ≤ (InternalSec.autOnHom hLV).ker := by
    intro l hl
    rw [InternalSec.mem_ker_autOnHom]
    exact hQC (hOQ ((mem_pCore_iff l).mp hl))
  refine Subgroup.card_dvd_of_surjective
    (f := QuotientGroup.lift _ (InternalSec.autOnHom hLV) hle) ?_
  intro y
  obtain ⟨l, rfl⟩ := InternalSec.autOnHom_surjective hLV y
  exact ⟨QuotientGroup.mk l, rfl⟩

theorem isPSL_of_isLnBlock
    (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hLn : IsLnBlock L 3) :
    IsPSL 3 2 1 ↥(autOn L (vPlus L T)) := by
  have hred := vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hQC : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hCLV := inf_centralizer_le_of_isLnBlock hLn hLV (hOQ.trans hQC)
    (h.not_L_le_centralizer h38 h39)
  obtain ⟨-, α, hαs, hαk, -⟩ := hLn
  have hker : (InternalSec.autOnHom hLV).ker = α.ker := by
    rw [hαk]
    ext l
    rw [InternalSec.mem_ker_autOnHom, mem_pCore_iff]
    exact ⟨fun hl => hCLV (Subgroup.mem_inf.mpr ⟨l.2, hl⟩), fun hl => hQC (hOQ hl)⟩
  let e₁ : ↥(autOn L (vPlus L T)) ≃* ↥L ⧸ α.ker :=
    ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (InternalSec.autOnHom_surjective hLV))).symm
  let e₂ : ↥L ⧸ α.ker ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)) :=
    QuotientGroup.quotientKerEquivOfSurjective α hαs
  exact CFSG.QuasithinUnique.Vol2Native.A312L.Seven.isPSL_three_two
    ((e₁.trans e₂).trans (specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm)

end Hyp331


theorem stmt3_3_28G2_of (h25 : Stmt3_3_25) (hTC : Stmt3_3_28G2TC) : Stmt3_3_28G2 := by
  intro G _ _ T M L D h hG2
  have hTC' := hTC G T M L D h hG2
  refine ⟨hTC', ?_⟩
  rcases (h25 G T M L D h).2.2 hTC' with hV | hA6
  · exact hV.symm
  · exfalso
    obtain ⟨-, α, hαs, hαk, -⟩ := hA6
    have h1 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 := F420.card_of_u33 hG2.2.1
    have h2 : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
      rw [← hαk, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hαs).toEquiv,
        nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    omega


end CFSG.Quasithin.H13
