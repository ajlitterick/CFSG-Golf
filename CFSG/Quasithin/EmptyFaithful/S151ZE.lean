module

public import CFSG.Quasithin.EmptyFaithful.S151ZD
public import CFSG.Quasithin.Background.FLcSL

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

@[expose] def Input15122L45Block' : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → CharTwo L → Case15120TwoC Mc Z₁ L → Case15122Three M Mc Z₁ L


@[expose] def L45NotA38Type : Prop :=
  ∀ (G : Type) [Group G] (L : Subgroup G),
    (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) →
      ¬ A38Types (↥L ⧸ CFSG.pCore 2 ↥L)

@[expose] def Input15122L45Gen : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S : Subgroup G),
    (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) →
    IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L →
    ∀ Q : Subgroup G, (∀ P : Subgroup G, SMin L S P → P ≤ Q) → L ≤ Q

@[expose] def Input15122L45No3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L S P : Subgroup G), CharTwo L →
    (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L)) →
    IsPGroup 2 ↥S → S ≤ Subgroup.normalizer (L : Set G) → IsSylowTwoOf (S ⊓ L) L → SMin L S P →
      ¬ C126Third (P ⊔ S) S

theorem input15122L45Block_of (h118 : TheoremC118) (h126 : TheoremC126) (h37 : A37ForSQTK)
    (h38 : A38ForSQTK) (kN : L45NotA38Type) (hgen : Input15122L45Gen) (hno3 : Input15122L45No3) :
    Input15122L45Block' := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hchar h2C
  obtain ⟨htype, hMLpar, hMLne⟩ := h2C
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hSet := hc.ctx.setting
  set S := s1516 T Z₁ with hSdef
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hS2 : IsPGroup 2 ↥S := hc.h18.four.2.1
  have hsyl : IsSylowTwoOf (S ⊓ L) L := hc.h20.sylow
  have hSN : S ≤ Subgroup.normalizer (L : Set G) := by
    rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38
        (hSet.pCore_g1_ne_bot hq hMf) hc.hL.comp with hn | ⟨-, h2⟩
    · exact (s1516_le_g1 T Z₁).trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLG).mp hn)
    · exact absurd h2 (kN G L htype)
  have hselfN : L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L := by
    rcases htype with h4 | h5
    · exact FLc.normalizer_inf_le_of_isPSL (n := 4) (by norm_num) h4 hsyl
    · exact FLc.normalizer_inf_le_of_isPSL (n := 5) (by norm_num) h5 hsyl
  have hSM : S ≤ M := (s1516_le T Z₁).trans hMf.1.1.2
  have hMLne' : M ⊓ L ≠ L := fun h => hc.h20.one (by rw [← h]; exact inf_le_left)
  have hBM : S ⊓ L ≤ M ⊓ L := le_inf (inf_le_left.trans hSM) inf_le_right
  have hQ : ∀ P : Subgroup G, SMin L S P → P ≤ (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) := by
    intro P hP
    have hRP : pCoreOf 2 L ≤ P := (hsyl.pCoreOf_le).trans hP.sl
    have hchP : CharTwo P := zb_charTwo_of_le hchar hRP hP.le
    have hchH : CharTwo (P ⊔ S) := zb_charTwo_sup hP.sP hS2 hchP
    have hmin : IsMinParabolicOf (P ⊔ S) (P ⊔ S) := hP.isMinParabolic hS2 hsyl hselfN
    have hno := hno3 G L S P hchar htype hS2 hSN hsyl hP
    rcases bang_of_good h118 h126 hc hP.le hchH hmin hno with h | h
    · exact le_sup_of_le_right (le_inf h hP.le)
    · exact le_sup_of_le_left (le_inf h hP.le)
  have hjoin : (mZ1516 Mc Z₁ ⊓ L) ⊔ (M ⊓ L) = L :=
    le_antisymm (sup_le inf_le_right inf_le_right) (hgen G L S htype hS2 hSN hsyl _ hQ)
  exact ⟨hchar, htype, hMLpar, hMLne, ⟨inf_le_right, S ⊓ L, hsyl, hselfN.trans hBM⟩, hMLne', hjoin⟩

end CFSG.Quasithin
