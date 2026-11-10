module

public import CFSG.ClassicalInvolution.Asc77.AscR31Model
public import CFSG.ClassicalInvolution.Asc77.AscT7Z22
public import CFSG.ClassicalInvolution.Asc77.AscT7PE

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace R31

set_option linter.unusedSectionVars false

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.Assembly.LowTwoRank
open CFSG.Timmesfeld (edgeD)
open CFSG.ClassicalInvolution.RouteD (zeroD)
open CFSG.LieType.Universal (minusCoeffs_irr)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockPair)

variable (p f : ℕ) [Fact p.Prime]

section CIT40


@[expose] def C23_recogNeg : Prop :=
  p ^ f % 4 = 3 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) →
        (LayerOrthType p f Ω u 5 true ∨ LayerOrthType p f Ω u 6 (!piSign p f)) →
          ∃ D : LieSystemData p f G Ω, D.card = 1 ∧
            ∃ i, (D.tag i = .POmegaOdd ∧ D.rank i = 3) ∨
              (D.tag i = .POmegaMinus ∧ D.rank i = 4)

@[expose] def C23_recogB3 : Prop :=
  p ^ f % 4 = 3 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) → LayerOrthType p f Ω u 5 true →
          ∃ D : LieSystemData p f G Ω, D.card = 1 ∧
            ∃ i, D.tag i = .POmegaOdd ∧ D.rank i = 3

@[expose] def C23_recogMinus4 : Prop :=
  p ^ f % 4 = 3 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (z u e g : G), Hyp23Setting p f Ω K K' z →
      Hyp23bData Ω K K' W z u e g →
        (alphaOf (Subgroup.closure ({u, z} : Set G)) = ⊥ ∧ rLayer Ω e ⊔ rLayer Ω u = ⊤) →
        LayerOrthType p f Ω e 6 (piSign p f) → LayerOrthType p f Ω u 6 (!piSign p f) →
          ∃ D : LieSystemData p f G Ω, D.card = 1 ∧
            ∃ i, D.tag i = .POmegaMinus ∧ D.rank i = 4

variable {p f} in
theorem c23_recogNeg_of_cases (h7 : C23_recogB3 p f) (h8 : C23_recogMinus4 p f) :
    C23_recogNeg p f := by
  intro hq G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  rcases hY with hY | hY
  · obtain ⟨D, hc, i, ht, hr⟩ := h7 hq G Ω K K' W z u e g hs hd hα hE hY
    exact ⟨D, hc, i, Or.inl ⟨ht, hr⟩⟩
  · obtain ⟨D, hc, i, ht, hr⟩ := h8 hq G Ω K K' W z u e g hs hd hα hE hY
    exact ⟨D, hc, i, Or.inr ⟨ht, hr⟩⟩

@[expose] def C22_recogNeg : Prop :=
  p ^ f % 4 = 3 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' K₃ : Subgroup G) (z u₁ u₂ u₃ : G), Hyp22Setting p f Ω K K' K₃ z u₁ u₂ u₃ →
      (∀ W ∈ WSet Ω, MuIsoWylD4 Ω W) →
        (LayerOrthType p f Ω (u₁ * u₂) 6 (piSign p f) ∧
          (⨆ M ∈ twinSet Ω K, M) ⊔ rLayer Ω (u₁ * u₂) = ⊤) →
          ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .POmegaPlus ∧ D.rank i = 4

@[expose] def C22_chainNeg : Prop :=
  p ^ f % 4 = 3 → C22_chainSettingX p f

@[expose] def C22_chainPos : Prop :=
  p ^ f % 4 = 1 → C22_chainSettingX p f

variable {p f} in
theorem c22_chainSettingX_of_pos_neg (hpos : C22_chainPos p f) (hneg : C22_chainNeg p f) :
    C22_chainSettingX p f := by
  intro G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs
  have hp : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hs.stand.odd
  have hmod : p ^ f % 2 = 1 := Nat.odd_iff.mp hp.pow
  have hcases : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by omega
  rcases hcases with h1 | h3
  · exact hpos h1 G Ω K K' K₃ z u₁ u₂ u₃ hs
  · exact hneg h3 G Ω K K' K₃ z u₁ u₂ u₃ hs

variable {p f} in
theorem c22_chainNeg_of_recog (h : C22_recogNeg p f) : C22_chainNeg p f := by
  intro hq G _ _ _ Ω K K' K₃ z u₁ u₂ u₃ hs hW hLayer
  obtain ⟨D, hc, i, ht, hr⟩ := h hq G Ω K K' K₃ z u₁ u₂ u₃ hs hW hLayer
  exact R31.chainD4_of_lieSystem hs.stand.five hs.stand.hyp.conjInvariant D hc ht hr

variable {p f} in
theorem c22_chainSettingX_of_recog (hpos : C22_chainPos p f) (h : C22_recogNeg p f) :
    C22_chainSettingX p f :=
  c22_chainSettingX_of_pos_neg hpos (c22_chainNeg_of_recog h)


end CIT40

section Big


variable {p f} in
theorem c23_chainNeg_of_recog (h : C23_recogNeg p f) : C23_chainNeg p f := by
  intro hq G _ _ _ Ω K K' W z u e g hs hd hα hE hY
  obtain ⟨D, hc, i, hi⟩ := h hq G Ω K K' W z u e g hs hd hα hE hY
  have hΩ := hs.stand.hyp.conjInvariant
  rcases hi with ⟨ht, hr⟩ | ⟨ht, hr⟩
  · exact Or.inl (R31.chainB3_of_lieSystem hs.stand.odd hs.stand.five hΩ D hc ht hr)
  · exact Or.inr (R31.chainMinus4_of_lieSystem hs.stand.odd hs.stand.five hΩ D hc ht hr)


end Big

end R31

end CFSG.ClassicalInvolution.Asc77
