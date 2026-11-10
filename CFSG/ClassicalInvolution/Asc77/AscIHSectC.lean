module

public import CFSG.ClassicalInvolution.Asc77.AscIHSectB
public import CFSG.ClassicalInvolution.Asc77.AscE184OddQuot
public import CFSG.ClassicalInvolution.Asc77.AscE184Sub

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Disconnected

variable {p f : ℕ} [Fact p.Prime]

section Bridge

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

def OmegaLie.toLieSystemData (D : OmegaLie p f Φ) (hgen : omegaGen Φ = ⊤) :
    LieSystemData p f X Φ where
  card := D.card
  tag := D.tag
  rank := D.rank
  exp := D.exp
  hom := D.hom
  isFundTag := D.isFundTag
  admissible := D.admissible
  exp_eq := D.exp_eq
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate.trans hgen
  fundamental := D.fundamental
  meets := D.meets

theorem LieSystemData.exists_of_hasLieType (hgen : omegaGen Φ = ⊤) {t : StatedLieTag} {n : ℕ}
    (h : HasLieType p f Φ t n) :
    ∃ D : LieSystemData p f X Φ, D.card = 1 ∧ ∃ i : Fin D.card, D.tag i = t ∧ D.rank i = n := by
  obtain ⟨D, hcard, i, ht, hn⟩ := h
  exact ⟨D.toLieSystemData hgen, hcard, i, ht, hn⟩

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {Y : Subgroup G}

theorem sectionLieType_of_hasLieType
    (hgen : omegaGen (oddQuotientFamily (restrictFamily Ω Y)) = ⊤) {t : StatedLieTag} {n : ℕ}
    (h : HasLieType p f (oddQuotientFamily (restrictFamily Ω Y)) t n) :
    SectionLieType p f Ω Y t n :=
  LieSystemData.exists_of_hasLieType hgen h

theorem sectionOrthType_of_hasOrthType
    (hgen : omegaGen (oddQuotientFamily (restrictFamily Ω Y)) = ⊤) {d : ℕ} {ε : Bool}
    (h : HasOrthType p f (oddQuotientFamily (restrictFamily Ω Y)) d ε) :
    SectionOrthType p f Ω Y d ε := by
  obtain ⟨t, n, hd, ht⟩ := h
  exact ⟨t, n, hd, sectionLieType_of_hasLieType hgen ht⟩

end Bridge

section Ambient

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


end Ambient

section Simple

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {Ω : Set (Subgroup G)}

theorem TransSection.of_simple (hΩ : HypOmegaMod p f Ω) (hne : Ω.Nonempty)
    (htrans : ∀ K ∈ Ω, ∀ L ∈ Ω, ∃ g : G, conjSub g K = L) (hA : ∀ J ∈ Ω, AEmpty Ω J) :
    TransSection p f Ω := by
  obtain ⟨K, hK⟩ := hne
  obtain ⟨z, hz⟩ := hΩ.classical K hK
  exact { hyp := hΩ
          oddCore := ih8_oddCore_eq_bot_of_simple hz.orderOf_eq_two
          gen := ih8_omegaGen_eq_top hΩ.conjInvariant hK (ih8_member_ne_bot hz)
          trans := htrans
          aEmpty := hA }

omit [Finite G] in
theorem top_notMem_of_simple (hΩ : HypOmegaMod p f Ω) : (⊤ : Subgroup G) ∉ Ω := by
  intro h
  obtain ⟨z, hz⟩ := hΩ.classical _ h
  exact ih8_not_top_member hz

end Simple


end CFSG.ClassicalInvolution.Asc77
