module

public import CFSG.ClassicalInvolution.Uniform.UOmegaLie

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.Assembly
open scoped MatrixGroups

section Defs

@[expose] def CompIs (p f : ℕ) [Fact p.Prime] (c : Q3.CompData) (t : LowTwoRank.StatedLieTag)
    (n : ℕ) : Prop :=
  ∃ e : ℕ, (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) ∧ IsFundTag t ∧
    LowTwoRank.StatedLieAdmissible t n p e ∧ c = compModel p e t n

@[expose] def HasLieTypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (t : LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∃ D : OmegaLieU p f Ω, D.card = 1 ∧ ∃ i : Fin D.card, CompIs p f (D.kind i) t n

@[expose] def HasM11TypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) : Prop :=
  p ^ f = 3 ∧ ∃ D : OmegaLieU p f Ω, D.card = 1 ∧ ∃ i : Fin D.card, D.kind i = Q3.CompData.m11

@[expose] def SectionLieTypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (Y : Subgroup G) (t : LowTwoRank.StatedLieTag) (n : ℕ) : Prop :=
  ∃ D : LieSystemDataU p f (Fin 1) (↥Y ⧸ classicalInvolutionOddCore ↥Y)
    (oddQuotientFamily (restrictFamily Ω Y)), CompIs p f (D.kind 0) t n

@[expose] def SectionCompU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (Y : Subgroup G) (c : Q3.CompData) : Prop :=
  ∃ D : LieSystemDataU p f (Fin 1) (↥Y ⧸ classicalInvolutionOddCore ↥Y)
    (oddQuotientFamily (restrictFamily Ω Y)), D.kind 0 = c

@[expose] def HasOrthTypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (d : ℕ) (ε : Bool) : Prop :=
  ∃ t n, IsOrthTag d ε t n ∧ HasLieTypeU p f Ω t n

@[expose] def SectionOrthTypeU (p f : ℕ) [Fact p.Prime] {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (Y : Subgroup G) (d : ℕ) (ε : Bool) : Prop :=
  ∃ t n, IsOrthTag d ε t n ∧ SectionLieTypeU p f Ω Y t n

end Defs

section Facades

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] noncomputable def CompIs.modelSpec {c : Q3.CompData} {t : LowTwoRank.StatedLieTag} {n : ℕ}
    (h : CompIs p f c t n) : ModelSpec p f c :=
  ⟨t, n, h.choose, h.choose_spec.2.1, h.choose_spec.2.2.1, h.choose_spec.1,
    h.choose_spec.2.2.2⟩

namespace OmegaLieU

@[expose] noncomputable def ofOmegaLie (h3 : p ^ f ≠ 3) (D : OmegaLie p f Ω) : OmegaLieU p f Ω where
  card := D.card
  kind i := compModel p (D.exp i) (D.tag i) (D.rank i)
  valid i := Or.inl ⟨D.tag i, D.rank i, D.exp i, D.isFundTag i, D.admissible i, D.exp_eq i, rfl⟩
  hom := D.hom
  ker_le_center := D.ker_le_center
  commute := D.commute
  generate := D.generate
  fundamental := D.fundamental
  meets := D.meets
  card_eq h := absurd h h3

@[expose] noncomputable def toOmegaLieOfSpec (D : OmegaLieU p f Ω)
    (σ : ∀ i, ModelSpec p f (D.kind i)) : OmegaLie p f Ω where
  card := D.card
  tag i := (σ i).tag
  rank i := (σ i).rank
  exp i := (σ i).exp
  hom i := castHom (σ i).eq (D.hom i)
  isFundTag i := (σ i).isFundTag
  admissible i := (σ i).admissible
  exp_eq i := (σ i).exp_eq
  ker_le_center i := castHom_ker_le_center _ _ (D.ker_le_center i)
  commute i j hij x y := by
    obtain ⟨x', hx⟩ := exists_castHom_eq (σ i).eq (D.hom i) x
    obtain ⟨y', hy⟩ := exists_castHom_eq (σ j).eq (D.hom j) y
    rw [hx, hy]
    exact D.commute i j hij x' y'
  generate := by
    have h : ∀ i, (castHom (σ i).eq (D.hom i)).range = (D.hom i).range :=
      fun i => range_castHom _ _
    exact (iSup_congr h).trans D.generate
  fundamental L hL := by
    obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom (σ i).eq (D.hom i) hR
    exact ⟨i, R', hR', hLR.trans hRR.symm⟩
  meets i := by
    obtain ⟨R, hR, hΩ⟩ := D.meets i
    obtain ⟨R', hR', hRR⟩ := exists_map_castHom (σ i).eq (D.hom i) hR
    exact ⟨R', hR', hRR ▸ hΩ⟩

end OmegaLieU


end Facades

end CFSG.ClassicalInvolution.Uniform
