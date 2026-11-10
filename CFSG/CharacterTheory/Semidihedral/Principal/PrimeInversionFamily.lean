module

public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeInversionSections
public import CFSG.CharacterTheory.Semidihedral.Principal.NormThreeGram
public import CFSG.CharacterTheory.Semidihedral.Principal.FullPrimePartBlock
public import CFSG.CharacterTheory.Semidihedral.Principal.CentralQuotientRegular
public import CFSG.CharacterTheory.TwoRankLowerBound.VirtualNormOne

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.Principal

open CFSG.TwoRankLowerBound.Helpers CFSG.RankTwoShapes

variable {G : Type*} [Group G]


section Pairing

variable [Fintype G]


theorem characterPairing_sum_left {H : Type*} [Group H] [Fintype H] {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) (F : ι → H → ℂ) (h : H → ℂ) :
    characterPairing (fun x => ∑ i ∈ s, c i * F i x) h =
      ∑ i ∈ s, c i * characterPairing (F i) h := by
  unfold characterPairing
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun x _ => ?_
  ring

end Pairing

section RootSums


end RootSums

section Labels

variable [Fintype G]

theorem characterPairing_label_label (basis : FiniteIrreducibleCharacterBasis G)
    (x y : basis.index) :
    characterPairing (basis.representation x).character (basis.representation y).character =
      if x = y then 1 else 0 := by
  rw [characterPairing_irreducible _ _ (basis.irreducible x) (basis.irreducible y)]
  by_cases h : x = y
  · subst h
    simp
  · have h' : (basis.representation x).character ≠ (basis.representation y).character :=
      fun hc => h (basis.distinct hc)
    simp [h, h']

theorem exists_conj_label (basis : FiniteIrreducibleCharacterBasis G) (x : basis.index) :
    ∃ x' : basis.index, ∀ g, (basis.representation x').character g =
      starRingEnd ℂ ((basis.representation x).character g) := by
  let data : FiniteComplexRepresentation G :=
    { vector := Module.Dual ℂ (basis.representation x).vector
      representation := (basis.representation x).representation.dual }
  have hchar : ∀ g, data.character g = starRingEnd ℂ ((basis.representation x).character g) := by
    intro g
    change (basis.representation x).representation.dual.character g = _
    rw [Representation.char_dual, finite_character_conjugate_inverse]
  have hself : characterPairing (basis.representation x).character
      (basis.representation x).character = 1 := by
    rw [characterPairing_label_label]
    simp
  have hnorm : characterPairing data.character data.character = 1 := by
    rw [← hself]
    unfold characterPairing
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    change (basis.representation x).representation.dual.character g *
      (basis.representation x).representation.dual.character g⁻¹ = _
    rw [Representation.char_dual, Representation.char_dual, inv_inv, mul_comm]
  obtain ⟨x', hx'⟩ := character_norm_one_basis_character basis data hnorm
  exact ⟨x', fun g => by rw [hx', hchar]⟩

end Labels

section SingularClasses

variable [Fintype G]


end SingularClasses

section Projections

variable [Fintype G]


end Projections

section Family

variable [Fintype G]

theorem label_character_one (basis : FiniteIrreducibleCharacterBasis G) (c : basis.index) :
    (basis.representation c).character 1 =
        (Module.finrank ℂ (basis.representation c).vector : ℂ) ∧
      0 < Module.finrank ℂ (basis.representation c).vector := by
  have h1 : (basis.representation c).character 1 =
      (Module.finrank ℂ (basis.representation c).vector : ℂ) := by
    rw [FiniteComplexRepresentation.character, Representation.char_one]
  refine ⟨h1, Nat.pos_of_ne_zero fun h0 => ?_⟩
  apply irreducible_character_degree_ne_zero _ (basis.irreducible c)
  rw [h1, h0, Nat.cast_zero]


end Family

section Values

variable [Fintype G]


end Values

theorem prime_inversion_weighted_identity (f a₁ a₂ δ : ℂ) (hδ : δ = 1 ∨ δ = -1) (hf : f ≠ 0)
    (hfδ : f + δ ≠ 0) :
    1 + a₁ * a₂ * δ / f + (a₁ + δ) * (a₂ + δ) * δ / (f + δ) * (-1) =
      (f - a₁) * (f - a₂) / (f * (f + δ)) := by
  rcases hδ with rfl | rfl
  · field_simp
    ring
  · field_simp
    ring

section Main

variable [Fintype G]

theorem characterPairing_one_add_sub_left (c : ℂ) (F F' g : G → ℂ) :
    characterPairing (fun x => 1 + c * F x - c * F' x) g =
      characterPairing (fun _ => 1) g + c * characterPairing F g - c * characterPairing F' g := by
  unfold characterPairing
  have h : ∀ x : G, (1 + c * F x - c * F' x) * g x⁻¹ =
      1 * g x⁻¹ + c * (F x * g x⁻¹) - c * (F' x * g x⁻¹) := fun x => by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring


end Main

end CFSG.Semidihedral.Principal
