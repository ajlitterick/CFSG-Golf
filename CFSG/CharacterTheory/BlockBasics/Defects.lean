module

public import CFSG.CharacterTheory.BlockBasics.Bridge
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockDefects
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.NormalBlockDefects
public import CFSG.CharacterTheory.BrauerThirdMainTheorem.BlockResidues
public import CFSG.CharacterTheory.TwoRankLowerBound.PrincipalBlockDefect

public section

open scoped Classical

namespace CFSG.BlockBasics

open CFSG CFSG.BrauerThirdMainTheorem.Helpers

theorem prime_mem_of_charP (p : ℕ) (m : Ideal BlocksAlgInt) [CharP (BlocksAlgInt ⧸ m) p] :
    (p : BlocksAlgInt) ∈ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem mem_localMaxIdeal_iff_of_sub_mem (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {a b : ℂ} (h : a - b ∈ BlocksLocalMaxIdeal m) :
    a ∈ BlocksLocalMaxIdeal m ↔ b ∈ BlocksLocalMaxIdeal m := by
  constructor
  · intro ha
    have hb := localMaxIdeal_sub m hm ha h
    rwa [sub_sub_cancel] at hb
  · intro hb
    have ha := localMaxIdeal_add m hm h hb
    rwa [sub_add_cancel] at ha

theorem blockDefect_iff_of_mem_blockOf (p : ℕ) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Finite G] {χ ψ : G → ℂ} (hχ : χ ∈ BlocksIrr G)
    (hψ : ψ ∈ BlocksBlockOf m G χ) (D : Subgroup G) :
    blockDefect p m χ D ↔ blockDefect p m ψ D := by
  have hres : ∀ C : ConjClasses G,
      BlocksCentralChar χ (classCoefficients C) ∉ BlocksLocalMaxIdeal m ↔
        BlocksCentralChar ψ (classCoefficients C) ∉ BlocksLocalMaxIdeal m := fun C =>
    not_congr (mem_localMaxIdeal_iff_of_sub_mem m hm
      (sameBlock_centralChar_congr m hm G hχ hψ (classCoefficients_central m hm C))).symm
  constructor
  · rintro ⟨⟨C, hC, hCres⟩, huniv⟩
    exact ⟨⟨C, hC, (hres C).mp hCres⟩, fun E hE => huniv E ((hres E).mpr hE)⟩
  · rintro ⟨⟨C, hC, hCres⟩, huniv⟩
    exact ⟨⟨C, hC, (hres C).mpr hCres⟩, fun E hE => huniv E ((hres E).mp hE)⟩

theorem forall_blockDefect_iff (p : ℕ) (m : Ideal BlocksAlgInt) (hm : m.IsMaximal)
    {G : Type} [Group G] [Finite G] {B : Set (G → ℂ)} (hB : BlocksIsBlock m G B)
    {χ : G → ℂ} (hχ : χ ∈ B) (D : Subgroup G) :
    (∀ ψ ∈ B, blockDefect p m ψ D) ↔ blockDefect p m χ D := by
  have hBχ := block_eq_blockOf_member m hB hχ
  have hχirr := block_subset_irr m hB hχ
  refine ⟨fun h => h χ hχ, fun h ψ hψ => ?_⟩
  rw [hBχ] at hψ
  exact (blockDefect_iff_of_mem_blockOf p m hm hχirr hψ D).mp h


theorem principal_block_defect (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    [hm : m.IsMaximal] [CharP (BlocksAlgInt ⧸ m) p] (G : Type) [Group G] [Finite G] :
    (∀ D : Subgroup G, (∀ χ ∈ BlocksPrincipalBlock m G, blockDefect p m χ D) ↔
      ∃ P : Sylow p G, (P : Subgroup G) = D) ∧
    ∀ (C : ConjClasses G) (Q : Subgroup G), classDefect p C Q →
      (BlocksCentralChar (fun _ => (1 : ℂ)) (classCoefficients C) ∉ BlocksLocalMaxIdeal m ↔
        ∃ P : Sylow p G, (P : Subgroup G) = Q) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨basis⟩ := CFSG.TwoRankLowerBound.Helpers.finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨l, hl⟩ := exists_label_of_mem_irr basis (trivial_mem_irr G)
  have hl1 : (basis.representation l).character = 1 := hl
  refine ⟨fun D => ?_, fun C Q hQ => ?_⟩
  · rw [forall_blockDefect_iff p m hm (principal_isBlock m G) (trivial_mem_principal m G) D, ← hl,
      ← coefficientBlockDefect_iff basis m p l D]
    exact CFSG.TwoRankLowerBound.Helpers.principal_coefficientBlockDefect_iff_sylow basis m p l
      hl1 D
  · have h := CFSG.TwoRankLowerBound.Helpers.principal_class_residue_ne_zero_iff_sylow basis m p l
      hl1 ((classDefect_iff p C Q).mpr hQ)
    rw [Ne, centralCharacterResidueHom_eq_zero_iff, hl] at h
    have hcoeff :
        (fun g => (CFSG.TwoRankLowerBound.Helpers.centralConjugacyClassSum
          (CFSG.TwoRankLowerBound.Helpers.localizedComplexIntegerRing m) C).val.coeff g) =
          classCoefficients C := by
      funext g
      exact centralConjugacyClassSum_coeff _ C g
    rw [hcoeff] at h
    exact h

theorem normal_p_subgroup_class_vanishing (p : ℕ) (hp : p.Prime) (m : Ideal BlocksAlgInt)
    (hm : m.IsMaximal) [CharP (BlocksAlgInt ⧸ m) p] (H : Type) [Group H] [Finite H]
    (P : Subgroup H) [P.Normal] (hP : IsPGroup p P) (B : Set (H → ℂ))
    (hB : BlocksIsBlock m H B) :
    (∀ C : ConjClasses H, (∀ x : H, ConjClasses.mk x = C → x ∉ Subgroup.centralizer (P : Set H)) →
      ∀ χ ∈ B, BlocksCentralChar χ (classCoefficients C) ∈ BlocksLocalMaxIdeal m) ∧
      ∀ D : Subgroup H, (∀ χ ∈ B, blockDefect p m χ D) → P ≤ D := by
  have hpm := prime_mem_of_charP p m
  refine ⟨fun C hC χ hχ => ?_, fun D hD => ?_⟩
  · apply normalPSubgroup_centralChar_vanishes p hp m hm hpm H P hP (block_subset_irr m hB hχ)
      (classCoefficients_central m hm C)
    intro x hx
    simp only [classCoefficients]
    rw [ite_eq_right]
    intro hxC
    exact hC x hxC hx
  · obtain ⟨χ, hχ⟩ := block_nonempty m hB
    exact normalPSubgroup_le_blockDefect p hp m hm hpm H P hP (block_subset_irr m hB hχ) (hD χ hχ)

section Basis

open CFSG.TwoRankLowerBound.Helpers

variable (p : ℕ) [Fact p.Prime] (m : Ideal BlocksAlgInt) [m.IsMaximal]
  [CharP (BlocksAlgInt ⧸ m) p] {G : Type} [Group G] [Fintype G]
  (basis : FiniteIrreducibleCharacterBasis G)


theorem principal_coefficientBlockDefect_iff_sylow_of_shared (l : basis.index)
    (hl : (basis.representation l).character = 1) (D : Subgroup G) :
    coefficientBlockDefect basis m p l D ↔ ∃ P : Sylow p G, (P : Subgroup G) = D := by
  rw [coefficientBlockDefect_iff, hl, ← (principal_block_defect p Fact.out m G).1 D]
  exact (forall_blockDefect_iff p m inferInstance (principal_isBlock m G)
    (trivial_mem_principal m G) D).symm

end Basis

end CFSG.BlockBasics
