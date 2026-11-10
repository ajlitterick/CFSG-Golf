module

public import CFSG.RankThree.PartTwo.Sec20.Statements
import CFSG.RankThree.PartTwo.Sec18.Item181b

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem exists_ctx20 {A M L N : Subgroup G} {c : G} (h : Hyp201 G A M L N c) :
    ∃ T : Subgroup G, Ctx20 G A M L N c T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Sc, hSc⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (M ⊓ Subgroup.centralizer {c})
  have hScM : Sc ≤ M := hSc.le.trans inf_le_left
  obtain ⟨Q, hQ⟩ := (hSc.isPGroup.comap_subtype (K := M)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup M).map M.subtype with hT
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 2 T M := ⟨Q, rfl⟩
  have hScT : Sc ≤ T := by
    rw [hT, ← Subgroup.map_subgroupOf_eq_of_le hScM]
    exact Subgroup.map_mono hQ
  refine ⟨T, h, hTsyl, ?_⟩
  have heq : T ⊓ Subgroup.centralizer {c} = Sc := by
    refine (hSc.eq_of_le (le_inf hScT (hSc.le.trans inf_le_right)) ?_ ?_).symm.symm
    · exact inf_le_inf_right _ hTsyl.le
    · exact hTsyl.isPGroup.to_le inf_le_left
  rw [heq]
  exact hSc

omit [Finite G] in
theorem le_normalizer_normalClosureIn (M : Subgroup G) (c : G) :
    M ≤ Subgroup.normalizer (normalClosureIn M c : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ normalClosureIn M c, m * x * m⁻¹ ∈ normalClosureIn M c := by
    intro m hm x hx
    have hle : normalClosureIn M c ≤
        (normalClosureIn M c).comap (MulAut.conj m).toMonoidHom := by
      rw [normalClosureIn, Subgroup.closure_le]
      rintro _ ⟨m', hm', rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine Subgroup.subset_closure ⟨m * m', M.mul_mem hm hm', ?_⟩
      change m * (m' * c * m'⁻¹) * m⁻¹ = m * m' * c * (m * m')⁻¹
      group
    exact hle hx
  intro m hm
  exact Sec18.mem_normalizer_of_conj_mem (key m hm) (key m⁻¹ (M.inv_mem hm))


end CFSG.RankThree.PartTwo.Sec20
