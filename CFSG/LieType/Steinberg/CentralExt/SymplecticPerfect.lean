module

public import CFSG.LieType.Steinberg.CentralExt.Model
public import CFSG.LieType.Steinberg.CentralExt.Families
public import CFSG.ClassicalGroups.Symplectic.Model
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public section

namespace CFSG.LieType.Steinberg

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.ClassicalGroups.Symplectic

theorem card_statedScalars_subgroupOf_statedSp_le_two (n : ℕ) (K : Type) [Field K] :
    Nat.card ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K)) ≤ 2 := by
  refine card_le_two_of_forall_scalar
    (φ := (StatedSp n K).subtype.comp (Subgroup.subtype _))
    (Subtype.val_injective.comp Subtype.val_injective) fun g => ?_
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 g.2
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨1, one_pow 2, Subsingleton.elim _ _⟩
  have hmat : (((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Matrix.scalar (Fin n ⊕ Fin n) (c : K) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hsp : ((g : StatedSp n K) : GL (Fin n ⊕ Fin n) K) ∈ TauCeti.GLSymplectic (Fin n) K := by
    rw [← statedSp_eq_GLSymplectic]
    exact (g : StatedSp n K).2
  rw [TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup, hmat,
    scalar_mem_symplecticGroup_iff hn] at hsp
  exact ⟨c, hsp, hmat⟩


end CFSG.LieType.Steinberg
