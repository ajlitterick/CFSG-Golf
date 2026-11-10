module

public import CFSG.Monster.B.Dyadic.Beta

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Dyadic

open Module CFSG.Monster.B.Dyadic.Native CFSG.Monster.B.Binary.Native
open scoped Matrix


variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module ℚ V]
  (R : Basis (Fin 4371) ℚ V) (ρ : G →* (V ≃ₗ[ℚ] V))


variable (hΛ : ∀ s, ∀ x ∈ Lam R, ρ s x ∈ Lam R)


theorem beta_range_eq
    (gens : Fin 26 → G) (hgen : Subgroup.closure (Set.range gens) = ⊤)
    (hact : ∀ g t, (ρ (gens g) : V →ₗ[ℚ] V) (R t) =
      ∑ u : Fin 4371, ((numer g t u : ℚ) / 8) • R u)
    (hf : ∀ s, modRep R ρ hΛ s (fbar R) = fbar R) :
    (beta R ρ hΛ hf).range = Subgroup.closure {u : GL (Fin 4370) (ZMod 2) |
      ∃ g : Fin 26, (u : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = (Qmat g).transpose} := by
  rw [beta_range R ρ hΛ gens hgen hf]
  refine congrArg Subgroup.closure (Set.ext fun u => ?_)
  rw [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g, beta_gen R ρ hΛ gens hact hf g⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, Units.ext ((beta_gen R ρ hΛ gens hact hf g).trans hg.symm)⟩

end CFSG.Monster.B.Dyadic
