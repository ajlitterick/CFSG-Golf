module

public import CFSG.LocalAnalysis.ZStar.OddNormalBlock
public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG

namespace ZStar.PrincipalBlockKernel

open ZStar.Helpers ZStar.OddNormalBlock

universe u v

variable {G : Type u} [Group G] [Fintype G]
variable {V : Type v} [AddCommMonoid V] [Module (ZMod 2) V]

@[expose] def PrincipalBlockActsAsIdentity
    (ρ : Representation (ZMod 2) G V) : Prop :=
  ρ.asAlgebraHom (principalBlockCandidate G) =
    (1 : Module.End (ZMod 2) V)

theorem oddNormal_action_eq_one
    (ρ : Representation (ZMod 2) G V)
    (hρ : PrincipalBlockActsAsIdentity ρ)
    (N : Subgroup G) [N.Normal] (hNodd : Odd (Nat.card N))
    (n : N) :
    ρ (n : G) = (1 : Module.End (ZMod 2) V) := by
  have hfix := single_mul_principalBlockCandidate_of_mem N hNodd n
  have hmap := congrArg ρ.asAlgebraHom hfix
  change ρ.asAlgebraHom (principalBlockCandidate G) = 1 at hρ
  simpa only [map_mul, Representation.asAlgebraHom_single_one, hρ,
    mul_one] using hmap


end ZStar.PrincipalBlockKernel

end CFSG
