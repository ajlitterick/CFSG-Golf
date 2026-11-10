module

public import CFSG.ClassicalInvolution.SubnormalClosure.Basic
public import CFSG.Blueprint.Catalog
import CFSG.ClassicalInvolution.OrderForm
import CFSG.GroupTheory.NonabelianSimpleOrderSixty
import CFSG.LocalAnalysis.ComponentClassification.LocalComponents

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open
open scoped MatrixGroups


section Witness

theorem classicalInvolutionWitness_of_mulEquiv {A B : Type*} [Group A] [Group B]
    {JA : Subgroup A} {JB : Subgroup B} (e : JA ≃* JB) (h : classicalInvolutionWitness JA) :
    classicalInvolutionWitness JB := by
  have hO : (classicalInvolutionOddCore JA).map e.toMonoidHom = classicalInvolutionOddCore JB :=
    CFSG.ComponentClassification.OddCore.equiv_invariant e
  let q : JA ⧸ classicalInvolutionOddCore JA ≃* JB ⧸ classicalInvolutionOddCore JB :=
    QuotientGroup.congr _ _ e hO
  have hZ : (Subgroup.center (JA ⧸ classicalInvolutionOddCore JA)).map q.toMonoidHom =
      Subgroup.center (JB ⧸ classicalInvolutionOddCore JB) := Subgroup.map_center_eq q
  rcases h with ⟨p, n, hp, hp2, hn, ⟨φ⟩⟩ | ⟨hqs, hcard, ⟨ψ⟩⟩
  · exact Or.inl ⟨p, n, hp, hp2, hn, ⟨q.symm.trans φ⟩⟩
  · refine Or.inr ⟨CFSG.ComponentClassification.Components.quasisimple_of_equiv q.symm hqs, ?_,
      ⟨(QuotientGroup.congr _ _ q hZ).symm.trans ψ⟩⟩
    rw [← hcard, ← hZ]
    exact Subgroup.card_map_of_injective q.injective

end Witness

section Closure

variable {G : Type*} [Group G]

theorem isComponentOf_top_of_normal_simple (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFnonab : ∃ a b : F, a * b ≠ b * a) : IsComponentOf F ⊤ := by
  have : Group.IsPerfect F :=
    ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top F hFnonab⟩
  exact ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
    CFSG.ComponentClassification.Quasisimple.simple_of_perfect F⟩

theorem le_subnormalClosure_of_isComponentOf [Finite G] {F K : Subgroup G}
    (hF : IsComponentOf F ⊤) (hC : Subgroup.centralizer (F : Set G) = ⊥) (hK : K ≠ ⊥) :
    F ≤ subnormalClosure K := by
  rcases CFSG.ComponentClassification.LocalComponents.subnormal_contains_or_commutes F
      (subnormalClosure K) hF (isSubnormal_subnormalClosure K) with h | h
  · exact h
  · rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, hC] at h
    exact (hK (le_bot_iff.mp ((le_subnormalClosure K).trans h))).elim

theorem eq_of_isQuasisimple_of_le {F H : Subgroup G} [F.Normal] (hFH : F ≤ H)
    (hH : CFSG.Open.IsQuasisimple H) (hFnonab : ∃ a b : F, a * b ≠ b * a) : H = F := by
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hH
    (F.subgroupOf H) with hcen | htop
  · obtain ⟨a, b, hab⟩ := hFnonab
    refine (hab ?_).elim
    have := Subgroup.mem_center_iff.mp (hcen (show (⟨a.1, hFH a.2⟩ : H) ∈ F.subgroupOf H from a.2))
      ⟨b.1, hFH b.2⟩
    exact Subtype.ext (congrArg Subtype.val this).symm
  · exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hFH

theorem subgroupOf_centralizer_inf {H : Subgroup G} {z : G} (hz : z ∈ H) :
    (Subgroup.centralizer ({z} : Set G) ⊓ H).subgroupOf H =
      Subgroup.centralizer ({(⟨z, hz⟩ : H)} : Set H) := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Set.mem_singleton_iff, forall_eq]
  exact ⟨fun hx => Subtype.ext hx.1, fun hx => ⟨congrArg Subtype.val hx, x.2⟩⟩

end Closure


end CFSG.ClassicalInvolution
