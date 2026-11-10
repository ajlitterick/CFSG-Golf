module

public import CFSG.RankThree.PartTwo.Sec13.Notation
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13

section Auto

variable {G : Type*} [Group G]

@[expose] def transvectionGroup (A : Subgroup G) (c : A) : Subgroup (MulAut A) where
  carrier := {σ | σ c = c ∧ ∀ a : A, σ a * a⁻¹ ∈ Subgroup.zpowers c}
  mul_mem' {σ τ} hσ hτ := by
    refine ⟨by simp [hσ.1, hτ.1], fun a => ?_⟩
    have h : (σ * τ) a * a⁻¹ = (σ (τ a) * (τ a)⁻¹) * (τ a * a⁻¹) := by
      simp [mul_assoc]
    rw [h]
    exact Subgroup.mul_mem _ (hσ.2 (τ a)) (hτ.2 a)
  one_mem' := ⟨rfl, fun a => by simp⟩
  inv_mem' {σ} hσ := by
    refine ⟨?_, fun a => ?_⟩
    · conv_lhs => rw [← hσ.1]
      simp
    · have h := Subgroup.inv_mem _ (hσ.2 (σ⁻¹ a))
      simpa [mul_inv_rev] using h

theorem mem_transvectionGroup_iff {A : Subgroup G} {c : A} {σ : MulAut A} :
    σ ∈ transvectionGroup A c ↔ σ c = c ∧ ∀ a : A, σ a * a⁻¹ ∈ Subgroup.zpowers c :=
  Iff.rfl

end Auto

section Bar

variable {G : Type*} [Group G] [Finite G]

@[expose] noncomputable def lBar (c : G) (L : Subgroup G) :
    Subgroup (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⧸
      aschbacherSolvableCore 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G))) :=
  (L.subgroupOf (Subgroup.normalizer (Subgroup.zpowers c : Set G))).map (QuotientGroup.mk' _)

@[expose] noncomputable def lcBar (c : G) (L : Subgroup G) : Subgroup G :=
  ((lBar c L ⊔ Subgroup.centralizer (lBar c L : Set _)).comap (QuotientGroup.mk' _)).map
    (Subgroup.normalizer (Subgroup.zpowers c : Set G)).subtype

end Bar

structure Sec12Std (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop extends PartTwoStanding G where
  partTwoF_eq : partTwoF G = partTwoE G
  isE27 : Late.IsE27 A
  mem_A : c ∈ A
  ne_one : c ≠ 1
  mem_thetaComponentsAt : L ∈ thetaComponentsAt 3 c
  mem_L : c ∈ L
  card_B : Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set G)) = 9
  sup_eq : (A ⊓ Subgroup.centralizer (L : Set G)) ⊔ (A ⊓ L) = A
  exists_sylow : ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) ∧
    ¬ A ⊓ Subgroup.centralizer (L : Set G) ≤ (Subgroup.center P).map P.subtype


@[expose] def Item122 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec12Std G A c L →
      Sec4.IsSLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) (alternatingGroup (Fin 7)) ∨
      Sec4.IsTripleCover (L ⧸ aschbacherSolvableCore 3 L) CFSG.Blueprint.NativeSporadic.M22


end CFSG.RankThree.PartTwo.Sec12
