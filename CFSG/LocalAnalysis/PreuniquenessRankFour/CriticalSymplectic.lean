module

public import CFSG.LocalAnalysis.PreuniquenessRankFour.CriticalSubgroup
public import CFSG.LocalAnalysis.PreuniquenessRankFour.AlternatingForm

public section

open CFSG.Open
open CFSG.Open
open scoped commutatorElement

namespace CFSG.PreuniquenessRankFour.Helpers

universe u v

theorem prime_card_two_group_action_trivial
    {acting : Type u} {source : Type v}
    [Group acting] [Group source] [Finite source] [MulDistribMulAction acting source]
    (hcard : Nat.card source = 2) :
    ∀ scalar : acting, ∀ member : source, scalar • member = member := by
  let : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  let : IsCyclic source := isCyclic_of_prime_card hcard
  have hautCard : Nat.card (MulAut source) = 1 := by
    rw [IsCyclic.card_mulAut, hcard]
    norm_num
  have hsubsingleton : Subsingleton (MulAut source) :=
    (Nat.card_eq_one_iff_unique.mp hautCard).1
  intro scalar member
  exact congrArg (fun equivalence : MulAut source => equivalence member)
    (hsubsingleton.elim (MulDistribMulAction.toMulAut acting source scalar) 1)


@[expose] def multiplicative_action_zmod_linear_aut
    {acting : Type u} {source : Type v}
    [Group acting] [CommGroup source] [MulDistribMulAction acting source]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] :
    acting →* (Additive source ≃ₗ[ZMod prime] Additive source) where
  toFun scalar :=
    { toLinearMap := AddMonoidHom.toZModLinearMap prime
        (MonoidHom.toAdditive (MulDistribMulAction.toMulAut acting source scalar).toMonoidHom)
      invFun := fun member => Additive.ofMul (scalar⁻¹ • member.toMul)
      left_inv := fun member => by
        change Additive.ofMul (scalar⁻¹ • (scalar • member.toMul)) = member
        rw [inv_smul_smul]
        rfl
      right_inv := fun member => by
        change Additive.ofMul (scalar • (scalar⁻¹ • member.toMul)) = member
        rw [smul_inv_smul]
        rfl }
  map_one' := by
    apply LinearEquiv.ext
    intro member
    change Additive.ofMul ((1 : acting) • member.toMul) = member
    rw [one_smul]
    rfl
  map_mul' first second := by
    apply LinearEquiv.ext
    intro member
    change Additive.ofMul ((first * second) • member.toMul) =
      Additive.ofMul (first • (second • member.toMul))
    rw [mul_smul]

theorem multiplicative_action_zmod_linear_aut_kernel
    {acting : Type u} {source : Type v}
    [Group acting] [CommGroup source] [MulDistribMulAction acting source]
    (prime : ℕ) [Module (ZMod prime) (Additive source)] :
    (multiplicative_action_zmod_linear_aut (acting := acting) (source := source) prime).ker =
      (MulDistribMulAction.toMulAut acting source).ker := by
  apply Subgroup.ext
  intro scalar
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hequal
    apply MulEquiv.ext
    intro member
    exact congrArg Additive.toMul
      (congrArg (fun equivalence : Additive source ≃ₗ[ZMod prime] Additive source =>
        equivalence (Additive.ofMul member)) hequal)
  · intro hequal
    apply LinearEquiv.ext
    intro member
    exact congrArg Additive.ofMul
      (congrArg (fun equivalence : MulAut source => equivalence member.toMul) hequal)

theorem faithful_multiplicative_action_zmod_linear_aut
    {acting : Type u} {source : Type v}
    [Group acting] [CommGroup source] [MulDistribMulAction acting source]
    (prime : ℕ) [Module (ZMod prime) (Additive source)]
    (hfaithful : Function.Injective (MulDistribMulAction.toMulAut acting source)) :
    Function.Injective (multiplicative_action_zmod_linear_aut (acting := acting) (source := source) prime) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [multiplicative_action_zmod_linear_aut_kernel]
  exact MonoidHom.ker_eq_bot _ hfaithful

theorem quotient_hom_injective_of_kernel_eq
    {source : Type u} {target : Type v} [Group source] [Group target]
    (normal : Subgroup source) [normal.Normal] (hom : source →* target)
    (hkernel : hom.ker = normal) :
    ∃ embedding : (source ⧸ normal) →* target,
      Function.Injective embedding ∧
        ∀ member : source, embedding ((QuotientGroup.mk' normal) member) = hom member := by
  let embedding := QuotientGroup.lift normal hom (le_of_eq hkernel.symm)
  have hinjective : Function.Injective embedding := by
    apply embedding.ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_lift, hkernel]
    apply le_antisymm _ bot_le
    rintro member ⟨lift, hlift, rfl⟩
    exact (QuotientGroup.eq_one_iff lift).mpr hlift
  exact ⟨embedding, hinjective, fun member => QuotientGroup.lift_mk' normal (le_of_eq hkernel.symm) member⟩


end CFSG.PreuniquenessRankFour.Helpers
