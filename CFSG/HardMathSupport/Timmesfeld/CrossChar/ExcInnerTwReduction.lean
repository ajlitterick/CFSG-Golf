module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerF4Toral

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {τ : Tag} {L : Type} [Field L]


theorem exists_rootChar_eq_one_of_finite
    {p : ℕ} (hp : p.Prime) {B : Subgroup (ModGL τ L)} [Finite B]
    (hB : B ≤ torusGroup τ L) (hpow : ∀ x ∈ B, x ^ p = 1) (hcard : p < Nat.card B)
    (α : Fin τ.rank → ℤ) :
    ∃ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ B ∧ rootDiagUnit τ a ≠ 1 ∧ rootChar a α = 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  by_contra hne
  push Not at hne
  set T₀ := B.comap (rootDiagUnitHom τ L) with hT₀
  have : Finite T₀ := Finite.of_injective (fun a : T₀ => (⟨rootDiagUnit τ a, a.2⟩ : B))
    fun a b h => Subtype.ext (rootDiagUnit_injective (congrArg Subtype.val h))
  let χ : (Fin τ.rank → Lˣ) →* Lˣ :=
    { toFun := fun a => rootChar a α
      map_one' := by simp [rootChar]
      map_mul' := fun a b => by simp only [rootChar, Pi.mul_apply, mul_zpow,
        Finset.prod_mul_distrib] }
  have h1 : Nat.card B ≤ Nat.card T₀ := by
    refine Nat.card_le_card_of_surjective (fun a : T₀ => (⟨rootDiagUnit τ a, a.2⟩ : B)) ?_
    rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := torusGroup_le_range_rootDiagUnitHom (hB hb)
    exact ⟨⟨a, hb⟩, rfl⟩
  have hker : ∀ a ∈ T₀, χ a = 1 → a = 1 := by
    intro a ha hχa
    by_contra ha1
    exact hne a ha (fun h => ha1 (rootDiagUnit_injective (h.trans rootDiagUnit_one.symm))) hχa
  have hpowa : ∀ a ∈ T₀, a ^ p = 1 := by
    intro a ha
    have h2 : rootDiagUnit τ (a ^ p) = rootDiagUnit τ a ^ p := map_pow (rootDiagUnitHom τ L) a p
    have h3 : rootDiagUnit τ a ^ p = 1 := hpow _ ha
    exact rootDiagUnit_injective (by rw [h2, h3, rootDiagUnit_one])
  let f : T₀ → rootsOfUnity p L := fun a => ⟨χ a, by
    rw [mem_rootsOfUnity, ← map_pow, hpowa a a.2, map_one]⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h3 : χ ((a : Fin τ.rank → Lˣ) * (b : Fin τ.rank → Lˣ)⁻¹) = 1 := by
      have : χ a = χ b := congrArg (fun z : rootsOfUnity p L => (z : Lˣ)) hab
      rw [map_mul, map_inv, this, mul_inv_cancel]
    have h4 := hker _ (T₀.mul_mem a.2 (T₀.inv_mem b.2)) h3
    exact Subtype.ext (mul_inv_eq_one.1 h4)
  have h5 := Nat.card_le_card_of_injective f hf
  have h6 := card_rootsOfUnity L p
  omega

theorem isSubnormal_inf_subgroupOf {G : Type*} [Group G] {S T : Subgroup G}
    (hS : (S.subgroupOf T).IsSubnormal) (A : Subgroup G) :
    ((S ⊓ A).subgroupOf (T ⊓ A)).IsSubnormal := by
  convert hS.comap (Subgroup.inclusion (inf_le_left : T ⊓ A ≤ T)) using 1
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.coe_inclusion,
    Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, (Subgroup.mem_inf.1 x.2).2⟩⟩


end CFSG.HardMathSupport.Timmesfeld.CrossChar
