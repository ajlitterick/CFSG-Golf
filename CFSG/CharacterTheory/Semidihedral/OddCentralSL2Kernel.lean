module

public import CFSG.CharacterTheory.Semidihedral.OddProjectiveCoverKernel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralLiftStructure

public section

namespace CFSG.Semidihedral.OddCentralSL2Kernel

universe u v

section QuotientKernel

variable {J : Type u} {H : Type v} [Group J] [Group H]

@[expose] def quotientProjection (β : J →* H)
    (N : Subgroup J) [N.Normal] (D : Subgroup H) [D.Normal]
    (himage : N.map β = D) : J ⧸ N →* H ⧸ D :=
  QuotientGroup.map N D β (by
    intro j hj
    rw [← himage]
    exact Subgroup.mem_map.mpr ⟨j, hj, rfl⟩)


theorem quotientProjection_surjective (β : J →* H) (hβ : Function.Surjective β)
    (N : Subgroup J) [N.Normal] (D : Subgroup H) [D.Normal]
    (himage : N.map β = D) : Function.Surjective (quotientProjection β N D himage) := by
  intro x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective D x
  obtain ⟨j, rfl⟩ := hβ h
  exact ⟨QuotientGroup.mk' N j, rfl⟩


theorem quotientProjection_ker (β : J →* H)
    (N : Subgroup J) [N.Normal] (D : Subgroup H) [D.Normal]
    (himage : N.map β = D) :
    (quotientProjection β N D himage).ker = β.ker.map (QuotientGroup.mk' N) := by
  rw [quotientProjection, QuotientGroup.ker_map, ← himage, Subgroup.comap_map_eq,
    Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]

theorem kernel_quotient_subgroupMap_injective (β : J →* H)
    (N : Subgroup J) [N.Normal] (hdisjoint : Disjoint β.ker N) :
    Function.Injective ((QuotientGroup.mk' N).subgroupMap β.ker) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  apply le_antisymm _ bot_le
  intro e he
  exact Subgroup.mem_bot.mpr (Subtype.ext
    (Subgroup.disjoint_def.mp hdisjoint e.property he))

@[expose] noncomputable def kernelQuotientEquiv (β : J →* H)
    (N : Subgroup J) [N.Normal] (D : Subgroup H) [D.Normal]
    (himage : N.map β = D) (hdisjoint : Disjoint β.ker N) :
    β.ker ≃* (quotientProjection β N D himage).ker :=
  (MulEquiv.ofBijective ((QuotientGroup.mk' N).subgroupMap β.ker)
    ⟨kernel_quotient_subgroupMap_injective β N hdisjoint,
      (QuotientGroup.mk' N).subgroupMap_surjective β.ker⟩).trans
    (MulEquiv.subgroupCongr (quotientProjection_ker β N D himage).symm)


theorem quotientProjection_ker_central (β : J →* H)
    (hcentral : β.ker ≤ Subgroup.center J)
    (N : Subgroup J) [N.Normal] (D : Subgroup H) [D.Normal]
    (himage : N.map β = D) :
    (quotientProjection β N D himage).ker ≤ Subgroup.center (J ⧸ N) := by
  rw [quotientProjection_ker]
  exact (Subgroup.map_mono hcentral).trans
    (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N))


end QuotientKernel

section CentralInvolution

open CFSG.ShultStronglyClosedTI

variable {J : Type u} {H : Type v} [Group J] [Group H]

theorem odd_kernel_disjoint_central_involution (β : J →* H)
    (hodd : Odd (Nat.card β.ker)) (t : Subgroup.center J)
    (ht : orderOf (t : J) = 2) : Disjoint β.ker (centralLiftKernel t) := by
  apply Subgroup.disjoint_of_coprime_natCard
  rw [centralLiftKernel_card_two t ht]
  exact Nat.coprime_two_right.mpr hodd


end CentralInvolution

section SpecialLinear

open Matrix CFSG.ShultStronglyClosedTI CFSG.Semidihedral.ProjectiveSL2Cover

variable (F : Type v) [Field F] {J : Type u} [Group J]

theorem central_involution_image_eq_scalars (β : J →* SpecialLinearGroup (Fin 2) F)
    (t : Subgroup.center J) (hβt : β t = minusIdentity F) :
    (centralLiftKernel t).map β = nativeScalarKernel F 2 := by
  change (Subgroup.zpowers (t : J)).map β = nativeScalarKernel F 2
  rw [MonoidHom.map_zpowers, hβt, nativeScalarKernel_two_eq_zpowers]

@[expose] def involutionScalarProjection (β : J →* SpecialLinearGroup (Fin 2) F)
    (t : Subgroup.center J) (hβt : β t = minusIdentity F) :
    J ⧸ centralLiftKernel t →* NativeScalarProjective F 2 :=
  quotientProjection β (centralLiftKernel t) (nativeScalarKernel F 2)
    (central_involution_image_eq_scalars F β t hβt)


theorem involutionScalarProjection_surjective (β : J →* SpecialLinearGroup (Fin 2) F)
    (hβ : Function.Surjective β) (t : Subgroup.center J)
    (hβt : β t = minusIdentity F) :
    Function.Surjective (involutionScalarProjection F β t hβt) :=
  quotientProjection_surjective β hβ _ _ (central_involution_image_eq_scalars F β t hβt)


@[expose] noncomputable def oddKernelScalarQuotientEquiv
    (β : J →* SpecialLinearGroup (Fin 2) F) (hodd : Odd (Nat.card β.ker))
    (t : Subgroup.center J) (ht : orderOf (t : J) = 2)
    (hβt : β t = minusIdentity F) : β.ker ≃* (involutionScalarProjection F β t hβt).ker :=
  kernelQuotientEquiv β _ _ (central_involution_image_eq_scalars F β t hβt)
    (odd_kernel_disjoint_central_involution β hodd t ht)


theorem involutionScalarProjection_ker_card
    (β : J →* SpecialLinearGroup (Fin 2) F) (hodd : Odd (Nat.card β.ker))
    (t : Subgroup.center J) (ht : orderOf (t : J) = 2)
    (hβt : β t = minusIdentity F) :
    Nat.card (involutionScalarProjection F β t hβt).ker = Nat.card β.ker :=
  (Nat.card_congr (oddKernelScalarQuotientEquiv F β hodd t ht hβt).toEquiv).symm

theorem involutionScalarProjection_ker_central
    (β : J →* SpecialLinearGroup (Fin 2) F) (hcentral : β.ker ≤ Subgroup.center J)
    (t : Subgroup.center J) (hβt : β t = minusIdentity F) :
    (involutionScalarProjection F β t hβt).ker ≤ Subgroup.center (J ⧸ centralLiftKernel t) :=
  quotientProjection_ker_central β hcentral _ _
    (central_involution_image_eq_scalars F β t hβt)

theorem involutionScalarProjection_ker_odd
    (β : J →* SpecialLinearGroup (Fin 2) F) (hodd : Odd (Nat.card β.ker))
    (t : Subgroup.center J) (ht : orderOf (t : J) = 2)
    (hβt : β t = minusIdentity F) :
    Odd (Nat.card (involutionScalarProjection F β t hβt).ker) := by
  rw [involutionScalarProjection_ker_card F β hodd t ht hβt]
  exact hodd


end SpecialLinear

section DefiningPrimeKernel

open Matrix CFSG.ShultStronglyClosedTI CFSG.Semidihedral.ProjectiveSL2Cover

variable {J : Type u} [Group J] [Finite J] [Group.IsPerfect J]
variable (F : Type v) [Field F]

theorem central_odd_SL2_cover_kernel_bounds
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f)
    (β : J →* SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (htorder : orderOf t = 2)
    (htβ : β t = OddFieldSL2.minusIdentity F) :
    (p ^ f ≠ 9 → β.ker = ⊥) ∧
      (p ^ f = 9 → IsCyclic β.ker ∧ Nat.card β.ker ≤ 3) := by
  let : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; omega)
  let z : Subgroup.center J := ⟨t, ht⟩
  have hzβ : β z = minusIdentity F := by
    simpa only [minusIdentity_eq_neg_one, OddFieldSL2.minusIdentity] using htβ
  let π := involutionScalarProjection F β z hzβ
  have hπ : Function.Surjective π := involutionScalarProjection_surjective F β hβ z hzβ
  have hπcentral : π.ker ≤ Subgroup.center (J ⧸ centralLiftKernel z) :=
    involutionScalarProjection_ker_central F β hcentral z hzβ
  have hπodd : Odd (Nat.card π.ker) :=
    involutionScalarProjection_ker_odd F β hodd z htorder hzβ
  have hbound := OddProjectiveCoverKernel.odd_projective_linear_two_perfect_odd_cover_kernel
    F hp hpodd hf hF π hπ hπcentral hπodd
  let e := oddKernelScalarQuotientEquiv F β hodd z htorder hzβ
  have hcard : Nat.card π.ker = Nat.card β.ker := (Nat.card_congr e.toEquiv).symm
  constructor
  · intro hnine
    apply β.ker.eq_bot_iff_card.mpr
    rw [← hcard, hbound.1 hnine, Subgroup.card_bot]
  · intro hnine
    have h := hbound.2 hnine
    let : IsCyclic π.ker := h.1
    exact ⟨isCyclic_of_injective e.toMonoidHom e.injective, hcard ▸ h.2⟩

theorem central_odd_SL2_cover_kernel_isPGroup
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) (hq : 5 ≤ p ^ f)
    (β : J →* SpecialLinearGroup (Fin 2) F) (hβ : Function.Surjective β)
    (hcentral : β.ker ≤ Subgroup.center J) (hodd : Odd (Nat.card β.ker))
    (t : J) (ht : t ∈ Subgroup.center J) (htorder : orderOf t = 2)
    (htβ : β t = OddFieldSL2.minusIdentity F) : IsPGroup p β.ker := by
  have hbound := central_odd_SL2_cover_kernel_bounds F hp hpodd hf hF hq β hβ
    hcentral hodd t ht htorder htβ
  by_cases hnine : p ^ f = 9
  · have hp3 : p = 3 := (OddProjectiveCoverKernel.prime_power_nine hp hf hnine).1
    have hcardle := (hbound.2 hnine).2
    have hcardpos : 0 < Nat.card β.ker := Nat.card_pos
    have hcardcases : Nat.card β.ker = 1 ∨ Nat.card β.ker = 3 := by
      obtain ⟨n, hn⟩ := hodd
      omega
    rcases hcardcases with hone | hthree
    · exact IsPGroup.of_card (n := 0) (by simpa using hone)
    · exact IsPGroup.of_card (n := 1) (by simpa [hp3] using hthree)
  · exact IsPGroup.of_card (n := 0) (by rw [hbound.1 hnine, Subgroup.card_bot, pow_zero])

end DefiningPrimeKernel

end CFSG.Semidihedral.OddCentralSL2Kernel
