module

public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.LangPrimeFieldInvolutionTorus
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.LieType.AlgebraicGroups.RationalCentralizerCocycle

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]


end Group

section Weyl

variable {τ : Tag} {K : Type} [Field K]

@[expose] def weylTuple
    (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) : Fin τ.rank → Kˣ :=
  fun i => rootChar b (w⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ))

theorem rootChar_weylTuple
    (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) (u : Fin τ.rank → ℤ) :
    rootChar (weylTuple w b) u = rootChar b (w⁻¹ • u) := by
  conv_rhs => rw [pi_eq_sum_univ u]
  rw [Finset.smul_sum, rootChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : (fun j => if i = j then (1 : ℤ) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [e, smul_comm, rootChar_zsmul]
  rfl

theorem canonicalRep_conj_rootDiagUnit
    (w : WeylGroup τ) (b : Fin τ.rank → Kˣ) :
    canonicalRep (coxeterSystem τ) K w * rootDiagUnit τ b *
        (canonicalRep (coxeterSystem τ) K w)⁻¹ = rootDiagUnit τ (weylTuple w b) :=
  ((rootDiagUnit_eq_conj_canonicalRep_iff (weylTuple w b) b w).2 fun v => by
    rw [rootChar_weylTuple, inv_smul_smul]).symm

theorem weylTuple_weylTuple
    (w w' : WeylGroup τ) (b : Fin τ.rank → Kˣ) :
    weylTuple w (weylTuple w' b) = weylTuple (w * w') b := by
  funext i
  simp only [weylTuple]
  rw [rootChar_weylTuple, mul_inv_rev, mul_smul]

theorem weylTuple_one
    (b : Fin τ.rank → Kˣ) : weylTuple (1 : WeylGroup τ) b = b := by
  funext i
  simp only [weylTuple, inv_one, one_smul]
  simpa using rootChar_nsmul_single b i 1

theorem rootChar_sq_eq_one {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i ^ 2 = 1) (u : Fin τ.rank → ℤ) :
    rootChar b u ^ 2 = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem weylTuple_sq_eq_one
    {b : Fin τ.rank → Kˣ} (hb : ∀ i, b i ^ 2 = 1) (w : WeylGroup τ)
    (i : Fin τ.rank) : weylTuple w b i ^ 2 = 1 :=
  rootChar_sq_eq_one hb _

end Weyl

section Aux

theorem commutator_subgroupOf_normal {G : Type*} [Group G] (R : Subgroup G) :
    (⁅R, R⁆.subgroupOf R).Normal := by
  have hcomm : ⁅R, R⁆.subgroupOf R = commutator R := by
    rw [← Subgroup.map_subtype_commutator, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective R.subtype_injective]
  rw [hcomm]
  infer_instance

theorem isSolvable_quotient_commutator_subgroupOf {G : Type*} [Group G] (R : Subgroup G)
    [(⁅R, R⁆.subgroupOf R).Normal] : Group.IsSolvable (R ⧸ ⁅R, R⁆.subgroupOf R) := by
  refine Group.isSolvable_of_comm fun a b => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have e : (((x * y)⁻¹ * (y * x) : R) : G) = ⁅(y : G)⁻¹, (x : G)⁻¹⁆ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def, inv_inv, mul_inv_rev]
    group
  rw [e]
  exact Subgroup.commutator_mem_commutator (inv_mem y.2) (inv_mem x.2)

theorem exists_intUnit_eq_of_sq_eq_one {L : Type*} [Field L] {u : Lˣ} (hu : u ^ 2 = 1) :
    ∃ s : ℤˣ, Units.map (Int.castRingHom L).toMonoidHom s = u := by
  have h : (u : L) * u = 1 := by
    rw [← Units.val_mul, ← sq, hu, Units.val_one]
  rcases mul_self_eq_one_iff.1 h with h1 | h1
  · exact ⟨1, Units.ext (by simp [h1])⟩
  · exact ⟨-1, Units.ext (by simp [h1])⟩

end Aux

section Select

variable {G : Type*} [Group G]


end Select

section SignDiag

variable {τ : Tag} {L : Type} [Field L]

theorem rootDiagUnit_conj_rootDiagUnit (a b : Fin τ.rank → Lˣ) :
    rootDiagUnit τ a * rootDiagUnit τ b * (rootDiagUnit τ a)⁻¹ = rootDiagUnit τ b := by
  rw [← rootDiagUnit_mul, mul_comm a b, rootDiagUnit_mul, mul_inv_cancel_right]

variable (τ L) in
@[expose] def signDiagGroup : Subgroup (ModGL τ L) :=
  ((rootDiagUnitHom τ L).comp (MonoidHom.compLeft (intUnitsMap L) (Fin τ.rank))).range

theorem mem_signDiagGroup {y : ModGL τ L} :
    y ∈ signDiagGroup τ L ↔ ∃ b : Fin τ.rank → Lˣ, (∀ i, b i ^ 2 = 1) ∧ rootDiagUnit τ b = y := by
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨fun i => intUnitsMap L (s i), fun i => ?_, rfl⟩
    rw [← map_pow, Int.units_sq, map_one]
  · rintro ⟨b, hb, rfl⟩
    choose s hs using fun i => exists_intUnit_eq_of_sq_eq_one (hb i)
    exact ⟨s, congrArg (rootDiagUnit τ) (funext hs)⟩

theorem card_signDiagGroup
    (hL : ringChar L ≠ 2) :
    Nat.card (signDiagGroup τ L) = 2 ^ τ.rank := by
  have hinj : Function.Injective
      ((rootDiagUnitHom τ L).comp (MonoidHom.compLeft (intUnitsMap L) (Fin τ.rank))) := by
    intro s s' h
    change rootDiagUnit τ (fun i => intUnitsMap L (s i)) =
      rootDiagUnit τ (fun i => intUnitsMap L (s' i)) at h
    funext i
    exact intUnitsMap_injective hL (congrFun (rootDiagUnit_injective h) i)
  rw [signDiagGroup, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int, Nat.card_fin]


theorem signDiagGroup_mul_self {y : ModGL τ L} (hy : y ∈ signDiagGroup τ L) : y * y = 1 := by
  obtain ⟨b, hb, rfl⟩ := mem_signDiagGroup.1 hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_one]
  congr 1
  funext i
  rw [Pi.mul_apply, ← pow_two, hb, Pi.one_apply]


theorem canonicalRep_conj_conj_of_mul_self
    {w : WeylGroup τ} (hw : w * w = 1)
    (b : Fin τ.rank → Lˣ) :
    canonicalRep (coxeterSystem τ) L w *
        (canonicalRep (coxeterSystem τ) L w * rootDiagUnit τ b *
          (canonicalRep (coxeterSystem τ) L w)⁻¹) *
        (canonicalRep (coxeterSystem τ) L w)⁻¹ = rootDiagUnit τ b := by
  rw [canonicalRep_conj_rootDiagUnit, canonicalRep_conj_rootDiagUnit, weylTuple_weylTuple, hw,
    weylTuple_one]


end SignDiag


end CFSG.LieType.Chevalley
