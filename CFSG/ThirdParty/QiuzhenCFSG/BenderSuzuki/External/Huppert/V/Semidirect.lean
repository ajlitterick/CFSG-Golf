module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Remaining
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection8.theorem_8_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.MinimalNormal
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.Algebra.Field.ULift

namespace CFSG
end CFSG
open CFSG
namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v
public theorem hkt_regularSemidirect_range_inl_normal
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A] :
    ((SemidirectProduct.inl :
      A →* A ⋊[MulDistribMulAction.toMulAut B A] B).range).Normal := by
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

public theorem hkt_regularSemidirect_range_inl_inf_range_inr_eq_bot
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A] :
    (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B)) ⊓
      (MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B)) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  rcases hxA with ⟨a, ha⟩
  rcases hxB with ⟨b, hb⟩
  have hab :
      (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) a :
          A ⋊[MulDistribMulAction.toMulAut B A] B) =
        SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) b := by
    exact ha.trans hb.symm
  have ha_one : a = 1 := by
    have hleft := congrArg SemidirectProduct.left hab
    simpa using hleft
  have hx_one : x = 1 := by
    rw [← ha]
    simp [ha_one]
  simp [hx_one]


public theorem hkt_regularSemidirect_range_inl_isComplement_range_inr
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A] :
    (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B)).IsComplement'
      (MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B)) := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · rw [disjoint_iff_inf_le]
    exact (hkt_regularSemidirect_range_inl_inf_range_inr_eq_bot (A := A) (B := B)).le
  · ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      rw [Set.mem_mul]
      refine ⟨SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) x.left,
        ?_, SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) x.right,
        ?_, ?_⟩
      · exact ⟨x.left, rfl⟩
      · exact ⟨x.right, rfl⟩
      · exact SemidirectProduct.inl_left_mul_inr_right x

public theorem hkt_regularSemidirect_range_inl_ne_bot_of_nontrivial
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A]
    [Nontrivial A] :
    MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B) ≠ ⊥ := by
  rcases exists_ne (1 : A) with ⟨a, ha⟩
  intro hbot
  have ha_mem :
      (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) a :
          A ⋊[MulDistribMulAction.toMulAut B A] B) ∈
        (⊥ : Subgroup (A ⋊[MulDistribMulAction.toMulAut B A] B)) := by
    rw [← hbot]
    exact ⟨a, rfl⟩
  have ha_one : a = 1 := by
    have h := Subgroup.mem_bot.mp ha_mem
    have hleft := congrArg SemidirectProduct.left h
    simpa using hleft
  exact ha ha_one

public theorem hkt_regularSemidirect_range_inr_ne_bot_of_nontrivial
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A]
    [Nontrivial B] :
    MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B) ≠ ⊥ := by
  rcases exists_ne (1 : B) with ⟨b, hb⟩
  intro hbot
  have hb_mem :
      (SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) b :
          A ⋊[MulDistribMulAction.toMulAut B A] B) ∈
        (⊥ : Subgroup (A ⋊[MulDistribMulAction.toMulAut B A] B)) := by
    rw [← hbot]
    exact ⟨b, rfl⟩
  have hb_one : b = 1 := by
    have h := Subgroup.mem_bot.mp hb_mem
    have hright := congrArg SemidirectProduct.right h
    simpa using hright
  exact hb hb_one

public theorem hkt_regularSemidirect_range_inr_elementCentralizerIn_range_inl_eq_bot
    {A B : Type*} [Group A] [Group B] [MulDistribMulAction B A]
    (hregular : ActsRegularly B A)
    (x :
      MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B))
    (hx : x ≠ 1) :
    elementCentralizerIn
      (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B))
      (x : A ⋊[MulDistribMulAction.toMulAut B A] B) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  rcases x.property with ⟨b, hb⟩
  have hb_ne : b ≠ 1 := by
    intro hb_one
    apply hx
    apply Subtype.ext
    simpa [hb_one] using hb.symm
  rcases hy with ⟨hyA, hycent⟩
  rcases hyA with ⟨a, ha⟩
  have hcomm :
      (SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) a :
          A ⋊[MulDistribMulAction.toMulAut B A] B) *
          SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) b =
        SemidirectProduct.inr (φ := MulDistribMulAction.toMulAut B A) b *
          SemidirectProduct.inl (φ := MulDistribMulAction.toMulAut B A) a := by
    have hcomm_yx : (y : A ⋊[MulDistribMulAction.toMulAut B A] B) * (x : _) =
        (x : A ⋊[MulDistribMulAction.toMulAut B A] B) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hycent
    simpa [ha, hb] using hcomm_yx
  have hfix : b • a = a := by
    have hleft := congrArg SemidirectProduct.left hcomm
    simpa using hleft.symm
  have ha_fixed : a ∈ fixedPointSubgroup (↥(Subgroup.zpowers b)) A := by
    rw [FixedPoints.mem_subgroup]
    intro z
    exact smul_eq_self_of_mem_zpowers z.2 hfix
  have ha_bot : a ∈ (⊥ : Subgroup A) := by
    simpa [hregular b hb_ne] using ha_fixed
  have ha_one : a = 1 := Subgroup.mem_bot.mp ha_bot
  rw [← ha]
  simp [ha_one]

public theorem hkt_regularSemidirect_isFrobenius
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [MulDistribMulAction B A] [Nontrivial A] [Nontrivial B]
    (hregular : ActsRegularly B A) :
    IsFrobeniusGroupWithKernelComplement
      (MonoidHom.range
        (SemidirectProduct.inl :
          A →* A ⋊[MulDistribMulAction.toMulAut B A] B))
      (MonoidHom.range
        (SemidirectProduct.inr :
          B →* A ⋊[MulDistribMulAction.toMulAut B A] B)) := by
  let φ : B →* MulAut A := MulDistribMulAction.toMulAut B A
  let SD := A ⋊[φ] B
  let : Finite SD := Finite.of_equiv (A × B) (SemidirectProduct.equivProd (φ := φ)).symm
  let K : Subgroup SD := MonoidHom.range (SemidirectProduct.inl : A →* SD)
  let R : Subgroup SD := MonoidHom.range (SemidirectProduct.inr : B →* SD)
  change IsFrobeniusGroupWithKernelComplement K R
  exact
    (lemma_3_1 (K := K) (R := R)
      (by
        simpa [K, SD, φ] using
          hkt_regularSemidirect_range_inl_ne_bot_of_nontrivial (A := A) (B := B))
      (by
        simpa [R, SD, φ] using
          hkt_regularSemidirect_range_inr_ne_bot_of_nontrivial (A := A) (B := B))
      (by
        simpa [K, SD, φ] using
          hkt_regularSemidirect_range_inl_normal (A := A) (B := B))
      (by
        simpa [K, R, SD, φ] using
          hkt_regularSemidirect_range_inl_isComplement_range_inr (A := A) (B := B))).2
      (by
        intro x hx
        simpa [K, R, SD, φ] using
          hkt_regularSemidirect_range_inr_elementCentralizerIn_range_inl_eq_bot
            (A := A) (B := B) hregular x hx)


public theorem hkt_mulAut_pow_apply_iterate
    {Q : Type u} [Group Q] (φ : MulAut Q) (n : ℕ) (q : Q) :
    (φ ^ n) q = (fun q : Q => φ q)^[n] q := by
  induction n generalizing q with
  | zero => simp
  | succ n ih =>
      simp [pow_succ, Function.iterate_succ, ih]


/-- A subgroup invariant under the HKT automorphism is mapped onto itself. -/
public theorem hkt_invariant_subgroup_map_eq
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q)
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) :
    N.map (φ : Q →* Q) = N := by
  apply le_antisymm
  · intro q hq
    rcases Subgroup.mem_map.mp hq with ⟨x, hx, rfl⟩
    exact (hN x).mp hx
  · intro q hq
    refine Subgroup.mem_map.mpr ⟨φ⁻¹ q, ?_, by simp⟩
    exact (hN (φ⁻¹ q)).mpr (by simpa using hq)

/-- Induced HKT automorphism on the quotient by an invariant normal subgroup. -/
@[expose]
public def invariantQuotientAut
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Normal]
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) : MulAut (Q ⧸ N) :=
  QuotientGroup.congr (G' := N) (H' := N) (e := φ)
    (hkt_invariant_subgroup_map_eq φ N hN)

/-- Representative formula for the induced HKT quotient automorphism. -/
public theorem invariantQuotientAut_mk'
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Normal]
    (hN : ∀ q : Q, q ∈ N ↔ φ q ∈ N) (q : Q) :
    invariantQuotientAut φ N hN (QuotientGroup.mk' N q) =
      QuotientGroup.mk' N (φ q) := by
  rfl


/-- A characteristic subgroup is invariant under the HKT automorphism. -/
public theorem hkt_characteristic_subgroup_invariant
    {Q : Type u} [Group Q] (φ : MulAut Q) (N : Subgroup Q) [N.Characteristic] :
    ∀ q : Q, q ∈ N ↔ φ q ∈ N := by
  intro q
  have hmap : N.map (φ : Q →* Q) = N :=
    Subgroup.characteristic_iff_map_eq.mp (inferInstance : N.Characteristic) φ
  constructor
  · intro hq
    have : φ q ∈ N.map (φ : Q →* Q) :=
      Subgroup.mem_map_of_mem (φ : Q →* Q) hq
    simpa [hmap] using this
  · intro hq
    have hmap' : N.map (φ.symm : Q →* Q) = N :=
      Subgroup.characteristic_iff_map_eq.mp (inferInstance : N.Characteristic) φ.symm
    have : φ.symm (φ q) ∈ N.map (φ.symm : Q →* Q) :=
      Subgroup.mem_map_of_mem (φ.symm : Q →* Q) hq
    simpa [hmap'] using this


/-- A helper instance: a normal subgroup is characteristic enough for mapping characteristic
subgroups of it into the ambient group as normal subgroups. -/
public theorem hkt_map_characteristic_of_normal_normal
    {Q : Type u} [Group Q] (M : Subgroup Q) [M.Normal]
    (K : Subgroup M) [K.Characteristic] :
    ((K.map M.subtype : Subgroup Q).Normal) := by
  infer_instance


/-- A cyclic subgroup generated by one element is cyclic. -/
public theorem isCyclic_zpowers {G : Type u} [Group G] (g : G) :
    IsCyclic (Subgroup.zpowers g) :=
  Subgroup.isCyclic_zpowers g


end External
end CFSG.BenderSuzuki
