module

public import CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.WeylConj
public import CFSG.Quasithin.Recognition.CertG2TwoOuter
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.EvenRootCommutatorG2

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open


open CFSG.Quasithin in
def burnsideF4c_qIdx : List ℕ := [0, 5, 6, 7, 8, 9, 11, 12, 18, 20, 21, 23, 24, 25, 26, 31]

open CFSG.Quasithin in
theorem burnsideF4c_qIdx_lt : ∀ i ∈ burnsideF4c_qIdx, i < 32 := by decide


open CFSG.Quasithin in
theorem burnsideF4c_Q_norm_perm :
    ∀ k ∈ [0, 1, 2, 4], ∀ i ∈ burnsideF4c_qIdx,
      (∃ j ∈ burnsideF4c_qIdx,
        u33GenP k * u33Tel u33GenP i * (u33GenP k)⁻¹ = u33Tel u33GenP j) ∧
      (∃ j ∈ burnsideF4c_qIdx,
        (u33GenP k)⁻¹ * u33Tel u33GenP i * u33GenP k = u33Tel u33GenP j) := by
  decide +kernel


open CFSG.Quasithin in
def burnsideF4c_Qset : Set U33G :=
  {g | ∃ i ∈ burnsideF4c_qIdx, u33Tel u33GenPG i = g}

open CFSG.Quasithin in
theorem burnsideF4c_Tel_mem_T
    (i : ℕ) (hi : i < 32) : u33Tel u33GenPG i ∈ u33Data.T :=
  u33Data.Tel_mem_T ⟨i, hi⟩

open CFSG.Quasithin in
theorem burnsideF4c_Qset_le_T
    : Subgroup.closure burnsideF4c_Qset ≤ u33Data.T := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, hi, rfl⟩
  exact burnsideF4c_Tel_mem_T i (burnsideF4c_qIdx_lt i hi)

open CFSG.Quasithin in
theorem burnsideF4c_gen_norm
    (k : ℕ) (hk : k ∈ [0, 1, 2, 4]) :
    u33GenPG k ∈ Subgroup.normalizer (Subgroup.closure burnsideF4c_Qset : Set U33G) := by
  apply mem_normalizer_closure_of
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨⟨j, hj, hjeq⟩, -⟩ := burnsideF4c_Q_norm_perm k hk i hi
    refine ⟨j, hj, ?_⟩
    apply u33PresHom_injective
    simpa only [map_mul, map_inv, u33Tel_hom, u33PresHom_genPG] using hjeq.symm
  · rintro _ ⟨i, hi, rfl⟩
    obtain ⟨-, ⟨j, hj, hjeq⟩⟩ := burnsideF4c_Q_norm_perm k hk i hi
    refine ⟨j, hj, ?_⟩
    apply u33PresHom_injective
    simpa only [map_mul, map_inv, u33Tel_hom, u33PresHom_genPG] using hjeq.symm


section G2Bridge

variable {K : Type} [Field K] [CharP K 2]

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

end G2Bridge

section Transport

variable {G H : Type*} [Group G] [Group H]

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

end Transport

section Assembly

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc in

end Assembly


abbrev burnsideF4c_SL : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def burnsideF4c_ent (A : burnsideF4c_SL) (i j : Fin 3) : ZMod 2 :=
  (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j

@[expose] def burnsideF4c_inP (A : burnsideF4c_SL) : Prop :=
  burnsideF4c_ent A 1 0 = 0 ∧ burnsideF4c_ent A 2 0 = 0

@[expose] def burnsideF4c_inL (A : burnsideF4c_SL) : Prop :=
  burnsideF4c_ent A 2 0 = 0 ∧ burnsideF4c_ent A 2 1 = 0

instance : DecidablePred burnsideF4c_inP := fun A => inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred burnsideF4c_inL := fun A => inferInstanceAs (Decidable (_ ∧ _))

theorem burnsideF4c_inP_mul (A B : burnsideF4c_SL) (hA : burnsideF4c_inP A)
    (hB : burnsideF4c_inP B) : burnsideF4c_inP (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  unfold burnsideF4c_inP burnsideF4c_ent at *
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hA1, hA2, hB1, hB2]

theorem burnsideF4c_inL_mul (A B : burnsideF4c_SL) (hA : burnsideF4c_inL A)
    (hB : burnsideF4c_inL B) : burnsideF4c_inL (A * B) := by
  obtain ⟨hA1, hA2⟩ := hA
  obtain ⟨hB1, hB2⟩ := hB
  unfold burnsideF4c_inL burnsideF4c_ent at *
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three, hA1, hA2, hB1, hB2]

theorem burnsideF4c_inP_inv : ∀ A : burnsideF4c_SL, burnsideF4c_inP A → burnsideF4c_inP A⁻¹ := by
  decide +kernel

theorem burnsideF4c_inL_inv : ∀ A : burnsideF4c_SL, burnsideF4c_inL A → burnsideF4c_inL A⁻¹ := by
  decide +kernel

@[expose] def burnsideF4c_P : Subgroup burnsideF4c_SL where
  carrier := {A | burnsideF4c_inP A}
  one_mem' := by decide +kernel
  mul_mem' := fun {A B} hA hB => burnsideF4c_inP_mul A B hA hB
  inv_mem' := fun {A} hA => burnsideF4c_inP_inv A hA

@[expose] def burnsideF4c_L : Subgroup burnsideF4c_SL where
  carrier := {A | burnsideF4c_inL A}
  one_mem' := by decide +kernel
  mul_mem' := fun {A B} hA hB => burnsideF4c_inL_mul A B hA hB
  inv_mem' := fun {A} hA => burnsideF4c_inL_inv A hA

instance : DecidablePred (· ∈ burnsideF4c_P) := fun A => inferInstanceAs (Decidable (burnsideF4c_inP A))
instance : DecidablePred (· ∈ burnsideF4c_L) := fun A => inferInstanceAs (Decidable (burnsideF4c_inL A))
instance : DecidablePred (· ∈ burnsideF4c_P ⊓ burnsideF4c_L) :=
  fun A => inferInstanceAs (Decidable (A ∈ burnsideF4c_P ∧ A ∈ burnsideF4c_L))


abbrev burnsideF4c_V : Type := {v : Fin 3 → ZMod 2 // v ≠ 0}

instance : MulAction burnsideF4c_SL burnsideF4c_V where
  smul A v := ⟨A • (v : Fin 3 → ZMod 2), by
    intro h
    exact v.2 ((smul_eq_zero_iff_eq A).1 h)⟩
  one_smul v := Subtype.ext (one_smul _ _)
  mul_smul A B v := Subtype.ext (mul_smul A B (v : Fin 3 → ZMod 2))


section Step


end Step


section Vertices


end Vertices


section Trans


end Trans


section Transport


end Transport

section Classify


end Classify


section PartA


end PartA


section Pull


end Pull

section Iso


end Iso


section Iso0


end Iso0


end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open

section


end


end CFSG.ASVolI
