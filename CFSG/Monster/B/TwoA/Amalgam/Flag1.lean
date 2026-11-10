module

public import CFSG.Monster.B.TwoA.Amalgam.Flag1Native

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Fischer CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
  CFSG.Monster.B.TwoA.Unitary Module
open scoped Pointwise

@[expose] def actP1
    (g : Pc 0) (S : Submodule F4 V6) : Submodule F4 V6 := sigmaAct S (rhoP1 g)⁻¹

theorem actP1_mul
    (g h : Pc 0) (S : Submodule F4 V6) : actP1 (g * h) S = actP1 g (actP1 h S) := by
  rw [actP1, actP1, actP1, map_mul, mul_inv_rev, sigmaAct_mul]

theorem actP1_one
    (S : Submodule F4 V6) : actP1 1 S = S := by
  rw [actP1, map_one, inv_one, sigmaAct_one]

theorem actP1_inv_actP1
    (g : Pc 0) (S : Submodule F4 V6) : actP1 g⁻¹ (actP1 g S) = S := by
  rw [← actP1_mul, inv_mul_cancel, actP1_one]

theorem actP1_mono
    {S S' : Submodule F4 V6} (h : S ≤ S') (g : Pc 0) : actP1 g S ≤ actP1 g S' :=
  sigmaAct_mono h _

theorem finrank_actP1
    (g : Pc 0) (S : Submodule F4 V6) :
    finrank F4 (actP1 g S) = finrank F4 S :=
  finrank_sigmaAct S _

theorem UIso.actP1
    {d : ℕ} {S : Submodule F4 V6} (h : UIso d S) (g : Pc 0) :
    UIso d (actP1 g S) :=
  h.sigmaAct _

theorem exists_actP1_eq
    (x : SigmaU6) : ∃ g : Pc 0, ∀ S, actP1 g S = sigmaAct S x := by
  obtain ⟨g, hg⟩ := rhoP1_surjective x⁻¹
  exact ⟨g, fun S => by rw [actP1, hg, inv_inv]⟩

theorem actP1_eq_self_iff
    {O : Submodule F4 V6} (g : Pc 0) :
    actP1 g O = O ↔ g ∈ (sigStab O).comap rhoP1 := by
  rw [Subgroup.mem_comap, ← Subgroup.inv_mem_iff]
  exact Iff.rfl

theorem actP1_Tsp_iff
    (g : Pc 0) : actP1 g Tsp = Tsp ↔ g ∈ (Pc 1).subgroupOf (Pc 0) := by
  rw [Pc_one_subgroupOf]
  exact actP1_eq_self_iff g

theorem actP1_Hsp_iff
    (g : Pc 0) : actP1 g Hsp = Hsp ↔ g ∈ (Pc 2).subgroupOf (Pc 0) := by
  rw [Pc_two_subgroupOf]
  exact actP1_eq_self_iff g

theorem actP1_Rsp_iff
    (g : Pc 0) : actP1 g Rsp = Rsp ↔ g ∈ (Pc 3).subgroupOf (Pc 0) := by
  rw [Pc_three_subgroupOf]
  exact actP1_eq_self_iff g

theorem exists_actP1_flag
    {R H T : Submodule F4 V6} (hR : UIso 1 R) (hH : UIso 2 H)
    (hT : UIso 3 T) (hRH : R ≤ H) (hHT : H ≤ T) :
    ∃ g : Pc 0, actP1 g Rsp = R ∧ actP1 g Hsp = H ∧ actP1 g Tsp = T := by
  obtain ⟨g', h1, h2, h3⟩ := exists_SUh_flag hR hH hT hRH hHT
  obtain ⟨g, hg⟩ := exists_actP1_eq (suElt g')
  exact ⟨g, (hg Rsp).trans h1, (hg Hsp).trans h2, (hg Tsp).trans h3⟩

theorem exists_actP1_Tsp
    {S : Submodule F4 V6} (hS : UIso 3 S) : ∃ g : Pc 0, actP1 g Tsp = S := by
  obtain ⟨R, H, hR, hH, hRH, hHS⟩ := exists_flag_of_three hS
  obtain ⟨g, -, -, h⟩ := exists_actP1_flag hR hH hS hRH hHS
  exact ⟨g, h⟩


theorem exists_actP1_Rsp
    {S : Submodule F4 V6} (hS : UIso 1 S) : ∃ g : Pc 0, actP1 g Rsp = S := by
  obtain ⟨H, T, hH, hT, hSH, hHT⟩ := exists_flag_of_one hS
  obtain ⟨g, h, -, -⟩ := exists_actP1_flag hS hH hT hSH hHT
  exact ⟨g, h⟩


theorem actP1_eq_of_mem
    {A : Subgroup (Pc 0)} {O : Submodule F4 V6}
    (hA : ∀ g, actP1 g O = O ↔ g ∈ A) {g x : Pc 0} (hx : g⁻¹ * x ∈ A) : actP1 x O = actP1 g O := by
  calc actP1 x O = actP1 g (actP1 (g⁻¹ * x) O) := by rw [← actP1_mul, mul_inv_cancel_left]
    _ = actP1 g O := by rw [(hA _).2 hx]

theorem le_of_incident
    {A B : Subgroup (Pc 0)} {O O' : Submodule F4 V6}
    (hA : ∀ g, actP1 g O = O ↔ g ∈ A) (hB : ∀ g, actP1 g O' = O' ↔ g ∈ B) (hle : O' ≤ O)
    {g h : Pc 0} (hgh : ∃ x : Pc 0, g⁻¹ * x ∈ A ∧ h⁻¹ * x ∈ B) : actP1 h O' ≤ actP1 g O := by
  obtain ⟨x, hxA, hxB⟩ := hgh
  rw [← actP1_eq_of_mem hA hxA, ← actP1_eq_of_mem hB hxB]
  exact actP1_mono hle x

theorem incidence_iff
    {A B : Subgroup (Pc 0)} {O O' : Submodule F4 V6}
    (hA : ∀ g, actP1 g O = O ↔ g ∈ A) (hB : ∀ g, actP1 g O' = O' ↔ g ∈ B) (hle : O' ≤ O)
    (hd : finrank F4 O' < finrank F4 O)
    (htr : ∀ g : Pc 0, actP1 g O' ≤ O → ∃ z : Pc 0, actP1 z O = O ∧ actP1 z O' = actP1 g O')
    (g h : Pc 0) :
    (g • (A : Set (Pc 0)) ∩ h • (B : Set (Pc 0))).Nonempty ↔
      (actP1 g O ≤ actP1 h O' ∨ actP1 h O' ≤ actP1 g O) := by
  have hmem : (g • (A : Set (Pc 0)) ∩ h • (B : Set (Pc 0))).Nonempty ↔
      ∃ x : Pc 0, g⁻¹ * x ∈ A ∧ h⁻¹ * x ∈ B := by
    simp only [Set.Nonempty, Set.mem_inter_iff, mem_leftCoset_iff, SetLike.mem_coe]
  rw [hmem]
  constructor
  · intro hx
    exact Or.inr (le_of_incident hA hB hle hx)
  · rintro (hle' | hle')
    · exfalso
      have := Submodule.finrank_mono hle'
      rw [finrank_actP1, finrank_actP1] at this
      omega
    · have h1 : actP1 (g⁻¹ * h) O' ≤ O := by
        rw [actP1_mul]
        have := actP1_mono hle' g⁻¹
        rwa [actP1_inv_actP1] at this
      obtain ⟨z, hzO, hzO'⟩ := htr _ h1
      refine ⟨g * z, ?_, ?_⟩
      · rw [inv_mul_cancel_left]
        exact (hA z).1 hzO
      · apply (hB _).1
        rw [actP1_mul, actP1_mul, hzO', ← actP1_mul g, mul_inv_cancel_left, actP1_inv_actP1]


theorem htr_TR
    (g : Pc 0) (hg : actP1 g Rsp ≤ Tsp) :
    ∃ z : Pc 0, actP1 z Tsp = Tsp ∧ actP1 z Rsp = actP1 g Rsp := by
  obtain ⟨H, hH, hSH, hHT⟩ := exists_flag_of_one_three (uIso_Rsp.actP1 g) uIso_Tsp hg
  obtain ⟨z, h1, -, h3⟩ := exists_actP1_flag (uIso_Rsp.actP1 g) hH uIso_Tsp hSH hHT
  exact ⟨z, h3, h1⟩


instance Nc_zero_subgroupOf_normal :
    ((Nc 0).subgroupOf (Pc 0)).Normal :=
  ker_rhoP1 ▸ rhoP1.normal_ker

theorem Nc_zero_subgroupOf_le
    (j : Fin 4) : (Nc 0).subgroupOf (Pc 0) ≤ (Pc j).subgroupOf (Pc 0) :=
  fun _ hg => Nc_le_Pc 0 j hg

theorem mem_Nc_zero_of_fix
    {x : Pc 0} (hx : ∀ S : Submodule F4 V6, UIso 3 S → actP1 x S = S) :
    (x : Dfull) ∈ Nc 0 := by
  have h1 : (rhoP1 x)⁻¹ = 1 := eq_one_of_sigmaAct_plane _ fun j => hx _ (isMaxIso_plane j)
  have h2 : x ∈ rhoP1.ker := by
    rw [MonoidHom.mem_ker]
    exact inv_eq_one.1 h1
  rw [ker_rhoP1] at h2
  exact h2

theorem normalCore_Pc_one :
    ((Pc 1).subgroupOf (Pc 0)).normalCore = (Nc 0).subgroupOf (Pc 0) := by
  refine le_antisymm (fun x hx => ?_) (Subgroup.normal_le_normalCore.2 (Nc_zero_subgroupOf_le 1))
  rw [Subgroup.mem_subgroupOf]
  apply mem_Nc_zero_of_fix
  intro S hS
  obtain ⟨c, rfl⟩ := exists_actP1_Tsp hS
  have h := (actP1_Tsp_iff _).2 (hx c⁻¹)
  rw [inv_inv, actP1_mul, actP1_mul] at h
  have h' := congrArg (actP1 c) h
  rwa [← actP1_mul c c⁻¹, mul_inv_cancel, actP1_one] at h'


end CFSG.Monster.B.TwoA.Amalgam
