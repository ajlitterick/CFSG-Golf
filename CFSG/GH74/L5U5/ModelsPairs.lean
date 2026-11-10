module

public import CFSG.GH74.L5U5.ModelsInvolution
public import CFSG.ClassicalInvolution.WeakCT.Standard

public section

namespace CFSG.GH74.L5U5

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockMat_apply_blockIdx blockIdx)
open scoped MatrixGroups

section BlockMat

variable {F : Type} [Field F]

theorem e4_symm_zero : e4.symm (0 : Fin 4) = Sum.inl 0 := rfl

theorem e4_symm_one : e4.symm (1 : Fin 4) = Sum.inl 1 := rfl

theorem e4_symm_two : e4.symm (2 : Fin 4) = Sum.inr 0 := rfl

theorem e4_symm_three : e4.symm (3 : Fin 4) = Sum.inr 1 := rfl

theorem blk4_apply (X Y : Matrix (Fin 2) (Fin 2) F) (a b : Fin 4) :
    blk4 X Y a b = fromBlocks X 0 0 Y (e4.symm a) (e4.symm b) := rfl


end BlockMat

section Transport

variable {F : Type} [Field F]

theorem linearBlockStandardPair_map' {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : LinearBlockStandardPair F W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    LinearBlockStandardPair F (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, h'⟩ := h
  refine ⟨φ.comp θ, c, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · rwa [MonoidHom.ker_comp_of_injective θ φ hφ]
  · rcases h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩
    · right
      rw [← Subgroup.map_map, ← Subgroup.map_map, h1, h2]
      exact ⟨rfl, rfl⟩

theorem weakCTSystem_map_equiv {X Y : Type} [Group X] [Group Y] {n : ℕ}
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X} (h : WeakCTSystem F n U W)
    (e : X ≃* Y) :
    WeakCTSystem F n (fun i => (U i).map e.toMonoidHom)
      (fun i j => (W i j).map e.toMonoidHom) where
  iso i := by
    obtain ⟨φ⟩ := h.iso i
    exact ⟨φ.trans ((U i).equivMapOfInjective e.toMonoidHom e.injective)⟩
  join i j hij := by rw [h.join i j hij, Subgroup.map_sup]
  comm i j hij := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h.comm i j hij x hx y hy]
  pair i j hj := linearBlockStandardPair_map' (h.pair i j hj) e.toMonoidHom e.injective
  gen := by
    rw [← Subgroup.map_iSup, h.gen]
    exact Subgroup.map_top_of_surjective _ e.surjective

end Transport

section Linear

variable {F : Type} [Field F]


end Linear

section Middle

variable {F : Type} [Field F]


@[expose] def elem12 : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩


end Middle

section SystemLin

variable {F : Type} [Field F] [Finite F]


theorem comm_of_center {K : Type} [Group K] {x y z : K} (hx : x ∈ Subgroup.center K)
    (h : y * z = z * y) : x * y * z = z * (x * y) := by
  have hz : z * x = x * z := Subgroup.mem_center_iff.1 hx z
  calc x * y * z = x * (y * z) := mul_assoc _ _ _
    _ = x * (z * y) := by rw [h]
    _ = (x * z) * y := (mul_assoc _ _ _).symm
    _ = (z * x) * y := by rw [hz]
    _ = z * (x * y) := mul_assoc _ _ _


end SystemLin

section StandardPairThree


end StandardPairThree

end CFSG.GH74.L5U5
