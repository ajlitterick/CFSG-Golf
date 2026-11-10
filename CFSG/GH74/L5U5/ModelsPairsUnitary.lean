module

public import CFSG.GH74.L5U5.ModelsPairs
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.GH74.L5U5

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply blockMat_apply_blockIdx blockIdx)
open CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg CFSG.LieType.BorelTits
open scoped MatrixGroups

section Transport

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

theorem unitaryBlockStandardPair_map' {X Y : Type} [Group X] [Group Y] {W U V : Subgroup X}
    (h : Phan.UnitaryBlockStandardPair F p f W U V) (φ : X →* Y) (hφ : Function.Injective φ) :
    Phan.UnitaryBlockStandardPair F p f (W.map φ) (U.map φ) (V.map φ) := by
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

theorem weakPhanA_map_equiv {X Y : Type} [Group X] [Group Y] {n : ℕ}
    {U : Fin n → Subgroup X} {W : Fin n → Fin n → Subgroup X}
    (h : Phan.WeakPhanA F p f n U W) (e : X ≃* Y) :
    Phan.WeakPhanA F p f n (fun i => (U i).map e.toMonoidHom)
      (fun i j => (W i j).map e.toMonoidHom) where
  iso i := by
    obtain ⟨φ⟩ := h.iso i
    exact ⟨φ.trans ((U i).equivMapOfInjective e.toMonoidHom e.injective)⟩
  join i j hij := by rw [h.join i j hij, Subgroup.map_sup]
  comm i j hij := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, h.comm i j hij x hx y hy]
  pair i j hj := unitaryBlockStandardPair_map' (h.pair i j hj) e.toMonoidHom e.injective
  gen := by
    rw [← Subgroup.map_iSup, h.gen]
    exact Subgroup.map_top_of_surjective _ e.surjective

end Transport

section Blocks

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

@[expose] noncomputable def suEquiv (n : ℕ) : Phan.Su F p f n ≃* ↥(StatedSU n (p ^ f) F) :=
  MulEquiv.subgroupCongr (SUid_eq_statedSU hF n)

theorem coe_suEquiv (n : ℕ) (x : Phan.Su F p f n) :
    ((suEquiv hF n x : ↥(StatedSU n (p ^ f) F)) : GL (Fin n) F) = (x : GL (Fin n) F) := rfl

theorem mem_uni_H2_iff {a : GL (Fin 2) F} :
    a ∈ (ModelData.uni hF).H2 ↔ a ∈ SUid (unitaryInvolution F p f) 2 := by
  change a ∈ StatedSU 2 (p ^ f) F ↔ _
  rw [← SUid_eq_statedSU hF 2]


end Blocks

section SystemUni

open CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices CFSG.GH74.Filter.ClassicalOdd

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

@[expose] noncomputable def negSu : Phan.Su F p f 2 :=
  ⟨(-1 : GL (Fin 2) F), (mem_uni_H2_iff hF).1 (ModelData.neg_one_mem_H2 _)⟩


omit [Finite F] [Fact p.Prime] [CharP F p] in
theorem coe_coe_negSu_aux : (((-1 : GL (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) = -1 := by
  simp

theorem coe_negSu : (((negSu hF : Phan.Su F p f 2) : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    -1 := coe_coe_negSu_aux

theorem negSu_mul_self : negSu hF * negSu hF = 1 :=
  Subtype.ext (by
    change (-1 : GL (Fin 2) F) * (-1 : GL (Fin 2) F) = 1
    rw [neg_mul_neg, one_mul])

theorem negSu_ne_one (h2 : (2 : F) ≠ 0) : negSu hF ≠ 1 := fun h =>
  ModelData.neg_one_ne_one_gl2 h2 (congrArg Subtype.val h)

theorem orderOf_negSu (h2 : (2 : F) ≠ 0) : orderOf (negSu hF) = 2 :=
  orderOf_eq_prime (by rw [sq]; exact negSu_mul_self hF) (negSu_ne_one hF h2)


end SystemUni

section StandardPairThree


end StandardPairThree

end CFSG.GH74.L5U5
