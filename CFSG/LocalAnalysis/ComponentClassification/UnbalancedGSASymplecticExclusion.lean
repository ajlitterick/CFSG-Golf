module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalDihedral
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd.Symplectic
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Matrix CFSG.Assembly.LowTwoRank

namespace SymplecticExclusion

theorem exists_quaternion_of_hom {S G : Type*} [Group S] [Group G] (φ : S →* G) {x y z : S}
    (hz2 : z ^ 2 = 1) (hx : x ^ 2 = z) (hy : y ^ 2 = z) (hxy : x * y = z * (y * x))
    (hz : φ z ≠ 1) : ∃ H : Subgroup G, Nonempty (H ≃* QuaternionGroup 2) := by
  have hz2' : φ z ^ 2 = 1 := by rw [← map_pow φ, hz2, map_one]
  have hx' : φ x ^ 2 = φ z := by rw [← map_pow φ, hx]
  have hy' : φ y ^ 2 = φ z := by rw [← map_pow φ, hy]
  have hxy' : φ x * φ y = φ z * (φ y * φ x) := by
    rw [← map_mul φ, hxy, map_mul φ, map_mul φ]
  obtain ⟨H, -, -, ⟨e⟩⟩ :=
    LocalAnalysis.ComponentInitial.exists_quaternion_subgroup_of_anticommuting hz hz2' hx' hy'
      hxy'
  exact ⟨H, ⟨e.symm⟩⟩

theorem exists_quaternion_of_sl2_hom {k G : Type*} [Field k] [Finite k] [Group G]
    (hk : ringChar k ≠ 2) (φ : SpecialLinearGroup (Fin 2) k →* G) (hφ : φ (-1) ≠ 1) :
    ∃ H : Subgroup G, Nonempty (H ≃* QuaternionGroup 2) := by
  obtain ⟨a, b, hab⟩ := LocalAnalysis.ComponentInitial.finite_odd_field_two_squares hk (-1)
  obtain ⟨x, y, -, -, hx, hy, hxy⟩ :=
    LocalAnalysis.ComponentInitial.sl2_exists_anticommuting_pair hab
  exact exists_quaternion_of_hom φ (by rw [neg_one_sq]) hx hy hxy hφ

variable {K : Type} [Field K] {n : ℕ}

@[expose] def famMat (X : Fin n → Matrix (Fin 2) (Fin 2) K) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  fromBlocks (diagonal fun j => X j 0 0) (diagonal fun j => X j 0 1)
    (diagonal fun j => X j 1 0) (diagonal fun j => X j 1 1)

theorem famMat_one : famMat (1 : Fin n → Matrix (Fin 2) (Fin 2) K) = 1 := by
  simp only [famMat, Pi.one_apply, one_apply_eq, one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]
  rw [diagonal_one, diagonal_zero, fromBlocks_one]

theorem famMat_mul (X Y : Fin n → Matrix (Fin 2) (Fin 2) K) :
    famMat (X * Y) = famMat X * famMat Y := by
  simp only [famMat, fromBlocks_multiply, diagonal_mul_diagonal, diagonal_add]
  congr 1 <;> congr 1 <;> funext j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def famHom : (Fin n → Matrix (Fin 2) (Fin 2) K) →*
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K where
  toFun := famMat
  map_one' := famMat_one
  map_mul' := famMat_mul

theorem famMat_symplectic {X : Fin n → Matrix (Fin 2) (Fin 2) K} (hX : ∀ j, (X j).det = 1) :
    (famMat X)ᵀ * fromBlocks 0 1 (-1) 0 * famMat X = fromBlocks 0 1 (-1) 0 := by
  have hX' : ∀ j, X j 0 0 * X j 1 1 - X j 0 1 * X j 1 0 = 1 := fun j => by
    rw [← det_fin_two]
    exact hX j
  simp only [famMat, fromBlocks_transpose, diagonal_transpose, fromBlocks_multiply,
    Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add, add_zero, neg_mul,
    diagonal_mul_diagonal, diagonal_neg, diagonal_add]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩ <;> ext a b <;>
    simp only [diagonal_apply, Matrix.zero_apply, Matrix.one_apply, Matrix.neg_apply] <;>
    split_ifs <;> first | rfl | ring1 | linear_combination hX' a | linear_combination -hX' a

@[expose] noncomputable def planeGL (i : Fin n) :
    SpecialLinearGroup (Fin 2) K →* GL (Fin n ⊕ Fin n) K :=
  (Units.map ((famHom (K := K) (n := n)).comp
    (MonoidHom.mulSingle (fun _ => Matrix (Fin 2) (Fin 2) K) i))).comp
    SpecialLinearGroup.toGL


theorem planeGL_mem (i : Fin n) (B : SpecialLinearGroup (Fin 2) K) :
    planeGL i B ∈ StatedSp n K := by
  refine Subgroup.subset_closure ?_
  change (famMat (Pi.mulSingle i (B : Matrix (Fin 2) (Fin 2) K)))ᵀ * fromBlocks 0 1 (-1) 0 *
    famMat (Pi.mulSingle i (B : Matrix (Fin 2) (Fin 2) K)) = fromBlocks 0 1 (-1) 0
  refine famMat_symplectic fun j => ?_
  by_cases hj : j = i
  · subst hj
    rw [Pi.mulSingle_eq_same]
    exact B.2
  · rw [Pi.mulSingle_eq_of_ne hj, det_one]

@[expose] noncomputable def planeProj (i : Fin n) :
    SpecialLinearGroup (Fin 2) K →* StatedProj (StatedSp n K) :=
  (QuotientGroup.mk' ((StatedScalars (Fin n ⊕ Fin n) K).subgroupOf (StatedSp n K))).comp
    ((planeGL i).codRestrict (StatedSp n K) (planeGL_mem i))


end SymplecticExclusion

open SymplecticExclusion


end CFSG.ComponentClassification.UnbalancedGS
