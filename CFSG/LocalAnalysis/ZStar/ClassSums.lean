module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import CFSG.LocalAnalysis.ZStar.CharacterContradiction

public section

namespace CFSG

namespace ZStar.ClassSums

noncomputable section

universe u v w

variable {G : Type u} [Group G] [Fintype G]

local instance : DecidableEq G := Classical.decEq G

@[expose] noncomputable def classRep (C : ConjClasses G) : G :=
  Classical.choose (ConjClasses.mk_surjective C)

omit [Fintype G] in
@[simp] theorem mk_classRep (C : ConjClasses G) : ConjClasses.mk (classRep C) = C :=
  Classical.choose_spec (ConjClasses.mk_surjective C)

@[expose] noncomputable def classFinset (C : ConjClasses G) : Finset G :=
  by
    classical
    exact C.carrier.toFinset

@[simp]
theorem mem_classFinset {C : ConjClasses G} {x : G} :
    x ∈ classFinset C ↔ ConjClasses.mk x = C := by
  classical
  simp [classFinset, ConjClasses.mem_carrier_iff_mk_eq]

@[simp]
theorem classRep_mem_classFinset (C : ConjClasses G) : classRep C ∈ classFinset C := by
  simp

@[expose] noncomputable def classSize (C : ConjClasses G) : ℕ :=
  (classFinset C).card


@[expose] noncomputable def classSum (R : Type v) [Semiring R] (C : ConjClasses G) :
    MonoidAlgebra R G :=
  ∑ x ∈ classFinset C, MonoidAlgebra.single x 1

@[simp]
theorem classSum_coeff (R : Type v) [Semiring R] (C : ConjClasses G) (x : G) :
    (classSum R C).coeff x = if ConjClasses.mk x = C then 1 else 0 := by
  classical
  simp [classSum, Finsupp.finsetSum_apply, Finsupp.single_apply,
    mem_classFinset]


private theorem classSum_commute_single (R : Type v) [CommSemiring R]
    (C : ConjClasses G) (g : G) :
    MonoidAlgebra.single g 1 * classSum R C =
      classSum R C * MonoidAlgebra.single g 1 := by
  classical
  ext x
  simp only [MonoidAlgebra.coeff_single_mul_apply,
    MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one, classSum_coeff]
  have hmk : ConjClasses.mk (g⁻¹ * x) = ConjClasses.mk (x * g⁻¹) := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    refine ⟨g, ?_⟩
    group
  rw [hmk]

theorem classSum_mem_center (R : Type v) [CommSemiring R] (C : ConjClasses G) :
    classSum R C ∈ Submonoid.center (MonoidAlgebra R G) := by
  classical
  rw [Submonoid.mem_center_iff]
  intro z
  induction z using MonoidAlgebra.induction_on with
  | of g =>
      simpa only [MonoidAlgebra.of_apply] using classSum_commute_single R C g
  | add x y hx hy =>
      simp only [add_mul, mul_add, hx, hy]
  | smul r x hx =>
      simpa only [Algebra.smul_mul_assoc, Algebra.mul_smul_comm] using congrArg (r • ·) hx

theorem classSum_commute (R : Type v) [CommSemiring R]
    (C : ConjClasses G) (z : MonoidAlgebra R G) :
    z * classSum R C = classSum R C * z :=
  (Submonoid.mem_center_iff.mp (classSum_mem_center R C)) z

omit [Fintype G] in
theorem coeff_eq_of_isConj (R : Type v) [CommSemiring R]
    {z : MonoidAlgebra R G} (hz : z ∈ Submonoid.center (MonoidAlgebra R G))
    {a b : G} (hab : IsConj a b) : z.coeff a = z.coeff b := by
  classical
  rw [isConj_iff] at hab
  obtain ⟨g, rfl⟩ := hab
  have hcomm := (Submonoid.mem_center_iff.mp hz) (MonoidAlgebra.single g 1)
  have hcoeff := congrArg (fun w : MonoidAlgebra R G => w.coeff (g * a)) hcomm
  simpa using hcoeff

private theorem coeff_eq_classRep (R : Type v) [CommSemiring R]
    {z : MonoidAlgebra R G} (hz : z ∈ Submonoid.center (MonoidAlgebra R G))
    (x : G) : z.coeff x = z.coeff (classRep (ConjClasses.mk x)) := by
  apply coeff_eq_of_isConj R hz
  apply ConjClasses.mk_eq_mk_iff_isConj.mp
  simp

theorem central_eq_sum_classSums (R : Type v) [CommSemiring R]
    {z : MonoidAlgebra R G} (hz : z ∈ Submonoid.center (MonoidAlgebra R G)) :
    z = ∑ C : ConjClasses G, z.coeff (classRep C) • classSum R C := by
  classical
  ext x
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, classSum_coeff]
  rw [Finset.sum_eq_single (ConjClasses.mk x)]
  · simp [coeff_eq_classRep R hz x]
  · intro C _ hC
    simp [Ne.symm hC]
  · simp

@[expose] noncomputable def structureConstant (C D E : ConjClasses G) : ℕ :=
  ((classFinset C ×ˢ classFinset D).filter
    (fun p : G × G => p.1 * p.2 = classRep E)).card

private theorem classSum_mul_coeff_classRep (R : Type v) [CommSemiring R]
    (C D E : ConjClasses G) :
    (classSum R C * classSum R D).coeff (classRep E) =
      (structureConstant C D E : R) := by
  classical
  rw [structureConstant]
  simp [classSum, Finset.sum_mul, Finset.mul_sum, Finsupp.finsetSum_apply,
    Finsupp.single_apply]
  rw [Finset.natCast_card_filter
    (fun p : G × G => p.1 * p.2 = classRep E)
    (classFinset C ×ˢ classFinset D)]
  rw [Finset.sum_product_right]
  apply Finset.sum_congr rfl
  intro y _
  exact Finset.natCast_card_filter
    (fun x : G => x * y = classRep E) (classFinset C)

theorem classSum_mul (R : Type v) [CommSemiring R] (C D : ConjClasses G) :
    classSum R C * classSum R D =
      ∑ E : ConjClasses G, (structureConstant C D E : R) • classSum R E := by
  calc
    classSum R C * classSum R D =
        ∑ E : ConjClasses G,
          (classSum R C * classSum R D).coeff (classRep E) • classSum R E :=
      central_eq_sum_classSums R
        ((Submonoid.center (MonoidAlgebra R G)).mul_mem
          (classSum_mem_center R C) (classSum_mem_center R D))
    _ = ∑ E : ConjClasses G,
          (structureConstant C D E : R) • classSum R E := by
      apply Finset.sum_congr rfl
      intro E _
      rw [classSum_mul_coeff_classRep]

section Schur

variable {k : Type v} [Field k] [IsAlgClosed k]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable (ρ : Representation k G V) [Representation.IsIrreducible ρ]

omit [Fintype G] in
theorem scalarAlgebraMap_bijective :
    Function.Bijective (algebraMap k (ρ.IntertwiningMap ρ)) :=
  Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)

@[expose] noncomputable def centralScalar {z : MonoidAlgebra k G}
    (hz : z ∈ Submonoid.center (MonoidAlgebra k G)) : k :=
  Classical.choose ((scalarAlgebraMap_bijective ρ).surjective
    (Representation.IntertwiningMap.centralAlgebraMul ρ hz))


@[expose] noncomputable def omega (C : ConjClasses G) : k :=
  centralScalar ρ (classSum_mem_center k C)


end Schur

end

end ZStar.ClassSums

end CFSG
