module

public import CFSG.CGT.Stroth77.Stroth31Cases

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

section PrintedImages

variable {D : Subgroup G} {m : ℕ}


@[simp] theorem e_c (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul dD.c) = Torus.c := by
  simp [StrothWeakTypeData.c]

@[simp] theorem e_a (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul dD.a) = Torus.a := by
  simp [StrothWeakTypeData.a]

@[simp] theorem e_b (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    dD.e (Additive.ofMul dD.b) = Torus.b := by
  simp [StrothWeakTypeData.b]


@[simp] theorem strothConj_one (r : G) : strothConj r 1 = 1 := by
  simp [strothConj]


end PrintedImages

section Orders

variable {D : Subgroup G} {m : ℕ}


theorem orderOf_a (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    orderOf dD.a = 2 ^ (m + 1) := by
  rw [StrothWeakTypeData.a, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq,
    addOrderOf_a]
  rfl

theorem orderOf_b (dD : StrothWeakTypeData D (StrothTypeIndex.t100 m)) :
    orderOf dD.b = 2 ^ (m + 1) := by
  rw [StrothWeakTypeData.b, ← addOrderOf_ofMul_eq_orderOf, ofMul_toMul, AddEquiv.addOrderOf_eq,
    addOrderOf_b]
  rfl

end Orders

section ConjugationCalculus

variable {D : Subgroup G}


theorem mul_comm_mem_of_isMulCommutative {D : Subgroup G} [IsMulCommutative D] {x y : G}
    (hx : x ∈ D) (hy : y ∈ D) : x * y = y * x := by
  have h := mul_comm' (⟨x, hx⟩ : D) ⟨y, hy⟩
  simpa using congrArg (Subtype.val) h


end ConjugationCalculus

section Case1Reduction


end Case1Reduction

section RemainingCases


end RemainingCases

end CFSG.CGT.Stroth77
