module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalDihedral
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCRankOneCenter
public import CFSG.LocalAnalysis.ComponentInitial.SLTwoInvolution
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.J1ModelTransport
public import CFSG.Open.StatedDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Open.Defs

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace MathieuJankoExclusion

open CFSG.Open CFSG.ProperTwoGeneratedCore Matrix


@[expose] def j1InvolX : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![4, 6, 9, 8, 5, 8, 10;
     6, 10, 0, 6, 2, 6, 3;
     9, 0, 10, 9, 3, 9, 10;
     8, 6, 9, 0, 3, 4, 9;
     5, 2, 3, 3, 1, 5, 7;
     8, 6, 9, 4, 5, 4, 7;
     10, 3, 10, 9, 7, 7, 3]

@[expose] def j1InvolY : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![6, 5, 4, 5, 5, 4, 10;
     5, 8, 8, 3, 6, 3, 5;
     4, 8, 5, 0, 4, 3, 6;
     5, 3, 0, 8, 4, 5, 4;
     5, 6, 4, 4, 10, 6, 5;
     4, 3, 3, 5, 6, 0, 7;
     10, 5, 6, 4, 5, 7, 6]

@[expose] def j1InvolZ : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  !![10, 5, 9, 3, 10, 0, 4;
     5, 1, 4, 6, 9, 3, 8;
     9, 4, 0, 2, 1, 2, 7;
     3, 6, 2, 2, 3, 2, 10;
     10, 9, 1, 3, 8, 1, 8;
     0, 3, 2, 2, 1, 0, 7;
     4, 8, 7, 10, 8, 7, 0]


@[expose] def j1VMat (i : Fin 8) : Matrix (Fin 7) (Fin 7) (ZMod 11) :=
  (if i.val % 2 = 1 then j1InvolX else 1) * (if i.val / 2 % 2 = 1 then j1InvolY else 1) *
    (if i.val / 4 % 2 = 1 then j1InvolZ else 1)


@[expose] def j1VXor (i j : Fin 8) : Fin 8 := ⟨(i.val ^^^ j.val) % 8, Nat.mod_lt _ (by omega)⟩

theorem j1VMat_mul : ∀ i j : Fin 8, j1VMat i * j1VMat j = j1VMat (j1VXor i j) := by
  decide +kernel

theorem j1VMat_one : j1VMat 0 = 1 := by
  decide +kernel

theorem j1VMat_mul_self (i : Fin 8) : j1VMat i * j1VMat i = 1 := by
  rw [j1VMat_mul, show j1VXor i i = 0 by revert i; decide, j1VMat_one]


theorem j1VXor_comm : ∀ i j : Fin 8, j1VXor i j = j1VXor j i := by decide

@[expose] def j1ElemAbelian : Subgroup (GL (Fin 7) (ZMod 11)) where
  carrier := {g | ∃ i, (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = j1VMat i}
  mul_mem' {g h} := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    exact ⟨j1VXor i j, by rw [Units.val_mul, hi, hj, j1VMat_mul]⟩
  one_mem' := ⟨0, by rw [Units.val_one, j1VMat_one]⟩
  inv_mem' {g} := by
    rintro ⟨i, hi⟩
    have h2 : g * g = 1 := Units.ext (by rw [Units.val_mul, Units.val_one, hi, j1VMat_mul_self])
    exact ⟨i, by rw [inv_eq_of_mul_eq_one_right h2, hi]⟩

theorem mem_j1ElemAbelian {g : GL (Fin 7) (ZMod 11)} :
    g ∈ j1ElemAbelian ↔ ∃ i, (g : Matrix (Fin 7) (Fin 7) (ZMod 11)) = j1VMat i := Iff.rfl


instance : CFSG.IsElementaryAbelian 2 j1ElemAbelian where
  is_comm := ⟨fun g h => by
    obtain ⟨i, hi⟩ := mem_j1ElemAbelian.mp g.2
    obtain ⟨j, hj⟩ := mem_j1ElemAbelian.mp h.2
    refine Subtype.ext (Units.ext ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, hi, hj, j1VMat_mul,
      j1VMat_mul, j1VXor_comm]⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
    obtain ⟨i, hi⟩ := mem_j1ElemAbelian.mp g.2
    refine Subtype.ext (Units.ext ?_)
    rw [sq, Subgroup.coe_mul, Units.val_mul, hi, j1VMat_mul_self, OneMemClass.coe_one,
      Units.val_one]


end MathieuJankoExclusion

open MathieuJankoExclusion


end CFSG.ComponentClassification.UnbalancedGS
