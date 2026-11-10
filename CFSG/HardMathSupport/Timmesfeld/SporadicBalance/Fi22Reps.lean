module

public import Certificates.Certificate13621
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase1
public import CFSG.Sporadic.FischerOddCore.RefineSpec

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Foote.E27.Fi22S0 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiNative CFSG.Sporadic.FischerOddCore
  CFSG.Sporadic.FischerOddCore.Native CFSG.Certificates CFSG.Certificates.Native


theorem countP_range_eq_card (q : ℕ → Bool) :
    (List.range 3510).countP q = Nat.card {w : Fin 3510 // q w = true} :=
  (card_fin_subtype_eq_countP 3510 q).symm


theorem card_fix_conj (g y : J) :
    Nat.card {w : Fin 3510 // (g * y * g⁻¹) • w = w} = Nat.card {w : Fin 3510 // y • w = w} := by
  refine Nat.card_congr
    { toFun := fun w => ⟨g⁻¹ • w.1, ?_⟩
      invFun := fun w => ⟨g • w.1, ?_⟩
      left_inv := fun w => Subtype.ext (smul_inv_smul g w.1)
      right_inv := fun w => Subtype.ext (inv_smul_smul g w.1) }
  · have h := w.2
    rw [mul_smul, mul_smul] at h
    calc y • g⁻¹ • w.1 = g⁻¹ • (g • y • g⁻¹ • w.1) := by rw [inv_smul_smul]
      _ = g⁻¹ • w.1 := by rw [h]
  · have h := w.2
    rw [mul_smul, mul_smul, inv_smul_smul, h]


theorem conj_eq_self_iff {g c : J} : g * c * g⁻¹ = c ↔ c * g = g * c := by
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm


theorem lt_of_mem_fixList {X : Table} {v : ℕ} (hv : v ∈ fixList X) : v < 3510 := by
  unfold fixList at hv
  rw [List.mem_filter, List.mem_range] at hv
  exact hv.1


theorem xRep_zero_smul_ne
    (v : Fin 3510) : xRep 0 • v ≠ v :=
  Certificates.certificate13621.1 v


theorem exists_orderOf_four_comm :
    ∃ t : J, orderOf t = 4 ∧ t * xRep 0 = xRep 0 * t :=
  Certificates.certificate13621.2.1


theorem card_centralizer_xRep_zero_le :
    Nat.card (Subgroup.centralizer ({xRep 0} : Set J)) ≤ 34992 :=
  Certificates.certificate13621.2.2.1

@[expose] def fixStab (x : J) : Subgroup J where
  carrier := {g | ∀ v : Fin 3510, x • v = v → g • v = v}
  mul_mem' := fun {g h} hg hh v hv => by rw [mul_smul, hh v hv, hg v hv]
  one_mem' := fun v _ => one_smul J v
  inv_mem' := fun {g} hg v hv => by
    have := hg v hv
    rw [← this, inv_smul_smul, this]


theorem card_centralizer_fix_le
    {k : ℕ} (hk : k ∈ [1, 2, 3]) :
    Nat.card ↥(Subgroup.centralizer ({xRep k} : Set J) ⊓ fixStab (xRep k)) ≤ 3 := by
  have e : Nat.card ↥(Subgroup.centralizer ({xRep k} : Set J) ⊓ fixStab (xRep k)) =
      Nat.card {g : J // g ∈ Subgroup.centralizer ({xRep k} : Set J) ∧
        ∀ v : Fin 3510, xRep k • v = v → g • v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [e]
  exact Certificates.certificate13621.2.2.2.1 k hk

theorem sep_xRep {k : ℕ}
    (hk : k ∈ [1, 2, 3]) :
    ∀ d ∈ D, d * xRep k = xRep k * d → ∀ d' ∈ D, d' * xRep k = xRep k * d' → d ≠ d' →
      d * d' = d' * d → ∃ e ∈ D, e * xRep k = xRep k * e ∧ e * d' = d' * e ∧ e * d ≠ d * e :=
  Certificates.certificate13621.2.2.2.2 k hk

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
