module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InvariantOddPSubgroupCentralized
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvariantOddPSubgroupCentralized
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

open scoped Pointwise
open Matrix
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups

universe u

/-- A nontrivial odd-prime-power subgroup cannot be both inverted and
centralized by the same involution. -/
public theorem no_nontrivial_oddP_inverted_centralized
    {G : Type u} [Group G] [Finite G]
    (s : G) (X : Subgroup G) {p : ℕ} [Fact p.Prime]
    (hinv : BenderGlauberman.IsInvertedBy s X)
    (hcent : X ≤ Subgroup.centralizer ({s} : Set G))
    (hXp : IsPGroup p X) (hpodd : Odd p) (hXne : X ≠ ⊥) :
    False := by
  classical
  let : Fintype X := Fintype.ofFinite X
  have hlt : 1 < Fintype.card X := by
    rw [← Nat.card_eq_fintype_card]
    exact (Subgroup.one_lt_card_iff_ne_bot X).mpr hXne
  obtain ⟨w, hwne⟩ := Fintype.exists_ne_of_one_lt_card hlt (1 : X)
  let x : G := (w : G)
  have hxmem : x ∈ X := w.property
  have hinvx : s * x * s⁻¹ = x⁻¹ := hinv x hxmem
  have hcomm : x * s = s * x :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hcent hxmem))
  have hcentx : s * x * s⁻¹ = x := by
    calc
      s * x * s⁻¹ = (x * s) * s⁻¹ := by rw [hcomm]
      _ = x := by group
  have hx_inv : x = x⁻¹ := by
    exact hcentx.symm.trans hinvx
  have hsq : x * x = 1 := by
    have hpar : x * x = x * x⁻¹ := by
      congr 2
    calc
      x * x = x * x⁻¹ := hpar
      _ = 1 := by group
  have hord2 : orderOf w ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [pow_two] using hsq
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hXp) w
  have hord_odd : Odd (orderOf w) := by
    rw [hk]
    exact hpodd.pow
  have hord1 : orderOf w = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
    · exact h
    · exfalso
      exact hord_odd.not_two_dvd_nat (by rw [h])
  have hw1 : w = 1 := orderOf_eq_one_iff.mp hord1
  exact hwne hw1


end CFSG.GorensteinWalter
