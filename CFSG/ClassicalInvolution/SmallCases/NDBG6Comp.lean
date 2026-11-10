module

public import CFSG.ClassicalInvolution.SmallCases.NDBG6Aut
public import CFSG.ClassicalInvolution.Asc77.AscBSE3
public import CFSG.ClassicalInvolution.SmallCases.NDBC4

public section

namespace CFSG.ClassicalInvolution.NDB.NDBG

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

section Comp

theorem eq_one_of_mem_range_of_comm {M X : Type} [Group M] [Group X] {ψ : M →* X}
    (hinj : Function.Injective ψ) (hZ : Subgroup.center M = ⊥) {s : X} (hs : s ∈ ψ.range)
    (hcomm : ∀ t ∈ ψ.range, s * t = t * s) : s = 1 := by
  obtain ⟨k, rfl⟩ := hs
  have hk : k ∈ Subgroup.center M := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply hinj
    rw [map_mul, map_mul]
    exact (hcomm _ ⟨g, rfl⟩).symm
  rw [hZ, Subgroup.mem_bot] at hk
  rw [hk, map_one]

theorem memberJoin_le_of_forall (C : XCtx p f Ω z) {H : Subgroup (OddQuot z)}
    (hH : ∀ j, (C.psi j).range ≤ H) : memberJoin (exactFamily Ω z) z ≤ H := by
  intro y hy
  rw [← range_sectionQuotientHom C.hs.normalizes] at hy
  obtain ⟨x, rfl⟩ := hy
  have hx : x ∈ ⨆ i, (C.D.hom i).range := by
    rw [C.D.generate]
    exact Subgroup.mem_top x
  induction hx using Subgroup.iSup_induction' with
  | hp k y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact hH k ⟨a, rfl⟩
  | h1 =>
    rw [map_one]
    exact H.one_mem
  | hmul a b _ _ ha hb =>
    rw [map_mul]
    exact H.mul_mem ha hb

theorem injective_and_center_of_g2 (C : XCtx p f Ω z) {b : Fin C.D.card}
    (hG2 : C.D.tag b = .G2) :
    Function.Injective (C.psi b) ∧ Subgroup.center (compModel C.D b).K = ⊥ :=
  ⟨RouteD.G2D4.injective_of_ker_le_center C.hp (Or.inl hG2) (C.D.rank b)
      (C.D.admissible b).2.1 (C.psi b) (C.psi_ker b),
    RouteD.G2D4.center_modelUniv_g2d4_eq_bot C.hp (Or.inl hG2) (C.D.rank b)
      (C.D.admissible b).2.1⟩

theorem zbar_ne_one (C : XCtx p f Ω z) : BSC.zbar z ≠ 1 := fun h =>
  C.hKz.ne_one (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one (Subtype.ext C.hKz.sq) h))

theorem zbar_not_mem_range (C : XCtx p f Ω z) {b : Fin C.D.card} (hG2 : C.D.tag b = .G2) :
    BSC.zbar z ∉ (C.psi b).range := fun h => by
  obtain ⟨hinj, hZ⟩ := injective_and_center_of_g2 C hG2
  exact zbar_ne_one C (eq_one_of_mem_range_of_comm hinj hZ h fun t _ => NDB.Cover.zbar_comm t)

end Comp

end CFSG.ClassicalInvolution.NDB.NDBG
