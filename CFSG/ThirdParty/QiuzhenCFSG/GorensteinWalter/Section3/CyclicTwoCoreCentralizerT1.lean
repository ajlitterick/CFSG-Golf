module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreBLeMSource
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreUInterM
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCorePrimeCoreAbelian
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Cyclic first-case centralizer equation `C_U(t₁) = B × P₀` — work in progress

The requested unconditional theorem
`firstCase_cyclic_centralizer_t1_eq_B_sup_P0_of_a7` is **not yet proved**
and is intentionally not declared under that name.  The exact printed
route (`X = B ∩ PP^g ⊴ C_U(t₁)` ⇒ `C_U(t₁) ≤ M`) is invalid: the
corrected `PP^g` witness proves only `B ≤ N_G(X)`, not
`C_U(t₁) ≤ N_G(X)`.  This module currently contains only a private
conditional helper `..._of_le_M` with the extra hypothesis
`C_U(t₁) ≤ M`; the remaining core is
`C_U(t₁) ≤ N_G(B)` (with `B ≠ ⊥ ≤ B ∩ M`, so the landed normalizer
control gives `N_G(B) = M`).

No `sorry`, `admit`, `axiom`, or `opaque` is used.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u


/-- In the cyclic first-case A₇ model, `S` centralizes no nontrivial
`q`-core of `U`: otherwise that core would lie in `B ∩ M`, be normal in
`H`, and force `H ≤ N_G(X) ≤ M`, contradicting `N_G(P₂) ⊄ H`. -/
public theorem firstCase_cyclic_S_not_centralizes_nontrivial_qCore
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3)
    {q : ℕ} (hq : qCoreOf od.d.bg.U q ≠ ⊥) :
    ¬ (od.d.bg.S : Subgroup G) ≤
      Subgroup.centralizer (qCoreOf od.d.bg.U q : Set G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  intro hScent
  let Qq : Subgroup G := qCoreOf od.d.bg.U q
  have hBleM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_source
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hQleB : Qq ≤ od.d.bg.B := by
    intro x hx
    have hxU : x ∈ od.d.bg.U := qCoreOf_le od.d.bg.U q hx
    have hxcentS : x ∈ Subgroup.centralizer
        ((od.d.bg.S : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hcomm := (Subgroup.mem_centralizer_iff.mp (hScent hs)) x hx
      change s * x = x * s
      exact hcomm.symm
    rw [B_eq_centralizer_U od.d.bg]
    exact Subgroup.mem_inf.mpr ⟨hxU, hxcentS⟩
  have hQleBM : Qq ≤ od.d.bg.B ⊓ M := le_inf hQleB (hQleB.trans hBleM)
  have hQnormalH : IsNormalIn Qq od.d.bg.H := by
    change IsNormalIn
      ((pCore q (↥od.d.bg.U)).map od.d.bg.U.subtype) od.d.bg.H
    exact map_characteristic_isNormalIn_of_isNormalIn
      (K := pCore q (↥od.d.bg.U)) (hKchar := by infer_instance)
      (hHnormal := bg_U_normal_in_H od.d.bg)
  have hHleNQ : od.d.bg.H ≤ Subgroup.normalizer (Qq : Set G) :=
    le_normalizer_of_isNormalIn hQnormalH
  have hEeq := firstCase_cyclic_componentLayer_normalizer_eq_of_a7
    hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 Qq hq hQleBM
  have hNQleM := firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq
    hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 Qq hq hQleBM hEeq
  have hHleM : od.d.bg.H ≤ M := hHleNQ.trans hNQleM
  have hHcoatom : IsCoatom od.d.bg.H := by
    simpa [od.d.H_eq, hHhat] using c.Hhat_maximal
  have hEq : od.d.bg.H = M := by
    by_cases hEq : od.d.bg.H = M
    · exact hEq
    · have hlt : od.d.bg.H < M := lt_of_le_of_ne hHleM hEq
      have hMtop : M = ⊤ := hHcoatom.2 M hlt
      exact False.elim (hMmax.1 hMtop)
  have hNleH : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ od.d.bg.H := by
    simpa [hEq] using hMN
  exact (firstCase_normalizer_P2_not_le_H hmin c od fd hU Q) hNleH

/-- The user's centralizer-core reduction: if `C_B(P) ≠ 1`, then the landed
normalizer control applied to that nontrivial subgroup of `B ∩ M` gives
`P ≤ M`. -/
public theorem firstCase_cyclic_primeCore_le_M_of_a7_of_CB_ne
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hfirst : FirstCase c) (hHhat : c.Hhat = c.H)
    (hU : od.d.bg.U = fittingSubgroupOf od.d.bg.U ⊔ od.d.bg.B)
    (Q : Sylow od.p ↥od.d.bg.B)
    (M : Subgroup G) (hMmax : IsCoatom M)
    (hMN : Subgroup.normalizer
      (sylowCarrier (firstCase_P2_sylow c od hU Q) : Set G) ≤ M)
    (hSM : (c.S : Subgroup G) ≤ M)
    (fd : FirstCaseFourData c od.d)
    (hV2 : fd.V2 ≤ componentLayerOf M)
    (hA7 : Nonempty ((componentLayerOf M) ⧸
      pPrimeCore 2 (componentLayerOf M) ≃* alternatingGroup (Fin 7)))
    (hp3 : od.p = 3)
    (hCB : od.d.bg.B ⊓ Subgroup.centralizer
      (qCoreOf od.d.bg.U od.p : Set G) ≠ ⊥) :
    qCoreOf od.d.bg.U od.p ≤ M := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let X : Subgroup G :=
    od.d.bg.B ⊓ Subgroup.centralizer (P : Set G)
  have hXleB : X ≤ od.d.bg.B := inf_le_left
  have hBleM : od.d.bg.B ≤ M :=
    firstCase_cyclic_B_le_M_of_a7_source
      hmin c od hfirst hHhat hU Q M hMmax hMN hSM fd hV2 hA7 hp3
  have hXleBM : X ≤ od.d.bg.B ⊓ M := le_inf hXleB (hXleB.trans hBleM)
  have hEeq := firstCase_cyclic_componentLayer_normalizer_eq_of_a7
    hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 X hCB hXleBM
  have hNXleM := firstCase_cyclic_normalizer_le_M_of_le_B_inter_M_of_componentLayer_eq
    hmin c od hfirst hHhat M hMmax hSM fd hV2 hA7 X hCB hXleBM hEeq
  have hPleCX : P ≤ Subgroup.centralizer (X : Set G) := by
    intro p hp x hx
    have hxcentP : x ∈ Subgroup.centralizer (P : Set G) :=
      (Subgroup.mem_inf.mp hx).2
    have hcomm : p * x = x * p :=
      (Subgroup.mem_centralizer_iff.mp hxcentP) p hp
    exact hcomm.symm
  have hPleNX : P ≤ Subgroup.normalizer (X : Set G) :=
    hPleCX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  exact hPleNX.trans hNXleM

end CFSG.GorensteinWalter
