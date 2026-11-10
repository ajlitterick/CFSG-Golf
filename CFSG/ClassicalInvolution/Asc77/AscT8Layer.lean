module

public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

namespace T8

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem oddCoreOf_le_oddCoreOf_of_normalized {Y C : Subgroup G} (hYC : Y ≤ C)
    (hn : ∀ c ∈ C, conjSub c Y = Y) : oddCoreOf Y ≤ oddCoreOf C := by
  have hchar : (classicalInvolutionOddCore ↥Y).Characteristic :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_characteristic
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥Y)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  set N : Subgroup G := oddCoreOf Y with hN
  have hNY : N ≤ Y := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hNC : N ≤ C := hNY.trans hYC
  have hMn : (N.subgroupOf C).Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨y, hy, hym⟩ := hm
    have hc : conjSub (g : G) Y = Y := hn g g.2
    let ψ : ↥Y ≃* ↥Y :=
      (Subgroup.equivMapOfInjective Y (MulAut.conj (g : G)).toMonoidHom
        (MulAut.conj (g : G)).injective).trans (MulEquiv.subgroupCongr hc)
    have hψ : ∀ x : ↥Y, ((ψ x : ↥Y) : G) = (g : G) * (x : G) * (g : G)⁻¹ := fun x => rfl
    have h1 : ψ y ∈ classicalInvolutionOddCore ↥Y :=
      (Subgroup.characteristic_iff_map_le.mp hchar ψ) ⟨y, hy, rfl⟩
    have hym' : (y : G) = (m : G) := hym
    refine ⟨ψ y, h1, ?_⟩
    rw [Subgroup.coe_subtype, hψ, hym']
    rfl
  have hMo : Odd (Nat.card (N.subgroupOf C)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv, hN]
    unfold oddCoreOf
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact hodd
  have hle : N.subgroupOf C ≤ classicalInvolutionOddCore ↥C :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore _ hMn hMo
  intro x hx
  exact ⟨⟨x, hNC hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end OddCore

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem rLayer_conjSub_eq (hΩ : ConjInvariant Ω) {a c : G}
    (hc : c ∈ Subgroup.centralizer ({a} : Set G)) : conjSub c (rLayer Ω a) = rLayer Ω a := by
  have key : ∀ d ∈ Subgroup.centralizer ({a} : Set G), conjSub d (rLayer Ω a) ≤ rLayer Ω a := by
    intro d hd
    unfold rLayer
    rw [conjSub, Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun R hR => iSup_le fun hRC => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have h1 : conjSub d R ∈ RSet Ω := RSet.conj hΩ hR d
    have h2 : conjSub d R ≤ Subgroup.centralizer ({a} : Set G) := by
      have := conjSub_mono (n := d) hRC
      rwa [conjSub_eq_self_of_mem hd] at this
    exact le_iSup₂_of_le (conjSub d R) h1 (le_iSup_of_le h2 le_rfl)
  refine le_antisymm (key c hc) ?_
  have h := conjSub_mono (n := c) (key c⁻¹ ((Subgroup.centralizer ({a} : Set G)).inv_mem hc))
  rwa [conjSub_conjSub_inv] at h

omit [Finite G] in
theorem oddCoreOf_centralizer_commutes {A : Subgroup G} (hA : alphaOf A = ⊥) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {y : G} (hy : y ∈ A) :
    ∀ x ∈ oddCoreOf (Subgroup.centralizer ({a} : Set G)), x * y = y * x := by
  intro x hx
  have hle : ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆ ≤ alphaOf A := by
    unfold alphaOf
    refine le_sup_of_le_left (le_trans ?_ (le_iSup₂ (f := fun (a' : G) (_ : a' ∈ A) =>
      ⨆ (_ : a' ≠ 1), ⁅oddCoreOf (Subgroup.centralizer ({a'} : Set G)), A⁆) a ha))
    exact le_iSup (fun _ : a ≠ 1 => ⁅oddCoreOf (Subgroup.centralizer ({a} : Set G)), A⁆) ha1
  rw [hA] at hle
  have h1 : ⁅x, y⁆ = 1 := Subgroup.mem_bot.mp (hle (Subgroup.commutator_mem_commutator hx hy))
  rw [commutatorElement_def] at h1
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h1, one_mul]

end Layer

end T8


end CFSG.ClassicalInvolution.Asc77
