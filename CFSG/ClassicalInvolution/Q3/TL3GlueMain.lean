module

public import CFSG.ClassicalInvolution.Q3.TL3GlueJ
public import CFSG.ClassicalInvolution.Q3.TL3GlueLie

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

section Conj

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

omit [Finite Y] in
theorem conjClass_conjSub (g : Y) (K : Subgroup Y) :
    CoreAssembly.conjClass (conjSub g K) = CoreAssembly.conjClass K := by
  ext X
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, conjSub_mul h g K⟩
  · rintro ⟨h, rfl⟩
    refine ⟨h * g⁻¹, ?_⟩
    show conjSub (h * g⁻¹) (conjSub g K) = conjSub h K
    rw [conjSub_mul, conjSub_inv_conjSub]

omit [Finite Y] in
theorem TightCls.conj (hc : TightCls Y R S t) (g : Y) {S' : Sylow 2 ↥(conjSub g R)}
    (e : (S' : Subgroup ↥(conjSub g R)) ≃* (S : Subgroup R)) :
    TightCls Y (conjSub g R) S' (g * t * g⁻¹) := by
  obtain ⟨⟨e8⟩, hgen, hO⟩ := hc
  refine ⟨⟨e.trans e8⟩, ?_, hO⟩
  have key : (⨆ h : Y, conjSub h (conjSub g (tightCore R))) =
      ⨆ h : Y, conjSub h (tightCore R) := by
    apply le_antisymm
    · refine iSup_le fun h => ?_
      rw [← conjSub_mul]
      exact le_iSup (fun h : Y => conjSub h (tightCore R)) (h * g)
    · refine iSup_le fun h => ?_
      have e1 : conjSub h (tightCore R) = conjSub (h * g⁻¹) (conjSub g (tightCore R)) := by
        rw [conjSub_mul, conjSub_inv_conjSub]
      rw [e1]
      exact le_iSup (fun h : Y => conjSub h (conjSub g (tightCore R))) (h * g⁻¹)
  show (⨆ h : Y, conjSub h (tightCore (conjSub g R))) = ⊤
  rw [← conjSub_tightCore R g, key]
  exact hgen

omit [Finite Y] in
theorem not_tightInO2_conj (h : ¬ TightInO2 t) (g : Y) : ¬ TightInO2 (g * t * g⁻¹) := by
  rintro ⟨P, hPn, hP2, hP⟩
  apply h
  refine ⟨P, hPn, hP2, ?_⟩
  have := hPn.conj_mem _ hP g⁻¹
  simpa [mul_assoc] using this

theorem TightDatum.card_dbar_lt (hd : TightDatum R S t) (hE2 : ¬ TightInO2 t) :
    Nat.card hd.Dbar < Nat.card Y := by
  have h1 : Nat.card hd.Dbar ≤ Nat.card ↥hd.act.ker :=
    Nat.card_le_card_of_surjective hd.toDbar (QuotientGroup.mk'_surjective _)
  have h2 : Nat.card ↥hd.act.ker ≤ Nat.card ↥(Subgroup.centralizer ({t} : Set Y)) :=
    Subgroup.card_le_card_group _
  have h3 : Nat.card ↥(Subgroup.centralizer ({t} : Set Y)) ≤ Nat.card Y :=
    Subgroup.card_le_card_group _
  have hne : Subgroup.centralizer ({t} : Set Y) ≠ ⊤ := by
    intro htop
    apply hE2
    have hcen : ∀ g : Y, g * t = t * g := fun g =>
      Subgroup.mem_centralizer_singleton_iff.mp (htop ▸ Subgroup.mem_top g)
    have htc : t ∈ Subgroup.center Y := Subgroup.mem_center_iff.mpr hcen
    have hle : Subgroup.zpowers t ≤ Subgroup.center Y := Subgroup.zpowers_le.mpr htc
    refine ⟨Subgroup.zpowers t, ⟨fun n hn g => ?_⟩, ?_, Subgroup.mem_zpowers t⟩
    · have hgn : g * n = n * g := Subgroup.mem_center_iff.mp (hle hn) g
      rw [hgn, mul_inv_cancel_right]
      exact hn
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hd.order, pow_one])
  have h4 : Nat.card ↥(Subgroup.centralizer ({t} : Set Y)) ≠ Nat.card Y :=
    fun h => hne ((Subgroup.card_eq_iff_eq_top _).mp h)
  omega

end Conj

section Cit3


end Cit3

end CFSG.ClassicalInvolution.Q3
