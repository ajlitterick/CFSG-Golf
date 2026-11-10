module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition
public import CFSG.ThirdParty.BrauerInduction.Background.Group.InternalDirectProduct

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# `p`-Elementary groups

This file defines `p`-elementary groups and develops their basic structure.

A `p`-elementary group is represented by explicit data: a cyclic prime-to-`p`
part `C`, a `p`-group part `P`, elementwise commutation between `C` and `P`,
and a decomposition of every element as a product `c * q`.

The file also constructs the `p`-elementary group associated to a `p`-regular
element `x`, namely the subgroup `Subgroup.zpowers x ⊔ P_of_Z p x`, where
`P_of_Z p x` is a chosen Sylow `p`-subgroup of the centralizer of `x`.
-/

universe u v

namespace CFSG.BrauerInduction

/--
A group `G` is `p`-elementary if it is the product of a cyclic `p`-regular
subgroup `C` and a `p`-group `P`, with `C` centralizing `P`.

The structure is data-bearing: it records chosen subgroups `C` and `P`. The
corresponding proposition is expressed as `Nonempty (PElementary p G)`, or
equivalently `IsPElementary p G`.
-/
structure PElementary (p : ℕ) (G : Type u) [Group G] where
  protected C : Subgroup G
  protected P : Subgroup G
  protected C_isCyclic : IsCyclic C
  protected P_isPGroup : IsPGroup p P
  protected C_isPRegular : ∀ {c : G}, c ∈ C → IsPRegular p c
  protected comm : ∀ {c q : G}, c ∈ C → q ∈ P → Commute c q
  protected decompose : ∀ h : G, ∃ c ∈ C, ∃ q ∈ P, c * q = h

/-- A group is `p`-elementary if it admits a `PElementary p` structure. -/
@[expose] def IsPElementary (p : ℕ) (G : Type u) [Group G] : Prop :=
  Nonempty (PElementary p G)

namespace PElementary

variable {p : ℕ} {G : Type u} [Group G] {g : G}

lemma isPSingular_of_mem_P [Fact p.Prime]
    (e : PElementary p G) {g : G} (hg : g ∈ e.P) :
    IsPSingular p g := by
  rcases (IsPGroup.iff_orderOf).1 e.P_isPGroup ⟨g, hg⟩ with ⟨k, hk⟩
  exact ⟨k, by simpa [Subgroup.orderOf_coe] using hk⟩

/--
In a `p`-elementary group `G = C * P`, an element of `G` is `p`-singular
iff it lies in the `p`-subgroup part `P`.
-/
lemma mem_P_iff_pSingular [Fact p.Prime]
    (e : PElementary p G) {g : G} :
    g ∈ e.P ↔ IsPSingular p g := by
  constructor
  · intro hg
    exact e.isPSingular_of_mem_P hg
  · intro hgu
    rcases e.decompose g with ⟨c, cC, q, qP, hg_eq⟩
    have hcr : IsPRegular p c := e.C_isPRegular cC
    have hqs  : IsPSingular p q := e.isPSingular_of_mem_P qP
    have hf : IsOfFinOrder (c * q) := by
      rw [hg_eq]
      exact hgu.isOfFinOrder
    have hcomm : q * c = c * q := by
      rw [e.comm cC qP]
    obtain ⟨hq_eq, hc_eq⟩ :=
      Group.pSingular_pRegular_unique p hf hcomm rfl hqs  hcr
    have hc1 : c = 1 := by
      rw [hc_eq]
      exact Group.isPSingular_pRegular_eq_one p hf (by simpa [hg_eq] using hgu)
    rw [← hg_eq, hc1, one_mul]
    exact qP

/--
In a `p`-elementary group `G = C * P`, an element of `G` is `p`-regular
iff it lies in the cyclic subgroup part `C`.
-/
lemma mem_C_iff_pRegular [Fact p.Prime]
    (e : PElementary p G) {g : G} :
    g ∈ e.C ↔ IsPRegular p g := by
  constructor
  · intro hg
    exact e.C_isPRegular hg
  · intro hgr
    rcases e.decompose g with ⟨c, cC, q, qP, hg_eq⟩
    have hps  : IsPSingular p q := e.isPSingular_of_mem_P qP
    have hpr : IsPRegular p c := e.C_isPRegular cC
    have hf : IsOfFinOrder (c * q) := by
      rw [hg_eq]
      exact hgr.isOfFinOrder
    have hcomm : q * c = c * q := by
      rw [e.comm cC qP]
    obtain ⟨hq_eq, hc_eq⟩ :=
      Group.pSingular_pRegular_unique p hf hcomm rfl hps  hpr
    have hq1 : q = 1 := by
      rw [hq_eq]
      exact Group.isPRegular_pSingular_eq_one p hf (by simpa [hg_eq] using hgr)
    rw [← hg_eq, hq1, mul_one]
    exact cC


/--
Every element of a `p`-elementary group has finite order.
-/
lemma isOfFinOrder [Fact p.Prime]
    (e : PElementary p G) (g : G) :
    IsOfFinOrder g := by
  rcases e.decompose g with ⟨c, hc, q, hq, rfl⟩
  exact Commute.isOfFinOrder_mul
    (e.comm hc hq)
    (IsPRegular.isOfFinOrder p (e.C_isPRegular hc))
    (IsPSingular.isOfFinOrder p (e.isPSingular_of_mem_P hq))


lemma inf_C_P_eq_bot [Fact p.Prime]
    (e : PElementary p G) : e.C ⊓ e.P = ⊥ := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_bot]
  constructor
  · rintro ⟨hx_C, hx_P⟩
    have hs  : IsPSingular p x := (e.mem_P_iff_pSingular).mp hx_P
    have hr : IsPRegular p x := (e.mem_C_iff_pRegular).mp hx_C
    exact IsPSingular.isPRegular_eq_one p x hs  hr
  · rintro rfl
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

/--
The product map `C × P → G` is an isomorphism for a `p`-elementary group.
-/
@[expose] noncomputable def mulEquivProd [Fact p.Prime]
    (e : PElementary p G) : e.C × e.P ≃* G :=
  (Subgroup.mulEquivProdOfInternalDirect e.C e.P (⊤ : Subgroup G)
    le_top le_top e.comm (e.inf_C_P_eq_bot)
    (by
      intro g _
      exact e.decompose g)).trans Subgroup.topEquiv


/-- The centralizer of `x`. -/
abbrev Z (x : G) : Subgroup G := Subgroup.centralizer ({x})

/-- The cyclic subgroup generated by `x`. -/
abbrev Cyc (x : G) : Subgroup G := Subgroup.zpowers x

@[simp]
lemma cyc_isCyclic (x : G) : IsCyclic (Cyc x) := by
  simp only [Subgroup.isCyclic_iff_exists_zpowers_eq_top]
  use x

lemma commute_of_mem_Z_of_mem_Cyc {x z c : G} (hz : z ∈ Z x)
    (hc : c ∈ Cyc x) : Commute c z := by
  rcases Subgroup.mem_zpowers_iff.mp hc with ⟨n, rfl⟩
  exact Commute.zpow_left (hz x rfl) n

/--
A chosen Sylow `p`-subgroup of the centralizer `Z x`.
-/
@[expose] noncomputable def P_in_Z (p : ℕ) (x : G) : Sylow p (Z x) :=
  Classical.choice (Sylow.nonempty : Nonempty (Sylow p (Z x)))

/-- Inclusion of `Z(x)` into `G`. -/
@[expose] def inclZ (x : G) : Z x →* G := Subgroup.subtype (Z x)

/--
The chosen Sylow `p`-subgroup of `Z x`, viewed as a subgroup of the ambient
group `G`.
-/
@[expose] noncomputable def P_of_Z (p : ℕ) (x : G) : Subgroup G :=
  Subgroup.map (inclZ x) (P_in_Z p x)

lemma P_of_Z_isPGroup (x : G) :
    IsPGroup p (P_of_Z p x) := IsPGroup.map (P_in_Z p x).isPGroup' (inclZ x)

/--
The chosen Sylow `p`-subgroup of `Z x`, viewed inside `G`, is contained in
`Z x`.
-/
lemma P_of_Z_le_Z (x : G) : P_of_Z p x ≤ Z x := by
  rw [P_of_Z]
  apply Subgroup.map_le_iff_le_comap.mpr
  intro g _
  exact g.property


/--
If every element of `C` commutes with every element of `P`, then every element
of `C ⊔ P` can be written as `c * p`.
-/
lemma sup_decompose_of_commute
    {C P : Subgroup G}
    (hcomm : ∀ ⦃c p : G⦄, c ∈ C → p ∈ P → Commute c p) :
    ∀ {h : G}, h ∈ C ⊔ P → ∃ c ∈ C, ∃ p ∈ P, c * p = h := by
  intro h hh
  have eq_closure : C ⊔ P = Subgroup.closure ((C : Set G) ∪ P) := by
    symm
    simp [Subgroup.closure_union]
  rw [eq_closure] at hh
  refine Subgroup.closure_induction
    (p := fun x _ => ∃ c ∈ C, ∃ p ∈ P, c * p = x)
    ?mem ?one ?mul ?inv hh
  · rintro x (hx | hx)
    · exact ⟨x, hx, 1, P.one_mem, by simp⟩
    · exact ⟨1, C.one_mem, x, hx, by simp⟩
  · exact ⟨1, C.one_mem, 1, P.one_mem, by simp⟩
  · rintro a b - - ⟨c1, hc1, p1, hp1, rfl⟩ ⟨c2, hc2, p2, hp2, rfl⟩
    refine ⟨c1 * c2, C.mul_mem hc1 hc2, p1 * p2, P.mul_mem hp1 hp2, ?_⟩
    calc (c1 * c2) * (p1 * p2)
      _ = c1 * (c2 * p1) * p2 := by simp [mul_assoc]
      _ = c1 * (p1 * c2) * p2 := by rw [(hcomm hc2 hp1).eq]
      _ = (c1 * p1) * (c2 * p2) := by simp [mul_assoc]
  · rintro a - ⟨c, hc, p, hp, rfl⟩
    exact ⟨c⁻¹, C.inv_mem hc, p⁻¹, P.inv_mem hp,
      by simp [mul_inv_rev, (hcomm hc hp).inv_left.inv_right.eq]⟩

/--
The `p`-elementary structure on the subgroup associated to a `p`-regular element
`x`.

The underlying group is `Cyc x ⊔ P_of_Z p x`.
-/
@[expose] noncomputable def associatedSubgroup {x : G} (hx : IsPRegular p x) :
    PElementary p ((Cyc x ⊔ P_of_Z p x : Subgroup G)) := by
  let H : Subgroup G := Cyc x ⊔ P_of_Z p x

  let C_H : Subgroup H :=
    Subgroup.comap (Subgroup.subtype H) (Cyc x)

  let P_H : Subgroup H :=
    Subgroup.comap (Subgroup.subtype H) (P_of_Z p x)

  exact
  { C := C_H
    P := P_H

    C_isCyclic := by
      have hle : Cyc x ≤ H := le_sup_left
      let φ := Subgroup.subgroupOfEquivOfLe hle
      exact (MulEquiv.isCyclic φ.symm).mp (cyc_isCyclic (G := G) x)

    P_isPGroup := by
      have hle : P_of_Z p x ≤ H := le_sup_right
      exact IsPGroup.of_equiv
        (P_of_Z_isPGroup (p := p) x)
        (Subgroup.subgroupOfEquivOfLe hle).symm

    C_isPRegular := by
      intro c hc
      have hcG : ((c : H) : G) ∈ Cyc x := hc
      have hc_regG : IsPRegular p ((c : H) : G) :=
        IsPRegular.of_mem_zpowers p hcG hx
      simpa [IsPRegular, Subgroup.orderOf_coe] using hc_regG

    comm := by
      intro c q hc hq
      have hcG : ((c : H) : G) ∈ Cyc x := hc
      have hqG : ((q : H) : G) ∈ P_of_Z p x := hq
      have hqZ : ((q : H) : G) ∈ Z x :=
        P_of_Z_le_Z (p := p) x hqG
      have hcommG : Commute ((c : H) : G) ((q : H) : G) :=
        commute_of_mem_Z_of_mem_Cyc (x := x) hqZ hcG
      apply Subtype.ext
      exact hcommG.eq

    decompose := by
      intro h
      have hh : ((h : H) : G) ∈ H := h.property
      rcases sup_decompose_of_commute
          (G := G)
          (C := Cyc x)
          (P := P_of_Z p x)
          (by
            intro c q hc hq
            have hqZ : q ∈ Z x := P_of_Z_le_Z (p := p) x hq
            exact commute_of_mem_Z_of_mem_Cyc (x := x) hqZ hc)
          hh with ⟨c, hc, q, hq, h_eq⟩
      refine ⟨⟨c, Subgroup.mem_sup_left hc⟩, hc,
              ⟨q, Subgroup.mem_sup_right hq⟩, hq, ?_⟩
      ext
      exact h_eq
}


/--
In the `p`-elementary subgroup associated to a `p`-regular element `r`, the
elements whose `p`-regular part is `r` are exactly the elements of the coset
`r * P_of_Z p r`.
-/
lemma mem_associatedSubgroup_fiber [Fact p.Prime]
    {r : G} (hr : IsPRegular p r)
    (h : ↥(Subgroup.zpowers r ⊔ P_of_Z p r)) :
    Group.pRegular p (h : G) = r ↔ ∃ s ∈ P_of_Z p r, (h : G) = r * s := by
  let H := Subgroup.zpowers r ⊔ P_of_Z p r
  let eH := associatedSubgroup (p := p) hr
  have hf : IsOfFinOrder (h : G) := by
    have hfH : IsOfFinOrder h := eH.isOfFinOrder h
    exact (Submonoid.isOfFinOrder_coe (x := h)).2 hfH
  constructor
  · intro h_reg_is_s
    let s := Group.pSingular p (h : G)
    have h_decomp : (h : G) = r * s := by
      simp only [← h_reg_is_s]
      rw [Group.pDecomp' p hf]
    use s
    constructor
    · have s_in_H : s ∈ H := by
        rw [eq_inv_mul_iff_mul_eq.mpr h_decomp.symm]
        apply Subgroup.mul_mem
        · apply Subgroup.inv_mem
          apply Subgroup.mem_sup_left
          simp only [Subgroup.mem_zpowers]
        · exact h.property
      have hsH : (⟨s, s_in_H⟩ : H) ∈ eH.P := by
        rw [eH.mem_P_iff_pSingular]
        exact
          (IsPSingular.subtype_iff p (x := ⟨s, s_in_H⟩)).1
              (Group.isPSingular_pSingular p (h : G))
      exact hsH
    · exact h_decomp
  · rintro ⟨s, hs, h_eq⟩
    rw [h_eq]
    have hsr_fin : IsOfFinOrder (r * s) := by
      simpa [← h_eq] using hf
    apply Group.pRegular_mul_eq_self_of_pSingular_commute p hsr_fin
    · exact hr
    · have s_in_H : s ∈ H := Subgroup.mem_sup_right hs
      have hsH : (⟨s, s_in_H⟩ : H) ∈ eH.P := hs
      have : IsPSingular p (⟨s, s_in_H⟩ : H) := (eH.mem_P_iff_pSingular).mp hsH
      exact (IsPSingular.subtype_iff p (x := ⟨s, s_in_H⟩)).2 this
    · have h_comm := P_of_Z_le_Z (p := p) r hs
      simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff] at h_comm
      exact (commute_iff_eq r s).mpr (h_comm r rfl)


end PElementary

namespace IsPElementary

open BrauerInduction


end IsPElementary

end CFSG.BrauerInduction
