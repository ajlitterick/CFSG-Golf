module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.AutETable

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native

@[expose] def tblMulIdx (n : ℕ) (E : Array Table) (a b : ℕ) : ℕ :=
  let p := compT n E[a]! E[b]!
  ((List.range E.size).find? fun c => tblEq n p E[c]!).getD 0

@[expose] def tblClosedOK (n : ℕ) (E : Array Table) : Bool :=
  (List.range E.size).all fun a => (List.range E.size).all fun b =>
    let c := tblMulIdx n E a b
    decide (c < E.size) && tblEq n (compT n E[a]! E[b]!) E[c]!

theorem tblClosedOK_spec {n : ℕ} {E : Array Table} (h : tblClosedOK n E = true) {a b : ℕ}
    (ha : a < E.size) (hb : b < E.size) :
    tblMulIdx n E a b < E.size ∧
      tblEq n (compT n E[a]! E[b]!) E[tblMulIdx n E a b]! = true := by
  simp only [tblClosedOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact h a ha b hb

namespace EnumSpec

variable {n : ℕ} {gens L : Array Table}

theorem inj (h : EnumSpec n gens L) {a b : ℕ} (ha : a < L.size) (hb : b < L.size)
    (hab : tablePerm n L[a]! = tablePerm n L[b]!) : a = b := by
  have hnd := h.nodup
  have ha' : a < (L.toList.map (tablePerm n)).length := by simpa using ha
  have hb' : b < (L.toList.map (tablePerm n)).length := by simpa using hb
  refine (hnd.getElem_inj_iff (hi := ha') (hj := hb')).1 ?_
  simpa [getElem!_pos L a ha, getElem!_pos L b hb] using hab

end EnumSpec

theorem tablePerm_zero_of_enumOK {n m : ℕ} (hn : n < 2 ^ 32) {gens : Array Table}
    {E : Array Table × Array ℕ × Array ℕ} {size : ℕ} (h : enumOK n m gens E size = true) :
    0 < E.1.size ∧ tablePerm n E.1[0]! = 1 := by
  simp only [enumOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨-, htree⟩, -⟩, -⟩, -⟩ := h
  simp only [mulTreeOK, Bool.and_eq_true, decide_eq_true_eq] at htree
  exact ⟨htree.1.1, tablePerm_eq (rep_of_tblEq (Rep.idT hn) htree.1.2)⟩

theorem rootSet_eq_image_wRoots {n : ℕ} {X : Subgroup (Equiv.Perm (Fin n))} {tT : Table}
    {cg W : Array Table} (htperm : permOK n tT = true) (hWs : EnumSpec n cg W)
    (hrperm : ∀ r ∈ wRoots n tT W, permOK n r = true)
    (hcg : closure (tp n '' {x | x ∈ cg}) =
      X ⊓ centralizer ({tp n tT} : Set (Equiv.Perm (Fin n)))) :
    rootSet X (tp n tT) = tp n '' {x | x ∈ wRoots n tT W} := by
  have ht : Rep n tT (tp n tT) := rep_tp htperm
  ext x
  constructor
  · rintro ⟨hxX, hxx⟩
    have hcomm : x * tp n tT = tp n tT * x := by rw [← hxx, ← mul_assoc]
    have hxK : x ∈ closure (tp n '' {x | x ∈ cg}) := by
      rw [hcg]
      exact ⟨hxX, mem_centralizer_singleton_iff.2 hcomm⟩
    obtain ⟨T, hTW, hT⟩ := hWs.cover_mem hxK
    have hTr : T ∈ wRoots n tT W := by
      refine Array.mem_filter.2 ⟨hTW, ?_⟩
      exact (tblEq_iff_eq (Rep.compT hT hT) ht).2 hxx
    exact ⟨T, hTr, rep_unique (rep_tp (hrperm T hTr)) hT⟩
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨h1, h2⟩ := Array.mem_filter.1 hr
    have hrr := rep_tp (hrperm r hr)
    obtain ⟨-, hmem⟩ := hWs.rep_mem h1
    rw [hcg, tablePerm_eq hrr] at hmem
    exact ⟨hmem.1, (tblEq_iff_eq (Rep.compT hrr hrr) ht).1 h2⟩


@[expose] def AutEClass (X : Type*) [Group X] : Prop :=
  ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → AutEFact ↥(rootGroup X t)

theorem AutEFact.rootGroup_map {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {t : X}
    (h : AutEFact ↥(rootGroup X t)) : AutEFact ↥(rootGroup Y (e t)) := by
  have hroots : {y : Y | y * y = e t} = e '' {x : X | x * x = t} := by
    ext y
    constructor
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact hy
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq, ← map_mul]
      exact congrArg e hx
  have hE : (rootGroup X t).map e.toMonoidHom = rootGroup Y (e t) := by
    unfold rootGroup
    rw [hroots, MonoidHom.map_closure]
    rfl
  exact AutEFact.of_mulEquiv
    (((rootGroup X t).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr hE)) h

theorem AutEClass.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : AutEClass X) : AutEClass Y := by
  intro t ht2 ⟨g, hg⟩
  have := (h (e.symm t) (by rw [MulEquiv.orderOf_eq]; exact ht2)
    ⟨e.symm g, by rw [← map_mul, hg]⟩).rootGroup_map e
  rw [MulEquiv.apply_symm_apply] at this
  exact this

theorem AutEClass.of_class {X : Type*} [Group X] (t₀ : X) (h₀ : AutEFact ↥(rootGroup X t₀))
    (hcls : ∀ t : X, orderOf t = 2 → (∃ g : X, g * g = t) → ∃ g : X, t = g * t₀ * g⁻¹) :
    AutEClass X := by
  intro t ht2 hsq
  obtain ⟨g, rfl⟩ := hcls t ht2 hsq
  exact h₀.rootGroup_map (MulAut.conj g)

end CFSG.EvenSporadicStandard.Fin76b
