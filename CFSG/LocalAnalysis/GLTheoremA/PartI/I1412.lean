module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
public import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator
  (fixSubgroup mem_fixSubgroup glaPComponent_map_fixSubgroup)
open CFSG.ComponentClassification.PerfectAutomorphisms
  (centerQuotientHom onCenterQuotient_apply_mk)

@[expose] def DownLe (p j : ℕ) (S : Type) [Group S] : Prop :=
  ∀ α : MulAut S, α ^ p = 1 → ∀ I : Subgroup S, GLAPComponent p (fixSubgroup α) I →
    kLevel p (PSimple p I) ≤ j


private noncomputable def i1412QuotEquiv {S S' : Type} [Group S] [Group S'] (p : ℕ)
    (e : S ≃* S') (X : Subgroup S) :
    (↥X ⧸ GLAPPrimeCore p ↥X) ≃*
      (↥(X.map e.toMonoidHom) ⧸ GLAPPrimeCore p ↥(X.map e.toMonoidHom)) :=
  QuotientGroup.congr _ _ (X.equivMapOfInjective e.toMonoidHom e.injective)
    (glaPPrimeCore_map_iso p (X.equivMapOfInjective e.toMonoidHom e.injective))

private theorem i1412_map_subgroupOf {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (X K : Subgroup S) :
    (K.subgroupOf X).map (X.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom =
      (K.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ⟨x.1, Subgroup.mem_subgroupOf.1 hx, rfl⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    obtain ⟨w, hwX, hwy⟩ := y.2
    have hzw : z = w := e.injective (hzy.trans hwy.symm)
    have hzX : z ∈ X := by
      rw [hzw]
      exact hwX
    exact ⟨⟨z, hzX⟩, Subgroup.mem_subgroupOf.2 hz, Subtype.ext hzy⟩

private theorem i1412_barX_quotEquiv {S S' : Type} [Group S] [Group S'] (p : ℕ) (e : S ≃* S')
    (X K : Subgroup S) :
    ((K.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map
        (i1412QuotEquiv p e X).toMonoidHom =
      ((K.map e.toMonoidHom).subgroupOf (X.map e.toMonoidHom)).map
        (QuotientGroup.mk' (GLAPPrimeCore p ↥(X.map e.toMonoidHom))) := by
  have hcomm : (i1412QuotEquiv p e X).toMonoidHom.comp
      (QuotientGroup.mk' (GLAPPrimeCore p ↥X)) =
      (QuotientGroup.mk' (GLAPPrimeCore p ↥(X.map e.toMonoidHom))).comp
        (X.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    rfl
  rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, i1412_map_subgroupOf]

private theorem i1412_map_map_symm {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (K : Subgroup S) : (K.map e.toMonoidHom).map e.symm.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id S := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem i1412_map_symm_map {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (K : Subgroup S') : (K.map e.symm.toMonoidHom).map e.toMonoidHom = K := by
  rw [Subgroup.map_map]
  have h : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id S' := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem i1412_glaPComponent_map {S S' : Type} [Group S] [Group S'] {p : ℕ} (e : S ≃* S')
    {X L : Subgroup S} (h : GLAPComponent p X L) :
    GLAPComponent p (X.map e.toMonoidHom) (L.map e.toMonoidHom) := by
  obtain ⟨hLX, hsn, hcomp, hmin⟩ := h
  refine ⟨Subgroup.map_mono hLX, CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e hsn,
    ?_, ?_⟩
  · have h1 : IsComponentOf
        (((L.subgroupOf X).map (QuotientGroup.mk' (GLAPPrimeCore p ↥X))).map
          (i1412QuotEquiv p e X).toMonoidHom)
        ((⊤ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)).map (i1412QuotEquiv p e X).toMonoidHom) :=
      CFSG.SignalizerFunctorTheorem.TransportA.isComponentOf_map (i1412QuotEquiv p e X) hcomp
    have htop : Subgroup.map (i1412QuotEquiv p e X).toMonoidHom
        (⊤ : Subgroup (↥X ⧸ GLAPPrimeCore p ↥X)) = ⊤ :=
      Subgroup.map_top_of_surjective _ (i1412QuotEquiv p e X).surjective
    rw [htop, i1412_barX_quotEquiv] at h1
    exact h1
  · intro J' hJ' hJ'sn heq
    have hJe : (J'.map e.symm.toMonoidHom).map e.toMonoidHom = J' := i1412_map_symm_map e J'
    have hJL : J'.map e.symm.toMonoidHom < L := by
      refine lt_of_le_of_ne ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        obtain ⟨l, hl, hly⟩ := hJ'.le hy
        rw [← hly]
        simpa using hl
      · intro hEq
        apply hJ'.ne
        rw [← hJe, hEq]
    have hJsn : IsSubnormal (J'.map e.symm.toMonoidHom) X := by
      have h2 : IsSubnormal (J'.map e.symm.toMonoidHom)
          ((X.map e.toMonoidHom).map e.symm.toMonoidHom) :=
        CFSG.SignalizerFunctorTheorem.TransportA.isSubnormal_map e.symm hJ'sn
      rwa [i1412_map_map_symm e X] at h2
    refine hmin _ hJL hJsn ?_
    apply Subgroup.map_injective (f := (i1412QuotEquiv p e X).toMonoidHom)
      (i1412QuotEquiv p e X).injective
    rw [i1412_barX_quotEquiv, i1412_barX_quotEquiv, hJe]
    exact heq

theorem downLe_of_mulEquiv {p j : ℕ} {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : DownLe p j S) : DownLe p j S' := by
  intro α' hα' I' hI'
  have hα : MulAut.congr e.symm α' ^ p = 1 := by
    rw [← map_pow, hα', map_one]
  have hfix : fixSubgroup (MulAut.congr e.symm α') =
      (fixSubgroup α').map e.symm.toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      have hx' : e.symm (α' (e x)) = x := hx
      refine ⟨e x, ?_, by simp⟩
      have h4 := congrArg e hx'
      exact mem_fixSubgroup.2 (by simpa using h4)
    · rintro ⟨y, hy, rfl⟩
      show e.symm (α' (e (e.symm y))) = e.symm y
      have hy' : α' y = y := hy
      simp [hy']
  have hI : GLAPComponent p (fixSubgroup (MulAut.congr e.symm α'))
      (I'.map e.symm.toMonoidHom) := by
    rw [hfix]
    exact i1412_glaPComponent_map e.symm hI'
  have hle := h _ hα _ hI
  have f : PSimple p I' ≃* PSimple p (I'.map e.symm.toMonoidHom) :=
    QuotientGroup.congr _ _ (i1412QuotEquiv p e.symm I') (Subgroup.map_center_eq _)
  rwa [← kLevel_congr p f] at hle

section Central


end Central


end CFSG.LocalAnalysis.GLTheoremA
