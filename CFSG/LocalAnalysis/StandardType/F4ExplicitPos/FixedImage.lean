module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import CFSG.GroupTheory.LangNormOneDescent
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.LangPositionPart1
public import CFSG.LieType.Chevalley.EvenF4AutomorphismNormalForm
import CFSG.LocalAnalysis.EvenBN.G2.Automorphisms
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.BruhatNo117Part2
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.PinnedBaseChange
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.FixedTorus
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.AmbientActionPart1
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.E6FieldU3Misc
public import TauCeti.Algebra.CharP.Frobenius.Fixed
public import TauCeti.FieldTheory.Finite.SepClosedSubfield
public import CFSG.HardMathSupport.Solomon.Coordinator.I23_26Comp
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsAlt
public import CFSG.HardMathSupport.Solomon.Coordinator.I271HoldsHatSixCore
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCOut
public import CFSG.HardMathSupport.Solomon.LocalBalance.ONFacts

@[expose] public section

public noncomputable section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.StandardType.F4ExplicitPos.BaseChange

open CFSG.StandardType.F4ExplicitPos.RootBaseChange

open CFSG.StandardType.F4ExplicitPos.PinnedBaseChange

open CFSG.StandardType.F4ExplicitPos.FixedTorus

open CFSG.StandardType.F4ExplicitPos.BruhatNo117

open CFSG.StandardType.F4ExplicitPos.PositiveNo117

namespace CFSG.StandardType.F4ExplicitPos.FixedImage

def prodPinnedXR
    (R : Type*) [CommRing R] {m : ℕ}
    (α : Fin m → Fin Tag.F4.rank → ℤ) (c : Fin m → R) :
    (Module.End R (RootModule Tag.F4 R))ˣ :=
  (List.ofFn fun i => pinnedX Tag.F4 R (α i) (c i)).prod

theorem bcGL_prodPinnedXR
    {R S : Type} [Field R] [Field S] (f : R →+* S) {m : ℕ}
    (α : Fin m → Fin Tag.F4.rank → ℤ) (c : Fin m → R) :
    bcGL (τ := Tag.F4) f (prodPinnedXR R α c) =
      prodPinnedXR S α (fun i => f (c i)) := by
  unfold prodPinnedXR
  rw [map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.2 (funext fun i => bcGL_pinnedX (τ := Tag.F4) f (α i) (c i))

theorem map_bcGL_torusGroup_le
    {R S : Type} [Field R] [Field S] (φ : R →+* S) :
    (torusGroup Tag.F4 R).map (bcGL (τ := Tag.F4) φ) ≤ torusGroup Tag.F4 S := by
  rw [torusGroup, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).2 ?_
  rintro x ⟨y, ⟨⟨i, t⟩, rfl⟩, rfl⟩
  rw [bcGL_torusElt φ i t]
  exact Subgroup.subset_closure ⟨(i, Units.map φ.toMonoidHom t), rfl⟩

theorem fixed_posUnipotent_mem_map_adjointGroup
    {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {u : ModGL Tag.F4 Ω} (hu : u ∈ posUnipotent Tag.F4 Ω)
    (hfix : Units.map (entrywiseHom Fr) u = u) :
    u ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) := by
  classical
  obtain ⟨α, hαinj, hαrange⟩ :=
    exists_rootEnum (finite_of_forall_isRoot_pos (τ := Tag.F4)
      (S := {β : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 β ∧ 0 < height β}) (fun _ h => h))
  have hBij := (f4_positive_root_collection (R := Ω)).2 α hαinj hαrange
  have hFmat : (Units.map (entrywiseHom Fr) : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) = bcGL Fr := by
    rw [bcGL, ← bcEndHom_eq_entrywiseHom Fr]
  have hfixbc : bcGL Fr u = u := by rw [← hFmat]; exact hfix
  obtain ⟨c, hc⟩ := hBij.2.2 hu
  have hc' : prodPinnedXR Ω α c = u := by simpa [prodPinnedXR] using hc
  have hcfix : (fun i => Fr (c i)) = c := by
    apply hBij.2.1 (Set.mem_univ _) (Set.mem_univ _)
    change prodPinnedXR Ω α (fun i => Fr (c i)) = prodPinnedXR Ω α c
    rw [← bcGL_prodPinnedXR Fr α c, hc', hfixbc]
  have hcoord : ∀ i, Fr (c i) = c i := fun i => congrFun hcfix i
  have hrange : ∀ i, c i ∈ Set.range (algebraMap K Ω) := fun i => by
    apply mem_range_algebraMap_of_pow_card_eq
    rw [← hFr (c i), hcoord i]
  choose a ha using hrange
  have hfun : (fun i => algebraMap K Ω (a i)) = c := funext ha
  refine Subgroup.mem_map.2 ⟨prodPinnedXR K α a, ?_, ?_⟩
  · rw [prodPinnedXR]
    refine list_prod_mem fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
    exact pinnedX_mem_adjointGroup (τ := Tag.F4) (α i) (a i)
  · rw [bcGL_prodPinnedXR (algebraMap K Ω) α a, hfun, hc']

theorem f4_finite_field_fixed_eq_map
    {K Ω : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) =
      adjointGroup Tag.F4 Ω ⊓
        (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id (ModGL Tag.F4 Ω)) := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨g, hg, rfl⟩
    refine Subgroup.mem_inf.2
      ⟨bcGL_mem_adjointGroup (τ := Tag.F4) (algebraMap K Ω) hg, ?_⟩
    exact units_map_entrywiseHom_bcGL_algebraMap (τ := Tag.F4) Fr hFr g
  · intro x hx
    obtain ⟨hxadj, hxfix⟩ := Subgroup.mem_inf.1 hx
    have hxfix' : Units.map (entrywiseHom Fr) x = x := hxfix
    have hFmatbc : (Units.map (entrywiseHom Fr) : ModGL Tag.F4 Ω →* ModGL Tag.F4 Ω) =
        bcGL (τ := Tag.F4) Fr := by
      rw [bcGL, ← bcEndHom_eq_entrywiseHom Fr]
    have hfixbc : bcGL (τ := Tag.F4) Fr x = x := by rw [← hFmatbc]; exact hxfix'
    obtain ⟨w, h, hh, u, hu, v, hv, hgfac⟩ := f4_hfactor x hxadj
    set n := canonicalRep (coxeterSystem Tag.F4) Ω w with hn
    have hFr_n : bcGL (τ := Tag.F4) Fr n = n := by
      rw [hn, bcGL_canonicalRep (τ := Tag.F4) Fr (coxeterSystem Tag.F4) w]
    have hFr_h : bcGL (τ := Tag.F4) Fr h ∈ torusGroup Tag.F4 Ω :=
      map_bcGL_torusGroup_le Fr (Subgroup.mem_map_of_mem _ hh)
    have hFr_u : bcGL (τ := Tag.F4) Fr u ∈ posUnipotent Tag.F4 Ω := by
      have hle := map_bcGL_rootSpan_le (τ := Tag.F4) Fr
        ({β : Fin Tag.F4.rank → ℤ | IsRoot Tag.F4 β ∧ 0 < height β})
      exact hle (Subgroup.mem_map_of_mem _ hu)
    have hFr_v : bcGL (τ := Tag.F4) Fr v ∈ rootSpan Tag.F4 Ω (inversionSet w) :=
      map_bcGL_rootSpan_le (τ := Tag.F4) Fr (inversionSet w) (Subgroup.mem_map_of_mem _ hv)
    have hfac' : bcGL (τ := Tag.F4) Fr x =
        bcGL (τ := Tag.F4) Fr h * bcGL (τ := Tag.F4) Fr u * n * bcGL (τ := Tag.F4) Fr v := by
      rw [hgfac, map_mul, map_mul, map_mul, hFr_n]
    have hfac'' : x =
        bcGL (τ := Tag.F4) Fr h * bcGL (τ := Tag.F4) Fr u * n * bcGL (τ := Tag.F4) Fr v :=
      hfixbc.symm.trans hfac'
    obtain ⟨hhfix, hufix, hvfix⟩ :=
      f4_sameW_bruhat_unique (w := w) hh hFr_h hu hFr_u hv hFr_v (hgfac.symm.trans hfac'')
    have hfix_h : Units.map (entrywiseHom Fr) h = h := by rw [hFmatbc, ← hhfix]
    have hfix_u : Units.map (entrywiseHom Fr) u = u := by rw [hFmatbc, ← hufix]
    have hfix_v : Units.map (entrywiseHom Fr) v = v := by rw [hFmatbc, ← hvfix]
    have hvU : v ∈ posUnipotent Tag.F4 Ω :=
      rootSpan_le_posUnipotent (fun α hα => inversionSet_pos (w := w) hα) hv
    have hJ : h ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) :=
      fixed_torus_mem_map_adjointGroup (K := K) (Ω := Ω) Fr hFr hh hfix_h
    have hJu : u ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) :=
      fixed_posUnipotent_mem_map_adjointGroup (K := K) (Ω := Ω) Fr hFr hu hfix_u
    have hJv : v ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) :=
      fixed_posUnipotent_mem_map_adjointGroup (K := K) (Ω := Ω) Fr hFr hvU hfix_v
    have hJn : n ∈ (adjointGroup Tag.F4 K).map (bcGL (τ := Tag.F4) (algebraMap K Ω)) := by
      rw [hn, ← bcGL_canonicalRep (τ := Tag.F4) (algebraMap K Ω) (coxeterSystem Tag.F4) w]
      exact Subgroup.mem_map_of_mem _
        (canonicalRep_mem_adjointGroup (coxeterSystem Tag.F4) K w)
    rw [hgfac]
    exact mul_mem (mul_mem (mul_mem hJ hJu) hJn) hJv

theorem iotaF4_range
    {K Ω X : Type} [Field K] [Finite K] [Field Ω] [Algebra K Ω] [Group X] [Finite X]
    (ψ : adjointGroup Tag.F4 K →* X) (G0 : Subgroup X) (hG0 : ψ.range = G0)
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup Tag.F4 K))
    (hcenter : Subgroup.center (adjointGroup Tag.F4 K) = ⊥) :
    (CFSG.StandardType.F4ExplicitPos.AmbientAction.iotaF4 (L := Ω) ψ G0 hG0 hker hcenter).range =
      (CFSG.StandardType.F4ExplicitPos.AmbientAction.jF4 (K := K) (L := Ω)).range := by
  refine le_antisymm ?_ ?_
  · rintro x ⟨y, rfl⟩
    obtain ⟨u, rfl⟩ :=
      (CFSG.StandardType.F4ExplicitPos.AmbientAction.eF4 ψ G0 hG0 hker hcenter).surjective y
    exact ⟨u, (CFSG.StandardType.F4ExplicitPos.AmbientAction.iotaF4_e ψ G0 hG0 hker hcenter u).symm⟩
  · rintro x ⟨u, rfl⟩
    exact ⟨CFSG.StandardType.F4ExplicitPos.AmbientAction.eF4 ψ G0 hG0 hker hcenter u,
      CFSG.StandardType.F4ExplicitPos.AmbientAction.iotaF4_e ψ G0 hG0 hker hcenter u⟩

section ActualAutomorphismFixedImage
open CFSG.LieType.Chevalley


end ActualAutomorphismFixedImage

section FiniteNormLang

open CFSG.GroupTheory CFSG.StandardType.F4ExplicitPos.LangPosition
open CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley.F4NativeNormalForm


end FiniteNormLang

end CFSG.StandardType.F4ExplicitPos.FixedImage

end

end
