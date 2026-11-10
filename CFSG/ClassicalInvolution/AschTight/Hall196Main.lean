module

public import CFSG.ClassicalInvolution.AschTight.Sec19Targets4
public import CFSG.ClassicalInvolution.AschTight.Sec19DataT
public import CFSG.ClassicalInvolution.AschTight.S1911EtaY3
public import CFSG.ClassicalInvolution.AschTight.Hall196Basic
public import CFSG.ClassicalInvolution.AschTight.Hall196Syl
public import CFSG.ClassicalInvolution.AschTight.Hall196Wr2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem mem_inf_of_commute [IsSimpleGroup G] (hstar : C19_11aTmp p f) {K : Subgroup G} {z : G}
    {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}
    (hDT : Sec19DataT p f K z S W L t V) (ef : S1911.EtaFacts K z S W V) {x : G}
    (hx : x ∈ (S : Subgroup G) ⊓ sec19Y K z) (hxt : x * t = t * x) : x ∈ W ⊓ sec19Y K z := by
  have hd := hDT.toSec19Data
  have htb := hd.tight.toTightBranch
  have hI := isUniqueInvolution_of_tight htb
  have hxN := ef.normalizes hx
  have hxL : x ∈ Subgroup.normalizer (L : Set G) := by
    obtain ⟨g, rfl⟩ := CoreAssembly.single_class K L hDT.memL
    have h2 : g * z * g⁻¹ = t := (hI.conj g).eq hDT.invL
    refine centralizer_le_normalizer_conjSub htb g ?_
    rw [Subgroup.mem_centralizer_singleton_iff, h2]
    exact hxt
  have hxV : ∀ v ∈ V, x * v = v * x := by
    intro v hv
    have hvW := hDT.leW hv
    have h1 : x * v * x⁻¹ ∈ V := inf_le_of_etaFacts hDT ef
      ⟨(Subgroup.mem_normalizer_iff.mp hxL v).mp (le_of_sec19DataT hDT hv),
        (Subgroup.mem_normalizer_iff.mp hxN v).mp hvW⟩
    have h2 : x * v * x⁻¹ * v⁻¹ ∈ V := V.mul_mem h1 (V.inv_mem hv)
    have h3 : x * v * x⁻¹ * v⁻¹ ∈ sec19Y K z := by
      have hw : v * x⁻¹ * v⁻¹ ∈ sec19Y K z := by
        have hc := conjSub_sec19Y hd.tight (hd.hSz (hd.hWS hvW))
        rw [← hc]
        exact conj_mem_conjSub (Subgroup.inv_mem _ hx.2)
      have e : x * v * x⁻¹ * v⁻¹ = x * (v * x⁻¹ * v⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx.2 hw
    have h4 : x * v * x⁻¹ * v⁻¹ ∈ V ⊓ sec19Y K z := ⟨h2, h3⟩
    rw [ef.disj, Subgroup.mem_bot] at h4
    calc x * v = x * v * x⁻¹ * v⁻¹ * (v * x) := by group
      _ = v * x := by rw [h4, one_mul]
  have hxK : ∀ u ∈ W ⊓ K, x * u = u * x := by
    intro u hu
    have h1 := mem_centralizer_inf_of_mem_cStar S.isPGroup'
      (centralizerModOdd_le_cStar _ _ hx.2) hx.1
    exact ((Subgroup.mem_centralizer_iff.mp h1) u ⟨hd.hWS hu.1, hu.2⟩).symm
  have hxW : x ∈ (S : Subgroup G) ⊓ sec19Y K z ⊓ Subgroup.centralizer (W : Set G) := by
    refine ⟨hx, ?_⟩
    have hle : W ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [ef.supU]
      refine sup_le (fun u hu => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hxK u hu).symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (hxV v hv).symm
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
  exact ⟨hstar _ K z S W hd hxW, hx.2⟩


end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
