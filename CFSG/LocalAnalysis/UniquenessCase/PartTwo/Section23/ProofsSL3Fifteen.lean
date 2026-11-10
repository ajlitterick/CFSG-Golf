module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.SL3Early
public import CFSG.GroupTheory.PCoreQuotientSylow
public import CFSG.GroupTheory.PowMemSupOfPGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem conjClosure_conjClosure_of_le {M K W : Subgroup G} (hKM : K ≤ M) :
    conjClosure M (conjClosure K W) = conjClosure M W := by
  refine le_antisymm ?_ ?_
  · refine uc22p22v_conjClosure_le (uc22p22v_le_normalizer_conjClosure M W) ?_
    exact uc22p22v_conjClosure_le
      (hKM.trans (uc22p22v_le_normalizer_conjClosure M W))
      (uc22p22v_le_conjClosure M W)
  · refine uc22p22v_conjClosure_le
      (uc22p22v_le_normalizer_conjClosure M (conjClosure K W)) ?_
    exact (uc22p22v_le_conjClosure K W).trans
      (uc22p22v_le_conjClosure M (conjClosure K W))


private theorem s23fifteen_E_eq_iSup {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h1930 : H1930 D)
    (hKW : H1930 D → ∀ c : Ctx2311 D Ch, conjClosure c.K c.W = c.V) :
    c.E = ⨆ k : ↥D.M, c.W.map (MulAut.conj (k : G)).toMonoidHom := by
  have hKM : c.K ≤ D.M := (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  rw [Ctx23L.E, ← hKW h1930 c]
  exact (conjClosure_conjClosure_of_le hKM).trans (uc22br4_conjClosure_eq D.M c.W)


private theorem isElemAbelian_E_of_le_centralizer {D : Data G} {Ch : Choice2011 G}
    (c : Ctx2311 D Ch) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hcent : c.E ≤ Subgroup.centralizer (c.V : Set G)) : IsElemAbelian 2 c.E := by
  have hVleE : c.V ≤ c.E := uc22p22v_le_conjClosure D.M c.V
  have hMnormE : D.M ≤ Subgroup.normalizer (c.E : Set G) :=
    uc22p22v_le_normalizer_conjClosure D.M c.V
  have hEeq : c.E = ⨆ k : ↥D.M, c.V.map (MulAut.conj (k : G)).toMonoidHom := by
    rw [Ctx23L.E]
    exact uc22br4_conjClosure_eq D.M c.V
  have hVk_ea : ∀ k : ↥D.M, IsElemAbelian 2
      (c.V.map (MulAut.conj (k : G)).toMonoidHom) :=
    fun k => (c.isElemAbelian_V h4 h1930).map _
  have hVk_cent : ∀ k : ↥D.M,
      c.V.map (MulAut.conj (k : G)).toMonoidHom ≤
        Subgroup.centralizer (c.E : Set G) := by
    intro k v hv
    obtain ⟨v0, hv0, rfl⟩ := Subgroup.mem_map.mp hv
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    change e * ((k : G) * v0 * (k : G)⁻¹) = ((k : G) * v0 * (k : G)⁻¹) * e
    have hkE : (k : G)⁻¹ * e * (k : G) ∈ c.E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hMnormE (D.M.inv_mem k.2)) e).mp he
    have hv0c : v0 * ((k : G)⁻¹ * e * (k : G)) =
        ((k : G)⁻¹ * e * (k : G)) * v0 :=
      (Subgroup.mem_centralizer_iff.mp (hcent hkE)) v0 hv0
    calc e * ((k : G) * v0 * (k : G)⁻¹)
        = (k : G) * ((k : G)⁻¹ * e * (k : G) * v0) * (k : G)⁻¹ := by group
      _ = (k : G) * (v0 * ((k : G)⁻¹ * e * (k : G))) * (k : G)⁻¹ := by rw [hv0c]
      _ = ((k : G) * v0 * (k : G)⁻¹) * e := by group
  have hpair : ∀ i j : ↥D.M,
      ∀ x ∈ c.V.map (MulAut.conj (i : G)).toMonoidHom,
      ∀ y ∈ c.V.map (MulAut.conj (j : G)).toMonoidHom, x * y = y * x := by
    intro i j x hx y hy
    have hyE : y ∈ c.E := by
      rw [hEeq]
      exact Subgroup.mem_iSup_of_mem j hy
    exact ((Subgroup.mem_centralizer_iff.mp (hVk_cent i hx)) y hyE).symm
  rw [hEeq]
  exact CFSG.Quasithin.CosetGeom.isElemAbelian_iSup _ hVk_ea hpair


end CFSG.LocalAnalysis.UniquenessCase.UC22
