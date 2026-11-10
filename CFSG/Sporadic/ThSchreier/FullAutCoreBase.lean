
module

public import CFSG.Sporadic.ThSchreier.TwoGenerateBase
public import CFSG.Sporadic.ThSchreier.CoreHyperplaneBase
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public meta import CFSG.Sporadic.ThSchreier.Text
public meta import CFSG.Sporadic.ThSchreier.RowBase
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase
public meta import CFSG.Sporadic.ThSchreier.WordsBase
public meta import CFSG.Sporadic.ThSchreier.LocalDataBase
public meta import CFSG.Sporadic.ThSchreier.TransporterBase
public meta import Certificates.Data.CFSGNative.Th.Base
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase
public meta import CFSG.Sporadic.ThSchreier.CentralizerDataBase
public meta import CFSG.Sporadic.ThSchreier.RigidityBase
public meta import CFSG.Sporadic.ThSchreier.Enc8

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.ComponentClassification.OuterAutomorphisms

theorem inner_eq_top_of_allInner {K : Type*} [Group K]
    (h : ∀ α : MulAut K, ∃ x : K, α = MulAut.conj x) : inner K = ⊤ := by
  refine eq_top_iff.2 fun α _ => ?_
  obtain ⟨x, rfl⟩ := h α
  exact ⟨x, rfl⟩

theorem inner_eq_top_of_equiv {K L : Type*} [Group K] [Group L] (e : K ≃* L)
    (h : inner L = ⊤) : inner K = ⊤ := by
  have hm := inner_map_congr e
  rw [h] at hm
  have hc := Subgroup.comap_map_eq_self_of_injective (f := (MulAut.congr e).toMonoidHom)
    (MulAut.congr e).injective (inner K)
  rw [hm, Subgroup.comap_top] at hc
  exact hc.symm

theorem subsingleton_outer_of_inner
    {K : Type*} [Group K] (h : inner K = ⊤) :
    Subsingleton (Outer K) := by
  refine ⟨fun p q => ?_⟩
  induction p using QuotientGroup.induction_on with
  | H α =>
    induction q using QuotientGroup.induction_on with
    | H β =>
      rw [QuotientGroup.eq, h]
      exact Subgroup.mem_top _

end CFSG.Sporadic.ThSchreier
