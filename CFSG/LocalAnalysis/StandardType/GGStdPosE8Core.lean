module

public import CFSG.LocalAnalysis.StandardType.GGStdPosLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.LieType.Steinberg.Adjoint.Presentation
import CFSG.LocalAnalysis.StandardType.GGStdPosIsogCore
import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint

namespace StdPosExc

theorem mem_ggTorus_adjDatum
    {τ : Tag} {F : RootOperatorFamily τ} {K : Type} [Field K]
    {v : adjointGroup τ K} (hv : (v : ModGL τ K) ∈ torusGroup τ K) :
    v ∈ ggTorus (adjDatum F K) := by
  simp only [ggTorus, Subgroup.mem_iInf]
  intro γ hγ
  have hγ' : IsRoot τ γ := mem_adjDatum_roots.1 hγ
  have hle : torusGroup τ K ≤ (Subgroup.normalizer
      ((adjDatum F K).rootGroup γ : Set (adjointGroup τ K))).map (adjointGroup τ K).subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, s⟩, rfl⟩
    refine Subgroup.mem_map.2 ⟨torusElement τ K i s, ?_, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨torusElement_conj_mem i s hγ', fun hx => ?_⟩
    have h := torusElement_conj_mem (F := F) i s⁻¹ hγ' hx
    have hinv : torusElement τ K i s⁻¹ = (torusElement τ K i s)⁻¹ :=
      map_inv (torusHom (τ := τ) K i) s
    have e : (torusElement τ K i s)⁻¹ * (torusElement τ K i s * x * (torusElement τ K i s)⁻¹) *
        (torusElement τ K i s)⁻¹⁻¹ = x := by group
    rwa [hinv, e] at h
  obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.1 (hle hv)
  rwa [show w = v from Subtype.ext hwv] at hw

theorem exists_stdPos_e8
    {F : Type} [Field F] [Finite F] [CharP F 2] {G : Type} [Group G] [Finite G]
    {ψ : adjointGroup .E8 F →* G} {p : ℕ} {Bs : Subgroup G}
    (hker : ψ.ker ≤ Subgroup.center (adjointGroup .E8 F)) (hBs : IsElemAbelian p Bs)
    (hinn : ∀ b ∈ Bs, GGPsiInnerDiag (e8Datum F) ψ b)
    (hc : p ^ 8 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (ψ.range : Set G)) ≤ Nat.card ↥Bs)
    (hT : GGExcToralRankInput .E8 F p) :
    ∃ s : adjointGroup .E8 F,
      GGKGPosStdPos (e8Datum F) (ψ.comp (MulAut.conj s).toMonoidHom) Bs :=
  exists_stdPos_of_toral (V := TableBExc.torusPow .E8 F p) (r := 8) center_adjointGroup_eq_bot
    hker (fun _ hv => mem_ggTorus_adjDatum (TableBExc.mem_torusPow.1 hv).1)
    (fun E hE hE8 => (hT E hE hE8).imp fun _ h => h.le) hBs
    (fun b hb => PsiDiag.Adj.exists_mem_centralizer_E8 ψ hker (hinn b hb)) hc

end StdPosExc

end CFSG.StandardType

end
