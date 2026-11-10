module

public import CFSG.Quasithin.EmptyFaithful.S152NBasic
public import CFSG.Quasithin.EmptyFaithful.S152FinKLA
public import CFSG.Quasithin.EmptyFaithful.S14113Layer
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.EmptyFaithful.S152Stmts

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.S152N

variable {G : Type} [Group G] [Finite G]

namespace S152Obs

omit [Finite G] in
theorem le_normalizer_inf_centralizer {K A V : Subgroup G}
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hKA : K ≤ Subgroup.normalizer (A : Set G)) :
    K ≤ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  refine S152Fin.le_normalizer_of_conj fun g hg x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hKA hg) x).mp hx.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (hKV (K.inv_mem hg)) v).mp hv
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hx.2 _ hv'
  calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [← h1]
    _ = g * x * g⁻¹ * v := by group


end S152Obs

theorem amalgamHypV_normalizer {T Mc M H : Subgroup G} (hs : Setting152 T Mc M) (hH : IsHStar T M H)
    (h1519 : Lemma1519Concl T Mc M) :
    AmalgamHypV ((M ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) ⊔ H)
      (M ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) H T
      (V154 T Mc M) := by
  have hTM : T ≤ M := hs.mf.1.1.2
  have hMV : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := le_normalizer_V154 T Mc M
  have hTN : T ≤ M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) :=
    le_inf hTM (S152Obs.le_normalizer_inf_centralizer (hTM.trans hMV) Subgroup.le_normalizer)
  have hSyl : IsSylowTwoOf T (M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) :=
    F7.isSylowTwoOf_mono_right (isSylowTwoOf_of_le151 hs.qtfe.sylow hTM) hTN inf_le_left
  refine ⟨⟨rfl, h1519.six_charTwo, hSyl, isSylowTwoOf_hStar hs hH, ?_⟩, h1519.six_reduced, ?_⟩
  ·
    by_contra hne
    obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hne
    have hM'N : InM (M ⊓ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)) M' :=
      ⟨hM'.1, le_sup_left.trans hM'.2⟩
    have hM'M : M' = M := h1519.five.2 M' hM'N
    exact hH.2.1 (hM'M ▸ (le_sup_right.trans hM'.2))
  ·
    set N : Subgroup G := M ⊓ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G) with hN
    have hRN : T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ N :=
      (inf_le_left : T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ T).trans hTN
    have hNV : N ≤ Subgroup.normalizer (V154 T Mc M : Set G) := inf_le_left.trans hMV
    have hCn : N ≤ Subgroup.normalizer ((N ⊓ Subgroup.centralizer (V154 T Mc M : Set G) :
        Subgroup G) : Set G) := S152Obs.le_normalizer_inf_centralizer hNV Subgroup.le_normalizer
    have hRpc : pCoreOf 2 N = T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := h1519.six_pCore
    apply le_antisymm
    · exact le_pCoreOf_of_le_normalizer 2 (le_inf hRN inf_le_right)
        ((inf_le_left : N ⊓ Subgroup.centralizer (V154 T Mc M : Set G) ≤ N).trans
          (inf_le_right : N ≤ Subgroup.normalizer
            ((T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) : Subgroup G) : Set G)))
        (hs.qtfe.sylow.1.to_le inf_le_left)
    · calc pCoreOf 2 (N ⊓ Subgroup.centralizer (V154 T Mc M : Set G))
          ≤ pCoreOf 2 N := F7.pCoreOf_mono_of_le_normalizer inf_le_left hCn
        _ = T ⊓ Subgroup.centralizer (V154 T Mc M : Set G) := hRpc


end CFSG.Quasithin
