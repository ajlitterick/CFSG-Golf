module

public import CFSG.Quasithin.Background.HZCoc24
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Milestones.ASVolI.H13

public section

open scoped Pointwise

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Coc24

@[expose] def colF (j : Fin 6) : Finset (Fin 24) := Finset.univ.filter fun i => colOf i = j

theorem mem_colF {j : Fin 6} {i : Fin 24} : i ∈ colF j ↔ colOf i = j := by simp [colF]

theorem card_colF (j : Fin 6) : (colF j).card = 4 := by
  fin_cases j <;> decide

theorem colF_injective : Function.Injective colF := by
  intro a b h
  have h1 : (⟨4 * (a : ℕ), by omega⟩ : Fin 24) ∈ colF a :=
    mem_colF.2 (Fin.ext (by simp only [colOf]; omega))
  rw [h, mem_colF] at h1
  rw [← h1]
  exact Fin.ext (by simp only [colOf]; omega)

@[expose] def S0 : Finset (Finset (Fin 24)) := Finset.univ.image colF

theorem mem_S0 (j : Fin 6) : colF j ∈ S0 := Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩


theorem eY_smul {σ : S24} (Y : Finset (Fin 24)) : eY (σ • Y) = G6.permAct 24 σ (eY Y) := by
  rw [smul_finset_eq_map, permAct_eY]

theorem isOctad_smul {σ : S24} (hσ : σ ∈ AutPerm) {O : Finset (Fin 24)} (h : IsOctad O) :
    IsOctad (σ • O) :=
  ⟨by rw [Finset.card_smul_finset]; exact h.1, by
    rw [eY_smul]; exact (preserves_cocode hσ).2 _ h.2⟩

theorem isSextet_smul {σ : S24} (hσ : σ ∈ AutPerm) {S : Finset (Finset (Fin 24))}
    (h : IsSextet S) : IsSextet (σ • S) := by
  obtain ⟨hc, h4, hd, hu, ho⟩ := h
  refine ⟨by rw [Finset.card_smul_finset]; exact hc, ?_, ?_, ?_, ?_⟩
  · intro B hB
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_smul_finset.1 hB
    rw [Finset.card_smul_finset]
    exact h4 B₁ hB₁
  · intro B hB B' hB' hne
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_smul_finset.1 hB
    obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_smul_finset.1 hB'
    have h12 : B₁ ≠ B₂ := fun e => hne (by rw [e])
    rw [smul_finset_eq_map, smul_finset_eq_map, Finset.disjoint_map]
    exact hd B₁ hB₁ B₂ hB₂ h12
  · ext x
    simp only [Finset.mem_biUnion, id, Finset.mem_univ, iff_true]
    have hx : σ⁻¹ x ∈ S.biUnion id := by rw [hu]; exact Finset.mem_univ _
    obtain ⟨B₁, hB₁, hxB⟩ := Finset.mem_biUnion.1 hx
    exact ⟨σ • B₁, Finset.mem_smul_finset.2 ⟨B₁, hB₁, rfl⟩,
      Finset.mem_smul_finset.2 ⟨σ⁻¹ x, hxB, by simp⟩⟩
  · intro B hB B' hB' hne
    obtain ⟨B₁, hB₁, rfl⟩ := Finset.mem_smul_finset.1 hB
    obtain ⟨B₂, hB₂, rfl⟩ := Finset.mem_smul_finset.1 hB'
    have h12 : B₁ ≠ B₂ := fun e => hne (by rw [e])
    rw [← Finset.smul_finset_union]
    exact isOctad_smul hσ (ho B₁ hB₁ B₂ hB₂ h12)


end CFSG.Quasithin.H153
