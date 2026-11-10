module

public import CFSG.Monster.B.GSide.RecognitionBT2
public import CFSG.Monster.B.GSide.BT2Bridge
public import CFSG.Monster.B.GSide.HSylowBeta
public import CFSG.Monster.B.GSide.HInnerFusionY3
public import CFSG.Monster.B.GSide.EdgeQCertDC
public import CFSG.Monster.B.GSide.EdgeQCertWit
public import CFSG.Monster.B.GSide.TwoDCentralizer
public import CFSG.Monster.B.TwoA.Amalgam.NativeChain
public import CFSG.Monster.B.TwoA.Fischer.AmbientRootNative

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Amalgam

theorem exists_mem_FA :
    ∃ β : vStab cv0, β ∈ FA := by
  obtain ⟨u, hu⟩ := sphereDistThree_nonempty_of_ambient ambientRootOrbitsHyp cv0
  exact ⟨⟨clabelS u, clabelS_mem_vStab_cv0_of_dist_three hu⟩, u, hu, rfl⟩

theorem hc5ii_of_extremal
    {X : Subgroup (vStab cv0)}
    (h6 : ∀ u ∈ (Subgroup.center X).map X.subtype ⊓ ⁅X, X⁆, u = 1 ∨ cV0 * u ∈ RA ∨
      (u * u = 1 ∧ u ∈ commutator (vStab cv0) ∧ u ∉ RA ∧ u ∉ RB ∧ u ≠ cV0 ∧
        rkH u = 2048 ∧ rkH (cV0 * u) = 2168)) :
    ∀ u ∈ centerInfCommutator X, u ≠ 1 →
      cV0 * u ∈ RA ∨ (u * u = 1 ∧ rkH u = 2048 ∧ rkH (cV0 * u) ≠ 1860) := by
  intro u hu hu1
  rcases (h6 u hu).resolve_left hu1 with h | ⟨h2, -, -, -, -, hr, hr'⟩
  · exact Or.inl h
  · exact Or.inr ⟨h2, hr, by rw [hr']; decide⟩

theorem gamma2D_of_gold
    (hGold : GoldschmidtTheorem) :
    ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] {d : G}, d ≠ 1 →
      ∀ (ψ : Subgroup.centralizer {d} ≃* vStab cv0) (Φ : Shat →* G),
      (∀ a : vStab cv0, Φ a = psiInvHom ψ a) →
      conjugatesOf d ∩ (Φ.range : Set G) = dZero Φ.range d →
      (∀ s : Shat, orderOf s = 2 → rankS s = 2048 → Subgroup.centralizer {Φ s} ≤ Φ.range) →
      ∀ s : Shat, orderOf s = 2 → rankS s = 2168 → Subgroup.centralizer {Φ s} ≤ Φ.range := by
  intro G _ _ _ d hd1 ψ Φ hΦ hDM _ s hs hrk
  exact centralizer_le_range_of_rankS_eq_2168_of_gold hd1 ψ Φ hΦ hDM hGold hs hrk

theorem recognition_models_of_gold
    (hGold : GoldschmidtTheorem)
    (d₀ : NativeSporadic.B) (hd₀ : orderOf d₀ = 2)
    (hrank : Matrix.rank (d₀.val.val - 1) = 1860)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (d : G) (hd : orderOf d = 2)
    (hcentralizer : Nonempty (Subgroup.centralizer ({d} : Set G) ≃*
      Subgroup.centralizer ({d₀} : Set NativeSporadic.B))) :
    Nonempty (G ≃* NativeSporadic.B) := by
  obtain ⟨β, hβ⟩ := exists_mem_FA
  obtain ⟨X, hXβ, hX⟩ := exists_sylow_centralizer_beta hβ
  obtain ⟨hβ2, hβK, ⟨T, hXT⟩, hcX, hβX, hXsyl, hZ, hcU, hβcU, hHC5, h6⟩ :=
    native_HC5_extremal_data hβ hXβ hX
  exact recognition_of_inputs bt2C1 T hβ2 hβK hXT hcX hβX hXβ hXsyl hX hZ hcU hβcU hHC5
    (hc5ii_of_extremal h6) hY3_native_all edgeQ_unique_center edgeQCert_hWit hGold
    (gamma2D_of_gold hGold) d₀ hd₀ hrank G d hd hcentralizer

end CFSG.Monster.B.GSide
