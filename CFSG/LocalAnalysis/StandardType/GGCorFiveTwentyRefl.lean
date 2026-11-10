module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridgeStab
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

section Quot

variable {G : Type} [Group G] [Finite G]


end Quot

section Conj

variable {G : Type} [Group G]

theorem ggGamma_conj_normalizer (L : Subgroup G) {B : Subgroup G}
    (hBN : B ≤ Subgroup.normalizer (L : Set G)) (g : Subgroup.normalizer (L : Set G)) (b : B)
    (hgb : (g : G) * b * (g : G)⁻¹ ∈ B) :
    L.normalizerMonoidHom g * ggGamma L hBN b * (L.normalizerMonoidHom g)⁻¹ =
      ggGamma L hBN ⟨(g : G) * b * (g : G)⁻¹, hgb⟩ := by
  ext l
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, normalizerMonoidHom_coe, ggGamma_coe,
    normalizerMonoidHom_coe, ggGamma_coe]
  push_cast
  group


end Conj

section Config

variable {G : Type} [Group G] [Finite G]


end Config

section Lab

variable {G : Type} [Group G]

@[expose] def GGInnerDiagOnLabel (S : ℕ → LargeEvenLabel → Prop) (p : ℕ) (Bs L : Subgroup G) :
    Prop :=
  LargeEvenMarking L (fun lab _ _ I _ θ => S p lab ∧ Bs ≤ Subgroup.normalizer (L : Set G) ∧
    ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)

theorem GGInnerDiagOn.label {Bs L : Subgroup G} (S : ℕ → LargeEvenLabel → Prop) (p : ℕ)
    (h : GGInnerDiagOn Bs L) : GGInnerDiagOnLabel (fun p lab => S p lab ∨ ¬ S p lab) p Bs L :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨em _, hP⟩) h

theorem GGInnerDiagOnLabel.elim_or {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ} {Bs L : Subgroup G}
    (h : GGInnerDiagOnLabel (fun p lab => S p lab ∨ T p lab) p Bs L) :
    GGInnerDiagOnLabel S p Bs L ∨ GGInnerDiagOnLabel T p Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hST, -⟩ := largeEvenRawDatum_exists hraw
  rcases hST with h | h
  · exact Or.inl ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩
  · exact Or.inr ⟨hperf, lab, hlab, largeEvenRawDatum_mono
      (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', h, hP⟩) hraw⟩

end Lab

@[expose] def GGPseudoReflStabModInputOn (S : ℕ → LargeEvenLabel → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J → GGInnerDiagOnLabel S p Bs L →
      ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs, GGIsPseudoReflection p φ →
        ∃ ψ ∈ ggAutomizer (ggG0 p B x L D J) Bs, (∀ b : ↥Bs, (b : G) = x → ψ b = b) ∧
          ∀ b : ↥Bs, (((ψ b)⁻¹ * φ b : ↥Bs) : G) ∈ Subgroup.zpowers x


theorem GGPseudoReflStabModInputOn.or {S T : ℕ → LargeEvenLabel → Prop}
    (hS : GGPseudoReflStabModInputOn S) (hT : GGPseudoReflStabModInputOn T) :
    GGPseudoReflStabModInputOn fun p lab => S p lab ∨ T p lab := by
  intro G _ _ p B Bs x L D J hH hL
  rcases hL.elim_or with h | h
  · exact hS G p B Bs x L D J hH h
  · exact hT G p B Bs x L D J hH h


end CFSG.StandardType

end
