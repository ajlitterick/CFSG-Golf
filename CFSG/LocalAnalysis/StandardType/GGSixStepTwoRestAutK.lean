module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenTable

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Types

variable {G : Type} [Group G]

@[expose] def GGStepTwoExcThreeType (L₁ : Subgroup G) : Prop :=
  LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSU 4 2 1 ∨
    Nonempty ((↥L₁ ⧸ Subgroup.center ↥L₁) ≃* alternatingGroup (Fin 6)) ∨
    LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .POmegaPlus 4 2 1

@[expose] def GGStepTwoExcFiveType (L₁ : Subgroup G) : Prop :=
  Nonempty ((↥L₁ ⧸ Subgroup.center ↥L₁) ≃* alternatingGroup (Fin 5)) ∨
    LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .POmegaPlus 4 2 1

theorem ggFusionException_of_component {p : ℕ} {L₁ : Subgroup G} {W' : Type} [Group W']
    [Finite W'] {H E C : Subgroup W'} (hC : IsComponentOf C (H ⊓ CFSG.generalizedFitting W'))
    (he : Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃* ↥C ⧸ Subgroup.center ↥C))
    (hex : GGFusionException p H E) :
    (p = 3 ∧ GGStepTwoExcThreeType L₁ ∧
        IsPGroup p ↥(CFSG.generalizedFitting W' ⊓ Subgroup.centralizer (E : Set W'))) ∨
      (p = 5 ∧ GGStepTwoExcFiveType L₁) := by
  obtain ⟨e⟩ := he
  rcases hex with ⟨-, -, hnc⟩ | ⟨hp5, -, hall⟩ |
      ⟨hpg, ⟨hp3, -, hall⟩ | ⟨hp3, -, hall⟩ | ⟨hp3, -, hall⟩ | ⟨-, -, hnc⟩ | ⟨-, -, hnc⟩⟩ |
      ⟨hp5, -, hall⟩
  · exact absurd hC (hnc C)
  · obtain ⟨e5⟩ := hall C hC
    exact Or.inr ⟨hp5, Or.inl ⟨e.trans e5⟩⟩
  · exact Or.inl ⟨hp3, Or.inr (Or.inr (lieModel_of_mulEquiv' e.symm (hall C hC))), hpg⟩
  · exact Or.inl ⟨hp3, Or.inl (lieModel_of_mulEquiv' e.symm (hall C hC)), hpg⟩
  · obtain ⟨e6⟩ := hall C hC
    exact Or.inl ⟨hp3, Or.inr (Or.inl ⟨e.trans e6⟩), hpg⟩
  · exact absurd hC (hnc C)
  · exact absurd hC (hnc C)
  · exact Or.inr ⟨hp5, Or.inr (lieModel_of_mulEquiv' e.symm (hall C hC))⟩

end Types

section Choice

variable {G : Type} [Group G]

theorem ggAutK_not_isPGroup [Finite G] {E₀ K M C L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ C)
    (hL₁K : L₁ ≤ K) (hL₁M : L₁ ≤ M) (hH₀C : E₀ ⊔ (K ⊓ M) ≤ C)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K) (hEK : E₀ ≤ Subgroup.normalizer (K : Set G))
    {W' : Type} [Group W'] [Finite W'] (π : ↥(E₀ ⊔ K) →* W') (hπ : Function.Surjective π)
    (hker : π.ker ≤ ((E₀ ⊔ (K ⊓ M)) ⊓ Subgroup.centralizer (K : Set G)).subgroupOf (E₀ ⊔ K))
    {p : ℕ} {g : G} (hgL : g ∈ L₁) (hgZ : ∃ l ∈ L₁, g * l ≠ l * g)
    (hgE : g ∈ Subgroup.centralizer (E₀ : Set G)) (hgp : Nat.Coprime (orderOf g) p) :
    ¬ IsPGroup p ↥(CFSG.generalizedFitting W' ⊓
      Subgroup.centralizer (((E₀.subgroupOf (E₀ ⊔ K)).map π : Subgroup W') : Set W')) := by
  intro hpg
  obtain ⟨hC, -⟩ := ggAutK_image_component hL₁ hL₁K hL₁M hH₀C hKq hEK π hπ hker
  have hgW : g ∈ E₀ ⊔ K := le_sup_right (a := E₀) (hL₁K hgL)
  set w : ↥(E₀ ⊔ K) := ⟨g, hgW⟩
  have hwF : π w ∈ CFSG.generalizedFitting W' :=
    (hC.1.trans inf_le_right) ⟨w, Subgroup.mem_subgroupOf.mpr hgL, rfl⟩
  have hwC : π w ∈ Subgroup.centralizer
      (((E₀.subgroupOf (E₀ ⊔ K)).map π : Subgroup W') : Set W') := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hgE _ (Subgroup.mem_subgroupOf.mp hu)
  have hw1 : π w ≠ 1 := by
    intro h1
    have hwk : w ∈ π.ker := h1
    have hgK := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hwk))).2
    obtain ⟨l, hl, hgl⟩ := hgZ
    exact hgl (Subgroup.mem_centralizer_iff.mp hgK l (hL₁K hl)).symm
  obtain ⟨k, hk⟩ := hpg ⟨π w, hwF, hwC⟩
  have hk' : (π w) ^ p ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf (π w) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf (π w) ∣ orderOf g := by
    have h := orderOf_map_dvd π w
    rwa [← Subgroup.orderOf_coe w] at h
  have hcop : Nat.Coprime (orderOf g) (p ^ k) := Nat.Coprime.pow_right k hgp
  have h3 : orderOf (π w) ∣ 1 := by
    have := Nat.dvd_gcd h2 h1
    rwa [hcop] at this
  exact hw1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))

end Choice

section Inputs


theorem ggStepTwo_map_conj_one_le {G : Type} [Group G] {p : ℕ} {Bs D : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hDBs : D ≤ Bs) {b : G} (hb : b ∈ Bs) :
    D.map (MulAut.conj (1 : G)⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} := by
  have := hBs.1
  rintro _ ⟨d, hd, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [inv_one, map_one, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
  exact congrArg Subtype.val (mul_comm' (⟨d, hDBs hd⟩ : Bs) ⟨b, hb⟩)


@[expose] def GGStepTwoAutKFiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J → p = 5 → ¬ GGStepTwoExcFiveType L₁

@[expose] def GGStepTwoAutKThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J → p = 3 → GGStepTwoExcThreeType L₁ →
          ∃ m ∈ ggM p B x L D J,
            D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} ∧
            ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
              g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
              Nat.Coprime (orderOf g) p


end Inputs

end CFSG.StandardType
