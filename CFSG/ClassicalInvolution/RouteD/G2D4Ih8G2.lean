module

public import CFSG.ClassicalInvolution.RouteD.G2D4E189Rest
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Edge
public import CFSG.ClassicalInvolution.ModelFacts.G2D4ThreeD4
public import CFSG.ClassicalInvolution.Asc77.AscIH8Thm678

public section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance.Q27

section Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem isMaxPGroup_of_card_eq {J J' R : Subgroup G} (hcard : Nat.card J = Nat.card J')
    (hRJ' : R ≤ J') (hR : IsPGroup p R)
    (hmax : ∀ T : Subgroup G, T ≤ J' → IsPGroup p T → R ≤ T → T = R) :
    ∀ T : Subgroup G, T ≤ J → IsPGroup p T → R ≤ T → T = R := by
  intro T hTJ hT hRT
  let P' : Sylow p J' :=
    ⟨R.subgroupOf J', hR.comap_subtype, fun {Q} hQ hle => by
      have h1 : R ≤ Q.map J'.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hRJ']
        exact Subgroup.map_mono hle
      have h2 := hmax (Q.map J'.subtype) (Subgroup.map_subtype_le _) (hQ.map _) h1
      rw [← Subgroup.comap_map_eq_self_of_injective J'.subtype_injective Q, h2]
      rfl⟩
  have hP' : Nat.card (R.subgroupOf J') = p ^ (Nat.card J').factorization p :=
    Sylow.card_eq_multiplicity P'
  have hT' : IsPGroup p ↥(T.subgroupOf J) := hT.comap_subtype
  obtain ⟨P, hTP⟩ := hT'.exists_le_sylow
  have hP : Nat.card P = p ^ (Nat.card J).factorization p := Sylow.card_eq_multiplicity P
  have h1 : Nat.card T = Nat.card (T.subgroupOf J) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTJ).toEquiv.symm
  have h2 : Nat.card R = Nat.card (R.subgroupOf J') :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRJ').toEquiv.symm
  have h3 : Nat.card (T.subgroupOf J) ≤ Nat.card P := Subgroup.card_le_of_le hTP
  have h4 : Nat.card T ≤ Nat.card R := by
    rw [h1, h2, hP', ← hcard]
    exact hP ▸ h3
  exact (Subgroup.eq_of_le_of_card_ge hRT h4).symm

end Sylow

section Transport

variable {Kmod G : Type} [Group Kmod] [Group G] [Finite G]

theorem dEdgeless_of_model (ψ : Kmod →* G) (hinj : Function.Injective ψ)
    (hsurj : Function.Surjective ψ) {cls : Set (Subgroup Kmod)} {Ω : Set (Subgroup G)}
    (hΩ : ∀ L, L ∈ Ω ↔ ∃ R ∈ cls, L = R.map ψ)
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (core : ∀ Q ∈ cls, ∀ g : Kmod, ∀ R : Subgroup Kmod, R ≤ conjSub g Q → IsPGroup 2 R →
      (∀ T : Subgroup Kmod, T ≤ conjSub g Q → IsPGroup 2 T → R ≤ T → T = R) →
      R ≤ Subgroup.normalizer (Q : Set Kmod) → conjSub g Q = Q) :
    Disconnected.DEdgeless Ω := by
  have key : ∀ K ∈ Ω, ∀ J ∈ Ω, J ∉ omegaNbr Ω K := by
    intro K hK J hJ hnbr
    obtain ⟨-, hne, R, hR, hRJ, hRN⟩ := hnbr
    obtain ⟨J', hJ', hRJ', hR2, hRmax⟩ := mem_RSet_iff.mp hR
    obtain ⟨g', hg'⟩ := htrans J' hJ' J hJ
    have hcard : Nat.card J = Nat.card J' := by
      rw [← hg']
      exact Subgroup.card_map_of_injective (MulAut.conj g').injective
    have hmaxJ := isMaxPGroup_of_card_eq hcard hRJ' hR2 hRmax
    obtain ⟨K₀, hK₀, rfl⟩ := (hΩ K).mp hK
    obtain ⟨J₀, hJ₀, rfl⟩ := (hΩ J).mp hJ
    obtain ⟨g₁, hg₁⟩ := htrans _ hK _ hJ
    obtain ⟨g, rfl⟩ := hsurj g₁
    have hJ₀eq : conjSub g K₀ = J₀ := by
      refine Subgroup.map_injective hinj ?_
      rw [← conjSub_map ψ g K₀]
      exact hg₁
    have hR₀J₀ : R.comap ψ ≤ J₀ := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hRJ (hx : ψ x ∈ R)
      have : y = x := hinj hyx
      rwa [this] at hy
    have hR₀max : ∀ T : Subgroup Kmod, T ≤ conjSub g K₀ → IsPGroup 2 T → R.comap ψ ≤ T →
        T = R.comap ψ := by
      intro T hT hT2 hle
      have h1 : T.map ψ ≤ J₀.map ψ := by
        rw [← hJ₀eq]
        exact Subgroup.map_mono hT
      have h2 : R ≤ T.map ψ := by
        rw [← Subgroup.map_comap_eq_self_of_surjective hsurj R]
        exact Subgroup.map_mono hle
      have h3 := hmaxJ (T.map ψ) h1 (hT2.map ψ) h2
      rw [← Subgroup.comap_map_eq_self_of_injective hinj T, h3]
    have hR₀N : R.comap ψ ≤ Subgroup.normalizer (K₀ : Set Kmod) := by
      intro x hx
      have h1 := hRN (hx : ψ x ∈ R)
      rw [normalizer_map_of_bijective ψ hinj hsurj K₀] at h1
      obtain ⟨n, hn, hnx⟩ := h1
      have : n = x := hinj hnx
      rwa [this] at hn
    have h := core K₀ hK₀ g (R.comap ψ) (hJ₀eq ▸ hR₀J₀) (hR2.comap_of_injective ψ hinj)
      (hJ₀eq ▸ hR₀max) hR₀N
    exact hne (by rw [← hJ₀eq, h])
  intro K hK J hJ hadj
  rcases hadj with h | h
  · exact key K hK J hJ h
  · exact key J hJ K hK h

end Transport

section Twins

variable {Kmod G : Type} [Group Kmod] [Group G]

theorem noTwins_of_model (ψ : Kmod →* G) (hinj : Function.Injective ψ)
    (hsurj : Function.Surjective ψ) {cls : Set (Subgroup Kmod)} {Ω : Set (Subgroup G)}
    (hΩ : ∀ L, L ∈ Ω ↔ ∃ R ∈ cls, L = R.map ψ)
    (htrans : ∀ K ∈ Ω, ∀ J ∈ Ω, ∃ g : G, conjSub g K = J)
    (hnt : ∀ R ∈ cls, ∀ c : Kmod, IsUniqueInvolution R c → ∀ g : Kmod,
      IsUniqueInvolution (conjSub g R) c → conjSub g R = R) :
    ∀ K ∈ Ω, ∀ K' ∈ twinSet Ω K, K' = K := by
  intro K hK K' hK'
  obtain ⟨R, hR, rfl⟩ := (hΩ K).mp hK
  obtain ⟨hK'Ω, z, hz, hz'⟩ := hK'
  obtain ⟨g, hg⟩ := htrans _ hK _ hK'Ω
  obtain ⟨g', rfl⟩ := hsurj g
  have h1 : (conjSub g' R).map ψ = K' := by
    rw [← conjSub_map ψ g' R]
    exact hg
  subst h1
  obtain ⟨c, hcz, hc⟩ := isUniqueInvolution_comap hinj hz
  obtain ⟨c', hc'z, hc'⟩ := isUniqueInvolution_comap hinj hz'
  have hcc : c' = c := hinj (hc'z.trans hcz.symm)
  rw [hcc] at hc'
  rw [hnt R hR c hc g' hc']


end Twins

section Ih8


end Ih8

section D4Three


end D4Three

end CFSG.ClassicalInvolution.G2D4Models
