module

public import CFSG.CGT.Stroth77.AmbientSplit
public import CFSG.CGT.Stroth77.WeakType
public import CFSG.GroupTheory.HuppertProduct.Mho

public section

namespace CFSG.CGT.Stroth77

variable {G : Type*} [Group G] [Finite G]

abbrev omegaIn (i : ℕ) (D : Subgroup G) : Subgroup G :=
  (CFSG.omega ↥D (p := 2) i).map D.subtype

theorem omegaIn_le (i : ℕ) (D : Subgroup G) : omegaIn i D ≤ D := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

abbrev mhoOne (D : Subgroup G) : Subgroup G :=
  CFSG.GroupTheory.HuppertProduct.mho D 2

structure StrothAmbient (G : Type*) [Group G] [Finite G] where
  S : Sylow 2 G
  A : Subgroup G
  hAS : A ≤ (S : Subgroup G)
  dataA : StrothWeakTypeData A (StrothTypeIndex.t100 1)
  hS_uv : dataA.uv ∈ (S : Subgroup G)
  hS_t : dataA.t ∈ (S : Subgroup G)
  hS_u : dataA.u ∈ (S : Subgroup G)
  hH : NoInvolutionsCentralizing (S : Subgroup G) A

namespace StrothAmbient

variable (X : StrothAmbient G)

@[expose] def L : Subgroup G := X.dataA.L


theorem card_A : Nat.card X.A = 32 := by
  have h := X.dataA.card
  rw [show (StrothTypeIndex.t100 1).k 0 = 1 from rfl,
    show (StrothTypeIndex.t100 1).k 1 = 2 from rfl,
    show (StrothTypeIndex.t100 1).k 2 = 2 from rfl] at h
  norm_num at h
  exact h

end StrothAmbient

structure StrothDatum (X : StrothAmbient G) where
  D : Subgroup G
  hAD : X.A ≤ D
  hDS : D ≤ (X.S : Subgroup G)
  τ : StrothTypeIndex
  dataD : StrothWeakTypeData D τ
  hL : dataD.L = X.L
  hcent : (X.S : Subgroup G) ⊓ Subgroup.centralizer (D : Set G) = D

namespace StrothDatum

variable {X : StrothAmbient G} (Z : StrothDatum X)

@[expose] def centralizerIn : Subgroup G :=
  (X.S : Subgroup G) ⊓ Subgroup.centralizer (Z.D : Set G)

@[expose] def normalizerIn : Subgroup G :=
  (X.S : Subgroup G) ⊓ Subgroup.normalizer (Z.D : Set G)

@[expose] def centralizerInMho : Subgroup G :=
  Z.normalizerIn ⊓ Subgroup.centralizer ((mhoOne Z.D : Subgroup G) : Set G)


theorem centralizerIn_eq : Z.centralizerIn = Z.D := Z.hcent

theorem D_le_normalizerIn : Z.D ≤ Z.normalizerIn := by
  intro x hx
  rw [normalizerIn]
  exact ⟨Z.hDS hx, Subgroup.le_normalizer hx⟩


theorem mem_of_mem_centralizer {x : G} (hxS : x ∈ (X.S : Subgroup G))
    (hx : x ∈ Subgroup.centralizer (Z.D : Set G)) : x ∈ Z.D := by
  have hx' : x ∈ Z.centralizerIn := by
    rw [centralizerIn]
    exact ⟨hxS, hx⟩
  rwa [Z.centralizerIn_eq] at hx'

theorem D_le_centralizerInMho : Z.D ≤ Z.centralizerInMho := by
  haveI : IsMulCommutative Z.D := Z.dataD.isMulCommutative
  intro x hx
  rw [centralizerInMho]
  exact ⟨Z.D_le_normalizerIn hx,
    Subgroup.centralizer_le (show ((mhoOne Z.D : Subgroup G) : Set G) ⊆ (Z.D : Set G) from
      CFSG.GroupTheory.HuppertProduct.mho_le Z.D 2) (Subgroup.le_centralizer Z.D hx)⟩

end StrothDatum


end CFSG.CGT.Stroth77
