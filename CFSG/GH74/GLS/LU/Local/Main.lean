module

public import CFSG.GH74.GLS.LU.Local.Conj
public import CFSG.GH74.GLS.LU.Main

public section

namespace CFSG.GH74.GLS.LU.Local

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS

structure LUEps (G : Type) [Group G] (q : ℕ) (ε : ℤ) (z : G) (K₁ : Subgroup G) (u : G) : Prop where
  eps : ε = 1 ∨ ε = -1
  mod8 : ¬ ((q : ℤ) ≡ ε [ZMOD 8])
  A0_cyc : IsCyclic ↥(A0 z)
  A0_dvd : ((Nat.card ↥(A0 z) : ℕ) : ℤ) ∣ (q : ℤ) - ε
  H_cyc : IsCyclic ↥(K₁ ⊓ centralizer ({u} : Set G))
  H_card : (Nat.card ↥(K₁ ⊓ centralizer ({u} : Set G)) : ℤ) = (q : ℤ) - ε

@[expose] def LUNbhdConcl (G : Type) [Group G] (Gs : Type) [Group Gs] (p f : ℕ) : Prop :=
  ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (z u : G) (Y : Fin 3 → Subgroup G),
        Nat.card K = p ^ f ∧ IsCentralInvolution z ∧ IsLinearA3Neighborhood K z u Y ∧
          Subgroup.centralizer ({z} : Set G) ≤
            Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G)) ∧
    ((p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f) →
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p) (F : Type) (_ : Field F)
        (_ : Finite F) (z u : G) (Y : Fin 3 → Subgroup G),
        Nat.card K = (p ^ f) ^ 2 ∧ Nat.card F = p ^ f ∧ IsCentralInvolution z ∧
          IsUnitaryA3Neighborhood (p ^ f) K F z u Y ∧
          Subgroup.centralizer ({z} : Set G) ≤
            Subgroup.normalizer ((⨆ i, Y i : Subgroup G) : Set G))

@[expose] def LUMax6AAt (G : Type) [Group G] (Gs : Type) [Group Gs] (p f : ℕ) : Prop :=
  ((p ^ f % 8 ≠ 1 ∧ LieModel Gs .PSL 4 p f) ∨ (p ^ f % 8 ≠ 7 ∧ LieModel Gs .PSU 4 p f)) →
    ∀ z : G, IsCentralInvolution z → MaxOverCentralizerPSp4 z p f


theorem LUSyl.isCentralInvolution {G : Type} [Group G] {z : G} {S : Sylow 2 G} {K₁ K₂ : Subgroup G}
    {t u : G} (h : LUSyl G z S K₁ K₂ t u) : IsCentralInvolution z :=
  ⟨h.z_inv, S, h.z_mem, fun _ hs => h.comm_z hs⟩


end CFSG.GH74.GLS.LU.Local
