module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Pointwise

namespace A315

@[expose] def InvertedIn {G : Type*} [Group G] (X Y : Subgroup G) : Prop :=
  ∃ t ∈ Y, ∀ x ∈ X, t * x * t⁻¹ = x⁻¹

@[expose] def ActsIrreducibly {G : Type*} [Group G] (T B : Subgroup G) : Prop :=
  T ≤ Subgroup.normalizer (B : Set G) ∧ B ≠ ⊥ ∧
    ∀ C : Subgroup G, C ≤ B → T ≤ Subgroup.normalizer (C : Set G) → C = ⊥ ∨ C = B

@[expose] def IsSylowOf (p : ℕ) {G : Type*} [Group G] (U L : Subgroup G) : Prop :=
  U ≤ L ∧ IsPGroup p ↥U ∧ ¬ p ∣ U.relIndex L

@[expose] def IsCartan (p : ℕ) {X : Type*} [Group X] (U I H : Subgroup X) : Prop :=
  H ≤ I ⊓ Subgroup.normalizer (U : Set X) ∧ ¬ p ∣ Nat.card ↥H ∧
    ∃ k : ℕ, H.relIndex (I ⊓ Subgroup.normalizer (U : Set X)) = p ^ k

@[expose] def IsLieChar2 (n : ℕ) (X : Type) [Group X] : Prop :=
  IsPSL 2 2 n X ∨ IsPSL 3 2 n X ∨ IsPSU 3 2 n X ∨ IsPSp4 2 n X ∨ IsG2 2 n X ∨ Is3D4 2 n X ∨
    IsSz n X ∨ Is2F4 n X

@[expose] def autImage {G : Type} [Group G] (L : Subgroup G) [L.Normal] (X : Subgroup G) :
    Subgroup (MulAut ↥L) :=
  X.map (MulAut.conjNormal : G →* MulAut ↥L)

end A315


structure A315Hyp {G : Type} [Group G] (L T B : Subgroup G) : Prop where
  sqtk : SQTKHyp G
  fitting : CFSG.generalizedFitting G = L
  simple : IsSimpleGroup ↥L
  nonabelian : ∃ a b : ↥L, a * b ≠ b * a
  sylow : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤
  odd : Odd (Nat.card ↥B)
  perm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)
  residual : pResidualOf 3 B ≠ ⊥
  cases : IsMulCommutative ↥B ∨ ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥B ∧ B ≤ L

@[expose] def A315Case1 {G : Type} [Group G] (L T B : Subgroup G) : Prop :=
  ∃ p e : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ e ∧ e ≤ 2 ∧ IsPSL 2 p e ↥L ∧ B ≤ L ∧ IsCyclic ↥B ∧
    (∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε ((p ^ e : ℕ) : ℤ) ∧
      ((Nat.card ↥B : ℕ) : ℤ) ∣ ((p ^ e : ℕ) : ℤ) - ε) ∧
    A315.InvertedIn B (T ⊓ L)

@[expose] def A315Case2 {G : Type} [Group G] (L T B : Subgroup G) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsPSL 3 p 1 ↥L ∧ B ≤ L ∧ IsElemAbelianOfRank p 2 ↥B ∧
    A315.ActsIrreducibly T B

@[expose] def A315Case3 {G : Type} [Group G] (L T B : Subgroup G) : Prop :=
  ∃ (δ : Bool) (p : ℕ), p.Prime ∧ p ≠ 2 ∧ IsPSLEps3 δ p 1 ↥L ∧
    ∃ K : Subgroup G, K ≤ L ∧ IsSL2 p ↥K ∧
      B = (B ⊓ K) ⊔ (B ⊓ Subgroup.centralizer (K : Set G)) ∧
      IsCyclic ↥(B ⊓ K) ∧ IsCyclic ↥(B ⊓ Subgroup.centralizer (K : Set G)) ∧
      (∃ H U : Subgroup G, A315.IsSylowOf p U L ∧ A315.IsCartan p U (L ⊔ B) H ∧
        B ⊓ Subgroup.centralizer (K : Set G) ≤ H) ∧
      Nat.card ↥(B ⊓ Subgroup.centralizer (K : Set G)) ∣ (if δ then p - 1 else p + 1) ∧
      (((∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ Int.ModEq 4 ε (p : ℤ) ∧
          ((Nat.card ↥(B ⊓ K) : ℕ) : ℤ) ∣ (p : ℤ) - ε) ∧
        A315.InvertedIn (B ⊓ K) (T ⊓ K)) ∨
       ((p % 8 = 3 ∨ p % 8 = 5) ∧ Nat.card ↥(B ⊓ K) = 3 ∧
        A315.InvertedIn (B ⊓ K) (T ⊓ L ⊓ Subgroup.normalizer (B : Set G) ⊓
          Subgroup.centralizer ((B ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G))))

@[expose] def A315Case4 {G : Type} [Group G] (L T B : Subgroup G) : Prop :=
  IsSporadic .J1 ↥L ∧ B ≤ L ⊓ Subgroup.normalizer (T : Set G) ∧ Nat.card ↥B = 7


@[expose] def A315Case6 {G : Type} [Group G] (L T B : Subgroup G) : Prop :=
  Is3D4 2 1 ↥L ∧ ∃ D : Subgroup G, A315.IsCartan 2 (T ⊓ L) L D ∧ Nat.card ↥D = 7 ∧
    (B = D ∨ ∃ A : Subgroup G, Nat.card ↥A = 3 ∧ D ⊓ A = ⊥ ∧
      (∀ d ∈ D, ∀ a ∈ A, d * a = a * d) ∧ B = D ⊔ A)

@[expose] def A315Case7 {G : Type} [Group G] (L _T B : Subgroup G) : Prop :=
  IsTits ↥L ∧ Nat.card ↥B = 5


end CFSG.Quasithin
