module

public import CFSG.GH74.Uniqueness.SU.SU4Defs
public import CFSG.GH74.GLS.Basic
public import CFSG.GH74.Uniqueness.SU.SU5Models

public section

namespace CFSG.GH74.Uniqueness.SU.SU4

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]


section Finite

variable [Finite G]

@[expose] def Lemma183Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U : Subgroup G), Setup18 S U →
    (∀ g ∈ gammaElem (S : Subgroup G), PermutesComp U g) ∧
    (∀ V : Subgroup G, ¬ IsIsolatedVertex ⊤ V) ∧
    (∀ A B : Subgroup G, IsFour ⊤ A → IsFour ⊤ B → ∃ g : G, conjSub g A ∈ compSet ⊤ B) ∧
    ((∃ E : Subgroup G, IsFour ⊤ E ∧ E ∉ compSet ⊤ U) → ∃ g : G, ¬ PermutesComp U g)

@[expose] def Lemma183CoreStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U : Subgroup G), Setup18Core S U →
    (∀ g ∈ gammaElem (S : Subgroup G), PermutesComp U g) ∧
    (∀ V : Subgroup G, ¬ IsIsolatedVertex ⊤ V) ∧
    (∀ A B : Subgroup G, IsFour ⊤ A → IsFour ⊤ B → ∃ g : G, conjSub g A ∈ compSet ⊤ B) ∧
    ((∃ E : Subgroup G, IsFour ⊤ E ∧ E ∉ compSet ⊤ U) → ∃ g : G, ¬ PermutesComp U g)


@[expose] def Lemma186Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M : Subgroup G), Hyp184 S U M →
    Concl184b M → Concl184a S M

structure Conf18H (S : Sylow 2 G) (M V : Subgroup G) (x z : G) : Prop where
  S_le : (S : Subgroup G) ≤ M
  iso : IsIsolatedVertex M V
  gen : V = Subgroup.closure ({x, z} : Set G)
  hx : orderOf x = 2
  hz : orderOf z = 2
  K_ex : ∃ K : Subgroup G, K ≤ centralizer ({x} : Set G) ⊓ (S : Subgroup G) ∧
    zpowers x ⊓ K = ⊥ ∧ zpowers x ⊔ K = centralizer ({x} : Set G) ⊓ (S : Subgroup G) ∧
    z ∈ K ∧ ∀ k ∈ K, k * k = 1 → k = 1 ∨ k = z
  syl_c : IsSylowIn (centralizer ({x} : Set G) ⊓ M) (centralizer ({x} : Set G) ⊓ (S : Subgroup G))
  z_center : ∀ s ∈ (S : Subgroup G), s * z = z * s
  z_unique : ∀ c ∈ (S : Subgroup G), (∀ s ∈ (S : Subgroup G), s * c = c * s) → c * c = 1 →
    c = 1 ∨ c = z
  x_mem : x ∈ M
  x_not : (⟨x, x_mem⟩ : ↥M) ∉ GLS.oResidual 2 ↥M

@[expose] def Lemma18HStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M : Subgroup G), Hyp184 S U M →
    (∃ V : Subgroup G, IsIsolatedVertex M V) → ∃ (V : Subgroup G) (x z : G), Conf18H S M V x z


@[expose] def Lemma188Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G),
    Hyp184 S U M → Conf18H S M V x z → ¬ IsFusionIsolated M (S : Subgroup G) z

@[expose] def Tsub (S : Sylow 2 G) (U : Subgroup G) : Subgroup G :=
  centralizer (U : Set G) ⊓ (S : Subgroup G)

abbrev Mbar (M : Subgroup G) : Type _ := ↥M ⧸ pPrimeCore 2 ↥M

@[expose] def barImage (M X : Subgroup G) : Subgroup (Mbar M) :=
  (X.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M))

@[expose] def xbar (M : Subgroup G) (x : G) (hx : x ∈ M) : Mbar M :=
  QuotientGroup.mk' (pPrimeCore 2 ↥M) ⟨x, hx⟩

structure Concl189 (S : Sylow 2 G) (U M : Subgroup G) (x : G) (hx : x ∈ M) : Prop where
  case : (LieModel ↥(generalizedFitting (Mbar M)) .PSL 3 2 2 ∧
        GLS.oPrimeResidual 2 (Mbar M) = generalizedFitting (Mbar M) ⊔ zpowers (xbar M x hx) ∧
        9 ∣ Nat.card ↥(centralizer ({xbar M x hx} : Set (Mbar M)) ⊓ generalizedFitting (Mbar M))) ∨
      barImage M (Tsub S U) = generalizedFitting (Mbar M)
  T_le : barImage M (Tsub S U) ≤ generalizedFitting (Mbar M)
  typeT : SU5.IsL34Type ↥(Tsub S U)
  typeS : SU5.IsJ2Type ↥(S : Subgroup G)
  normalizerT : ∃ Hh H₀ : Subgroup (Mbar M),
    normalizer ((barImage M (Tsub S U) : Subgroup (Mbar M)) : Set (Mbar M)) =
        barImage M (Tsub S U) ⊔ Hh ∧
      barImage M (Tsub S U) ⊓ Hh = ⊥ ∧ H₀ ≤ Hh ∧ Nonempty (↥H₀ ≃* Equiv.Perm (Fin 3)) ∧
      Hh = H₀ ⊔ (centralizer ((barImage M U : Subgroup (Mbar M)) : Set (Mbar M)) ⊓ Hh) ∧
      H₀ ⊓ (centralizer ((barImage M U : Subgroup (Mbar M)) : Set (Mbar M)) ⊓ Hh) = ⊥ ∧
      (∀ a ∈ H₀, ∀ c ∈ centralizer ((barImage M U : Subgroup (Mbar M)) : Set (Mbar M)) ⊓ Hh,
        a * c = c * a) ∧
      (∀ a ∈ H₀, orderOf a = 3 → ∀ t ∈ barImage M (Tsub S U), a * t * a⁻¹ = t → t = 1) ∧
      (Nat.card ↥(centralizer ((barImage M U : Subgroup (Mbar M)) : Set (Mbar M)) ⊓ Hh) = 1 ∨
        Nat.card ↥(centralizer ((barImage M U : Subgroup (Mbar M)) : Set (Mbar M)) ⊓ Hh) = 3)

@[expose] def Prop189Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Sylow 2 G) (U M V : Subgroup G) (x z : G)
    (h : Conf18H S M V x z), Hyp184 S U M → Concl189 S U M x h.x_mem

end Finite

end CFSG.GH74.Uniqueness.SU.SU4
