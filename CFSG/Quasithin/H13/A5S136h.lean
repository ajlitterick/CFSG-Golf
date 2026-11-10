module

public import CFSG.Quasithin.H13.A5S136f
public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)

structure Hyp1367 : Prop where
  hab : IsElemAbelian 2 (conjClosure V S.G1)
  hF : CharTwo (Subgroup.centralizer ({S.v12} : Set G))
  hVv : ¬ Subgroup.centralizer ({S.v12} : Set G) ≤ Subgroup.normalizer (S.Vv : Set G)
  hJ : ¬ thompsonJ (T ⊓ Subgroup.centralizer ({S.v12} : Set G)) ≤
    Subgroup.centralizer (S.Uv : Set G)

@[expose] noncomputable def Tv : Subgroup G := T ⊓ Subgroup.centralizer ({S.v12} : Set G)

theorem z_mem_Uv : S.z ∈ S.Uv := le_conjClosure _ _ (Subgroup.mem_zpowers _)

@[expose] noncomputable def zU : ↥S.Uv := ⟨S.z, S.z_mem_Uv⟩

@[expose] def InX0 (X : Subgroup (MulAut ↥S.Uv)) : Prop :=
  X ≤ autOn (Subgroup.centralizer ({S.v12} : Set G)) S.Uv ∧
    autOn (S.Lv ⊔ S.Tv) S.Uv ≤ Subgroup.normalizer (X : Set (MulAut ↥S.Uv)) ∧
    oTwoRes X = X ∧ X ≠ ⊥ ∧ ⁅X, autOn (thompsonJ S.Tv) S.Uv⁆ = X

@[expose] def InXz (X : Subgroup (MulAut ↥S.Uv)) : Prop :=
  S.InX0 X ∧ ∃ x ∈ X, x S.zU ≠ S.zU

@[expose] def InYz (K : Subgroup G) : Prop :=
  K ≤ Subgroup.centralizer ({S.v12} : Set G) ∧ K ∈ lFamily S.Tv ∧
    CFSG.IsQuasisimple (↥(autOn K S.Uv) ⧸ CFSG.pCore 2 ↥(autOn K S.Uv)) ∧
    S.InXz (conjClosure (autOn K S.Uv) (autOn S.Tv S.Uv))

@[expose] noncomputable def WK (K : Subgroup G) : Subgroup G :=
  conjClosure S.V1 (conjClosure K S.Tv ⊔ S.Lv)

@[expose] noncomputable def plus (K : Subgroup G) : Subgroup (MulAut ↥(S.WK K)) :=
  autOn K (S.WK K)

end Setting


@[expose] def List1367 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
      CFSG.IsQuasisimple ↥(S.plus K) ∧ B56QuasisimpleList ↥(S.plus K)

@[expose] def Lemma13618 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))

@[expose] def Lemma13618Four : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (F : Type) [Field F] [Finite F], Nat.card F = 4 →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 2 F))

@[expose] def Lemma13619 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting G T L V), S.Hyp1367 →
    ∀ K : Subgroup G, S.InYz K → S.Tv ≤ Subgroup.normalizer (K : Set G) →
    ∀ (n : ℕ) (F : Type) [Field F] [Finite F], 2 ≤ n → Nat.card F = 2 ^ n →
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) ∧
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∧
      ¬ Nonempty (↥(S.plus K) ≃* ↥(CFSG.Open.quasithinG2 F))


@[expose] def NotQS1367 : Prop :=
  ∀ (X : Type) [Group X], CFSG.IsQuasisimple X → ∀ (F : Type) [Field F] [Finite F],
    Nat.card F = 2 →
      ¬ Nonempty (X ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 F)) ∧
      ¬ Nonempty (X ≃* ↥(CFSG.Open.quasithinG2 F))

theorem two_le_of_field {F : Type} [Field F] [Finite F] {n : ℕ} (h : Nat.card F = 2 ^ n) :
    1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [h, pow_zero] at h1
    omega
  · exact hn


end CFSG.Quasithin.H13.A5
