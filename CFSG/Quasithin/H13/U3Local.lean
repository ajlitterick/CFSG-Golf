module

public import CFSG.Quasithin.H13.U3LocalSylow
public import CFSG.Quasithin.H13.AssemblyLocal
public import CFSG.Quasithin.H13.Statements
public import CFSG.Quasithin.SteinbergCBIrreducibleTI

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] def UniqueMaxTwoLocal (X M : Subgroup G) : Prop :=
  quasithinIsMaxTwoLocal M ∧ X ≤ M ∧ ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → X ≤ M' → M' = M

@[expose] def FiveQuotientExactOrders : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    (Nonempty (Q ≃* alternatingGroup (Fin 5)) → Nat.card Q = 60) ∧
    (LieModel Q .PSL 3 2 1 → Nat.card Q = 168) ∧
    (Nonempty (Q ≃* alternatingGroup (Fin 6)) → Nat.card Q = 360) ∧
    (Group.IsPerfect Q → Nat.card (center Q) = 3 →
      Nonempty (Q ⧸ center Q ≃* alternatingGroup (Fin 6)) → Nat.card Q = 1080) ∧
    (LieModel Q .PSU 3 3 1 → Nat.card Q = 6048) ∧
    (QT13Five Q → Nat.card Q ≤ 6048)


@[expose] def SylowNormalizedMaximalLocalUniqueNormalizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    quasithinIsMaximalLocal T L → T ≤ normalizer (L : Set G) → pCoreOf 2 L ≠ ⊥ →
    normalizer (L : Set G) = normalizer (pCoreOf 2 L : Set G) ∧
      UniqueMaxTwoLocal (L ⊔ T) (normalizer (L : Set G)) ∧
      ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q → Q ≤ L ⊔ T → L ⊔ T ≤ normalizer (Q : Set G) →
        normalizer (Q : Set G) ≤ normalizer (L : Set G) ∧
          UniqueMaxTwoLocal (normalizer (Q : Set G)) (normalizer (L : Set G))

theorem pCoreOf_ne_bot_of_isFaithfulLocal {T L : Subgroup G} (hL : quasithinIsFaithfulLocal T L) :
    pCoreOf 2 L ≠ ⊥ := by
  intro h
  apply hL.2.2.2
  rw [quasithinV2, h]
  have h1 : closure {z : G | z ∈ (⊥ : Subgroup G) ⊓ centralizer ((⊥ : Subgroup G) : Set G) ∧
      z ^ 2 = 1} = ⊥ := by
    rw [eq_bot_iff, closure_le]
    rintro z ⟨⟨hz, -⟩, -⟩
    exact hz
  rw [h1, commutator_bot_left]


end CFSG.Quasithin.H13.U3
