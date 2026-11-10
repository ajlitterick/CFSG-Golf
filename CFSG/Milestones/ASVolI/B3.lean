module

public import CFSG.Milestones.ASVolI.B1
public import CFSG.Quasithin.Background.B3ThreeMain
public import CFSG.Quasithin.Background.B3Four

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.B3 CFSG.ASVolI.ChB
open scoped commutatorElement

@[expose] def B_3_1 : Prop :=
  ∀ n : ℕ, SQTKn n →
    (Nontrivial (Mod.V n Mod.ut0) ∧
      ∀ X : Subgroup (Mod.V n Mod.ut0),
        (∀ g ∈ alternatingGroup (Fin n), ∀ v ∈ X, Mod.act n Mod.ut0 g v ∈ X) → X = ⊥ ∨ X = ⊤) ∧
    (n % 2 = 1 →
      U0 n ⊓ Esub n = ⊥ ∧ U0 n ⊔ Esub n = ⊤ ∧ rk (Mod.V n Mod.ut0) = n - 1 ∧
        ∃ φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.u0, ∀ (g : Gp n) (v : Mod.V n Mod.ut0),
          φ (Mod.act n Mod.ut0 g v) = Mod.act n Mod.u0 g (φ v)) ∧
    (n % 2 = 0 →
      (Esub n < U0 n ∧ U0 n < ⊤) ∧
      (∀ (g : Gp n), ∀ x ∈ Esub n, permAct n g x ∈ Esub n) ∧
      (∀ (g : Gp n), ∀ x ∈ U0 n, permAct n g x ∈ U0 n) ∧
      (∀ X : Subgroup (U n), (∀ g ∈ alternatingGroup (Fin n), ∀ x ∈ X, permAct n g x ∈ X) →
        X = ⊥ ∨ X = Esub n ∨ X = U0 n ∨ X = ⊤) ∧
      rk (Mod.V n Mod.ut0) = n - 2)


@[expose] def B_3_2 : Prop :=
  ∀ n : ℕ, SQTKn n → ∀ k : Mod,
    (∀ m : ℕ, 1 ≤ m → m ≤ n / 2 →
      rk (Am n m) = m ∧
      (¬ (CaseB n k ∧ m = n / 2) → rkIdx (fixV ((Am n m).map (Mod.act n k))) = m) ∧
      (CaseB n k ∧ m = n / 2 → rkIdx (fixV ((Am n m).map (Mod.act n k))) = n / 2 - 1)) ∧
    (CaseB n k → rk (A0 n) = n / 2 ∧ rkIdx (fixV ((A0 n).map (Mod.act n k))) = n / 2) ∧
    (n = 8 → k = Mod.ut0 → ∀ A ∈ Rset n, rkIdx (fixV (A.map (Mod.act n k))) = 3) ∧
    (CaseA n k →
      (∀ A : Subgroup (Gp n), IsOffG n k A ↔
        ∃ m, 1 ≤ m ∧ m ≤ n / 2 ∧ A ∈ conjClass (Am n m)) ∧
      (∃ T : Sylow 2 (Gp n), (∀ m, m ≤ n / 2 → Am n m ≤ T) ∧ A0 n ≤ T ∧
        ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (Dsub n).map (Mod.act n k)) ∧
      qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((1 : ℚ) : WithTop ℚ)) ∧
    (CaseB n k → ¬ (n = 8 ∧ k = Mod.ut0) →
      (∀ A : Subgroup (Gp n), IsOffG n k A ↔
        A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
          (∃ m, 1 ≤ m ∧ m ≤ n / 2 ∧ A ∈ conjClass (Am n m)) ∨ A ∈ Hset n) ∧
      (∃ T : Sylow 2 (Gp n), (∀ m, m ≤ n / 2 → Am n m ≤ T) ∧ A0 n ≤ T ∧
        ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) =
          (Dsub n ⊔ Subgroup.closure
            {x : Gp n | x ∈ (T : Subgroup (Gp n)) ∧ IsConj (ti n 0 * ti n 1) x}).map
              (Mod.act n k)) ∧
      qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((((n : ℚ) - 2) / n : ℚ) : WithTop ℚ)) ∧
    (n = 8 → k = Mod.ut0 →
      (∀ A : Subgroup (Gp n), IsOffG n k A ↔
        A ∈ conjClass (Dsub n ⊓ alternatingGroup (Fin n)) ∨ A ∈ conjClass (A0 n) ∨
          (∃ m, 1 ≤ m ∧ m ≤ 4 ∧ A ∈ conjClass (Am n m)) ∨ A ∈ Hset n ∨ A ∈ Rset n) ∧
      (∃ T : Sylow 2 (Gp n), (∀ m, m ≤ 4 → Am n m ≤ T) ∧ A0 n ≤ T ∧
        ffJ ((T : Subgroup (Gp n)).map (Mod.act n k)) = (T : Subgroup (Gp n)).map (Mod.act n k) ∧
        ∀ A : Subgroup (Gp n), A ≤ T →
          (IsStrongFFStarOffender ((T : Subgroup (Gp n)).map (Mod.act n k)) (A.map (Mod.act n k)) ↔
            A = Dsub n)) ∧
      qOf ((⊤ : Subgroup (Gp n)).map (Mod.act n k)) = ((3 / 4 : ℚ) : WithTop ℚ))

section


end

@[expose] def B_3_3 : Prop :=
  ∀ n : ℕ, SQTKn n → ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    (∀ ρ : LG n →* MulAut V, HasOneChief n ρ → IsIndec ρ →
      (n % 2 = 1 →
        Nat.card (H1 (actL n Mod.ut0)) = 1 ∧
        (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ) ∧
        (∃ Φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.u0, IsModIso (actL n Mod.ut0) (actL n Mod.u0) Φ) ∧
        (∃ Φ : Mod.V n Mod.ut0 ≃* Mod.V n Mod.ut, IsModIso (actL n Mod.ut0) (actL n Mod.ut) Φ)) ∧
      (n % 2 = 0 → Nat.card (H1 (actL n Mod.ut0)) = 2)) ∧
    (n % 2 = 0 → ∀ ρ : LG n →* MulAut V, HasOneChief n ρ → IsIndec ρ →
      (∃ θ : (V ⧸ fixG ρ) ≃* WV n, ∀ x v,
        θ (QuotientGroup.mk (ρ x v)) = actL n Mod.ut0 x (θ (QuotientGroup.mk v))) →
      (∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ) ∨
      (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ)) ∧
    (n % 2 = 0 → ∀ ρG : Gp n →* MulAut V,
      HasOneChief n (ρG.comp (alternatingGroup (Fin n)).subtype) →
      IsIndec (ρG.comp (alternatingGroup (Fin n)).subtype) →
      (∃ θ : (V ⧸ fixG ρG) ≃* WV n, ∀ x v,
        θ (QuotientGroup.mk ((ρG.comp (alternatingGroup (Fin n)).subtype) x v)) =
          actL n Mod.ut0 x (θ (QuotientGroup.mk v))) →
      (∃ Φ : V ≃* Mod.V n Mod.u0,
        IsModIso (ρG.comp (alternatingGroup (Fin n)).subtype) (actL n Mod.u0) Φ) ∨
      (∃ Φ : V ≃* Mod.V n Mod.ut0,
        IsModIso (ρG.comp (alternatingGroup (Fin n)).subtype) (actL n Mod.ut0) Φ)) ∧
    (n % 2 = 0 → ∀ ρ : LG n →* MulAut V, HasOneChief n ρ → IsIndec ρ →
      ((∃ φ : ↥(commG ρ) ≃* WV n,
          IsModIso (resAct ρ (commG ρ) (isInv_commG ρ)) (actL n Mod.ut0) φ) →
        (∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ) ∨
        (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ)) ∧
      ((∃ Φ : V ≃* Mod.V n Mod.u, IsModIso ρ (actL n Mod.u) Φ) ∨
        (∃ Φ : V ≃* Mod.V n Mod.u0, IsModIso ρ (actL n Mod.u0) Φ) ∨
        (∃ Φ : V ≃* Mod.V n Mod.ut, IsModIso ρ (actL n Mod.ut) Φ) ∨
        (∃ Φ : V ≃* Mod.V n Mod.ut0, IsModIso ρ (actL n Mod.ut0) Φ)))


@[expose] def B_3_4 : Prop :=
  ∀ k : Mod, (k = Mod.u0 ∨ k = Mod.ut0) →
    (∀ P : Set (Subgroup (MulAut (Mod.V 6 k))),
      IsStableFF ((alternatingGroup (Fin 6)).map (Mod.act 6 k)) P →
      ∀ T : Subgroup (Gp 6), IsSylow2In (alternatingGroup (Fin 6)) T →
      ∀ W₁ W₂ : Subgroup (Mod.V 6 k),
        IsFlagSpace 6 k (alternatingGroup (Fin 6)) T 1 W₁ →
        IsFlagSpace 6 k (alternatingGroup (Fin 6)) T 2 W₂ →
      ∀ H₁ H₂ R₁ R₂ : Subgroup (Gp 6),
        H₁ = stabW (alternatingGroup (Fin 6)) W₁ → H₂ = stabW (alternatingGroup (Fin 6)) W₂ →
        R₁ = O2s H₁ → R₂ = O2s H₂ →
      ∀ J J₁ : Subgroup (MulAut (Mod.V 6 k)),
        J = ffJP P (T.map (Mod.act 6 k)) → J₁ = ffJP P (R₁.map (Mod.act 6 k)) →
          J = R₂.map (Mod.act 6 k) ∧ rk R₂ = 2 ∧
          (∀ A : Subgroup (MulAut (Mod.V 6 k)), A ≤ R₂.map (Mod.act 6 k) →
            ¬ IsStrongFFStarOffender ((alternatingGroup (Fin 6)).map (Mod.act 6 k)) A) ∧
          J₁ = ⊥) ∧
    (∀ P : Set (Subgroup (MulAut (Mod.V 6 k))),
      IsStableFF ((⊤ : Subgroup (Gp 6)).map (Mod.act 6 k)) P →
      ∀ T : Subgroup (Gp 6), IsSylow2In ⊤ T →
      ∀ W₁ W₂ : Subgroup (Mod.V 6 k), IsFlagSpace 6 k ⊤ T 1 W₁ → IsFlagSpace 6 k ⊤ T 2 W₂ →
      ∀ H₁ H₂ R₁ R₂ L₁ L₂ : Subgroup (Gp 6),
        H₁ = stabW ⊤ W₁ → H₂ = stabW ⊤ W₂ → R₁ = O2s H₁ → R₂ = O2s H₂ →
        L₁ = H₁ ⊓ alternatingGroup (Fin 6) → L₂ = H₂ ⊓ alternatingGroup (Fin 6) →
      ∀ J J₁ : Subgroup (MulAut (Mod.V 6 k)),
        J = ffJP P (T.map (Mod.act 6 k)) → J₁ = ffJP P (R₁.map (Mod.act 6 k)) →
          FourG k P T R₁ R₂ L₁ L₂ J J₁)

section


end

end CFSG.ASVolI
