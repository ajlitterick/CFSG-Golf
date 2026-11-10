module

public import CFSG.Quasithin.AppendixH.H16.Vocab
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.HF166B
public import CFSG.Quasithin.Background.HF1607M22B
public import CFSG.Quasithin.Background.HMathieuCode23
public import CFSG.Quasithin.Background.RonanH164Main
import CFSG.Quasithin.AppendixH.H16.Concl161
import CFSG.Quasithin.AppendixH.H16.H162Final
import CFSG.Quasithin.AppendixH.H16.H165FourGlue
import CFSG.Quasithin.AppendixH.H16.H165Glue
import CFSG.Quasithin.AppendixH.H16.H165One
import CFSG.Quasithin.AppendixH.H16.H165Three
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.H14

public section

open scoped Pointwise Matrix commutatorElement

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code

open CFSG.Quasithin.H.Mathieu


@[expose] def H_16_1 : Prop :=
  AllMCtxAt true 24 fun _ _ _ _ S _ _ Γ V _ ρ _ =>
    ∃ V₁₀ : Subgroup V,
      (IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) ⊥ (fixV (rImg ρ (KY Γ S))) ∧
        rk ↥(fixV (rImg ρ (KY Γ S))) = 4 ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) (fixV (rImg ρ (KY Γ S))) V₁₀ ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ S))) V₁₀ ⊤ ∧
        V₁₀ = commV (rImg ρ (perfectCore (MY Γ S))) ∧ rkIdx V₁₀ = 1) ∧
      (∃ N : Subgroup S24, IsO23 (MY Γ S) N ∧
        (∃ π : ↥(MY Γ S) →* ↥(CFSG.Open.StatedSp 2 (ZMod 2)), Function.Surjective π ∧
          π.ker = N.subgroupOf (MY Γ S)) ∧
        (∀ g : ↥Γ, (g : S24) ∈ MY Γ S →
          ((∀ x ∈ fixV (rImg ρ (KY Γ S)), ρ g x = x) ↔ (g : S24) ∈ N)) ∧
        InducesOn (rImg ρ (MY Γ S)) (fixV (rImg ρ (KY Γ S))) ⊥
          (Multiplicative (Fin 2 ⊕ Fin 2 → ZMod 2))
          (natSubI (Fin 2 ⊕ Fin 2) (ZMod 2) (CFSG.Open.StatedSp 2 (ZMod 2)))) ∧
      FullTranspAxis (rImg ρ (MY Γ S)) (rImg ρ (KY Γ S)) (fixV (rImg ρ (KY Γ S))) V₁₀

section H16_1


end H16_1

@[expose] def H_16_2 : Prop :=
  AllMCtxAt true 24 fun _ _ O _ S _ T₀ Γ V _ ρ _ =>
    ∃ V₅ : Subgroup V,
      (IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ O))) ⊥ (fixV (rImg ρ (KY Γ O))) ∧
        rk ↥(fixV (rImg ρ (KY Γ O))) = 1 ∧
        IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ O))) (fixV (rImg ρ (KY Γ O))) V₅ ∧
        rk ↥V₅ = 5 ∧ IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ O))) V₅ ⊤) ∧
      (FullTranspCenter (rImg ρ (MY Γ O)) (rImg ρ (KY Γ O)) V₅ (fixV (rImg ρ (KY Γ O))) ∧
        IsDualOfConj ρ (MY Γ O) V₅ (fixV (rImg ρ (KY Γ O))) (KY Γ O)) ∧
      (∃ β' : V →* Multiplicative (Fin 6 → ZMod 2),
        InducesOnVia (rImg ρ (MY Γ O)) ⊤ V₅ (Multiplicative (Fin 6 → ZMod 2)) (omegaN 6 qPlus6)
          (β'.comp (⊤ : Subgroup V).subtype) ∧
        (∀ g : ↥Γ, (g : S24) ∈ MY Γ O → ((∀ x : V, ρ g x * x⁻¹ ∈ V₅) ↔ (g : S24) ∈ KY Γ O)) ∧
        rk ↥(fixV (rImg ρ (KY Γ S)) ⊔ V₅) = 6 ∧
        (∀ x ∈ fixV (rImg ρ (KY Γ S)) ⊔ V₅, qPlus6 (Multiplicative.toAdd (β' x)) = 0) ∧
        (fixV (rImg ρ (KY Γ S)) = fixV (rImg ρ (KY Γ O ⊓ KY Γ S))) ∧
        ∀ z : S24, IsCenterGen T₀ z →
          (rk ↥(fixV (rImg ρ (Subgroup.zpowers z)) ⊔ V₅) = 8 ∧
            ∀ x ∈ fixV (rImg ρ (Subgroup.zpowers z)) ⊔ V₅, qPlus6 (Multiplicative.toAdd (β' x)) = 0) ∧
          cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) = (Subgroup.zpowers z).subgroupOf Γ ∧
          (rk ↥(V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))) = 4 ∧
            IsE2k 4 (cenMS ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z)))) ∧
            pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({z} : Set S24)) =
              KY Γ O ⊔ cenMS ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))) ∧
            ∀ element ∈ pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({z} : Set S24)),
              ∃ kernelElement ∈ KY Γ O,
                ∃ centralizerElement ∈ cenMS ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))),
                  element = kernelElement * centralizerElement) ∧
          (∀ B : Subgroup S24, z ∈ B → B ≤ cenMS ρ (V₅ ⊓ fixV (rImg ρ (Subgroup.zpowers z))) →
            rk ↥(fixV (rImg ρ B)) = 8 - rk ↥B) ∧
          (∀ g ∈ Γ ⊓ Subgroup.centralizer ({z} : Set S24),
            rk ↥(commOn (fixV (rImg ρ (Subgroup.zpowers z))) (rImg ρ (Subgroup.zpowers g))) = 1 →
              g ∈ pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({z} : Set S24))))

section H16_2


end H16_2

@[expose] def H_16_3 : Prop :=
  AllMCtxAt true 22 fun a b _ _ S B _ Γ V _ ρ _ =>
    Γ = M2ab a b →
      (∃ V₈ V₉ : Subgroup V,
        Chain163 ρ (S.erase B) V₈ V₉ ∧
        FullTranspAxis (rImg ρ (MY Γ (S.erase B))) (rImg ρ (KY Γ (S.erase B)))
          (fixV (rImg ρ (KY Γ (S.erase B)))) V₉) ∧
      InducesOnSub (rImg ρ (MY Γ (S.erase B))) (fixV (rImg ρ (KY Γ (S.erase B)))) ⊥ (G6.PermMod 5)
        (G6.coreMod 5) (G6.permAct 5).range ∧
      (cenM ρ (fixV (rImg ρ (KY Γ (S.erase B)))) = (KY Γ (S.erase B)).subgroupOf Γ ∧
        IsPGroup 2 ↥(KY Γ (S.erase B)))

section H16_3


end H16_3

@[expose] def H_16_4 : Prop :=
  AllMCtxAt true 22 fun a b O _ S B _ Γ V _ ρ _ =>
    Γ = M2ab a b →
      ∃ V₅ V₆ : Subgroup V,
        Chain164 ρ ((O.erase a).erase b) V₅ V₆ ∧
        (FullTranspCenter (rImg ρ (MY Γ ((O.erase a).erase b))) (rImg ρ (KY Γ ((O.erase a).erase b))) V₅
            (fixV (rImg ρ (KY Γ ((O.erase a).erase b)))) ∧
          IsDualOfConj ρ (MY Γ ((O.erase a).erase b)) V₅ (fixV (rImg ρ (KY Γ ((O.erase a).erase b))))
            (KY Γ ((O.erase a).erase b))) ∧
        ((∃ π : ↥(MY Γ ((O.erase a).erase b)) →* Equiv.Perm (Fin 6), Function.Surjective π ∧
            π.ker = (KY Γ ((O.erase a).erase b)).subgroupOf (MY Γ ((O.erase a).erase b))) ∧
          InducesOnSub (rImg ρ (MY Γ ((O.erase a).erase b))) ⊤ V₅ (G6.PermMod 6) (G6.coreMod 6)
            (G6.permAct 6).range) ∧
        ((∃ V₈ V₉ : Subgroup V, Chain163 ρ (S.erase B) V₈ V₉ ∧
            V₅ ≤ V₉ ∧ ¬ V₅ ≤ fixV (rImg ρ (KY Γ (S.erase B)))) ∧
          (∀ V₈ V₉ : Subgroup V, Chain163 ρ (S.erase B) V₈ V₉ →
            V₅ ≤ V₉ ∧ ¬ V₅ ≤ fixV (rImg ρ (KY Γ (S.erase B))))) ∧
        (∀ x : V, x ∈ V₅ ↔ ∀ g ∈ rImg ρ (KY Γ ((O.erase a).erase b)),
          g x * x⁻¹ ∈ fixV (rImg ρ (KY Γ ((O.erase a).erase b))))

section H16_4


end H16_4

@[expose] def H_16_5 : Prop :=
  (AllMCtxAt true 24 fun _ _ _ _ S _ _ Γ _ _ ρ _ =>
    H.IsFOneOffender ρ.range (rImg ρ (KY Γ S)) ∧
    ∀ A : Subgroup S24, A ≤ Γ → H.IsFOneOffender ρ.range (rImg ρ A) →
      ∃ g ∈ Γ, conjSubg g A = KY Γ S) ∧
  (AllMCtxAt true 23 fun _ _ _ _ _ _ _ Γ _ _ ρ _ =>
    ∀ A : Subgroup S24, A ≤ Γ → ¬ H.IsFOneOffender ρ.range (rImg ρ A)) ∧
  (AllMCtxAt true 22 fun a b _ _ S B _ Γ _ _ ρ _ =>
    Γ = M2ab a b →
      H.IsFOneOffender ρ.range (rImg ρ (KY Γ (S.erase B))) ∧
      ∀ A : Subgroup S24, A ≤ Γ → H.IsFOneOffender ρ.range (rImg ρ A) →
        ∃ g ∈ Γ, conjSubg g A = KY Γ (S.erase B)) ∧
  (AllMCtxAt true 22 fun a b _ _ _ _ _ Γ _ _ ρ _ =>
    Γ = M2ab a b → ∀ z ∈ Γ, orderOf z = 2 → IsTwoCentralElt Γ z →
      cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z))) =
          Γ ⊓ Subgroup.centralizer ((twoResidual (Γ ⊓ Subgroup.centralizer ({z} : Set S24)) :
            Subgroup S24) : Set S24) ∧
      IsE2k 2 (cenMS ρ (fixV (rImg ρ (Subgroup.zpowers z)))))

section H165One

open CFSG.ASVolI.H16


end H165One

section H165Two


end H165Two

section H165Three

open CFSG.ASVolI.H16


end H165Three

section H165Four

open CFSG.ASVolI.H16


end H165Four

section H165


end H165

@[expose] def H_16_6 : Prop :=
  AllMCtxAt true 24 fun _ _ _ _ _ _ _ Γ _ _ ρ _ =>
    ∀ Y : Subgroup S24, Y ≤ Γ → Nat.card ↥Y = 3 → rkIdx (fixV (rImg ρ Y)) = 6 →
      cenMS ρ (fixV (rImg ρ Y)) = Y

section H16_6


end H16_6

@[expose] def H_16_7 : Prop :=
  AllMCtx true (fun d => d = 22 ∨ d = 24) fun _ _ _ _ _ _ _ _ Γ _ _ ρ _ =>
    ∀ s : ℕ, (s = 2 ∨ s = 3) → ∀ A Y : Subgroup S24, A ≤ Γ → Y ≤ Γ → IsE2k (2 * s) A →
      Nat.card ↥Y = 3 → Y ≤ Subgroup.normalizer (A : Set S24) → ⁅A, Y⁆ = A →
        rkIdx (fixV (rImg ρ (A ⊔ Y))) ≠ 2 * (s + 1)

section H16_7


end H16_7

@[expose] def H_16_8 : Prop :=
  AllMCtxAt true 23 fun _ _ _ _ _ _ T₀ Γ _ _ ρ _ =>
    ∀ A : Subgroup S24, A ≤ T₀ ⊓ Γ → IsE2k 4 A → rkIdx (xiSub (rImg ρ A)) ≤ 1

section H16_8


end H16_8

end CFSG.ASVolI
