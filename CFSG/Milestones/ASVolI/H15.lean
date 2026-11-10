module

public import CFSG.Quasithin.AppendixH.H15.Vocab
public import CFSG.Quasithin.Background.RonanH15O2
public import CFSG.Quasithin.Background.RonanH15Plumb
public import CFSG.Quasithin.Background.RonanH15Stab
public import CFSG.Quasithin.Background.RonanH15Stab3
public import CFSG.Quasithin.Background.H158UMain
public import CFSG.Quasithin.Background.H156Main
public import CFSG.Quasithin.Background.H153Main
public import CFSG.Quasithin.Background.RonanH155Main
import CFSG.Quasithin.AppendixH.H15.CocodeTwoMain
import CFSG.Quasithin.AppendixH.H15.H157Main

public section

open scoped Pointwise Matrix commutatorElement MatrixGroups

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH CFSG.Open CFSG.Monster.Code

@[expose] def H_15_1 : Prop :=
  AllMCtx false (fun d => d = 22 ∨ d = 23 ∨ d = 24) fun d a b _ _ _ _ _ Γ V _ ρ β =>
    ((∀ v : V, IsO2Vec d a b Γ β v → v ≠ 1) ∧
      (∃ v₀ : V, IsO2Vec d a b Γ β v₀ ∧ ∀ v : V, IsO2Vec d a b Γ β v → ∃ g : ↥Γ, ρ g v₀ = v) ∧
      (∀ v : V, IsO2Vec d a b Γ β v → ∀ g : ↥Γ, IsO2Vec d a b Γ β (ρ g v)) ∧
      (∀ v : V, IsO2Vec d a b Γ β v →
        (d = 24 → Nonempty (↥(cenM ρ (Subgroup.zpowers v)) ≃*
          MulAut ↥CFSG.Blueprint.NativeSporadic.M22)) ∧
        (d = 23 → Nonempty (↥(cenM ρ (Subgroup.zpowers v)) ≃* ↥CFSG.Blueprint.NativeSporadic.M22)) ∧
        (d = 22 →
          (∃ j : Fin 24, j ≠ a ∧ j ≠ b ∧
            IsVecOf (mathModel false d a b Γ) β (pairVec a j) v ∧
            ∀ g : ↥Γ, (g ∈ cenM ρ (Subgroup.zpowers v) ↔ (g : S24) j = j)) ∧
          ∃ (K : Type) (_ : Field K), Nat.card K = 4 ∧
            (Γ = M22g a b → Nonempty (↥(cenM ρ (Subgroup.zpowers v)) ≃* PSL(3, K))) ∧
            (Γ ≠ M22g a b → ∃ N : Subgroup ↥(cenM ρ (Subgroup.zpowers v)), N.index = 2 ∧
              Nonempty (↥N ≃* PSL(3, K)))))) ∧
    (∀ v : V, IsO2Vec d a b Γ β v → commOn ⊤ (ρ.range ⊓ centSub (Subgroup.zpowers v)) = ⊤)


section H151

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.RonanH15


end H151

@[expose] def H_15_2 : Prop :=
  AllMCtx false (fun d => d = 22 ∨ d = 23 ∨ d = 24) fun d a b O _ _ _ T₀ Γ V _ ρ β =>
    ((H.IsFOneOffender ρ.range (rImg ρ (KY Γ (Yd d a b O))) ∧
        ∀ A : Subgroup (MulAut V), A ≤ rImg ρ (T₀ ⊓ Γ) → H.IsFOneOffender ρ.range A →
          A = rImg ρ (KY Γ (Yd d a b O))) ∧
      (rk ↥(fixV (rImg ρ (KY Γ (Yd d a b O)))) = (if d = 22 then 5 else 6) ∧
        (∀ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) →
          ((∀ u ∈ fixV (rImg ρ (KY Γ (Yd d a b O))), ρ g u = u) ↔ (g : S24) ∈ KY Γ (Yd d a b O))) ∧
        (d = 24 →
          InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (KY Γ (Yd d a b O)))) ⊥
            (Multiplicative (Fin 6 → ZMod 2)) (omegaN 6 qPlus6)) ∧
        (d = 23 → ∃ Γ₇ : Subgroup (MulAut (Multiplicative (Fin 6 → ZMod 2))), Γ₇ ≤ omegaN 6 qPlus6 ∧
          Nonempty (↥Γ₇ ≃* ↥(alternatingGroup (Fin 7))) ∧
          InducesOn (rImg ρ (MY Γ (Yd d a b O))) (fixV (rImg ρ (KY Γ (Yd d a b O)))) ⊥
            (Multiplicative (Fin 6 → ZMod 2)) Γ₇) ∧
        (d = 22 → ∃ (w : Multiplicative (Fin 6 → ZMod 2)) (π : Multiplicative (Fin 6 → ZMod 2) →* V),
          qPlus6 (Multiplicative.toAdd w) = 1 ∧ π.range = fixV (rImg ρ (KY Γ (Yd d a b O))) ∧
          π.ker = Subgroup.zpowers w ∧
          (∀ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) →
            ∃ γ ∈ omegaN 6 qPlus6, γ w = w ∧ ∀ x, π (γ x) = ρ g (π x)) ∧
          (Γ ≠ M22g a b → ∀ γ ∈ omegaN 6 qPlus6, γ w = w →
            ∃ g : ↥Γ, (g : S24) ∈ MY Γ (Yd d a b O) ∧ ∀ x, π (γ x) = ρ g (π x))) ∧
        (d = 23 → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 7)), Function.Surjective π ∧
          π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
        (d = 24 → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 8)), Function.Surjective π ∧
          π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
        (d = 22 → (Γ = M22g a b → ∃ π : ↥(MY Γ (Yd d a b O)) →* ↥(alternatingGroup (Fin 6)),
            Function.Surjective π ∧ π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O))) ∧
          (Γ ≠ M22g a b → ∃ π : ↥(MY Γ (Yd d a b O)) →* Equiv.Perm (Fin 6),
            Function.Surjective π ∧ π.ker = (KY Γ (Yd d a b O)).subgroupOf (MY Γ (Yd d a b O)))))) ∧
    (∀ I : Subgroup V, I ≤ fixV (rImg ρ (KY Γ (Yd d a b O))) → (∀ x ∈ I, ¬ IsO2Vec d a b Γ β x) →
      rk ↥I ≤ (if d = 24 then 3 else 4)) ∧
    rkIdx (xiSub (rImg ρ (KY Γ (Yd d a b O)))) = 1 ∧
    ((∀ z ∈ Γ, orderOf z = 2 → IsTwoCentralElt Γ z →
        cenM ρ (fixV (rImg ρ (Subgroup.zpowers z))) = (Subgroup.zpowers z).subgroupOf Γ) ∧
      (∀ A : Subgroup S24, A ≤ KY Γ (Yd d a b O) → ¬ IsCyclic ↥A →
        fixV (rImg ρ A) = fixV (rImg ρ (KY Γ (Yd d a b O))))) ∧
    FullTranspAxis (rImg ρ (MY Γ (Yd d a b O))) (rImg ρ (KY Γ (Yd d a b O)))
      (fixV (rImg ρ (KY Γ (Yd d a b O)))) (xiSub (rImg ρ (KY Γ (Yd d a b O))))

section H15_2


end H15_2

@[expose] def H_15_3 : Prop :=
  AllMCtxAt false 24 fun a b _ _ S _ _ Γ V _ ρ β =>
    ∃ V₇ : Subgroup V,
      Chain153 a b β ρ S V₇ ∧
      FullTranspCenter (rImg ρ (MY Γ S)) (rImg ρ (KY Γ S)) V₇ (fixV (rImg ρ (KY Γ S))) ∧
      xiSub (rImg ρ (KY Γ S)) = ⊤ ∧
      (∀ x : V, x ∈ V₇ ↔ ∀ g ∈ rImg ρ (KY Γ S), g x * x⁻¹ ∈ fixV (rImg ρ (KY Γ S)))

section H15_3


end H15_3

@[expose] def H_15_4 : Prop :=
  AllMCtxAt false 22 fun a b _ _ S B _ Γ V _ ρ _ =>
    Γ = M2ab a b →
      (∃ V₆ : Subgroup V,
        (IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ (S.erase B)))) ⊥
            (fixV (rImg ρ (KY Γ (S.erase B)))) ∧
          rk ↥(fixV (rImg ρ (KY Γ (S.erase B)))) = 1 ∧
          IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ (S.erase B))))
            (fixV (rImg ρ (KY Γ (S.erase B)))) (fixV (rImg ρ (KY Γ (S.erase B) ⊓ M22g a b))) ∧
          rk ↥(fixV (rImg ρ (KY Γ (S.erase B) ⊓ M22g a b))) = 2 ∧
          IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ (S.erase B))))
            (fixV (rImg ρ (KY Γ (S.erase B) ⊓ M22g a b))) V₆ ∧
          IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ (S.erase B)))) V₆ ⊤ ∧ rk ↥V₆ = 6 ∧
          IsDualOfConj ρ (MY Γ (S.erase B)) V₆ (fixV (rImg ρ (KY Γ (S.erase B)))) (KY Γ (S.erase B)) ∧
          InducesOnSub (rImg ρ (MY Γ (S.erase B))) ⊤ V₆ (G6.PermMod 5) (G6.coreMod 5)
            (G6.permAct 5).range ∧
          (∀ g : ↥Γ, (g : S24) ∈ MY Γ (S.erase B) →
            ((∀ x : V, ρ g x * x⁻¹ ∈ V₆) ↔ (g : S24) ∈ KY Γ (S.erase B)))) ∧
        FullTranspCenter (rImg ρ (MY Γ (S.erase B))) (rImg ρ (KY Γ (S.erase B))) V₆
          (fixV (rImg ρ (KY Γ (S.erase B))))) ∧
      (∀ A : Subgroup S24, A ≤ KY Γ (S.erase B) → Nat.card A * 2 = Nat.card (KY Γ (S.erase B)) →
        xiSub (rImg ρ A) = ⊤ ∧ rk ↥(fixV (rImg ρ A)) = 2) ∧
      (⨆ (B' : Subgroup S24) (_ : B' ≤ KY Γ (S.erase B)) (_ : IsE2k 2 B'), fixV (rImg ρ B')) = ⊤

section H154

open CFSG.Quasithin.H.Mathieu


end H154

@[expose] def H_15_5 : Prop :=
  AllMCtxAt false 22 fun a b O _ S B T₀ Γ _ _ ρ _ =>
    Γ = M2ab a b → ∀ A : Subgroup S24, A ≤ T₀ ⊓ Γ → IsE2k 4 A →
      (A = KY Γ ((O.erase a).erase b) ∧ rk ↥(fixV (rImg ρ A)) = 5 ∧ rkIdx (xiSub (rImg ρ A)) = 1) ∨
      ((∃ g ∈ Γ, conjSubg g A ≤ KY Γ (S.erase B)) ∧ rk ↥(fixV (rImg ρ A)) = 2 ∧
        xiSub (rImg ρ A) = ⊤) ∨
      ((∃ i ∈ A, i ∉ M22g a b ∧
          (∃ O' : Finset (Fin 24), IsOctad O' ∧ ¬ (a ∈ O' ∧ b ∈ O') ∧ fixedSet i = O') ∧
          A = pCoreOf 2 (Γ ⊓ Subgroup.centralizer ({i} : Set S24)) ∧
          ∃ π : ↥(Γ ⊓ Subgroup.centralizer ({i} : Set S24)) →* GL (Fin 3) (ZMod 2),
            Function.Surjective π ∧ π.ker = A.subgroupOf (Γ ⊓ Subgroup.centralizer ({i} : Set S24))) ∧
        rk ↥(fixV (rImg ρ A)) = 3 ∧ xiSub (rImg ρ A) = ⊤) ∨
      (rk ↥(A ⊓ KY Γ ((O.erase a).erase b)) = 3 ∧ rk ↥(fixV (rImg ρ A)) = 3 ∧
        rkIdx (xiSub (rImg ρ A)) ≤ 1)

section H155

open CFSG.Quasithin.H.Mathieu


end H155

@[expose] def H_15_6 : Prop :=
  AllMCtxAt false 24 fun _ _ _ Tr _ _ _ _ V _ ρ _ =>
    ∃ V₉ : Subgroup V, Chain156 ρ Tr V₉ ∧ TensorFactors156 ρ Tr V₉

section H15_6


end H15_6

@[expose] def H_15_7 : Prop :=
  AllMCtxAt false 24 fun a b _ _ S _ _ Γ V _ ρ β =>
    ∀ Mx : Subgroup S24, (Mx = M24g ∨ Mx = M23g a) → ∀ y ∈ Mx, (orderOf y).Prime → Odd (orderOf y) →
      4 ≤ rk ↥(fixV (rImg ρ (Subgroup.zpowers y))) →
      (orderOf y = 3 ∧ rk ↥(fixV (rImg ρ (Subgroup.zpowers y))) = 5 ∧
        ∃ g ∈ M24g,
          (M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ⊓
              KY M24g S = ⊥ ∧
          (M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ⊔
              KY M24g S = MY M24g S ∧
          fixV (rImg ρ (KY M24g S)) =
            fixV (rImg ρ (M24g ⊓ Subgroup.normalizer
              ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24))) ∧
          ∃ π : ↥(M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24))
              →* Equiv.Perm (Fin 6), Function.Surjective π ∧
            π.ker = (conjSubg g (Subgroup.zpowers y)).subgroupOf
              (M24g ⊓ Subgroup.normalizer ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24)) ∧
            ∃ coordinates : Fin 6 ↪ Fin 24,
              (∀ point : Fin 24, (g * y * g⁻¹) point = point ↔
                ∃ index : Fin 6, coordinates index = point) ∧
              ∀ (acting : ↥(M24g ⊓ Subgroup.normalizer
                  ((conjSubg g (Subgroup.zpowers y) : Subgroup S24) : Set S24))) (index : Fin 6),
                (acting : S24) (coordinates index) = coordinates (π acting index)) ∧
      (∀ x : V, x ∈ fixV (rImg ρ (Subgroup.zpowers y)) ↔
        ∃ u : PM24, u ∈ G6.coreMod 24 ∧ (∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → y i = i) ∧
          IsVecOf (mathModel false 24 a b Γ) β u x) ∧
      (∀ u : PM24, u ≠ 1 → u ∈ G6.coreMod 24 → (∀ i : Fin 24, Multiplicative.toAdd u i ≠ 0 → y i = i) →
        u ∉ golayC) ∧
      (∀ I : Subgroup V, I ≤ fixV (rImg ρ (Subgroup.zpowers y)) →
        (Mx = M24g → (∀ x ∈ I, ¬ IsO2Vec 24 a b Γ β x) → rk ↥I ≤ 2) ∧
        (Mx = M23g a → (∀ x ∈ I, ¬ ∃ j : Fin 24, j ≠ a ∧
          IsVecOf (mathModel false 24 a b Γ) β (pairVec a j) x) → rk ↥I ≤ 4))

section H15_7


end H15_7

@[expose] def H_15_8 : Prop :=
  AllMCtxAt false 24 fun a b _ Tr S _ _ Γ V _ ρ β =>
    ∀ V₇ V₉ : Subgroup V, Chain153 a b β ρ S V₇ → Chain156 ρ Tr V₉ →
      V₇ ≤ V₉ ∧ ¬ V₇ ≤ fixV (rImg ρ (KY Γ Tr))

section H15_8


end H15_8

end CFSG.ASVolI
