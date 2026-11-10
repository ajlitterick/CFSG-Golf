module

public import CFSG.Milestones.ASVolI.B2
public import CFSG.Quasithin.Background.B610

public section

namespace CFSG.ASVolI.ChB

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique

@[expose] def B68ThreeStruct (X : Type) [Group X] (T M : Subgroup X) : Prop :=
  ∃ L : Subgroup (X ⧸ kerIn M ⊤), IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧
    L ≤ (twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)) ∧
    (twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)) =
      ⨆ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)), B6.conjSub t L ∧
    sSupIndep {S : Subgroup (X ⧸ kerIn M ⊤) |
      ∃ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)), S = B6.conjSub t L} ∧
    (∀ t ∈ T.map (QuotientGroup.mk' (kerIn M ⊤)),
      ((B6.conjSub t L).subgroupOf
        ((twoResidual (⊤ : Subgroup X)).map (QuotientGroup.mk' (kerIn M ⊤)))).Normal) ∧
    autOn ⊤ L ∈ uFamHat (autOn ⊤ L) (autOn (T.map (QuotientGroup.mk' (kerIn M ⊤))) L) ∧
    IsUniqueMaxOver (autOn ⊤ L) (autOn (T.map (QuotientGroup.mk' (kerIn M ⊤))) L)
      (autOn (M.map (QuotientGroup.mk' (kerIn M ⊤))) L)

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI.ChB

section DirectSumMod

variable {M : Type*} [Group M]

@[expose] def IsIntDirSumMod {ι : Type*} (X C : Subgroup M) (Us : ι → Subgroup M) : Prop :=
  C ⊔ (⨆ i, Us i) = C ⊔ X ∧
    ∀ i, (C ⊔ Us i) ⊓ (C ⊔ (⨆ (j : ι) (_ : j ≠ i), Us j)) = C

end DirectSumMod

end CFSG.ASVolI.ChB

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

@[expose] def B_6_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H X : Subgroup G), X < H → (⨆ U ∈ uFam H X, U) = H

section BurnsideB6a


end BurnsideB6a


@[expose] def B_6_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H X : Subgroup G), X ≤ H →
    (uHat H X ≤ H ∧ ((uHat H X).subgroupOf H).Normal ∧
      (uHat H X : Set G) * ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) = (H : Set G)) ∧
    (X < H → (⨆ h ∈ H, X.map (MulAut.conj h).toMonoidHom) = H → uHat H X = H)


@[expose] def B_6_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T : Subgroup G), IsSylowTwoOf T H →
    twoPrimeResidual H = H → T < H → uHat H T = H


@[expose] def B_6_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T : Subgroup G), IsSylowTwoOf T H →
    (H ⊓ Subgroup.normalizer (T : Set G)) ⊔ uHat H T = H


@[expose] def B_6_8 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T M : Subgroup X), MinParabolic (⊤ : Subgroup X) T M →
    (pCore 2 X = pCoreOf 2 (kerIn M ⊤) ∧ ¬ twoResidual (⊤ : Subgroup X) ≤ kerIn M ⊤) ∧
    (Group.IsSolvable X → ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ O2p2 X p = ⊤ ∧
      (kerIn M ⊤).map (QuotientGroup.mk' (pCore 2 X)) =
        (frattini (pCore p (X ⧸ pCore 2 X))).map (pCore p (X ⧸ pCore 2 X)).subtype ∧
      pCore p (X ⧸ kerIn M ⊤) ≠ ⊥ ∧
      ∀ S : Subgroup (X ⧸ kerIn M ⊤), S ≤ pCore p (X ⧸ kerIn M ⊤) →
        T.map (QuotientGroup.mk' (kerIn M ⊤)) ≤ Subgroup.normalizer (S : Set (X ⧸ kerIn M ⊤)) →
        S = ⊥ ∨ S = pCore p (X ⧸ kerIn M ⊤)) ∧
    (¬ Group.IsSolvable X →
      kerIn M ⊤ = O2F X ∧ twoResidual (⊤ : Subgroup X) ⊔ T = ⊤ ∧ B68ThreeStruct X T M ∧
      ((kerIn M ⊤ = O2F X ∧ O2F X = O2Fstar X) ∨
        (kerIn M ⊤ = solvableRadical X ∧ O2E2 X = ⊤))) ∧
    (∀ Y : Subgroup X, Y.Normal → Y ≤ kerIn M ⊤ ∨ twoResidual (⊤ : Subgroup X) ≤ Y) ∧
    IsSylowTwoOf (pCore 2 X) (kerIn M ⊤) ∧
    (∀ (W : Type) [CommGroup W], (∀ w : W, w ^ 2 = 1) → ∀ ρ : X →* MulAut W,
      (¬ twoResidual (⊤ : Subgroup X) ≤ ρ.ker → ρ.ker ≤ kerIn M ⊤) ∧
      (ρ.ker ≤ M → ρ.ker ≤ kerIn M ⊤ ∧ IsSylowTwoOf (pCore 2 X ⊓ ρ.ker) ρ.ker) ∧
      (pCore 2 X ≤ ρ.ker → ρ.ker ≤ M → pCore 2 (X ⧸ ρ.ker) = ⊥)) ∧
    (∀ V : Subgroup X, V ∈ primeReducedFamily X 2 → ⁅V, (⊤ : Subgroup X)⁆ ≠ ⊥ →
      ∀ N : Subgroup X, N ≤ T → (N.subgroupOf T).Normal →
        ((⁅twoResidual (⊤ : Subgroup X), N⁆ < twoResidual (⊤ : Subgroup X) ↔ N ≤ pCore 2 X) ∧
          (N ≤ pCore 2 X ↔ N ≤ T ⊓ Subgroup.centralizer (V : Set X))) ∧
        ((⁅V, Jj T 0⁆ = ⊥ ↔ Jj T 0 = Jj (pCore 2 X) 0) ∧
          (Jj T 0 = Jj (pCore 2 X) 0 ↔ baumOf T = baumOf (pCore 2 X))) ∧
        (⁅V, Jj T 0⁆ ≠ ⊥ → Jj ⊤ 0 = twoResidual (⊤ : Subgroup X) ⊔ Jj T 0 ∧
          ∃ hV : IsElemAbelian 2 V, IsFFModule (autI hV ⊤))) ∧
    (kerIn M ⊤).map (QuotientGroup.mk' (pCore 2 X)) = frattini (X ⧸ pCore 2 X)


@[expose] def B_6_9 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ H T M : Subgroup (MulAut V), MinParabolic H T M → CFSG.SectionRank.IsKGroupCat ↥H →
      pCoreOf 2 H = ⊥ → IsFFModule H →
        (qOf H = 1 ∧ ∀ A, ¬ IsStrongFFStarOffender H A) ∧
        ∃ (s : ℕ) (Hs : Fin s → Subgroup (MulAut V)),
          IsIntDirProd (ffJ H) Hs ∧
          IsIntDirSumMod (commV (ffJ H)) (fixV (ffJ H)) (fun i => commV (Hs i)) ∧
          (∀ i j, i ≠ j → commSub (commV (Hs i)) (Hs j) = ⊥) ∧
          ((∀ t ∈ T, ∀ i, ∃ j, (Hs i).map (MulAut.conj t).toMonoidHom = Hs j) ∧
            (∀ i j, ∃ t ∈ T, (Hs i).map (MulAut.conj t).toMonoidHom = Hs j)) ∧
          (((ffJ H : Subgroup (MulAut V)) : Set (MulAut V)) * (T : Set (MulAut V)) =
            (H : Set (MulAut V))) ∧
          ∀ i : Fin s,
            (∃ e : ℕ, 1 ≤ e ∧
              Nonempty (↥(Hs i) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)) ∧
              M ⊓ Hs i = Hs i ⊓ Subgroup.normalizer ((T ⊓ Hs i : Subgroup (MulAut V)) : Set (MulAut V)) ∧
              BinaryNaturalSL (Hs i) (fixV (ffJ H) ⊔ commV (Hs i)) (fixV (ffJ H)) 2 e) ∨
            (∃ k : ℕ, Nonempty (↥(Hs i) ≃* Equiv.Perm (Fin (2 ^ k + 1))) ∧
              Nonempty (↥(M ⊓ Hs i) ≃* Equiv.Perm (Fin (2 ^ k))) ∧
              G6.IsSymCore (Hs i) (commV (Hs i)) (2 ^ k + 1))


@[expose] def B_6_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V L : Subgroup G) (n : ℕ),
    MinParabolic H T M → quasithinGenFitting H = pCoreOf 2 H → IsTwoReducedIn H V →
    IsSubnormal L H → IsNaturalL2Prime n L V → ⁅V, Jj T 0⁆ ≠ ⊥ →
      (∀ s ∈ baumOf T, ∀ hs : s ∈ Subgroup.normalizer (V : Set G),
        conjAct V ⟨s, hs⟩ ∈ Subgroup.normalizer (autOn L V : Set (MulAut V))) ∧
      IsSylowTwoOf (baumOf T) (⨆ l ∈ L, (baumOf T).map (MulAut.conj l).toMonoidHom) ∧
      (twoResidual L = L →
        omegaOneCenterOf (Jj T 0) =
          (⁅V, L⁆ ⊓ Subgroup.centralizer (Jj T 0 : Set G)) ⊔
            (omegaOneCenterOf (Jj T 0) ⊓ Subgroup.centralizer (L : Set G)))

end CFSG.ASVolI
