
module

public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.Background.A3Structure312Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Cases

variable {G : Type} [Group G]

@[expose] def C31Case1 (_H _R M L V K : Subgroup G) : Prop :=
  ∃ n : ℕ, IsRankTwoLie2Over n (↥K ⧸ Subgroup.center ↥K) ∧ IsMaxParabolic2 K (M ⊓ K) ∧
    conjClosure L M = perfectCore (M ⊓ K) ∧ IsPSL 2 2 n (ModO2 (conjClosure L M)) ∧
    ((∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsNaturalSection (conjClosure L M) V (V ⊓ centerOf K) (CFSG.pCore 2 ↥(conjClosure L M))
          (StatedSL 2 F)) ∨
      (IsPSp4 2 n ↥K ∧ ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
        IsNaturalSection (conjClosure L M) V (V ⊓ Subgroup.centralizer (conjClosure L M : Set G))
          (CFSG.pCore 2 ↥(conjClosure L M)) (StatedSL 2 F)))


@[expose] def C31Case2 (_H _R M L V K : Subgroup G) : Prop :=
  ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ IsPSL n 2 1 ↥K ∧ IsParabolic2 K (M ⊓ K) ∧
    conjClosure L M = perfectCore (M ⊓ K) ∧
    ((IsPSL (n - 1) 2 1 (ModO2 (conjClosure L M)) ∧ V = pCoreOf 2 (conjClosure L M) ∧
        IsNaturalSection (conjClosure L M) V ⊥ (CFSG.pCore 2 ↥(conjClosure L M))
          (StatedSL (n - 1) (ZMod 2))) ∨
      (n = 5 ∧ IsExt ↥(conjClosure L M) (fun N _ => IsE2 6 N) (fun Y _ => IsPSL 3 2 1 Y) ∧
        IsNaturalSection (conjClosure L M) V ⊥ (CFSG.pCore 2 ↥(conjClosure L M))
          (StatedSL 3 (ZMod 2))))

@[expose] def C31Case3 (_H _R M L _V K : Subgroup G) : Prop :=
  IsSporadic .M22 (↥K ⧸ Subgroup.center ↥K) ∧
    (IsExt ↥(imageModCenter K (conjClosure L M)) (fun N _ => IsE2 4 N) (fun Y _ => IsPSL 2 2 2 Y) ∨
      IsExt ↥(imageModCenter K (conjClosure L M)) (fun N _ => IsE2 4 N) (fun Y _ => IsAlt 6 Y) ∨
      IsExt ↥(imageModCenter K (conjClosure L M)) (fun N _ => IsE2 3 N) (fun Y _ => IsPSL 3 2 1 Y))

@[expose] def C31Case4 (_H _R M L _V K : Subgroup G) : Prop :=
  IsSporadic .M23 ↥K ∧
    (IsExt ↥(conjClosure L M) (fun N _ => IsE2 4 N) (fun Y _ => IsPSL 2 2 2 Y) ∨
      IsExt ↥(conjClosure L M) (fun N _ => IsE2 4 N) (fun Y _ => IsAlt 7 Y) ∨
      IsExt ↥(conjClosure L M) (fun N _ => IsE2 3 N) (fun Y _ => IsPSL 3 2 1 Y))

@[expose] def C31Case5 (_H _R M L _V K : Subgroup G) : Prop :=
  IsSporadic .M24 ↥K ∧
    (IsExt ↥(conjClosure L M) (fun N _ => IsE2 6 N)
        (fun Y _ => IsHat Y ↥(alternatingGroup (Fin 6))) ∨
      IsExt ↥(conjClosure L M) (fun N _ => IsE2 4 N) (fun Y _ => IsPSL 4 2 1 Y) ∨
      IsExt ↥(conjClosure L M) (fun N _ => IsE2 6 N) (fun Y _ => IsPSL 3 2 1 Y))

@[expose] def C31Case6M24 (M L : Subgroup G) : Prop :=
  IsExt ↥(conjClosure L M) (fun N _ => IsE2 11 N) (fun Y _ => IsSporadic .M24 Y)

@[expose] def C31Case6L3 (M L : Subgroup G) : Prop :=
  IsExt ↥(conjClosure L M) (fun N _ => IsSpecial2Group 3 12 N) (fun Y _ => IsPSL 3 2 1 Y)

@[expose] def C31Case6L5 (M L : Subgroup G) : Prop :=
  IsExt ↥(conjClosure L M) (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y)

@[expose] def C31Case6 (_H _R M L _V K : Subgroup G) : Prop :=
  IsSporadic .J4 ↥K ∧ (C31Case6M24 M L ∨ C31Case6L3 M L ∨ C31Case6L5 M L)

@[expose] def C31Case7 (_H _R M L _V K : Subgroup G) : Prop :=
  IsSporadic .HS (↥K ⧸ Subgroup.center ↥K) ∧
    (IsExt ↥(imageModCenter K (conjClosure L M)) (fun N _ => IsZ4Cubed N)
        (fun Y _ => IsPSL 3 2 1 Y) ∨
      IsExt ↥(imageModCenter K (conjClosure L M)) (fun N _ => IsE2 4 N) (fun Y _ => IsAlt 6 Y))

@[expose] def C31Case8 (_H _R M L _V K : Subgroup G) : Prop :=
  IsSporadic .He ↥K ∧
    IsExt ↥(conjClosure L M) (fun N _ => IsE2 6 N) (fun Y _ => IsHat Y ↥(alternatingGroup (Fin 6)))

@[expose] def C31Case9 (_H _R M L _V K : Subgroup G) : Prop :=
  IsSporadic .Ru (↥K ⧸ Subgroup.center ↥K) ∧
    (IsExt ↥(imageModCenter K (conjClosure L M)) (fun N _ => IsSpecial2Group 3 8 N)
        (fun Y _ => IsPSL 3 2 1 Y) ∨
      IsExt ↥(imageModCenter K (conjClosure L M)) (fun N _ => IsE2 6 N)
        (fun Y _ => IsPSU 3 3 1 Y))

@[expose] def C31Case10 (_H _R M L V K : Subgroup G) : Prop :=
  IsDoubleCover ↥K ↥(alternatingGroup (Fin 8)) ∧
    centerOf K = V ⊓ Subgroup.centralizer (conjClosure L M : Set G) ∧
    IsB48TwoModule (conjClosure L M) V

@[expose] def C31Conclusion (H R M L V K : Subgroup G) : Prop :=
  L = conjClosure L M ∧ ((conjClosure L M).subgroupOf M).Normal ∧ conjClosure L M ≤ K ∧
    M ≤ Subgroup.normalizer (K : Set G) ∧ IsPGroup 2 ↥(centerOf K) ∧
    (C31Case1 H R M L V K ∨ C31Case2 H R M L V K ∨ C31Case3 H R M L V K ∨
      C31Case4 H R M L V K ∨ C31Case5 H R M L V K ∨ C31Case6 H R M L V K ∨
      C31Case7 H R M L V K ∨ C31Case8 H R M L V K ∨ C31Case9 H R M L V K ∨
      C31Case10 H R M L V K)

end Cases

@[expose] def ASC31Statement (G : Type) [Group G] [Finite G] : Prop :=
  ∀ H R M L V K : Subgroup G, HypC28 H R M L V → CFSG.Open.IsComponentOf K H →
    C31Conclusion H R M L V K

end CFSG.Quasithin
