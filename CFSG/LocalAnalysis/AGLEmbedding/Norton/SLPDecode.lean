module

public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.WordCheck
public import CFSG.LocalAnalysis.AGLEmbedding.Norton.MON5_7.GmatGen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.Norton

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Generated CFSG.YGroups CFSG.YGroups.Y443
  CFSG.YGroups.Y443Native CFSG.AGLEmbedding.Norton.MON5_7

@[expose] def tokNat (s : String) : ℕ := s.toNat?.getD 0

@[expose] def decodeLetters (perms : Array (Array ℕ)) : List String → List Native.Gen
  | "r" :: s :: a :: d :: rest =>
      .rho (tokNat s != 0, tokNat a, tokNat d) :: decodeLetters perms rest
  | "p" :: k :: rest => .perm perms[tokNat k]! :: decodeLetters perms rest
  | "x" :: rest => .xi :: decodeLetters perms rest
  | "t" :: rest => .tau :: decodeLetters perms rest
  | "g" :: a :: rest => .sign (tokNat a) :: decodeLetters perms rest
  | _ => []

@[expose] def tokens (line : String) : List String :=
  (line.splitOn " ").filter (· ≠ "")


@[expose] def agreeC (c : Native.Ctx) (va vb vw : Native.DVec) (w₁ w₂ : List Native.Gen) : Bool :=
  w₁.all (fun g => g.validB) && w₂.all (fun g => g.validB) &&
    (Native.evalWordC c w₁ va).eqv (Native.evalWordC c w₂ va) &&
    (Native.evalWordC c w₁ vb).eqv (Native.evalWordC c w₂ vb) &&
    (Native.evalWordC c w₁ vw).eqv (Native.evalWordC c w₂ vw)

theorem agreeC_eq (w₁ w₂ : List Native.Gen) :
    agreeC (Native.mkCtx ()) (aV ()) (bV ()) (wV ()) w₁ w₂ = agree w₁ w₂ := rfl


end CFSG.AGLEmbedding.Norton
