module

public import CFSG.ClassicalInvolution.Q3.Q3TWWAutB
public import CFSG.ClassicalInvolution.Q3.Q3TWWEvalB
public import CFSG.ClassicalInvolution.Q3.Q3ZAdjChain

public section

namespace CFSG.ClassicalInvolution.Q3.Q3TW

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.Q3.Q3Z
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped MatrixGroups

section Adjust

variable {G : Type} [Group G]

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "sB" =>
  (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB2" => (longBlock (ZMod 3) 2 1 : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))


end Adjust

end CFSG.ClassicalInvolution.Q3.Q3TW
