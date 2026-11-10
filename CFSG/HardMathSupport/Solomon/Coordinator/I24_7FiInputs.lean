module

public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexP
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSA
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSB
public import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSC
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexP
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSA
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSB
public meta import CFSG.HardMathSupport.Solomon.Coordinator.I24_7FiHexSC
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import CFSG.RankThree.PartOne.KS.PKit
public meta import CFSG.RankThree.Native.PermEnumeration
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import CFSG.RankThree.PartOne.KS.PKitLines
public import CFSG.RankThree.PartOne.KS.PKitLines
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Mathieu CFSG.Monster.B.Fischer

@[expose] def fi22CoverP0Gens : Array (Array ℕ) :=
  Array.ofFn (n := 9) fun j => hexTable3 3510 (3510 * j.val) fi22CoverHexP

@[expose] def fi22CoverHexS : String := fi22CoverHexSA ++ fi22CoverHexSB ++ fi22CoverHexSC

@[expose] def fi22CoverS : Array (Array ℕ) :=
  Array.ofFn (n := 20) fun j => hexTable3 3510 (3510 * j.val) fi22CoverHexS


@[expose] def fi22CoverEvalWord (w : List ℤ) : Array ℕ :=
  wordA 3510 fi22CoverP0Gens (rawInvs 3510 fi22CoverP0Gens) w

@[expose] def fi22CoverE5 : Array (Array ℕ) :=
  #[fi22CoverEvalWord [1], fi22CoverEvalWord [4], fi22CoverEvalWord [7],
    fi22CoverEvalWord [8, 6], fi22CoverEvalWord [6, 8]]

@[expose] def fi22CoverQ4 : Array (Array ℕ) :=
  #[fi22CoverEvalWord [1], fi22CoverEvalWord [2], fi22CoverEvalWord [4],
    fi22CoverEvalWord [7]]


end CFSG.HardMathSupport.Solomon.Coordinator
