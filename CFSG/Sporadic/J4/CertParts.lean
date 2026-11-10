module

import Mathlib.Tactic.IrreducibleDef
public import CFSG.Sporadic.J4.FaithSpec
import Certificates.Data.CFSGNative.J4.Cert

public section

namespace CFSG.Sporadic.J4

open Native CFSG.Sporadic.Th CFSG.Perm.Native

noncomputable abbrev tbi0 : ByteArray := invTab nPts bs0.beta 3

noncomputable abbrev tx0 : Array (Array V2) := (locMats ()).map frTable

noncomputable abbrev txi0 : Array (Array V2) := (locInvs ()).map frTable

noncomputable abbrev zT (k : ℕ) : ByteArray := matTab bs0.keys bs0.slots nPts txi0[k]! 3

noncomputable abbrev O0 : VOrb := vorbit tx0 (rdV2 bs0.keys 24) 15180 15

noncomputable abbrev qIdx0 : Array ℕ :=
  (O0.pts.extract 0 qLen).map fun p => findIdx bs0.keys bs0.slots p - 1

noncomputable abbrev q00 : Array ℕ := qIdx0.push stripBase

noncomputable abbrev tS0 : Array V2 := frTable (sigRows (fsOf qIdx0))

noncomputable abbrev d0 : ByteArray := sigTable bs0.keys tS0 basisIdx 26

noncomputable abbrev letters0 : Array Th.Native.Table :=
  chainLetters 15180 (strongTables 15180 (tx0.map (posTable O0)) chainWords)

noncomputable irreducible_def trees0 : Array Tree := chainTrees 15180 letters0 chainBase

noncomputable abbrev O5 : VOrb := vorbit tx0 (rdV2 bs0.keys stripBase) stripOrbit 23

noncomputable abbrev o5idx : Array ℕ := O5.pts.map fun p => findIdx bs0.keys bs0.slots p - 1

noncomputable abbrev lev0 : Level := ⟨NatMap.ofKeys o5idx 23, O5.par, O5.lab, #[zT 0, zT 1, zT 2]⟩

noncomputable abbrev ts50 : Array (Array V2) := (stabMats ()).map frTable

noncomputable irreducible_def tg0 : Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (Array ℕ) ℕ :=
  tupleGroup bs0.keys bs0.slots ts50 q00 stabOrder

noncomputable irreducible_def t20 : ByteArray × ByteArray := tree2 nPts bs0.alpha bs0.beta tbi0

noncomputable abbrev cpts0 : Array ℕ := pointsOfDepth nPts t20.2 cacheDepth

noncomputable abbrev pairs0 : Array ByteArray := mkPairs nPts bs0.alpha bs0.beta tbi0 3

noncomputable irreducible_def GD0 : GData :=
  ⟨nPts, bs0.alpha, bs0.beta, tbi0, t20.1, t20.2, q00, lev0, qLen, tg0.1, tg0.2.2.2, cacheDepth,
    NatMap.ofKeys cpts0 21, mkCache t20.1 bs0.alpha bs0.beta tbi0 q00 cpts0, pairs0⟩

noncomputable abbrev L0 : Labels :=
  labelPar nPts (zT 0) (zT 1) (zT 2) subReps subSizes.toArray labelGroups

structure J4NativeFacts : Prop where
  mat : MatFacts
  count : bs0.count = nPts
  orbit : orbitOK (frTable rowsA) (frTable rowsB) rootV bs0 nPts 3 = true
  inv : invOK32 nPts bs0.beta tbi0 3 = true
  z0 : matTabOK bs0.keys nPts txi0[0]! (zT 0) 3 = true
  z1 : matTabOK bs0.keys nPts txi0[1]! (zT 1) 3 = true
  z2 : matTabOK bs0.keys nPts txi0[2]! (zT 2) 3 = true
  o0 : vorbOK tx0 (rdV2 bs0.keys 24) O0 15180 = true
  qsize : qIdx0.size = qLen
  q : (List.range qLen).all (fun t => decide (qIdx0[t]! < nPts) &&
    (rdV2 bs0.keys qIdx0[t]!).beq O0.pts[t]!) = true
  sig : uniqueSigOK bs0.keys nPts tS0 basisIdx 26 d0 3 = true
  bsize : basisIdx.size = 112
  blt : basisIdx.all (· < nPts) = true
  basis : eqRows (mulRows basisRows (invRows basisRows)) idRows = true
  chain : chainOK 15180 letters0 chainBase (Array.range qLen) chainBase trees0 3 = true
  sizes : orbitSizes trees0 = chainSizes
  tg : tupleGroupOK bs0.keys nPts ts50 q00 tg0.1 tg0.2.1 tg0.2.2.1 = true
  tgsize : tg0.1.size = stabOrder
  tree : treeOK nPts bs0.alpha bs0.beta tbi0 t20.1 t20.2 3 = true
  pairs : pairsOK nPts bs0.alpha bs0.beta tbi0 pairs0 3 = true
  global : globalOK GD0 3 = true
  label : labelOK nPts (zT 0) (zT 1) (zT 2) L0 3 = true
  reps : (L0.reps == subReps) = true
  counts : ((countLab nPts 7 L0).toList == subSizes) = true


end CFSG.Sporadic.J4
