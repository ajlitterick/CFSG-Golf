
module

public import CFSG.Sporadic.ThSchreier.UASpaceBase
public import CFSG.Sporadic.ThSchreier.TransporterBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def discOf (pl : ℕ) : ℕ := 2 * treePar pl + (treeLab pl - 1)


@[expose] def centFixedArr : Array ℕ := centFixedIdx.toArray

@[expose] def centImageArr : Array ℕ := centImageIdx.toArray

@[expose] def centImageKeys : Array Key :=
  Array.ofFn (n := 120) fun k =>
    ⟨v4OfNat (centImageRows.getD (2 * k.val) 0), v4OfNat (centImageRows.getD (2 * k.val + 1) 0)⟩


structure ScanFacts (st : BFSState) (fT uT : Array V4) (fl il : Array ℕ) (ip : Array Key)
    (sk : Key) (si : ℕ) : Prop where
  alphaSize : st.alpha.size = 4 * st.count
  mono : ∀ k, 1 ≤ k → k + 1 < st.count →
    discOf (readU32 st.par k) < discOf (readU32 st.par (k + 1))
  discA : ∀ k < st.count, readU32 st.alpha k < st.count →
    readU32 st.alpha k = 0 ∨ discOf (readU32 st.par (readU32 st.alpha k)) ≤ 2 * k
  discB : ∀ k < st.count, readU32 st.beta k < st.count →
    readU32 st.beta k = 0 ∨ discOf (readU32 st.par (readU32 st.beta k)) ≤ 2 * k + 1
  fixedCount : ((Finset.range st.count).filter fun i => readU32 st.alpha i = i).card = fl.size
  fixedMem : ∀ k < fl.size, fl[k]! < st.count ∧ readU32 st.alpha fl[k]! = fl[k]!
  fixedSorted : ∀ k, k + 1 < fl.size → fl[k]! < fl[k + 1]!
  fixedImage : ∀ k < fl.size,
    (inUAT uT (imageKey fT (readKey st.keys fl[k]!)).u &&
      inUAT uT (imageKey fT (readKey st.keys fl[k]!)).v) = il.contains fl[k]!
  imageMem : ∀ k < il.size, il[k]! < st.count ∧
    imageKey fT (readKey st.keys il[k]!) = ip[k]! ∧ inUAT uT ip[k]!.u = true ∧
    inUAT uT ip[k]!.v = true
  imageSorted : ∀ k, k + 1 < il.size → il[k]! < il[k + 1]!
  star : si < st.count ∧ imageKey fT (readKey st.keys si) = sk


abbrev ThScanFacts : Prop :=
  ScanFacts (thBFS ()) (frTable (transposeRows fcRows)) (frTable rowsUAQ) centFixedArr
    centImageArr centImageKeys starKey 120754

end CFSG.Sporadic.ThSchreier
