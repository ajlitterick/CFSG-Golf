module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporThMat
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Table2
public import CFSG.Monster.B.Fischer.ArrCert

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Monster.B.Fischer
  CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.Assembly (IsElemAbelian)
open CFSG.RankThree.PartTwo.Sec4.Item434SporLy (wordG wordG_mem)

@[expose] def encV (v : V4) : Array ℕ := #[v.w0.toNat, v.w1.toNat, v.w2.toNat, v.w3.toNat]

@[expose] def decV (a : Array ℕ) : V4 :=
  ⟨UInt64.ofNat a[0]!, UInt64.ofNat a[1]!, UInt64.ofNat a[2]!, UInt64.ofNat a[3]!⟩


theorem encV_get0 (v : V4) : (encV v)[0]! = v.w0.toNat := rfl

theorem encV_get1 (v : V4) : (encV v)[1]! = v.w1.toNat := rfl

theorem encV_get2 (v : V4) : (encV v)[2]! = v.w2.toNat := rfl

theorem encV_get3 (v : V4) : (encV v)[3]! = v.w3.toNat := rfl

theorem decV_encV (v : V4) : decV (encV v) = v := by
  obtain ⟨w0, w1, w2, w3⟩ := v
  simp only [decV, encV_get0, encV_get1, encV_get2, encV_get3, UInt64.ofNat_toNat]


end CFSG.RankThree.PartTwo.Sec4.Item434SporTh
