module

public import Certificates.Data.CFSGNative.MonsterAxis.Cover
public import Certificates.Data.CFSGNative.MonsterB.Short

public section

namespace CFSG.Monster.AxisCount.Native

open CFSG.Monster.AxisCount.Native.Cover

namespace Baby

@[expose] def lamBeta (_ : Unit := ()) : Nat := 12288


@[expose] def frameLev (_ : Unit := ()) : ByteArray := CFSG.Monster.VisCert.Native.frameTables.klev

@[expose] def shortLev (_ : Unit := ()) : ByteArray := CFSG.Monster.B.Short.Native.shortTables.klev

@[expose] def inDp (v : Nat) : Bool :=
  rd8 frameLev v != 0 && rd8 shortLev (v ^^^ lamBeta) != 0

@[inline, expose] def cvOKm (m : Nat) (T : CoverTables) (rows : Array (Array Nat))
    (seeds : Array Nat) (v : Nat) : Bool :=
  let o := rd8 T.lab v
  if o == 0 then true else
    let l := rd8 T.lev v
    o ≤ seeds.size &&
    (if l == 1 then v == seeds[o - 1]! else
      let p := rd32 T.par v
      let g := rd8 T.gen v
      l != 0 && p < 2 ^ 24 && g < m && rd8 T.lab p == o && rd8 T.lev p + 1 == l &&
        cvImg rows g p == v) &&
    allFrom (fun j => rd8 T.lab (cvImg rows j v) == o) 0 m


end Baby

end CFSG.Monster.AxisCount.Native
