module

public import Certificates.Data.CFSGNative.MonsterB.DyadicReduce
public import Certificates.Data.CFSGNative.MonsterB.BinarySha

public section

namespace CFSG.Monster.B.Binary.Native

open CFSG.Monster.B.Dyadic.Native


@[expose] def fixedVector (_ : Unit := ()) : Nat :=
  (((((((((((((((516283594158468584084124995243078636
    * 10 ^ 80 + 73671939191008431804525390494670400441721943376662223132062160267895571613672166)
    * 10 ^ 80 + 77130904768858544119611147118937953784986882056352705850375888901809511212954465)
    * 10 ^ 80 + 78220522729902683047800777726019802674921579760689221284823247732685252739052617)
    * 10 ^ 80 + 8982897259413764956902981398486002751801169301406865325073451174682562284673946)
    * 10 ^ 80 + 55692987405538782404356847811297922247282162810218952188117613382783837240443135)
    * 10 ^ 80 + 34623855831729815691797362584084256123542997553769609304870149572042210443253006)
    * 10 ^ 80 + 597537434018433300651299102984466147627391584311600637153870886214720017067077)
    * 10 ^ 80 + 63176510875291907107522592157116967783998033169727955151515914440874934031089926)
    * 10 ^ 80 + 40866917343849928127443713068578099530879958302559807653783462619168643354232258)
    * 10 ^ 80 + 40615554089301283503703474306125088109509810085154507219133601159619276304307588)
    * 10 ^ 80 + 7884797759964883640208793426233566133351848855882141247134703343385805021440095)
    * 10 ^ 80 + 84312339928997797840321309549234980557323699102130734394064243642755569594450613)
    * 10 ^ 80 + 63747750216804895748130563773558331271910996219284476440844365810367483943674208)
    * 10 ^ 80 + 2208836082638088679813848552157639996071899277225887930216392312712194531430442)
    * 10 ^ 80 + 13471176987536715115131553110040416859026484320739525792395602496151685247616345)
    * 10 ^ 80 + 50576687275055988713751067147926921887114476763607006320441685793835275524243456

@[expose] def removedCoord (_ : Unit := ()) : Nat := 1197


@[expose] def bytesOfNat (x : Nat) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := 552) fun b => UInt8.ofNat (x >>> (8 * b.val)))

@[expose] def rowBit (row : ByteArray) (j : Nat) : Bool :=
  ((row.get! (j / 8)).toNat >>> (j % 8)) % 2 == 1

@[expose] def srcIdx (j : Nat) : Nat := if j < removedCoord then j else j + 1

@[expose] def qRowBytes (fr y : ByteArray) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := 552) fun b => packByte fun u =>
    decide (8 * b.val + u < 4370) && (rowBit y (srcIdx (8 * b.val + u)) ^^
      (rowBit y removedCoord && rowBit fr (srcIdx (8 * b.val + u)))))

@[expose] def allCRows (chunks : Nat) : Array (Array ByteArray) :=
  Array.ofFn (n := 26) fun g => binRows g.val chunks

@[expose] def qPartsWith (fr : ByteArray) (C : Array (Array ByteArray)) :
    Array (Task (Array ByteArray)) :=
  Array.ofFn (n := 26) fun g => Task.spawn fun _ =>
    Array.ofFn (n := 4370) fun i => qRowBytes fr (C[g.val]![srcIdx i.val]!)

@[noinline, expose] def qParts (C : Array (Array ByteArray)) : Array (Task (Array ByteArray)) :=
  qPartsWith (bytesOfNat fixedVector) C

@[noinline, expose] def allQRows (parts : Array (Task (Array ByteArray))) :
    Array (Array ByteArray) :=
  Array.ofFn (n := 26) fun g => (parts[g.val]!).get

@[expose] def header (m : Nat) : ByteArray := u32le 1 ++ u32le m ++ u32le 26 ++ u32le 69

@[expose, irreducible] def payloadSize (m : Nat) : Nat := 16 + 26 * m * 552

@[expose] def payloadByte (m : Nat) (R : Array (Array ByteArray)) (pos : Nat) : UInt8 :=
  if pos < 16 then (header m).get! pos
  else ((R[(pos - 16) / 552 / m]!)[(pos - 16) / 552 % m]!).get! ((pos - 16) % 552)

@[expose] def payload (m : Nat) (R : Array (Array ByteArray)) : ByteArray :=
  ByteArray.mk (Array.ofFn (n := payloadSize m) fun pos => payloadByte m R pos.val)


end CFSG.Monster.B.Binary.Native
