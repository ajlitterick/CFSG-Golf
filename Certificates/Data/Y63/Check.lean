module

public import Certificates.Data.Y63.Tab
public import Certificates.Data.Y63.Model
public import Certificates.Data.Y63.Spec

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk

@[expose] def bfsWords (tab : Array (Array ℕ)) (_ : Unit := ()) : Array (List ℕ) := Id.run do
  let mut words : Array (List ℕ) := Array.replicate 512 []
  let mut seen : Array Bool := (Array.replicate 512 false).set! 0 true
  let mut queue : Array ℕ := #[0]
  for i in [0:512] do
    if i < queue.size then
      let x := queue[i]!
      for c in [0:10] do
        let y := (tab.getD x #[]).getD c 0
        if !(seen.getD y true) then
          seen := seen.set! y true
          words := words.set! y (words.getD x [] ++ [c])
          queue := queue.push y
  return words

@[expose] def mulTable (tab : Array (Array ℕ)) (W : Array (List ℕ)) (_ : Unit := ()) :
    Array (Array ℕ) :=
  (Array.range 512).map fun x => (Array.range 512).map fun y =>
    (W.getD y []).foldl (fun a c => (tab.getD a #[]).getD c 0) x

@[expose] def invTable (mt : Array (Array ℕ)) (_ : Unit := ()) : Array ℕ :=
  (Array.range 512).map fun x =>
    ((List.range 512).find? fun y => (mt.getD x #[]).getD y 0 == 0).getD 0


end CFSG.OddStandard.HigherRank.YamadaG23.Y63Chk
