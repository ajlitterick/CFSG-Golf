module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Native
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage2Lin

public section

namespace CFSG.EvenSmallLie.OmegaEight.Stage2

open Matrix CFSG.EvenSmallLie.UnitarySix.YamadaPar

@[expose] def candFilter (E₂ : Enum) (samples : List ℕ) (m : ℕ) : Bool :=
  memK E₂.keys (mulK m m) && fpowK m 256 == idK &&
    samples.all fun c => memK E₂.keys (mulK (mulK m c) (fpowK m 255))

@[expose] def repOK (EC : Enum) (reps : List (ℕ × ℕ)) (m : ℕ) : Bool :=
  reps.any fun r => memK EC.keys (mulK r.2 m)

@[expose] def candCons (zs ys : List ℕ) (cc : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  List.zipWith (fun z y => (z, y)) zs ys ++ cc


end CFSG.EvenSmallLie.OmegaEight.Stage2
