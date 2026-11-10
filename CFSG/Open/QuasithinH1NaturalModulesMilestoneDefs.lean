module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.Open
open CFSG.Open

open scoped MatrixGroups

@[expose] noncomputable def quasithinH1MatrixRep {G ι K : Type} [Group G] [Fintype ι] [DecidableEq ι]
    [Field K] [Algebra (ZMod 2) K] (φ : G →* Matrix ι ι K) :
    Representation (ZMod 2) G (ι → K) where
  toFun g := (Matrix.toLin' (φ g)).restrictScalars (ZMod 2)
  map_one' := by ext v; simp
  map_mul' g h := by ext v; simp


end CFSG.Open
