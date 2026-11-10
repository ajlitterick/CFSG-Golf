module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH


def oddVecs5 : Finset (Fin 5 → ZMod 2) := Finset.univ.filter fun x => x ⬝ᵥ x = 1


def stdBasis5 : Finset (Fin 5 → ZMod 2) :=
  {![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]}

def otherBasis5 : Fin 5 → Finset (Fin 5 → ZMod 2)
  | 0 => {![1, 0, 0, 0, 0], ![0, 0, 1, 1, 1], ![0, 1, 0, 1, 1], ![0, 1, 1, 0, 1], ![0, 1, 1, 1, 0]}
  | 1 => {![0, 1, 0, 0, 0], ![0, 0, 1, 1, 1], ![1, 0, 0, 1, 1], ![1, 0, 1, 0, 1], ![1, 0, 1, 1, 0]}
  | 2 => {![0, 0, 1, 0, 0], ![0, 1, 0, 1, 1], ![1, 0, 0, 1, 1], ![1, 1, 0, 0, 1], ![1, 1, 0, 1, 0]}
  | 3 => {![0, 0, 0, 1, 0], ![0, 1, 1, 0, 1], ![1, 0, 1, 0, 1], ![1, 1, 0, 0, 1], ![1, 1, 1, 0, 0]}
  | 4 => {![0, 0, 0, 0, 1], ![0, 1, 1, 1, 0], ![1, 0, 1, 1, 0], ![1, 1, 0, 1, 0], ![1, 1, 1, 0, 0]}

def bases5 : Fin 6 → Finset (Fin 5 → ZMod 2) :=
  ![stdBasis5, otherBasis5 0, otherBasis5 1, otherBasis5 2, otherBasis5 3, otherBasis5 4]


private def ExtendsFour (a b c d : Fin 5 → ZMod 2) : Prop :=
  ∀ e ∈ oddVecs5, a ⬝ᵥ e = 0 → b ⬝ᵥ e = 0 → c ⬝ᵥ e = 0 → d ⬝ᵥ e = 0 →
    ∃ i : Fin 6, a ∈ bases5 i ∧ b ∈ bases5 i ∧ c ∈ bases5 i ∧ d ∈ bases5 i ∧ e ∈ bases5 i

private instance (a b c d : Fin 5 → ZMod 2) : Decidable (ExtendsFour a b c d) := by
  unfold ExtendsFour
  infer_instance

private def ExtendsThree (a b c : Fin 5 → ZMod 2) : Prop :=
  ∀ d ∈ oddVecs5, a ⬝ᵥ d = 0 → b ⬝ᵥ d = 0 → c ⬝ᵥ d = 0 → ExtendsFour a b c d

private instance (a b c : Fin 5 → ZMod 2) : Decidable (ExtendsThree a b c) := by
  unfold ExtendsThree
  infer_instance

private def ExtendsTwo (a b : Fin 5 → ZMod 2) : Prop :=
  ∀ c ∈ oddVecs5, a ⬝ᵥ c = 0 → b ⬝ᵥ c = 0 → ExtendsThree a b c

private instance (a b : Fin 5 → ZMod 2) : Decidable (ExtendsTwo a b) := by
  unfold ExtendsTwo
  infer_instance

private def ExtendsOne (a : Fin 5 → ZMod 2) : Prop :=
  ∀ b ∈ oddVecs5, a ⬝ᵥ b = 0 → ExtendsTwo a b

private instance (a : Fin 5 → ZMod 2) : Decidable (ExtendsOne a) := by
  unfold ExtendsOne
  infer_instance


end CFSG.ASVolI.ChH
