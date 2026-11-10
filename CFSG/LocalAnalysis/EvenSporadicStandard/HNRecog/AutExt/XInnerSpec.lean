module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XInnerAbs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.Section3


structure XNFacts : Prop where
  a_mem : elemA ∈ XP
  a_central : ∀ x ∈ XP, x * elemA = elemA * x
  inner : XAutInner ↥XP ⟨elemA, a_mem⟩
  norm_N : ∀ g ∈ XP, ∀ n ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))),
    g * n * g⁻¹ ∈ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408)))
  der_le : derivedOf XP ≤ closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408)))
  c1_mem : elemW xC1 ∈ derivedOf XP
  c2_mem : elemW xC2 ∈ derivedOf XP


theorem xInner_of_facts (F : XNFacts) :
    ∀ A : ↥XP, (A : Equiv.Perm (Fin 1408)) = elemA → XAutInner ↥XP A := by
  intro A hA
  have : A = ⟨elemA, F.a_mem⟩ := Subtype.ext hA
  rw [this]
  exact F.inner


end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
