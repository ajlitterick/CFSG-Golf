module

public import CFSG.Assembly.OrderReductions.InvolutionFusion
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OrderReductions.TIInvolutionProducts

open CFSG.OrderReductions.InvolutionGraph

@[expose] def conjugateSet {group : Type*} [Group group] (support : Set group) (conjugator : group) : Set group :=
  (fun element => conjugator * element * conjugator⁻¹) '' support

@[expose] def TI {group : Type*} [Group group] (support : Set group) (normalizer : Subgroup group) : Prop :=
  support.Nonempty ∧ (1 : group) ∉ support ∧ Subgroup.normalizer support = normalizer ∧
    ∀ conjugator : group, conjugator ∉ normalizer → Disjoint support (conjugateSet support conjugator)


end CFSG.OrderReductions.TIInvolutionProducts
