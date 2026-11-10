module

public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureDefs
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic

public section

namespace CFSG.ClassicalInvolution.Generic.DeltaClosure

open CFSG.Open
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn)

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem comm_of_mem_elemAbelian (hA : IsElemAbelian 2 A) {x y : G} (hx : x ∈ A) (hy : y ∈ A) :
    x * y = y * x := CFSG.Open.IsElemAbelian.comm hA hx hy


theorem le_normalizer_oddCoreIn_centralizingLayer [Finite G] (hΩ : ConjInvariant Ω)
    (hA : IsElemAbelian 2 A) {a : G} (ha : a ∈ A) :
    A ≤ Subgroup.normalizer (oddCoreIn (centralizingLayer Ω {a}) : Set G) := fun _ hg =>
  mem_normalizer_oddCoreIn_centralizingLayer hΩ
    (Subgroup.mem_centralizer_singleton_iff.mpr (comm_of_mem_elemAbelian hA hg ha))


end CFSG.ClassicalInvolution.Generic.DeltaClosure
