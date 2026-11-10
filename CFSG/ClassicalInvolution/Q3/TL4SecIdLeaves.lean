module

public import CFSG.ClassicalInvolution.Q3.TL3T10

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.Blueprint
open scoped commutatorElement

@[expose] def SecIdE4OddCent : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      TightOddCent t

@[expose] def SecIdE4Edge : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      ¬ TightEdgeless R

@[expose] def SecIdE4DStar : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      T3.DStarConnected (CoreAssembly.conjClass (tightCore R))

@[expose] def SecIdE4NoClique5 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TightDatum R S t → TightCls Y R S t → ¬ TightInO2 t → Subgroup.center Y ≠ ⊥ →
      (LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 1 ∨
        LieModel (Y ⧸ Subgroup.center Y) .POmegaPlus 4 2 1) →
      ∀ B : Fin 5 → Subgroup Y, (∀ i, B i ∈ CoreAssembly.conjClass (tightCore R)) →
        Function.Injective B →
          ¬ ∀ i j, i ≠ j → B j ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (B i)


section Cit3


end Cit3


end CFSG.ClassicalInvolution.Q3.TL4
