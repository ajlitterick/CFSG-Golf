module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LieType.Chevalley.E6OuterOrder
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
import CFSG.Models.Blueprint
public import CFSG.LieType.Chevalley.RootCommutatorData

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint.Chevalley

theorem tmOut_E6
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hd : d.1 = .E6 q)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  dsimp only at hd
  subst hd
  obtain ⟨e⟩ := e
  obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  let e' : J ≃* adjointGroup .E6 K := e.trans φ
  have hK' : Nat.card K = q.p ^ q.exponent := by
    rw [TauCeti.PrimePower.card_def] at hK
    exact hK
  have hOutK : Nat.card (Outer (adjointGroup .E6 K)) ∣
      2 * Nat.gcd 3 (q.p ^ q.exponent - 1) * q.exponent :=
    CFSG.LieType.Chevalley.card_outer_adjointGroup_E6_dvd
      q.prime_p q.exponent_pos K hK'
  have hOutJ : Nat.card (Outer J) ∣
      2 * Nat.gcd 3 (q.p ^ q.exponent - 1) * q.exponent := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact hOutK
  have haut := CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd hOutJ
  have htm : tmLieOut (.E6 q) = 2 * Nat.gcd 3 (q.p ^ q.exponent - 1) * q.exponent := by
    simp only [tmLieOut, TauCeti.PrimePower.card_def]
  change Nat.card (MulAut J) ∣ Nat.card J * tmLieOut (.E6 q)
  rw [htm]
  exact haut

end CFSG.StandardType.FrameRoute

end
