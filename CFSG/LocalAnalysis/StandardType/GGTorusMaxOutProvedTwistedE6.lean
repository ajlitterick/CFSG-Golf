module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
public import CFSG.LieType.Chevalley.TwistedE6OuterOrder
import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.Adapters.TauCetiExceptional.B1Exceptional
import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem tmOut_twistedE6
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = .twistedE6 q)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  have hd' : d' = .twistedE6 q := hd
  subst hd'
  obtain ⟨e⟩ := e
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel J .twistedE6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hp2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hp2 (by decide) e
    · exact CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hp2 (by decide) e
  obtain ⟨K, hField, hFinite, σ, hK, hσ, ⟨e2⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hm
  let : Field K := hField
  let : Finite K := hFinite
  have h1 := CFSG.LieType.Chevalley.card_outer_twistedE6RootGroup_dvd
    q.prime_p q.exponent_pos K hK σ hσ
  have hOutJ : Nat.card (Outer J) ∣ 2 * Nat.gcd 3 (q.card + 1) * q.exponent := by
    have h1' : Nat.card (Outer (CFSG.LieType.Chevalley.twistedE6RootGroup K σ)) ∣
        2 * Nat.gcd 3 (q.card + 1) * q.exponent := by
      simpa only [TauCeti.PrimePower.card_def] using h1
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e2).toEquiv]
    exact h1'
  refine CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd ?_
  simpa only [tmLieOut, TauCeti.PrimePower.card_def] using hOutJ

end CFSG.StandardType.FrameRoute

end
