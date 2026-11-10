module

public import CFSG.Milestones.ASVolI.B4
public import CFSG.Quasithin.Background.SmithB42G2Nat
public import CFSG.Quasithin.MS93.M15G2Off
public import CFSG.Quasithin.Background.SmithB42G2IdFact
public import CFSG.GH74.GLS.Stage4.HexModelG2
public import CFSG.Quasithin.Vol2.Ch11G2Q8ParG2
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base13
public import CFSG.Quasithin.Background.SmithC27RTypeU33
public import CFSG.Quasithin.Vol2.Ch11G2Q8Siegel
public import CFSG.Sporadic.Recognition.LyonsAS44Frattini
public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.ASVolI

open CFSG.Open

section Base

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8


variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}


end Base

section Cert

open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.Ch11.G2Q8
  CFSG.Quasithin.Vol2.KGNat CFSG.GH74.GLS.Stage4.Hex CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint


end Cert

section R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}


section Transfer

variable {M N : Type*} [Group M] [Group N]


end Transfer

end R

section GS

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}


end GS

section M

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

section Defs

variable (K : Type) [Field K] [CharP K 2]


end Defs

variable {V : Type} [CommGroup V] {n : ℕ} {K : Type} [Field K]
  {G L : Subgroup (MulAut V)} {π : ↥(quasithinG2 K) →* MulAut V}
  {θ : V →* Multiplicative (NatQ K)}


end M

section MP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

variable {K : Type} [Field K] [CharP K 2]


open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL)


@[expose] def burnsideB46_mp_Rel (y y' : Ix3 → K) : Prop :=
  ∃ p ∈ stabQ (stdF K 1), g2Act p y = y'


theorem burnsideB46_mp_Rel.symm {y y' : Ix3 → K} (h : burnsideB46_mp_Rel y y') :
    burnsideB46_mp_Rel y' y := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p⁻¹, Subgroup.inv_mem _ hp, g2Act_inv_apply p y⟩

theorem burnsideB46_mp_Rel.trans {y y' y'' : Ix3 → K} (h : burnsideB46_mp_Rel y y')
    (h' : burnsideB46_mp_Rel y' y'') : burnsideB46_mp_Rel y y'' := by
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨p', hp', rfl⟩ := h'
  exact ⟨p' * p, Subgroup.mul_mem _ hp' hp, g2Act_mul_apply p' p y⟩


end MP

section WP2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open CFSG.ClassicalInvolution.ModelFacts.OddCover (uSL uSL_inv)


variable {K : Type} [Field K] [CharP K 2]

@[expose] def burnsideB46_wp2_Rel (y y' : Ix3 → K) : Prop :=
  ∃ p ∈ stabQ (stdF K 2), g2Act p y = y'


theorem burnsideB46_wp2_Rel.symm {y y' : Ix3 → K} (h : burnsideB46_wp2_Rel y y') :
    burnsideB46_wp2_Rel y' y := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p⁻¹, Subgroup.inv_mem _ hp, g2Act_inv_apply p y⟩

theorem burnsideB46_wp2_Rel.trans {y y' y'' : Ix3 → K} (h : burnsideB46_wp2_Rel y y')
    (h' : burnsideB46_wp2_Rel y' y'') : burnsideB46_wp2_Rel y y'' := by
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨p', hp', rfl⟩ := h'
  exact ⟨p' * p, Subgroup.mul_mem _ hp' hp, g2Act_mul_apply p' p y⟩


end WP2

section W14B

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end W14B

section N1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement


section N1Transport


end N1Transport


end N1

section W1G

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement


end W1G

section Fin1

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


section Certs1


end Certs1


end Fin1

section OF

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end OF

section OFa

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end OFa

section P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end P3

section P3a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB


section NatQ


end NatQ

section MaxPar


end MaxPar

end P3a

section P3b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end P3b

section P3c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end P3c

section P3d

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end P3d

section P3e

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end P3e

section P3f

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped Matrix


end P3f

section P3g

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end P3g

section P3h

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB


end P3h

section P3i

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end P3i

section P3j

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end P3j

section P3k


end P3k

section P3n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end P3n

section ASModel

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end ASModel

section ASV

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end ASV

section ASb

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end ASb

section OFn

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end OFn

section ASn

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end ASn

section P4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


open scoped commutatorElement


end P4

section P4a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


open scoped commutatorElement


namespace burnsideB46_p4_Coord


end burnsideB46_p4_Coord

section OfHyp


end OfHyp


namespace burnsideB46_p4_Coord


end burnsideB46_p4_Coord


namespace burnsideB46_p4_Coord


end burnsideB46_p4_Coord

end P4a

section P4b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement Pointwise


end P4b

section P4c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped commutatorElement


end P4c

section P4d

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement Pointwise


end P4d

section P4e

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped commutatorElement


end P4e

section P4n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped commutatorElement


end P4n

section P4na

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement Pointwise


end P4na

section P5

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped Matrix


section Transfer


end Transfer


end P5

section V

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped Matrix


end V

section P5a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped Matrix


end P5a

section P5b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped Matrix


section ConjModel


end ConjModel

end P5b

section V6

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped Matrix


end V6

section P5c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end P5c

section P5d

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end P5d

section P5n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped Matrix


end P5n

section V5n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped Matrix


end V5n

section P5na

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end P5na

section W11

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


section Model


end Model

section VLevel


end VLevel

end W11

section W11a

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end W11a

section W11aV

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end W11aV

section W11b

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end W11b

section W11c

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end W11c

section W11n

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end W11n

section W14D

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2

open scoped commutatorElement Matrix


end W14D

section W14

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2
open scoped commutatorElement Pointwise

section PartA


end PartA

section Abstract


end Abstract


section Model


end Model


section VLevel


end VLevel

end W14

section Fin2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end Fin2

section Asm

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end Asm

section AsmOne

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end AsmOne

section Asm2

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end Asm2

section Fin3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end Fin3

section Fin4

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise

end Fin4

section Target

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end Target

section Printed

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
open scoped commutatorElement Pointwise


end Printed

section Neg

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChB
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Quasithin.Vol2.KGNat
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2


end Neg

end CFSG.ASVolI
