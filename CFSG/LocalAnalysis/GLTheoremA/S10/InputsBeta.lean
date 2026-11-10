module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsU

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA.S10
open scoped commutatorElement

namespace S10

@[expose] def isU6n (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 5 q => q.p = 2 ∧ q.exponent = n | _ => False

@[expose] def isTE6n (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedE6 q => q.p = 2 ∧ q.exponent = n | _ => False

@[expose] def isL2n (n : ℕ) : TauCeti.CFSGIndex → Prop
  | .alternating m _ => n = 2 ∧ m = 5
  | .lie i =>
    match i.1 with
    | .A 1 q => q.p = 2 ∧ q.exponent = n
    | _ => False
  | _ => False

@[expose] def isU3n (n : ℕ) : TauCeti.CFSGIndex → Prop :=
  onLie fun | .twistedA 2 q => q.p = 2 ∧ q.exponent = n | _ => False

end S10


@[expose] def Su32InterAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X X' L J : Subgroup G) (b d y : G), GLAPComponent 3 X L → GLAPComponent 3 X' J →
    catalogIs (PSimple 3 L) S9.isU4eight → catalogIs (PSimple 3 J) S9.isU4eight → FieldOn 3 b L → FieldOn 3 d J →
    b ^ 3 = 1 → d ^ 3 = 1 →
    Ipart 3 L b = Ipart 3 J d → y ∈ Ipart 3 L b → y ^ 3 = 1 → y ≠ 1 → IsCentralIn 3 y (Ipart 3 L b) →
    IsCentralIn 3 y L → IsCentralIn 3 y J →
    ∃ Q : Subgroup G, Q ≤ GLAPLayer 3 (L ⊓ Subgroup.centralizer ({y} : Set G)) ⊓
        GLAPLayer 3 (J ⊓ Subgroup.centralizer ({y} : Set G)) ∧
      (∃ g ∈ Q, ∃ g' ∈ Q, g * g' ≠ g' * g) ∧ GLAPPrimeCoreOf 3 Q = ⊥

@[expose] def FieldU3RestrictAt (G : Type) [Group G] [Finite G] : Prop :=
  ∀ (X M : Subgroup G) (g y : G), GLAPComponent 3 X M → catalogIs (PSimple 3 M) S9.isU4eight → FieldOn 3 g M →
    y ^ 3 = 1 → y ≠ 1 → IsCentralIn 3 y M → g * y = y * g →
    FieldOn 3 g (GLAPLayer 3 (M ⊓ Subgroup.centralizer ({y} : Set G)))

end CFSG.LocalAnalysis.GLTheoremA
