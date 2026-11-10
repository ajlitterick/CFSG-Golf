module

public import CFSG.ClassicalInvolution.Q3.Q3TY11
public import CFSG.ClassicalInvolution.Q3.Q3TY9
public import CFSG.ClassicalInvolution.Q3.Q3WASTInner
public import CFSG.ClassicalInvolution.Q3.Q3TCCp
public import CFSG.ClassicalInvolution.Q3.Q3TY1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TC
open CFSG.ClassicalInvolution.RouteD.TWD
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

structure TwinYConfigL3 {G : Type} [Group G] (Ω : Set (Subgroup G)) (K T : Subgroup G) (z : G)
    (e : TwinElt K T z) (J J' : Subgroup G) (w : G) (e' : TwinElt J J' w) (β : Subgroup G)
    (s : G) : Prop where
  twin : IsTwinAt Ω K T z
  clsT : IsClassicalMember3 T z
  mem_J : J ∈ centralizingMembers Ω {z}
  mem_J' : J' ∈ centralizingMembers Ω {z}
  J_ne_K : J ≠ K
  J_ne_T : J ≠ T
  J'_ne_K : J' ≠ K
  J'_ne_T : J' ≠ T
  twinJ : IsTwinAt Ω J J' w
  clsJ : IsClassicalMember3 J w
  clsJ' : IsClassicalMember3 J' w
  memβ : β ∈ centralizingMembers Ω {e'.u}
  clsβ : IsClassicalMember3 β s
  linear : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β
  comm_u : s * e.u = e.u * s
  comm_J : Commutes β J
  comm_J' : Commutes β J'

section Config

variable {G : Type} [Group G] [Finite G]


theorem localShapeC3_at_member {a : ℕ} {c : CompData} {K : Subgroup G} {z : G}
    (hR : RouteD3Setup K z) (hshape : LocalShapeC3 a c (conjClass3 K) z) {M : Subgroup G}
    {w : G} (hM : M ∈ conjClass3 K) (hw : IsClassicalMember3 M w) :
    LocalShapeC3 a c (conjClass3 M) w := by
  obtain ⟨g, hg⟩ := hM
  have hMg : M = conjSub g K := hg.symm
  have hw' : w = g * z * g⁻¹ := involution_unique3 hw (hMg ▸ hR.cls.conj g)
  rw [conjClass3_eq_of_mem ⟨g, hg⟩, hw']
  exact hshape.conjShape3 hR.inClass.conjInvariant g

variable [IsSimpleGroup G] {K : Subgroup G} {z : G}


end Config

section Y4


@[expose] def TwinYPatternAtL3 (t : StatedLieTag) (n : ℕ)
    (Pat : ∀ {G : Type} [Group G], Set (Subgroup G) → Subgroup G → Subgroup G → G → Prop) :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), RouteD3Setup K z →
      LocalShapeC3 2 (CompData.model t n) (conjClass3 K) z →
        ∀ (T : Subgroup G) (e : TwinElt K T z) (J J' : Subgroup G) (w : G)
          (e' : TwinElt J J' w) (β : Subgroup G) (s : G),
          TwinYConfigL3 (conjClass3 K) K T z e J J' w e' β s →
          LocalOddCentral (conjClass3 K) {e.u} → LocalOddThreeFree3 (conjClass3 K) e.u →
          LocalOddCentral (conjClass3 K) {e'.u} → LocalOddThreeFree3 (conjClass3 K) e'.u →
          LocalShapeC3 0 (CompData.model (twinYModel 3 t n).1 (twinYModel 3 t n).2)
            (conjClass3 K) e.u →
          LocalShapeC3 0 (CompData.model (twinYModel 3 t n).1 (twinYModel 3 t n).2)
            (conjClass3 K) e'.u → Pat (conjClass3 K) K β s


theorem chainPiece3TwinTD_of_pattern (h3 : OddThreeFreeInput)
    (hpat : ∀ m, 4 ≤ m → PartnerPatternStmt3 m) : Q3TW.ChainPiece3TwinTD :=
  chainPiece3TwinTD_of_on (P := fun _ => True)
    (chainPiece3TwinTDOn_of_pattern h3 (Gaps.fundNoncentral 3)
      (fun N hN _ => hpat (N - 2) (by omega)))
    (chainPiece3TwinTDOn_of_pattern h3 (Gaps.fundNoncentral 3) (fun _ _ h => absurd trivial h))


end Y4

end CFSG.ClassicalInvolution.Q3.Q3TY
