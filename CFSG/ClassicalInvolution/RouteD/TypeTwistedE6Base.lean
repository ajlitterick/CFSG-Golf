module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Chain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6Frame
public import CFSG.ClassicalInvolution.RouteD.TypeUChain

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg.Exceptional
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

structure IsTE6Base (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) {G : Type} [Group G]
    (Ω : Set (Subgroup G)) (K : Subgroup G) (z : G) (V : Fin 3 → Subgroup G) : Prop where
  mem : V 0 ∈ Ω
  comm : Commutes (V 0) (V 2)
  pair_long : ∃ W, UnitaryB2BlockStandardPair (frobQ p f) (frobQ_frobQ p f hf) W (V 0) (V 1) ∧
    W ≤ V 0 ⊔ V 1 ⊔ V 2
  pair_short : ∃ W, LinearBlockStandardPair (GaloisField p (2 * f)) W (V 1) (V 2)
  cover : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → ∃ h ∈ V 0 ⊔ V 1 ⊔ V 2, L = conjSub h (V 0)

@[expose] def TE6Partner (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G))
    (V : Fin 3 → Subgroup G) : Prop :=
  ∃ β ∈ Ω, (∃ W, LinearBlockStandardPair (GaloisField p f) W β (V 0)) ∧ Commutes β (V 1) ∧
    Commutes β (V 2)

theorem IsTE6Base.isTE6Chain {hf : 1 ≤ f} {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}
    {V : Fin 3 → Subgroup G} (hV : IsTE6Base p f hf Ω K z V) {β : Subgroup G}
    (h01 : ∃ W, LinearBlockStandardPair (GaloisField p f) W β (V 0)) (h1 : Commutes β (V 1))
    (h2 : Commutes β (V 2)) : IsTE6Chain p f hf ![β, V 0, V 1, V 2] where
  comm i j hij := by
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact h1
    · exact h2
    · exact hV.comm
  pair01 := h01
  pair23 := hV.pair_short
  pair12 := hV.pair_long

theorem routeD_twistedE6_of_base [Finite G] (hadm : StatedLieAdmissible .twistedE6 0 p f)
    (hq : 5 ≤ p ^ f) {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) {V : Fin 3 → Subgroup G}
    (hV : IsTE6Base p f hadm.2.1 Ω K z V) (hpartner : TE6Partner p f Ω V) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .twistedE6 ∧ D.rank i = 0 := by
  obtain ⟨β, hβ, h01, h1, h2⟩ := hpartner
  exact routeD_twistedE6_of_chain hadm hq hΩ hK hsingle hconn hz
    (U := ![β, V 0, V 1, V 2]) (hV.isTE6Chain h01 h1 h2) hβ hV.cover

section Existence

theorem injective_comp_of_center {X Y Z W : Type*} [Group X] [Group Y] [Group Z] [Group W]
    (Θ : Y →* Z) (hker : Θ.ker ≤ Subgroup.center Y) (ι : X →* Y) (b : W →* X)
    (hb : Function.Injective (ι.comp b)) (S : Subgroup Y) (hS : (ι.comp b).range ≤ S)
    (hSc : ∀ s ∈ S, s ∈ Subgroup.center Y → s = 1) : Function.Injective ((Θ.comp ι).comp b) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have h1 : (ι.comp b) a ∈ Θ.ker := ha
  have h2 : (ι.comp b) a = 1 := hSc _ (hS ⟨a, rfl⟩) (hker h1)
  exact (injective_iff_map_eq_one _).mp hb a h2

theorem ker_comp_le_center {X Y Z : Type*} [Group X] [Group Y] [Group Z] (Θ : Y →* Z)
    (hker : Θ.ker ≤ Subgroup.center Y) (ι : X →* Y) (hι : Function.Injective ι) :
    (Θ.comp ι).ker ≤ Subgroup.center X := by
  intro x hx
  have hc := hker (show ι x ∈ Θ.ker from hx)
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro y
  apply hι
  rw [map_mul, map_mul]
  exact hc (ι y)


end Existence

end CFSG.ClassicalInvolution.RouteD
