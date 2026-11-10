module

public import CFSG.ClassicalInvolution.Generic.CoreAssemblyPieces
public import CFSG.ClassicalInvolution.Balance.BootstrapTriple
public import CFSG.ClassicalInvolution.Balance.PassTwoConj
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureDefs

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem card_closure_pair_le_four [Finite G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) : Nat.card (Subgroup.closure ({x, y} : Set G)) ≤ 4 := by
  classical
  have c : y * x = x * y := hxy.symm
  have s1' : ∀ b, x * (x * b) = b := fun b => by rw [← mul_assoc, hx, one_mul]
  have c' : ∀ b, y * (x * b) = x * (y * b) := fun b => by rw [← mul_assoc, c, mul_assoc]
  have i1 : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have i2 : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  have key : ∀ g (hg : g ∈ Subgroup.closure ({x, y} : Set G)),
      g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
    intro g hg
    refine Subgroup.closure_induction
      (p := fun g _ => g = 1 ∨ g = x ∨ g = y ∨ g = x * y) ?_ ?_ ?_ ?_ hg
    · intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with hu | hu <;> subst hu <;> simp
    · simp
    · rintro a b - - (ha | ha | ha | ha) (hb | hb | hb | hb) <;> subst ha <;> subst hb <;>
        simp [mul_assoc, hx, hy, s1', c, c']
    · rintro a - (ha | ha | ha | ha) <;> subst ha <;> simp [i1, i2, c]
  have hsub : (Subgroup.closure ({x, y} : Set G) : Set G) ⊆ ({1, x, y, x * y} : Finset G) := by
    intro g hg
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] using key g hg
  calc Nat.card (Subgroup.closure ({x, y} : Set G))
      = Nat.card ((Subgroup.closure ({x, y} : Set G) : Set G)) := rfl
    _ ≤ Nat.card (({1, x, y, x * y} : Finset G) : Set G) := Nat.card_mono (Set.toFinite _) hsub
    _ = Finset.card ({1, x, y, x * y} : Finset G) := Nat.card_eq_finsetCard _
    _ ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp


theorem omegaConnected_of_deltaConnected {Ω : Set (Subgroup G)}
    (h : CFSG.ClassicalInvolution.RouteD.DeltaConnected Ω) :
    CFSG.ClassicalInvolution.Generic.DeltaClosure.OmegaConnected Ω := by
  intro L hL L' hL'
  have hr := (SimpleGraph.reachable_iff_reflTransGen _ _).mp
    (h.preconnected ⟨L, hL⟩ ⟨L', hL'⟩)
  refine Relation.ReflTransGen.lift
    (p := fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) (fun v : ↥Ω => (v : Subgroup G))
    (fun a b hab => ?_) _ _ hr
  obtain ⟨-, hcomm⟩ := CFSG.ClassicalInvolution.Models.commGraph_adj.mp hab
  exact ⟨b.2, hcomm⟩

end CFSG.ClassicalInvolution.Balance.Bootstrap
