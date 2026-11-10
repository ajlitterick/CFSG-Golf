module

public import CFSG.LieType.Multipliers.PresentedCover
public import CFSG.Certificates.CosetTableOrders
public import CFSG.Sporadic.Bridge.TwoGen

public section

namespace CFSG.LieType.Multipliers

open Subgroup CFSG.CosetTable CFSG.Open
open scoped commutatorElement

variable {m : ℕ}

abbrev wordSet (ws : List (List (Fin m × Bool))) : Set (FreeGroup (Fin m)) :=
  {r | r ∈ ws.map FreeGroup.mk}

@[expose] def commWord (u v : List (Fin m × Bool)) : List (Fin m × Bool) :=
  u ++ v ++ FreeGroup.invRev u ++ FreeGroup.invRev v

@[expose] def commWords (c : List (List (Fin m × Bool) × List (Fin m × Bool))) :
    List (Fin m × Bool) :=
  (c.map fun p => commWord p.1 p.2).flatten

@[expose] def coverWords (R : List (List (Fin m × Bool))) (w : Fin m → List (Fin m × Bool)) :
    List (List (Fin m × Bool)) :=
  (List.finRange m).flatMap (fun i => R.map fun r => commWord [(i, true)] r) ++
    (List.finRange m).map fun i => (i, false) :: w i

theorem mk_commWord (u v : List (Fin m × Bool)) :
    FreeGroup.mk (commWord u v) = ⁅FreeGroup.mk u, FreeGroup.mk v⁆ := by
  simp only [commWord, commutatorElement_def, ← FreeGroup.mul_mk, FreeGroup.inv_mk]

theorem mk_commWords_mem_commutator (c : List (List (Fin m × Bool) × List (Fin m × Bool))) :
    FreeGroup.mk (commWords c) ∈ commutator (FreeGroup (Fin m)) := by
  induction c with
  | nil => exact one_mem _
  | cons p c ih =>
    rw [commWords, List.map_cons, List.flatten_cons, ← FreeGroup.mul_mk, mk_commWord]
    exact mul_mem (commutator_mem_commutator (mem_top _) (mem_top _)) ih

theorem coverRelators_wordSet (R : List (List (Fin m × Bool)))
    (w : Fin m → List (Fin m × Bool)) :
    coverRelators (wordSet R) (fun i => FreeGroup.mk (w i)) = wordSet (coverWords R w) := by
  ext x
  simp only [coverRelators, coverWords, Set.mem_union, Set.mem_ofPred_eq, Set.mem_range,
    List.map_append, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_finRange,
    true_and]
  constructor
  · rintro (⟨i, _, ⟨r, hr, rfl⟩, rfl⟩ | ⟨i, rfl⟩)
    · exact Or.inl ⟨_, ⟨i, r, hr, rfl⟩, by rw [mk_commWord]; rfl⟩
    · refine Or.inr ⟨_, ⟨i, rfl⟩, ?_⟩
      rw [← List.singleton_append, ← FreeGroup.mul_mk]
      rfl
  · rintro (⟨_, ⟨i, r, hr, rfl⟩, rfl⟩ | ⟨_, ⟨i, rfl⟩, rfl⟩)
    · exact Or.inl ⟨i, _, ⟨r, hr, rfl⟩, by rw [mk_commWord]; rfl⟩
    · refine Or.inr ⟨i, ?_⟩
      rw [← List.singleton_append, ← FreeGroup.mul_mk]
      rfl

theorem lift_comp_mulEquiv {X Y : Type*} [Group X] [Group Y] {ι : Type*} (g : ι → X)
    (e : X ≃* Y) :
    FreeGroup.lift (fun i => e (g i)) = e.toMonoidHom.comp (FreeGroup.lift g) :=
  FreeGroup.ext_hom _ _ fun i => by simp

theorem lift_mulEquiv {X Y : Type*} [Group X] [Group Y] {ι : Type*} (g : ι → X) (e : X ≃* Y)
    (w : FreeGroup ι) : FreeGroup.lift (fun i => e (g i)) w = e (FreeGroup.lift g w) := by
  rw [lift_comp_mulEquiv]
  rfl

theorem IsPresentation.mulEquiv {X Y : Type*} [Group X] [Group Y] {ι : Type*} {g : ι → X}
    {R : Set (FreeGroup ι)} (hP : IsPresentation g R) (e : X ≃* Y) :
    IsPresentation (fun i => e (g i)) R := by
  refine ⟨?_, ?_⟩
  · rw [lift_comp_mulEquiv]
    exact e.surjective.comp hP.lift_surjective
  · rw [lift_comp_mulEquiv, ← hP.ker_lift]
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]

theorem lift_mk_eq_wordProd {G : Type*} [Group G] (x : ℕ → G) (v : List (Fin m × Bool)) :
    FreeGroup.lift (fun i : Fin m => x i.val) (FreeGroup.mk v) =
      CFSG.Sporadic.Bridge.wordProd x (v.map fun l => (l.1.val, l.2)) := by
  rw [FreeGroup.lift_mk, CFSG.Sporadic.Bridge.wordProd, List.map_map]
  congr 1
  refine List.map_congr_left fun l _ => ?_
  rcases l with ⟨i, _ | _⟩ <;> rfl

theorem lift_mk_eq_of_wordProd {G : Type*} [Group G] (x : ℕ → G) {w : List (Fin m × Bool)}
    {i : Fin m}
    (h : CFSG.Sporadic.Bridge.wordProd x ((w ++ [(i, false)]).map fun l => (l.1.val, l.2)) = 1) :
    FreeGroup.lift (fun j : Fin m => x j.val) (FreeGroup.mk w) = x i.val := by
  rw [← lift_mk_eq_wordProd, ← FreeGroup.mul_mk, map_mul, FreeGroup.lift_mk] at h
  simpa [mul_inv_eq_one] using h


private theorem card_finite_of_orderCheck {ws : List (List (Fin m × Bool))} {k cap n fuel : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} (h : orderCheck ws [] k cap n words fuel = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS : subsetOf m [] = [] := by simp [subsetOf]
  have : Finite (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) := by
    rw [hS]; exact (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) = 1 := by
    rw [hS]; exact card_PG_zero _
  have := card_le_of_subsetCheckShortC ws [] (subsetCheckShortC_of_orderCheck h)
  rwa [hc, mul_one] at this


end CFSG.LieType.Multipliers
