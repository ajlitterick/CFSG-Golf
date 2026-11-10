module

public import CFSG.Certificates.CentralizerFinite
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.CosetTable

open CFSG.Certificates CFSG.Certificates.CosetEnumeration
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commute_of_comm_eq_one {x v : G} (h : x⁻¹ * v⁻¹ * x * v = 1) : Commute x v := by
  have : v⁻¹ * x * v = x := by
    have := congrArg (x * ·) h
    simpa [mul_assoc] using this
  calc x * v = v * (v⁻¹ * x * v) := by group
    _ = v * x := by rw [this]


@[expose] def invC (w : List ℕ) : List ℕ := w.reverse.map invCode

@[expose] def commC (X : ℕ) (v : List ℕ) : List ℕ := [X + 1] ++ invC v ++ [X] ++ v

@[expose] def centOf (X : ℕ) (sq : Bool) (r : List ℕ) (k : ℕ) : List (List ℕ) :=
  if k = 0 then [] else
  let v := (r.take (r.length / k)).drop ((r.take (r.length / k)).length / 2 + 1)
  if r = (List.replicate k (commC X v)).flatten then
    if k = 1 then [v]
    else if sq then
      if k % 2 = 0 then [(List.replicate (k / 2) (commC X v)).flatten,
          (List.replicate (k / 2) (commC X (invC v))).flatten]
      else [v ++ (List.replicate (k / 2) (commC X v)).flatten,
          invC v ++ (List.replicate (k / 2) (commC X (invC v))).flatten]
    else []
  else []

@[expose] def centWords (X : ℕ) (rels : List (List ℕ)) : List (List ℕ) :=
  [[X]] ++ rels.flatMap fun r =>
    (List.range (r.length + 1)).flatMap (centOf X (rels.contains [X, X]) r)

@[expose] def relWords (rels : List (List ℕ)) : List (List ℕ) :=
  rels.flatMap fun r => rotations r ++ rotations (invC r)


section Presented

variable {m : ℕ} {rels : Set (FreeGroup (Fin m))}


theorem evalWord_invC {w : List ℕ} (hw : ∀ c ∈ w, c < 2 * m) :
    evalWord (presLetter rels) (invC w) = (evalWord (presLetter rels) w)⁻¹ := by
  have := evalWord_invWord (gen := presLetter rels) (inv := invArr m) (w := w)
    (fun y hy => by rw [invArr_getD (hw y hy)]; exact presLetter_invCode rels (hw y hy))
  have h2 : invWord (invArr m) w = invC w := by
    simp only [invWord, invC]
    apply List.map_congr_left
    intro y hy
    exact invArr_getD (hw y (List.mem_reverse.mp hy))
  rwa [h2] at this


theorem evalWord_codes_eq_one {ws : List (List (Fin m × Bool))} {r : List ℕ}
    (hr : r ∈ codes ws) :
    evalWord (presLetter {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) r = 1 := by
  simp only [codes, List.mem_map] at hr
  obtain ⟨v, hv, rfl⟩ := hr
  rw [evalWord_presLetter]
  exact PresentedGroup.one_of_mem (List.mem_map_of_mem hv)


theorem commute_of_mul_self {x w : G} (hx : x * x = 1) (hw : w * w = 1)
    (h : x * w * x * w = 1) : Commute x w := by
  have hx' : x⁻¹ = x := (eq_inv_of_mul_eq_one_left hx).symm
  have hw' : w⁻¹ = w := (eq_inv_of_mul_eq_one_left hw).symm
  have h2 : (x * w) * (x * w) = 1 := by rw [← h]; simp only [mul_assoc]
  have h3 := eq_inv_of_mul_eq_one_left h2
  rwa [mul_inv_rev, hx', hw'] at h3


theorem lift_mk_eq {ws : List (List (Fin m × Bool))} {K : Type*} [Group K] (φ : PG m ws →* K)
    (w : List (Fin m × Bool)) :
    FreeGroup.lift (fun i => φ (PresentedGroup.of i)) (FreeGroup.mk w) =
      φ (PresentedGroup.mk _ (FreeGroup.mk w)) := by
  have : FreeGroup.lift (fun i => φ (PresentedGroup.of i)) =
      φ.comp (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}) :=
    FreeGroup.ext_hom _ _ fun i => by rw [FreeGroup.lift_apply_of]; rfl
  rw [this]; rfl


@[expose] def commWords (m : ℕ) : List (List (Fin m × Bool)) :=
  (List.finRange m).flatMap fun i =>
    (List.finRange m).map fun j => [(i, false), (j, false), (i, true), (j, true)]

@[expose] def genWord (m i : ℕ) : List (Fin m × Bool) :=
  ((List.finRange m).filter fun j => j.val = i).map fun j => (j, true)


@[expose] def centCheck {m : ℕ} (ws : List (List (Fin m × Bool))) (i cap n cap₂ cap₃ : ℕ) : Bool :=
  decide (i < m) &&
  (centWords (2 * i) (codes ws)).all (fun s => s.all fun c => decide (c < 2 * m)) &&
  checkHLT (mkParams (2 * m) (invArr m) (codes ws) (centWords (2 * i) (codes ws))) cap n &&
  check (presParams (ws ++ [genWord m i]) []) cap₂ 1 &&
  check (presParams (ws ++ commWords m) []) cap₃ 1


end Presented

end CFSG.CosetTable
