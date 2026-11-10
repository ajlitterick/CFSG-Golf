module

public import CFSG.Walter.Ree.Thompson2.BaseRel.Card
public import CFSG.Walter.Ree.Thompson2.BaseRel.Enum

public section

namespace CFSG.Walter.Ree.T2.BaseRel

open CFSG.Walter.J1Recog Word

section Ev

variable {H : Type*} [Group H]

@[expose] def evList {n : ℕ} (f : Fin n → H) (w : Word n) : H :=
  (w.map fun x => cond x.2 (f x.1) (f x.1)⁻¹).prod

theorem ev_cons {n : ℕ} (f : Fin n → H) (x : Fin n × Bool) (w : Word n) :
    ev f (x :: w) = cond x.2 (f x.1) (f x.1)⁻¹ * ev f w := by
  obtain ⟨i, b⟩ := x
  have h : ((i, b) :: w : Word n) = cond b (gen i) (inv (gen i)) ++ w := by cases b <;> rfl
  rw [h, ev_append]
  cases b <;> simp

theorem ev_eq_evList {n : ℕ} (f : Fin n → H) (w : Word n) : ev f w = evList f w := by
  induction w with
  | nil => simp [evList]
  | cons x w ih =>
    rw [ev_cons, ih]
    simp [evList]

theorem range_lift {n : ℕ} (l : List (Word n)) (f : Fin n → H) (hf : ∀ w ∈ l, ev f w = 1) :
    (lift l f hf).range = Subgroup.closure (Set.range f) := by
  rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
    ← Set.range_comp]
  congr 1
  ext x
  simp


end Ev

@[expose] def pglGen : Fin 4 → Equiv.Perm (Fin 9) := ![pglJ, pglK, pglT, pglY]

theorem range_pglGen : Set.range pglGen = {pglJ, pglK, pglT, pglY} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [pglGen]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

theorem pglGen_rels1512 : ∀ w ∈ rels1512, ev pglGen w = 1 := by
  intro w hw
  rw [ev_eq_evList]
  revert w
  decide +kernel

noncomputable def toPerm1512 : Pres1512 →* Equiv.Perm (Fin 9) :=
  lift rels1512 pglGen pglGen_rels1512

theorem range_toPerm1512 : toPerm1512.range = PGammaL28 := by
  rw [toPerm1512, range_lift, range_pglGen]
  rfl

noncomputable def toPGL1512 : Pres1512 →* PGammaL28 :=
  toPerm1512.codRestrict PGammaL28 fun x => range_toPerm1512 ▸ ⟨x, rfl⟩

theorem toPGL1512_bijective : Function.Bijective toPGL1512 := by
  have hsurj : Function.Surjective toPGL1512 := by
    rintro ⟨g, hg⟩
    rw [← range_toPerm1512] at hg
    obtain ⟨x, rfl⟩ := hg
    exact ⟨x, rfl⟩
  have := card_pres1512_le.1
  exact hsurj.bijective_of_nat_card_le (by rw [card_PGammaL28]; exact card_pres1512_le.2)

noncomputable def iso1512 : Pres1512 ≃* PGammaL28 :=
  MulEquiv.ofBijective toPGL1512 toPGL1512_bijective

theorem iso1512_of (i : Fin 4) :
    ((iso1512 (PresentedGroup.of i) : PGammaL28) : Equiv.Perm (Fin 9)) = pglGen i := by
  change toPerm1512 (PresentedGroup.of i) = pglGen i
  rw [toPerm1512, lift_of]

theorem iso1512_symm_j : iso1512.symm PGammaL28.j = PresentedGroup.of 0 :=
  iso1512.symm_apply_eq.mpr (Subtype.ext (iso1512_of 0).symm)


abbrev C2 := Multiplicative (ZMod 2)


end CFSG.Walter.Ree.T2.BaseRel
