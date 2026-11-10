module

public import CFSG.ClassicalInvolution.RouteD.Leaf
public import CFSG.ClassicalInvolution.RouteD.Root
public import CFSG.LieType.Universal.Spin.Roots.TypeB
public import CFSG.LieType.Universal.Spin.Roots.TypeD

public section

namespace CFSG.ClassicalInvolution.RouteD

open TauCeti CFSG.LieType.RootSystem


section B

open CFSG.LieType.Universal.Spin


end B

section D

open CFSG.LieType.Universal.Spin


end D


section Exceptional

@[expose] def refl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (v : Fin n → ℤ) :
    Fin n → ℤ :=
  fun k => if k = i then v k - ∑ j, A i j * v j else v k

theorem reflection_eq_refl {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (v : Fin n → ℤ) :
    reflection A i v = refl A i v := by
  funext k
  rw [reflection_apply]
  by_cases hk : k = i
  · subst hk; simp [refl, sub_eq_add_neg]
  · simp [refl, hk]

@[expose] def chainVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) (l : List (Fin n)) :
    Fin n → ℤ :=
  l.foldl (fun v i => refl A i v) (Pi.single j 1)

theorem rroot_chainVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (j : Fin n) (l : List (Fin n)) :
    RRoot A (chainVec A j l) := by
  suffices ∀ (l : List (Fin n)) (v : Fin n → ℤ), RRoot A v →
      RRoot A (l.foldl (fun v i => refl A i v) v) from this l _ (RRoot.simple j)
  intro l
  induction l with
  | nil => intro v hv; exact hv
  | cons i l ih =>
    intro v hv
    exact ih _ (by show RRoot A (refl A i v); rw [← reflection_eq_refl]; exact hv.reflect i)


end Exceptional


end CFSG.ClassicalInvolution.RouteD
