module

public import CFSG.Open.LocalVocabulary
import CFSG.Mathlib.GroupTheory.PermCenter

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Open

theorem exists_permHom {H : Type*} [Group H] {X : Type*} (act : H → X → X)
    (hone : ∀ x, act 1 x = x) (hmul : ∀ g h x, act (g * h) x = act g (act h x)) {n : ℕ}
    (p : Fin n → X) (hinj : Function.Injective p)
    (hinv : ∀ (h : H) (i : Fin n), ∃ j : Fin n, act h (p i) = p j) :
    ∃ π : H →* Equiv.Perm (Fin n), ∀ (h : H) (i : Fin n), act h (p i) = p (π h i) := by
  classical
  let f : H → Fin n → Fin n := fun h i => Classical.choose (hinv h i)
  have hf : ∀ h i, act h (p i) = p (f h i) := fun h i => Classical.choose_spec (hinv h i)
  have hf1 : f 1 = id := by
    funext i
    exact hinj (by rw [← hf 1 i, hone]; rfl)
  have hfcomp : ∀ g h, f (g * h) = f g ∘ f h := by
    intro g h
    funext i
    apply hinj
    calc p (f (g * h) i) = act (g * h) (p i) := (hf (g * h) i).symm
      _ = act g (act h (p i)) := hmul g h (p i)
      _ = act g (p (f h i)) := by rw [hf h i]
      _ = p (f g (f h i)) := hf g (f h i)
  have hleft : ∀ h, f h⁻¹ ∘ f h = id := by
    intro h
    rw [← hfcomp h⁻¹ h, inv_mul_cancel, hf1]
  have hright : ∀ h, f h ∘ f h⁻¹ = id := by
    intro h
    rw [← hfcomp h h⁻¹, mul_inv_cancel, hf1]
  let πfun : H → Equiv.Perm (Fin n) := fun h =>
    Equiv.ofBijective (f h)
      ⟨Function.LeftInverse.injective (fun i => congrFun (hleft h) i),
       Function.RightInverse.surjective (fun i => congrFun (hright h) i)⟩
  have hπ : ∀ h i, πfun h i = f h i := fun h i => Equiv.ofBijective_apply (f h) _ i
  have hmulπ : ∀ g h, πfun (g * h) = πfun g * πfun h := by
    intro g h
    apply Equiv.ext
    intro i
    rw [Equiv.Perm.mul_apply, hπ, hπ, hπ]
    exact congrFun (hfcomp g h) i
  have honeπ : πfun 1 = 1 := by
    apply Equiv.ext
    intro i
    rw [hπ, hf1]
    rfl
  exact ⟨{ toFun := πfun, map_one' := honeπ, map_mul' := hmulπ }, fun h i => hf h i⟩


end CFSG.Quasithin.AppendixH.H12
