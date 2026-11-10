module

public import CFSG.GroupTheory.GLnTwoSplitting.Main

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Matrix

variable {Γ : Type*} [Group Γ] {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]

structure TwoCocycle (ρ : Γ →* (A ≃ₗ[ZMod 2] A)) where
  f : Γ × Γ → A
  cond : ∀ g h j, f (g * h, j) + f (g, h) = ρ g (f (h, j)) + f (g, h * j)

namespace TwoCocycle

variable {ρ : Γ →* (A ≃ₗ[ZMod 2] A)} (c : TwoCocycle ρ)

theorem f_one_left (g : Γ) : c.f (1, g) = c.f (1, 1) := by
  have h := c.cond 1 1 g
  rw [one_mul, one_mul, map_one] at h
  change c.f (1, g) + c.f (1, 1) = c.f (1, g) + c.f (1, g) at h
  exact (add_left_cancel h).symm

theorem f_one_right (g : Γ) : c.f (g, 1) = ρ g (c.f (1, 1)) := by
  have h := c.cond g 1 1
  rw [mul_one, mul_one] at h
  exact add_right_cancel h

@[ext] structure Ext (_c : TwoCocycle ρ) where
  fst : A
  snd : Γ

instance : Mul c.Ext :=
  ⟨fun x y => ⟨x.fst + ρ x.snd y.fst + c.f (x.snd, y.snd), x.snd * y.snd⟩⟩

instance : One c.Ext :=
  ⟨⟨-c.f (1, 1), 1⟩⟩

instance : Inv c.Ext :=
  ⟨fun x => ⟨-c.f (1, 1) - ρ x.snd⁻¹ x.fst - c.f (x.snd⁻¹, x.snd), x.snd⁻¹⟩⟩

@[simp] theorem mul_fst (x y : c.Ext) : (x * y).fst = x.fst + ρ x.snd y.fst + c.f (x.snd, y.snd) :=
  rfl

@[simp] theorem mul_snd (x y : c.Ext) : (x * y).snd = x.snd * y.snd :=
  rfl

@[simp] theorem one_fst : (1 : c.Ext).fst = -c.f (1, 1) :=
  rfl

@[simp] theorem one_snd : (1 : c.Ext).snd = 1 :=
  rfl

@[simp] theorem inv_fst (x : c.Ext) :
    x⁻¹.fst = -c.f (1, 1) - ρ x.snd⁻¹ x.fst - c.f (x.snd⁻¹, x.snd) :=
  rfl

@[simp] theorem inv_snd (x : c.Ext) : x⁻¹.snd = x.snd⁻¹ :=
  rfl

instance : Group c.Ext :=
  Group.ofLeftAxioms
    (fun x y z => by
      refine Ext.ext ?_ (mul_assoc _ _ _)
      simp only [mul_fst, mul_snd, map_add, map_mul, LinearEquiv.mul_apply]
      have := c.cond x.snd y.snd z.snd
      calc _ = x.fst + ρ x.snd y.fst + ρ x.snd (ρ y.snd z.fst) +
            (c.f (x.snd * y.snd, z.snd) + c.f (x.snd, y.snd)) := by abel
        _ = _ := by rw [this]; abel)
    (fun x => by
      refine Ext.ext ?_ (one_mul _)
      simp only [mul_fst, one_fst, one_snd, map_one, c.f_one_left]
      change -c.f (1, 1) + x.fst + c.f (1, 1) = _
      abel)
    (fun x => by
      refine Ext.ext ?_ (inv_mul_cancel _)
      simp only [mul_fst, inv_fst, inv_snd, one_fst]
      abel)

@[expose] def snd' : c.Ext →* Γ where
  toFun x := x.snd
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def ι (a : A) : c.Ext :=
  ⟨a - c.f (1, 1), 1⟩

theorem ι_add (a b : A) : c.ι (a + b) = c.ι a * c.ι b := by
  refine Ext.ext ?_ (mul_one 1).symm
  simp only [ι, mul_fst, map_one]
  change a + b - c.f (1, 1) = a - c.f (1, 1) + (b - c.f (1, 1)) + c.f (1, 1)
  abel

theorem mul_ι (x : c.Ext) (e : A) : x * c.ι e = c.ι (ρ x.snd e) * x := by
  refine Ext.ext ?_ (by
    change x.snd * 1 = 1 * x.snd
    rw [mul_one, one_mul])
  simp only [ι, mul_fst]
  rw [c.f_one_right x.snd, c.f_one_left x.snd, map_sub, map_one]
  change x.fst + (ρ x.snd e - ρ x.snd (c.f (1, 1))) + ρ x.snd (c.f (1, 1)) =
    ρ x.snd e - c.f (1, 1) + x.fst + c.f (1, 1)
  abel

instance [Finite A] [Finite Γ] : Finite c.Ext :=
  Finite.of_injective (fun x : c.Ext => (x.fst, x.snd)) fun _ _ h =>
    Ext.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

@[expose] noncomputable def natExt (hinj : Function.Injective ρ) (hsurj : Function.Surjective ρ) :
    NatExt c.Ext A where
  ι := c.ι
  ι_add := c.ι_add
  injective a b h := sub_left_injective (congrArg Ext.fst h)
  π := ρ.comp c.snd'
  surjective := hsurj.comp fun g => ⟨⟨0, g⟩, rfl⟩
  ker_iff x := by
    constructor
    · intro h
      have hx : x.snd = 1 := hinj (h.trans (map_one ρ).symm)
      exact ⟨x.fst + c.f (1, 1), Ext.ext (add_sub_cancel_right _ _) hx.symm⟩
    · rintro ⟨e, rfl⟩
      exact map_one ρ
  conj x e := by
    rw [c.mul_ι, mul_inv_cancel_right]
    rfl

theorem exists_eq [Finite Γ] [FiniteDimensional (ZMod 2) A] (hA : 6 ≤ finrank (ZMod 2) A)
    (hinj : Function.Injective ρ) (hsurj : Function.Surjective ρ) :
    ∃ s : Γ → A, ∀ g h, c.f (g, h) = ρ g (s h) - s (g * h) + s g := by
  have : Finite A := Module.finite_of_finite (ZMod 2)
  let X := c.natExt hinj hsurj
  obtain ⟨K, hVK, hVK'⟩ := X.exists_complement hA
  have hsnd : ∀ y ∈ X.V, y.snd = 1 := by
    rintro _ ⟨e, rfl⟩
    rfl
  have hex : ∀ g : Γ, ∃ k ∈ K, k.snd = g := by
    intro g
    have hmem : (⟨0, g⟩ : c.Ext) ∈ X.V ⊔ K := by rw [hVK']; exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.1 hmem
    refine ⟨z, hz, ?_⟩
    have := congrArg Ext.snd hyz
    rwa [mul_snd, hsnd y hy, one_mul] at this
  choose k hkK hk2 using hex
  have huniq : ∀ k' ∈ K, k' = k k'.snd := by
    intro k' hk'
    have h1 : k' * (k k'.snd)⁻¹ ∈ X.V ⊓ K := by
      refine Subgroup.mem_inf.2 ⟨(X.ker_iff _).1 ?_, K.mul_mem hk' (K.inv_mem (hkK _))⟩
      change ρ ((k' * (k k'.snd)⁻¹).snd) = 1
      rw [mul_snd, inv_snd, hk2, mul_inv_cancel, map_one]
    rw [hVK, Subgroup.mem_bot] at h1
    exact mul_inv_eq_one.1 h1
  refine ⟨fun g => -(k g).fst, fun g h => ?_⟩
  have h1 := huniq (k g * k h) (K.mul_mem (hkK g) (hkK h))
  rw [mul_snd, hk2, hk2] at h1
  have h3 := congrArg Ext.fst h1
  simp only [mul_fst, hk2] at h3
  show c.f (g, h) = ρ g (-(k h).fst) - -(k (g * h)).fst + -(k g).fst
  rw [map_neg, ← h3]
  abel

end TwoCocycle

@[expose] def repLinearEquivHom {k G V : Type*} [CommSemiring k] [Group G]
    [AddCommMonoid V] [Module k V] (ρ : Representation k G V) : G →* (V ≃ₗ[k] V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).toMonoidHom.comp ρ.asGroupHom

@[expose] noncomputable def naturalRep (n : ℕ) :
    Representation (ZMod 2) (GL (Fin n) (ZMod 2)) (Fin n → ZMod 2) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) (ZMod 2) ≃ₐ[ZMod 2] _).toMonoidHom.comp
    (Units.coeHom _)

end CFSG.GroupTheory.GLnTwoSplitting
