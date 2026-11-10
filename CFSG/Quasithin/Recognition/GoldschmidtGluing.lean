module

public import CFSG.Quasithin.Recognition.GoldschmidtBasic

public section

namespace CFSG.Quasithin

namespace GoldAmalgam

variable {A C B A' C' B' : Type*} [Group A] [Group C] [Group B] [Group A'] [Group C'] [Group B']

structure Iso (X : GoldAmalgam A C B) (Y : GoldAmalgam A' C' B') where
  eA : A ≃* A'
  eC : C ≃* C'
  eB : B ≃* B'
  comm_toA : ∀ c, eA (X.toA c) = Y.toA (eC c)
  comm_toB : ∀ c, eB (X.toB c) = Y.toB (eC c)

@[expose] def IsIso (X : GoldAmalgam A C B) (Y : GoldAmalgam A' C' B') : Prop :=
  Nonempty (X.Iso Y)

theorem IsIso.refl (X : GoldAmalgam A C B) : X.IsIso X :=
  ⟨⟨MulEquiv.refl _, MulEquiv.refl _, MulEquiv.refl _, fun _ => rfl, fun _ => rfl⟩⟩

theorem IsIso.symm {X : GoldAmalgam A C B} {Y : GoldAmalgam A' C' B'} (h : X.IsIso Y) :
    Y.IsIso X := by
  obtain ⟨f⟩ := h
  refine ⟨⟨f.eA.symm, f.eC.symm, f.eB.symm, fun c => ?_, fun c => ?_⟩⟩
  · apply f.eA.injective
    rw [MulEquiv.apply_symm_apply, f.comm_toA, MulEquiv.apply_symm_apply]
  · apply f.eB.injective
    rw [MulEquiv.apply_symm_apply, f.comm_toB, MulEquiv.apply_symm_apply]

theorem IsIso.trans {A'' C'' B'' : Type*} [Group A''] [Group C''] [Group B'']
    {X : GoldAmalgam A C B} {Y : GoldAmalgam A' C' B'} {Z : GoldAmalgam A'' C'' B''}
    (h : X.IsIso Y) (h' : Y.IsIso Z) : X.IsIso Z := by
  obtain ⟨f⟩ := h
  obtain ⟨g⟩ := h'
  refine ⟨⟨f.eA.trans g.eA, f.eC.trans g.eC, f.eB.trans g.eB, fun c => ?_, fun c => ?_⟩⟩
  · simp [f.comm_toA, g.comm_toA]
  · simp [f.comm_toB, g.comm_toB]


@[expose] def inducedAut (i : C →* A) : Subgroup (MulAut C) where
  carrier := {α | ∃ f : MulAut A, ∀ c, f (i c) = i (α c)}
  one_mem' := ⟨1, fun c => rfl⟩
  mul_mem' := by
    rintro α β ⟨f, hf⟩ ⟨g, hg⟩
    exact ⟨f * g, fun c => by rw [MulAut.mul_apply, hg c, hf (β c)]; rfl⟩
  inv_mem' := by
    rintro α ⟨f, hf⟩
    refine ⟨f⁻¹, fun c => ?_⟩
    apply f.injective
    rw [MulAut.apply_inv_self, hf (α⁻¹ c), MulAut.apply_inv_self]


@[expose] def glue (iA : C →* A) (iB : C →* B) (hA : Function.Injective iA)
    (hB : Function.Injective iB) (θ : MulAut C) : GoldAmalgam A C B :=
  ⟨iA, iB.comp θ.toMonoidHom, hA, hB.comp θ.injective⟩


end GoldAmalgam

end CFSG.Quasithin
