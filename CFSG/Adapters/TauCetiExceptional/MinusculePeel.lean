module

public import CFSG.Adapters.TauCetiExceptional.MinusculeGenPoint
public import CFSG.LieType.Steinberg.Minuscule.Form

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell MinData

variable {τ : Tag} {D : MinData τ} (hV : D.Valid) {R : Type*} [CommRing R]


variable {ι : Type*} (γ : ι → Fin τ.rank → ℤ) (c : ι → R) (φ : (Fin τ.rank → ℤ) →+ ℤ)


@[expose] def EntriesIn {n : ℕ} (T : Subring R) (M : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, M i j ∈ T

theorem EntriesIn.mul {n : ℕ} {T : Subring R} {M N : Matrix (Fin n) (Fin n) R}
    (hM : EntriesIn T M) (hN : EntriesIn T N) : EntriesIn T (M * N) := fun i j => by
  rw [Matrix.mul_apply]
  exact T.sum_mem fun k _ => T.mul_mem (hM i k) (hN k j)


@[expose] def htHom : (Fin τ.rank → ℤ) →+ ℤ :=
  AddMonoidHom.mk' (ht (ι := Fin τ.rank)) fun u v => by
    simp only [ht, Pi.add_apply, Finset.sum_add_distrib]

theorem htHom_apply (v : Fin τ.rank → ℤ) : htHom v = ht v :=
  rfl


end CFSG.TauCetiBridge.Minuscule
