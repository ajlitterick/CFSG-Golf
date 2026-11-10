module

public import CFSG.Adapters.TauCetiExceptional.MinusculePeel
public import CFSG.LieType.Steinberg.Minuscule.BruhatExtras
public import CFSG.LieType.Steinberg.Bruhat
public import CFSG.Adapters.TauCetiExceptional.BigCellCore

public noncomputable section

namespace CFSG.TauCetiBridge.Minuscule

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg
  CFSG.TauCetiBridge.BigCell CFSG.LieType.Universal CFSG.LieType.RootSystem MinData

section Mono

variable {d : ℕ} {K : Type*} [Field K]

@[expose] def IsMono (f : Module.End K (Fin d →₀ K)) : Prop :=
  ∀ a, ∃ b, ∃ c : K, f (Finsupp.single a 1) = c • Finsupp.single b 1

theorem IsMono.mul {f g : Module.End K (Fin d →₀ K)} (hf : IsMono f) (hg : IsMono g) :
    IsMono (f * g) := fun a => by
  obtain ⟨b, c, hb⟩ := hg a
  obtain ⟨b', c', hb'⟩ := hf b
  exact ⟨b', c * c', by rw [Module.End.mul_apply, hb, map_smul, hb', smul_smul]⟩


end Mono

section Group


end Group

end CFSG.TauCetiBridge.Minuscule
