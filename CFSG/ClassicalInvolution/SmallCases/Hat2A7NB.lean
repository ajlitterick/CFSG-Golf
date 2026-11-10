module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7NDefs
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7LocalB

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Hat2A7

section Stable

variable {F : Type} [Group F]

theorem conj_conj_comm {x c : F} (hxc : x * c = c * x) (y : F) :
    x * (c * y * c⁻¹) * x⁻¹ = c * (x * y * x⁻¹) * c⁻¹ := by
  have h2 : x⁻¹ * c⁻¹ = c⁻¹ * x⁻¹ := (Commute.inv_inv (show Commute x c from hxc)).eq
  calc x * (c * y * c⁻¹) * x⁻¹ = (x * c) * y * (c⁻¹ * x⁻¹) := by group
    _ = (c * x) * y * (x⁻¹ * c⁻¹) := by rw [hxc, ← h2]
    _ = c * (x * y * x⁻¹) * c⁻¹ := by group

theorem IsTwinDiag.map_conj {K : Subgroup F} {x : F} {L : Subgroup F} (hL : IsTwinDiag K x L)
    {c : F} (hc : c ∈ Subgroup.centralizer ({x} : Set F)) :
    IsTwinDiag K x (L.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨K', hK', h, rfl⟩ := hL
  have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.mp hc x rfl
  have h' : ∀ k ∈ K'.map (MulAut.conj c).toMonoidHom, ∀ k' ∈ K'.map (MulAut.conj c).toMonoidHom,
      k * (x * k' * x⁻¹) = (x * k' * x⁻¹) * k := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := h a ha b hb
    show c * a * c⁻¹ * (x * (c * b * c⁻¹) * x⁻¹) = x * (c * b * c⁻¹) * x⁻¹ * (c * a * c⁻¹)
    rw [conj_conj_comm hxc b]
    calc c * a * c⁻¹ * (c * (x * b * x⁻¹) * c⁻¹) = c * (a * (x * b * x⁻¹)) * c⁻¹ := by group
      _ = c * ((x * b * x⁻¹) * a) * c⁻¹ := by rw [h1]
      _ = c * (x * b * x⁻¹) * c⁻¹ * (c * a * c⁻¹) := by group
  refine ⟨K'.map (MulAut.conj c).toMonoidHom, hK'.trans (isConjSubgroup_map_conj K' c), h', ?_⟩
  ext y
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨⟨c * (k : F) * c⁻¹, (k : F), k.2, rfl⟩, ?_⟩
    show c * (k : F) * c⁻¹ * (x * (c * (k : F) * c⁻¹) * x⁻¹) =
      c * ((k : F) * (x * (k : F) * x⁻¹)) * c⁻¹
    rw [conj_conj_comm hxc (k : F)]
    group
  · rintro ⟨⟨_, k, hk, rfl⟩, rfl⟩
    refine ⟨k * (x * k * x⁻¹), ⟨⟨k, hk⟩, rfl⟩, ?_⟩
    show c * (k * (x * k * x⁻¹)) * c⁻¹ = c * k * c⁻¹ * (x * (c * k * c⁻¹) * x⁻¹)
    rw [conj_conj_comm hxc k]
    group

end Stable

section Closure


end Closure

section NarrowedB


end NarrowedB

end CFSG.ClassicalInvolution.Hat2A7N
