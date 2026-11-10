module

public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Induction

public section

namespace CFSG.ClassicalInvolution.Hat2A7N

open CFSG.Open CFSG.ClassicalInvolution.Hat2A7

section Families

variable {F : Type} [Group F]

@[expose] def IsConjSubgroup (K L : Subgroup F) : Prop :=
  ∃ g : F, L = K.map (MulAut.conj g).toMonoidHom

theorem IsConjSubgroup.refl (K : Subgroup F) : IsConjSubgroup K K :=
  ⟨1, (map_conj_one K).symm⟩

theorem IsConjSubgroup.trans {K K' L : Subgroup F} (h₁ : IsConjSubgroup K K')
    (h₂ : IsConjSubgroup K' L) : IsConjSubgroup K L := by
  obtain ⟨g, rfl⟩ := h₁
  obtain ⟨h, rfl⟩ := h₂
  exact ⟨h * g, map_map_conj K g h⟩

theorem isConjSubgroup_map_conj (K : Subgroup F) (g : F) :
    IsConjSubgroup K (K.map (MulAut.conj g).toMonoidHom) := ⟨g, rfl⟩

@[expose] def IsCommProd (z x : F) : Prop :=
  ∃ S : Set F, S ⊆ classOf z ∧ (∀ a ∈ S, ∀ b ∈ S, a * b = b * a) ∧ x ∈ Subgroup.closure S

theorem isCommProd_of_mem_classOf {z v : F} (hv : v ∈ classOf z) : IsCommProd z v :=
  ⟨{v}, Set.singleton_subset_iff.mpr hv, by rintro a rfl b rfl; rfl, Subgroup.subset_closure rfl⟩

theorem IsCommProd.congr {z x : F} (hx : x ∈ classOf z) {y : F} :
    IsCommProd x y ↔ IsCommProd z y := by
  rw [IsCommProd, IsCommProd, classOf_eq_of_mem hx]

@[expose] def IsTwinDiag (K : Subgroup F) (x : F) (L : Subgroup F) : Prop :=
  ∃ K' : Subgroup F, IsConjSubgroup K K' ∧
    ∃ h : (∀ k ∈ K', ∀ k' ∈ K', k * (x * k' * x⁻¹) = (x * k' * x⁻¹) * k),
      L = (diagHom K' x h).range

theorem IsTwinDiag.of_isConjSubgroup {K K' : Subgroup F} (h : IsConjSubgroup K K') {x : F}
    {L : Subgroup F} (hL : IsTwinDiag K' x L) : IsTwinDiag K x L := by
  obtain ⟨K'', h'', hc, rfl⟩ := hL
  exact ⟨K'', h.trans h'', hc, rfl⟩

end Families

section Narrowed


end Narrowed

section Tight

variable {F : Type} [Group F]

@[expose] def TightIH (K : Subgroup F) (z : F) : Prop :=
  ∀ x : F, orderOf x = 2 → IsCommProd z x → ∀ (L M : Subgroup F) (u v : F),
    (IsConjSubgroup K L ∨ IsTwinDiag K x L) → IsConjSubgroup K M →
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) L u →
    IsClassical2A7 (Subgroup.centralizer ({x} : Set F)) M v → CommOrEq L M

@[expose] def TightP1 (K : Subgroup F) : Prop :=
  ∀ (L : Subgroup F) (u : F), IsConjSubgroup K L → IsClassical2A7 ⊤ L u →
    classicalInvolutionOddCore ↥L ≤ Subgroup.center ↥L

structure TightSettingN (F : Type) [Group F] (K : Subgroup F) (z : F) : Prop where
  tight : IsTight K z
  center_trivial : ∀ x : F, (∀ y : F, x * y = y * x) → x = 1
  IH : TightIH K z
  P1 : TightP1 K


end Tight

end CFSG.ClassicalInvolution.Hat2A7N
