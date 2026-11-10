module

public import CFSG.Quasithin.EmptyFaithful.S151cFDec

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section Six151c

variable {V : Type*} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

@[expose] def Shape6 {W : Type*} [CommGroup W] [Finite W] (Y : Subgroup (MulAut W)) (r : ℚ) :
    Prop :=
  IsElemAbelian 3 (fittingOf Y) ∧ Nat.card (fittingOf Y) = 27 ∧
    (∃ A : Subgroup (MulAut W), A ≤ Y ∧ IsElemAbelian2 A ∧ Nat.card A = 4 ∧
      Y = fittingOf Y ⊔ A) ∧ rk W = 6 ∧ r = 3 / 2

open Classical in
theorem not_isCyclic_fittingOf_block (h : Setting151c X Tb Xc) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I)
    (hnc : ¬ IsCyclic ↥(fittingOf (autSub L (commV L)))) : ¬ IsCyclic ↥(fittingOf L) := by
  intro hcyc
  have hs := suppData_block h hI hL
  have hmem : ∀ g : ↥(fittingOf L), resHom (commV L) ⟨(g : MulAut V), hs.stab (fittingOf_le L g.2)⟩ ∈
      fittingOf (autSub L (commV L)) := fun g =>
    fittingOf_autSub_le hs.stab (mem_autSub.mpr ⟨⟨g, hs.stab (fittingOf_le L g.2)⟩, g.2, rfl⟩)
  let f : ↥(fittingOf L) →* ↥(fittingOf (autSub L (commV L))) :=
    { toFun := fun g => ⟨resHom (commV L) ⟨(g : MulAut V), hs.stab (fittingOf_le L g.2)⟩, hmem g⟩
      map_one' := Subtype.ext (by
        have : (⟨((1 : ↥(fittingOf L)) : MulAut V),
            hs.stab (fittingOf_le L (1 : ↥(fittingOf L)).2)⟩ : stabSub (commV L)) = 1 := rfl
        simp only [this, map_one]
        rfl)
      map_mul' := fun a b => Subtype.ext (by
        have : (⟨((a * b : ↥(fittingOf L)) : MulAut V),
            hs.stab (fittingOf_le L (a * b : ↥(fittingOf L)).2)⟩ : stabSub (commV L)) =
            ⟨(a : MulAut V), hs.stab (fittingOf_le L a.2)⟩ *
              ⟨(b : MulAut V), hs.stab (fittingOf_le L b.2)⟩ := rfl
        simp only [this, map_mul]
        rfl) }
  have hsurj : Function.Surjective f := by
    rintro ⟨ψ, hψ⟩
    have hψ' : ψ ∈ autSub (fittingOf L) (commV L) := by rw [hs.autSub_fittingOf]; exact hψ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.mp hψ'
    exact ⟨⟨(g : MulAut V), hg⟩, rfl⟩
  exact hnc (isCyclic_of_surjective f hsurj)


omit [Finite V] in
theorem conj_resHom_mem_autSub {L : Subgroup (MulAut V)} {U : Subgroup V} (hX : X ≤ stabSub U)
    (hLX : L ≤ X) (hL : NormalIn X L) {x : MulAut V} (hx : x ∈ X) {y : MulAut U}
    (hy : y ∈ autSub L U) :
    resHom U ⟨x, hX hx⟩ * y * (resHom U ⟨x, hX hx⟩)⁻¹ ∈ autSub L U := by
  obtain ⟨l, hl, rfl⟩ := mem_autSub.mp hy
  have hxl : x * (l : MulAut V) * x⁻¹ ∈ L := hL x hx l hl
  have hxlX : x * (l : MulAut V) * x⁻¹ ∈ stabSub U :=
    hX (X.mul_mem (X.mul_mem hx (hLX hl)) (X.inv_mem hx))
  refine mem_autSub.mpr ⟨⟨x * l * x⁻¹, hxlX⟩, hxl, ?_⟩
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

omit [Finite V] in
theorem resHom_mem_normalizer_autSub {L : Subgroup (MulAut V)} {U : Subgroup V}
    (hX : X ≤ stabSub U) (hLX : L ≤ X) (hL : NormalIn X L) {x : MulAut V} (hx : x ∈ X) :
    resHom U ⟨x, hX hx⟩ ∈ Subgroup.normalizer (autSub L U : Set (MulAut U)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_resHom_mem_autSub hX hLX hL hx hy, fun hy => ?_⟩
  have := conj_resHom_mem_autSub hX hLX hL (X.inv_mem hx) hy
  have e : resHom U ⟨x⁻¹, hX (X.inv_mem hx)⟩ = (resHom U ⟨x, hX hx⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e] at this
  simpa [mul_assoc] using this


end Six151c

end CFSG.Quasithin
