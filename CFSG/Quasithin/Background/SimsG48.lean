module

public import CFSG.Quasithin.Background.SimsG4Defs
public import CFSG.Quasithin.Background.SimsG45Transv

public section

namespace CFSG.Quasithin.SimsG4

open LinearMap (BilinForm)

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

namespace G48


theorem exists_ne_zero_of_span (B : BilinForm F V) (hnd : ∀ x, (∀ y, B x y = 0) → x = 0)
    {I : AddSubgroup V} (hspan : Submodule.span F (I : Set V) = ⊤) {x : V} (hx0 : x ≠ 0) :
    ∃ y ∈ I, B x y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine hx0 (hnd x fun y => ?_)
  have hle : Submodule.span F (I : Set V) ≤ LinearMap.ker (B x) :=
    Submodule.span_le.mpr fun z hz => LinearMap.mem_ker.mpr (hcon z hz)
  have hy : y ∈ LinearMap.ker (B x) := hle (by rw [hspan]; exact Submodule.mem_top)
  exact LinearMap.mem_ker.mp hy

theorem eq_zero_of_forall_left (B : BilinForm F V) (halt : ∀ x, B x x = 0)
    (hnd : ∀ x, (∀ y, B x y = 0) → x = 0) {I : AddSubgroup V}
    (hspan : Submodule.span F (I : Set V) = ⊤) {x : V} (h : ∀ y ∈ I, B y x = 0) : x = 0 := by
  by_contra hx0
  obtain ⟨y, hy, hxy⟩ := exists_ne_zero_of_span B hnd hspan hx0
  apply hxy
  rw [SimsG45.bilin_skew B halt x y, h y hy, neg_zero]

theorem exists_not_mem_span_pair (hdim : Module.finrank F V = 4) {I : AddSubgroup V}
    (hspan : Submodule.span F (I : Set V) = ⊤) (p q : V) :
    ∃ z ∈ I, z ∉ Submodule.span F {p, q} := by
  classical
  by_contra hcon
  push Not at hcon
  have hle : Submodule.span F (I : Set V) ≤ Submodule.span F {p, q} :=
    Submodule.span_le.mpr fun z hz => hcon z hz
  rw [hspan] at hle
  have h1 : Module.finrank F (Submodule.span F ({p, q} : Set V)) ≤ 2 := by
    have h := finrank_span_finset_le_card (R := F) ({p, q} : Finset V)
    rw [Finset.coe_insert, Finset.coe_singleton] at h
    exact h.trans Finset.card_le_two
  have h2 : Module.finrank F (Submodule.span F ({p, q} : Set V)) = 4 := by
    rw [eq_top_iff.mpr hle, finrank_top, hdim]
  omega

theorem linearIndependent_antidiag (B₀ : BilinForm F V) {e : Fin 4 → V}
    (hb : ∀ i j, B₀ (e i) (e j) = if i.val + j.val = 3 then 1 else 0) :
    LinearIndependent F e := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have key : ∀ j, ∑ i, g i * B₀ (e i) (e j) = 0 := fun j => by
    simpa [map_sum, map_smul] using congrArg (fun x => B₀ x (e j)) hg
  fin_cases i
  · simpa [Fin.sum_univ_four, hb] using key 3
  · simpa [Fin.sum_univ_four, hb] using key 2
  · simpa [Fin.sum_univ_four, hb] using key 1
  · simpa [Fin.sum_univ_four, hb] using key 0

theorem repr_antidiag (B₀ : BilinForm F V) (b : Module.Basis (Fin 4) F V)
    (hb : ∀ i j, B₀ (b i) (b j) = if i.val + j.val = 3 then 1 else 0) (w : V) (i : Fin 4) :
    b.repr w i = B₀ (b i.rev) w := by
  conv_rhs => rw [← b.sum_repr w]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hb]
  fin_cases i <;> simp [Fin.sum_univ_four, Fin.rev]

theorem exists_antidiag_family [CharP F 2] (B₀ : BilinForm F V) (halt : ∀ x, B₀ x x = 0)
    {F₀ : Subfield F} {I : AddSubgroup V} (hsm : ∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I)
    (hval : ∀ x ∈ I, ∀ y ∈ I, B₀ x y ∈ F₀) (hnd : ∀ x ∈ I, x ≠ 0 → ∃ y ∈ I, B₀ x y ≠ 0)
    (hI0 : I ≠ ⊥) (hbig : ∀ p q : V, ∃ z ∈ I, z ∉ Submodule.span F {p, q}) :
    ∃ e : Fin 4 → V, (∀ i, e i ∈ I) ∧
      ∀ i j, B₀ (e i) (e j) = if i.val + j.val = 3 then 1 else 0 := by
  have hskew : ∀ x y, B₀ x y = - B₀ y x := SimsG45.bilin_skew B₀ halt
  have hsymm : ∀ x y, B₀ x y = B₀ y x := fun x y => by rw [hskew x y, CharTwo.neg_eq]
  obtain ⟨e₀, he₀I, he₀0⟩ : ∃ e₀ ∈ I, e₀ ≠ 0 := by
    obtain ⟨⟨x, hx⟩, hx0⟩ := AddSubgroup.ne_bot_iff_exists_ne_zero.mp hI0
    exact ⟨x, hx, fun h => hx0 (Subtype.ext h)⟩
  obtain ⟨y, hyI, hy0⟩ := hnd e₀ he₀I he₀0
  obtain ⟨e₃, he₃⟩ : ∃ e₃ : V, e₃ = (B₀ e₀ y)⁻¹ • y := ⟨_, rfl⟩
  have he₃I : e₃ ∈ I := he₃ ▸ hsm _ (F₀.inv_mem (hval e₀ he₀I y hyI)) y hyI
  have p03 : B₀ e₀ e₃ = 1 := by rw [he₃, map_smul, smul_eq_mul, inv_mul_cancel₀ hy0]
  obtain ⟨P, hP⟩ : ∃ P : V → V, ∀ w, P w = w - B₀ w e₃ • e₀ + B₀ w e₀ • e₃ :=
    ⟨_, fun _ => rfl⟩
  have hPI : ∀ w ∈ I, P w ∈ I := fun w hw => by
    rw [hP]
    exact I.add_mem (I.sub_mem hw (hsm _ (hval w hw e₃ he₃I) e₀ he₀I))
      (hsm _ (hval w hw e₀ he₀I) e₃ he₃I)
  have hP0 : ∀ w, B₀ (P w) e₀ = 0 := fun w => by
    rw [hP]
    simp only [LinearMap.map_add₂, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul, halt,
      hskew e₃ e₀, p03]
    ring
  have hP3 : ∀ w, B₀ (P w) e₃ = 0 := fun w => by
    rw [hP]
    simp only [LinearMap.map_add₂, LinearMap.map_sub₂, LinearMap.map_smul₂, smul_eq_mul, halt,
      p03]
    ring
  have hPx : ∀ x w, B₀ x e₀ = 0 → B₀ x e₃ = 0 → B₀ x (P w) = B₀ x w := fun x w h0 h3 => by
    rw [hP]
    simp only [map_add, map_sub, map_smul, smul_eq_mul, h0, h3]
    ring
  obtain ⟨z, hzI, hz⟩ := hbig e₀ e₃
  have he₁0 : P z ≠ 0 := by
    intro h
    apply hz
    have e1 : z = B₀ z e₃ • e₀ - B₀ z e₀ • e₃ + P z := by
      rw [hP]
      abel
    rw [e1, h, add_zero]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨y', hy'I, hy'0⟩ := hnd (P z) (hPI z hzI) he₁0
  have hs : B₀ (P z) (P y') = B₀ (P z) y' := hPx _ _ (hP0 z) (hP3 z)
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : V, e₂ = (B₀ (P z) y')⁻¹ • P y' := ⟨_, rfl⟩
  have he₂I : e₂ ∈ I := he₂ ▸ hsm _ (F₀.inv_mem (hval _ (hPI z hzI) y' hy'I)) _ (hPI y' hy'I)
  have p12 : B₀ (P z) e₂ = 1 := by rw [he₂, map_smul, smul_eq_mul, hs, inv_mul_cancel₀ hy'0]
  have p20 : B₀ e₂ e₀ = 0 := by
    rw [he₂, LinearMap.map_smul₂, smul_eq_mul, hP0, mul_zero]
  have p23 : B₀ e₂ e₃ = 0 := by
    rw [he₂, LinearMap.map_smul₂, smul_eq_mul, hP3, mul_zero]
  have p10 := hP0 z
  have p13 := hP3 z
  obtain ⟨e, he⟩ : ∃ e : Fin 4 → V, e = ![e₀, P z, e₂, e₃] := ⟨_, rfl⟩
  refine ⟨e, fun i => ?_, fun i j => ?_⟩
  · fin_cases i <;> simp [he, he₀I, hPI z hzI, he₂I, he₃I]
  · have p01 : B₀ e₀ (P z) = 0 := by rw [hsymm, p10]
    have p02 : B₀ e₀ e₂ = 0 := by rw [hsymm, p20]
    have p21 : B₀ e₂ (P z) = 1 := by rw [hsymm, p12]
    have p30 : B₀ e₃ e₀ = 1 := by rw [hsymm, p03]
    have p31 : B₀ e₃ (P z) = 0 := by rw [hsymm, p13]
    have p32 : B₀ e₃ e₂ = 0 := by rw [hsymm, p23]
    fin_cases i <;> fin_cases j <;>
      simp [he, halt, p01, p02, p03, p10, p12, p13, p20, p21, p23, p30, p31, p32]

theorem linearIndependent_of_subfield (F₀ : Subfield F) {I : AddSubgroup V} (B₀ : BilinForm F V)
    (hsm : ∀ c ∈ F₀, ∀ x ∈ I, c • x ∈ I) (hval : ∀ x ∈ I, ∀ y ∈ I, B₀ x y ∈ F₀)
    (hnd : ∀ x ∈ I, (∀ y ∈ I, B₀ y x = 0) → x = 0)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ i, v i ∈ I) (hli : LinearIndependent F₀ v) :
    LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff] at hli ⊢
  intro l hl i
  refine (Module.forall_dual_apply_eq_zero_iff F₀ (l i)).mp fun π => ?_
  have hw : ∑ j, π (l j) • v j = 0 := by
    refine hnd _ (AddSubgroup.sum_mem _ fun j _ => ?_) fun y hy => ?_
    · rw [Subfield.smul_def]
      exact hsm _ (π (l j)).2 _ (hv j)
    let t : ι → F₀ := fun j => ⟨B₀ y (v j), hval y hy (v j) (hv j)⟩
    have hL : B₀ y (∑ j, π (l j) • v j) = ∑ j, (π (l j) : F) * (t j : F) := by
      simp only [map_sum, Subfield.smul_def, map_smul, smul_eq_mul]
      rfl
    have hR : ((π (∑ j, t j • l j) : F₀) : F) = ∑ j, (π (l j) : F) * (t j : F) := by
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      push_cast
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h0 : ∑ j, t j • l j = 0 := by
      have e1 : ∑ j, t j • l j = B₀ y (∑ j, l j • v j) := by
        simp only [map_sum, map_smul, smul_eq_mul, Subfield.smul_def]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      rw [e1, hl, map_zero]
    rw [hL, ← hR, h0, map_zero, ZeroMemClass.coe_zero]
  exact hli _ hw i


section Descent


end Descent

section Irred


end Irred


end G48


end CFSG.Quasithin.SimsG4
