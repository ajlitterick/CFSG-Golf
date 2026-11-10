module

public import CFSG.LocalAnalysis.StandardType.GGDepAConfig

public import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp

public import CFSG.LocalAnalysis.StandardType.GGResIBasic

public import CFSG.LocalAnalysis.StandardType.GGK2E6E6DependentD5Span
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixModuleAux
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace E6QTwo


end E6QTwo

theorem e6_dependent_span_card_and_axis_decomposition
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [Finite V]
    {h : Fin 6 → V} {α : Fin 6 → Dual (ZMod 3) V} {y : V}
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.E 6 i j : ZMod 3))
    (hy : y ≠ 0) (hker : ∀ i, α i y = 0)
    (hdim : Module.finrank (ZMod 3) V = 6)
    (hdep : ¬ LinearIndependent (ZMod 3) h) :
    Nat.card (E6QTwo.spanH h) = 3 ^ 5 ∧ y ∉ E6QTwo.spanH h ∧
      ∀ v : V, ∃ (c : ZMod 3) (u : V), u ∈ E6QTwo.spanH h ∧ v = c • y + u := by
  classical
  let W : Submodule (ZMod 3) V :=
    Submodule.span (ZMod 3) (Set.range fun i : Fin 5 => h (d5Index i))
  obtain ⟨c, hc⟩ := e6_dependent_d5_span hpair hy hker hdim hdep
  have h0W : h 0 ∈ W := by
    rw [hc]
    exact W.sum_mem fun i _ => W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSW : E6QTwo.spanH h = W := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro v ⟨i, rfl⟩
      refine Fin.cases h0W (fun j => ?_) i
      exact Submodule.subset_span ⟨j, rfl⟩
    · apply Submodule.span_mono
      rintro v ⟨i, rfl⟩
      exact ⟨d5Index i, rfl⟩
  have hWcard : Nat.card W = 3 ^ 5 := by
    rw [E6QTwo.natCard_submodule]
    change 3 ^ Module.finrank (ZMod 3)
      (Submodule.span (ZMod 3) (Set.range fun i : Fin 5 => h (d5Index i))) = 3 ^ 5
    rw [finrank_span_eq_card (d5_roots_linearIndependent hpair), Fintype.card_fin]
  refine ⟨hSW ▸ hWcard, ?_, ?_⟩
  · rw [hSW]
    exact axis_not_mem_d5_span hpair hy hker
  · intro v
    have hLI := d5_axis_linearIndependent hpair hy hker
    have hcard : Fintype.card (Option (Fin 5)) = Module.finrank (ZMod 3) V := by
      simp [hdim]
    have hspan := hLI.span_eq_top_of_card_eq_finrank' hcard
    have hmem : v ∈ Submodule.span (ZMod 3)
        (Set.range fun o : Option (Fin 5) => o.casesOn' y (fun i => h (d5Index i))) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨d, hd⟩ := hmem
    refine ⟨d none, ∑ i : Fin 5, d (some i) • h (d5Index i), ?_, ?_⟩
    · rw [hSW]
      exact W.sum_mem fun i _ => W.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Fintype.sum_option] at hd
      simpa only [Option.casesOn'_none, Option.casesOn'_some, add_comm] using hd.symm

theorem GGResHyp.K_simple_roots_kill_y
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (hy : y ∈ Bs)
    {Γ : Type} (φ : Γ → MulAut ↥Bs) (h : Γ → V) (α : Γ → Dual (ZMod 3) V)
    (hφ : ∀ i, φ i ∈ ggAutomizer K Bs)
    (hself : ∀ i, α i (h i) = 2)
    (hlin : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i) :
    ∀ i, α i (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) = 0 := by
  obtain ⟨_, _, _, hKy, _⟩ := (hH.2.2.2.2.1.1 : LargeEvenSHat 3 B y K)
  intro i
  have hfix : φ i (⟨y, hy⟩ : ↥Bs) = ⟨y, hy⟩ :=
    ggAutomizer_apply_eq_of_le_centralizer hKy (hφ i)
  have hfixV := (ggLin_fix_iff (p := 3) ι (φ i) (⟨y, hy⟩ : ↥Bs)).mp hfix
  rw [hlin i] at hfixV
  have hzero : α i (ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs))) • h i = 0 :=
    sub_eq_self.mp hfixV
  have hne : h i ≠ 0 := by
    intro hi
    have hc := hself i
    rw [hi, map_zero] at hc
    exact (by decide : (0 : ZMod 3) ≠ 2) hc
  exact (smul_eq_zero.mp hzero).resolve_right hne

theorem e6_actual_automizer_linear_map_eq
    {G : Type} [Group G] {Bs K : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V) (φ : Fin 6 → MulAut ↥Bs)
    (h : Fin 6 → V) (α : Fin 6 → Dual (ZMod 3) V)
    (hself : ∀ i, α i (h i) = 2)
    (hlin : ∀ i w, ggLin (p := 3) ι (φ i) w = w - α i w • h i)
    (hgen : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    (ggAutomizer K Bs).map (ggLin (p := 3) ι) = E6QTwo.e6Weyl hself := by
  rw [hgen, MonoidHom.map_closure]
  unfold E6QTwo.e6Weyl
  have heq : (ggLin (p := 3) ι) '' Set.range φ =
      Set.range (fun i => Module.reflection (hself i)) := by
    ext a
    constructor
    · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      ext w
      rw [hlin i, Module.reflection_apply]
    · rintro ⟨i, rfl⟩
      refine ⟨φ i, ⟨i, rfl⟩, ?_⟩
      ext w
      rw [hlin i, Module.reflection_apply]
  rw [heq]


end CFSG.StandardType

end
