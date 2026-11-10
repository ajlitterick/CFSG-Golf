module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Gen
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Targets
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Frat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf8Cent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

theorem center_eq_bot_of_eq {M : Type*} [Group M] {H H' : Subgroup M} (h : H = H')
    (hc : Subgroup.center ↥H' = ⊥) : Subgroup.center ↥H = ⊥ := by
  subst h; exact hc

theorem center_Hn {n : ℕ} (hn : 5 ≤ n) : Subgroup.center ↥(TwinThinPf8.Hn n) = ⊥ := by
  have e : AE.aeBarOver (⊤ : Subgroup (Equiv.Perm (Fin n))) = TwinThinPf8.Hn n := by
    simp [AE.aeBarOver, AE.aeSubOver, TwinThinPf8.Hn]
  have h := TwinThinPf.center_eq_bot_of_members (A := (⊤ : Subgroup (Equiv.Perm (Fin n))))
    (𝒜 := {β : Finset (Fin n) | β.card = 4}) hn
    (fun x y hxy => by
      have hs : ({x} : Finset (Fin n)) ⊆ Finset.univ.erase y := by
        intro a ha
        rw [Finset.mem_singleton] at ha
        subst ha
        simp [hxy]
      have hc4 : 4 ≤ (Finset.univ.erase y).card := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ y)]; simp; omega
      obtain ⟨t, hxt, hty, hcard⟩ := Finset.exists_subsuperset_card_eq (n := 4) hs (by simp) hc4
      exact ⟨t, hcard, hxt (Finset.mem_singleton_self x), fun hy => by
        have := hty hy
        simp at this⟩)
    (fun β hβ => hβ)
    (fun v hv x y => by
      obtain ⟨t, hxyt, -, hcard⟩ := Finset.exists_subsuperset_card_eq (n := 4)
        (Finset.subset_univ ({x, y} : Finset (Fin n)))
        (by
          calc ({x, y} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
            _ ≤ 4 := by norm_num)
        (by simp; omega)
      exact hv t hcard x (hxyt (by simp)) y (hxyt (by simp)))
    (fun β _ hβ b => by rw [e]; exact TwinThinPf8.memBar_le_Hn β hβ b)
  rw [e] at h
  exact h

theorem comm_memBar_twin {n : ℕ} (α : Finset (Fin n)) (h : α.card = 4) :
    ∀ x ∈ AE.memBar α h true, ∀ y ∈ AE.memBar α h false, x * y = y * x := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact AE.comm_memK_memKStar (AE.emb α h) a ha b hb

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem nbrAdj_of_comm {J J' : Subgroup G} (hJ : J ∈ CoreAssembly.conjClass K₀)
    (hJ' : J' ∈ CoreAssembly.conjClass K₀) (hne : J' ≠ J) (hc : ∀ x ∈ J, ∀ y ∈ J', x * y = y * x) :
    nbrAdj (CoreAssembly.conjClass K₀) J J' := by
  refine ⟨hJ, (mem_omegaNbr_iff S.hs.hyp S.hs.two).mpr ⟨hJ', hne, fun y hy => ?_⟩⟩
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have h1 : y * x * y⁻¹ = x := by
      rw [← hc x hx y hy, mul_inv_cancel_right]
    rw [h1]
    exact hx
  · have h1 := hc _ hx y hy
    have h2 : x = y * x * y⁻¹ := by
      calc x = y⁻¹ * (y * x * y⁻¹ * y) := by group
        _ = y⁻¹ * (y * (y * x * y⁻¹)) := by rw [h1]
        _ = y * x * y⁻¹ := by group
    rw [h2]
    exact hx


end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
