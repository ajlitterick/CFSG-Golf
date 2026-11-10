module

public import CFSG.ClassicalInvolution.Q3.Q3ZAdjEval
public import CFSG.ClassicalInvolution.Q3.Q3ZMat
public import CFSG.ClassicalInvolution.Q3.Q3ZAut
public import CFSG.ClassicalInvolution.Phan.Blocks
public import CFSG.LieType.CurtisTits.SpecialLinear

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Z

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.ClassicalInvolution.WeakCT (blockSL)
open scoped MatrixGroups

theorem exists_mulEquiv_of_range_eq {H G : Type*} [Group H] [Group G] {f g : H →* G}
    (hf : Function.Injective f) (hg : Function.Injective g) (h : f.range = g.range) :
    ∃ α : H ≃* H, ∀ a, f (α a) = g a := by
  have hmem : ∀ a, g a ∈ f.range := fun a => h ▸ ⟨a, rfl⟩
  choose φ hφ using hmem
  have hφinj : Function.Injective φ := fun a b hab => hg (by rw [← hφ, ← hφ, hab])
  have hmul : ∀ a b, φ (a * b) = φ a * φ b := fun a b =>
    hf (by rw [map_mul, hφ, hφ, hφ, map_mul])
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨a, ha⟩ : f b ∈ g.range := h ▸ ⟨b, rfl⟩
    exact ⟨a, hf (by rw [hφ, ha])⟩
  exact ⟨MulEquiv.ofBijective (MonoidHom.mk' φ hmul) ⟨hφinj, hsurj⟩, hφ⟩

theorem mem_map_range {H G' G : Type*} [Group H] [Group G'] [Group G] (θ : G' →* G)
    (f : H →* G') (a : H) : θ (f a) ∈ f.range.map θ :=
  Subgroup.mem_map_of_mem θ (MonoidHom.mem_range.2 ⟨a, rfl⟩)

theorem adj_xpS_ne_one : xpS ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, ZMod 3) => (A : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1) h
  simp [coe_xpS] at this

theorem adj_autXp_eq : autXp = xpS := Subtype.ext rfl

theorem adj_autXm_eq : autXm = xmS := Subtype.ext rfl


section Assembly

variable {G : Type} [Group G]

local notation "bA0" => (blockSL (ZMod 3) 3 2 0 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "bA1" => (blockSL (ZMod 3) 3 2 1 (by omega) : SL(2, ZMod 3) →* SL(3, ZMod 3))
local notation "sB" =>
  (shortBlock (ZMod 3) (zero_ne_one : (0 : Fin 2) ≠ 1) : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB2" => (longBlock (ZMod 3) 2 1 : SL(2, ZMod 3) →* StatedSp 2 (ZMod 3))
local notation "lB3" => (longBlock (ZMod 3) 3 2 : SL(2, ZMod 3) →* StatedSp 3 (ZMod 3))


end Assembly

end CFSG.ClassicalInvolution.Q3.Q3Z
