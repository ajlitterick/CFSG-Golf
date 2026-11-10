module

public import CFSG.Quasithin.Background.G6PGroup
public import CFSG.Quasithin.Background.Ordering
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

@[expose] def IsQuotientOfSQTK (X : Type*) [Group X] : Prop :=
  ∃ (S : Type) (_ : Group S) (_ : Finite S), CFSG.SectionRank.IsSQTKCat S ∧
    ∃ φ : S →* X, Function.Surjective φ

namespace G6

variable {V : Type*} [CommGroup V]

@[expose] def IsHSubmodule (H : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  ∀ h ∈ H, ∀ u ∈ U, h u ∈ U

@[expose] def commOn (X : Subgroup (MulAut V)) (U : Subgroup V) : Subgroup V :=
  Subgroup.closure {w | ∃ x ∈ X, ∃ u ∈ U, x u * u⁻¹ = w}

@[expose] def submoduleClosure (X : Subgroup (MulAut V)) (W : Subgroup V) : Subgroup V :=
  ⨆ g ∈ X, W.map (g : MulAut V).toMonoidHom

@[expose] def classClosure (X : Subgroup (MulAut V)) (a : MulAut V) : Subgroup (MulAut V) :=
  conjClosure (Subgroup.zpowers a) X

theorem commV_eq_commOn_top (X : Subgroup (MulAut V)) : commV X = commOn X ⊤ := by
  unfold commV commOn
  congr 1
  ext w
  simp

theorem mem_commOn_of_mem {X : Subgroup (MulAut V)} {U : Subgroup V} {x : MulAut V} (hx : x ∈ X)
    {u : V} (hu : u ∈ U) : x u * u⁻¹ ∈ commOn X U :=
  Subgroup.subset_closure ⟨x, hx, u, hu, rfl⟩

theorem commOn_le_iff {X : Subgroup (MulAut V)} {U W : Subgroup V} :
    commOn X U ≤ W ↔ ∀ x ∈ X, ∀ u ∈ U, x u * u⁻¹ ∈ W := by
  constructor
  · intro h x hx u hu
    exact h (mem_commOn_of_mem hx hu)
  · intro h
    refine (Subgroup.closure_le _).2 ?_
    rintro w ⟨x, hx, u, hu, rfl⟩
    exact h x hx u hu

theorem commV_closure_le {S : Set (MulAut V)} {W : Subgroup V}
    (h : ∀ s ∈ S, ∀ v : V, s v * v⁻¹ ∈ W) : commV (Subgroup.closure S) ≤ W :=
  CFSG.Quasithin.FixVLat.commV_closure_le h


theorem conj_mem_classClosure {X : Subgroup (MulAut V)} {a g : MulAut V} (hg : g ∈ X) :
    g * a * g⁻¹ ∈ classClosure X a :=
  mem_conjClosure hg (Subgroup.mem_zpowers a)

theorem classClosure_le {X : Subgroup (MulAut V)} {a : MulAut V} (ha : a ∈ X) :
    classClosure X a ≤ X :=
  conjClosure_le fun _ hg _ hz =>
    X.mul_mem (X.mul_mem hg ((Subgroup.zpowers_le.2 ha) hz)) (X.inv_mem hg)

theorem conj_mem_classClosure_of_mem {X : Subgroup (MulAut V)} {a g k : MulAut V} (hg : g ∈ X)
    (hk : k ∈ classClosure X a) : g * k * g⁻¹ ∈ classClosure X a :=
  (Subgroup.mem_normalizer_iff.1 (le_normalizer_conjClosure (Subgroup.zpowers a) X hg) k).1 hk

theorem pResidual_normal_aux {Y : Type*} [Group Y] (p : ℕ) : (pResidual p Y).Normal := by
  refine ⟨fun n hn g => ?_⟩
  simp only [pResidual, Subgroup.mem_iInf] at hn ⊢
  intro N hN hp
  exact hN.conj_mem n (hn N hN hp) g

theorem exists_pow_mem_pResidual {Y : Type*} [Group Y] [Finite Y] (p : ℕ) (y : Y) :
    ∃ m : ℕ, y ^ p ^ m ∈ pResidual p Y := by
  classical
  set 𝒮 : Set (Subgroup Y) := {N | N.Normal ∧ ∀ x : Y, ∃ k : ℕ, x ^ p ^ k ∈ N} with h𝒮
  have htop : (⊤ : Subgroup Y) ∈ 𝒮 := ⟨inferInstance, fun x => ⟨0, trivial⟩⟩
  obtain ⟨N₀, hN₀, hmin⟩ := (wellFounded_lt (α := Subgroup Y)).has_min 𝒮 ⟨⊤, htop⟩
  have hnorm : N₀.Normal := hN₀.1
  have hle : pResidual p Y ≤ N₀ := pResidual_le hN₀.2
  have hge : N₀ ≤ pResidual p Y := by
    refine le_iInf fun N => le_iInf fun hN => le_iInf fun hp => ?_
    have hmem : N ⊓ N₀ ∈ 𝒮 := by
      refine ⟨inferInstance, fun x => ?_⟩
      obtain ⟨k₁, hk₁⟩ := hp x
      obtain ⟨k₂, hk₂⟩ := hN₀.2 x
      refine ⟨k₁ + k₂, Subgroup.mem_inf.2 ⟨?_, ?_⟩⟩
      · rw [pow_add, pow_mul]
        exact N.pow_mem hk₁ _
      · rw [pow_add, mul_comm, pow_mul]
        exact N₀.pow_mem hk₂ _
    have heq : N ⊓ N₀ = N₀ := by
      by_contra hne
      exact hmin _ hmem (lt_of_le_of_ne inf_le_right hne)
    calc N₀ = N ⊓ N₀ := heq.symm
      _ ≤ N := inf_le_left
  obtain ⟨m, hm⟩ := hN₀.2 y
  exact ⟨m, (le_antisymm hle hge).symm ▸ hm⟩

structure Hypothesis61 [Finite V] (X : Subgroup (MulAut V)) (a : MulAut V) : Prop where
  sq_eq_one : ∀ v : V, v ^ 2 = 1
  pCoreOf_eq_bot : pCoreOf 2 X = ⊥
  isQuotientOfSQTK : IsQuotientOfSQTK X
  mem : a ∈ X
  ne_one : a ≠ 1
  mul_self : a * a = 1
  card_commV_le : Nat.card (commV (Subgroup.zpowers a)) ≤ 4
  span : submoduleClosure X (commV (Subgroup.zpowers a)) = ⊤

variable {X : Subgroup (MulAut V)} {a : MulAut V}

theorem lemma_G62_1 [Finite V] (h : Hypothesis61 X a) : commV (classClosure X a) = ⊤ := by
  rw [eq_top_iff, ← h.span]
  refine iSup₂_le fun g hg => ?_
  rw [Subgroup.map_le_iff_le_comap, commV_le_iff]
  intro x hx v
  rw [Subgroup.mem_comap]
  have h1 := mem_commV_of_mem (X := classClosure X a) (mem_conjClosure hg hx) (g v)
  have h2 : (g * x * g⁻¹) (g v) * (g v)⁻¹ = g (x v * v⁻¹) := by simp
  rw [h2] at h1
  exact h1


end G6

end CFSG.Quasithin
