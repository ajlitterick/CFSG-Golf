module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusAct
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusNum

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

section Diag

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K}

@[expose] def diagChar (b : Fin D.rank → Fˣ) (γ : Fin D.rank → ℤ) : Fˣ := ∏ i, b i ^ γ i

theorem diagChar_single (b : Fin D.rank → Fˣ) (i : Fin D.rank) :
    diagChar b (Pi.single i 1) = b i := by
  rw [diagChar, Finset.prod_eq_single i]
  · simp
  · intro l _ hl
    simp [hl]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem diagChar_neg (b : Fin D.rank → Fˣ) (γ : Fin D.rank → ℤ) :
    diagChar b (-γ) = (diagChar b γ)⁻¹ := by
  simp [diagChar, zpow_neg, Finset.prod_inv_distrib]

theorem diagChar_reflection (b : Fin D.rank → Fˣ) (i : Fin D.rank) (γ : Fin D.rank → ℤ) :
    diagChar b (reflection D.cartan i γ) = diagChar b γ * b i ^ (-pair D.cartan γ i) := by
  have h : ∀ l, b l ^ (reflection D.cartan i γ) l =
      b l ^ γ l * (Pi.mulSingle i (b i ^ (-pair D.cartan γ i)) : Fin D.rank → Fˣ) l := by
    intro l
    rw [reflection_apply]
    by_cases hl : l = i
    · subst hl
      simp [pair, sub_eq_add_neg, zpow_add, zpow_neg]
    · simp [hl]
  rw [diagChar, Finset.prod_congr rfl fun l _ => h l, Finset.prod_mul_distrib,
    Finset.prod_pi_mulSingle']
  simp [diagChar]


variable {α : K →* K} {g : K} {a : Fin D.rank → Fˣ} {φ : F ≃+* F} {π : Equiv.Perm (Fin D.rank)}

theorem alpha_weylElement
    (hα₁ : ∀ i c, α (x (Pi.single i 1) c) =
      g * x (Pi.single (π i) 1) ((a (π i) : F) * φ c) * g⁻¹)
    (hα₂ : ∀ i c, α (x (-Pi.single i 1) c) =
      g * x (-Pi.single (π i) 1) ((((a (π i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹)
    (i : Fin D.rank) (t : Fˣ) :
    α (weylElement x i t) =
      g * weylElement x (π i) (a (π i) * Units.map (φ : F →+* F) t) * g⁻¹ := by
  unfold weylElement
  rw [map_mul, map_mul, hα₁, hα₂]
  have e1 : (a (π i) : F) * φ (t : F) =
      ((a (π i) * Units.map (φ : F →+* F) t : Fˣ) : F) := by simp
  have e2 : (((a (π i))⁻¹ : Fˣ) : F) * φ (-((t⁻¹ : Fˣ) : F)) =
      -(((a (π i) * Units.map (φ : F →+* F) t)⁻¹ : Fˣ) : F) := by
    simp only [map_neg]
    simp
    exact mul_comm _ _
  rw [e1, e2]
  group

theorem alpha_torusGen
    (hom : ∀ i s s', torusGen x i (s * s') = torusGen x i s * torusGen x i s')
    (hα₁ : ∀ i c, α (x (Pi.single i 1) c) =
      g * x (Pi.single (π i) 1) ((a (π i) : F) * φ c) * g⁻¹)
    (hα₂ : ∀ i c, α (x (-Pi.single i 1) c) =
      g * x (-Pi.single (π i) 1) ((((a (π i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹)
    (i : Fin D.rank) (s : Fˣ) :
    α (torusGen x i s) = g * torusGen x (π i) (Units.map (φ : F →+* F) s) * g⁻¹ := by
  have hw : ∀ (j : Fin D.rank) (u : Fˣ), weylElement x j u = torusGen x j u * weylElement x j 1 :=
    fun j u => by simp [torusGen]
  unfold torusGen
  rw [map_mul, map_inv, alpha_weylElement hα₁ hα₂, alpha_weylElement hα₁ hα₂, map_one]
  set u := a (π i) with hu
  set v : Fˣ := Units.map (φ : F →+* F) s with hv
  rw [hw (π i) (u * v), hw (π i) (u * 1)]
  have h1 : torusGen x (π i) (u * v) = torusGen x (π i) v * torusGen x (π i) u := by
    rw [mul_comm u v, hom]
  rw [mul_one, h1]
  simp only [torusGen]
  group


structure NormalForm (x : (Fin D.rank → ℤ) → F → K) (α : K →* K) (g : K)
    (a : Fin D.rank → Fˣ) (φ : F ≃+* F) (π : Equiv.Perm (Fin D.rank)) : Prop where
  pos : ∀ i c, α (x (Pi.single i 1) c) = g * x (Pi.single (π i) 1) ((a (π i) : F) * φ c) * g⁻¹
  neg : ∀ i c, α (x (-Pi.single i 1) c) =
    g * x (-Pi.single (π i) 1) ((((a (π i))⁻¹ : Fˣ) : F) * φ c) * g⁻¹

variable {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}


theorem roots_empty (hS : TorusSetup D x n H) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    γ ∈ roots D.isFiniteType ∅ := by
  rw [← hS.div]
  exact hγ


end Diag

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
