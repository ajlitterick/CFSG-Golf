module

public import CFSG.RankThree.GF2n.Smith81.S81E7Hwl
public import CFSG.RankThree.GF2n.Smith81.S81E7Lam
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe3

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits


variable {K : Type} [Field K]

theorem tor_conj_xm {t : ↥(e7Data_valid.minGroup K)} (ht : t ∈ Tor K)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ∃ s : K, s ≠ 0 ∧ ∀ c : K, t * e7Data_valid.xm K γ c * t⁻¹ = e7Data_valid.xm K γ (s * c) := by
  refine Subgroup.iSup_induction (fun i => e7Data_valid.torus K i)
    (C := fun t => ∃ s : K, s ≠ 0 ∧ ∀ c : K,
      t * e7Data_valid.xm K γ c * t⁻¹ = e7Data_valid.xm K γ (s * c)) ht ?_ ?_ ?_
  · intro i x hx
    obtain ⟨s, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
    exact ⟨((s ^ MinData.toWeight γ i : Kˣ) : K), Units.ne_zero _,
      fun c => e7Data_valid.hm_conj_xm K hγ i s c⟩
  · exact ⟨1, one_ne_zero, fun c => by simp⟩
  · rintro x y ⟨sx, hsx, hx⟩ ⟨sy, hsy, hy⟩
    refine ⟨sx * sy, mul_ne_zero hsx hsy, fun c => ?_⟩
    calc x * y * e7Data_valid.xm K γ c * (x * y)⁻¹
        = x * (y * e7Data_valid.xm K γ c * y⁻¹) * x⁻¹ := by group
      _ = x * e7Data_valid.xm K γ (sy * c) * x⁻¹ := by rw [hy c]
      _ = e7Data_valid.xm K γ (sx * (sy * c)) := hx _
      _ = e7Data_valid.xm K γ (sx * sy * c) := by rw [mul_assoc]

theorem NN_inf_GG {g : (Module.End K (V K))ˣ} (h1 : g ∈ NN K) (h2 : g ∈ GG K) : g = 1 := by
  have hR : RaisesFil (g : Module.End K (V K)) :=
    (show RaisesFil (g : Module.End K (V K)) ∧
      RaisesFil ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) from h1).1
  have hP : PresPiece (g : Module.End K (V K)) :=
    (show PresPiece (g : Module.End K (V K)) ∧
      PresPiece ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) from h2).1
  have hfix : ∀ a : Fin e7Data.d,
      (g : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single a 1 := by
    intro a
    have hs : (Finsupp.single a (1 : K) : V K) ∈ Piece K (pr a theta) := by
      refine mem_Piece_iff.2 fun b hb => ?_
      have hne : a ≠ b := fun hab => hb (by rw [hab])
      rw [Finsupp.single_apply, if_neg hne]
    have hF := hR (pr a theta) _ (piece_mem_fil hs)
    have hPg := hP (pr a theta) _ hs
    refine Finsupp.ext fun b => ?_
    by_cases hb : pr b theta = pr a theta
    · have h3 := mem_Fil_iff.1 hF b (by omega)
      rw [Finsupp.sub_apply, sub_eq_zero] at h3
      exact h3
    · rw [mem_Piece_iff.1 hPg b hb, mem_Piece_iff.1 hs b hb]
  have key : ∀ (a : Fin e7Data.d) (b : K),
      (g : Module.End K (V K)) (Finsupp.single a b) = Finsupp.single a b := by
    intro a b
    have e : (Finsupp.single a b : V K) = b • Finsupp.single a 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e, map_smul, hfix a]
  apply Units.ext
  rw [Units.val_one]
  apply Finsupp.lhom_ext
  intro a b
  rw [Module.End.one_apply]
  exact key a b


theorem Lam_le_GG [CharP K 2] : Lam K ≤ GG K := by
  rw [Lam, Subgroup.closure_le]
  rintro g ⟨β, hβ, c, rfl⟩
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  exact xu_mem_GG hβ'.1 hβ'.2 c


theorem single_mem_Piece (a : Fin e7Data.d) :
    (Finsupp.single a (1 : K) : V K) ∈ Piece K (pr a theta) := by
  refine mem_Piece_iff.2 fun b hb => ?_
  have hne : a ≠ b := fun h => hb (by rw [h])
  rw [Finsupp.single_apply, if_neg hne]


end CFSG.RankThree.GF2n.Smith81.E7Model
