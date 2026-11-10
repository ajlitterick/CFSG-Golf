module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreePrimeCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Quot
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedOrbitsAux
public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {A : Type} [Group A] [Finite A] {p : ℕ}


theorem commutator_mem_centralizer_of_isCyclic {G : Type*} [Group G] {U : Subgroup G} [U.Normal]
    [IsCyclic U] (g h : G) : g * h * g⁻¹ * h⁻¹ ∈ centralizer (U : Set G) := by
  set φ : G →* MulAut U := MulAut.conjNormal
  set e := IsCyclic.mulAutMulEquiv U
  have hcomm : φ g * φ h = φ h * φ g := e.injective (by rw [map_mul, map_mul, mul_comm])
  have h1 : φ (g * h * g⁻¹ * h⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  rw [mem_centralizer_iff]
  intro u hu
  have h2 := congrArg (fun f : MulAut U => ((f ⟨u, hu⟩ : U) : G)) h1
  simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc u * (g * h * g⁻¹ * h⁻¹) = (g * h * g⁻¹ * h⁻¹) * u * (g * h * g⁻¹ * h⁻¹)⁻¹ *
        (g * h * g⁻¹ * h⁻¹) := by rw [h2]
    _ = (g * h * g⁻¹ * h⁻¹) * u := by group


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free
