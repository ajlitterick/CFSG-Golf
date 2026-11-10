module

public import CFSG.LocalAnalysis.StandardType.GGCellWitness
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95C
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGForkA8NotRefl
public import CFSG.Assembly.OpenBridges
public import CFSG.Goldschmidt.Basic
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma32
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec5Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FInputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7Interface
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux
public import CFSG.LocalAnalysis.GLTheoremA.S6.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.SignalizerFunctor
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.ComponentClassification Subgroup

@[expose] def GGReflRealizedIn {G : Type} [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G) :
    Prop :=
  ∀ t ∈ ggAutomizer X Bs, GGIsReflection p t →
    ∃ Jt : Subgroup G, t ∈ ggInduced Jt Bs ∧
      GLAPComponent p (X ⊓ centralizer (ggFixG Bs t : Set G)) Jt

theorem mem_ggFixG_of_mem_ggAutomizer {G : Type} [Group G] [Finite G] {Bs X : Subgroup G}
    {z : G} (hzBs : z ∈ Bs)
    (hXz : X ≤ centralizer ({z} : Set G)) {t : MulAut ↥Bs} (ht : t ∈ ggAutomizer X Bs) :
    z ∈ ggFixG Bs t := by
  obtain ⟨g, hgX, -, hg⟩ := mem_ggAutomizer_iff.mp ht
  have hc : g * z = z * g := mem_centralizer_singleton_iff.mp (hXz hgX)
  refine ⟨⟨z, hzBs⟩, Subtype.ext ((hg ⟨z, hzBs⟩).trans ?_), rfl⟩
  change g * z * g⁻¹ = z
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

theorem ggRealized_of_reflRealizedIn {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs X : Subgroup G} {z : G}
    (hzBs : z ∈ Bs) (hX : GLAPComponent p (centralizer ({z} : Set G)) X)
    (hR : GGReflRealizedIn p Bs X) {t : MulAut ↥Bs} (htA : t ∈ ggAutomizer X Bs)
    (ht : GGIsReflection p t) : GGRealized p Bs t := by
  obtain ⟨Jt, hind, hJ⟩ := hR t htA ht
  have hXz := ((CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    hp).mp hX).1
  have hzE := mem_ggFixG_of_mem_ggAutomizer hzBs hXz htA
  obtain ⟨hle, hpc⟩ := (CFSG.HardMathSupport.Solomon.Coordinator.i183_glaPComponent_iff_isPComponent
    hp).mp (CFSG.LocalAnalysis.GLTheoremA.S9.glaPComponent_centralizer hp hX hzE hJ)
  exact ⟨Jt, hind, hle, hpc⟩

theorem ggRealized_of_reflRealizedIn_L {G : Type} [Group G] [Finite G]
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hR : GGReflRealizedIn p Bs L)
    {t : MulAut ↥Bs} (htA : t ∈ ggAutomizer L Bs) (ht : GGIsReflection p t) :
    GGRealized p Bs t := by
  obtain ⟨hp, -, hxBs, -, -⟩ := hcfg.tableB_facts
  obtain ⟨hI, -, hDJ⟩ := hcfg
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hDJ
  obtain ⟨-, hLpc, -⟩ := eq_of_le_of_stdSub hI hDJ hpJ
  exact ggRealized_of_reflRealizedIn hp hxBs
    ((CFSG.Assembly.LargeEven.largeEvenPComponent_iff_glaPComponent p _ L).mp hLpc) hR htA ht


end CFSG.StandardType
