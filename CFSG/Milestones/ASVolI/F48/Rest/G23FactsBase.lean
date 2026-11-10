
module

public import Certificates.Certificate7762
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

@[expose] public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates

attribute [local irreducible] burnsideF48t_g23LArr burnsideF48t_g23Tau burnsideF48t_g23GensArr
  burnsideF48t_g23PtsStr


section Letters

theorem burnsideF48t_g23_X_eq : burnsideF48t_g23X =
    Subgroup.closure (Set.range fun k : Fin 4 => burnsideF48t_g23γ k) :=
  Certificates.certificate7762.1

theorem burnsideF48t_g23_γ_mem {i : ℕ} (hi : i < 4) : burnsideF48t_g23γ i ∈ burnsideF48t_g23X := by
  rw [burnsideF48t_g23_X_eq]
  exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩


end Letters

end CFSG.ASVolI
