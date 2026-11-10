module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55Comp5Split
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5L3
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5L4
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Sp4
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5U3
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5U4
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5G2
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5D4
public import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5Ree
public import CFSG.Certificates.Kernel.Spor.ONKSound
public import CFSG.ClassicalInvolution.Asc77.AscC25W15
public import CFSG.ClassicalInvolution.Models.LinearFrames.Frame
public import CFSG.ClassicalInvolution.Models.UnitaryPairs
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LieType.Steinberg.CentralExt.GriessGTwoThree
public import CFSG.LieType.Steinberg.CentralExt.GriessNativeModels
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeFrobenius
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Suz.Setup
public import CFSG.Sporadic.Suz.W64Spec

public section

namespace CFSG.OddStandard.GH71.S55

open CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

theorem comp5m2_of_comp5 {Fd : ℕ → (Y : Type) → [Group Y] → Prop} (h : Comp5 Fd) :
    Comp5m2 Fd := by
  intro r p Y _ _ hr hr2 hp hp5 hrp hY _ y g hy hE hJ
  exact h r p Y hr hr2 hp hp5 hrp hY y g hy hE hJ

theorem comp5m1_of_comp5 {Fd : ℕ → (Y : Type) → [Group Y] → Prop} (h : Comp5 Fd) :
    Comp5m1 Fd := by
  intro r p Y _ _ hr hr2 hp hp5 hrp hY _ y g hy hE hJ
  exact h r p Y hr hr2 hp hp5 hrp hY y g hy hE hJ

theorem comp5m2Types_proved : Comp5m2Types where
  l3 := comp5m2_of_comp5 comp5_fL3d
  u3 := comp5m2_of_comp5 comp5_fu3d
  sp4 := comp5m2_of_comp5 comp5_fSp4d
  g2 := comp5m2_of_comp5 comp5_fg2d
  d4 := comp5m2_of_comp5 comp5_fd4d
  l4 := comp5m2_of_comp5 comp5_fL4d
  u4 := comp5m2_of_comp5 comp5_fu4d
  ree := comp5m2_of_comp5 comp5_freed

theorem comp5m1Types_proved : Comp5m1Types where
  l3 := comp5m1_of_comp5 comp5_fL3d
  u3 := comp5m1_of_comp5 comp5_fu3d
  sp4 := comp5m1_of_comp5 comp5_fSp4d
  g2 := comp5m1_of_comp5 comp5_fg2d
  d4 := comp5m1_of_comp5 comp5_fd4d
  l4 := comp5m1_of_comp5 comp5_fL4d
  u4 := comp5m1_of_comp5 comp5_fu4d
  ree := comp5m1_of_comp5 comp5_freed

end CFSG.OddStandard.GH71.S55
