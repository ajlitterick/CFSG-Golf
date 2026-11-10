module

public import Certificates.Data.Kernel.L5.HFV
public import Certificates.Data.Kernel.L5.HFQ
public import CFSG.Certificates.Kernel.L5.HFCSound

public section

namespace CFSG.Certificates.Kernel.L5H

open Equiv Perm CFSG.Certificates.Kernel.PkCV CFSG.KC.Enum CFSG.Certificates.Kernel.L5S
  CFSG.GH74.GLS.C3.Layer2.L5 CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.GH74.GLS.C3.Layer2.Model


theorem planes0_map : planes0.map List.toFinset = fam0L := rfl

theorem planes1_map : planes1.map List.toFinset = fam1L := rfl

theorem planes0_fam0 : ∀ V ∈ planes0, V.toFinset ∈ fam0 := by
  intro V hV
  rw [mem_fam0, ← planes0_map]
  exact List.mem_map_of_mem hV

theorem fam0_planes0 : ∀ F ∈ fam0, ∃ W ∈ planes0, W.toFinset = F := by
  intro F hF
  rwa [mem_fam0, ← planes0_map, List.mem_map] at hF

theorem planes1_fam1 : ∀ V ∈ planes1, V.toFinset ∈ fam1 := by
  intro V hV
  rw [mem_fam1, ← planes1_map]
  exact List.mem_map_of_mem hV

theorem fam1_planes1 : ∀ F ∈ fam1, ∃ W ∈ planes1, W.toFinset = F := by
  intro F hF
  rwa [mem_fam1, ← planes1_map, List.mem_map] at hF

end CFSG.Certificates.Kernel.L5H

end
