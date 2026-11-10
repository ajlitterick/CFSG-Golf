module

public import CFSG.GH74.GLS.C3.Layer2.L5Star9Inputs
meta import Mathlib.GroupTheory.SpecificGroups.Alternating
meta import CFSG.GH74.GLS.C3.Prop121.ModelFive
meta import CFSG.GH74.GLS.C3.Prop121.ModelFiveS
meta import CFSG.GH74.GLS.C3.Layer2.FinModelDefs
meta import CFSG.GH74.GLS.C3.Layer2.FinModelEmb
meta import CFSG.GH74.GLS.C3.Layer2.NumMoved
meta import CFSG.GH74.GLS.C3.Layer2.L5Fin
meta import CFSG.GH74.GLS.C3.Layer3.AltInvolutions
meta import CFSG.GH74.GLS.C3.Layer2.L5Star9Inputs

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3
open scoped Pointwise

namespace CertificateChecks.Batch5074

open CFSG
open CFSG.GH74
open CFSG.GH74.GLS
open CFSG.GH74.GLS.C3
open CFSG.GH74.GLS.C3.Layer2
open CFSG.GH74.GLS.C3.Layer2.L5
open Equiv Perm Subgroup CFSG.GH74.GLS.C3.Prop121 CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Layer3
open scoped Pointwise

set_option maxRecDepth 100000

private theorem D9list_mul_chk_0 : D9list.all (fun a => D9list.all fun b => decide (a * b ∈ D9list)) = true := by
  decide +kernel

private theorem D9list_inv_chk_1 : D9list.all (fun a => decide (a⁻¹ ∈ D9list)) = true := by
  decide +kernel

private theorem D9list_nodup_2 : D9list.Nodup := by
  decide +kernel

private theorem D9list_length_3 : D9list.length = 24 := by
  decide +kernel

private theorem D9_comm_yS_chk_4 : D9list.all (fun d => decide (d * yS = yS * d)) = true := by
  decide +kernel

private theorem D9_even_chk_5 : D9list.all (fun d => decide (sign d = 1)) = true := by
  decide +kernel

private theorem D9_inter_E9_chk_6 : D9list.all (fun d => imp (decide (d ∈ E9l)) (decide (d = 1))) = true := by
  decide +kernel

private theorem D9_norm_E9_chk_7 : D9list.all (fun d => E9l.all fun e => decide (d * e * d⁻¹ ∈ E9l)) = true := by
  decide +kernel

private theorem D9_faithful_chk_8 : D9list.all (fun d => imp (E9l.all fun e => decide (d * e = e * d))
    (decide (d = 1))) = true := by
  decide +kernel

private theorem E9_comm_yS_chk_9 : E9l.all (fun e => decide (e * yS = yS * e)) = true := by
  decide +kernel

private theorem E9_even_chk_10 : E9l.all (fun e => decide (sign e = 1)) = true := by
  decide +kernel


private theorem numMoved_yPerm9_12 : numMoved (yPerm (by norm_num : 8 ≤ 9)) = 8 := by
  decide +kernel

end CertificateChecks.Batch5074

namespace Certificates

open CertificateChecks


end Certificates
