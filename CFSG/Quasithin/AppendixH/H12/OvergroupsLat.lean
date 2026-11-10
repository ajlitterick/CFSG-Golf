module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open CFSG.QuasithinUnique.Unc25K1.Six
open Equiv

set_option maxRecDepth 200000 in
private lemma wt1t : cert.tGens[0] = evalW cert.mGens
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] := by decide
set_option maxRecDepth 200000 in
private lemma wt2t : cert.tGens[1] = evalW cert.mGens
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0] := by decide
set_option maxRecDepth 200000 in
private lemma wt3t : cert.tGens[2] = evalW cert.mGens
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] := by decide


private lemma tGens_le_Mgrp : Subgroup.closure {g | g ∈ cert.tGens} ≤ Mgrp := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk3 : k < 3 := by rw [show cert.tGens.length = 3 from rfl] at hk; exact hk
  interval_cases k
  · rw [wt1t]; exact evalW_mem_closure _ _
  · rw [wt2t]; exact evalW_mem_closure _ _
  · rw [wt3t]; exact evalW_mem_closure _ _


theorem card_Ugrp : Nat.card Ugrp = 128 := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  change Nat.card ((Subgroup.closure {g | g ∈ cert.tGens}).subgroupOf Mgrp) = 128
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tGens_le_Mgrp).toEquiv,
    cert.card_t (rawIsEnc 22) hcl hsz]
  rfl


end CFSG.Quasithin.AppendixH.H12
