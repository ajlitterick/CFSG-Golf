module

public import CFSG.Sporadic.Co2Schreier.TextCheck
public import CFSG.Sporadic.Co2Cert.Cert

public noncomputable section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Co2Cert CFSG.Monster.B.Binary.Native

structure LocalShape (L : LocalCert) : Prop where
  schema : L.schemaVersion = 1
  odd : L.alignmentOddOrders = [3, 3]
  rank : L.expectedFrattiniRank = 5
  indices : L.expectedCentralizerIndices = [56925, 1024650]
  cInit_length : L.cInitialWords.length = 2
  cInit_letters : ∀ w ∈ L.cInitialWords, lettersOK 2 w = true
  dWords_length : L.dWords.length = 2
  dWords_letters : ∀ w ∈ L.dWords, lettersOK 2 w = true
  dDeriv_length : L.dStrongDerivations.length = 5
  dDeriv_letters : extWordsOK 2 L.dStrongDerivations = true
  rWords_length : L.rWords.length = 10
  rWords_letters : ∀ w ∈ L.rWords, lettersOK 7 w = true
  z0_letters : lettersOK 2 L.cInitialCenterWord = true
  t_letters : lettersOK 2 L.dCenterWord = true
  z_letters : lettersOK 10 L.zRWord = true
  w_letters : lettersOK 2 L.alignmentIntermediateWord = true
  cDeriv_length : L.cStrongDerivations.length = 7
  cDeriv_letters : extWordsOK 2 L.cStrongDerivations = true
  qWords_length : L.qWords.length = 8
  qWords_letters : ∀ w ∈ L.qWords, lettersOK 9 w = true
  sWords_length : L.sQuotientWords.length = 7
  sWords_letters : ∀ w ∈ L.sQuotientWords, lettersOK 9 w = true
  profiles_length : L.frattiniProfiles.length = 32
  profiles_rows : ∀ r ∈ L.frattiniProfiles, r.length = 12
  chainC : ChainShape L.chains.C 2300 2 14 [0, 1, 2, 3, 4, 5]
  chainD : ChainShape L.chains.D 2300 2 12 [1, 2, 0, 3]
  chainQ : ChainShape L.chains.qAction 512 2 17 [1, 2, 3, 5, 4, 7, 8, 6]
  chainR : ChainShape L.chains.rAction 2048 2 11 [3, 1, 2, 5, 8, 7, 4]
  chainS : ChainShape L.chains.S 2300 15 23 [0, 1, 3]
  chainJoin : ChainShape L.chains.join 2300 4 17 [0, 1, 2, 3, 4, 5]

theorem localShape : LocalShape localRec := by
  have h := localShapeOK_eq_true
  simp only [localShapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, and_assoc] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, chainShape_of h25, chainShape_of h26, chainShape_of h27,
    chainShape_of h28, chainShape_of h29, chainShape_of h30⟩


@[expose] def extendTuple {G : Type*} [Group G] (gs : List G) (ds : List (List ℤ)) : List G :=
  ds.foldl (fun acc w => acc ++ [wordValue acc w]) gs

@[expose] def aSeeds : List (Equiv.Perm (Fin 2300)) := [co2Gen 0, co2Gen 1]

@[expose] def cInitTuple : List (Equiv.Perm (Fin 2300)) :=
  localRec.cInitialWords.map (wordValue aSeeds)

@[expose] def dTuple : List (Equiv.Perm (Fin 2300)) := localRec.dWords.map (wordValue aSeeds)

@[expose] def dStarTuple : List (Equiv.Perm (Fin 2300)) :=
  extendTuple dTuple localRec.dStrongDerivations

@[expose] def rTuple : List (Equiv.Perm (Fin 2300)) := localRec.rWords.map (wordValue dStarTuple)

@[expose] def locR : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ rTuple}

@[expose] def locZ0 : Equiv.Perm (Fin 2300) := wordValue cInitTuple localRec.cInitialCenterWord

@[expose] def locT : Equiv.Perm (Fin 2300) := wordValue dTuple localRec.dCenterWord

@[expose] def locZ : Equiv.Perm (Fin 2300) := wordValue rTuple localRec.zRWord

@[expose] def locW : Equiv.Perm (Fin 2300) := wordValue aSeeds localRec.alignmentIntermediateWord

@[expose] def locX : Equiv.Perm (Fin 2300) := locW * locZ0 * locW⁻¹

@[expose] def oddN1 : ℕ := localRec.alignmentOddOrders.getD 0 0

@[expose] def oddN2 : ℕ := localRec.alignmentOddOrders.getD 1 0

@[expose] def locH : Equiv.Perm (Fin 2300) :=
  (locX * locZ) ^ ((oddN2 - 1) / 2) * (locZ0 * locX) ^ ((oddN1 - 1) / 2)

@[expose] def cTuple : List (Equiv.Perm (Fin 2300)) := cInitTuple.map fun g => locH * g * locH⁻¹

@[expose] def locC : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ cTuple}

@[expose] def locD : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ dTuple}

@[expose] def cStarTuple : List (Equiv.Perm (Fin 2300)) :=
  extendTuple cTuple localRec.cStrongDerivations

@[expose] def qTuple : List (Equiv.Perm (Fin 2300)) := localRec.qWords.map (wordValue cStarTuple)

@[expose] def locQ : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ qTuple}

@[expose] def sTuple : List (Equiv.Perm (Fin 2300)) :=
  qTuple ++ localRec.sQuotientWords.map (wordValue cStarTuple)

@[expose] def locS : Subgroup (Equiv.Perm (Fin 2300)) := Subgroup.closure {g | g ∈ sTuple}

theorem records_rawOfArrays_of_shape {c : ChainRecord} {n k r : ℕ} {base : List ℕ}
    (hc : ChainShape c n k r base) (hn : 1 ≤ n) (hle : c.origArrs.size ≤ c.strongArrs.size)
    (hlt : ∀ i < c.baseArr.size, c.baseArr[i]! < n) (hnd : c.baseArr.toList.Nodup)
    (hkr : k + (r - k) = r) :
    c.Records (rawOfArrays n c.origArrs c.strongArrs c.baseArr c.wordArrs hn hle hlt hnd) := by
  have hlen : c.generators.length + c.derivations.length = c.strongGenerators.length := by
    rw [hc.gens_length, hc.derivs_length, hc.strong_length, hkr]
  refine ⟨hc.degree, hlen, ?_⟩
  exact
    { orig_size := rfl
      strong_size := rfl
      base_size := rfl
      orig := fun i => by
        rw [rawOfArrays_original_get]
        have hi : (i : ℕ) < k := by
          have := i.2
          change (i : ℕ) < c.origArrs.size at this
          rwa [hc.origArrs_size] at this
        exact (rep_permOfArr (hc.orig_inv hi)).1
      strong := fun j => by
        rw [rawOfArrays_strong_get]
        have hj : (j : ℕ) < r := by
          have := j.2
          change (j : ℕ) < c.strongArrs.size at this
          rwa [hc.strongArrs_size] at this
        exact (rep_permOfArr (hc.strong_inv hj)).1
      base_val := fun i => rawOfArrays_base_get i
      deriv := fun _ _ => rfl }

theorem baseArr_lt_of_shape {c : ChainRecord} {n k r : ℕ} {base : List ℕ}
    (hc : ChainShape c n k r base) (hb : ∀ x ∈ base, x < n) :
    ∀ i < c.baseArr.size, c.baseArr[i]! < n := by
  intro i hi
  rw [baseArr_eq, hc.base_eq] at hi ⊢
  rw [getElem!_pos _ i hi]
  exact hb _ (by simp)

theorem baseArr_nodup_of_shape {c : ChainRecord} {n k r : ℕ} {base : List ℕ}
    (hc : ChainShape c n k r base) (hb : base.Nodup) : c.baseArr.toList.Nodup := by
  rw [baseArr_eq, hc.base_eq]
  simpa using hb

@[expose] def chainC : RawSchreierDatum 2300 :=
  rawOfArrays 2300 localRec.chains.C.origArrs localRec.chains.C.strongArrs
    localRec.chains.C.baseArr localRec.chains.C.wordArrs (by norm_num)
    (by rw [localShape.chainC.origArrs_size, localShape.chainC.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape localShape.chainC (by decide))
    (baseArr_nodup_of_shape localShape.chainC (by decide))

@[expose] def chainD : RawSchreierDatum 2300 :=
  rawOfArrays 2300 localRec.chains.D.origArrs localRec.chains.D.strongArrs
    localRec.chains.D.baseArr localRec.chains.D.wordArrs (by norm_num)
    (by rw [localShape.chainD.origArrs_size, localShape.chainD.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape localShape.chainD (by decide))
    (baseArr_nodup_of_shape localShape.chainD (by decide))

@[expose] def chainS : RawSchreierDatum 2300 :=
  rawOfArrays 2300 localRec.chains.S.origArrs localRec.chains.S.strongArrs
    localRec.chains.S.baseArr localRec.chains.S.wordArrs (by norm_num)
    (by rw [localShape.chainS.origArrs_size, localShape.chainS.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape localShape.chainS (by decide))
    (baseArr_nodup_of_shape localShape.chainS (by decide))

@[expose] def chainJoin : RawSchreierDatum 2300 :=
  rawOfArrays 2300 localRec.chains.join.origArrs localRec.chains.join.strongArrs
    localRec.chains.join.baseArr localRec.chains.join.wordArrs (by norm_num)
    (by rw [localShape.chainJoin.origArrs_size, localShape.chainJoin.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape localShape.chainJoin (by decide))
    (baseArr_nodup_of_shape localShape.chainJoin (by decide))

@[expose] def chainQAction : RawSchreierDatum 512 :=
  rawOfArrays 512 localRec.chains.qAction.origArrs localRec.chains.qAction.strongArrs
    localRec.chains.qAction.baseArr localRec.chains.qAction.wordArrs (by norm_num)
    (by rw [localShape.chainQ.origArrs_size, localShape.chainQ.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape localShape.chainQ (by decide))
    (baseArr_nodup_of_shape localShape.chainQ (by decide))

@[expose] def chainRAction : RawSchreierDatum 2048 :=
  rawOfArrays 2048 localRec.chains.rAction.origArrs localRec.chains.rAction.strongArrs
    localRec.chains.rAction.baseArr localRec.chains.rAction.wordArrs (by norm_num)
    (by rw [localShape.chainR.origArrs_size, localShape.chainR.strongArrs_size]; norm_num)
    (baseArr_lt_of_shape localShape.chainR (by decide))
    (baseArr_nodup_of_shape localShape.chainR (by decide))

theorem chainC_records : localRec.chains.C.Records chainC :=
  records_rawOfArrays_of_shape localShape.chainC _ _ _ _ (by norm_num)

theorem chainD_records : localRec.chains.D.Records chainD :=
  records_rawOfArrays_of_shape localShape.chainD _ _ _ _ (by norm_num)

theorem chainS_records : localRec.chains.S.Records chainS :=
  records_rawOfArrays_of_shape localShape.chainS _ _ _ _ (by norm_num)

theorem chainJoin_records : localRec.chains.join.Records chainJoin :=
  records_rawOfArrays_of_shape localShape.chainJoin _ _ _ _ (by norm_num)

theorem chainQAction_records :
    localRec.chains.qAction.Records chainQAction :=
  records_rawOfArrays_of_shape localShape.chainQ _ _ _ _ (by norm_num)

theorem chainRAction_records :
    localRec.chains.rAction.Records chainRAction :=
  records_rawOfArrays_of_shape localShape.chainR _ _ _ _ (by norm_num)


end CFSG.Sporadic.Co2Schreier
