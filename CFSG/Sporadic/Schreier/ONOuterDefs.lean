module

public import CFSG.Sporadic.Schreier.ONSchreierData
public import CFSG.Sporadic.Schreier.ONOuterData
public import CFSG.Sporadic.Schreier.ONArrayDatum
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public noncomputable section

namespace CFSG.ONSchreier

open CFSG.Sporadic.ON CFSG.Certificates CFSG.ComponentClassification

@[expose] def evalS
    (w : List ℤ) : Equiv.Perm (Fin N) :=
  Quiver.SchreierGraph.evalWord (fun h : Fin 7 => sgen h) (ptoLetters 7 w)

@[expose] def evalList
    (ws : Array (List ℤ)) : List (Equiv.Perm (Fin N)) := ws.toList.map evalS

theorem evalS_mem
    (w : List ℤ) : evalS w ∈ Pv := by
  apply (Subgroup.closure_le _).2 ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ _)
  rintro _ ⟨h, rfl⟩
  exact sgen_mem h.val

theorem evalList_mem
    {ws : Array (List ℤ)} {g : Equiv.Perm (Fin N)} (hg : g ∈ evalList ws) :
    g ∈ Pv := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
  exact evalS_mem w

theorem closure_evalList_le
    (ws : Array (List ℤ)) :
    Subgroup.closure {g | g ∈ evalList ws} ≤ Pv :=
  (Subgroup.closure_le _).2 fun _ hg => evalList_mem hg

@[expose] def onTgens :
    List (Equiv.Perm (Fin N)) := evalList Data.TWords

@[expose] def onMgens :
    List (Equiv.Perm (Fin N)) := evalList Data.MWords

@[expose] def onLgens :
    List (Equiv.Perm (Fin N)) := evalList Data.LWords

@[expose] def onDgens :
    List (Equiv.Perm (Fin N)) := evalList Data.intersectionWords

@[expose] def onT :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.closure {g | g ∈ onTgens}

@[expose] def onM :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.closure {g | g ∈ onMgens}

@[expose] def onL :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.closure {g | g ∈ onLgens}

@[expose] def onD0 :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.closure {g | g ∈ onDgens}

@[expose] def onz :
    Equiv.Perm (Fin N) := evalS Data.zWord

@[expose] def onq :
    Equiv.Perm (Fin N) := evalS Data.centerGeneratorWord

@[expose] def ont :
    Equiv.Perm (Fin N) := evalS Data.tWord

@[expose] def onc :
    Equiv.Perm (Fin N) := evalS Data.pairConjugatorWord

@[expose] def onQ :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.zpowers onq

@[expose] def onM1 :
    Subgroup (Equiv.Perm (Fin N)) := onM.map (MulAut.conj onc).toMonoidHom

@[expose] def onWMgens :
    List (Equiv.Perm (Fin N)) :=
  Data.MCommutatorSpecs.toList.map (commSpec onMgens)

@[expose] def onWLgens :
    List (Equiv.Perm (Fin N)) :=
  Data.LCommutatorSpecs.toList.map (commSpec onLgens)

@[expose] def onWM :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.closure {g | g ∈ onWMgens}

@[expose] def onWL :
    Subgroup (Equiv.Perm (Fin N)) := Subgroup.closure {g | g ∈ onWLgens}

@[expose] def onJgens :
    List (Equiv.Perm (Fin N)) := onMgens ++ onMgens.map fun g => onc * g * onc⁻¹

@[expose] def ptN (b : ℕ) : Fin N := ⟨b % N, Nat.mod_lt _ (by norm_num)⟩

@[expose] def bigBase (ch : Data.BigChain) : List (Fin N) := ch.base.toList.map ptN

@[expose] def bigChain (ch : Data.BigChain) (orig : List (Equiv.Perm (Fin N)))
    (hk : orig.length ≤ ch.strongWords.size) (hb : (bigBase ch).Nodup) : RawSchreierDatum N :=
  RawSchreierDatum.ofWords N (by norm_num) orig ch.strongWords hk (bigBase ch) hb

@[expose] def base3 : List (Fin N) :=
  [⟨0, by norm_num⟩, ⟨227759, by norm_num⟩, ⟨100817, by norm_num⟩]

theorem base3_nodup : base3.Nodup := by decide

theorem bigBase_T : bigBase Data.TChain = base3 := by decide
theorem bigBase_M : bigBase Data.MChain = base3 := by decide
theorem bigBase_L : bigBase Data.LChain = base3 := by decide
theorem bigBase_Mcomm : bigBase Data.McommChain = base3 := by decide
theorem bigBase_Lcomm : bigBase Data.LcommChain = base3 := by decide
theorem bigBase_joint : bigBase Data.jointChain = base3 := by decide

@[expose] def onTChain :
    RawSchreierDatum N :=
  bigChain Data.TChain onTgens (by simp [onTgens, evalList]; decide)
    (bigBase_T ▸ base3_nodup)

@[expose] def onMChain :
    RawSchreierDatum N :=
  bigChain Data.MChain onMgens (by simp [onMgens, evalList]; decide)
    (bigBase_M ▸ base3_nodup)

@[expose] def onLChain :
    RawSchreierDatum N :=
  bigChain Data.LChain onLgens (by simp [onLgens, evalList]; decide)
    (bigBase_L ▸ base3_nodup)

@[expose] def onMcommChain :
    RawSchreierDatum N :=
  bigChain Data.McommChain onWMgens (by simp [onWMgens]; decide)
    (bigBase_Mcomm ▸ base3_nodup)

@[expose] def onLcommChain :
    RawSchreierDatum N :=
  bigChain Data.LcommChain onWLgens (by simp [onWLgens]; decide)
    (bigBase_Lcomm ▸ base3_nodup)

@[expose] def onJointChain :
    RawSchreierDatum N :=
  bigChain Data.jointChain onJgens (by simp [onJgens, onMgens, evalList]; decide)
    (bigBase_joint ▸ base3_nodup)

@[expose] def smallBase (n : ℕ) (hn : 0 < n) (ch : Data.SmallChain) : List (Fin n) :=
  ch.base.toList.map fun b => ⟨b % n, Nat.mod_lt _ hn⟩

@[expose] def smallChain (n : ℕ) (hn : 0 < n) (ch : Data.SmallChain)
    (hk : ch.generators.size ≤ ch.strongGenerators.size) (hb : (smallBase n hn ch).Nodup) :
    RawSchreierDatum n :=
  RawSchreierDatum.ofArrays n hn ch.generators ch.strongGenerators hk (smallBase n hn ch) hb
    ch.derivations

@[expose] def onT32Chain : RawSchreierDatum 32 :=
  smallChain 32 (by norm_num) Data.T32Chain (by decide) (by decide)

@[expose] def onM120Chain : RawSchreierDatum 120 :=
  smallChain 120 (by norm_num) Data.M120Chain (by decide) (by decide)

@[expose] def onL120Chain : RawSchreierDatum 120 :=
  smallChain 120 (by norm_num) Data.L120Chain (by decide) (by decide)

@[expose] def onPSL21Chain : RawSchreierDatum 21 :=
  smallChain 21 (by norm_num) Data.PSL21Chain (by decide) (by decide)

@[expose] def onPSL120Chain : RawSchreierDatum 120 :=
  smallChain 120 (by norm_num) Data.PSL120Chain (by decide) (by decide)

@[expose] def onX : Subgroup (Equiv.Perm (Fin 120)) := onPSL120Chain.originalSubgroup

@[expose] def onR : List (Fin N) := Data.TPoints.toList.map ptN

@[expose] def onB : List (List (Fin N)) := Data.quotientBlocks.toList.map fun b => b.toList.map ptN

@[expose] def onu : Equiv.Perm (Fin 120) := permOfArr 120 Data.quotientConjugator

@[expose] def onz32 : Equiv.Perm (Fin 32) := permOfArr 32 Data.T32z


@[expose] def codeF4 (c : ℕ) : PSL3Four.F4 := ⟨⟨c % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def vecOfCodes (v : Array ℕ) : PSL3Four.Vec := ![codeF4 v[0]!, codeF4 v[1]!, codeF4 v[2]!]

@[expose] def onTargetVecs : List PSL3Four.Vec := Data.targetPoints.toList.map vecOfCodes

@[expose] def pt21 (i : ℕ) : Fin 21 := ⟨i % 21, Nat.mod_lt _ (by norm_num)⟩

@[expose] def onFanoBlocks : List (Finset (Fin 21)) :=
  Data.targetFanoBlocks.toList.map fun b => (b.toList.map pt21).toFinset

@[expose] def elemSL (i j : Fin 3) (h : i ≠ j) (a : PSL3Four.F4) :
    Matrix.SpecialLinearGroup (Fin 3) PSL3Four.F4 :=
  ⟨Matrix.transvection i j a, Matrix.det_transvection_of_ne i j h a⟩

@[expose] def onElems : List (Matrix.SpecialLinearGroup (Fin 3) PSL3Four.F4) :=
  [elemSL 0 1 (by decide) 1, elemSL 0 1 (by decide) PSL3Four.F4.ω,
    elemSL 0 2 (by decide) 1, elemSL 0 2 (by decide) PSL3Four.F4.ω,
    elemSL 1 0 (by decide) 1, elemSL 1 0 (by decide) PSL3Four.F4.ω,
    elemSL 1 2 (by decide) 1, elemSL 1 2 (by decide) PSL3Four.F4.ω,
    elemSL 2 0 (by decide) 1, elemSL 2 0 (by decide) PSL3Four.F4.ω,
    elemSL 2 1 (by decide) 1, elemSL 2 1 (by decide) PSL3Four.F4.ω]

@[expose] def onU : Subgroup (Matrix.SpecialLinearGroup (Fin 3) PSL3Four.F4) :=
  Subgroup.closure {g | g ∈ onElems}


end CFSG.ONSchreier
