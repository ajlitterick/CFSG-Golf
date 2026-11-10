module

public import CFSG.Quasithin.Background.RonanH155Cls

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.Mathieu.H16Pf CFSG.Quasithin.H.ModChk CFSG.QuasithinUnique.Setup.X1
  CFSG.Quasithin.RonanH143 CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH154

@[expose] def powA24 (a : Array ℕ) : ℕ → Array ℕ
  | 0 => idA24
  | n + 1 => compA24 a (powA24 a n)

structure Alt3Data where
  l : List PG2
  si : PG2
  mO : ℕ
  hA : Array ℕ
  hI : Array ℕ
  yA : Array ℕ
  yI : Array ℕ
  mh : ℕ
  my : ℕ
  bfs : List (ℕ × ℕ × ℕ)
  w : List (PG2 × ℕ)

@[expose] def Alt3Elt (l : List PG2) (si : PG2) (gA gI : Array ℕ) : Prop :=
  InvPairOK 24 gA gI = true ∧ autArrOK gA gI = true ∧ gA[0]! = 0 ∧ gA[1]! = 1 ∧
    compA24 gA (arrP2 si) = compA24 (arrP2 si) gA ∧
    (∀ s ∈ subprods l, ∃ s' ∈ subprods l, compA24 (compA24 gA (arrP2 s)) gI = arrP2 s') ∧
    (∀ s ∈ subprods l, ∃ s' ∈ subprods l, compA24 (compA24 gI (arrP2 s)) gA = arrP2 s')

@[expose] def Alt3OK (d : Alt3Data) : Prop :=
  d.si ∈ subprods d.l ∧ (arrP2 d.si)[0]! = 1 ∧
    (maskSet d.mO).card = 8 ∧ syndM d.mO = 0 ∧
    (∀ p : Fin 24, ((arrP2 d.si)[p.val]! = p.val ↔ p ∈ maskSet d.mO)) ∧
    (0 : Fin 24) ∉ maskSet d.mO ∧
    Alt3Elt d.l d.si d.hA d.hI ∧ powA24 d.hA 7 = idA24 ∧
    d.mh ∈ fixMasks 10 actP2 d.l ∧ act10 d.hA d.mh ≠ d.mh ∧
    Alt3Elt d.l d.si d.yA d.yI ∧ compA24 d.yA d.yA = idA24 ∧
    d.my ∈ fixMasks 10 actP2 d.l ∧ act10 d.yA d.my ≠ d.my ∧
    bfsOK d.mO d.bfs = true ∧ (d.bfs.map Prod.fst).Nodup ∧ (∀ e ∈ d.bfs, e.1 < 2 ^ 24) ∧
    d.bfs.length = 330 ∧
    (fixMasks 10 actP2 d.l).length = 2 ^ 3 ∧ WitOK d.l d.w ∧ d.w.length = 10

instance (l : List PG2) (si : PG2) (gA gI : Array ℕ) : Decidable (Alt3Elt l si gA gI) := by
  unfold Alt3Elt
  infer_instance

instance (d : Alt3Data) : Decidable (Alt3OK d) := by
  unfold Alt3OK
  infer_instance


end CFSG.Quasithin.RonanH155
