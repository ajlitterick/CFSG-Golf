module

public import CFSG.Quasithin.Background.B3FourData
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B3VMod

public section

namespace CFSG.KC.B3Six

open CFSG.Quasithin.B3

@[expose] def pAux : ℕ → List ℕ → List ℕ → List (List ℕ)
  | 0, _, _ => []
  | _ + 1, [], _ => []
  | f + 1, t :: ts, is =>
      List.foldr (fun y r => (List.permutationsAux2 t ts r y id).2) (pAux f ts (t :: is))
        (is :: pAux f is [])

@[expose] def permsK (l : List ℕ) : List (List ℕ) := l :: pAux (l.length ^ 2 + l.length + 1) l []


@[expose] def dedupF (seen : List Tab) : List Tab → List Tab
  | [] => []
  | x :: xs => if seen.contains x then dedupF seen xs else x :: dedupF (x :: seen) xs

@[expose] def closeTK (n : ℕ) (gens : List Tab) : List Tab := closeT n (dedupF [] gens)


@[expose] def HlX (P : List Tab) (b : Bool) : List Tab := if b then P else P.filter isEvenT

@[expose] def flagCX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool := cmask n k (HlX P b)

@[expose] def flagF1X (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool :=
  fmask n (Tgl n b) (flagCX P n k b)

@[expose] def flagF2X (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : ℕ → Bool :=
  fmask n (Tgl n b) (flagF1X P n k b)

@[expose] def flagTabsX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) :
    List Bool × List Bool × List Bool :=
  let T := Tgl n b
  let tC := tabOf n (flagCX P n k b)
  let tF1 := tabOf n (fmask n T (lkM n tC (flagCX P n k b)))
  let tF2 := tabOf n (fmask n T (lkM n tF1 (flagF1X P n k b)))
  (tC, tF1, tF2)


@[expose] def H1tabX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : List Tab :=
  let tabs := flagTabsX P n k b
  stabTab n k (HlX P b) (lkM n tabs.2.1 (flagF1X P n k b))

@[expose] def H2tabX (P : List Tab) (n : ℕ) (k : Mod) (b : Bool) : List Tab :=
  let tabs := flagTabsX P n k b
  stabTab n k (HlX P b) (lkM n tabs.2.2 (flagF2X P n k b))

@[expose] def fourDX (P : List Tab) (k : Mod) (b : Bool) : FourD :=
  let n := 6
  let T := Tgl n b
  let H1 := H1tabX P n k b
  let H2 := H2tabX P n k b
  { T := T
    H1 := H1
    H2 := H2
    R1 := rTab H1 T
    R2 := rTab H2 T
    L1 := H1.filter isEvenT
    L2T := closeTK n ((H2.filter isEvenT) ++ T)
    L1d := closeTK n (commGens (H1.filter isEvenT) (H1.filter isEvenT))
    A1p := closeT n [tab (ti n 2)]
    w := cntF n k [idT n] }


end CFSG.KC.B3Six
