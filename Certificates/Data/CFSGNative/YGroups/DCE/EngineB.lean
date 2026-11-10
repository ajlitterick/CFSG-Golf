module

public import Certificates.Data.CFSGNative.YGroups.DCE.PermB

public section

namespace CFSG.YGroups.DCE.B

open CFSG.Monster.B.Co2.Native CFSG.YGroups.DCE

set_option compiler.extract_closed false

structure CtxB where
  n : Nat
  letters : Array ByteArray
  cl : Nat
  N : Nat
  act : ByteArray → Nat → Nat
  actAll : ByteArray → ByteArray
  nodes : Array (Nat × Nat)
  one : ByteArray
  braid : Bool
  rels : Array (Array ByteArray × ByteArray)

@[expose] def CtxB.c (C : CtxB) : ByteArray := C.letters[C.cl]!

structure CFB where
  i : Nat
  p : Nat
  k : Nat
  a : ByteArray

@[expose] def chainStep (C : CtxB) : Option (Nat × ByteArray) → CFB × ByteArray →
    Option (Nat × ByteArray)
  | none, _ => none
  | some (i, c), (f, h) =>
    if f.i == i && f.p == C.act (bcomp C.n c h) 0 then some (f.k, bcomp C.n f.a c) else none

@[expose] def chainEnd (C : CtxB) (j₀ : Nat) (c₀ : ByteArray) (fs : List CFB)
    (hs : List ByteArray) : Option (Nat × ByteArray) :=
  (fs.zip hs).foldl (chainStep C) (some (j₀, c₀))

@[expose] def coinc (C : CtxB) (a b : ByteArray) : ByteArray := bcomp C.n b (binvCand C.n a)

structure RulesB (C : CtxB) (PE : ByteArray → Prop) (W : Nat → ByteArray → Prop)
    (V : Nat → Nat → Nat → ByteArray → Prop) : Prop where
  letter : ∀ l < C.letters.size, PE C.letters[l]!
  mul : ∀ a b, PE a → PE b → PE (bcomp C.n a b)
  inv : ∀ a, PE a → bisInv C.n a (binvCand C.n a) = true → PE (binvCand C.n a)
  wpe : ∀ j a, W j a → PE a
  vpe : ∀ i p k a, V i p k a → PE a
  wroot : ∀ a, PE a → W 0 a
  wmul : ∀ j a b, W j a → W j b → W j (bcomp C.n a b)
  winv : ∀ j a, W j a → bisInv C.n a (binvCand C.n a) = true → W j (binvCand C.n a)
  wid : ∀ j, W j C.one
  r0 : ∀ j i p, 0 < j → C.nodes[j]? = some (i, p) → p < C.N → V i p j C.one
  r1 : ∀ i p k a, V i p k a → bisInv C.n a (binvCand C.n a) = true →
    V k (C.act a p) i (binvCand C.n a)
  r2 : ∀ j p k a s q, V j p k a → W j s → q < C.N → C.act s q = p →
    V j q k (bcomp C.n a s)
  r3 : ∀ i p k a b, V i p k a → V i p k b → bisInv C.n b (binvCand C.n b) = true →
    W k (bcomp C.n a (binvCand C.n b))
  r4 : ∀ g i j k a b, C.braid = true → PE g → bisInv C.n g (binvCand C.n g) = true →
    V i (C.act g 0) j a → V j (C.act a (C.act (bcomp C.n g C.c) 0)) k b →
    V i (C.act (bcomp C.n g C.c) 0) k
      (bcomp C.n (bcomp C.n b a) (bcomp C.n (bcomp C.n g C.c) (binvCand C.n g)))
  r5 : ∀ g i j k a b, C.braid = true → PE g → bisInv C.n g (binvCand C.n g) = true →
    bisInv C.n a (binvCand C.n a) = true →
    V i (C.act g 0) j a → V i (C.act (bcomp C.n g C.c) 0) k b →
    V j (C.act a (C.act (bcomp C.n g C.c) 0)) k
      (bcomp C.n (bcomp C.n b (bcomp C.n (bcomp C.n g C.c) (binvCand C.n g)))
        (binvCand C.n a))
  r6 : ∀ r < C.rels.size, ∀ j₀ c₀ (fs : List CFB) i c, PE c₀ →
    (∀ f ∈ fs, V f.i f.p f.k f.a) → fs.length + 1 = C.rels[r]!.1.size →
    chainEnd C j₀ c₀ fs C.rels[r]!.1.toList = some (i, c) →
    bisInv C.n c (binvCand C.n c) = true →
    V i (C.act (bcomp C.n c C.rels[r]!.1[fs.length]!) 0) j₀
      (bcomp C.n (bcomp C.n c₀ C.rels[r]!.2) (binvCand C.n c))
  r7 : ∀ i p k a k' b m q c, V i p k a → V i p k' b → bisInv C.n a (binvCand C.n a) = true →
    V m q k c → V m q k' (bcomp C.n (coinc C a b) c)
  r8 : ∀ i p k a k' b s, V i p k a → V i p k' b → bisInv C.n a (binvCand C.n a) = true →
    bisInv C.n (coinc C a b) (binvCand C.n (coinc C a b)) = true → W k s →
    W k' (bcomp C.n (bcomp C.n (coinc C a b) s) (binvCand C.n (coinc C a b)))

structure EnvB where
  C : CtxB
  PE : ByteArray → Prop
  W : Nat → ByteArray → Prop
  V : Nat → Nat → Nat → ByteArray → Prop
  rules : RulesB C PE W V

abbrev PEltB (E : EnvB) : Type := {a : ByteArray // E.PE a}

abbrev WEltB (E : EnvB) : Type := {x : Nat × ByteArray // E.W x.1 x.2}

abbrev VEltB (E : EnvB) : Type := {f : CFB // E.V f.i f.p f.k f.a}

namespace EnvB

variable (E : EnvB)

@[expose] def pletter (l : Nat) : Option (PEltB E) :=
  if h : l < E.C.letters.size then some ⟨E.C.letters[l]!, E.rules.letter l h⟩ else none

@[expose] def pmul (x y : PEltB E) : PEltB E := ⟨bcomp E.C.n x.1 y.1, E.rules.mul _ _ x.2 y.2⟩

@[expose] def pinv (x : PEltB E) : Option (PEltB E) :=
  if h : bisInv E.C.n x.1 (binvCand E.C.n x.1) = true then some ⟨_, E.rules.inv _ x.2 h⟩ else none

@[expose] def wpe (x : WEltB E) : PEltB E := ⟨x.1.2, E.rules.wpe _ _ x.2⟩

@[expose] def vpe (x : VEltB E) : PEltB E := ⟨x.1.a, E.rules.vpe _ _ _ _ x.2⟩

@[expose] def wroot (x : PEltB E) : WEltB E := ⟨(0, x.1), E.rules.wroot _ x.2⟩

@[expose] def wmul (x y : WEltB E) : Option (WEltB E) :=
  if h : x.1.1 = y.1.1 then
    some ⟨(x.1.1, bcomp E.C.n x.1.2 y.1.2), E.rules.wmul _ _ _ x.2 (by rw [h]; exact y.2)⟩
  else none

@[expose] def winv (x : WEltB E) : Option (WEltB E) :=
  if h : bisInv E.C.n x.1.2 (binvCand E.C.n x.1.2) = true then
    some ⟨(x.1.1, binvCand E.C.n x.1.2), E.rules.winv _ _ x.2 h⟩
  else none

@[expose] def wid (j : Nat) : WEltB E := ⟨(j, E.C.one), E.rules.wid j⟩

@[expose] def mk0 (j : Nat) : Option (VEltB E) :=
  match h : E.C.nodes[j]? with
  | none => none
  | some (i, p) =>
    if hp : 0 < j ∧ p < E.C.N then
      some ⟨⟨i, p, j, E.C.one⟩, E.rules.r0 j i p hp.1 h hp.2⟩
    else none

@[expose] def mk1 (f : VEltB E) : Option (VEltB E) :=
  if h : bisInv E.C.n f.1.a (binvCand E.C.n f.1.a) = true then
    some ⟨⟨f.1.k, E.C.act f.1.a f.1.p, f.1.i, binvCand E.C.n f.1.a⟩, E.rules.r1 _ _ _ _ f.2 h⟩
  else none

@[expose] def mk2 (f : VEltB E) (s : WEltB E) : Option (VEltB E) :=
  let q := E.C.act (binvCand E.C.n s.1.2) f.1.p
  if h : s.1.1 = f.1.i ∧ q < E.C.N ∧ E.C.act s.1.2 q = f.1.p then
    some ⟨⟨f.1.i, q, f.1.k, bcomp E.C.n f.1.a s.1.2⟩,
      E.rules.r2 _ _ _ _ _ _ f.2 (by rw [← h.1]; exact s.2) h.2.1 h.2.2⟩
  else none

@[expose] def mk3 (f g : VEltB E) : Option (WEltB E) :=
  if h : f.1.i = g.1.i ∧ f.1.p = g.1.p ∧ f.1.k = g.1.k ∧
      bisInv E.C.n g.1.a (binvCand E.C.n g.1.a) = true then
    some ⟨(f.1.k, bcomp E.C.n f.1.a (binvCand E.C.n g.1.a)),
      E.rules.r3 f.1.i f.1.p f.1.k f.1.a g.1.a f.2
        (by rw [h.1, h.2.1, h.2.2.1]; exact g.2) h.2.2.2⟩
  else none

@[expose] def conjC (g : PEltB E) : ByteArray :=
  bcomp E.C.n (bcomp E.C.n g.1 E.C.c) (binvCand E.C.n g.1)

@[expose] def mk4 (g : PEltB E) (f f2 : VEltB E) : Option (VEltB E) :=
  if hb : E.C.braid = true then
  if h : bisInv E.C.n g.1 (binvCand E.C.n g.1) = true ∧ f.1.p = E.C.act g.1 0 ∧
      f2.1.i = f.1.k ∧
      f2.1.p = E.C.act f.1.a (E.C.act (bcomp E.C.n g.1 E.C.c) 0) then
    some ⟨⟨f.1.i, E.C.act (bcomp E.C.n g.1 E.C.c) 0, f2.1.k,
        bcomp E.C.n (bcomp E.C.n f2.1.a f.1.a) (E.conjC g)⟩,
      E.rules.r4 g.1 f.1.i f.1.k f2.1.k f.1.a f2.1.a hb g.2 h.1 (by rw [← h.2.1]; exact f.2)
        (by rw [← h.2.2.1, ← h.2.2.2]; exact f2.2)⟩
  else none
  else none

@[expose] def mk5 (g : PEltB E) (f f3 : VEltB E) : Option (VEltB E) :=
  if hb : E.C.braid = true then
  if h : bisInv E.C.n g.1 (binvCand E.C.n g.1) = true ∧
      bisInv E.C.n f.1.a (binvCand E.C.n f.1.a) = true ∧ f.1.p = E.C.act g.1 0 ∧
      f3.1.i = f.1.i ∧ f3.1.p = E.C.act (bcomp E.C.n g.1 E.C.c) 0 then
    some ⟨⟨f.1.k, E.C.act f.1.a (E.C.act (bcomp E.C.n g.1 E.C.c) 0), f3.1.k,
        bcomp E.C.n (bcomp E.C.n f3.1.a (E.conjC g)) (binvCand E.C.n f.1.a)⟩,
      E.rules.r5 g.1 f.1.i f.1.k f3.1.k f.1.a f3.1.a hb g.2 h.1 h.2.1
        (by rw [← h.2.2.1]; exact f.2) (by rw [← h.2.2.2.1, ← h.2.2.2.2]; exact f3.2)⟩
  else none
  else none

@[expose] def mk6 (r j₀ : Nat) (c₀ : PEltB E) (fs : Array (VEltB E)) : Option (VEltB E) :=
  if hr : r < E.C.rels.size then
    match hce : chainEnd E.C j₀ c₀.1 (fs.toList.map (·.1)) E.C.rels[r]!.1.toList with
    | none => none
    | some (i, c) =>
      if hc : (fs.toList.map (·.1)).length + 1 = E.C.rels[r]!.1.size ∧
          bisInv E.C.n c (binvCand E.C.n c) = true then
        some ⟨⟨i, E.C.act (bcomp E.C.n c E.C.rels[r]!.1[(fs.toList.map (·.1)).length]!) 0, j₀,
            bcomp E.C.n (bcomp E.C.n c₀.1 E.C.rels[r]!.2) (binvCand E.C.n c)⟩,
          E.rules.r6 r hr j₀ c₀.1 _ i c c₀.2
            (fun f hf => by obtain ⟨x, -, rfl⟩ := List.mem_map.1 hf; exact x.2)
            hc.1 hce hc.2⟩
      else none
  else none

@[expose] def mk7 (f g f3 : VEltB E) : Option (VEltB E) :=
  if h : f.1.i = g.1.i ∧ f.1.p = g.1.p ∧ f3.1.k = f.1.k ∧
      bisInv E.C.n f.1.a (binvCand E.C.n f.1.a) = true then
    some ⟨⟨f3.1.i, f3.1.p, g.1.k, bcomp E.C.n (coinc E.C f.1.a g.1.a) f3.1.a⟩,
      E.rules.r7 f.1.i f.1.p f.1.k f.1.a g.1.k g.1.a f3.1.i f3.1.p f3.1.a f.2
        (by rw [h.1, h.2.1]; exact g.2) h.2.2.2 (by rw [← h.2.2.1]; exact f3.2)⟩
  else none

@[expose] def mk8 (f g : VEltB E) (w : WEltB E) : Option (WEltB E) :=
  if h : f.1.i = g.1.i ∧ f.1.p = g.1.p ∧ w.1.1 = f.1.k ∧
      bisInv E.C.n f.1.a (binvCand E.C.n f.1.a) = true ∧
      bisInv E.C.n (coinc E.C f.1.a g.1.a) (binvCand E.C.n (coinc E.C f.1.a g.1.a)) = true then
    some ⟨(g.1.k, bcomp E.C.n (bcomp E.C.n (coinc E.C f.1.a g.1.a) w.1.2)
        (binvCand E.C.n (coinc E.C f.1.a g.1.a))),
      E.rules.r8 f.1.i f.1.p f.1.k f.1.a g.1.k g.1.a w.1.2 f.2
        (by rw [h.1, h.2.1]; exact g.2) h.2.2.2.1 h.2.2.2.2 (by rw [← h.2.2.1]; exact w.2)⟩
  else none

end EnvB

inductive Ins where
  | pLetter (dst l : Nat)
  | pMul (dst a b : Nat)
  | pInv (dst a : Nat)
  | pOfW (dst w : Nat)
  | pOfV (dst f : Nat)
  | wRoot (dst p : Nat)
  | wMul (dst a b : Nat)
  | wInv (dst a : Nat)
  | wId (dst j : Nat)
  | v0 (dst j : Nat)
  | v1 (dst f : Nat)
  | v2 (dst f s : Nat)
  | w3 (dst f g : Nat)
  | v4 (dst g f f2 : Nat)
  | v5 (dst g f f3 : Nat)
  | v6 (dst r j h : Nat) (fs : Array Nat)
  | v7 (dst f g f3 : Nat)
  | w8 (dst f g w : Nat)

structure RSt (E : EnvB) where
  ps : Array (Option (PEltB E))
  ws : Array (Option (WEltB E))
  vs : Array (Option (VEltB E))
  err : Nat

namespace RSt

variable {E : EnvB}

@[inline, expose] def put {α : Type} (a : Array (Option α)) (i : Nat) (x : α) : Array (Option α) :=
  if i < a.size then a.set! i (some x)
  else (a ++ Array.replicate (i + 1 - a.size) none).set! i (some x)

@[inline, expose] def get {α : Type} (a : Array (Option α)) (i : Nat) : Option α :=
  (a[i]?).getD none

@[expose] def step (st : RSt E) (ins : Ins) : RSt E :=
  if st.err != 0 then st else
  match ins with
  | .pLetter d l =>
    match E.pletter l with
    | some x => { st with ps := put st.ps d x }
    | none => { st with err := 1 }
  | .pMul d a b =>
    match get st.ps a, get st.ps b with
    | some x, some y => { st with ps := put st.ps d (E.pmul x y) }
    | _, _ => { st with err := 2 }
  | .pInv d a =>
    match (get st.ps a).bind E.pinv with
    | some y => { st with ps := put st.ps d y }
    | none => { st with err := 3 }
  | .pOfW d w =>
    match get st.ws w with
    | some x => { st with ps := put st.ps d (E.wpe x) }
    | none => { st with err := 4 }
  | .pOfV d f =>
    match get st.vs f with
    | some x => { st with ps := put st.ps d (E.vpe x) }
    | none => { st with err := 17 }
  | .wRoot d p =>
    match get st.ps p with
    | some x => { st with ws := put st.ws d (E.wroot x) }
    | none => { st with err := 5 }
  | .wMul d a b =>
    match get st.ws a, get st.ws b with
    | some x, some y =>
      match E.wmul x y with
      | some z => { st with ws := put st.ws d z }
      | none => { st with err := 6 }
    | _, _ => { st with err := 6 }
  | .wInv d a =>
    match (get st.ws a).bind E.winv with
    | some y => { st with ws := put st.ws d y }
    | none => { st with err := 7 }
  | .wId d j => { st with ws := put st.ws d (E.wid j) }
  | .v0 d j =>
    match E.mk0 j with
    | some f => { st with vs := put st.vs d f }
    | none => { st with err := 8 }
  | .v1 d f =>
    match (get st.vs f).bind E.mk1 with
    | some g => { st with vs := put st.vs d g }
    | none => { st with err := 9 }
  | .v2 d f s =>
    match get st.vs f, get st.ws s with
    | some x, some y =>
      match E.mk2 x y with
      | some z => { st with vs := put st.vs d z }
      | none => { st with err := 10 }
    | _, _ => { st with err := 10 }
  | .w3 d f g =>
    match get st.vs f, get st.vs g with
    | some x, some y =>
      match E.mk3 x y with
      | some z => { st with ws := put st.ws d z }
      | none => { st with err := 11 }
    | _, _ => { st with err := 11 }
  | .v4 d g f f2 =>
    match get st.ps g, get st.vs f, get st.vs f2 with
    | some x, some y, some z =>
      match E.mk4 x y z with
      | some w => { st with vs := put st.vs d w }
      | none => { st with err := 12 }
    | _, _, _ => { st with err := 12 }
  | .v5 d g f f3 =>
    match get st.ps g, get st.vs f, get st.vs f3 with
    | some x, some y, some z =>
      match E.mk5 x y z with
      | some w => { st with vs := put st.vs d w }
      | none => { st with err := 13 }
    | _, _, _ => { st with err := 13 }
  | .v6 d r j h fs =>
    match get st.ps h, fs.mapM (get st.vs) with
    | some x, some ys =>
      match E.mk6 r j x ys with
      | some w => { st with vs := put st.vs d w }
      | none => { st with err := 14 }
    | _, _ => { st with err := 14 }
  | .v7 d f g f3 =>
    match get st.vs f, get st.vs g, get st.vs f3 with
    | some x, some y, some z =>
      match E.mk7 x y z with
      | some w => { st with vs := put st.vs d w }
      | none => { st with err := 15 }
    | _, _, _ => { st with err := 15 }
  | .w8 d f g w =>
    match get st.vs f, get st.vs g, get st.ws w with
    | some x, some y, some z =>
      match E.mk8 x y z with
      | some u => { st with ws := put st.ws d u }
      | none => { st with err := 16 }
    | _, _, _ => { st with err := 16 }

end RSt


structure NodeFin where
  fgens : Array Nat
  cover : Array Nat
  chain : Array (Nat × Array Nat)
deriving Inhabited


@[expose] def orbitRec (n β : Nat) (sg : Array ByteArray) :
    Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let mut pos : Array Nat := (Array.replicate n n).set! β 0
  let mut tp : Array Nat := Array.replicate n n
  let mut tl : Array Nat := Array.replicate n 0
  let mut pts : Array Nat := #[β]
  let mut h := 0
  for _ in [0:n] do
    if h < pts.size then
      let x := pts[h]!
      h := h + 1
      for i in [0:sg.size] do
        let y := bget sg[i]! x
        if y < n && pos[y]! == n then
          pos := pos.set! y pts.size
          tp := tp.set! y x
          tl := tl.set! y i
          pts := pts.push y
    else
      break
  return (pts, pos, tp, tl)

namespace EnvB


end EnvB

end CFSG.YGroups.DCE.B
