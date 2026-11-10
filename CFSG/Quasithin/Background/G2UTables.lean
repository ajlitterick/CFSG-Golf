module

public import CFSG.Quasithin.Background.G2UClosure
public import CFSG.Quasithin.Background.G2UColumns

public section

namespace CFSG.Quasithin.G2U

open Matrix

@[expose] def cc : List ℕ :=
  mul2 (mul2 g0c g1c) (mul2 g0c g1c)

@[expose] def dc : List ℕ :=
  mul2 (mul2 g2c g3c) (mul2 g2c g3c)

@[expose] def ac : List ℕ :=
  mul2 cc cc

@[expose] def bc : List ℕ :=
  mul2 (mul2 (mul2 cc cc) cc) dc

@[expose] def Ac : List ℕ :=
  [2, 0, 0, 0, 2, 0, 0, 0, 1]

@[expose] def Bc : List ℕ :=
  [2, 7, 2, 4, 3, 1, 1, 3, 4]

@[expose] def Bic : List ℕ :=
  [2, 7, 1, 4, 6, 6, 2, 1, 7]


@[expose] def mulP (c c' : List ℕ) : List ℕ :=
  mul3 c c' ++ mul2 (c.drop 9) (c'.drop 9)

@[expose] def oneP : List ℕ :=
  id3 ++ id2

@[expose] def canonP (c : List ℕ) : Bool :=
  canon3 (c.take 9) && canon2 (c.drop 9)


@[expose] def gensR : List (List ℕ) :=
  [g0c, g1c, g2c, g3c]

@[expose] def parR : List (ℕ × ℕ) :=
  bfsParents id2 mul2 gensR 12096

@[expose] def elemsR : Array (List ℕ) :=
  build id2 mul2 gensR parR

@[expose] def gensD : List (List ℕ) :=
  [Ac ++ ac, Bc ++ bc]

@[expose] def parD : List (ℕ × ℕ) :=
  bfsParents oneP mulP gensD 6048

@[expose] def elemsD : Array (List ℕ) :=
  build oneP mulP gensD parD

@[expose] def pairOK (c : List ℕ) : Bool :=
  canonP c && (c.drop 9 == id2) == (c.take 9 == id3)

theorem pairOK_spec {c : List ℕ} (h : pairOK c = true) :
    canonP c = true ∧ (c.drop 9 = id2 ↔ c.take 9 = id3) := by
  simp only [pairOK, Bool.and_eq_true] at h
  refine ⟨h.1, ?_⟩
  rw [← beq_iff_eq (a := c.drop 9), ← beq_iff_eq (a := c.take 9), beq_iff_eq.mp h.2]

end CFSG.Quasithin.G2U
