module

public import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import CFSG.Monster.Existence.StdOdd.Defs
public meta import CFSG.LieType.Chevalley.C2E6StdMatrixModel
public import Certificates.Certificate6036
public import CFSG.Monster.GMS.Facts.TableV

public section

namespace CFSG.Monster.Existence.StdOdd.Cert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LieType.Chevalley.C2E6Std CFSG.LieType.Chevalley.C2E6Std.MatrixModel
  CFSG.Sporadic.Bridge CFSG.Sporadic.Bridge.TwoGen

@[expose] noncomputable def repOf
    (v : List (ℕ × Bool)) : Rgrp := wordProd (img2 stdA stdB) v

@[expose] noncomputable def rep5 :
    Rgrp := repOf repWord5

@[expose] noncomputable def rep7A :
    Rgrp := repOf repWord7A

@[expose] noncomputable def rep7B :
    Rgrp := repOf repWord7B

@[expose] noncomputable def rep11 :
    Rgrp := repOf repWord11

@[expose] noncomputable def rep13 :
    Rgrp := repOf repWord13

@[expose] noncomputable def rep17 :
    Rgrp := repOf repWord17

@[expose] noncomputable def rep19 :
    Rgrp := repOf repWord19

theorem coe_repOf
    (v : List (ℕ × Bool)) :
    ((repOf v : Rgrp) : ModGL Tag.E6 K) = wordProd (img2 genA genB) v := by
  rw [repOf, coe_wordProd, img2_stdA_stdB]

theorem orderOf_repOf
    (v : List (ℕ × Bool)) {p : ℕ} [Fact p.Prime]
    (h : Native.ordP (Native.wordMat nativeAB.1 nativeAB.2 v) p = true) :
    orderOf (repOf v) = p := by
  rw [← Subgroup.orderOf_coe, coe_repOf]
  exact orderOf_wordProd v h

theorem orderOf_rep5 :
    orderOf rep5 = 5 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  orderOf_repOf _ Certificates.certificate6036.1

theorem orderOf_rep7A :
    orderOf rep7A = 7 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_repOf _ Certificates.certificate6036.2.1

theorem orderOf_rep7B :
    orderOf rep7B = 7 :=
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  orderOf_repOf _ Certificates.certificate6036.2.2.1

theorem orderOf_rep11 :
    orderOf rep11 = 11 :=
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  orderOf_repOf _ Certificates.certificate6036.2.2.2.1

theorem orderOf_rep13 :
    orderOf rep13 = 13 :=
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  orderOf_repOf _ Certificates.certificate6036.2.2.2.2.1

theorem orderOf_rep17 :
    orderOf rep17 = 17 :=
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  orderOf_repOf _ Certificates.certificate6036.2.2.2.2.2.1

theorem orderOf_rep19 :
    orderOf rep19 = 19 :=
  have : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  orderOf_repOf _ Certificates.certificate6036.2.2.2.2.2.2

end CFSG.Monster.Existence.StdOdd.Cert
