module

public import CFSG.ClassicalInvolution.Q3.TL3CentTwin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.Bridge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge.HasLiftTwin

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

theorem tightBelow_mono {m n : ℕ} (h : m ≤ n) (hn : TightBelow n) : TightBelow m :=
  fun Y _ _ hY R S t hd hc => hn Y (lt_of_lt_of_le hY h) R S t hd hc


theorem cit3Below_mono {m n : ℕ} (h : m ≤ n) (hn : CIT3Below n) : CIT3Below m :=
  fun Y _ _ hY Λ hΛ => hn Y (lt_of_lt_of_le hY h) Λ hΛ


end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
