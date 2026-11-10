module

public import Certificates.Data.Fi22Pump
public meta import Certificates.Data.Fi22Pump

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabFi22Small

open CFSG.RankThree.Native CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Certificates.Native CFSG.HardMathSupport.Solomon.Coordinator.Fi22Pump

set_option compiler.extract_closed false

@[expose] def hex : String := include_str "TabFi22Small.txt"

@[expose] def uArr (k : ℕ) : Array ℕ := hexTable3 3510 (3510 * k) hex


end CFSG.HardMathSupport.Dickson.I271.TabFi22Small
