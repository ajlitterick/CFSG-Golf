module

public import Certificates.Data.ONanCMRels
public import CFSG.Certificates.CosetTablePresented
public import Mathlib

public section

namespace CFSG.OddStandard.ONanRec.CM

open CFSG.CosetTable

abbrev cmChain1 := restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) cmRelWords
abbrev cmChain2 := restrictWords (subsetOf _ [0, 1, 2, 4]) cmChain1
abbrev cmChain3 := restrictWords (subsetOf _ [0, 1, 2]) cmChain2
abbrev cmChain4 := restrictWords (subsetOf _ [0, 1]) cmChain3
abbrev cmChain5 := restrictWords (subsetOf _ [0]) cmChain4


end CFSG.OddStandard.ONanRec.CM
