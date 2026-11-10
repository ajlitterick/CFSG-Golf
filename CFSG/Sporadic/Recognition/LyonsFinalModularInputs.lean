module

public import CFSG.Sporadic.Recognition.LyonsFinalBInputs
public import CFSG.CosetTable.HintedColumns

public section

namespace CFSG.Sporadic.Recognition.LyonsSims.LyFinal

open CFSG.CosetTable

@[expose] def modularLearnedStrings : List String :=
  ["DaDaDacbdcdcda", "DaDaDaDaDaDa", "Dacdebcbebcbeb", "DbDbDbcdbdaedb", "DbdbeaeDbdbeae",
   "DbDbDbDbDbDb", "DbDcbeaebDbecec", "DbDecaeDbececec", "DaDcDadceDb", "DaeDbdbDcDc",
   "DbDecbeaebDbcec", "DbDbDbeDbdacb", "acbceacbebcaecbc", "DaebeaeDecedbdac",
   "DbaDbaDbaDbaDbcdba", "Dbeaedeacecacece", "DaDcbebDececbca", "DaDedacacacacadb", "DDcabDcae",
   "DacbedaedeDeaDebdb", "DadacbedececaDca", "DabDecDbDabDecDb", "DabDbebadbDbDbabaDba",
   "DaDbdcdbdaDc", "DaedeceDebDecDb", "DaDaebecebeadadebe", "DbDbdeacbdea", "DaDceaedeaceDeDca",
   "DaeDbcdcdc", "DaeDbDebDbdeaec", "DacbDbDbaeDbdba", "DbDbecdbdabDcedb", "DaDecbdeaDeDc",
   "DbcdeDbcde", "DabaDcbeceadeDebcaba", "DaDbcDaDcdc", "DabdbDeaeDbeaDc", "DabdbcaDcDceaDc",
   "DaDacbDbeDbda", "DbcdaeDbcdce", "DaDcdeacecDbDabca", "DDeacbebDededbedea", "DDeadbdecb",
   "DcdacDecdb", "DaeadbabeDaeadbabe", "DaeaedbDbDbeaDc", "Dbdacaebeaebceca",
   "DaDaDeadceDebcbeb", "DabdeaDcDaeDc", "DaceDbdbDceDc", "DaDcbdecdc", "DaDeDbcbc",
   "DabcadaDcDceaDc", "DaDbDbdeaDc", "DacDebDbdeaDb", "DbaDcbeDbaceaebea", "DbcaDcDceaDbdac",
   "DabeDbdacbDbeDc", "DbacDeabdedc", "DDedadcbcb", "DaDadcDcDbc", "DacDeadbde"]

@[expose] def modularLearned : List (List (Fin 6 × Bool)) := modularLearnedStrings.map parseWord

@[expose] def modularE : List (List (Fin 6 × Bool)) :=
  ["kckabDebcdaDababeDea", "kdeDcbkadabededeceadbaD", "kdbedeaekadbceacbcbcbcaDec",
   "kaeabebekDeacedbeabDbdc"].map parseWord

@[expose] def modularD1 : List (List (Fin 6 × Bool)) :=
  ["kbkekbkebebe", "kbkbebkbkbeb", "kbkdeDcbckbkabacacecacabaeae",
   "kbkbabaeakbkebeabaeabebe"].map parseWord

@[expose] def modularD2 : List (List (Fin 6 × Bool)) :=
  ["kdkebcacbekDkbabaDbcebabaDebD", "kdkDceacaecdkDkcaDcDbedabDbDbe",
   "kdkabdbecabakDkbaeDcbcaebacaeb", "kdkabDeDeaebckDkebcdecbceadceab"].map parseWord

@[expose] def modularD3 : List (List (Fin 6 × Bool)) :=
  ["kDbkcbaDbecebdabckbdkedbabaedaDeababDe", "kDbkcbaDbedeDcbebdabckbdkaDebaceaDeDceabe",
   "kDbkcbaDbeadbDaebdabckbdkdeacbacbacebadaea"].map parseWord

@[expose] def modularD : List (List (Fin 6 × Bool)) := modularD1 ++ modularD2 ++ modularD3

@[expose] def modularR (Rc RD : List (List (Fin 6 × Bool))) : List (List (Fin 6 × Bool)) :=
  Rc ++ modularLearned ++ RD


end CFSG.Sporadic.Recognition.LyonsSims.LyFinal
