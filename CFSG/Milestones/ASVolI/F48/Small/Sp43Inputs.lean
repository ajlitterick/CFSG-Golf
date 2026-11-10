module

public import CFSG.Certificates.CosetTablePresented
public meta import CFSG.Certificates.CosetTablePresented
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Milestones.ASVolI.F48.Small.U42LetterData
public import Certificates.Data.U42F431Perm
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.ASVolI

open CFSG.CosetTable CFSG.Quasithin

@[expose] def burnsideF48s_sp43Letter (c : Char) : Fin 4 × Bool :=
  (⟨"abpq".toList.idxOf c.toLower % 4, Nat.mod_lt _ (by norm_num)⟩, c.isLower)

@[expose] def burnsideF48s_sp43Word (s : String) : List (Fin 4 × Bool) :=
  s.toList.map burnsideF48s_sp43Letter

@[expose] def burnsideF48s_sp43Words (l : List String) : List (List (Fin 4 × Bool)) :=
  l.map burnsideF48s_sp43Word

@[expose] def burnsideF48s_sp43R1S : List String :=
  ["pp", "bbb", "apAp", "aaBAbAB", "BpBpBpBp", "AABpBAAbpb", "pBABAbpBpbA"]
@[expose] def burnsideF48s_sp43R2S : List String :=
  ["bbb", "qqqq", "QQaaa", "qAQAQA", "baBabAA", "bAQBQBAA", "babaBABABABa"]
@[expose] def burnsideF48s_sp43P1Str : String :=
  " a A b B p aa ab aB ap AA Ab AB Ap ba bA bp Ba BA Bp pb pB aaa aab aaB aap aba abA abp \
    aBa aBA aBp apb apB AAb AAB AAp Aba AbA Abp ABa ABA ABp Apb ApB baa bab baB bap bAA bAb \
    bAB bAp bpb bpB Baa Bab BaB Bap BAA BAb BAB BAp Bpb BpB pba pbA pbp pBa pBA pBp aaab \
    aaaB aaap aaba aabA aabp aaBa aaBp aapb aapB abaa abab abaB abap abAb abAB abAp abpb \
    abpB aBaa aBaB aBap aBAA aBAB aBAp aBpb aBpB apba apbA apbp apBa apBA apBp AAbA AAbp \
    AABa AABA AABp AApb AApB Abaa Abap AbAA AbAb AbAp Abpb AbpB ABab ABaB ABap ABAA ABAb \
    ABAB ABAp ABpb ABpB Apba ApbA Apbp ApBa ApBA ApBp baaa baab baaB baap baba babA babp \
    baBA baBp bapb bapB bAAp bAba bAbA bAbp bABA bABp bApb bApB bpba bpbA bpbp bpBa bpBp \
    Baaa Baap Baba Babp BaBA BaBp Bapb BapB BAAB BAAp BAba BAbp BABA BABp BApb BApB BpbA \
    Bpbp BpBa BpBA BpBp pbaa pbaB pbap pbAA pbAb pbAB pbAp pbpB pBaa pBab pBaB pBap pBAA \
    pBAb pBAp pBpb aaabA aaabp aaaBa aaaBp aaapb aaapB aabaa aabab aabap aabAb aabAB aabAp \
    aabpb aabpB aaBaa aaBaB aaBap aaBpb aaBpB aapba aapbA aapbp aapBa aapBp abaab abaaB \
    abaap ababa ababA ababp abaBA abaBp abapB abAba abAbA abAbp abABA abABp abApb abApB \
    abpba abpbA abpbp abpBa abpBp aBaaa aBaap aBaBA aBaBp aBapb aBapB aBAAB aBAAp aBABA \
    aBABp aBApb aBApB aBpbA aBpbp aBpBa aBpBA aBpBp apbaa apbaB apbAb apbAB apbAp apbpB \
    apBaa apBaB apBap apBAA apBAp apBpb AAbAA AAbAb AAbAp AAbpb AAbpB AABab AABaB AABap \
    AABAA AABAp AABpb AABpB AApbA AApbp AApBa AApBA AApBp Abaaa Abaab Abaap Abapb AbapB \
    AbAAp AbAbA AbApB Abpba Abpbp AbpBa AbpBp ABaba ABabp ABaBA ABaBp ABapb ABapB ABAAB \
    ABAAp ABAba ABAbp ABABp ABApb ABpbp ABpBa ABpBp Apbaa Apbap ApbAA ApbAp ApbpB ApBab \
    ApBaB ApBap ApBAA ApBAb ApBpb baaab baaaB baaap baabA baabp baaBp baapb baapB babab \
    babaB babap babAb babAB babAp baBAA baBAB baBAp baBpb baBpB bapbA bapBa bapBA bapBp \
    bAApB bAbap bAbAp bABAb bABAB bABAp bABpB bApba bApbp bApBa bApBA bApBp bpbaB bpbap \
    bpbAB bpbAp bpBaa bpBab bpBap bpBpb Baaab BaaaB Baaap Baapb Babab BabaB Babap BaBAB \
    BaBAp BapbA BapBA BapBp BAABa BAABp BAApb BAApB BAbaa BAbap BAbpb BAbpB BABAb BABAB \
    BABAp BApba BApbA BApbp BApBa BpbAA BpbAB BpbAp BpBab BpBap BpBAp pbaaa pbaab pbaap \
    pbaBA pbaBp pbAAp pbAba pbABA pbABp pbApb pbApB pbpBa pbpBp pBaaa pBaap pBaba pBabp \
    pBaBA pBapb pBapB pBAAB pBAAp pBAba pBAbp pBpbA pBpbp aaabAb aaabAp aaabpb aaabpB aaaBaB \
    aaaBap aaaBpb aaaBpB aaapbA aaapbp aaapBa aaapBp aabaab aabaaB aabaap aababp aabapB \
    aabAba aabAbp aabABA aabABp aabApb aabApB aabpbA aabpbp aabpBp aaBaap aaBpbA aaBpbp \
    aaBpBA aaBpBp aapbaa aapbAb aapbAB aapbAp aapbpB aapBaa aapBap aapBpb abaabA abaabp \
    abaaBp abaapb abaapB ababAb ababAB ababAp abaBAA abaBAB abaBAp abapBa abapBA abAbap \
    abAbAp abABAb abABAB abABAp abABpB abApba abApbp abApBa abApBA abApBp abpbap abpbAB \
    abpbAp abpBaa abpBap aBaaab aBaaaB aBaaap aBaBAp aBapbA aBapBA aBapBp aBAABa aBAABp \
    aBAApb aBAApB aBABAb aBABAB aBABAp aBApba aBApbA aBApbp aBApBa aBpbAA aBpbAB aBpbAp \
    aBpBap aBpBAp apbaab apbaBA apbAba apbABA apbABp apbApb apbApB apbpBa apBaaa apBaap \
    apBaBA apBapb apBapB apBAAB apBAAp apBpbA AAbAAp AAbpbp AAbpBp AABabp AABapb AABAAB \
    AABAAp AABpbp AABpBp AApbAA AApbAp AApbpB AApBab AApBap AApBAA AApBpb Abaaab Abaaap \
    AbaabA Abaabp Abaapb AbaapB AbapBa AbpbaB Abpbap AbpBaa AbpBab AbpBap ABabab ABabaB \
    ABabap ABaBAB ABapBA ABapBp ABAABp ABAApB ABAbap ABApba ABpBab ABpBap Apbaaa Apbaab \
    Apbaap ApbAAp ApbpBa ApBaba ApBabp ApBapB ApBAAB ApBAba baaabp baaapb baabAB baapbp \
    babAbp babABp babApb babApB baBAAB baBAAp baBABp baBApB baBpbA bapbAB bAbapB bABAbp \
    bABpBa bABpBp bApbpB bApBaB bpbaBA bpbaBp bpbApb bpBaap bpBapB BaaaBp BaaapB BaBABp \
    BaBApb BapbAb BAApBp BAbaap BAbapb BAbpBa BApBab BpbAAp BpbApb BpBapB pbaaab pbaBAA \
    pbaBAB pbpBaa pBaaaB pBaBAB pBAbaa pBpbAA aaabpbp aaaBpBp aaapbAp aaapBap aabaabp \
    aabABAb aabABpB aabApba aabApbp aabpbAB aabpbAp aaBpbAA aaBpbAp aaBpBAp abaBAAB abABAbp \
    abpBapB aBaaaBp apBaaaB apBpbAA"
@[expose] def burnsideF48s_sp43P2Str : String :=
  " a A b B q Q aa ab aB aq aQ AA Ab AB Aq AQ ba bA bq bQ Ba BA Bq BQ qa qA qb qB qq Qa QA \
    Qb QB aab aaB aba abA abq abQ aBa aBA aBq aBQ aqa aqA aqb aqB aQa aQA aQb aQB AAb AAB \
    Aba AbA Abq AbQ ABa ABA ABq ABQ Aqa AqA Aqb AqB AQa AQA AQb AQB baa bab baB baq baQ bAA \
    bAb bAB bAq bAQ bqa bqA bqb bqB bqq bQa bQA bQb bQB Baa Bab BaB Baq BaQ BAA BAb BAB BAq \
    BAQ Bqa BqA Bqb BqB Bqq BQa BQA BQb BQB qab qaB qAb qAB qba qbA qbq qbQ qBa qBA qBq qBQ \
    qqb qqB Qab QaB QAb QAB Qba QbA Qbq QbQ QBa QBA QBq QBQ aaba aabA aabq aabQ aaBa aaBq \
    aaBQ abaa abab abaB abaq abaQ abAB abAq abAQ abqa abqA abqb abqB abqq abQa abQA abQb \
    abQB aBaa aBaB aBaq aBaQ aBAA aBAB aBAq aBqa aBqA aBqB aBqq aBQa aBQA aBQb aBQB aqab \
    aqaB aqAb aqAB aqba aqbA aqbq aqbQ aqBa aqBA aqBq aQab aQaB aQAb aQAB aQba aQbA aQbq \
    aQbQ aQBa aQBA aQBq aQBQ AAbA AAbq AAbQ AABa AABA AABq AABQ Abaa AbaQ AbAA AbAq Abqa \
    AbqA Abqb Abqq AbQa AbQA AbQb ABab ABaq ABaQ ABAA ABAb ABAB ABAQ ABqa ABqA ABqb ABqB \
    ABqq ABQa ABQA ABQb Aqab AqaB AqAb AqAB Aqba AqbA Aqbq AqbQ AqBa AqBA AqBq AqBQ AQab \
    AQaB AQAb AQAB AQba AQbA AQbQ AQBa AQBA AQBq baab baba babA babq babQ baBA baBq baqa \
    baqA baQA baQB bAbq bAqa bAqb bAQa bAQA bAQb bqab bqaB bqAb bqAB bqba bqbA bqbQ bqBA \
    bqqb bqqB bQab bQaB bQAb bQba bQbA bQbq bQbQ bQBa bQBA BaBQ Baqa BaqA BaQA BaQB BAAB \
    BABA BABq BABQ BAqa BAqb BAQa BAQA BqaB BqAb BqAB Bqba BqbA BqBA BqBq BqBQ Bqqb BqqB \
    BQab BQaB BQAb BQba BQBa BQBA qaba qabq qabQ qaBA qaBq qaBQ qbab qbaB qbaq qbAb qbAQ \
    qbqq qbQb qBaa qBaq qBAA qBAB qBAQ qBqq qqbA qqbq qqbQ qqBa qqBq qqBQ QAba QAbq QAbQ \
    QABq QABQ Qbaa Qbab Qbaq QbAA QbAQ Qbqq QBaB QBaq QBAB QBAQ QBqB QBqq aabaa aabab aabaq \
    aabAB aabAq aabqa aabqq aabQa aabQb aabQB aaBaa aaBqa aaBqB aaBqq aaBQa ababa ababA \
    ababq ababQ abaBA abaqa abaqA abaQA abAqa abAqb abAQA abqab abqAb abqAB abqba abqbA \
    abqBA abqqb abqqB abQaB abQba abQbA abQbq abQbQ abQBa abQBA aBaBQ aBaqa aBaqA aBaQA \
    aBAAB aBABA aBABq aBABQ aBqaB aBqAB aBqBA aBqBQ aBqqb aBqqB aBQab aBQaB aBQAb aBQba \
    aBQBa aBQBA aqaba aqabQ aqaBA aqaBq aqaBQ aqbab aqbaB aqbAb aqbAQ aqbqq aqbQb aqBaa \
    aqBAB aqBAQ aQbaa aQbab aQbAQ aQbqq aQBAB aQBAQ aQBqB aQBqq AAbAA AAbqA AAbqq AAbQb \
    AABab AABaQ AABAA AABAQ AABqA AABqb AABqB AABqq AABQA Abqab AbqAb Abqba AbqbA AbqbQ \
    Abqqb AbqqB AbQAb AbQba AbQbA AbQbq ABaqa ABaQA ABaQB ABABq ABABQ ABAQA ABqAb ABqba \
    ABqbA ABqBA ABqBq ABqBQ ABqqb ABqqB ABQab ABQaB ABQba Aqbab AqbaB Aqbqq AqBAB AqBqq \
    AQAba AQAbq AQAbQ AQABq AQbab AQBAB AQBqB baabA baabQ babab babaB babAq babAQ babqa \
    babqA babqB babQa babQA babQb baqab baqaB baQBA bAbqb bAqab bAqba bAqbA bAqbQ bAQAb \
    bAQAB bqaba bqabq bqbAb bqBAA bqBAQ bqqbq bqqbQ bqqBq bQbaa bQbab bQbAA bQbAQ bQbqq \
    bQBAB Baqab BaqaB BaQBa BaQBA BAABq BABAb BABAB BABqA BABQa BABQA BABQb BAqba BAQAb \
    BAQAB Bqbab BqBAA BqBqq BqqbQ BqqBq BqqBQ BQbaa BQbaq qaBqB qbaba qbAbq qbQba qbQbq \
    qbQbQ qBAAB qBABA qBABq qqbqq qqbQb qqBqq QAbQb Qbaab Qbaba QbabQ QBaBQ QBABA QBqBA \
    QBqBQ aabAqb aabqab aabqqb aabQba aaBqqB ababab ababaB ababqA ababqB ababQa ababQb \
    abaqab abaqaB abAqab abAqbQ abAQAb abAQAB abqaba abqbAb abqqbq abqqBq abQbaa abQbab \
    abQbAQ abQbqq abQBAB aBaqaB aBAABq aBABqA aBABQa aBABQA aBqqbQ aBqqBQ aqbQbq aqBABq \
    aQbaab aQbaba aQbabQ aQBABA aQBqBA aQBqBQ AAbqqb AABaQB AABqBA AABqqB Abqabq AbqbAb \
    AbqqBq ABaqab ABaqaB ABABqA ABABQa ABAQAb ABAQAB ABqbab ABqBAA ABqBqq ABqqbQ Aqbaba \
    AqBABA AqBABq AQBqBQ babAqa babAQA baqaba bAQAbQ bqbAbq bqqbqq bQbaba bQbabQ BAqbaB \
    BqqBqq qaBqBQ qbabab qBAABq QbaabQ"
@[expose] def burnsideF48s_sp43US : List String :=
  ["p", "p", "p", "p", "aaap", "aaap", "aaap", "aaap"]
@[expose] def burnsideF48s_sp43VS : List String :=
  ["q", "q", "Q", "Q", "q", "q", "Q", "Q"]
@[expose] def burnsideF48s_sp43WS : List String :=
  ["", "aaa", "", "aaa", "", "aaa", "", "aaa"]
@[expose] def burnsideF48s_sp43R1 : List (List (Fin 4 × Bool)) := burnsideF48s_sp43Words burnsideF48s_sp43R1S

@[expose] def burnsideF48s_sp43R2 : List (List (Fin 4 × Bool)) := burnsideF48s_sp43Words burnsideF48s_sp43R2S


@[expose] def burnsideF48s_sp43U : List (List (Fin 4 × Bool)) := burnsideF48s_sp43Words burnsideF48s_sp43US

@[expose] def burnsideF48s_sp43V : List (List (Fin 4 × Bool)) := burnsideF48s_sp43Words burnsideF48s_sp43VS

@[expose] def burnsideF48s_sp43W : List (List (Fin 4 × Bool)) := burnsideF48s_sp43Words burnsideF48s_sp43WS

abbrev burnsideF48s_sp43Ws (k : ℕ) : List (List (Fin 4 × Bool)) :=
  burnsideF48s_eWs burnsideF48s_sp43R1 burnsideF48s_sp43R2 4 (burnsideF48s_sp43U.getD k [])
    (burnsideF48s_sp43V.getD k []) (burnsideF48s_sp43W.getD k [])

abbrev burnsideF48s_sp43WsB (k : ℕ) : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) (burnsideF48s_sp43Ws k)


end CFSG.ASVolI
