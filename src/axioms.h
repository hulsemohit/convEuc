#pragma once

#include <map>
#include <string>

#include "theorem.h"

// A list of all axioms.
const std::map<std::string, theorem> axioms{
    // common notions
    {"equalitytransitive", theorem({"EQAC", "EQBC"}, "EQAB")},
    {"congruencetransitive", theorem({"EEPQBC", "EEPQDE"}, "EEBCDE")},
    {"equalityreflexive", theorem({}, "EQAA")},
    {"congruencereflexive", theorem({}, "EEABAB")},
    {"equalityreverse", theorem({}, "EEABBA")},
    {"stability", theorem({"NONEAB"}, "EQAB")},

    // axioms    
    {"betweennessidentity", theorem({}, "NOBEABA")},
    {"betweennesssymmetry", theorem({"BEABC"}, "BECBA")},
    {"innertransitivity", theorem({"BEABD", "BEBCD"}, "BEABC")},
    {"connectivity", theorem({"BEABD", "BEACD", "NOBEABC", "NOBEACB"}, "EQBC")},
    {"nullsegment1", theorem({"EEABCC"}, "EQAB")},
    {"nullsegment2", theorem({}, "EEAABB")},
    {"5-line", theorem({"EEBCbc", "EEADad", "EEBDbd", "BEABC", "BEabc", "EEABab"},
            "EEDCdc")},

    // postulates
    {"extension", theorem({"NEAB", "NECD"}, "ANBEABX+EEBXCD")},
    {"Pasch-inner", theorem({"BEAPC", "BEBQC", "NCACB"}, "ANBEAXQ+BEBXP")},
    {"Pasch-outer", theorem({"BEAPC", "BEBCQ", "NCBQA"}, "ANBEAXQ+BEBPX")},
    {"line-circle", theorem({"CIKCPQ", "ICBK", "NEAB"}, 
            "ANCOABX+COABY+ONXK+ONYK+BEXBY")},
    {"circle-circle", theorem({"CIJCRS", "ICPJ", "OCQJ", "CIKDFG", "ONPK", "ONQK"},
            "ANONXJ+ONXK")},
    {"Euclid5", theorem({"BErts", "BEptq", "BEraq", "EEptqt", "EEtrts"},
            "ANBEpaX+BEsqX")},

    // additional axioms
    {"congruentequal", theorem({"TCABCabc"}, "ETABCabc")},
    {"ETpermutation", theorem({"ETABCabc"},
            "ANETABCbca+ETABCacb+ETABCbac+ETABCcba+ETABCcab")},
    {"ETsymmetric", theorem({"ETABCabc"}, "ETabcABC")},
    {"EFpermutation", theorem({"EFABCDabcd"},
    "ANEFABCDbcda+EFABCDdcba+EFABCDcdab+EFABCDbadc+EFABCDdabc+EFABCDcbad+EFABCDadcb")},
    {"halvesofequals", theorem({"ETABCBCD", "OSABCD", "ETabcbcd",
            "OSabcd", "EFABDCabdc"}, "ETABCabc")},
    {"EFsymmetric", theorem({"EFABCDabcd"}, "EFabcdABCD")},
    {"EFtransitive", theorem({"EFABCDabcd", "EFabcdPQRS"}, "EFABCDPQRS")},
    {"ETtransitive", theorem({"ETABCabc", "ETabcPQR"}, "ETABCPQR")},
    {"cutoff1", theorem({"BEABC", "BEabc", "BEEDC", "BEedc", "ETBCDbcd", "ETACEace"},
            "EFABDEabde")},
    {"cutoff2", theorem({"BEBCD", "BEbcd", "ETCDEcde", "EFABDEabde"}, "EFABCEabce")},
    {"paste1", theorem({"BEABC", "BEabc", "BEEDC", "BEedc", "ETBCDbcd", "EFABDEabde"},
            "ETACEace")},
    {"deZolt1", theorem({"BEBED"}, "NOETDBCEBC")},
    {"deZolt2", theorem({"TRABC", "BEBEA", "BEBFC"}, "NOETABCEBF")},
    {"paste2", theorem({"BEBCD", "BEbcd", "ETCDEcde", "EFABCEabce",
            "BEAMD", "BEBME", "BEamd", "BEbme"}, "EFABDEabde")},
    {"paste3", theorem({"ETABCabc", "ETABDabd", "BECMD", "ORBEAMB|EQAM|EQMB",
            "BEcmd", "ORBEamb|EQam|EQmb"}, "EFACBDacbd")},
    {"paste4", theorem({"EFABmDFKHG", "EFDBeCGHML", "BEAPC", "BEBPD", "BEKHM",
            "BEFGL", "BEBmD", "BEBeC", "BEFJM", "BEKJL"}, "EFABCDFKML")},
};
