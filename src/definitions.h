#pragma once

#include <map>
#include <utility>
#include <string>

#include "theorem.h"

// Each definition is an if-and-only-if statement.
// The two directions are represented by _f and _b.
const std::vector<std::pair<std::string, theorem>> def_list{

    {"collinear_f", theorem({"COABC"}, "OREQAB|EQAC|EQBC|BEBAC|BEABC|BEACB")},
    {"collinear_b", theorem({"OREQAB|EQAC|EQBC|BEBAC|BEABC|BEACB"}, "COABC")},

    {"circle_f", theorem({"NEAB"}, "CIXCAB")},
    {"circle_b", theorem({"CIXCAB"}, "NEAB")},

    {"inside_f", theorem({"CIJCAB", "ICPJ"}, "ANCIJCAB+BEXCY+EECYAB+EECXAB+BEXPY")},
    {"inside_b", theorem({"CIJCAB", "BEXCY", "EECYAB", "EECXAB", "BEXPY"}, "ANCIJCAB+ICPJ")},

    {"outside_f", theorem({"CIJCAB", "OCPJ"}, "ANCIJCAB+BECXP+EECXAB")},
    {"outside_b", theorem({"CIJCAB", "BECXP", "EECXAB"}, "ANCIJCAB+OCPJ")},

    {"on_f", theorem({"CIJACD", "ONBJ"}, "ANCIJACD+EEABCD")},
    {"on_b", theorem({"CIJACD", "EEABCD"}, "ANCIJACD+ONBJ")},

    {"equilateral_f", theorem({"ELABC"}, "ANEEABBC+EEBCCA")},
    {"equilateral_b", theorem({"EEABBC", "EEBCCA"}, "ELABC")},

    {"triangle_f", theorem({"TRABC"}, "NCABC")},
    {"triangle_b", theorem({"NCABC"}, "TRABC")},

    {"ray_f", theorem({"RAABC"}, "ANBEXAC+BEXAB")},
    {"ray_b", theorem({"BEXAC", "BEXAB"}, "RAABC")},

    {"lessthan_f", theorem({"LTABCD"}, "ANBECXD+EECXAB")},
    {"lessthan_b", theorem({"BECXD", "EECXAB"}, "LTABCD")},

    {"midpoint_f", theorem({"MIABC"}, "ANBEABC+EEABBC")},
    {"midpoint_b", theorem({"BEABC", "EEABBC"}, "MIABC")},

    {"equalangles_f", theorem({"EAABCabc"}, "ANRABAU+RABCV+RAbau+RAbcv+EEBUbu+EEBVbv+EEUVuv+NCABC")},
    {"equalangles_b", theorem({"RABAU", "RABCV", "RAbau", "RAbcv", "EEBUbu", "EEBVbv", "EEUVuv", "NCABC"}, "EAABCabc")},

    {"supplement_f", theorem({"SUABCDF"}, "ANRABCD+BEABF")},
    {"supplement_b", theorem({"RABCD", "BEABF"}, "SUABCDF")},

    {"rightangle_f", theorem({"RRABC"}, "ANBEABX+EEABXB+EEACXC+NEBC")},
    {"rightangle_b", theorem({"BEABX", "EEABXB", "EEACXC", "NEBC"}, "RRABC")},

    {"perpat_f", theorem({"PAPQABC"}, "ANCOPQC+COABC+COABX+RRXCP")},
    {"perpat_b", theorem({"COPQC", "COABC", "COABX", "RRXCP"}, "PAPQABC")},

    {"perpendicular_f", theorem({"PEPQAB"}, "PAPQABX")},
    {"perpendicular_b", theorem({"PAPQABX"}, "PEPQAB")},

    {"interior_f", theorem({"IAABCP"}, "ANRABAX+RABCY+BEXPY")},
    {"interior_b", theorem({"RABAX", "RABCY", "BEXPY"}, "IAABCP")},

    {"oppositeside_f", theorem({"OSPABQ"}, "ANBEPXQ+COABX+NCABP")},
    {"oppositeside_b", theorem({"BEPXQ", "COABX", "NCABP"}, "OSPABQ")},

    {"sameside_f", theorem({"SSPQAB"}, "ANCOABU+COABV+BEPUX+BEQVX+NCABP+NCABQ")},
    {"sameside_b", theorem({"COABU", "COABV", "BEPUX", "BEQVX", "NCABP", "NCABQ"}, "SSPQAB")},

    {"isosceles_f", theorem({"ISABC"}, "ANTRABC+EEABAC")},
    {"isosceles_b", theorem({"TRABC", "EEABAC"}, "ISABC")},

    {"cut_f", theorem({"CUABCDE"}, "ANBEAEB+BECED+NCABC+NCABD")},
    {"cut_b", theorem({"BEAEB", "BECED", "NCABC", "NCABD"}, "CUABCDE")},

    {"trianglecongruence_f", theorem({"TCABCabc"}, "ANEEABab+EEBCbc+EEACac+TRABC")},
    {"trianglecongruence_b", theorem({"EEABab", "EEBCbc", "EEACac", "TRABC"}, "TCABCabc")},

    {"anglelessthan_f", theorem({"AOABCDEF"}, "ANBEUXV+RAEDU+RAEFV+EAABCDEX")},
    {"anglelessthan_b", theorem({"BEUXV", "RAEDU", "RAEFV", "EAABCDEX"}, "AOABCDEF")},

    {"togethergreater_f", theorem({"TGABCDEF"}, "ANBEABX+EEBXCD+LTEFAX")},
    {"togethergreater_b", theorem({"BEABX", "EEBXCD", "LTEFAX"}, "TGABCDEF")},

    {"togetherfour_f", theorem({"TTABCDEFGH"}, "ANBEEFX+EEFXGH+TGABCDEX")},
    {"togetherfour_b", theorem({"BEEFX", "EEFXGH", "TGABCDEX"}, "TTABCDEFGH")},

    {"tworightangles_f", theorem({"RTABCDEF"}, "ANSUXYUVZ+EAABCXYU+EADEFVYZ")},
    {"tworightangles_b", theorem({"SUXYUVZ", "EAABCXYU", "EADEFVYZ"}, "RTABCDEF")},

    {"meet_f", theorem({"MEABCD"}, "ANNEAB+NECD+COABX+COCDX")},
    {"meet_b", theorem({"NEAB", "NECD", "COABX", "COCDX"}, "MEABCD")},

    {"cross_f", theorem({"CRABCD"}, "ANBEAXB+BECXD")},
    {"cross_b", theorem({"BEAXB", "BECXD"}, "CRABCD")},

    {"tarski_parallel_f", theorem({"TPABCD"}, "ANNEAB+NECD+NOMEABCD+SSCDAB")},
    {"tarski_parallel_b", theorem({"NEAB", "NECD", "NOMEABCD", "SSCDAB"}, "TPABCD")},

    {"parallel_f", theorem({"PRABCD"}, "ANNEAB+NECD+COABU+COABV+NEUV+COCDu+COCDv+NEuv+NOMEABCD+BEUXv+BEuXV")},
    {"parallel_b", theorem({"NEAB", "NECD", "COABU", "COABV", "NEUV", "COCDu", "COCDv", "NEuv", "NOMEABCD", "BEUXv", "BEuXV"}, "PRABCD")},

    {"anglesum_f", theorem({"ASABCDEFPQR"}, "ANEAABCPQX+EADEFXQR+BEPXR")},
    {"anglesum_b", theorem({"EAABCPQX", "EADEFXQR", "BEPXR"}, "ASABCDEFPQR")},

    {"parallelogram_f", theorem({"PGABCD"}, "ANPRABCD+PRADBC")},
    {"parallelogram_b", theorem({"PRABCD", "PRADBC"}, "PGABCD")},

    {"square_f", theorem({"SQABCD"}, "ANEEABCD+EEABBC+EEABDA+RRDAB+RRABC+RRBCD+RRCDA")},
    {"square_b", theorem({"EEABCD", "EEABBC", "EEABDA", "RRDAB", "RRABC", "RRBCD", "RRCDA"}, "SQABCD")},

    {"rectangle_f", theorem({"REABCD"}, "ANRRDAB+RRABC+RRBCD+RRCDA+CRACBD")},
    {"rectangle_b", theorem({"RRDAB", "RRABC", "RRBCD", "RRCDA", "CRACBD"}, "REABCD")},

    {"congruentrectangles_f", theorem({"RCABCDabcd"}, "ANREABCD+REabcd+EEABab+EEBCbc")},
    {"congruentrectangles_b", theorem({"REABCD", "REabcd", "EEABab", "EEBCbc"}, "RCABCDabcd")},

    {"equalrectangles_f", theorem({"ERABCDabcd"}, "ANRCABCDXYZU+RCabcdxYzu+BExYZ+BEXYz+BEWUw")},
    {"equalrectangles_b", theorem({"RCABCDXYZU", "RCabcdxYzu", "BExYZ", "BEXYz", "BEWUw"}, "ERABCDabcd")},

    {"baserectangle_f", theorem({"BRABCDE"}, "ANREBCDE+CODEA")},
    {"baserectangle_b", theorem({"REBCDE", "CODEA"}, "BRABCDE")},

    {"figurerectangle_f", theorem({"FRABCDEFGH"}, "ANREEFGH+BEEBF+BEHDG+BRCBDGF+BRABDHE")},
    {"figurerectangle_b", theorem({"REEFGH", "BEEBF", "BEHDG", "BRCBDGF", "BRABDHE"}, "FRABCDEFGH")},

    {"equaltriangles_f", theorem({"TEABCabc"}, "ANREABXY+REabxy+COXYC+COxyc+ERABXYabxy")},
    {"equaltriangles_b", theorem({"REABXY", "REabxy", "COXYC", "COxyc", "ERABXYabxy"}, "TEABCabc")},

    {"equalfigures_f", theorem({"FEABCDabcd"}, "ANOSABCD+OSabcd+FRABCDXYZU+FRabcdxyzu+ERXYZUxyzu")},
    {"equalfigures_b", theorem({"OSABCD", "OSabcd", "FRABCDXYZU", "FRabcdxyzu", "ERXYZUxyzu"}, "FEABCDabcd")},
/*
    {"equaltrianglefigure_f", theorem({"TFABCabcd"}, "ANBRABCXY+FRabcdxyzu+ERBCXYxyzu")},
    {"equaltrianglefigure_b", theorem({"BRABCXY", "FRabcdxyzu", "ERBCXYxyzu"}, "TFABCabcd")},
*/
};

const std::map<std::string, theorem> definitions(def_list.begin(), def_list.end());

