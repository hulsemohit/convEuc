#pragma once

#include <map>
#include <string>

class command {
public:
    const std::string name;
    const int arity;

public:
    command(const std::string& _name, int _arity)
        : name{_name}, arity{_arity} {};

    std::string convert(const std::string& vars) const;
};

// All Euc commands
const std::map<std::string, command> commands{
    {"BE", command{"bet", 3}},
    {"EQ", command{"eq_pnt", 2}},
    {"NE", command{"neq_pnt", 2}},
    {"CO", command{"col", 3}},
    {"NC", command{"\\<not> col", 3}},
    {"EE", command{"seg_eq", 4}},
    {"TR", command{"triangle", 3}},
    {"EA", command{"ang_eq", 6}},
    {"ON", command{"cir_on", 2}},
    {"RA", command{"ray_on", 3}},
    {"IC", command{"cir_in", 2}},
    {"OC", command{"cir_ou", 2}},
    {"CI", command{"circle", 4}},
    {"CU", command{"cuts", 5}},
    {"SU", command{"supplement", 5}},
    {"TC", command{"tri_cong", 6}},
    {"LT", command{"seg_lt", 4}},
    {"ME", command{"meets", 4}},
    {"CR", command{"cross", 4}},
    {"SS", command{"same_side", 4}},
    {"OS", command{"oppo_side", 4}},
    {"AO", command{"ang_lt", 6}},
    {"EL", command{"equilateral", 3}},
    {"RR", command{"ang_right", 3}},
    {"MI", command{"midpoint", 3}},
    {"IS", command{"tri_isos", 3}},
    {"PA", command{"perp_at", 5}},
    {"PR", command{"parallel", 4}},
    {"TP", command{"tarski_parallel", 4}},
    {"PE", command{"perp", 4}},
    {"TG", command{"seg_sum_gt", 6}},
    {"TT", command{"seg_sum_pair_gt", 8}},
    {"IA", command{"ang_in", 4}},
    {"RT", command{"ang_sum_right", 6}},
    {"AS", command{"area_sum_eq", 9}},
    {"PG", command{"parallelogram", 4}},
    {"SQ", command{"square", 4}},
    {"EF", command{"qua_eq_area", 8}},
    {"ET", command{"tri_eq_area", 6}},
    {"RE", command{"rectangle", 4}},
    {"RC", command{"rec_cong", 8}},
    {"ER", command{"rec_eq_area", 8}},
    {"TE", command{"tri_eq_area", 6}},
    {"FE", command{"qua_eq_area", 8}},
    {"BR", command{"base_rect", 5}},
    {"FR", command{"figure_rect", 8}},
};

// A map from the name of command's definition to itself.
const std::map<std::string, std::string> euc_cmd_names{
    {"unequal", "NE"},
    {"collinear", "CO"},
    {"noncollinear", "NC"},
    {"circle", "CI"},
    {"inside", "IC"},
    {"outside", "OC"},
    {"on", "ON"},
    {"equilateral", "EL"},
    {"triangle", "TR"},
    {"ray", "RA"},
    {"lessthan", "LT"},
    {"midpoint", "MI"},
    {"equalangles", "EA"},
    {"supplement", "SU"},
    {"rightangle", "RR"},
    {"perpat", "PA"},
    {"perpendicular", "PE"},
    {"interior", "IA"},
    {"oppositeside", "OS"},
    {"sameside", "SS"},
    {"isosceles", "IS"},
    {"cut", "CU"},
    {"trianglecongruence", "TC"},
    {"anglelessthan", "AO"},
    {"togethergreater", "TG"},
    {"togetherfour", "TT"},
    {"tworightangles", "RT"},
    {"meet", "ME"},
    {"cross", "CR"},
    {"tarski_parallel", "TP"},
    {"parallel", "PR"},
    {"anglesum", "AS"},
    {"parallelogram", "PG"},
    {"square", "SQ"},
    {"rectangle", "RE"},
    {"congruentrectangles", "RC"},
    {"equalrectangles", "ER"},
    {"baserectangle", "BR"},
    {"figurerectangle", "FR"},
    {"equaltriangles", "TE"},
    {"equalfigures", "EF"},
    {"equaltrianglefigure", "TF"}};
