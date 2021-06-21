#pragma once

#include <map>
#include <string>

#include "theorem.h"

const std::map<std::string, theorem> definitions{
#warning "Definitions aren\'t complete."
    {"collinear_f", theorem({"COABC"}, "OREQAB|EQAC|EQBC|BEBAC|BEABC|BEACB")},
    {"collinear_b", theorem({"OREQAB|EQAC|EQBC|BEBAC|BEABC|BEACB"}, "COABC")},
    // TODO more
};
