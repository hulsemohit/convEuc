#pragma once

#include <map>
#include <string>

#include "theorem.h"

const std::map<std::string, theorem> axioms{
    {"equalitytransitive", theorem({"EQAC", "EQBC", "EQAB"}, "EQAB")}
    // TODO more
};
