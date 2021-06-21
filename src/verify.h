#include <string>

#include "fact_set.h"

namespace verify {
    std::string verify(const std::string& vars, const fact_set& facts,
            const std::string& stmt, const std::string& reason);

    std::string reason_type(const std::string& reason);
} //namespace verify
