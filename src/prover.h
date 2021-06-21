#include <string>

#include "fact_set.h"

namespace prover {

    void prove_and_generate(const std::string& fname);

    std::string by_fact(const std::string& stmt, const fact_set& facts);

    std::string by_axiom(const std::string& stmt, const std::string& ax,
            const std::string& vars, const fact_set& facts);

    std::string by_definition(const std::string& stmt, const std::string& def,
            const std::string& vars, const fact_set& facts);

    std::string by_theorem(const std::string& stmt, const std::string& th,
            const std::string& vars, const fact_set& facts);

    std::string start_contradiction();

    std::string start_cases();

    std::string translate(const std::string& stmt);

} //namespace prover
