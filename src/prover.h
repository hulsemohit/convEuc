#include <string>
#include <fstream>

#include "fact_set.h"

namespace prover {

    void generate_proof(const std::string& fname);

    std::string proof_step(std::ifstream& in, fact_set& facts, std::string& vars);

    std::string by_contr(std::ifstream& in, fact_set facts,
            std::string vars, std::string assm);

    std::string by_cases(std::ifstream& in, fact_set facts, std::string vars);
   
} // namespace prover
