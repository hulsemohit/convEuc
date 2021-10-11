#include <fstream>
#include <string>

#include "fact_set.h"

namespace prover {

    void generate_proof(const std::string& fname);

    void proof_step(std::ifstream& in, std::ofstream& out, fact_set& facts,
                    std::string& vars);

    void by_contr(std::ifstream& in, std::ofstream& out, fact_set facts,
                  std::string vars, std::string assm);

    void by_cases(std::ifstream& in, std::ofstream& out, fact_set facts,
                  std::string vars);

}  // namespace prover
