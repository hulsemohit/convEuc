#pragma once

#include <vector>
#include <string>
#include <map>

#include "fact_set.h"

class theorem {
    public:
        const std::vector<std::string> assumptions;
        const std::string conclusion;
        static std::map<std::string, theorem> theorems;
        
    private:
        int var_cnt;
        std::vector<std::vector<std::vector<int>>> assms_pos;
        std::vector<std::vector<int>> conc_pos;
        std::string exists;
        std::vector<int> exists_pos;

        std::set<std::string> depends;

    public:
        theorem(std::vector<std::string> euc_assms = {}, std::string euc_conc = "");

        theorem instantiate(const std::string& vars) const;

        bool check_assumptions(const fact_set& facts) const;

        std::string to_string() const;

        int get_var_cnt() const;

        std::string get_exists() const;

        void add_depends(const std::string& s);
        
        std::set<std::string> get_depends() const;

        bool is_exists_pos(int p) const;
};

