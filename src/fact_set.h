#pragma once

#include <string>
#include <set>
#include <vector>

class fact_set {
    private:
        std::set<std::string> facts;
        
    public:
        void add_fact(const std::string& fact);

        bool has_fact(const std::string& fact) const;

        std::string trace_demorgan_and(const std::string& fact) const;

        bool verify_facts(const std::vector<std::string>& facts) const;
};
