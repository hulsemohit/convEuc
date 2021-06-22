#pragma once

#include <string>
#include <set>
#include <vector>

class fact_set {
    private:
        std::set<std::string> facts;
        std::string last;
        
    public:
        void add_fact(const std::string& fact);

        bool has_fact(const std::string& fact) const;

        std::string trace_logical(std::string fact, bool reverse = false) const;

        bool verify_facts(const std::vector<std::string>& facts) const;

        std::string find_contradiction() const;

        std::vector<std::string> all_matches(const std::string& pattern) const;

    private:
        std::string check_or(const std::string& cases) const;
};
