#include "fact_set.h"
#include "utils.h"

using std::string, std::set, std::vector;

void fact_set::add_fact(const string& fact) {
    facts.insert(fact);
}


bool fact_set::has_fact(const string& fact) const {
    return facts.find(fact) != facts.end();
}


#warning "trace_demorgan_and doesn't use de Morgans\'s law yet."
string fact_set::trace_demorgan_and(const string& fact) const {
    if(has_fact(fact))
        return fact;
    for(const string& s: facts)
        if(s.substr(0, 2) == "AN") {
            vector<string> v = utils::split_at(s.substr(2), "+");
            for(string f: v)
                if(fact == f)
                    return s;
        } /* else if(s.substr(0, 4) == "NOOR") {
            vector<string> v = utils::split_at(s.substr(4), "|");
            for(string f: v)
                if(fact == f)
                    return s;
        } */

    return "FALSE";
}


bool fact_set::verify_facts(const vector<string>& fact) const {
    for(const string& f: fact)
        if(!has_fact(f))
            return false;
    return true;
}

