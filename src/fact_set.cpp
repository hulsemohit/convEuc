#include "fact_set.h"
#include "utils.h"
#include "parse.h"

#include <algorithm>

using std::string, std::set, std::vector;

// Adds a new fact to the set of facts.
void fact_set::add_fact(const string& fact) {
    facts.insert(fact);
    last = fact;
    vars += parse::get_vars(fact);
    utils::unique(vars);
}

// Check if a literal fact exists.
bool fact_set::has_fact(const string& fact) const {
    return facts.find(fact) != facts.end();
}

bool fact_set::has_var(char v) const {
    return vars.find(string(1, v)) != string::npos;
}

// Check if the pattern matches the fact.
// '?'s in the pattern match with any point.
bool matches(const string& fact, const string& pattern) {
    if(fact.size() != pattern.size())
        return false;
    for(int i{}; i < fact.size(); ++i)
        if(pattern[i] != '?' && fact[i] != pattern[i])
            return false;
    return true;
}

// Verifies a fact (pattern) taking into account de Morgan's law, as well as
// and/or clauses.
// If the fact is logically equivalent to an already proven fact F,
// it returns F. Returns "FALSE" otherwise. 
// If the fact is a conjunction, it returns a list of facts seprated by spaces,
// for each clause.
string fact_set::trace_logical(string fact, bool reverse) const {
    fact = parse::canonical(fact);

    for(string t: facts) {
        string s = parse::canonical(t);
        if(reverse ? matches(fact, s) : matches(s, fact))
            return t;
        if(s.substr(0, 2) == "AN") {
            vector<string> v = utils::split_at(s.substr(2), "+");
            for(string f: v)
                if(reverse ? matches(fact, f) : matches(f, fact)) {
                    return t;
                }
        }
    } 

    if(fact.substr(0, 2) == "OR") {
        vector<string> v = utils::split_at(fact.substr(2), "|");
        for(string c: v)
            if(string s = trace_logical(c); s != "FALSE")
                return s;
        return check_or(fact);
    }

    if(fact.substr(0, 2) == "AN") {
        vector<string> v = utils::split_at(fact.substr(2), "+");
        string r;
        for(string c: v)
            if(string s = trace_logical(c); s == "FALSE")
                return "FALSE";
            else
                r += (r.empty() ? "" : " ") + s;
        return r;
    }

    return "FALSE";
}

// Checks if a list of facts can be verified.
bool fact_set::verify_facts(const vector<string>& fact) const {
    for(const string& f: fact)
        if(trace_logical(f) == "FALSE")
            return false;
    return true;
}

// Returns the last statement added, as well as a statement that
// contradicts it.
// Returns "FALSE" if no contradiction is found.
std::string fact_set::find_contradiction() const {
    string s = trace_logical("NO" + last);
    if(s == "FALSE")
        return "FALSE";

    return last + " " + s;
}

// A special check for disjunctions: if another disjuntion which
// is a superset of all_cases exists, and the rest of its clauses are
// false it returns these.
// Otherwise returns "FALSE".
string fact_set::check_or(const string& all_cases) const {
    vector<string> cases{utils::split_at(all_cases.substr(2), "|")};
    for(string f: facts) {
        string s = f;
        f = parse::canonical(f);
        if(f.substr(0, 2) != "OR")
            continue;

        vector<string> clauses{utils::split_at(f.substr(2), "|")};
        bool b{true};
        for(string c: clauses)
            if(std::find(cases.begin(), cases.end(), c) == cases.end()) {
                if(string k = trace_logical("NO" + c); k == "FALSE") {
                    b = false;
                    break;
                } else
                    s += " " + k;
            }

        if(b)
            return s;
    }

    return "FALSE";
}

// Returns all facts that match the pattern.
vector<string> fact_set::all_matches(const std::string& pattern) const {
    vector<string> res;
    for(string s: facts)
        if(matches(s, pattern))
            res.push_back(s);
    return res;
}
