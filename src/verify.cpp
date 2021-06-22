#include <fstream>
#include <algorithm>

#include "verify.h"
#include "parse.h"
#include "definitions.h"
#include "command.h"
#include "axioms.h"
#include "utils.h"

namespace verify {
    using std::string, std::vector;

    // Performs a semi-brute-force test of all combination of variables
    // that can prove stmt using facts and th.
    string test_combination(const string& stmt, const theorem& th,
            const string& vars, const string& sub, const fact_set& facts) {

        if(sub.size() == th.get_var_cnt()) {
            theorem th_ = th.instantiate(sub);
            if(!facts.verify_facts(th_.assumptions))
                return "";
                    
            if(th_.conclusion == stmt)
                return sub;

            fact_set f; f.add_fact(th_.conclusion);
            if(f.trace_logical(stmt) != "FALSE")
                return sub;

            return "";

        } else {
            string s;
            for(char c: vars) {
                string sub_ = sub + c + string(th.get_var_cnt() -
                        int(sub.size()) - 1, '?');
                theorem th_ = th.instantiate(sub_);

                if(!facts.verify_facts(th_.assumptions))
                    continue;

                fact_set tmp; tmp.add_fact(th_.conclusion);
                if(tmp.trace_logical(stmt, true) == "FALSE")
                    continue;

                if(std::all_of(th_.assumptions.begin(), th_.assumptions.end(),
                            [](string str){
                            return str.find("?") == string::npos;
                            })) {
                        return sub_;
                }
                           
                int missing_count{};
                for(char x: parse::get_vars(stmt))
                    if((sub + c).find(x) == string::npos)
                        missing_count++;

                if(missing_count > th.get_var_cnt() - int(sub.size()) - 1)
                    continue;

                s = test_combination(stmt, th, vars, sub + c, facts);
                if(s != "")
                    break;
            }
            return s;
        }
    }

    // This method is slower on most proofs (but faster ocassionally).
    // For this reason, this method isn't used.
    string test_combination_slow(const string& stmt, const theorem& th,
            const string& vars, string sub, const fact_set& facts) {
        if(sub.empty()) {
            sub = parse::get_vars(stmt);
            sub = string(th.get_var_cnt() - int(sub.size()), '?') + sub;
            do {
                string s = test_combination_slow(stmt, th, vars, sub, facts);
                if(!s.empty())
                    return s;
            } while(next_permutation(sub.begin(), sub.end()));

            return "";
        }

        theorem th_ = th.instantiate(sub);
        if(!facts.verify_facts(th_.assumptions))
            return "";
        fact_set tmp; tmp.add_fact(th_.conclusion);
        if(tmp.trace_logical(stmt, true) == "FALSE")
            return "";

        if(std::all_of(th_.assumptions.begin(), th_.assumptions.end(),
                        [](string str){
                    return str.find("?") == string::npos;
                    })) {
                return sub;
        }

        int i = sub.find("?");
        if(i == string::npos)
            return "";

        string good_vars{};
        for(string s: th_.assumptions)
            for(string k: facts.all_matches(s))
                good_vars += parse::get_vars(k);
        utils::unique(good_vars);

        for(char c: good_vars) {
            sub[i] = c;
            string s = test_combination_slow(stmt, th, vars, sub, facts);
            if(!s.empty())
                return s;
        }

        for(char c: vars) if(good_vars.find(c) == string::npos) {
            sub[i] = c;
            string s = test_combination_slow(stmt, th, vars, sub, facts);
            if(!s.empty())
                return s;
        }

        return "";
    }

    // Generates an Isabelle reason for
    // stmt using theorem th (which has name name)
    // and facts.
    string generate_reason(const string& name, const theorem& th,
            const string& stmt, const fact_set& facts) {
        bool b{true};
        for(string h: th.assumptions)
            if(!facts.has_fact(h))
                b = false;

        if(b) {
            string res = "using " + name + "[OF `axioms`";
            for(string h: th.assumptions)
                res += " `" + parse::translate(h) + "`";
            res += "] ";
            if(th.conclusion == stmt)
                res += ".";
            else
                res += "by blast";
            return res;
        } else {
            string res = "using " + name + " `axioms` ";
            for(string h: th.assumptions) {
                if(string s = facts.trace_logical(h); s != "FALSE") {
                    for(string k: utils::split_at(s, " "))
                        res += "`" + parse::translate(k) + "` ";
                } else {
                    Warn("Attempted to use theorem " + name + " to prove "
                            + stmt + " with incomplete preconditions, using sorry.");
                    return "sorry";
                }
            }

            res += "by blast";
            return res;
        }
    }

    // Proof by fact (already proven or equivalent to a proven statement).
    string by_fact(const std::string& stmt, const fact_set& facts) {
        if(facts.has_fact(stmt))
            return "using `" + parse::translate(stmt) + "` .";

        else if(string s = facts.trace_logical(stmt); s != "FALSE") {
            string ret{"using "};
            for(string k: utils::split_at(s, " "))
                ret += "`" + parse::translate(k) + "` ";
            ret += "by blast";
            return ret;
        }

        Warn("Could not check fact `" + stmt + "`, using sorry.");
        return "sorry";
    }

    // Proof by substituting equal variables in a proven statement.
    string by_equalitysub(const string& stmt, const fact_set& facts) {
        vector<string> possibilities{
            facts.all_matches(
                    theorem({}, stmt).instantiate(
                        string(parse::get_vars(stmt).size(), '?')
                        ).conclusion
                    )
        };

        for(string s: possibilities) {
            string reason = "using `" + parse::translate(s) + "` ";
            for(int i{}; i < stmt.size(); ++i)
                if(stmt[i] != s[i]) {
                    if(string k = facts.trace_logical(string("EQ") + s[i] + stmt[i]);
                            k != "FALSE") {
                        reason += "`" + parse::translate(k) + "` ";
                    } else if(k = facts.trace_logical(string("EQ") + stmt[i] + s[i]);
                            k != "FALSE") {
                        reason += "`" + parse::translate(k) + "` ";
                    } else {
                        reason = "FALSE";
                        break;
                    }
                }
            if(reason != "FALSE")
                return reason + "by blast";
        }

        Warn("Failed to show " + stmt + " using equalitysub, using sorry.");
        return "sorry";
    }

    // Proof using an axiom.
    string by_axiom(const string& stmt, const string& ax,
            const string& vars, const fact_set& facts) {

        if(ax == "equalitysub")
            return by_equalitysub(stmt, facts);

        if(axioms.find(ax) == axioms.end()) {
            Warn("Unknown axiom `" + ax + "`, using sorry.");
            return "sorry";
        }

        theorem axiom{axioms.find(ax)->second};
        
        if(string s{test_combination(stmt, axiom, vars, "", facts)}; s != "")
            return generate_reason(ax + "E", axiom.instantiate(s), stmt, facts);

        Warn("Failed to use axiom `" + ax + "` to show `"
                + stmt + "`, using sorry.");
        return "sorry";
    }

    // Proof using a theorem.
    string by_theorem(const string& stmt, const string& th,
            const string& vars, const fact_set& facts) {
        if(theorem::theorems.find(th) == theorem::theorems.end()) {
            Warn("Unknown theorem `" + th + "`, using sorry.");
            return "sorry";
        }

        theorem thy{theorem::theorems.find(th)->second};
        
        if(string s{test_combination(stmt, thy, vars, "", facts)}; s != "")
            return generate_reason(th, thy.instantiate(s), stmt, facts);

        Warn("Failed to use theorem `" + th + "` to show `"
                + stmt + "`, using sorry.");
        return "sorry";
    }

    // Proof using a definition.
    string by_definition(const string& stmt, string def,
            const std::string& vars, const fact_set& facts) {
       
        if(definitions.find(def + "_f") == definitions.end()) {
            Warn("Could not find definition `" + def + "`, using sorry.");
            return "sorry";
        }

        theorem de_f{definitions.find(def + "_f")->second};
        if(string s{test_combination(stmt, de_f, vars, "", facts)}; s != "")
            return generate_reason(def + "_f", de_f.instantiate(s), stmt, facts);

        theorem de_b{definitions.find(def + "_b")->second};
        if(string s{test_combination(stmt, de_b, vars, "", facts)}; s != "")
            return generate_reason(def + "_b", de_b.instantiate(s), stmt, facts);
        
        Warn("Failed to use definition `" + def + "` to show `"
                + stmt + "`, using sorry.");
        return "sorry";
    }


    // Separates the type of reason from the reason (eg. cn, axiom, lemma etc...)
    string reason_type(const string& reason) {
        return utils::split_at(reason, ":")[0];
    }

    // Verifies a stmt using one of the above methods.
    string verify(const string& vars, const fact_set& facts,
            const string& stmt, const string& reason) {

        string type{reason_type(reason)};

        if(type == "")
            return by_fact(stmt, facts);

        else if(type == "axiom" || type == "cn" || type == "postulate") 
            return by_axiom(stmt, utils::split_at(reason, ":")[1], vars, facts);

        else if(type == "lemma")
            return by_theorem(stmt, utils::fix_name(utils::split_at(reason, ":")[1]),
                    vars, facts);

        else if(type == "proposition")
            return by_theorem(stmt, "Prop" + utils::split_at(reason, ":")[1],
                    vars, facts);

        else if(type == "defn")
            return by_definition(stmt, utils::split_at(reason, ":")[1], vars, facts);

        else if(type == "assumption" || type == "reductio")
            Abort("Arguments by contr should be handled in a different function.");

        else if(type == "cases")
            Abort("Arguments by cases should be handled in a different function.");

        else 
            Abort("Unknown reason: " + reason);

        return "";
    }

} // namespace verify
