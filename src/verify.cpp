#include <fstream>

#include "verify.h"
#include "parse.h"
#include "definitions.h"
#include "command.h"
#include "axioms.h"
#include "utils.h"

namespace verify {
    using std::string, std::vector;

    string test_combination(const string& stmt, const theorem& th,
            const string& vars, const string& sub, const fact_set& facts) {
        if(sub.size() == th.get_var_cnt()) {
            theorem th_ = th.instantiate(sub);
            if(!facts.verify_facts(th_.assumptions))
                return "";
                    
            if(th_.conclusion == stmt)
                return sub;

            if(th_.conclusion.substr(0, 2) == "AN") {
                vector<string> clauses{utils::split_at(th_.conclusion.substr(2), "+")};
                for(string cl: clauses)
                    if(cl == stmt)
                        return sub;
            }

            return "";
        } else {
            string s;
            for(char c: vars) {
                if(th.conclusion.size() == stmt.size()) {
                    theorem th_ = th.instantiate(sub + c +
                            string(th.get_var_cnt() - int(sub.size()) - 1, '?'));
                    bool b = true;
                    for(int i{}; i < stmt.size(); ++i)
                        if(th_.conclusion[i] != '?' && th_.conclusion[i] != stmt[i]) {
                            b = false;
                            break;
                        }
                    if(!b) continue;
                }
                s = test_combination(stmt, th, vars, sub + c, facts);
                if(s != "")
                    break;
            }
            return s;
        }
    }

    string generate_reason(const string& name, const theorem& th, const string& stmt) {
        string res = "using " + name + "[OF `axioms`";
        for(string h: th.assumptions)
            res += " `" + parse::translate(h) + "`";
        res += "] ";
        if(th.conclusion == stmt)
            res += ".";
        else
            res += "by blast";
        return res;
    }

    string by_fact(const std::string& stmt, const fact_set& facts) {
        if(facts.has_fact(stmt))
            return "using `" + parse::translate(stmt) + "` .";

        else if(string s = facts.trace_demorgan_and(stmt); s != "FALSE")
            return "using `" + parse::translate(s) + "` by simp";

        else if(stmt.substr(0, 2) == "AN") {
            string reason = " using ";
            vector<string> clauses{utils::split_at(stmt.substr(2), "+")};
            for(string cl: clauses)
                if(string t = facts.trace_demorgan_and(cl); t != "FALSE")
                    reason += "`" + parse::translate(t) + "` ";
                else {
                    Warn("Could not check fact `" + cl + "` in "
                            + stmt + " using sorry.");
                    return "sorry";
                }
            reason += "by simp";
            return reason;

        } else if(stmt.substr(0, 2) == "OR") {
            string reason = " using ";
            vector<string> clauses{utils::split_at(stmt.substr(2), "|")};
            for(string cl: clauses)
                if(string t = facts.trace_demorgan_and(cl); t != "FALSE")
                    return "using `" + parse::translate(t) + "` by simp";
            Warn("Could not check fact `" + stmt + "`, using sorry.");
            return "sorry";

        } else {
            Warn("Could not check fact `" + stmt + "`, using sorry.");
            return "sorry";
        }
    }

    string by_axiom(const string& stmt, const string& ax,
            const string& vars, const fact_set& facts) {

        if(ax == "equalitysub") {
#warning "equalitysub has not been implemented."
            Warn("TODO equalitysub, using sorry.");
            return "sorry";
        }


        if(axioms.find(ax) == axioms.end()) {
            Warn("Unknown axiom `" + ax + "`, using sorry.");
            return "sorry";
        }

        theorem axiom{axioms.find(ax)->second};
        
        if(string s{test_combination(stmt, axiom, vars, "", facts)}; s != "") 
            return generate_reason(ax + "E", axiom.instantiate(s), stmt);

        Warn("Failed to use axiom `" + ax + "` to show `"
                + stmt + "`, using sorry.");
        return "sorry";
    }

    string by_theorem(const string& stmt, const string& th,
            const string& vars, const fact_set& facts) {
        if(theorem::theorems.find(th) == theorem::theorems.end()) {
            Warn("Unknown theorem `" + th + "`, using sorry.");
            return "sorry";
        }

        theorem thy{theorem::theorems.find(th)->second};
        
        if(string s{test_combination(stmt, thy, vars, "", facts)}; s != "")
            return generate_reason(th, thy.instantiate(s), stmt);

        Warn("Failed to use theorem `" + th + "` to show `"
                + stmt + "`, using sorry.");
        return "sorry";
    }

    string by_definition(const string& stmt, string def,
            const std::string& vars, const fact_set& facts) {
        if(euc_cmd_names.find(def) == euc_cmd_names.end()) {
            Warn("Unknown definition `" + def + "`, using sorry.");
            return "sorry";
        }

        def = euc_cmd_names.at(def);

        if(commands.find(def) == commands.end()) {
            Warn("No command `" + def + "` corresponding to definition, using sorry.");
            return "sorry";
        }
       
        def = commands.at(def).name;

        if(definitions.find(def + "_f") == definitions.end()) {
            Warn("Could not find definition `" + def + "`, using sorry.");
            return "sorry";
        }

        theorem de_f{definitions.find(def + "_f")->second};
        if(string s{test_combination(stmt, de_f, vars, "", facts)}; s != "")
            return generate_reason(def + "_f", de_f.instantiate(s), stmt);

        theorem de_b{definitions.find(def + "_b")->second};
        if(string s{test_combination(stmt, de_b, vars, "", facts)}; s != "")
            return generate_reason(def + "_b", de_b.instantiate(s), stmt);
        
        Warn("Failed to use definition `" + def + "` to show `"
                + stmt + "`, using sorry.");
        return "sorry";
    }

    string reason_type(const string& reason) {
        return utils::split_at(reason, ":")[0];
    }

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