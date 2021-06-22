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

            fact_set f; f.add_fact(th_.conclusion);
            if(f.trace_logical(stmt) != "FALSE")
                return sub;

            return "";

        } else {
            string s;
            for(char c: vars) {
                theorem th_ = th.instantiate(sub + c +
                        string(th.get_var_cnt() - int(sub.size()) - 1, '?'));

                if(!facts.verify_facts(th_.assumptions))
                    continue;

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
            return generate_reason(ax + "E", axiom.instantiate(s), stmt, facts);

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
            return generate_reason(th, thy.instantiate(s), stmt, facts);

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
            // Warn("Could not find definition `" + def + "`, using sorry.");
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
