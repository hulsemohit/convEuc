#include <iostream>
#include <algorithm>

#include "theorem.h"
#include "utils.h"
#include "command.h"


using std::string, std::vector;

std::map<char, vector<int>> get_pos(string euc_statement, int offset = 0) {
    string cmd{euc_statement.substr(0, 2)}, args{euc_statement.substr(2)};
    
    if(cmd == "NO")
        return get_pos(args, offset + 2);
    else if(cmd == "AN" || cmd == "OR") {
        vector<string> clauses{utils::split_at(args, cmd == "AN" ? "+" : "|")};
        std::map<char, vector<int>> res;
        offset += 2;
        for(string s: clauses) {
            for(auto [v, p]: get_pos(s))
                for(int k: p)
                    res[v].push_back(k + offset);
            offset += s.size();
        }

        return res;
    } else {
        std::map<char, vector<int>> res;
        for(int i{}; i < args.size(); ++i)
            res[args[i]].push_back(offset + 2 + i);
        return res;
    }
}


theorem::theorem(vector<string> euc_assms, string euc_conc): assumptions{euc_assms}, conclusion{euc_conc} {
    string vars;

    vector<std::map<char, vector<int>>> assms;
    for(string s: euc_assms) {
        assms.push_back(get_pos(s));
        for(auto c: assms.back())
            vars += c.first;
    }
    
    std::map<char, vector<int>> conc{get_pos(euc_conc)};
    for(auto c: conc)
        vars += c.first;

    std::sort(vars.begin(), vars.end());
    vars.erase(std::unique(vars.begin(), vars.end()), vars.end());

    var_cnt = vars.size();

    for(std::map<char, vector<int>> m: assms) {
        assms_pos.emplace_back();
        for(int i{}; i < var_cnt; ++i)
           assms_pos.back().push_back(m[vars[i]]);
    }

    for(int i{}; i < var_cnt; ++i)
        conc_pos.push_back(conc[vars[i]]);
}


theorem theorem::instantiate(const string& vars) const {
    if(var_cnt != vars.size()) {
        Abort("Attempted to instantiate a theorem with " +
                std::to_string(var_cnt) + " arguments using " + vars);
    }
    
    vector<string> assms_copy{assumptions};
    string conc_copy{conclusion};
    for(int i{}; i < var_cnt; ++i) {
        for(int j{}; j < assumptions.size(); ++j)
            for(int k: assms_pos[j][i])
                assms_copy[j][k] = vars[i];

        for(int k: conc_pos[i])
            conc_copy[k] = vars[i];
    }

    return theorem(assms_copy, conc_copy);
}


bool theorem::check_assumptions(const fact_set& facts) const {
    return facts.verify_facts(assumptions);
}

string theorem::to_string() const {
    string s{};
    for(string a: assumptions)
        s += a + " ";
    s += "==> " + conclusion;
    return s;
}

int theorem::get_var_cnt() const {
    return var_cnt;
}

std::map<string, theorem> theorem::theorems{};
