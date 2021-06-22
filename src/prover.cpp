#include <vector>
#include <sstream>

#include "prover.h"
#include "verify.h"
#include "parse.h"
#include "utils.h"
#include "theorem.h"

namespace prover {

    using std::string, std::vector, std::ifstream, std::ostream, std::ostringstream;

    int indent_level{};

    string proof_step(ifstream& in, fact_set& facts, string& vars) {
        string s; getline(in, s); int l(s.size()); s = utils::trim(s);
        if(s.empty() || s[0] == '%') return "";
        
        string stmt, reason;
        if(int i(s.find(" ")); i == string::npos)
            stmt = s;
        else {
            stmt = utils::trim(s.substr(0, i));
            reason = utils::trim(s.substr(i));
        }

        string new_vars;
        for(char c: parse::get_vars(stmt))
            if(vars.find(c) == string::npos)
                new_vars += c;

        vars += new_vars; utils::unique(vars);

        string type{verify::reason_type(reason)};

        ostringstream out;
        if(type == "assumption") {
            out << string(indent_level, '\t');
            out << "have ";
            string nstmt;
            if(stmt.substr(0, 2) == "NO")
                nstmt = stmt.substr(2);
            else
                nstmt  = "NO" + stmt;
            out << "\"" << parse::translate(nstmt) << "\"\n";
            out << string(indent_level, '\t');
            out << "proof (rule ccontr)\n";
            indent_level++;
            out << by_contr(in, facts, vars, stmt);
            facts.add_fact(nstmt);
            getline(in, s); s = utils::trim(s);
            facts.add_fact(s.substr(0, s.find(" ")));
            return out.str();

        } else if(type == "reductio") {
            out << string(indent_level, '\t');

            out << "show \"False\" ";
            string contr = facts.find_contradiction();
            if(contr == "FALSE") {
                Warn("Failed to find proof by contradiction, using sorry.");
                out << "sorry\n";
            } else {
                out << "using ";
                for(string s: utils::split_at(contr, " "))
                    out << "`" << parse::translate(s) << "` ";
                out << "by blast\n";
            }

            indent_level--;
            out << string(indent_level, '\t');
            out << "qed\n";
            out << string(indent_level, '\t');
            out << "hence \"" << parse::translate(stmt) << "\" by blast\n";
            in.seekg(-(l + !in.eof()), std::ios_base::cur);
            return out.str();

        } else if(stmt == "cases") {
            stmt = type;
            string all_cases = utils::split_at(reason, ":")[1];
            vector<string> cases = utils::split_at(all_cases, "|");
            out << string(indent_level, '\t');
            out << "consider ";
            for(string c: cases) {
                out << "\"" << parse::translate(c) << "\"";
                if(c != cases.back())
                    out << "|";
            }

            if(string s = facts.trace_logical("OR" + all_cases); s != "FALSE") {
                out << " using ";
                for(string k: utils::split_at(s, " "))
                    out << "`" << parse::translate(k) << "` ";
            }
            out << " by blast\n";

            out << string(indent_level, '\t');
            out << "hence " << parse::translate(stmt) << '\n';
            out << string(indent_level, '\t');
            out << "proof (cases)\n";
            for(string c: cases) {
                indent_level++;
                fact_set new_facts{facts};
                new_facts.add_fact(c);
                out << by_cases(in, new_facts, vars);
            }
            facts.add_fact(stmt);
            return out.str();
        } else if(stmt == "case") {
            return string(indent_level, '\t') + "case " + type + "\n";
        } else if(stmt == "qedcase") {
            indent_level--;
            return string(indent_level, '\t') + "next\n";
        } else if(reason == "cases") {
            return "";
        }

        out << string(indent_level, '\t');
        if(!new_vars.empty()) {
            out << "obtain ";
            for(char c: new_vars)
                out << c << " ";
            out << "where ";
        } else {
            out << "have ";
        }

        out << "\"" << parse::translate(stmt) << "\" ";

        string x = verify::verify(vars, facts, stmt, reason);

        if(!new_vars.empty() && x.back() == '.') {
            x.pop_back();
            out << x << " by  blast";
        } else
            out << x;

        out << '\n';

        facts.add_fact(stmt);

        return out.str();
    }

    string by_cases(ifstream& in, fact_set facts, string vars) {
        const int cur_level{indent_level};
        ostringstream out;
        while(cur_level <= indent_level)
            out << proof_step(in, facts, vars);
        return out.str();
    }

    string by_contr(ifstream& in, fact_set facts, string vars, string assm) {
        const int cur_level{indent_level};
        ostringstream out;
        out << string(indent_level, '\t');
        out << "assume \"" << parse::translate(assm) << "\"\n"; 
        facts.add_fact(assm);
        while(indent_level >= cur_level)
            out << proof_step(in, facts, vars);
        return out.str();
    }

    void generate_proof(const std::string& fname) {
        const string name{utils::fix_name(fname.substr(0, fname.size() - 4))};
        std::ofstream out("../thyfiles/" + name + ".thy");
        out << "theory " << name << '\n';
#warning "Figure out imports"
        out << '\t' << "imports Axioms Definitions Theorems" << '\n';
        out << "begin" << "\n\n";

        out << "theorem " << name << ":\n";
        out << "\tassumes: `axioms`";
        out << std::flush;

        fact_set facts;
        string vars;
        for(string assm: theorem::theorems[name].assumptions) {
            out << "\n\t\t\"" << parse::translate(assm) << "\"";
            facts.add_fact(assm);
            vars += parse::get_vars(assm);
        }

        out << "\n\tshows: \"";
        string e{theorem::theorems[name].get_exists()};

        if(!e.empty()) {
            out << "\\<exists>";
            for(char c: e) out << " " << c;
            out << ". ";
        }

        out << parse::translate(theorem::theorems[name].conclusion) << "\"\n";
        out << "proof -\n" << std::flush;

        indent_level++;

        std::ifstream in("../eucfiles/" + fname);
        string s, stmt, reason;
        
        for(getline(in, s); utils::trim(s).find(" ") == string::npos; getline(in, s));
        in.seekg(-int(s.size() + 1), std::ios_base::cur);

        while(!facts.has_fact(theorem::theorems[name].conclusion) && !in.eof())
            out << proof_step(in, facts, vars) << std::flush;

        out << "\tthus ?thesis by blast\n";
        out << "qed\n\nend";
        indent_level--;
        
        
        out.close();
        in.close();
    }

} // namespace prover
