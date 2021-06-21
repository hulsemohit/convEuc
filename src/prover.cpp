#include "prover.h"
#include "command.h"
#include "utils.h"

namespace prover {
    using std::string, std::vector;

    string translate(const string& stmt) {
        if(stmt.size() <= 1)
            Abort("Cannot parse incomplete statement: " + stmt);

        string cmd{stmt.substr(0, 2)}, args{stmt.substr(2)};

        if(cmd == "NO")
            return "\\<not> (" + translate(args) + ")";

        else if(cmd == "AN" || cmd == "OR") {
            vector<string> clauses = utils::split_at(args, cmd == "AN" ? "+" : "|");
            string res;
            for(string s: clauses) {
                if(res.empty())
                    res += translate(s);
                else
                    res += (cmd == "AN" ? " \\<and> " : " \\<or> ") + translate(s);
            }
            return res;

        } else {
            if(commands.find(cmd) == commands.end())
                Abort("Unkown command " + cmd + " while parsing " + stmt);
            return commands.at(cmd).convert(args);
        }
    }

    string by_fact(const std::string& stmt, const fact_set& facts) {
        if(facts.has_fact(stmt))
            return " using `" + translate(stmt) + "` .";
        else if(string s = facts.trace_demorgan_and(stmt); s != "FALSE")
            return " using `" + translate(s) + "` by simp";
        else {
            Warn("Could not check " + stmt + ", using `sorry`.");
            return "sorry";
        }
    }

} // namespace prover
