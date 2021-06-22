#include <string>
#include <vector>

#include "utils.h"
#include "command.h"
#include "parse.h"

namespace parse {

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
                Abort("Unknown command " + cmd + " while parsing " + stmt);
            return commands.at(cmd).convert(args);
        }
    }

    string get_vars(const string& stmt) {
        string cmd{stmt.substr(0, 2)}, args{stmt.substr(2)};
        if(cmd == "NO")
            return get_vars(args);

        if(cmd == "AN" || cmd == "OR") {
            vector<string> clauses{utils::split_at(args, (cmd == "AN" ? "+" : "|"))};
            string vars{};
            for(string s: clauses)
                vars += get_vars(s);
            utils::unique(vars);
            return vars;
        }

        utils::unique(args);
        return args;
    }

    // canonical form: cannot have "NONO" "NOAN" "NOOR" "NOEQ" "NOCO""NONE" "NONC
    // these are converted into "" "ORNO...|NO..." "ANNO..+" "NE" "NC" "EQ" "CO"
    string canonical(const string& s) {
        if(s.size() <= 3)
            return s;
        if(s.substr(0, 4) == "NONO")
            return canonical(s.substr(4));
        if(s.substr(0, 4) == "NOEQ")
            return "NE" + s.substr(4);
        if(s.substr(0, 4) == "NOCO")
            return "NC" + s.substr(4);
        if(s.substr(0, 4) == "NONE")
            return "EQ" + s.substr(4);
        if(s.substr(0, 4) == "NONC")
            return "CO" + s.substr(4);
        if(s.substr(0, 4) == "NOOR" || s.substr(0, 4) == "NOAN") {
            bool b = s.substr(2, 2) == "AN";
            string f{b ? "OR" : "AN"};
            vector<string> clauses{utils::split_at(s.substr(4), b ? "+" : "|")};
            for(string cl: clauses)
                f += canonical("NO" + cl)  + (b ? "|" : "+");
            f.pop_back();
            return f;
        }
        if(s.substr(0, 2) == "AN" || s.substr(0, 2) == "OR") {
            bool b = s.substr(0, 2) == "AN";
            string f{b ? "AN" : "OR"};
            vector<string> clauses{utils::split_at(s.substr(2), b ? "+" : "|")};
            for(string cl: clauses)
                f += canonical(cl) + (b ? "+" : "|");
            f.pop_back();
            return f;
        }

        return s;
    }

} // namespace parse
