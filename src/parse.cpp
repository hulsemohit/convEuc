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

} // namespace parse
