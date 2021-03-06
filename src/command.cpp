#include "command.h"
#include "utils.h"

using std::string;

// Creates a Euc word from the given variables and the command.
string command::convert(const string& vars) const {
    if (vars.length() != arity)
        Abort("Attempted to apply command " + name + " of arity "
              + std::to_string(arity) + " to " + vars);

    if (name == "eq_pnt") return vars[0] + string(" = ") + vars[1];

    if (name == "neq_pnt") return vars[0] + string(" \\<noteq> ") + vars[1];

    string result{name};
    for (char c: vars) {
        result += " ";
        if (c == 'O') result += "p";
        result += c;
    }

    return result;
}
