#include <fstream>
#include <string>

#include "axioms.h"
#include "command.h"
#include "definitions.h"
#include "parse.h"
#include "prover.h"
#include "theorem.h"
#include "utils.h"
#include "verify.h"

void generate_statement(const std::string&);
void generate_base_theory();

int main(int, char* argv[]) {
    // Don't automatically generate Geometry.thy, some sections have been
    // modified by hand. Automatic generation uses `sorry` to prove three lemmas
    // and also has some incorrect parenthesization (in `definition paste3`).
    //
    // generate_base_theory();

    std::ifstream in("eucfiles/list.txt");
    std::ofstream root("thyfiles/ROOT");

    root << "session Euc = HOL +\n";
    root << "theories\n";
    root << "\tGeometry\n";

    std::string s;
    Info("Generating theorem statements...");
    while (getline(in, s)) {
        Info("Generating statement for " + s);
        generate_statement(s);
        root << "\t" << utils::fix_name(s.substr(0, s.size() - 4)) << '\n';
    }
    in.close();
    root.close();

    in = std::ifstream("eucfiles/list.txt");
    while (getline(in, s)) {
        Info("Verifying " + s);
        prover::generate_proof(s);
    }
    in.close();

    return 0;
}

// Generates the statements of a theorem.
void generate_statement(const std::string& fname) {
    using std::string, std::vector;
    std::ifstream in("eucfiles/" + fname);

    string name{utils::fix_name(fname.substr(0, fname.size() - 4))};

    string line;
    if (!getline(in, line)) {
        Warn("Empty file, skipping.");
        return;
    }

    line = utils::trim(line);
    vector<string> assms;
    while (line.find(" ") == string::npos) {
        if (!line.empty()) assms.push_back(line);
        getline(in, line);
        line = utils::trim(line);
    }

    string conc;
    do {
        line = utils::trim(line);
        if (!line.empty()) conc = line;
    } while (getline(in, line));
    conc = conc.substr(0, conc.find(" "));
    in.close();

    theorem::theorems.insert({name, theorem(assms, conc)});
    Info(name + " = " + theorem::theorems[name].to_string());

    theorem& th = theorem::theorems[name];
    Info("Finding dependencies for theorem " + name);
    in.open("eucfiles/" + fname);

    while (getline(in, line)) {
        line = utils::trim(line);
        if (line.find(" ") == string::npos) continue;
        string reason = utils::trim(line.substr(line.find(" ")));
        string rtype  = verify::reason_type(reason);
        if (rtype == "proposition")
            th.add_depends("Prop" + utils::split_at(reason, ":")[1]);
        else if (rtype == "lemma")
            th.add_depends(utils::split_at(reason, ":")[1]);
    }
    in.close();
}

// Generates the Geometry.thy file.
void generate_base_theory() {
    using std::string, std::vector;
    std::ofstream out("thyfiles/Geometry.thy");

    const string a = " \\<Rightarrow> ", p = "point", b = "bool", q = "\"";

    out << "theory Geometry\n";
    out << "\timports Main\n";
    out << "begin\n\n";

    out << "typedecl point\n";
    out << "typedecl circ\n\n";

    out << "consts\n";
    out << "\tbet :: " << q + p + a + p + a + p + a + b + q << "\n";
    out << "\tseg_eq :: " << q + p + a + p + a + p + a + p + a + b + q << "\n";
    out << "\tcircle :: \"circ" << a + p + a + p + a + p + a + b + q << "\n\n";

    Info("Creating definitions.");
    for (auto [name_, th]: def_list) {
        if (name_.back() != 'f') continue;
        string name = name_;
        name.pop_back();
        name.pop_back();
        if (th.assumptions.size() != 1 || name == "circle") {
            Warn("Manually add definition for " + name);
            continue;
        }

        Info("Defining " + name);
        if (euc_cmd_names.find(name) == euc_cmd_names.end()) {
            Warn("Couldn't find Euc command for " + name);
            continue;
        }

        if (commands.find(euc_cmd_names.at(name)) == commands.end()) {
            Warn("Command " + euc_cmd_names.at(name) + " for " + name
                 + " doesn't exist.");
            continue;
        }

        string isa_name = commands.at(euc_cmd_names.at(name)).name;
        out << "definition " << isa_name << " where\n";
        out << "\t\"" << parse::translate(th.assumptions[0]) << " \\<equiv> ";
        if (!th.get_exists().empty()) {
            out << "\\<exists>";
            for (char c: th.get_exists()) out << " " << c;
            out << ". ";
        }
        out << parse::translate(th.conclusion) << "\"";
        out << "\n\n" << std::flush;
    }

    out << "definition cir_in where\n";
    out << "\t\"cir_in P J \\<equiv> \\<forall> C A B. circle J C A B ";
    out << "\\<longrightarrow> (\\<exists> X Y. ";
    out << parse::translate(definitions.at("inside_f").conclusion) << ")\"\n\n";

    out << "definition cir_ou where\n";
    out << "\t\"cir_ou P J \\<equiv> \\<forall> C A B. circle J C A B ";
    out << "\\<longrightarrow> (\\<exists> X. ";
    out << parse::translate(definitions.at("outside_f").conclusion)
        << ")\"\n\n";

    out << "definition cir_on where\n";
    out << "\t\"cir_on B J \\<equiv> \\<forall> A C D. circle J A C D ";
    out << "\\<longrightarrow> ";
    out << parse::translate(definitions.at("on_f").conclusion) << "\"\n\n";

    out << "\n";
    Info("Definitions completed.");

    Info("Creating axioms");
    string all_axioms;
    for (auto [name_, th]: axioms) {
        string name = utils::fix_name(name_);
        Info("Axiom " + name);
        if (!all_axioms.empty()) all_axioms += " \\<and> ";
        all_axioms += name;
        out << "definition " << name << " where\n";
        out << "\t\"" << name << " \\<equiv> ";
        string vars;
        for (string s: th.assumptions) vars += parse::get_vars(s);
        utils::unique(vars);

        string exists = th.get_exists();
        if (name_ == "equalityreflexive" || name_ == "congruencereflexive"
            || name_ == "equalityreverse" || name_ == "betweennessidentity"
            || name_ == "nullsegment2") {
            vars += exists;
            exists = "";
            vars += parse::get_vars(th.conclusion);
            utils::unique(vars);
            out << "\\<forall>";
            for (char c: vars) out << ' ' << c;
            out << " :: point. ";
            out << parse::translate(th.conclusion);
            out << "\"\n\n";
            continue;
        }

        for (char c: parse::get_vars(th.conclusion))
            if (exists.find(c) == string::npos) vars += c;
        utils::unique(vars);

        out << "\\<forall>";
        for (char c: vars) out << ' ' << c;
        if (name == "equalitytransitive" || name == "stability")
            out << " :: point";
        out << ". ";
        if (!th.assumptions.empty()) {
            for (int i{}; i < th.assumptions.size(); ++i) {
                if (i != 0) out << " \\<and> ";
                out << parse::translate(th.assumptions[i]);
            }
        }

        out << " \\<longrightarrow> (";
        if (!exists.empty()) {
            out << "\\<exists>";
            for (char c: exists) out << ' ' << c;
            out << ". ";
        }

        out << parse::translate(th.conclusion) << ")\"\n\n";
    }

    out << "definition circle_ne where\n";
    out << "\t\"circle_ne \\<equiv> \\<forall> A B C.";
    out << "(\\<exists> X. circle X C A B) \\<longleftrightarrow> ";
    out << "A \\<noteq> B\"\n\n";

    all_axioms += " \\<and> circle_ne";

    out << "definition axioms where\n";
    out << "\t\"axioms \\<equiv> " << all_axioms << "\"\n\n";

    Info("Axioms created.");

    Info("Creating elimination rules for definitions.");

    for (auto [name, th]: definitions) {
        Info("Creating " + name);
        out << "lemma " << name << ":\n";
        out << "\tassumes \"axioms\"\n";
        for (string s: th.assumptions)
            out << "\t\t\"" << parse::translate(s) << "\"\n";
        out << "\tshows \"";
        if (name == "circle_f")
            out << "\\<forall> C. \\<exists> X. ";
        else {
            if (!th.get_exists().empty()) {
                out << "\\<exists>";
                for (char c: th.get_exists()) out << " " << c;
                out << ". ";
            }
        }
        out << parse::translate(th.conclusion);
        out << "\"\n";
        out << "\tusing assms axioms_def ";
        string name_ = name;
        if (name == "circle_f" || name == "circle_b")
            name_ = "circle_ne";
        else {
            name_.pop_back(), name_.pop_back();
            name_ = commands.at(euc_cmd_names.at(name_)).name;
        }
        out << name_ << "_def";
        if (name == "inside_b" || name == "outside_b" || name == "on_b") {
            Warn("Circle definitions need to be fixed.");
            out << " sorry\n\n";
        } else {
            out << " by fastforce\n\n";
        }
    }
    Info("Created definition elimination rules.");

    out << "\n";

    Info("Creating axiom elimination rules.");
    for (auto [name_, th]: axioms) {
        string name = utils::fix_name(name_);
        Info("Creating " + name + "E");
        out << "lemma " << name << "E:\n";
        out << "\tassumes \"axioms\"\n";
        for (string s: th.assumptions)
            out << "\t\t\"" << parse::translate(s) << "\"\n";

        string exists = th.get_exists();
        if (name_ == "equalityreflexive" || name_ == "congruencereflexive"
            || name_ == "equalityreverse" || name_ == "betweennessidentity"
            || name_ == "nullsegment2")
            exists = "";
        out << "\tshows \"";
        if (!exists.empty()) {
            out << "\\<exists>";
            for (char c: exists) out << ' ' << c;
            out << ". ";
        }
        out << parse::translate(th.conclusion) << "\"\n";
        out << "\tusing assms axioms_def ";
        out << name << "_def by blast\n\n";
    }

    Info("Created axiomsE");

    out << "end";
    out.close();
}
