#include <fstream>
#include <string>

#include "theorem.h"
#include "command.h"
#include "utils.h"
#include "prover.h"

void generate_statement(const std::string&);

int main() {
    std::ifstream in("../eucfiles/list.txt");

    std::string s;
    Info("Generating theorem statements...");
    while(getline(in, s)) {
        Info("Generating statement for " +  s);
        generate_statement(s);
    }
    
    in.close();

    return 0;
    in = std::ifstream("../eucfiles/list.txt");
    Info("Verifying proofs, and generating output...");
    while(getline(in, s)) {
        Info("Verifying " + s);
    }

    return 0;
}


void generate_statement(const std::string& fname) {
    using std::string, std::vector;
    std::ifstream in("../eucfiles/" + fname);

    string name{utils::fix_name(fname.substr(0, fname.size() - 4))};

    string line; 
    if(!getline(in, line)) {
        Warn("Empty file, skipping.");
        return;
    }

    line = utils::trim(line);
    vector<string> assms;
    while(line.find(" ") == string::npos) {
        if(!line.empty())
            assms.push_back(line);
        getline(in, line);
        line = utils::trim(line);
    }

    string conc;
    do {
        line = utils::trim(line);
        if(!line.empty())
            conc = line;
    } while(getline(in, line));
    conc = conc.substr(0, conc.find(" "));

    theorem::theorems.insert({name, theorem(assms, conc)});
    Info(name + " = " + theorem::theorems[name].to_string());
    Info(name + " \\<equiv>  " + prover::translate(theorem::theorems[name].conclusion));
}