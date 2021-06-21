#include <iostream>
#include <algorithm>

#include "utils.h"


namespace utils {

    using std::string, std::vector;
    
    vector<string> split_at(const string& s, const string& d) {
        vector<string> parts;
        for(int i{}, j{}; j != string::npos; i = j + int(d.size())) {
            j = s.find(d, i);
            parts.push_back(trim(s.substr(i, j - i)));
        }
        return parts;
    }

    string trim(string s) {
        while(!s.empty() && isspace(*s.begin()))
            s.erase(s.begin());
        while(!s.empty() && isspace(*s.rbegin()))
            s.erase(s.end() - 1);
        return s;
    }

    string fix_name(string s) {
        if(!isalpha(s[0]))
            s = "n" + s;
        for(char& c: s) if(c == '.') c = '_';
        return s;
    }

    void unique(string& s) {
        std::sort(s.begin(), s.end());
        s.erase(std::unique(s.begin(), s.end()), s.end());       
    }

    namespace log {
        void abort(const string& s) {
            std::cerr << "[FAIL]: " << s << std::endl;
            exit(1);
        }

        void info(const string& s) {
            std::cerr << "[INFO]: " << s << std::endl;
        }

        void warn(const string& s) {
            std::cerr << "[WARN]: " << s << std::endl;
        }
    }

} // namespace utils
