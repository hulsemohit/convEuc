#pragma once

#include <string>
#include <vector>

#define Abort(s) utils::log::abort(std::string(__func__) + "::"\
        + std::to_string(__LINE__) + " - " +  s)
#define Info(s) utils::log::info(std::string(__func__) + "::"\
        + std::to_string(__LINE__) + " - " +  s)
#define Warn(s) utils::log::warn(std::string(__func__) + "::"\
        + std::to_string(__LINE__) + " - " +  s)

namespace utils {

    std::vector<std::string> split_at(const std::string& s, const std::string& d);
    
    std::string trim(std::string s);

    std::string fix_name(std::string s);

    void unique(std::string& s);

    namespace log {

        void abort(const std::string& s);

        void info(const std::string& s);

        void warn(const std::string& s);

    } // namespace log

} // namespace utils
