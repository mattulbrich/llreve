#include "Helper.h"

using std::string;
using std::set;

string resolveName(const string Name, const set<string> Constructed) {
    if (Constructed.find(Name) == Constructed.end()) {
        return Name + "_old";
    }
    return Name;
}
