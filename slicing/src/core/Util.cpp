/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "Util.h"

#include "llvm/Support/raw_ostream.h"

using namespace std;
using namespace llvm;

string& Util::toString(
		Value const& value,
		string&      str,
		bool const   isForDebug) {
	
	raw_string_ostream rso(str);
	
	value.print(rso, isForDebug);
	
	return str;
}

string Util::toString(
		Value const& value,
		bool const   isForDebug) {
	
	string str;
	
	return Util::toString(value, str, isForDebug);
}
