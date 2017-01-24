/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

/**
 * Usage:
 * Log(Level) << "message";
 * LOG(LEVEL) << "message";
 * TIMED_FUNC(obj-name)
 * TIMED_SCOPE(obj-name, block-name)
 */
#pragma once

// Dont like writing uppercase a lot
#define Trace TRACE
#define Debug DEBUG
#define Fatal FATAL
#define Error ERROR
#define Warning WARNING
#define Info INFO
#define Verbose VERBOSE
#define Log LOG

#ifdef __clang__
//Disable all clang warning for the logging library:
#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wall"
#pragma clang diagnostic ignored "-Wpedantic"
#pragma clang diagnostic ignored "-Wextra"
#pragma clang diagnostic ignored "-Wc++98-compat-pedantic"
#pragma clang diagnostic ignored "-Wweak-vtables"
#pragma clang diagnostic ignored "-Wdocumentation-unknown-command"
#pragma clang diagnostic ignored "-Wundef"
#pragma clang diagnostic ignored "-Wsign-conversion"
#pragma clang diagnostic ignored "-Wdeprecated"
#pragma clang diagnostic ignored "-Wdouble-promotion"
#pragma clang diagnostic ignored "-Wnewline-eof"
#pragma clang diagnostic ignored "-Wdocumentation"
#pragma clang diagnostic ignored "-Wmissing-noreturn"
#endif

#define ELPP_FRESH_LOG_FILE
#define ELPP_NO_DEFAULT_LOG_FILE
#define ELPP_DISABLE_DEFAULT_CRASH_HANDLING
#include "easylogging++.h"

#ifdef __clang__
#pragma clang diagnostic pop
#endif

#include <chrono>

typedef std::chrono::high_resolution_clock Clock;
typedef Clock::time_point TimePoint;
typedef std::chrono::milliseconds TimeDuration;

namespace Util{
	void configureLogger();
}

class TimeLog {
public:
	friend std::ostream & operator<<(std::ostream & Str, const TimeLog &timeLog);
	TimeLog();
	TimeLog* stop();
	TimeDuration getTime() const;
private:
	TimePoint start;
	TimeDuration time;
	bool isStoped;
};
