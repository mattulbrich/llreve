/*
 * This file is part of
 *    llreve - Automatic regression verification for LLVM programs
 *
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 *
 * The system is published under a BSD license.
 * See LICENSE (distributed with this file) for details.
 */

#include "logging.h"
#include <assert.h>

void Util::configureLogger(){
	el::Configurations conf;
	conf.setToDefault();

	conf.setGlobally(el::ConfigurationType::Filename, "log");
	conf.setGlobally(el::ConfigurationType::ToStandardOutput, "false");
	conf.setGlobally(el::ConfigurationType::Format, "%level %datetime{%y-%M-%d %H:%m:%s} %fbase:%line; %msg");
	conf.setGlobally(el::ConfigurationType::ToStandardOutput, "false");

	conf.set(el::Level::Error, el::ConfigurationType::ToStandardOutput, "true");
	conf.set(el::Level::Fatal, el::ConfigurationType::ToStandardOutput, "true");

	el::Loggers::reconfigureLogger("default", conf);

	conf.setGlobally(el::ConfigurationType::Format, "%level %datetime{%y-%M-%d %H:%m:%s}; %msg");
	el::Loggers::reconfigureLogger("performance", conf);
}

TimeLog::TimeLog():start(Clock::now()){
	isStoped = false;
}

TimeLog* TimeLog::stop() {
	if (!isStoped) {
		isStoped = true;
		time = std::chrono::duration_cast<TimeDuration> 
                            (Clock::now() - start);
	}
	return this;
}

TimeDuration TimeLog::getTime() const {
	assert(isStoped && "InternalError: Did not stop time before getting.");
	return time;
}


std::ostream & operator<<(std::ostream & stream, const TimeLog &timeLog) { 
  stream << timeLog.getTime().count() << "ms";
  return stream;
}
