import re
import os
import pandas

class LogParser:
	smtSolverTimePattern = re.compile(r".*\[SMTSolver\] in \[(.*) (.*)\]")
	smtResultPattern = re.compile(r".*SMT Solver Result: (.*)")
	executionTimePattern = re.compile(r".*\[main\] in \[(.*) (.*)\]")
	slicingTimePattern = re.compile(r".*\[Slicing\] in \[(.*) (.*)\]")
	verificationTimePattern = re.compile(r".*\[Final Verification\] in \[(.*) (.*)\]")
	instructionsPattern = re.compile(r".*Instructions in (program|slice): (.*)")

	def __init__(self, fileName):
		self.file = open(fileName, 'r')
		self.smtSolverTime = list()
		self.smtResult = list()

		self.slicingTime = 0.0
		self.executionTime = 0.0
		self.verificationTime = 0.0

		self.programInstructions = 0
		self.sliceInstructions = 0

		hasVerification = False
		for line in self.file:
			self._collectSolverTime(line)
			self._collectSatResult(line)
			self._collectExecutionTime(line)
			self._collectSicingTime(line)
			hasVerification |= self._collectVerificationTime(line)
			self._collectInstructions(line)


		data = list(zip(self.smtSolverTime, self.smtResult))
		if (hasVerification):
			del data[-1]
		self.smtData = pandas.DataFrame(data = data, columns=['Time', 'Result'])
		self.reveCalls = len(data)

	def __str__(self):
		 return "Slicing Time: " + str(self.slicingTime) + "\n" \
			"Execution Time: " + str(self.executionTime) + "\n" \
			"Verification Time: " + str(self.verificationTime) + "\n" \
			"Instructions Program: " + str(self.programInstructions) + "\n" \
			"Instructions Slice: " + str(self.sliceInstructions)

	def _collectSolverTime(self, line):
		match = LogParser.smtSolverTimePattern.match(line)
		if (match):
			time = float(match.group(1))
			unit = match.group(2)

			self.smtSolverTime.append(self._convertTime(time, unit))

	def _collectExecutionTime(self, line):
		match = LogParser.executionTimePattern.match(line)
		if (match):
			time = float(match.group(1))
			unit = match.group(2)
			self.executionTime = self._convertTime(time, unit)

	def _collectSicingTime(self, line):
		match = LogParser.slicingTimePattern.match(line)
		if (match):
			time = float(match.group(1))
			unit = match.group(2)
			self.slicingTime = self._convertTime(time, unit)

	def _collectVerificationTime(self, line):
		match = LogParser.verificationTimePattern.match(line)
		if (match):
			time = float(match.group(1))
			unit = match.group(2)
			self.verificationTime = self._convertTime(time, unit)
			return True
		return False

	def _collectSatResult(self, line):
		match = LogParser.smtResultPattern.match(line)
		if (match):
			result = match.group(1)
			self.smtResult.append(result)

	def _collectInstructions(self, line):
		match = LogParser.instructionsPattern.match(line)
		if (match):
			what = match.group(1)
			if (what == "program"):
				self.programInstructions = int(match.group(2))
			elif (what == "slice"):
				self.sliceInstructions = int(match.group(2))
			else:
				assert(False)

	def _convertTime(self, time, unit):
		units = dict()
		units['ms'] = 1.0
		units['seconds'] = 1000.0
		units['minutes'] = 1000.0 * 60

		return time * units[unit]

def main():
	cwd = os.getcwd()
	pattern = re.compile(r".*/logs/([^/]*)/([^/]*)/([^/]*)")

	i = 0

	print("%50s %6s %3s %8s %4s %4s %4s" % ("name", "method", "run", "time",
		"programInstructions", "sliceInstructions", "reveCalls"))
	for dirpath,_,_ in os.walk(cwd):
		match = pattern.match(dirpath)
		fileName = os.path.join(dirpath,"log")
		if (match and os.path.isfile(fileName)):
			method = match.group(1)
			name = match.group(2)
			run = match.group(3)

			parser = LogParser(fileName)

			print('%50s %6s %3s %8.1f %4i %4i %4i' % (name, method, run, parser.executionTime,
			parser.programInstructions, parser.sliceInstructions, parser.reveCalls))

#pandas.concat([smtData, problemData], axis=1, join_axes=[smtData.problem])
if __name__ == "__main__":
    main()