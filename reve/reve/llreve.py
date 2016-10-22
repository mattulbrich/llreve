# run with python2

# You need to add reve, eld-client and z3 to your path before you execute this.

# return values and their explanation
# EQUAL             | The two programs have been proved equivalent.
# NOT_EQUAL         | The two programs are not equivalent for the used coupling.
# UNKNOWN           | The solver returned UNKNOWN.
# UNSUPPORTED_INPUT | llreve cannot translate the input to SMT, this could also mean that llreve has crashed.
# INTERNAL_ERROR    | The solver crashed or returned an error because SMT produced by llreve was invalid.

import subprocess
import sys

verboseOpt = False
z3Opt = False


def log(s):
    if verboseOpt:
        print(s)


# Like index but returns -1 instead of throwing an exception when the
# item is not in the list
def safeIndex(l, item):
    index = -1
    try:
        index = l.index(item)
    except ValueError:
        index = -1
    return index


def detectZ3Option():
    # We use eldarica except when -z3 or --z3 is passed. We don't use
    # a proper commandline parser because all most commands should be
    # passed to llreve.
    global z3Opt
    if safeIndex(sys.argv, "-z3") >= 0:
        sys.argv.remove("-z3")
        z3Opt = True
    if safeIndex(sys.argv, "--z3") >= 0:
        sys.argv.remove("--z3")
        z3Opt = True


def detectVerboseOption():
    if safeIndex(sys.argv, "-v") >= 0:
        sys.argv.remove("-v")
        global verboseOpt
        verboseOpt = True


def detectOptions():
    detectZ3Option()
    detectVerboseOption()


def runProcess(args):
    log("Running %s" % args)
    stdout = None
    stderr = None
    if not verboseOpt:
        stdout = open('/dev/null', 'w')
        stderr = open('/dev/null', 'w')
    return subprocess.call(args, stdout=stdout, stderr=stderr)


def llreve(fileName):
    log("Running llreve")
    args = ["reve"] + sys.argv[1:]
    if (z3Opt):
        args.append("-muz")
    args.append("-o")
    args.append(fileName)
    return runProcess(args)


def getSMTFileName():
    return "out.smt2"


def z3(fileName):
    log("Running z3")
    args = ["z3", "fixedpoint.engine=duality", fileName]
    if verboseOpt:
        args.append("-v:1")
    process = subprocess.Popen(args, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
    result = "INTERNAL_ERROR"
    for line in iter(process.stdout.readline, ''):
        if verboseOpt:
            sys.stdout.write(line)
        line = line.strip()
        if line == "sat":
            result = "NOT_EQUAL"
        elif line == "unsat":
            result = "EQUAL"
        elif line == "unknown":
            result = "UNKNOWN"
    process.wait()
    if process.returncode == 0:
        return result
    return "INTERNAL_ERROR"


def eldarica(fileName):
    log("Running Eldarica")
    args = ["eld-client", fileName]
    if verboseOpt:
        args.append("-log")
    process = subprocess.Popen(args, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)
    result = "INTERNAL_ERROR"
    for line in iter(process.stdout.readline, ''):
        if verboseOpt:
            sys.stdout.write(line)
        line = line.strip()
        if line == "sat":
            result = "EQUAL"
        elif line == "unsat":
            result = "NOT_EQUAL"
        elif line == "unknown":
            result = "UNKNOWN"
    process.wait()
    if process.returncode == 0:
        return result
    return "INTERNAL_ERROR"


def main():
    detectZ3Option()
    detectVerboseOption()
    smtFileName = getSMTFileName()
    exit = llreve(smtFileName)
    if exit != 0:
        print("UNSUPPORTED_INPUT")
        return
    if z3Opt:
        ret = z3(smtFileName)
        print(ret)
    else:
        ret = eldarica(smtFileName)
        print(ret)


if __name__ == "__main__":
    main()
