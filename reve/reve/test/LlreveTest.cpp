#include <gtest/gtest.h>
#include <memory>
#include <regex>

using std::string;

static std::string PathToTestExecutable;

static std::pair<int, std::string> exec(const std::string &cmd) {
    std::array<char, 128> buffer;
    std::string result;
    auto pipe = popen(cmd.c_str(), "r");
    if (!pipe)
        throw std::runtime_error("popen() failed!");
    while (!feof(pipe)) {
        if (fgets(buffer.data(), 128, pipe) != NULL)
            result += buffer.data();
    }
    int exitCode = pclose(pipe);
    return {exitCode, result};
}

enum class Solver { Z3, ELDARICA };
enum class ExpectedResult { EQUIVALENT, NOT_EQUIVALENT, UNKNOWN };

std::ostream &operator<<(::std::ostream &os, ExpectedResult result) {
    switch (result) {
    case ExpectedResult::EQUIVALENT:
        return os << "EQUIVALENT";
    case ExpectedResult::NOT_EQUIVALENT:
        return os << "NOT_EQUIVALENT";
    case ExpectedResult::UNKNOWN:
        return os << "UNKNOWN";
    }
}

ExpectedResult parseZ3Result(const std::string &output) {
    if (std::regex_search(output, std::regex("(^|\n)unsat"))) {
        return ExpectedResult::EQUIVALENT;
    }
    if (std::regex_search(output, std::regex("^sat"))) {
        return ExpectedResult::NOT_EQUIVALENT;
    }
    return ExpectedResult::UNKNOWN;
}

ExpectedResult parseEldResult(const std::string &output) {
    if (std::regex_search(output, std::regex("^sat"))) {
        return ExpectedResult::EQUIVALENT;
    }
    if (std::regex_search(output, std::regex("^unsat"))) {
        return ExpectedResult::NOT_EQUIVALENT;
    }
    return ExpectedResult::UNKNOWN;
}

class LlreveTest
    : public testing::TestWithParam<
          ::testing::tuple<std::string, std::string, ExpectedResult, Solver>> {
  protected:
    virtual void SetUp() {}
    virtual void TearDown() {}
};

TEST_P(LlreveTest, Llreve) {
    std::string directory;
    std::string fileName;
    ExpectedResult expectedResult;
    Solver solver;
    std::tie(directory, fileName, expectedResult, solver) = GetParam();
    fileName =
        PathToTestExecutable + "../../examples/" + directory + "/" + fileName;
    auto smtOutput = std::tmpnam(nullptr);
    std::ostringstream llreveCommand;
    llreveCommand << PathToTestExecutable << "llreve -inline-opts -o "
                  << smtOutput << " -I=" << PathToTestExecutable
                  << "../../examples/headers"
                  << " ";
    if (solver == Solver::Z3) {
        llreveCommand << "-muz ";
    }
    llreveCommand << fileName << "_1.c"
                  << " " << fileName << "_2.c";
    std::string llreveOutput;
    int exitCode;
    std::tie(exitCode, llreveOutput) = exec(llreveCommand.str());
    ASSERT_EQ(exitCode, 0);
    switch (solver) {
    case Solver::Z3: {
        std::ostringstream z3Command;
        z3Command << "z3 fixedpoint.engine=duality " << smtOutput;
        std::string z3Output;
        std::tie(exitCode, z3Output) = exec(z3Command.str());
        ASSERT_EQ(exitCode, 0);
        ASSERT_EQ(parseZ3Result(z3Output), expectedResult);
        break;
    }
    case Solver::ELDARICA:
        std::ostringstream eldCommand;
        eldCommand << "eld-client -hsmt " << smtOutput;
        std::string eldOutput;
        std::tie(exitCode, eldOutput) = exec(eldCommand.str());
        ASSERT_EQ(exitCode, 0);
        parseEldResult(eldOutput);
        break;
    }
    std::remove(smtOutput);
    EXPECT_EQ(0, 0);
}

INSTANTIATE_TEST_CASE_P(
    Loop, LlreveTest,
    testing::Combine(testing::Values("loop"),
                     testing::Values("barthe", "barthe2", "barthe2-big",
                                     "barthe2-big2", "break", "break_single",
                                     "bug15", "digits10_inl", "fib", "loop",
                                     "loop2", "loop3", "loop_unswitching",
                                     "nested-while", "simple-loop", "upcount",
                                     "while_after_while_if", "while-if"),
                     testing::Values(ExpectedResult::EQUIVALENT),
                     testing::Values(Solver::Z3, Solver::ELDARICA)));

INSTANTIATE_TEST_CASE_P(
    Faulty, LlreveTest,
    testing::Combine(testing::Values("faulty"),
                     testing::Values("ackermann!", "add-horn!", "barthe!",
                                     "inlining!", "limit1!", "limit2!",
                                     "loop5!", "nested-while!"),
                     testing::Values(ExpectedResult::NOT_EQUIVALENT),
                     testing::Values(Solver::Z3, Solver::ELDARICA)));

// This example cannot be solved by Z3. It can be solved when we instantiate the
// array in the custom precondition but Z3 issues a warning and it is unclear if
// that is actually handled correctly.
INSTANTIATE_TEST_CASE_P(
    HeapEldarica, LlreveTest,
    testing::Combine(testing::Values("heap"), testing::Values("cocome2"),
                     testing::Values(ExpectedResult::EQUIVALENT),
                     testing::Values(Solver::ELDARICA)));

INSTANTIATE_TEST_CASE_P(
    Heap, LlreveTest,
    testing::Combine(testing::Values("heap"),
                     testing::Values("clearstr", "fib", "heap_call", "memcpy_a",
                                     "memcpy_b", "propagate"),
                     testing::Values(ExpectedResult::EQUIVALENT),
                     testing::Values(Solver::Z3, Solver::ELDARICA)));

INSTANTIATE_TEST_CASE_P(
    Rec, LlreveTest,
    testing::Combine(testing::Values("rec"),
                     testing::Values("ackermann", "add-horn", "cocome1",
                                     "inlining", "limit1unrolled", "limit2",
                                     "limit3", "loop_rec", "mccarthy91",
                                     "rec_while", "triangular"),
                     testing::Values(ExpectedResult::EQUIVALENT),
                     testing::Values(Solver::Z3, Solver::ELDARICA)));

INSTANTIATE_TEST_CASE_P(
    Libc, LlreveTest,
    testing::Combine(testing::Values("libc"),
                     testing::Values("memccpy_1", "memchr_1", /* "memmem_1", */
                                     "memmove_1", "memrchr_1", "memset_1",
                                     "sbrk_1", "stpcpy_1", "strcmp",
                                     /* "strcspn_2", "strcspn_3", */
                                     /* "strncasecmp_1", */ "strncmp_2",
                                     "strncmp_3",
                                     /* "strpbrk_1", */ /* "strpbrk_2", */
                                     "strpbrk_3" /* "swab" */),
                     testing::Values(ExpectedResult::EQUIVALENT),
                     testing::Values(Solver::Z3, Solver::ELDARICA)));

static std::string getDirectory(std::string filePath) {
    auto pos = filePath.rfind('/');
    if (pos != std::string::npos) {
        filePath = filePath.substr(0, pos) + "/";
    }
    std::cout << filePath << "\n";
    return filePath;
}

int main(int argc, char **argv) {
    PathToTestExecutable = getDirectory(argv[0]);
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
