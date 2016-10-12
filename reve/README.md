Regression Verification on LLVM
===============================

For a description of the technial isntallation and usage conditions, please refer to the README.md of the subdirectory reve.

----------

Idea
----

Given two programs which each implement a functionality (which may contain loops or recursive calls), the job of regression verification is to formally prove that both implementations behave equally (perfect equivalence) or that behave equally under a precondition (conditional eq) or that they behave equally in a defined way (relational eq).

To be independent of the used programming language, we implemented our approach on top of LLVM. In order to allow for conditional and relational equivalence, means of regression specifications have been added (see subdirectory reve for details).

It is a declared goal of LLReve to be an automatic tool, i.e., apart from the toplevel specifciation which says which equivalence relation is to be analysed, no further specification is required.

Assumptions and Limitations
---------------------------

While we build on top of LLVM, the techniques that we employ have properties which require us to make assumptions on the code to be regression verified and prevent us from supporting all features of LLVM.

**This section is subject to change!**

### Syntactical Limitations

Some language features cannot be encoded into our logical representations of the program. This includes datatypes and operations. We have two possibilities to act if an unsupported language feature occurs:

1. We report it to the user thus rejecting the input program (the result message is UNSUPPORTED)
2. We abstract away from datatypes and operations by replacing them with totally unknown values. In some cases this may allow the engine to find a proof, but whenever there is an impact on the result, this overapproximation may result in a false positive (yielding UNEQUAL plus a spurios counterexample).
3. In some cases we can abstract away from operations as if they were external functions with unknown implementation. This gives less counterexamples, but still may raise some.

Features which fall into this category:

- `float` or `double` are not supported. Currently, UNSUPPORTED is raised if they are encountered
- bitwise operations like `<<`, `&` etc. are only partially supported, UNSUPPORTED may be thrown.

Multiplication (even of integer types) is different: It's syntax is supported and we can encode it logically into the equivalence proof obligation, but the underlying solvers are unable to incorporate multiplication into the solutions they infer. Hence: No spurious counterexamples but often UNKNOWN.

### Semantical Assumptions

The beforementioned conditions can be checked syntactically and either the problem is rejected or one lives with false positives.

The following properties that programs need to have such that reve can deal with them are different as they cannot be checked by a simple syntax analysis but require a more thorough analysis. They are, however, the kind of properties which are typically successfully checkable by static functional verification tools like CBMC, LLBMC, CPA/Checker etc.

llreve works correctly if the following functional properties hold:

1. Every memory access reads from/writes to a memory location previously allocated -- regardless of the memory allocation strategy.
    - Pointer arithmethic does not go beyond the boundary of memory blocks allocated by a call to `malloc`. (This is a consequence of the above)
2. No integer operation ever causes an over-/underflow in its datatype.
    - Equivalent: All integer operations must yield the same results if performed on the mathematical integers.
    - There shall be a switch which relieves this assumptions at the cost of possibly getting more UNKNOWN results.

