# llrêve

## Usage

The inputs to llrêve are two C source files. Most of the C language
the preprocessor are supported. Notable exceptions are bit operations
and floating points.

There are two (mostly orthogonal) ways to customize the behavior of llrêve:

### CLI Arguments

For a complete list and an explanations of the different options run
  `llreve --help`.

### Annotations in the source code

These annotations can be separated into function calls of special
intrinsics and comments of specific forms.

#### Intrinsic functions

- `__mark`

This function is called with a single integer argument. The points in
the programs where both programs call this function with the same
argument are used for creating the coupling predicates. If these marks
are placed manually they have to break all cycles in the CFG.

- `__splitmark`

This is almost identical to `__mark` but the call to `__splitmark`
ends up in a basic block on its own. This is mostly useful when
multiple marks are in in a program segement without cycles.

- `__inlineCall`

Inline the call wrapped by `__inlineCall`.


#### Special comments

- `/*@ opt arguments @*/`

This allows specifying commandline options directly in the source via
`arguments`. This is mostly useful in the webinterface where this is
the only way to specify cli args.

- /*@ rel_in arg @*/

Replace the input relation (equality by default) by `arg`. `arg` needs
to be valid SMT (this is currently not checked). A function parameter called `n`
in program `i` can be accessed via the SMT variable `n$i_0`

- /*@ rel_out arg @*/

Replace the output relation (equality by default) by `arg`. `arg`
needs to be valid SMT (this is currently not checked). The two return
values can be accessed via the SMT variable `ret$1` and `ret$2`.

- /*@ pre arg @*/

Add `arg` conjunctively to the input relation. `arg` needs to be valid
SMT (this is currently not checked). A function parameter called `n`
in program `i` can be accessed via the SMT variable `n$i_0`.

- /*@ addfuncond function cond @*/

Add `cond` conjunctively to the output of the specification for an
extern function.

#### Other annotations
` __attribute__((always_inline))`

## Installation

### Prerequisites

LLVM and Clang 3.8.0 are required, other version probably won't work,
so make sure you have the right one.
Also you need to build z3 from the master branch

### Vagrant

If you don’t want to mess with your system and are not familiar with
the LLVM build process you can build the vagrant image.
To do so, execute the following commands:

```
cd reve/vagrant
vagrant up
# This will take a long time since it builds llvm & clang but this is a one time process.
```

After that you can either run `vagrant ssh` and work inside of the vm
or execute `build.sh` to build static binaries which can be used for
the webinterface.

### Docker

There is a docker image in `reve/docker` based on
[Alpine Linux](https://alpinelinux.org/) which is great for static
linking. It has the big advantage over vagrant that Alpine includes
working packages of Clang & LLVM so the docker image builds a lot
faster than the corresponding vagrant image. I won’t explain Docker
here so please consult the
[official documentation](https://docs.docker.com/engine/getstarted/).

### Ubuntu/Debian

Ubuntu & Debian completely messed up the cmake config so both the
packages provided by the distros as well as the packages provided by
llvm.org are unusable.

The easiest solution to this problem is probably to insult the package
maintainers until they stop messing with upstream packages and just
distribute them like they are intended.

### Arch
Just install the packages from the repo and be happy that you have to do way less work than everybody else.
