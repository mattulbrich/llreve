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

### Archlinux

Just install the packages from the repo and be happy that you have to
do way less work than everybody else.

### Windows

First of all you need to install `Visual Studio 2015` (other versions
may work but have not been tested). The free community edition is
enough for our purposes. Make sure to select the C++ toolchain during
the installation process.

Before we start building anything, download the
[`ninja` build system](https://github.com/ninja-build/ninja/releases)
and add the executable to your path. In `Powershell` you can do this
permanently via

```
[Environment]::SetEnvironmentVariable("Path", "$env:Path;C:\path\to\directory\containing\ninja\", "User")
```

From now on you should run everything from inside the `Developer
Command Prompt for VS2015` which you can find in the start menu.

You can now install LLVM & Clang via the usual installation procedure
using Ninja. (I’ll leave it up to you to translate the commands to
windows).

```
wget -c http://llvm.org/releases/3.8.0/llvm-3.8.0.src.tar.xz
wget -c http://llvm.org/releases/3.8.0/cfe-3.8.0.src.tar.xz
tar xvf llvm-3.8.0.src.tar.xz
tar xvf cfe-3.8.0.src.tar.xz
mkdir llvm-3.8.0.src/tools/clang
cp -r cfe-3.8.0.src/* llvm-3.8.0.src/tools/clang
cd llvm-3.8.0.src
mkdir build
cd build
cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=C:\Where\You\Want\To\Install\LLVM -GNinja
ninja
ninja install
```

Now you can install [Z3](https://github.com/Z3Prover/z3.git) from the
git master branch using the
[cmake](https://github.com/Z3Prover/z3/blob/master/README-CMake.md)
instructions. The important customizations here are `-GNinja` and
`-DCMAKE_INSTALL_PREFIX`, `-DBUILD_LIBZ3_SHARED=OFF`. You also need to make sure to set
`-DCMAKE_BUILD_TYPE=Release`.

Now that all dependencies are setup we can finally build `llreve`
using the usual cmake dance. Again you should use `-GNinja` and if
`Z3` is not detected, pass
`-DZ3_LIB=C:\Z3\Install_prefix\lib\libz3.lib` and
`-DZ3_INCLUDE_DIRS=C:\Z3\Install_prefix\include` to cmake.
