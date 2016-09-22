# Reve

## Prerequisites

LLVM and Clang 3.8.0 are required, other version probably won't work,
so make sure you have the right one.
Also you need to build z3 from the master branch

## Vagrant

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

## Ubuntu/Debian

Ubuntu & Debian completely messed up the cmake config so both the
packages provided by the distros as well as the packages provided by
llvm.org are unusable.

The easiest solution to this problem is probably to insult the package
maintainers until they stop messing with upstream packages and just
distribute them like they are intended.

## Arch
Just install the packages from the repo and be happy that you have to do way less work than everybody else.
