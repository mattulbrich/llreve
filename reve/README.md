### Reve

#### Prerequisites

LLVM and Clang 3.7.0 are required, other version probably won't work,
so make sure you have the right one.

##### Ubuntu 14.04

The following instructions assume you are root, if you are not prepend
sudo as necessary.

First we install some basic tools

```
apt-get install cmake wget
```

Now we need to add a repository for llvm

```
echo 'deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.7 main' >> /etc/apt/sources.list
echo 'deb-src http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.7 main' >> /etc/apt/sources.list
wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key|apt-key add -
apt-get update
```

Then we install clang

```
apt-get install clang-3.7 libclang-3.7-dev
ln -s /usr/bin/clang++-3.7 /usr/bin/clang++ # cmake looks for clang++
```

Finally we need two other dependencies, which are probably installed
on most systems, but for the sake of completeness

```
apt-get install libz-dev libedit-dev
```

##### Archlinux

Install clang and llvm using

```
pacman -S clang llvm llvm-libs
```

#### Build

```
mkdir build
cd build
cmake ..
make
```

#### Usage

Run using

```
./reve path/to/c/file1 path/to/c/file2
```
