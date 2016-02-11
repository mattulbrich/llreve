# Reve

## Prerequisites

LLVM and Clang 3.7.1 are required, other version probably won't work,
so make sure you have the right one.

## Ubuntu 14.04

### Compile llvm/clang against libc++

```
wget http://llvm.org/releases/3.7.1/clang+llvm-3.7.1-x86_64-linux-gnu-ubuntu-14.04.tar.xz
tar xvf clang+llvm-3.7.1-x86_64-linux-gnu-ubuntu-14.04.tar.xz
sudo cp -r clang+llvm-3.7.1-x86_64-linux-gnu-ubuntu-14.04/* /usr/local/
wget http://llvm.org/releases/3.7.1/llvm-3.7.1.src.tar.xz
tar xvf llvm-3.7.1.src.tar.xz
wget http://llvm.org/releases/3.7.1/cfe-3.7.1.src.tar.xz
tar xvf cfe-3.7.1.src.tar.xz
mv cfe-3.7.1.src llvm-3.7.1.src/tools/clang
sudo apt-get install cmake libstdc++-4.8-dev
export CC=clang
export CXX=clang++
cd llvm-3.7.1.src
mkdir build
cd build
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=/usr/local/  -DLLVM_ENABLE_LIBCXX=ON -DLLVM_ENABLE_LIBCXXABI=ON ..
sudo make install
```

### Building reve against the correct llvm

Make sure that /usr/local/bin is in your path and that `which clang++`
points to `/usr/local/bin/clang++`.

Then run

```
export CC=clang
export CXX=clang++
```

Then the usual build process aka

```
mkdir build
cd build
cmake ..
make
```

should work™. Make sure that you see the following line when running cmake
```
Using LLVMConfig.cmake in: /usr/local/share/llvm/cmake
```

## Archlinux

Install clang and llvm using

```
pacman -S clang llvm llvm-libs
```

## Build

```
mkdir build
cd build
cmake ..
make
```

## Usage

Run using

```
./reve path/to/c/file1 path/to/c/file2
```
