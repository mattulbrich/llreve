# Reve

## Prerequisites

LLVM and Clang 3.8.0 are required, other version probably won't work,
so make sure you have the right one.

## Ubuntu 14.04

### Compile llvm/clang against libc++

```
wget http://llvm.org/releases/3.8.0/clang+llvm-3.8.0-x86_64-linux-gnu-ubuntu-14.04.tar.xz
tar xvf clang+llvm-3.8.0-x86_64-linux-gnu-ubuntu-14.04.tar.xz
sudo cp -r clang+llvm-3.8.0-x86_64-linux-gnu-ubuntu-14.04/* /usr/local/
wget http://llvm.org/releases/3.8.0/llvm-3.8.0.src.tar.xz
tar xvf llvm-3.8.0.src.tar.xz
wget http://llvm.org/releases/3.8.0/cfe-3.8.0.src.tar.xz
tar xvf cfe-3.8.0.src.tar.xz
mv cfe-3.8.0.src llvm-3.8.0.src/tools/clang
sudo apt-get install cmake libstdc++-4.8-dev
export CC=clang
export CXX=clang++
cd llvm-3.8.0.src
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

## OpenSuse 13.2

Take a look at the reve/opensuse directory.
There is a vagrantfile which downloads the correct immage, however you still need to manually install llvm inside of that. Take a look at `bootstrap.sh` for the commands you need for that.

Now you can simply run `./build.sh` and a static binary will be
built. You can then just copy `reve/build/reve` to a more convenient
place. Repeat that every time you want a new binary.

## Build

This currently requires libc++, if anybody is motivated to dive into
cmake and figure out how to make it generic, be my guest.

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
