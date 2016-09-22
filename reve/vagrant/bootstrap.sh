#/usr/bin/bash
set -e
sudo add-apt-repository ppa:george-edison55/cmake-3.x
sudo add-apt-repository ppa:ubuntu-toolchain-r/test
sudo add-apt-repository 'deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.8 main'
wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key | sudo apt-key add -

sudo apt-get update -y
sudo apt-get upgrade -y
sudo apt-get install -y cmake g++-5 gcc-5 clang-3.8

# The llvm ubuntu/debian packages are completely fucked up, so we need
# to build it ourselves. Don’t blame me, blame silly debian packaging
# standards.

if [ ! -d "llvm-3.8.0.src" ]; then
    echo "llvm not found, downloading and cmaking"
    wget -c http://llvm.org/releases/3.8.0/llvm-3.8.0.src.tar.xz
    wget -c http://llvm.org/releases/3.8.0/cfe-3.8.0.src.tar.xz
    tar xvf llvm-3.8.0.src.tar.xz
    tar xvf cfe-3.8.0.src.tar.xz
    mkdir -p llvm-3.8.0.src/tools/clang
    cp -r cfe-3.8.0.src/* llvm-3.8.0.src/tools/clang
    cd llvm-3.8.0.src
    mkdir -p build
    cd build
    cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_COMPILER=clang++-3.8 -DCMAKE_C_COMPILER=clang-3.8 -DCMAKE_INSTALL_PREFIX=/usr/local
else
    cd llvm-3.8.0.src/build
fi
make -j4
sudo make install
cd ~

# Install z3 from git master
Z3_REV=e8f4dd76c21b52460b6bd95487183aea88749ce0
sudo apt-get install -y git
if [ ! -d "z3" ]; then
    git clone https://github.com/Z3Prover/z3.git
    cd z3
    git checkout "$Z3_REV"
    python contrib/cmake/bootstrap.py create
    mkdir -p build
    cd build
    cmake -DUSE_OPENMP=OFF -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=/usr/local -DBUILD_LIBZ3_SHARED=OFF -DCMAKE_CXX_COMPILER=clang++ -DCMAKE_C_COMPILER=clang ..
else
    cd z3/build
fi
make -j4
sudo make install
cd ~
