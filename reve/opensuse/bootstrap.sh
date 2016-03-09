sudo zypper up
# restart to load new vbox guest extensions
wget http://llvm.org/releases/3.8.0/clang+llvm-3.8.0-x86_64-opensuse13.2.tar.xz
wget http://llvm.org/releases/3.8.0/llvm-3.8.0.src.tar.xz
wget http://llvm.org/releases/3.8.0/cfe-3.8.0.src.tar.xz
wget http://llvm.org/releases/3.8.0/libcxx-3.8.0.src.tar.xz
wget http://llvm.org/releases/3.8.0/libcxxabi-3.8.0.src.tar.xz
tar xvf clang+llvm-3.8.0-x86_64-opensuse13.2.tar.xz
sudo cp -r clang+llvm-3.8.0-x86_64-opensuse13.2/* /usr/local/
tar xvf llvm-3.8.0.src.tar.xz
tar xvf cfe-3.8.0.src.tar.xz
mv cfe-3.8.0.src llvm-3.8.0.src/tools/clang
tar xvf libcxx-3.8.0.src.tar.xz
mv libcxx-3.8.0.src llvm-3.8.0.src/projects/libcxx
tar xvf libcxxabi-3.8.0.src.tar.xz
mv libcxxabi-3.8.0.src llvm-3.8.0.src/projects/libcxxabi
cd llvm-3.8.0.src
mkdir build
cd build
sudo zypper install -n cmake
export CC=clang
export CXX=clang++
sudo zypper install -n libstdc++-devel
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=/usr/local/  -DLLVM_ENABLE_LIBCXX=ON -DLLVM_ENABLE_LIBCXXABI=ON -DLIBCXX_ENABLE_SHARED=OFF ..
make -j4
# Yes you really need to build another time because otherwise make install complains
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=/usr/local/  -DLLVM_ENABLE_LIBCXX=ON -DLLVM_ENABLE_LIBCXXABI=ON -DLIBCXX_ENABLE_SHARED=ON ..
make -j4
sudo make install
sudo zypper install -n glibc-static
