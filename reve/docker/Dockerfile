FROM ubuntu:16.04
MAINTAINER Moritz Kiefer <moritz.kiefer@purelyfunctional.org>
ENV LLVM_VERSION 3.9.0
RUN apt-get update && \
    apt-get install -y \
      cmake \
      curl \
      g++ \
      gcc \
      ninja-build \
      python \
      xz-utils
RUN curl -SL http://llvm.org/releases/$LLVM_VERSION/llvm-$LLVM_VERSION.src.tar.xz | tar xJ
RUN curl -SL http://llvm.org/releases/$LLVM_VERSION/cfe-$LLVM_VERSION.src.tar.xz | tar xJ && \
    mv cfe-$LLVM_VERSION.src llvm-$LLVM_VERSION.src/tools/clang
RUN mkdir /llvm-$LLVM_VERSION.src/build
WORKDIR /llvm-$LLVM_VERSION.src/build
RUN cmake .. -GNinja \
             -DCMAKE_BUILD_TYPE=Release \
             -DLLVM_ENABLE_ASSERTIONS=ON \
             -DCMAKE_INSTALL_PREFIX=/usr/local \
             -DLLVM_PARALLEL_LINK_JOBS=1
RUN ninja && ninja install
WORKDIR /
RUN rm -r /llvm-$LLVM_VERSION.src
ENV Z3_VERSION 4.5.0
RUN curl -SlL https://github.com/Z3Prover/z3/archive/z3-$Z3_VERSION.tar.gz | tar xz
RUN mkdir /z3-z3-$Z3_VERSION/build
WORKDIR /z3-z3-$Z3_VERSION
RUN python contrib/cmake/bootstrap.py create
WORKDIR /z3-z3-$Z3_VERSION/build
RUN cmake .. -GNinja \
             -DCMAKE_BUILD_TYPE=Release \
             -DCMAKE_INSTALL_PREFIX=/usr/local \
             -DBUILD_LIBZ3_SHARED=OFF \
             -DUSE_OPENMP=FALSE
RUN ninja && ninja install
WORKDIR /
RUN rm -r /z3-z3-$Z3_VERSION
