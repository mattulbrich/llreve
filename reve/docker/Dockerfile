FROM ubuntu:16.04
MAINTAINER Moritz Kiefer <moritz.kiefer@purelyfunctional.org>
ENV LLVM_VERSION 3.9.0
ENV Z3_VERSION 4.5.0
RUN apt-get update && \
    apt-get install -y \
      bison \
      cmake \
      curl \
      flex \
      g++ \
      gcc \
      git \
      libgmp-dev \
      ninja-build \
      python \
      xz-utils && \
    rm -rf /var/lib/apt/lists/*
RUN curl -SL http://llvm.org/releases/$LLVM_VERSION/llvm-$LLVM_VERSION.src.tar.xz | tar xJ && \
    curl -SL http://llvm.org/releases/$LLVM_VERSION/cfe-$LLVM_VERSION.src.tar.xz | tar xJ && \
    mv cfe-$LLVM_VERSION.src llvm-$LLVM_VERSION.src/tools/clang && \
    mkdir /llvm-$LLVM_VERSION.src/build && \
    cd /llvm-$LLVM_VERSION.src/build && \
    cmake .. -GNinja \
             -DCMAKE_BUILD_TYPE=Release \
             -DLLVM_ENABLE_ASSERTIONS=ON \
             -DCMAKE_INSTALL_PREFIX=/usr/local \
             -DLLVM_PARALLEL_LINK_JOBS=1 \
             -DLLVM_TARGETS_TO_BUILD=X86 && \
    ninja && ninja install && \
    rm -r /llvm-$LLVM_VERSION.src
RUN curl -SL https://github.com/Z3Prover/z3/archive/z3-$Z3_VERSION.tar.gz | tar xz && \
    mkdir /z3-z3-$Z3_VERSION/build && \
    cd /z3-z3-$Z3_VERSION && \
    python contrib/cmake/bootstrap.py create && \
    cd /z3-z3-$Z3_VERSION/build && \
    cmake .. -GNinja \
             -DCMAKE_BUILD_TYPE=Release \
             -DCMAKE_INSTALL_PREFIX=/usr/local \
             -DBUILD_LIBZ3_SHARED=OFF \
             -DUSE_OPENMP=FALSE && \
    ninja && ninja install && \
    rm -r /z3-z3-$Z3_VERSION
