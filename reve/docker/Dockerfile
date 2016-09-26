FROM alpine:3.4
MAINTAINER Moritz Kiefer <moritz.kiefer@purelyfunctional.org>
RUN apk add --no-cache cmake make git python binutils llvm-dev llvm-static llvm clang clang-dev gcc g++ zlib-dev
RUN git clone https://github.com/Z3Prover/z3.git /root/z3
WORKDIR /root/z3
RUN git checkout 8cf356224e08c872c6656eb7d2cf2c3422c6a2b2
RUN python contrib/cmake/bootstrap.py create
RUN mkdir -p build
WORKDIR /root/z3/build
RUN cmake -DUSE_OPENMP=OFF -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=/usr/local -DBUILD_LIBZ3_SHARED=OFF ..
RUN make
RUN make install
WORKDIR /root
