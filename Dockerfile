FROM ubuntu:14.04.3

# Install basic tools
RUN apt-get -y update && apt-get -y upgrade
RUN apt-get -y install cmake wget

# Add llvm repo and backports of newer libstdc++ versions
RUN apt-get -y install software-properties-common
RUN echo 'deb http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.7 main' >> /etc/apt/sources.list
RUN echo 'deb-src http://llvm.org/apt/trusty/ llvm-toolchain-trusty-3.7 main' >> /etc/apt/sources.list
RUN wget -O - http://llvm.org/apt/llvm-snapshot.gpg.key|apt-key add -
# RUN add-apt-repository -y ppa:ubuntu-toolchain-r/test
RUN apt-get update

# Install clang
RUN apt-get -y install clang-3.7 libclang-3.7-dev
RUN ln -s /usr/bin/clang++-3.7 /usr/bin/clang++

# Install newer libstdc++
# RUN apt-get -y install libstdc++-5-dev

# Install link dependencies
RUN apt-get -y install libz-dev libedit-dev

# Add actual source code
ADD reve /reve
RUN mkdir /reve/build

CMD cd /reve/build/ && cmake .. && make
