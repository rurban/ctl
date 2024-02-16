#!/bin/sh
set -e
make -j9
make -j4 CXX='g++ -std=c++03' CFLAGS=-I.
make -j4 CXX='g++ -std=c++11' CFLAGS=-I.
make -j4 CXX='g++ -std=c++17' CFLAGS=-I.
make -j4 CXX='g++ -std=c++20' CFLAGS=-I.
make -j4 CXX='g++ -std=c++23' CFLAGS=-I.
make -j9 LONG=1 O0=1 SANITIZE=1
make -j9 LONG=1 O1=1 SANITIZE=1
make -j9 LONG=1 O2=1 SANITIZE=1
make -j9 LONG=1 O3=1 SANITIZE=1
make -j9 LONG=1 Og=1 SANITIZE=1
make -j9 LONG=1 Os=1 SANITIZE=1
make -j9 DEBUG=1
make -j9 LONG=1 Ofast=1
make -j9 LONG=1 O0=1 SANITIZE=0
make -j9 LONG=1 O1=1 SANITIZE=0
make -j9 LONG=1 O2=1 SANITIZE=0
make -j9 LONG=1 O3=1 SANITIZE=0
make -j9 LONG=1 Og=1 SANITIZE=0
make -j9 LONG=1 Os=1 SANITIZE=0
make -j9 LONG=1 Ofast=1 SANITIZE=0
make -j9 CC=gcc\ -std=c99
make -j9 CC=gcc\ -std=c11
make -j9 CC=gcc\ -std=c17
make -j9 CC=gcc\ -std=c2x
make -j9 CXX='clang++ -stdlib=libc++'
make -j9 CXX='clang++ -std=c++11 -stdlib=libc++'
make -j9 CXX='clang++ -std=c++17 -stdlib=libc++'
make -j9 CXX='clang++ -std=c++20 -stdlib=libc++'
make -j9 CXX='clang++ -std=c++23 -stdlib=libc++'
make -j9 CC=clang CXX='clang++ -std=c++11'
make -j9 CC=clang CXX='clang++ -std=c++17'
make -j9 CC=clang CXX='clang++ -std=c++20'
make -j9 CC=clang CXX='clang++ -std=c++23'
make examples SANITIZE=1
make examples SANITIZE=0
