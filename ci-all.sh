#!/bin/sh
set -e
make -j9
make -j9 LONG=1 O0=1 SANITIZE=1
make -j9 LONG=1 O1=1 SANITIZE=1
make -j9 LONG=1 O2=1 SANITIZE=1
make -j9 LONG=1 O3=1 SANITIZE=1
make -j9 LONG=1 Og=1 SANITIZE=1
make -j9 LONG=1 Os=1 SANITIZE=1
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
make examples SANITIZE=1
make examples SANITIZE=0
make -j9 CC=clang CXX=clang++
