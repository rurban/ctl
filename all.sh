#!/bin/sh

make -j16 O3=1
make examples O3=1
sh gen_images.sh
