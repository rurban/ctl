#!/bin/sh

make -j16
make examples
sh gen_images.sh
