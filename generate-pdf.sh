#!/bin/sh
make all
make COQDOCFLAGS="-g -l --no-lib-name --toc-depth 0 " all.pdf
