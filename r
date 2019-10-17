#!/bin/bash
# debug build
dmd -g -debug -J. -Jlibrary *.d ast/*.d util/*.d -ofpsi -L-fuse-ld=gold && time ./psi $@
# dmd -release -inline -J. -O *.d -ofprob && time ./prob $@
