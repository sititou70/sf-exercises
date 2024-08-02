#!/bin/sh
set -eu
cd $(dirname $0)

coq_makefile -f _CoqProject -o Makefile
make
