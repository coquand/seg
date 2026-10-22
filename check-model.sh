#!/bin/sh
# The full check of seg/model in ONE process (the checking server, see segc):
# the tree is loaded once and every file-module is checked in import order;
# a module fails if a declaration fails or overruns, or if it takes 10 s or
# more.  About 1:40 instead of 23 min for the per-file runs (kept as
# check-model-perfile.sh).  The server is stopped afterwards (it holds
# several GB once everything is evaluated).
cd "$(dirname "$0")" || exit 2
./segc model all; r=$?
./segc model stop > /dev/null
exit $r
