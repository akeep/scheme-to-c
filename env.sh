#!/bin/sh
# ref: https://datagrok.org/python/activate/
export CHEZSCHEMELIBDIRS="$PWD:$PWD/nanopass-framework-scheme/::"
unset CHEZSCHEMELIBEXTS

exec "${@:-$SHELL}"
