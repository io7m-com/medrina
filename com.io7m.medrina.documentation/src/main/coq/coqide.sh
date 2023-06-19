#!/bin/sh

# XXX: Write a Coq maven plugin.
LANARK_DIRECTORY="../../../target/Lanark/com"

COQ_DIRECTORIES="-Q Medrina Medrina -Q ${LANARK_DIRECTORY} com"

exec coqide ${COQ_DIRECTORIES} "$@"
