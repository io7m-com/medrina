#!/bin/sh -ex

# XXX: Write a Coq maven plugin.
LANARK_DIRECTORY="../../../target/Lanark/com"

COQ_DIRECTORIES="-Q Medrina Medrina -Q ${LANARK_DIRECTORY} com"

coqc ${COQ_DIRECTORIES} ${LANARK_DIRECTORY}/io7m/lanark/core/Lanark.v
coqc ${COQ_DIRECTORIES} Medrina/Names.v
coqc ${COQ_DIRECTORIES} Medrina/Attributes.v
coqc ${COQ_DIRECTORIES} Medrina/Roles.v
coqc ${COQ_DIRECTORIES} Medrina/Subjects.v
coqc ${COQ_DIRECTORIES} Medrina/Objects.v
coqc ${COQ_DIRECTORIES} Medrina/Actions.v
coqc ${COQ_DIRECTORIES} Medrina/Matches.v
coqc ${COQ_DIRECTORIES} Medrina/Rules.v
coqc ${COQ_DIRECTORIES} Medrina/Policies.v

mkdir -p html

coqdoc ${COQ_DIRECTORIES} --toc --utf8 -d html Medrina/*.v
