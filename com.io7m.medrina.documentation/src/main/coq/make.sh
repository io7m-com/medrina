#!/bin/sh -ex

coqc -Q Medrina Medrina Medrina/ListExtras.v
coqc -Q Medrina Medrina Medrina/Forall.v
coqc -Q Medrina Medrina Medrina/Medrina.v

mkdir -p html

coqdoc -Q Medrina Medrina --parse-comments --utf8 -d html Medrina/*.v
