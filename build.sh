#!/bin/bash
set -e

export OPAMYES=1

NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.08.0+flambda"
SPARROW_OPAM_SWITCH=sparrow-"$OCAML_VERSION"
opam init --compiler=$OCAML_VERSION -j $NCPU --no-setup

switch_exists=no
for installed_switch in $(opam switch list --short); do
  if [[ "$installed_switch" == "$SPARROW_OPAM_SWITCH" ]]; then
    switch_exists=yes
    break
  fi
done
if [ "$switch_exists" = "no" ]; then
  opam switch create $SPARROW_OPAM_SWITCH $OCAML_VERSION
else
  opam switch $SPARROW_OPAM_SWITCH
fi

eval $(SHELL=bash opam config env --switch=$SPARROW_OPAM_SWITCH)
opam install depext
opam depext apron clangml
opam pin add cil https://github.com/prosyslab/cil.git -n
opam pin add sparrow . -n
opam install -j $NCPU sparrow --deps-only
opam pin remove sparrow
make
