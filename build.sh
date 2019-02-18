#!/bin/bash
set -e
NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.07.1+flambda"
SPARROW_OPAM_SWITCH=sparrow-"$OCAML_VERSION"
opam init --compiler=$OCAML_VERSION -j $NCPU --no-setup --yes

switch_exists=no
for installed_switch in $(opam switch list --short); do
  if [[ "$installed_switch" == "$SPARROW_OPAM_SWITCH" ]]; then
    switch_exists=yes
    break
  fi
done
if [ "$switch_exists" = "no" ]; then
  opam switch create $SPARROW_OPAM_SWITCH $OCAML_VERSION
fi

eval $(SHELL=bash opam config env --switch=$SPARROW_OPAM_SWITCH)
opam install depext --yes
opam pin add cil https://github.com/KihongHeo/cil.git -n --yes
opam pin add sparrow . -n --yes
opam depext apron
opam install -j $NCPU sparrow --yes --deps-only
opam pin remove sparrow
./configure --enable-tests
make
