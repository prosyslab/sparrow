#!/bin/bash
set -e

export OPAMYES=1

NCPU="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 1)"
OCAML_VERSION="4.13.1"
SPARROW_OPAM_SWITCH=sparrow-"$OCAML_VERSION"+flambda
SPARROW_OPAM_SWITCH_OPTION="--package=ocaml-variants.${OCAML_VERSION}+options,ocaml-option-flambda"

USER_OPAM_SWITCH=no

function usage() {
  echo "Usage: $0 [options]"
  echo
  echo " options:"
  echo "   -h,--help             show this message"
  echo "   --user-opam-switch    use the current opam switch to install haechi (default: $OPAM_SWITCH)"
  echo
  echo " examples:"
  echo "    $0                     # build haechi with default options"
  echo "    $0 --user-opam-switch  # build haechi in the current opam switch (e.g., for Github CI)"
}

while [[ $# -gt 0 ]]; do
  opt_key="$1"
  case $opt_key in
    --user-opam-switch)
      USER_OPAM_SWITCH=yes
      shift
      continue
      ;;
  esac
done

function setup_opam() {
  opam init --reinit --bare --no-setup

  switch_exists=no
  for installed_switch in $(opam switch list --short); do
    if [[ "$installed_switch" == "$SPARROW_OPAM_SWITCH" ]]; then
      switch_exists=yes
      break
    fi
  done
  if [ "$switch_exists" = "no" ]; then
    opam switch create $SPARROW_OPAM_SWITCH_OPTION $SPARROW_OPAM_SWITCH
  else
    opam switch $SPARROW_OPAM_SWITCH
  fi

  eval $(SHELL=bash opam config env --switch=$SPARROW_OPAM_SWITCH)
}

if [ "$USER_OPAM_SWITCH" == "no" ]; then
  setup_opam
fi

echo -e "\e[31m[NOTE]\e[0m If you are not a sudo user, press Ctrl+D and skip installing system libraries. Contact the sysadmin, if they are not installed."
opam install apron || echo "Skip system library install"
opam pin add prosys-cil https://github.com/prosyslab/cil.git -n
opam pin add claml https://github.com/prosyslab/claml.git -n
opam pin add sparrow . -n
opam install -j $NCPU sparrow --deps-only
opam pin remove sparrow
# development packages
opam install -j $NCPU ocamlformat.0.24.1 merlin ocp-index ocp-indent ocaml-lsp-server
make
