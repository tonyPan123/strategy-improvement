#!/bin/sh
#
# Build and install everything SimSat needs into an opam switch.
#
# Verified on Ubuntu 24.04 (gcc 13.3, python 3.12) with OCaml 4.14.2.
#
# System packages assumed to be present:
#   opam libgmp-dev libmpfr-dev m4 pkg-config build-essential curl
#
# MathSAT is installed into /usr/local (this is where conf-mathsat and the
# ocaml-mathsat stubs look for it), so this script needs sudo for that step.

set -e

SWITCH=${SWITCH:-simsat}
OCAML_VERSION=${OCAML_VERSION:-4.14.2}
WORKDIR=${WORKDIR:-$(pwd)/_deps}
JOBS=${JOBS:-$(nproc)}

MATHSAT=mathsat-5.3.14-linux-x86_64
Z3_TAG=20180513
OCRS_TAG=20180427v3

mkdir -p "$WORKDIR"
cd "$WORKDIR"

# ---------------------------------------------------------------- opam switch
if ! opam switch list --short | grep -qx "$SWITCH"; then
    opam switch create "$SWITCH" "$OCAML_VERSION"
fi
eval $(opam env --switch="$SWITCH")

opam install -y batteries ppx_deriving ocamlgraph ounit menhir ocamlbuild \
                ocamlfind camlidl apron oasis num

PREFIX=$(opam var prefix)

# -------------------------------------------------------------------- MathSAT
# Version 5.3.14 specifically: the API changed incompatibly in 5.4.
if [ ! -f /usr/local/include/mathsat.h ]; then
    [ -d "$MATHSAT" ] || {
        curl -O "https://mathsat.fbk.eu/release/$MATHSAT.tar.gz"
        tar xzf "$MATHSAT.tar.gz"
    }
    sudo cp "$MATHSAT/include/"*.h /usr/local/include/
    sudo cp "$MATHSAT/lib/libmathsat.a" /usr/local/lib/
    sudo ldconfig
fi

# ------------------------------------------------------------- ocaml-mathsat
if ! ocamlfind query mathsat >/dev/null 2>&1; then
    [ -d ocaml-mathsat ] || git clone https://github.com/zkincaid/ocaml-mathsat.git
    cd ocaml-mathsat
    # `make all` also builds mathsat.cmxs, which cannot be linked against the
    # static libmathsat.a; the .cma/.cmxa that ark needs build fine.
    make _build/mathsat.cma _build/mathsat.cmxa
    make install
    cd ..
fi

# ------------------------------------------------------------------------ OCRS
# The 20180427v3 release installs as findlib `ocrs' and exposes a top-level
# `Ocrs' module, which is what ark/iteration.ml expects.  OCRS master installs
# as `OCRS' and wraps its modules, so it cannot be substituted here.
if ! ocamlfind query ocrs >/dev/null 2>&1; then
    [ -d "OCRS-$OCRS_TAG" ] || {
        curl -L -o "ocrs-$OCRS_TAG.tar.gz" \
             "https://github.com/cyphertjohn/OCRS/archive/$OCRS_TAG.tar.gz"
        tar xzf "ocrs-$OCRS_TAG.tar.gz"
    }
    cd "OCRS-$OCRS_TAG"
    ocaml setup.ml -configure --prefix "$PREFIX"
    ocaml setup.ml -build
    ocaml setup.ml -install
    cd ..
fi

# -------------------------------------------------------------------------- Z3
# zkincaid/z3 rather than upstream: ark/game.ml needs the interpolation API,
# which was removed from upstream Z3 after 4.5.
if ! ocamlfind query Z3 >/dev/null 2>&1; then
    [ -d "z3-$Z3_TAG" ] || {
        curl -L -o "z3-$Z3_TAG.tar.gz" \
             "https://github.com/zkincaid/z3/archive/$Z3_TAG.tar.gz"
        tar xzf "z3-$Z3_TAG.tar.gz"
    }
    cd "z3-$Z3_TAG"
    # The definitions of the proof_utils:: member functions are disabled in
    # this tree, but nothing else defines them, so libz3.so fails to link.
    sed -i 's|^#if 0 // ZK: *multiple defs|#if 1|' src/ast/proofs/proof_utils.cpp
    python3 scripts/mk_make.py --ml --prefix="$PREFIX"
    make -C build -j "$JOBS"
    make -C build install
    cd ..
fi

echo
echo "Dependencies installed.  Now run:"
echo "    eval \$(opam env --switch=$SWITCH)"
echo "    make"
