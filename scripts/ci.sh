#!/usr/bin/env bash
# Build detlog2 with plain GHC (base, containers, process, directory only) and run the tests.
set -euo pipefail
cd "$(dirname "$0")/.."
ghc --version
mkdir -p build
ghc -O1 -Wall -Wno-incomplete-uni-patterns -Wno-name-shadowing -Wno-unused-do-bind \
    -isrc -outputdir build -o build/detlog2 app/Main.hs
if [ -f tests/Spec.hs ]; then
  ghc -O0 -isrc -outputdir build/t -o build/spec tests/Spec.hs
  ./build/spec
fi
if [ -f tests/cli.sh ]; then bash tests/cli.sh; fi
