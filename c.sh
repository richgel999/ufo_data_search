#!/bin/bash
emcc -s ASSERTIONS=0 -O3 -fno-strict-aliasing miniz.c stem.c cmodule.cpp -s WASM=1 -o cmodule.js -Wno-switch -Wno-unused-value -s EXIT_RUNTIME=1 -s TOTAL_MEMORY=67108864 -s ALLOW_MEMORY_GROWTH=1 -s SINGLE_FILE=0 -s "EXPORTED_RUNTIME_METHODS=["UTF8ToString", "cwrap"]" --preload-file majestic.zip
