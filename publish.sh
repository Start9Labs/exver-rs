#!/bin/sh

set -e

cd `dirname "$BASH_SOURCE"`
wasm-pack build --release --target=bundler -- --features=wasm-bindgen
cp package.json pkg/package.json
cd pkg
npm publish