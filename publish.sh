#!/bin/sh

set -e

cd `dirname "$BASH_SOURCE"`
wasm-pack build --release --target=bundler -- --features=wasm-bindgen
cp emver.d.ts pkg/emver.d.ts
cd pkg
jq '.name = "@start9labs/emver"' package.json > package.json.tmp
mv package.json.tmp package.json
npm publish