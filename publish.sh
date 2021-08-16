#!/bin/sh

set -e

cd `dirname "$BASH_SOURCE"`
wasm-pack build --release --target=bundler -- --features=wasm-bindgen
cd pkg
jq '.name = "@start9labs/emver"' package.json > package.json.tmp
jq '.files[3] = "emver_bg.js"' package.json.tmp > package.json
npm publish