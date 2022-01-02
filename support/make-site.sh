#!/usr/bin/env bash

cp _build/{html,site} -rv
mkdir -p _build/site/static/
cp ~/static/* _build/site/static/ -rv
cp /lib/node_modules/katex/dist/{katex.min.css,fonts} _build/site/css -rv