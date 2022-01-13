#!/usr/bin/env sh

cp _build/html _build/site -rv
mkdir -p _build/site/static/ _build/site/css
cp /root/static/* _build/site/static/ -rv
cp /lib/node_modules/katex/dist/katex.min.css _build/site/css -rv
cp /lib/node_modules/katex/dist/fonts _build/site/css -rv