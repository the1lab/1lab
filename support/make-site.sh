#!/usr/bin/env sh

rm -rf _build/site
cp _build/html _build/site -rv
mkdir -p _build/site/static/ _build/site/css
cp /root/static/* _build/site/static/ -rv
cp -L /lib/node_modules/katex/dist/katex.min.css _build/site/css -rv
cp -L /lib/node_modules/katex/dist/fonts _build/site/css -rv
