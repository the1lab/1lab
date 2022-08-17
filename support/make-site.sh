#!/usr/bin/env sh

rm -rf _build/site
cp _build/html _build/site -rvf
mkdir -p _build/site/static/ _build/site/css
cp /root/static/* _build/site/static/ -rvf
cp /root/css/* _build/site/css -rvf
