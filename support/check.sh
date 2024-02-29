#!/usr/bin/env bash

set -eo pipefail

# Slightly hacky script to generate _build/all-pages.agda and check it,
# possibly with a specified version of Agda (use the AGDA environment
# variable).

unsorted="$(mktemp)"
agda="${AGDA:-agda}"

if ! type "${agda}" &>/dev/null; then
  echo "${agda} is not executable. Either add it to your path or set \$AGDA."
  exit 1
else
  echo ">>> Checking with ${agda} ($(type "${agda}"))"
fi

add-module () {
  echo "$1"                             | \
    # Remove the leading `src/`, and turn slashes into dots
    sed -re 's@^src/@@;s@/@.@g'         | \

    # Remove the trailing file extension
    sed -re 's@(\.lagda\.md|\.agda)$@@' | \

    # Make this into an import
    sed -re 's@^@open import @'         >> ${unsorted}
}

echo ">>> Building _build/all-pages.agda"

git ls-files --full-name src/ | while IFS='' read file; do
  if echo "${file}" | egrep "l?agda(.md)?$" >/dev/null; then
    printf '.'
    add-module "${file}"
  fi
done

# Sort the all-pages file to mimic what we would get with a proper
# build, call the provided executable.

printf '\n>>> Checking %s modules\n' "$(wc -l "${unsorted}" | cut -d' ' -f1)"

sort "${unsorted}" > _build/all-pages.agda
rm "${unsorted}"

${AGDA:-agda} _build/all-pages.agda --trace-imports=3 ${AGDAFLAGS}
