#!/usr/bin/env bash

# See: https://github.com/super-linter/super-linter/blob/dd82ec5c927bff0fecc98865b0be8aa6ef849001/docs/run-linter-locally.md
docker run --platform linux/amd64 \
  --env-file "$(pwd)/../.github/linters/super-linter.env" \
  --env-file "$(pwd)/../.github/linters/super-linter-local.env" \
  -e LOG_LEVEL=NOTICE \
  -e RUN_LOCAL=true \
  -e FIX_MARKDOWN="${FIX_MARKDOWN:-false}" \
  -e FIX_NATURAL_LANGUAGE="${FIX_NATURAL_LANGUAGE:-false}" \
  -e FIX_SPELL_CODESPELL="${FIX_SPELL_CODESPELL:-false}" \
  -v "$(pwd)/../":/tmp/lint \
  ghcr.io/super-linter/super-linter:latest
