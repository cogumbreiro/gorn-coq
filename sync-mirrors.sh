#!/bin/bash
USER="$1"
[[ -z $USER ]] && USER=cogumbreiro
git push --mirror git@github.com:$USER/gorn-coq.git
