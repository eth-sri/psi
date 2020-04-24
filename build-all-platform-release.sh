#!/bin/bash
set -eu
rm psi psi-osx psi.exe ||:
sudo ./build-xosx-release.sh
./build-release.sh
./build-xwindows-release.sh
