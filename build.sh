#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

pushd .
pip install $(pwd)/pysmt
cd pysmt
python2 install.py --force --z3 --confirm-agreement
popd

pushd .
cd ivy
python2 setup.py install
popd

RETURN="$?"
if [ "${RETURN}" != "0" ]; then
    echo "Building dependencies failed!"
    exit 1
fi

