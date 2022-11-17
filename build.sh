#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

# Build and install Yices 2
pushd .
sudo apt-get install -y libgmp-dev gperf
git clone https://github.com/aman-goel/yices2.git
cd yices2
autoconf
./configure
make
sudo make install
pip install yices
popd

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

