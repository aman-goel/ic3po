#!/bin/bash -x
# Make sure we exit if there is a failure
set -e

# Build and install Yices 2
pushd .
sudo apt-get install -y libgmp-dev gperf
cd yices2
autoconf
./configure
make
sudo make install
python2 -m pip install yices
popd

pushd .
python2 -m pip install $(pwd)/pysmt
cd pysmt
python2 install.py --force --z3 --confirm-agreement
python2 install.py --force --bdd
popd

pushd .
cd repycudd
make
repycuddPath=$(pwd)
echo "export PYTHONPATH=${repycuddPath}:\${PYTHONPATH}" >> ~/.bash_profile
source ~/.bash_profile
popd

pushd .
cd ivy
python2 setup.py install --user
popd

RETURN="$?"
if [ "${RETURN}" != "0" ]; then
    echo "Building dependencies failed!"
    exit 1
fi

