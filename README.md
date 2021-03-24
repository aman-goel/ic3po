# IC3PO

<img align="right" width="100" height="auto" src="logo.png">
</img>

**IC3** for **P**r**o**ving **P**r**o**tocol **P**r**o**perties

> Copyright (c) 2021  Aman Goel [(amangoel@umich.edu)](amangoel@umich.edu)  and  Karem Sakallah [(karem@umich.edu)](karem@umich.edu) , University of Michigan

Reads a parameterized distributed protocol and performs property checking

#### Installation
Clone the repository and:
- run ```` git submodule update --init --recursive ```` to clone submodules
- run ```` ./build.sh ```` from the project folder to install dependencies

#### Usage
	python2 ic3po.py -o <output-path> -n <test-name> <path>/<file>.ivy
	(check the output in <output-path>/<test-name>)
	 
	Example:	python2 ic3po.py -o foo -n bar ivybench/ex/ivy/toy_consensus.ivy
				(check the output in foo/bar)

#### ic3po Tool Flow
![Image of ic3po toolflow](ic3po_toolflow.png)

#### License
Copyright (c) 2021  Aman Goel and Karem Sakallah, University of Michigan. All rights reserved.

IC3PO is available for research and evaluation purposes only.
IC3PO is provided as is, without any warranty.
Any usage of IC3PO needs to comply with the usage terms as detailed in the file [COPYING](https://github.com/aman-goel/ic3po/blob/master/COPYING).


We would be glad to hear from you and help you in the case you are having a difficulty in using IC3PO

Please report bugs and share your usage experience via email  [(amangoel@umich.edu)](amangoel@umich.edu) or on github [(https://github.com/aman-goel/ic3po)](https://github.com/aman-goel/ic3po)
