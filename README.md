<img align="right" width="100" height="auto" src="logo.png">
</img>

# IC3PO

**IC3** for **P**r**o**ving **P**r**o**tocol **P**r**o**perties

> Copyright (c) 2021  Aman Goel [(amangoel@umich.edu)](amangoel@umich.edu)  and  Karem Sakallah [(karem@umich.edu)](karem@umich.edu) , University of Michigan

Reads a parameterized distributed protocol and performs property checking

#### Research Papers
- [[NFM'21](https://link.springer.com/chapter/10.1007/978-3-030-76384-8_9)]  IC3PO paper
- [[arXiv'21](https://arxiv.org/abs/2103.14831)]   Extended version of IC3PO paper

#### Research Talks
- [[YouTube](https://youtu.be/e0pr3P2BrEU)] IC3PO presented at NFM'21
- [[YouTube](https://www.youtube.com/watch?v=-da_iG9LQgk)] IC3PO presented at Simons Institute

#### Installation
Clone the repository and:
- run ```` git submodule update --init --recursive ```` to clone submodules
- run ```` ./build.sh ```` from the project folder to install dependencies

#### Usage
	python2 ic3po.py -o <output-path> -n <test-name> <path>/<file>.ivy
	(check the output in <output-path>/<test-name>)
	 
	Example:	python2 ic3po.py -o foo -n bar ivybench/ex/ivy/toy_consensus.ivy
				(check the output in foo/bar)

#### IC3PO Tool Flow
<img align="center" width="700" height="auto" src="ic3po.png">
</img>

#### Output
IC3PO creates a directory ```<output-path>/<test-name>``` which contains results, statistics and logs relating to the run

````
<output-path>
└── <test-name>
    ├── <test-name>.ivy		[input Ivy file]
    ├── <test-name>.vmt		[input converted to SMT-LIB compatible VMT file]
    ├── bar.inv				[unbounded inductive invariant proof (if property is proved safe)]
    ├── <test-name>.results		[statistics file]
    └── <test-name>.log			[IC3PO log]
````
As a quick summary relating to the run, IC3PO produces certain key information as output.
	For example, running ```python2 ic3po.py -o foo -n bar ivybench/ex/ivy/toy_consensus.ivy --init 3``` produces the following output:
````
	(output dir: foo/bar)
	(frontend: ivy)
	(converting: ivy -> vmt)
	(mode: ic3po)
	(reuse: 1)
	(opt: 1)
	(const: 1)
	(wires: 1)
	(init size: 3)
	(using z3 4.8.9.0 with seed 0)
	(using yices 2.6.2 with seed 0)
	(found #4 definitions)
	(epr: True)
	(gen: prefer_epr)
	(found #2 actions)
	(setting |node| to 3)
	(setting |quorum| to 3)
	(setting |value| to 3)

Finite sorts: #3
	|node| = 3
	|quorum| = 3
	|value| = 3
	(input is in epr)
@     0s  0: 1 :1    
@     0s  1: 1 1 :2    
@     2s  2: 1 2 3 :6    
@     3s  3: 1 3 3 3 :10    
@     5s  4: 1 2 3 1 4 :11    
@     5s  5: 1 2 2 1 0 5 :11    

@     5s  Minimizing...
@     6s  Minimized proof certificate (finite) of size 3.
@     6s  (finite convergence checks)
@     6s  	|node| = 4 :	pass
@     6s  	|value| = 4 :	pass
@     6s  	|quorum| = 4 :	pass
@     6s  (all finite convergence checks passed)
@     6s  (unbounded induction checks passed)
Finite sorts (final): #3
	|quorum| = 3
	|node| = 3
	|value| = 3
	(invariant file: foo/bar/bar.inv)
@     6s  Property proved. Proof certificate of size 3
	(with inv: epr: True)
````
":" separated numbers indicate the following:

```<max IC3 frame> : <# of added clauses in each frame> s: <total # of clauses learnt>```

#### License
Copyright (c) 2021  Aman Goel and Karem Sakallah, University of Michigan. All rights reserved.

IC3PO is available for research and evaluation purposes only.
IC3PO is provided as is, without any warranty.
Any usage of IC3PO needs to comply with the usage terms as detailed in the file [COPYING](https://github.com/aman-goel/ic3po/blob/master/COPYING).



We would be glad to hear from you and help you in the case you are having a difficulty in using IC3PO

Please report bugs and share your usage experience via email  [(amangoel@umich.edu)](amangoel@umich.edu) or on github [(https://github.com/aman-goel/ic3po)](https://github.com/aman-goel/ic3po)
