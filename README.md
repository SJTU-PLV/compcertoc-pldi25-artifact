# CompCertOC: Verified Compositional Compilation of Multi-Threaded Programs with Shared Stacks (Artifact for PLDI 2025)

## 1.Overview 

This artifact contains CompCertOC, an extension 
of CompCertO that provides verified compositional
compilation of multi-threaded programs with shared 
stacks. The extended CompCertO is based con CompCert
version 3.13.

This artifact accompanies the following paper:

> [*CompCertOC: Verified Compositional Compilation of Multi-Threaded Programs with Shared Stacks*](pldi25-paper146-submission.pdf). Ling Zhang, Yuting Wang, Yalun Liang and Zhong Shao

[TODO]

**Notice**: if you are on [the main page](https://github.com/SJTU-PLV/direct-refinement-popl24-artifact)
of this github repository, some
hyperlinks may lead to "Not Found" errors. Please navigate the README.md file 
[directly](https://github.com/SJTU-PLV/direct-refinement-popl24-artifact/blob/main/README.md)
to ensure that the hyperlinks work properly.


## 2. List of Claims

We list the definitions, lemmas and theorems from each section of
the paper below along with the references to their corresponding Coq
formalization in the artifact.
<!-- A more organized and complete explanation -->
<!-- of the Coq formalization is located in the section "Structure of the Formal Proofs" below. -->

### Section 2

### Section 3

### Section 4

### Section 5

### Section 6


## 3. Installation

### 3.1. Requirements

The compiler is based on CompCertO and CompCert v3.13. You can find the user manual of CompCert [here](http://compcert.inria.fr/man/).

The development is known to compile with the following software:
- Menhir v.20220210
- Coq v8.12.0
- OCaml v4.10.1

- If you are using the VM, all the required software have already been installed on the virtual machine.

- If you prefer to compile the source code on your own computer, then we recommend using the [`opam`](https://opam.ocaml.org/) package manager to set up a build environment in Linux. 
We have tested the building on Linux with the following shell commands.
```
    # Initialize opam (if you haven't used it before)
    opam init --bare
    
    # Create an "opam switch" dedicated to building the code
    opam switch create direct-refinement ocaml-base-compiler.4.10.1
    
    # Install the necessary packages
    opam repository add coq-released https://coq.inria.fr/opam/released
    opam install coq.8.12.0 menhir.20220210
    
    # Configure the current shell to use the newly created opam switch
    eval $(opam env)
```

### 3.2. Instructions for compiling the Coq code

Download the source code form github (If you are using the VM, ignore this).
```
git clone git@github.com:SJTU-PLV/compcertoc-pldi25-artifact.git
```

The Coq code is located in the `CompCertOC` directory.
First, you need to build a library named [Coqrel](https://github.com/CertiKOS/coqrel).
```
    (cd coqrel && ./configure && make)
```
Then, you can build the CompCertOC as follows:
```
    ./configure x86_64-linux
    make
```

You are all set if the compilation finishes successfully.  You may
also speed up the process by using `-jN` argument to run the Coq
compiler in parallel.

> [TODO]
<!-- We have tested running `make -j4` in the VM with 4GB virtual memory and 4 CPU cores, which in turn runs -->
<!-- on a host machine with Intel i9-12900H and 64 GB memory. The whole compilation takes about 8 -->
<!-- minutes. When using `make` command without any parallel compilation, -->
<!-- it takes about 20 minutes. -->


For CompCert unit tests, enter the `test` directory and run
```
make
make test
```

Note that we do not support the tests using interpreter in `test/regression`.
Because the interpreter relies on the whole program semantics which is not
implemented (based on open semantics) yet.

You can run `make clean` to clean up the compiled code.

### 3.3. Navagating the proofs

After that, you can navigate the source code by using
[emacs](https://www.gnu.org/software/emacs/) with [proof-general](https://proofgeneral.github.io/doc/master/userman/Introducing-Proof-General/)
installed.

For example, running

```
emacs cklr/InjectFootprint.v
```

opens the emacs window in 
proof-general
mode for browsing the file `cklr/InjectFootprint.v`. 

You can also compile the source code into html files for better
readability. Simply run the following command (needs
`coq2html` which has already been installed in the VM)

```
make documentation
```

Then, the html versions of source code can be found at `doc/html`.
Note that the [index page](DirectRefinement/doc/index.html) is provided by CompCertO.

Note that if you compile the code in your own machine (without
`coq2html` installed), you need to install `coq2html` using the
following commands:

```
git clone https://github.com/xavierleroy/coq2html.git
cd coq2html
make
sudo make install
```

## 4 Evaluation

### 4.1 Soundness 


### 4.2 Proof effort

