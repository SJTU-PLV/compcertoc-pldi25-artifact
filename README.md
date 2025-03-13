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

We list the definitions, lemmas and theorems from each section of the paper below along with the references to their corresponding Coq formalization in the artifact.
<!-- A more organized and complete explanation -->
<!-- of the Coq formalization is located in the section "Structure of the Formal Proofs" below. -->

### Section 2

- The *private memory* (line 222-227) is formally defined as [loc_unmapped](CompCertOC/common/Events.v#L616) and [loc_out_of_reach](CompCertOC/common/Events.v#L619) in the Coq file [common/Events](CompCertOC/common/Events.v).

### Section 3

- The memory model from Section 3.1 can be found in [common/Memory.v](CompCertOC/common/Memory.v). The nominal interface for the memory model (line 377) is defined as [SUP](CompCertOC/common/Memtype.v) in the Coq file [common/Memtype.v](CompCertOC/common/Memtype.v).

- Definition 3.1 from Section 3.2 (line 404)   corresponds to [fsim_properties](CompCertOC/common/Smallstep.v#L597) in [common/Smallstep.v](CompCertOC/common/Smallstep.v). 

>[TODO: remove these backgrounds to sec5?]
- Definition 3.2 from Section 3.2 (line 429) is defined as `cklr` in [cklr/CKLR.v](CompCertOC/cklr/CKLR.v).

- Definition 3.3 from Section 3.3 (line 433) is defined as `injp` in [cklr/InjectFootprint.v](CompCertOC/cklr/InjectFootprint.v). Note that it is not actually used is this work.

- Definition 3.4 from Section 3.3 (line 444) is
defined as `cc_c_asm_injp` in [driver/CA.v](CompCertOC/driver/CA.v).

### Section 4

- For the multi-threaded instantiation of nominal memory model (Section 4.1),
  the type [block](CompCertOC/common/Values.v#L37) is defined in 
  [common/Values.v](CompCertOC/common/Values.v). The type [sup](CompCertOC/common)
  is defined in module [Sup](CompCertOC/common/Memory.v#L116) with newly added operations.

- Definition 4.1 from Section 4.2 (line 493) corresponds to the two accessibilities 
  [injp_acci](CompCertOC/concur/Injp.v#53) and [injp_acce](CompCertOC/concur/Injp.v#72)
  from the Coq file [concur/Injp.v](CompCertOC/concur/Injp.v)

- Definition 4.2 from Section 4.2 (line 511) is defined as 
  [callconv](CompCertOC/concur/CallconvBig.v#L135) in [concur/CallconvBig.v](CompCertOC/concur/CallconvBig.v).
  The TKMR `P` and the operations `get` and `set` correspond to the type class 
  [World](CompCertOC/concur/CallconvBig.v#L70) in the same file. 

- Definition 4.3 from Section 4.2 (line 524) is defined as 
  [fsim_properties](CompCertOC/concur/CallconvBig.v#191) in the same file.

- Definition 4.4 from Section 4.2 (line 580) can be found as
  [cc_c_asm_injp_new](CompCertOC/concur/CAnew.v#81) in [concur/CAnew.v](CompCertOC/concur/CAnew.v).

- Theorem 4.5 from Section 4.3.1 (line 599) corresponds to the lemma
  [composie_simulation](CompCertOC/concur/HCompBig.v#357) in 
  [concur/HCompBig.v](CompCertOC/concur/HCompBig.v).

- Definition 4.6 from Section 4.3.1 (line 612) corresponds to the definitions
  [Concur_sem_c](CompCertOC/concur/CMulti.v#281) and 
  [Concur_sem_asm](CompCertOC/concur/AsmMulti.v#266) in
  [concur/CMulti.v](CompCertOC/concur/CMulti.v) and
  [concur/AsmMulti.v](CompCertOC/concur/AsmMulti.v) for C and assembly, respectively.

- Theorem 4.7 from Section 4.3.1 (line 629) is proved as 
  [Opensim_to_Globalsim](CompCertOC/concur/ThreadLinking.v#2925) in
  [concur/ThreadLinking.v](CompCertOC/concur/ThreadLinking.v).

- Theorem 4.8 from Section 4.3.2 (line 651) corresponds to the lemma
  [st_fsim_vcomp](CompCertOC/concur/VCompBig.v#L109) in
  [concur/VCompBig.v](CompCertOC/concur/VCompBig.v).

- Theorem 4.9 from Section 4.3.2 (line 660) is proved as 
  [open_fsim_cctrans'](CompCertOC/concur/CallConvAlgebra.v#L79)
  in [concur/CallConvAlgebra.v](CompCertOC/concur/CallConvAlgebra.v).
  The refinement between simulation conventions $\sqsubseteq$ correspond
  s to [cctrans'](CompCertOC/concur/CallConvAlgebra.v#L71) in the same file.

- As mentioned in line 666, Theorem 4.10 from Section 4.3.2 (line 669) corresponds to the critical part of [cctrans_injp_comp](CompCertOC/concur/CallConvLibs.v#L2157) in the Coq file [concur/CallConvLibs.v](CompCertOC/concur/CallConvLibs.v).


### Section 5

- Lemma 5.1 from Section 5.1.2 (line 759) is proved
as [transf_program_correct](CompCertOC/concur/StackingproofC.v#L3043) in [concur/StackingproofC.v](CompCertOC/concur/StackingproofC.v).

- For Lemma 5.2 from Section 5.2 (line 786),
    - property (1) is [cctrans_injp_comp](CompCertOC/concur/CallConvLibs.v#L2157) in the Coq file [concur/CallConvLibs.v](CompCertOC/concur/CallConvLibs.v).
    - property (2) is [cctrans_ext_comp](CompCertOC/concur/CallConvLibs.v#L2249) in the same file.
    - property (3) is [cctrans_injp_ext](CompCertOC/concur/CallConvLibs.v#L2541) in the same file.
    - property (4) is [cctrans_ro_injp_compose](CompCertOC/concur/Composition.v#L295) in the Coq file [concur/Composition.v](CompCertOC/concur/Composition.v).

- For Lemma 5.3 from Section 5.2 (line 792),
  - property (1) corresponds to the lemmas 
    [CL_trans_ext](CompCertOC/concur/CallConvLibs.v#L398),
    [CL_trans_ext1](CompCertOC/concur/CallConvLibs.v#L482), 
    [CL_trans_injp](CompCertOC/concur/CallConvLibs.v#L563) and 
    [CL_trans_injp1](CompCertOC/concur/CallConvLibs.v#L653) in the Coq file [concur/CallConvLibs.v](CompCertOC/concur/CallConvLibs.v).
  - property (2) corresponds to the lemmas
    [MA_trans_injp1](CompCertOC/concur/CallConvLibs.v#L816),
    [MA_trans_injp2](CompCertOC/concur/CallConvLibs.v#L904),
    [MA_trans_ext1](CompCertOC/concur/CallConvLibs.v#L1003) and
    [MA_trans_ext2](CompCertOC/concur/CallConvLibs.v#L1096) in the same file.

- For Lemma 5.4 from Section 5.2 (line 797), 
  - property (1) is proved as [cctrans_injp_ext_ccstacking](CompCertOC/concur/StackingRefine.v#L121) in the Coq file
  [concur/StackingRefine.v](CompCertOC/concur/StackingRefine.v).
  - property (2) is proved as [cctrans_CAinjp](CompCertOc/concur/Composition.v#L567) in the Coq file [concur/Composition.v](CompCertOC/concur/Composition.v).

- For Lemma 5.5 from Section 5.2 (line 802),
  - property (1) corresponds to the lemmas
  [cctrans_ro_wt_c](CompCertOC/concur/Composition.v#L418) and 
  [cctrans_wt_c_ro](CompCertOC/concur/Composition.v#L423) in the Coq file [concur/Composition.v](CompCertOC/concur/Composition.v).
  - property (2) corresponds to the lemmas
  [move_wt_injp](CompCertOC/concur/Composition.v#L60) and
  [move_wt_ext](CompCertOC/concur/Composition.v#L119) in the same file.
  - property (3) corresponds to 
  [cctrans_wt_c_compose](CompCertOC/concur/Composition.v#L459) in the same file.

- Lemma 5.6 from Section 5.3 (line 820) corresponds to the theorem
  [TODO].
  The refinement sequence (line825-833) is proved as
  [cc_collapse](CompCertOC/concur/Composition.v) in the Coq file
  [concur/Composition.v](CompCertOC/concur/Composition.v).


### Section 6

- Definition 6.1 from Section 6.1 (line 847) is defined as [L_E](CompCertOC/cdemo/EncryptSpec.v#L45)
in the Coq file [cdemo/EncryptSpec.v](CompCertOC/cdemo/EncryptSpec.v).

- Lemma 6.2 from Section 6.1 (line 855) is proved as
[correctness_L_E](CompCertOC/cdemo/Encryptproof.v#L586) in the Coq file [cdemo/Encryptproof.v](CompCertOC/cdemo/Encryptproof.v).

- Lemma 6.3 from Section 6.1 (line 865) corresponds to [module_linking_correct](CompCertOC/cdemo/Demoproof.v#L67) in the Coq file [cdemo/Demoproof.v](CompCertOC/cdemo/Demoproof.v).

- Lemma 6.4 from Section 6.1 (line 869) is proved as [asm_linking](CompCertOC/x86/AsmLinking.v#L371)
in the Coq file [x86/AsmLinking.v](CompCertOC/x86/AsmLinking.v).

- Lemma 6.5 from Section 6.1 (line 875) is proved
as [thread_linking_correct](CompCertOC/cdemo/Demoproof.v#L80) in the Coq file [cdemo/Demoproof.v](CompCertOC/cdemo/Demoproof.v).


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
    opam switch create compcertoc ocaml-base-compiler.4.10.1
    
    # Install the necessary packages
    opam repository add coq-released https://coq.inria.fr/opam/released
    opam install coq.8.12.0 menhir.20220210
    
    # Configure the current shell to use the newly created opam switch
    eval $(opam env)
```

### 3.2. Instructions for compiling the Coq code

Download the source code form github (If you are using the VM, ignore this).
```
    git clone https://github.com/SJTU-PLV/compcertoc-pldi25-artifact.git
```

The Coq code is located in the `CompCertOC` directory.
First, you need to build a library named [Coqrel](https://github.com/CertiKOS/coqrel).
```
    (cd coqrel && ./configure && make)
```
Then, you can build and install the CompCertOC as follows:
```
    ./configure x86_64-linux
    make
    sudo make install
```

You are all set if the compilation finishes successfully.  You may
also speed up the process by using `-jN` argument to run the Coq
compiler in parallel.


We have tested running `make` in the VM with 4GB virtual memory and 4 CPU cores, which in turn runs on a host machine with Intel i9-12900H and 64 GB memory. The whole compilation takes 1 hour.
When using `make -4j` command for parallel compilation,
it takes about 20 minutes. -->


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
emacs concur/CallconvBig.v
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

## 4. Evaluation

### 4.1. Soundness 
To check that there is no admit in the artifact, enter `DirectRefinement` and run
```
find . -name "*.v" | xargs grep "Admitted"
```
which should show no admit.

### 4.2. Proof effort

The following are the instructions for reproducing the lines of code
mentioned in Section 6.2.
