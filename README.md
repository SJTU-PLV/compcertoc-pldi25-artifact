# CompCertOC: Verified Compositional Compilation of Multi-Threaded Programs with Shared Stacks (Artifact for PLDI 2025)

## 1.Overview 

This artifact contains CompCertOC, an extension 
of CompCertO that provides verified compositional
compilation of multi-threaded programs with shared 
stacks. Both CompCertOC and CompCertO are based on CompCert
version 3.13. Our implementation is located in the
[`CompCertOC`](CompCertOC) directory. For comparison,
we also provide a copy of CompCertO in the directory
[`CompCertO`](CompCertO).

This artifact accompanies the following paper:

> CompCertOC: Verified Compositional Compilation of Multi-Threaded Programs with Shared Stacks. Ling Zhang, Yuting Wang, Yalun Liang and Zhong Shao

We first introduce the structure of this artifact according to 
the polished [camera-ready](camera-ready.pdf) version of our paper in Section 2.
The formal definitions and theorems of the claims we made in the 
[submission](pldi25-paper146-submission.pdf) can be found in Section 3.
The instructions for building and evaluating can be found in Section 4 and Section 5.
In Section 6, we present the newly added definitions and 
theorems for backward simulations which were not included in the submission but 
requested by the reviewers.
Finally in Section 7, we demonstrate how to compile and verify the running example
and some additional examples.

**Notice**: if you are on [the main page](https://github.com/SJTU-PLV/compcertoc-pldi25-artifact)
of this github repository, some
hyperlinks may lead to "Not Found" errors. Please navigate the README.md file 
[directly](https://github.com/SJTU-PLV/compcertoc-pldi25-artifact/blob/main/README.md)
to ensure that the hyperlinks work properly.


## 2. Structure of the Artifact

As mentioned above, this artifact is developed based on CompCert and CompCertO.
We first briefly introduce the structure of CompCert and CompcertO.
We then present the structure of CompCertOC which supports multi-threaded programs.

### 2.1. CompCert

CompCert is the-state-of-art verified C compiler. The documentation of the 
latest version of it can be found [here](https://compcert.org/doc/).
The file structure described in this document is largely preserved in CompCertO and 
CompCertOC.

### 2.2. CompCertO

CompCertO is an extension of CompCert for supporting verified compositional compilation of heterogeneous modules. The semantic model of CompCert has been extended to describe the behavior of individual compilation units and enable compositional verification.

CompCertOC is based on a the latest version of CompCertO with Direct Refinements which
introduces `injp` for protection of private memory regions. You can find the 
documentation of this version
[here](https://github.com/SJTU-PLV/direct-refinement-popl24-artifact/blob/main/README.md) which describes the code in `CompCertO` directory of this artifact.


### 2.3. CompCertOC

Most of the developments of CompCertOC are located in the [concur](CompCertOC/concur)
directory. We introduce these *new* contents according to the presentation order in the [camera-ready](camera-ready.pdf) paper.

#### Multi-threaded memory model, threaded Kripke memory relations, threaded simulations and their compositionality

- The multi-threaded memory model (Section 4.1) is defined in [common/Memory.v](CompCertOC/common/Memory.v). The `sup` type is defined as:
```
Record sup' : Type :=
  mksup
    {
      stacks : list (list positive);
      tid : nat;
      
      tid_valid: (0 < tid < (length stacks))%nat;
    }.
```
  
- For Threaded Kripke Memory Relations (Section 4.2),
  the accessibilities of `tinjp` are
  defined in [concur/Injp.v](CompCertOC/concur/Injp.v).
  The internal accessibility `injp_acci` is defined as:

```
   Inductive injp_acci : relation injp_world :=
    injp_acci_intro : forall (f : meminj) (m1 m2 : mem) (Hm : Mem.inject f m1 m2) (f' : meminj) 
		(m1' m2' : mem) (Hm' : Mem.inject f' m1' m2')
		...
		Mem.unchanged_on_i (loc_unmapped f) m1 m1' ->
		Mem.unchanged_on_i (loc_out_of_reach f m1) m2 m2' ->
		inject_incr f f' ->
		...
		injp_acci (injpw f m1 m2 Hm) (injpw f' m1' m2' Hm').
```

Here, `Mem.unchanged_on_i` and `inject_incr` correspond to the formula
in our paper. Other properties are omitted for simplicity. Note that they are verified to be satisfied by all the compiler passes using `tinjp`.

- Threaded forward simulation (Section 4.3) is defined in 
  [concur/CallconvBig.v](CompCertOC/concur/CallconvBig.v).
  
  - The threaded simulation convention (Def4.2) is defined as follows:
  ```
  
  Record callconv {li1 li2} :=
  mk_callconv {
    ccworld : Type;
    ccworld_world : World ccworld;
    match_senv: ccworld -> Genv.symtbl -> Genv.symtbl -> Prop;
    match_query: ccworld -> query li1 -> query li2 -> Prop;
    match_reply: ccworld -> reply li1 -> reply li2 -> Prop;

	...
    }.
  ```
  The TKMR and the operations `get` and `set` are defined in the typeclass `World` as follows:
  ```
  Class Lens (T A: Type) :=
  {
    get : T -> A;
    set : T -> A -> T;
    get_set : forall t a, get (set t a) = a;
    set_get : forall t, set t (get t) = t;
    set_set : forall t a1 a2, set (set t a1) a2 = set t a2;
  }.
  
  Class World (T: Type) :=
  {
    w_state : Type;
    w_lens : Lens T w_state;
    w_acci : w_state -> w_state -> Prop;
    w_acce : w_state -> w_state -> Prop;
    w_acci_trans : PreOrder w_acci;
  }.

  ```
  Here `w_state` is the sub-world type, the operations are defined in `w_lens`.
  
  - Threaded forward simulation (Definition 4.3) is formalized as follows:
  ```
    Record fsim_properties
           (L1: lts li1 li1 state1) (L2: lts li2 li2 state2)
           (index: Type) (order: index -> index -> Prop)
           (match_states: gw_type -> index -> state1 -> state2 -> Prop) :=
      {
        fsim_match_valid_query:
        forall q1 q2, match_query cc wb q1 q2 ->
                 valid_query L2 q2 = valid_query L1 q1;
        fsim_match_initial_states:
          forall q1 q2 s1, match_query cc wb q1 q2 -> initial_state L1 q1 s1 ->
          match_senv cc wb se1 se2 ->
          exists i, exists s2, initial_state L2 q2 s2 /\ match_states (get wb) i s1 s2;
        fsim_match_final_states:
          forall gw i s1 s2 r1, match_states gw i s1 s2 -> final_state L1 s1 r1 ->
          exists r2 gw', final_state L2 s2 r2 /\ (get wb) o-> gw' /\ gw *-> gw' /\
          match_reply cc (set wb gw') r1 r2;
        fsim_match_external:
          forall gw i s1 s2 q1, match_states gw i s1 s2 -> at_external L1 s1 q1 ->
          exists wa q2 , at_external L2 s2 q2 /\ gw *-> (get wa) /\
          match_query cc wa q1 q2 /\ match_senv cc wa se1 se2 /\
          forall r1 r2 s1' gw'', (get wa) o-> gw'' -> match_reply cc (set wa gw'') r1 r2 ->
          after_external L1 s1 r1 s1' ->
          exists i' s2', after_external L2 s2 r2 s2' /\
          match_states gw'' i' s1' s2';
          (* exists gw''' , gw'' *-> gw''' /\ match_states gw''' i' s1' s2'; (*The problem of va passes*) *)
        fsim_simulation:
          forall s1 t s1', Step L1 s1 t s1' ->
          forall gw i s2, match_states gw i s1 s2 ->
          exists i', exists s2', (Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)) /\
          match_states gw i' s1' s2';
      }.
  ```
- Compositionality of Threaded Forward Simulations (Section 4.4)
  is defined in several files.
  - The concatenation of threaded simulations (Theorem 4.4) is proved in [concur/VCompBig.v](CompCertOC/concur/VCompBig.v) as follows:
  ```
  Lemma st_fsim_vcomp
  `(cc1: callconv lis lin) `(cc2: callconv lin lif)
  (Ls: semantics lis lis) (Ln: semantics lin lin) (Lf: semantics lif lif):
  forward_simulation cc1 Ls Ln ->
  forward_simulation cc2 Ln Lf ->
  forward_simulation (cc_compose cc1 cc2) Ls Lf.
  ```
  - The refinement of threaded simulation conventions (Fig 12) is defined
  in [concur/CallConvAlgebra.v](CompCertOC/concur/CallConvAlgebra.v) as follows:
  ```
  Record cctrans' {li1 li2} (cc1 cc2: callconv li1 li2) :=
    Callconv_Trans{
        match12 : gworld cc1 -> gworld cc2 -> Prop;
        big_step_incoming : ccref_incoming cc1 cc2 match12;
        big_step_outgoing : ccref_outgoing cc1 cc2 match12;
      }.
	  
  ```
  Note that we use `match12` to embed Fig 12(c) into `big_step_incoming` (Fig 12(a))
  and `big_step_outgoing` (Fig 12(b)).
  
  - Theorem 4.5 is proved in the same file as:
  ```
  Lemma open_fsim_cctrans' {li1 li2: language_interface}:
  forall (cc1 cc2: callconv li1 li2) L1 L2,
    forward_simulation cc1 L1 L2 ->
    cctrans' cc1 cc2 ->
    forward_simulation cc2 L1 L2.
  ```
  
  - The refinement of `tinjp` (Theorem 4.6) is proved in [concur/CallConvLibs.v](CompCertOC/concur/CallConvLibs.v) as follows:
  ```
  Lemma cctrans_injp_comp : cctrans (cc_compose c_injp c_injp) (c_injp).
  ```
  
  - The correctness of module linking (Theorem 4.7) is proved in [concur/HCompBig.v](CompCertOC/concur/HCompBig.v) as follows:
  ```
  Lemma compose_simulation {li1 li2} (cc: GS.callconv li1 li2) L1a L1b L1 L2a L2b L2:
  GS.forward_simulation cc L1a L2a ->
  GS.forward_simulation cc L1b L2b ->
  compose L1a L1b = Some L1 ->
  compose L2a L2b = Some L2 ->
  GS.forward_simulation cc L1 L2.
  ```

  - The threaded linking function for C and assembly are defined in [concur/CMulti.v](CompCertOC/concur/CMulti.v) and [concur/AsmMulti.v](CompCertOC/concur/AsmMulti.v). The correctness of thread linking (Theorem 4.8) is proved in [concur/ThreadLinking.v](CompCertOC/concur/ThreadLinking.v) as follows:
  ```
  Theorem Opensim_to_Globalsim : forall OpenC OpenA,
    GS.forward_simulation cc_compcert OpenC OpenA ->
    Closed.forward_simulation (Concur_sem_c OpenC) (Concur_sem_asm OpenA).
  ```

#### Threaded simulations in CompCertOC
- For the passes listed in Table 1, the proofs of them can be found in the [concur](CompCertOC/concur) directory. For example, [concur/SimplLocalsproofC.v](CompCertOC/concur/SimplLocalsproofC.v) proves the `SimplLocals` pass using threaded simulation.

- The properties of refining threaded simulation conventions (Section 5.2) can be found
in [concur/CallConvLibs.v](CompCertOC/concur/CallConvLibs.v), [concur/StackingRefine.v](CompCertOC/concur/StackingRefine.v) and [concur/Composition.v](CompCertOC/concur/Composition.v). The detailed position of these properties are listed in Section 3 below.

- The composing of threaded forward simulations (Section 5.3) is proved in [concur/Composition.v](CompCertOC/concur/Composition.v) as follows:
```
Definition cc_compcert : GS.callconv li_c li_asm :=
       ro @ wt_c @
       cc_c_asm_injp_new @ asm_ext.

Lemma cc_collapse :
  cctrans
    ( ro @ c_injp @ 
      c_injp @
      (wt_c @ c_ext) @ c_ext @
      c_injp @
      c_ext @ c_injp @
      (ro @ c_injp) @ (ro @ c_injp) @ (ro @ c_injp) @
      (wt_c @ c_ext @ cc_c_locset) @            (* Alloc *)
      locset_ext @                              (* Tunneling *)
      (wt_loc @ cc_stacking_injp) @ (* Stacking *)
      (mach_ext @ cc_mach_asm)
    )
    cc_compcert.
```
- The compiler correctness of CompCertOC is proved in [driver/Compiler.v](CompCertOC/driver/Compiler.v) as follows:
```
Theorem transf_clight_program_correct:
  forall p tp,
  transf_clight_program p = OK tp ->
  GS.forward_simulation cc_compcert (Clight.semantics1 p) (Asm.semantics tp) /\
    GS.backward_simulation cc_compcert (Clight.semantics1 p) (Asm.semantics tp).
Proof.
  intros. apply clight_semantic_preservation. apply transf_clight_program_match; auto.
Qed.
```

Note that this theorem also claims that threaded backward simulation holds.

#### Verifying the running example

The running example is formalized in the [cdemo](CompCertOC/cdemo) directory.

- The specitificaion of `encrypt.s` (Definition 6.1) is defined in [cdemo/EncryptSpec.v](CompCertOC/cdemo/EncryptSpec.v)
  and the proof (Lemma 6.2) can be found in [cdemo/Encryptproof.v](CompCertOC/cdemo/Encryptproof.v) as:
  ```
  Theorem correctness_L_E :
  forward_simulation cc_compcert L_E (Asm.semantics encrypt_s).
  ```

- The equivalence of syntactic and semantics linking of assembly modules (Theorem 6.3)
is defined in [x86/AsmLinking.v](CompCertOC/x86/AsmLinking.v) as follows:
```
   Lemma asm_linking:
   forward_simulation cc_id cc_id
      (HCompBig.semantics L (erase_program p))
      (semantics p).
```

- The top-level correctness of the running example (Lemma 6.4 and Lemma 6.5) are proved
in [cdemo/Demoproof.v](CompCertOC/cdemo/Demoproof.v) as follows:
```
	Theorem module_linking_correct :
	forward_simulation cc_compcert c_spec (Asm.semantics asm_prog).

	Theorem thread_linking_back :
    Closed.backward_simulation (Concur_sem_c c_spec) (Concur_sem_asm (Asm.semantics asm_prog)).
```



## 3. List of Claims

We list the definitions, lemmas and theorems from each section of the 
[submission](pldi25-paper146-submission.pdf)
below along with the references to their corresponding Coq formalization 
in the artifact.

### Section 2

- The *private memory* (line 222-227) is formally defined as [loc_unmapped](CompCertOC/common/Events.v#L616) and [loc_out_of_reach](CompCertOC/common/Events.v#L619) in the Coq file [common/Events](CompCertOC/common/Events.v).

### Section 3

- The memory model from Section 3.1 can be found in [common/Memory.v](CompCertOC/common/Memory.v). The nominal interface for the memory model (line 377) is defined as [SUP](CompCertOC/common/Memtype.v#L87) in the Coq file [common/Memtype.v](CompCertOC/common/Memtype.v).

- Definition 3.1 from Section 3.2 (line 404)   corresponds to [fsim_properties](CompCertOC/common/Smallstep.v#L597) in [common/Smallstep.v](CompCertOC/common/Smallstep.v). 

- Definition 3.2 from Section 3.2 (line 429) is defined as [cklr](CompCertOC/cklr/CKLR.v#L43) in [cklr/CKLR.v](CompCertOC/cklr/CKLR.v).

- Definition 3.3 from Section 3.3 (line 433) is defined as [injp](CompCertOC/cklr/InjectFootprint.v#L286) in [cklr/InjectFootprint.v](CompCertOC/cklr/InjectFootprint.v). 

- Definition 3.4 from Section 3.3 (line 444) is
defined as [cc_c_asm_injp](CompCertOC/driver/CA.v#L184) in [driver/CA.v](CompCertOC/driver/CA.v).

### Section 4

- For the multi-threaded instantiation of nominal memory model (Section 4.1),
  the type [block](CompCertOC/common/Values.v#L37) is defined in 
  [common/Values.v](CompCertOC/common/Values.v). The type `sup`
  is defined in module [Sup](CompCertOC/common/Memory.v#L116) with newly added operations in [common/Memory.v](CompCertOC/common/Memory.v).

- Definition 4.1 from Section 4.2 (line 493) corresponds to the two accessibilities 
  [injp_acci](CompCertOC/concur/Injp.v#L53) and [injp_acce](CompCertOC/concur/Injp.v#L72)
  from the Coq file [concur/Injp.v](CompCertOC/concur/Injp.v)

- Definition 4.2 from Section 4.2 (line 511) is defined as 
  [callconv](CompCertOC/concur/CallconvBig.v#L135) in [concur/CallconvBig.v](CompCertOC/concur/CallconvBig.v).
  The TKMR `P` and the operations `get` and `set` correspond to the type class 
  [World](CompCertOC/concur/CallconvBig.v#L70) in the same file. 

- Definition 4.3 from Section 4.2 (line 524) is defined as 
  [fsim_properties](CompCertOC/concur/CallconvBig.v#L191) in the same file.

- Definition 4.4 from Section 4.2 (line 580) can be found as
  [cc_c_asm_injp_new](CompCertOC/concur/CAnew.v#L81) in [concur/CAnew.v](CompCertOC/concur/CAnew.v).

- Theorem 4.5 from Section 4.3.1 (line 599) corresponds to the lemma
  [compose_simulation](CompCertOC/concur/HCompBig.v#L383) in 
  [concur/HCompBig.v](CompCertOC/concur/HCompBig.v).

- Definition 4.6 from Section 4.3.1 (line 612) corresponds to the definitions
  [Concur_sem_c](CompCertOC/concur/CMulti.v#L283) and 
  [Concur_sem_asm](CompCertOC/concur/AsmMulti.v#L266) in
  [concur/CMulti.v](CompCertOC/concur/CMulti.v) and
  [concur/AsmMulti.v](CompCertOC/concur/AsmMulti.v) for C and assembly, respectively.

- Theorem 4.7 from Section 4.3.1 (line 629) is proved as 
  [Opensim_to_Globalsim](CompCertOC/concur/ThreadLinking.v#L2969) in
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
  - property (2) is proved as [cctrans_CAinjp](CompCertOC/concur/Composition.v#L567) in the Coq file [concur/Composition.v](CompCertOC/concur/Composition.v).

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
  [transf_clight_program_correct](CompCertOC/driver/Compiler.v#L549) in
  the Coq file [driver/Compiler.v](CompCertOC/driver/Compiler.v).
  The refinement sequence (line825-833) is proved as
  [cc_collapse](CompCertOC/concur/Composition.v#L698) in the Coq file
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

- We claim that we have added 15.8k lines of code (LOC) on top of CompCertO in Section 6.2 (line 879).
  In this artifact, we have revised the code for better readability, and added more contents according to
  the reviews. Therefore, the total amount of Coq is about 21.4k LOC. The details are discussed
  in the section "Evaluation" below.

## 4. Installation

### 4.1. Requirements

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

### 4.2. Instructions for compiling the Coq code

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

### 4.3. Navigating the proofs

After that, you can navigate the source code by using
[emacs](https://www.gnu.org/software/emacs/) with
[proof-general](https://proofgeneral.github.io/doc/master/userman/Introducing-Proof-General/)
installed.

For example, and running (in the directory `CompCertOC`)

```
emacs concur/CallconvBig.v
```

opens the emacs window in 
proof-general
mode for browsing the file `concur/CallconvBig.v`. 

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

## 5. Evaluation

### 5.1. Soundness 
To check that there is no admit in the artifact, enter `DirectRefinement` and run
```
find . -name "*.v" | xargs grep "Admitted"
```
which should show no admit.

### 5.2. Proof effort

The following are the instructions for reproducing the lines of code (LOC)
of each part of our implementation according to Section 6.2 (line 879-899).
As mentioned in the overview, the concrete numbers are slightly changed after submission.

#### Multi-stack memory model

run the following command in directories `CompCertO` and `CompCertOC`, respectively:

```
coqwc common/Memory.v common/Values.v
```

The last row of the results should be
```
#CompCertO:
     3635     4538      478 total#8173
#CompCertOC:
     4013     5181      530 total#9194
```
Therefore, we added total 1.0k(1021) lines of code to implement memory model.

#### The framework of threaded simulation

Run the following command in directory `CompCertOC`:
```
coqwc concur/CallconvBig.v concur/CallConvAlgebra.v concur/Injp.v concur/Ext.v concur/HCompBig.v concur/VCompBig.v concur/InvariantC.v
```

The last row of result should be 
```
     1278     1302      271 total#2580
```

We used 2.6k(2580) lines of code for the threaded simulation framework. 

#### Verification of compilation passes

For comparison, firstly run the following command in directory `CompCertO`:
```
coqwc cfrontend/SimplLocalsproof.v cfrontend/Cminorgenproof.v backend/RTLgenproof.v backend/Selectionproof.v backend/Tailcallproof.v backend/Inliningproof.v backend/Constpropproof.v backend/CSEproof.v backend/Deadcodeproof.v backend/Allocproof.v backend/Tunnelingproof.v backend/Stackingproof.v x86/Asmgenproof.v

```
The last row of result should be
```
     6163    13146     1497 total#19309
```

Then, run the following command in `CompCertOC`:
```
coqwc concur/SimplLocalsproofC.v concur/CminorgenproofC.v concur/RTLgenproofC.v concur/SelectionproofC.v concur/TailcallproofC.v concur/InliningproofC.v concur/ConstpropproofC.v concur/CSEproofC.v concur/DeadcodeproofC.v concur/AllocproofC.v concur/TunnelingproofC.v concur/StackingproofC.v concur/AsmgenproofC.v
```

The last row of result should be
```
     6770    15334     1512 total#22104
```

Therefore, we added 2.8k(2795) lines of code (LOC) on the top of 19.3k(19309) LOC in CompCertO. Note that 
pass `Unusedglob` is not included in the current artifact.

#### Refinement of threaded simulation conventions

Run the following command in `CompCertOC`:

```
coqwc concur/InjpAccoComp.v concur/InjpExtAccoComp.v concur/RTLselfsim.v concur/CAnew.v concur/CallConvLibs.v concur/StackingRefine.v concur/Composition.v
```
The last row of result should be
```
     1581     6015     1073 total#7596
```

We added 7.6k(7596) lines of code to verify the refinements of threaded simulation conventions.

#### Multi-threaded semantics and thread linking

Run the following command in `CompCertOC`:
```
coqwc concur/MultiLibs.v concur/CMulti.v concur/AsmMulti.v concur/ThreadLinking.v concur/ThreadLinkingBack.v
```
The last row of result should be:
```
     1181     5115      389 total#6296
```

Totally 6.3k(6296) lines of code are needed to define multi-threaded semantics and prove thread linking.
Note that about 3.2k LOC from `ThreadLinkingBack.v` is for backward simulation which is newly added and
not counted in the submission.


#### Running example

For the running example, simply run the following command in `CompCertOC`:
```
coqwc cdemo/*.v
```

The last row of result should be:

```
      544      556      142 total#1100
```

We used 1.1k lines of code to verify the running example.

In summary, our Coq development contains (1.0+2.6+2.8+7.6+6.3+1.1 =) 21.4k lines of code on top of
CompCertO.

## 6. Newly added contents: backward simulation 

As the reviewers point out: backward simulation is the gold standard
of compiler correctness, while we only talk about forward simulation
in the submission. We have shown that (threaded) backward simulation
can be derived by flipping our forward simulation following the
standard practice in CompCert. The implementation of our threaded
backward simulation and their thread linking theorem is listed as
follows.

- The threaded backward simulation is defined as 
[bsim_properties](CompCertOC/concur/CallconvBig.v#L733)
in [concur/CallconvBig.v](CompCertOC/concur/CallconvBig.v).

- The theorem for flipping threaded forward simulation into backward
simulation is defined as
[forward_to_backward_simulation](CompCertOC/concur/CallconvBig.v#L1099)
in the same file.

- The compiler correctness theorem 
 [transf_clight_program_correct](CompCertOC/driver/Compiler.v#L549) in
 the Coq file [driver/Compiler.v](CompCertOC/driver/Compiler.v) 
 contains both forward and backward simulations.
 
- We are able to prove the correctness of thread linking in the form
  of backward simulation as
  [BSIM](CompCertOC/concur/ThreadLinkingBack.v#L3321) in
  [concur/ThreadLinkingBack.v](CompCertOC/concur/ThreadLinkingBack.v).
  To apply this theorem, the soundness properties `determinate_big
  OpenC`, `after_external_receptive OpenC` and
  `initial_state_receptive OpenC` are needed for the source semantics,
  which we have proven for the Clight programs at the end of the same
  file.
  
- With the above results, we updated the correctness property of our
  running example in the form of 
  threaded backward simulation 
  ([module_linking_back](CompCertOC/cdemo/Demoproof.v#L254))
  and closed backward simulation between multi-threaded semantics 
  ([thread_linking_back](CompCertOC/cdemo/Demoproof.v#L262)) in the Coq file 
  [cdemo/Demoproof.v](CompCertOC/cdemo/Demoproof.v).
  Note that the closed backward simulation 
  is the exact same one in vanilla CompCert for closed programs. Therefore, we have successfully linked our compiler correctness with
  the standard backward simulation in CompCert.
  
  
## 7. Compile and verify examples

We demonstrate how to use CompCertOC to compile the running example and some other examples
in [examples](CompCertOC/examples) directory.
Make sure that you have already run the command `make install` such that `ccomp` is installed.
The usage of `ccomp` can be found at the CompCert manual page [here](https://compcert.org/man/).
<!-- The commands for compiling the examples is given, you can also try to write some new code using  -->
<!-- `pthread.t` and compile it using CompCertOC. -->

Note that `ccomp` is the full compilation chain generated from
CompCertOC which consists of the following passes:

* Lexer, parser and preprocessor for generating CompCert C source code
  (not fully verified).

* `SimplExpr` for translating CompCert C into `Clight`.

* The verified compilation chain from `Clight` to CompCert Asm
  code. This is the `transf_clight_program` function in
  `CompCertOC/driver/Compiler.v`.

* Pretty printer of CompCert Asm to `*.s` files.

* GNU assembler and linker for generating executable files.


### 7.1 Running examples

You can find the running example of our paper in [examples/running_example](CompCertOC/examples/running_example). 
Run `make` in this directory to compile the source files and link them into an executable file `main`. You can see the commands using `ccomp` in the terminal as follows:

```
ccomp -g -Wall -c client.c -o client.o
ccomp -g -Wall -c server.c -o server.o
ccomp -g -Wall -c encrypt.s -o encrypt.o
ccomp -lpthread -o main client.o server.o encrypt.o
Done.
```

After compilation, run `./main` to execute the compiled program:
```
./main
11; 8; 9; 14; 15; 
```

Note that the source files (`client.c`, `server.c` and `encrypt.s`) correspond to Fig.2 in
the paper.  The primitive `yield` is not included in this files because we are running 
*preemptive* programs here.
As mentioned in our camera-ready paper, we focus on the *cooperative semantics* and the connection
with preemptive semantics is left for future work.

Although the compilation pass `SimplExpr` from C to Clight is not verified in this artifact 
(as mentioned in the paper), we have successfully composed this pass with the current compiler
correctness in the form of threaded backward simulation. Interested readers can see the code
[here](https://github.com/SJTU-PLV/CompCert/tree/Direct-MultiThread).

Similarly, run `make` and `./main` in [examples/fig1](CompCertOC/examples/fig1) to see the result 
of the simple example in Fig. 1 of the paper.

### 7.2 Additional examples

Besides the examples in our paper, we provide two more exmaples to illustrate the possible 
multi-threaded programs supported by CompCertOC (i.e. they only use `pthread_create` and 
`pthread_join`).

- [examples/workers](CompCertOC/examples/workers) includes a classic multi-threaded program where
the main thread creates several worker threads to finish some requests parallelly.

- [examples/thread_tree](CompCertOC/examples/thread_tree) includes another program where each 
thread may split into two sub-threads to form a binary tree for solving some problem recursively.

Similarly, they can be compiled and run using `make` and `./main` in their directories. 
You can also write your own programs and compile them using CompCertOC(`ccomp`).

  
  
  
