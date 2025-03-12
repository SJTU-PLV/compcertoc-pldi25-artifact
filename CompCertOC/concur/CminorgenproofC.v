(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for Cminor generation. *)

Require Import Coq.Program.Equality FSets Permutation.
Require Import FSets FSetAVL Orders Mergesort.
Require Import Coqlib Maps Ordered Errors Integers Floats.
Require Intv.
Require Import AST Linking.
Require Import Values Memory Events Globalenvs Smallstep.
Require Import CallconvBig.
Require Import Injp.

Require Import Csharpminor Switch Cminor Cminorgen.
Require Import LanguageInterface cklr.CKLR cklr.Inject cklr.InjectFootprint.

Require Import SimplLocalsproofC.


Local Open Scope error_monad_scope.

Definition match_prog (p: Csharpminor.program) (tp: Cminor.program) :=
  match_program (fun cu f tf => transl_fundef f = OK tf) eq p tp.

Lemma transf_program_match:
  forall p tp, transl_program p = OK tp -> match_prog p tp.
Proof.
  intros. apply match_transform_partial_program; auto.
Qed.

Section TRANSLATION.

Variable prog: Csharpminor.program.
Variable tprog: Cminor.program.
Hypothesis TRANSL: match_prog prog tprog.
Variable w: world injp.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Let ge : Csharpminor.genv := Genv.globalenv se prog.
Let tge: genv := Genv.globalenv tse tprog.

Hypothesis GE: match_stbls injp w se tse.

Lemma functions_translated (j: meminj):
  Genv.match_stbls j se tse ->
  forall (v tv: val) (f: Csharpminor.fundef),
  Val.inject j v tv -> Genv.find_funct ge v = Some f ->
  exists f', Genv.find_funct tge tv = Some f' /\ transl_fundef f = OK f'.
Proof.
  apply (Genv.find_funct_transf_partial TRANSL).
Qed.

Lemma sig_preserved_body:
  forall f tf cenv size,
  transl_funbody cenv size f = OK tf ->
  tf.(fn_sig) = Csharpminor.fn_sig f.
Proof.
  intros. unfold transl_funbody in H. monadInv H; reflexivity.
Qed.

Lemma sig_preserved:
  forall f tf,
  transl_fundef f = OK tf ->
  Cminor.funsig tf = Csharpminor.funsig f.
Proof.
  intros until tf; destruct f; simpl.
  unfold transl_function. destruct (build_compilenv f).
  case (zle z Ptrofs.max_unsigned); simpl bind; try congruence.
  intros. monadInv H. simpl. eapply sig_preserved_body; eauto.
  intro. inv H. reflexivity.
Qed.

(** * Derived properties of memory operations *)

Lemma load_freelist:
  forall fbl chunk m b ofs m',
  (forall b' lo hi, In (b', lo, hi) fbl -> b' <> b) ->
  Mem.free_list m fbl = Some m' ->
  Mem.load chunk m' b ofs = Mem.load chunk m b ofs.
Proof.
  induction fbl; intros.
  simpl in H0. congruence.
  destruct a as [[b' lo] hi].
  generalize H0. simpl. case_eq (Mem.free m b' lo hi); try congruence.
  intros m1 FR1 FRL.
  transitivity (Mem.load chunk m1 b ofs).
  eapply IHfbl; eauto. intros. eapply H. eauto with coqlib.
  eapply Mem.load_free; eauto. left. apply not_eq_sym. eapply H. auto with coqlib.
Qed.

Lemma perm_freelist:
  forall fbl m m' b ofs k p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs k p ->
  Mem.perm m b ofs k p.
Proof.
  induction fbl; simpl; intros until p.
  congruence.
  destruct a as [[b' lo] hi]. case_eq (Mem.free m b' lo hi); try congruence.
  intros. eauto with mem.
Qed.

Lemma support_freelist:
  forall fbl m m',
  Mem.free_list m fbl = Some m' ->
  Mem.support m' = Mem.support m.
Proof.
  induction fbl; intros until m'; simpl.
  congruence.
  destruct a as [[b lo] hi].
  case_eq (Mem.free m b lo hi); intros; try congruence.
  transitivity (Mem.support m0). eauto. eapply Mem.support_free; eauto.
Qed.

Lemma free_list_freeable:
  forall l m m',
  Mem.free_list m l = Some m' ->
  forall b lo hi,
  In (b, lo, hi) l -> Mem.range_perm m b lo hi Cur Freeable.
Proof.
  induction l; simpl; intros.
  contradiction.
  revert H. destruct a as [[b' lo'] hi'].
  caseEq (Mem.free m b' lo' hi'); try congruence.
  intros m1 FREE1 FREE2.
  destruct H0. inv H.
  eauto with mem.
  red; intros. eapply Mem.perm_free_3; eauto. exploit IHl; eauto.
Qed.

(** * Correspondence between C#minor's and Cminor's environments and memory states *)

(** In C#minor, every variable is stored in a separate memory block.
  In the corresponding Cminor code, these variables become sub-blocks
  of the stack data block.  We capture these changes in memory via a
  memory injection [f]:
  [f b = Some(b', ofs)] means that C#minor block [b] corresponds
  to a sub-block of Cminor block [b] at offset [ofs].

  A memory injection [f] defines a relation [Val.inject f] between
  values and a relation [Mem.inject f] between memory states.  These
  relations will be used intensively in our proof of simulation
  between C#minor and Cminor executions. *)

(** ** Matching between Cshaprminor's temporaries and Cminor's variables *)

Definition match_temps (f: meminj) (le: Csharpminor.temp_env) (te: env) : Prop :=
  forall id v, le!id = Some v -> exists v', te!(id) = Some v' /\ Val.inject f v v'.

Lemma match_temps_invariant:
  forall f f' le te,
  match_temps f le te ->
  inject_incr f f' ->
  match_temps f' le te.
Proof.
  intros; red; intros. destruct (H _ _ H1) as [v' [A B]]. exists v'; eauto.
Qed.

Lemma match_temps_assign:
  forall f le te id v tv,
  match_temps f le te ->
  Val.inject f v tv ->
  match_temps f (PTree.set id v le) (PTree.set id tv te).
Proof.
  intros; red; intros. rewrite PTree.gsspec in *. destruct (peq id0 id).
  inv H1. exists tv; auto.
  eauto.
Qed.

(** ** Matching between C#minor's variable environment and Cminor's stack pointer *)

Inductive match_var (f: meminj) (sp: block): option (block * Z) -> option Z -> Prop :=
  | match_var_local: forall b sz ofs,
      Val.inject f (Vptr b Ptrofs.zero) (Vptr sp (Ptrofs.repr ofs)) ->
      match_var f sp (Some(b, sz)) (Some ofs)
  | match_var_global:
      match_var f sp None None.

(** Matching between a C#minor environment [e] and a Cminor
  stack pointer [sp].
  The [bes] delimits the range of addresses allocated before the
  blocks referenced from  [e].
  The [ts] total support, delimits the range of addresses of and before [e] *)

Definition init_m := match w with injpw _ m _ _ => m end.

Definition local_t : nat := Mem.tid (Mem.support (wm1 w)).

Definition sup_In_local (b: block) (s: sup) := sup_In b s /\ fst b = local_t.

Record match_env (f: meminj) (cenv: compilenv)
                 (e: Csharpminor.env) (sp: block)
                 (sps: sup) (bes es: sup) : Prop :=
  mk_match_env {

    me_sps:
      sp = fresh_block sps;

    me_sps_tid :
      Mem.tid sps = local_t;
      
    me_sup_include:
      Mem.sup_include bes es;
(** C#minor local variables match sub-blocks of the Cminor stack data block. *)
    me_vars:
      forall id, match_var f sp (e!id) (cenv!id);

(** Every block appearing in the C#minor environment [e] must be
  in the range es. *)
    me_bounded:
      forall id b sz, PTree.get id e = Some(b, sz) -> sup_In b es /\ ~ sup_In b bes;

(** All blocks mapped to sub-blocks of the Cminor stack data must be
    images of variables from the C#minor environment [e] *)
    me_inv:
      forall b delta,
      f b = Some(sp, delta) ->
      exists id, exists sz, PTree.get id e = Some(b, sz);

(** All C#minor blocks below [lo] (i.e. allocated before the blocks
  referenced from [e]) must map to blocks that are below [sp]
  (i.e. allocated before the stack data for the current Cminor function). *)
    me_incr:
      forall b tb delta,
        f b = Some(tb, delta) -> sup_In b bes -> fst b = local_t -> sup_In tb sps;
    me_inits:
      Mem.sup_include (Mem.support init_m) es;
    me_tid:
      Mem.tid es = local_t;
(** All blocks are locally allocated blocks *)      
    me_local:
      forall id b sz, PTree.get id e = Some (b, sz) -> fst b = local_t /\ ~ Mem.valid_block init_m b
  }.

Ltac geninv x :=
  let H := fresh in (generalize x; intro H; inv H).

Lemma match_env_invariant:
  forall f1 cenv e sp sps bes es f2,
  match_env f1 cenv e sp sps bes es ->
  inject_incr f1 f2 ->
  (forall b delta, f2 b = Some(sp, delta) -> fst b = fst sp /\ f1 b = Some(sp, delta)) ->
  (forall b, sup_In b bes -> fst b = local_t -> f2 b = f1 b) ->
  match_env f2 cenv e sp sps bes es.
Proof.
  intros. destruct H. constructor; auto.
(* vars *)
  intros. geninv (me_vars0 id); econstructor; eauto.
(* bounded *)
  intros. exploit H1; eauto. intros [A B].
  eauto.
(* below *)
  intros. eapply me_incr0; eauto. erewrite <- H2; eauto.
Qed.

(** [match_env] and external calls *)

Remark inject_incr_separated_same:
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b, Mem.valid_block m1 b -> f2 b = f1 b.
Proof.
  intros. case_eq (f1 b).
  intros [b' delta] EQ. apply H; auto.
  intros EQ. case_eq (f2 b).
  intros [b'1 delta1] EQ1. exploit H0; eauto. intros [C D]. contradiction.
  auto.
Qed.

Remark inject_incr_separated_same':
  forall f1 f2 m1 m1',
  inject_incr f1 f2 -> inject_separated f1 f2 m1 m1' ->
  forall b b' delta,
  f2 b = Some(b', delta) -> Mem.valid_block m1' b' -> f1 b = Some(b', delta).
Proof.
  intros. case_eq (f1 b).
  intros [b'1 delta1] EQ. exploit H; eauto. congruence.
  intros. exploit H0; eauto. intros [C D]. contradiction.
Qed.

(** [match_env] and allocations *)

Lemma match_env_alloc:
  forall f1 id cenv e sp sps bes m1 sz m2 b ofs f2,
  match_env f1 (PTree.remove id cenv) e sp sps bes (Mem.support m1) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  match_env f2 cenv (PTree.set id (b, sz) e) sp sps bes (Mem.support m2).
Proof.
  intros until f2; intros ME ALLOC CENV INCR SAME OTHER ENV.
  exploit Mem.support_alloc; eauto. intros SUPPORT.
  exploit Mem.alloc_result; eauto. intros RES.
  inv ME; constructor. auto.
  congruence.
(* sup_include *)
  rewrite SUPPORT. eapply Mem.sup_include_trans; eauto.
(* vars *)
  intros. rewrite PTree.gsspec. destruct (peq id0 id).
  (* the new var *)
  subst id0. rewrite CENV. constructor. econstructor. eauto.
  rewrite Ptrofs.add_commut; rewrite Ptrofs.add_zero; auto.
  (* old vars *)
  generalize (me_vars0 id0). rewrite PTree.gro; auto. intros M; inv M.
  try setoid_rewrite <- H.
  constructor; eauto.
  try setoid_rewrite <- H0.
  constructor.

(* bounded *)
  intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inv H. rewrite SUPPORT. split. apply Mem.sup_incr_in1. auto.
  intro.  eapply freshness; eauto.
  exploit me_bounded0; eauto. rewrite SUPPORT. intros [A B].
  split. apply Mem.sup_incr_in2. auto. auto.
(* inv *)
  intros. destruct (eq_block b (Mem.nextblock m1)).
  subst b. rewrite SAME in H; inv H. exists id; exists sz. apply PTree.gss.
  rewrite OTHER in H; auto. exploit me_inv0; eauto.
  intros [id1 [sz1 EQ]]. exists id1; exists sz1. rewrite PTree.gso; auto. congruence.
(* incr *)
  intros. rewrite OTHER in H. eauto. intro. subst b.
  eapply freshness; eauto.
(* inits *)
  red. intros. apply me_inits0 in H.
  eapply Mem.valid_block_alloc; eauto.
(* tid *)
  rewrite SUPPORT. simpl. congruence.
(* local *)
  intros. rewrite PTree.gsspec in H. destruct (peq id0 id). subst.
  inv H. split. rewrite <- me_tid0. reflexivity.
  intro. eapply freshness. apply me_inits0; eauto. eauto.
Qed.

(** The sizes of blocks appearing in [e] are respected. *)

Definition match_bounds (e: Csharpminor.env) (m: mem) : Prop :=
  forall id b sz ofs p,
  PTree.get id e = Some(b, sz) -> Mem.perm m b ofs Max p -> 0 <= ofs < sz.

Lemma match_bounds_invariant:
  forall e m1 m2,
  match_bounds e m1 ->
  (forall id b sz ofs p,
   PTree.get id e = Some(b, sz) -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  match_bounds e m2.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

(** ** Permissions on the Cminor stack block *)

(** The parts of the Cminor stack data block that are not images of
    C#minor local variable blocks remain freeable at all times. *)

Inductive is_reachable_from_env (f: meminj) (e: Csharpminor.env) (sp: block) (ofs: Z) : Prop :=
  | is_reachable_intro: forall id b sz delta,
      e!id = Some(b, sz) ->
      f b = Some(sp, delta) ->
      delta <= ofs < delta + sz ->
      is_reachable_from_env f e sp ofs.

Definition padding_freeable (f: meminj) (e: Csharpminor.env) (tm: mem) (sp: block) (sz: Z) : Prop :=
  forall ofs,
  0 <= ofs < sz -> Mem.perm tm sp ofs Cur Freeable \/ is_reachable_from_env f e sp ofs.

Lemma padding_freeable_invariant:
  forall f1 e tm1 sp sz cenv sps bes es f2 tm2,
  padding_freeable f1 e tm1 sp sz ->
  match_env f1 cenv e sp sps bes es ->
  (forall ofs, Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, sup_In b es -> fst b = local_t -> f2 b = f1 b) ->
  padding_freeable f2 e tm2 sp sz.
Proof.
  intros; red; intros.
  exploit H; eauto. intros [A | A].
  left; auto.
  right. inv A. exploit me_bounded; eauto. intros [D E].
  econstructor; eauto. rewrite H2; auto.
  inv H0. exploit me_local0; eauto. intros [A ?]. auto.
Qed.

(** Decidability of the [is_reachable_from_env] predicate. *)

Lemma is_reachable_from_env_dec:
  forall f e sp ofs, is_reachable_from_env f e sp ofs \/ ~is_reachable_from_env f e sp ofs.
Proof.
  intros.
  set (pred := fun id_b_sz : ident * (block * Z) =>
                 match id_b_sz with
                 | (id, (b, sz)) =>
                      match f b with
                           | None => false
                           | Some(sp', delta) =>
                               if eq_block sp sp'
                               then zle delta ofs && zlt ofs (delta + sz)
                               else false
                      end
                 end).
  destruct (List.existsb pred (PTree.elements e)) eqn:?.
  (* yes *)
  rewrite List.existsb_exists in Heqb.
  destruct Heqb as [[id [b sz]] [A B]].
  simpl in B. destruct (f b) as [[sp' delta] |] eqn:?; try discriminate.
  destruct (eq_block sp sp'); try discriminate.
  destruct (andb_prop _ _ B).
  left. apply is_reachable_intro with id b sz delta.
  apply PTree.elements_complete; auto.
  congruence.
  split; eapply proj_sumbool_true; eauto.
  (* no *)
  right; red; intro NE; inv NE.
  assert (existsb pred (PTree.elements e) = true).
  rewrite List.existsb_exists. exists (id, (b, sz)); split.
  apply PTree.elements_correct; auto.
  simpl. rewrite H0. rewrite dec_eq_true.
  unfold proj_sumbool. destruct H1. rewrite zle_true; auto. rewrite zlt_true; auto.
  congruence.
Qed.

(** * Invariant on abstract call stacks  *)

(** Call stacks represent abstractly the execution state of the current
  C#minor and Cminor functions, as well as the states of the
  calling functions.  A call stack is a list of frames, each frame
  collecting information on the current execution state of a C#minor
  function and its Cminor translation. *)

Inductive frame : Type :=
  Frame(cenv: compilenv)
       (tf: Cminor.function)
       (e: Csharpminor.env)
       (le: Csharpminor.temp_env)
       (te: Cminor.env)
       (sp: block)
       (sps bes es: sup).

Definition callstack : Type := list frame.

(** Matching of call stacks imply:
- matching of environments for each of the frames
- matching of the global environments
- separation conditions over the memory blocks allocated for C#minor local variables;
- separation conditions over the memory blocks allocated for Cminor stack data;
- freeable permissions on the parts of the Cminor stack data blocks
  that are not images of C#minor local variable blocks.
*)

Definition range_inject (f:meminj) e sz sp : Prop :=
  forall id b1 ofs1 delta sz1,
    f b1 = Some (sp, delta) -> e ! id = Some (b1, sz1) ->
    0 <= ofs1 < sz1 -> 0 <= ofs1 + delta < sz.

Inductive match_callstack (f: meminj) (m: mem) (tm: mem):
                          callstack -> sup -> sup -> Prop :=
  | mcs_nil:
      forall bound tbound
        (TID: Mem.tid bound = Mem.tid (Mem.support m))
        (TTID: Mem.tid tbound = Mem.tid (Mem.support tm))
        (INJTL: Mem.meminj_thread_local f)
        (INITTID1: Mem.tid (Mem.support m) = local_t)
        (INITTID2: Mem.tid (Mem.support tm) = local_t),
        inj_incr' w (injw f bound tbound) ->
      match_callstack f m tm nil bound tbound
  | mcs_cons:
      forall cenv tf e le te sp sps bes es cs bound tbound
        (TID: Mem.tid bound = Mem.tid (Mem.support m))
        (TTID: Mem.tid tbound = Mem.tid (Mem.support tm))
        (BOUND: Mem.sup_include es bound)
        (TBOUND: Mem.sup_include (sup_incr sps) tbound)
        (MTMP: match_temps f le te)
        (MENV: match_env f cenv e sp sps bes es)
        (BOUND: match_bounds e m)
        (PERM: padding_freeable f e tm sp tf.(fn_stackspace))
        (RANGE: range_inject f e tf.(fn_stackspace) sp)
        (MCS: match_callstack f m tm cs bes sps),
      match_callstack f m tm (Frame cenv tf e le te sp sps bes es :: cs) bound tbound.

Lemma match_callstack_inj_incr : forall f m tm cs s1 s2,
    match_callstack f m tm cs s1 s2 ->
    inj_incr' w (injw f s1 s2).
Proof.
  induction 1; eauto. inv IHmatch_callstack.
  constructor; eauto. inv MENV.
  eapply Mem.sup_include_trans; eauto.
Qed.

Lemma match_callstack_inj_tl : forall f m tm cs s1 s2,
    match_callstack f m tm cs s1 s2 ->
    Mem.meminj_thread_local f.
Proof.
  induction 1; eauto.
Qed.

(** [match_callstack] implies [match_globalenvs]. *)

Lemma match_callstack_match_globalenvs:
  forall f m tm cs bound tbound,
  match_callstack f m tm cs bound tbound ->
  Genv.match_stbls f se tse.
Proof.
  induction 1; eauto. inv H.
  rewrite <- H5 in GE. inv GE.
  eapply Genv.match_stbls_incr_noglobal; eauto.
Qed.

Lemma match_callstack_tid1: forall f m tm cs s1 s2,
    match_callstack f m tm cs s1 s2 ->
    Mem.tid (Mem.support m) = local_t.
Proof.
  induction 1; eauto.
Qed.

Lemma match_callstack_tid2: forall f m tm cs s1 s2,
    match_callstack f m tm cs s1 s2 ->
    Mem.tid (Mem.support tm) = local_t.
Proof.
  induction 1; eauto.
Qed.

(** Invariance properties for [match_callstack]. *)

Lemma match_callstack_invariant:
  forall f1 m1 tm1 f2 m2 tm2 cs bound tbound,
  match_callstack f1 m1 tm1 cs bound tbound ->
  inject_incr f1 f2 ->
  inject_separated_noglobal f1 f2 ->
  inject_separated_tl f1 f2 ->
  (forall b ofs p, sup_In b bound -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  (forall sp ofs, sup_In sp tbound -> Mem.perm tm1 sp ofs Cur Freeable -> Mem.perm tm2 sp ofs Cur Freeable) ->
  (forall b, sup_In b bound -> fst b = Mem.tid (Mem.support m1) -> f2 b = f1 b) ->
  (forall b b' delta, f2 b = Some(b', delta) -> sup_In b' tbound -> fst b' = Mem.tid (Mem.support tm1)-> f1 b = Some(b', delta)) ->
  (Mem.tid (Mem.support m1) = Mem.tid (Mem.support m2)) ->
  (Mem.tid (Mem.support tm1) = Mem.tid (Mem.support tm2)) ->
  match_callstack f2 m2 tm2 cs bound tbound.
Proof.
  induction 1; intros INCR NOG TL PERM1 PERM2 INJ1 INJ2 TID1 TID2.
  (* base case *)
  econstructor; eauto; try congruence.
  eapply inject_incr_thread_local; eauto.
  inv H.
  constructor; eauto. eapply inject_incr_trans; eauto.
  red. intros. destruct (f1 b1) as [[? ?]|] eqn:Hfb1.
  apply INCR in Hfb1 as Heq. rewrite H0 in Heq.
  inv Heq. eapply H4; eauto. split. intro. erewrite INJ1 in H0. congruence. eauto.
  unfold local_t in INITTID1. rewrite <- H5 in INITTID1. simpl in INITTID1. congruence.
  intro. assert (sup_In b2 tbound). eauto.
  assert (fst b2 = Mem.tid (Mem.support tm1)).
  erewrite <- TL; eauto.
  unfold local_t in INITTID2. rewrite <- H5 in INITTID2. simpl in INITTID2. congruence.
  specialize (INJ2 _ _ _ H0 H9 H10). congruence.
  red. intros. destruct (f1 b1) as [[? ?]|] eqn:Hfb1. apply INCR in Hfb1 as Heq. rewrite H0 in Heq.
  inv Heq. eapply H6; eauto. eapply NOG; eauto.
  (* inductive case *)
  assert (Mem.sup_include bes es) by (eapply me_sup_include; eauto ).
  assert (sp = fresh_block sps) by (eapply me_sps; eauto). subst.
  econstructor; eauto.
  congruence. congruence.
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto.
  intros. exploit inject_incr_thread_local; eauto. eapply match_callstack_inj_tl; eauto.
  intro. split. auto. apply INJ2; eauto.
  inv MENV. simpl. rewrite me_sps_tid0. erewrite match_callstack_tid2; eauto.
  intros. eapply INJ1; eauto. erewrite match_callstack_tid1; eauto.
  eapply match_bounds_invariant; eauto.
  intros. eapply PERM1; eauto.
  exploit me_bounded; eauto. intros [A B]. auto.
  eapply padding_freeable_invariant; eauto.
  intros. eapply INJ1; eauto. erewrite match_callstack_tid1; eauto.
  red. intros. eapply RANGE; eauto.
  erewrite <- INJ1; eauto.
  exploit me_bounded; eauto. intros [A B]. auto.
  exploit me_local; eauto. intros [A B]. erewrite match_callstack_tid1; eauto.
  eapply IHmatch_callstack; eauto.
    intros. eapply PERM2; eauto.  apply TBOUND. apply Mem.sup_incr_in2. auto.
    intros. eapply INJ2; eauto. apply TBOUND. apply Mem.sup_incr_in2. auto.
Qed.

Lemma match_callstack_incr_bound:
  forall f m tm cs bound tbound bound' tbound',
  match_callstack f m tm cs bound tbound ->
  Mem.sup_include bound bound' -> Mem.sup_include tbound tbound' ->
  Mem.tid bound = Mem.tid bound' -> Mem.tid tbound = Mem.tid tbound' ->
  match_callstack f m tm cs bound' tbound'.
Proof.
  intros. inv H. inv H2.
  econstructor; eauto. congruence. congruence.
  inv H4. econstructor; eauto.
  constructor; eauto. congruence. congruence.
Qed.

(** Assigning a temporary variable. *)

Lemma match_callstack_set_temp:
  forall f cenv e le te sp sps bes es cs bound tbound m tm tf id v tv,
  Val.inject f v tv ->
  match_callstack f m tm (Frame cenv tf e le te sp sps bes es :: cs) bound tbound ->
  match_callstack f m tm (Frame cenv tf e (PTree.set id v le) (PTree.set id tv te) sp sps bes es :: cs) bound tbound.
Proof.
  intros. inv H0. constructor; auto.
  eapply match_temps_assign; eauto.
Qed.

(** Preservation of [match_callstack] by freeing all blocks allocated
  for local variables at function entry (on the C#minor side)
  and simultaneously freeing the Cminor stack data block. *)

Lemma in_blocks_of_env:
  forall e id b sz,
  e!id = Some(b, sz) -> In (b, 0, sz) (blocks_of_env e).
Proof.
  unfold blocks_of_env; intros.
  change (b, 0, sz) with (block_of_binding (id, (b, sz))).
  apply List.in_map. apply PTree.elements_correct. auto.
Qed.

Lemma in_blocks_of_env_inv:
  forall b lo hi e,
  In (b, lo, hi) (blocks_of_env e) ->
  exists id, e!id = Some(b, hi) /\ lo = 0.
Proof.
  unfold blocks_of_env; intros.
  exploit list_in_map_inv; eauto. intros [[id [b' sz]] [A B]].
  unfold block_of_binding in A. inv A.
  exists id; intuition. apply PTree.elements_complete. auto.
Qed.

Lemma match_callstack_freelist:
  forall f cenv tf e le te sp sps bes es cs m m' tm,
  Mem.inject f m tm ->
  Mem.free_list m (blocks_of_env e) = Some m' ->
  match_callstack f m tm (Frame cenv tf e le te sp sps bes es :: cs) (Mem.support m) (Mem.support tm) ->
  exists tm',
  Mem.free tm sp 0 tf.(fn_stackspace) = Some tm'
  /\ match_callstack f m' tm' cs (Mem.support m') (Mem.support tm')
  /\ Mem.inject f m' tm'.
Proof.
  intros until tm; intros INJ FREELIST MCS. inv MCS. inv MENV.
  assert ({tm' | Mem.free tm (fresh_block sps) 0 (fn_stackspace tf) = Some tm'}).
  apply Mem.range_perm_free.
  red; intros.
  exploit PERM; eauto. intros [A | A].
  auto.
  inv A. assert (Mem.range_perm m b 0 sz Cur Freeable).
  eapply free_list_freeable; eauto. eapply in_blocks_of_env; eauto.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply Mem.perm_inject; eauto. apply H3. lia.
  destruct X as  [tm' FREE].
  exploit support_freelist; eauto. intro NEXT.
  exploit Mem.support_free; eauto. intro NEXT'.
  exists tm'. split. auto. split.
  rewrite NEXT; rewrite NEXT'.
  apply match_callstack_incr_bound with bes sps; try lia.
  apply match_callstack_invariant with f m tm; auto.
  red. intros. congruence.
  red. intros. congruence.
  intros. eapply perm_freelist; eauto.
  intros. eapply Mem.perm_free_1; eauto. left.
  intro. rewrite H1 in H. eapply freshness; eauto. congruence. congruence.
  eapply Mem.sup_include_trans; eauto.
  eapply Mem.sup_include_trans; eauto.
  inv MCS0. auto. auto. inv MCS0. auto. auto.
  eapply Mem.free_inject; eauto.
  intros. exploit me_inv0; eauto. intros [id [sz A]].
  exists 0; exists sz; split.
  eapply in_blocks_of_env; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_max. eauto.
Qed.

(** Preservation of [match_callstack] by external calls. *)

Lemma inject_incr_sep_back : forall f1 f2 b1 m1 m2 b2 d,
    inject_incr f1 f2 ->
    inject_separated_internal f1 f2 m1 m2 ->
    Mem.valid_block m2 b2 ->
    fst b1 = Mem.tid (Mem.support m1) ->
    f2 b1 = Some (b2, d) -> f1 b1 = Some (b2 ,d).
Proof.
  intros. destruct (f1 b1) as [[b2' d']|] eqn: Hf1.
  - apply H in Hf1. rewrite H3 in Hf1. congruence.
  - exploit H0; eauto. intros [A b]. congruence.
Qed.


Lemma match_callstack_external_call:
  forall f1 f2 m1 m2 m1' m2',
  Mem.unchanged_on_e (loc_unmapped f1) m1 m2 ->
  Mem.unchanged_on_e (loc_out_of_reach f1 m1) m1' m2' ->
  inject_incr f1 f2 ->
  inject_separated_internal f1 f2 m1 m1' ->
  inject_separated_noglobal f1 f2 ->
  Mem.meminj_thread_local f2 ->
  (forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  forall cs bound tbound,
  match_callstack f1 m1 m1' cs bound tbound ->
  Mem.sup_include bound (Mem.support m1) ->
  Mem.sup_include tbound (Mem.support m1') ->
  match_callstack f2 m2 m2' cs bound tbound.
Proof.
  intros until m2'.
  intros UNMAPPED OUTOFREACH INCR SEPARATED NOG TL MAXPERMS.
  induction 1; intros.
(* base case *)
  apply mcs_nil; auto. destruct UNMAPPED as [[A ?] ?]. congruence.
  destruct OUTOFREACH as [[A ?] ?]. congruence.
  destruct UNMAPPED as [[_ X] _]. congruence.
  destruct OUTOFREACH as [[_ X] _]. congruence.
  inv H.
  constructor; eauto. eapply inject_incr_trans; eauto.
  red. intros. case_eq (f1 b1).
  intros [b2' delta'] EQ. 
  destruct w. inv H2. apply INCR in EQ as Heq. rewrite H11 in Heq. inv Heq. eauto.
  intro EQ. exploit SEPARATED; eauto. rewrite INITTID1.
  unfold local_t. rewrite <- H7. simpl. auto. intros [A B].
  unfold Mem.valid_block in *. inv GE; split; eauto.
  red. intros. case_eq (f1 b1).
  intros [b2' delta'] EQ. apply INCR in EQ as Heq. rewrite H2 in Heq. inv Heq.
  eapply H8; eauto. intro EQ. eapply NOG; eauto.
    
(* inductive case *)
  assert (sp = fresh_block sps) by (eapply me_sps; eauto). subst.
  destruct UNMAPPED as [S1 UNMAPPER].
  destruct OUTOFREACH as [S2 OUTOFREACH].
  constructor. destruct S1. congruence. destruct S2. congruence.  auto. auto.
  eapply match_temps_invariant; eauto.
  eapply match_env_invariant; eauto.
  red in SEPARATED. intros. destruct (f1 b) as [[b' delta']|] eqn:?.
  exploit INCR; eauto. intro. split; try congruence.
  eapply TL; eauto.
  exploit SEPARATED; eauto. erewrite match_callstack_tid1; eauto.
  erewrite TL; eauto. simpl. erewrite me_sps_tid; eauto.
  intros [A B]. elim B. red.
  eapply Mem.sup_include_trans; eauto.
  intros. assert (Mem.sup_include bes es) by (eapply me_sup_include; eauto).
  destruct (f1 b) as [[b' delta']|] eqn:?. 
  apply INCR; auto.
  destruct (f2 b) as [[b' delta']|] eqn:?; auto.
  exploit SEPARATED; eauto.  erewrite match_callstack_tid1; eauto.
  intros [A B]. elim A. red.
  eapply Mem.sup_include_trans; eauto.
  eapply match_bounds_invariant; eauto.
  intros. eapply MAXPERMS; eauto. red. exploit me_bounded; eauto.
  intros [A B]. apply H0,BOUND. auto.
  (* padding-freeable *)
  red; intros.
  destruct (is_reachable_from_env_dec f1 e (fresh_block sps) ofs).
  inv H3. right. apply is_reachable_intro with id b sz delta; auto.
  exploit PERM; eauto. intros [A|A]; try contradiction.
  left. eapply Mem.perm_unchanged_on; eauto. 
  split.
  red; intros; red; intros. elim H3.
  exploit me_inv; eauto. intros [id [lv B]].
  exploit BOUND0; eauto. intros C.
  apply is_reachable_intro with id b0 lv delta; auto; lia.
  inv H. rewrite <- TTID0. reflexivity. rewrite <- TTID0. reflexivity.
  red. intros. eapply RANGE; eauto. eapply inject_incr_sep_back; eauto.
  apply H1. apply TBOUND. auto. erewrite match_callstack_tid1; eauto.
  exploit me_local; eauto. intros [A _]. auto.
  (* induction *)
  eapply IHmatch_callstack; eauto. inv MENV.
  eapply Mem.sup_include_trans; eauto.
Qed.

(** [match_callstack] and allocations *)

Lemma match_callstack_alloc_right:
  forall f m tm cs tf tm' sp le te cenv,
  match_callstack f m tm cs (Mem.support m) (Mem.support tm) ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  Mem.inject f m tm ->
  match_temps f le te ->
  (forall id, cenv!id = None) ->
  match_callstack f m tm'
      (Frame cenv tf empty_env le te sp (Mem.support tm) (Mem.support m) (Mem.support m) :: cs)
      (Mem.support m) (Mem.support tm').
Proof.
  intros.
  exploit Mem.support_alloc; eauto. intros SUPPORT.
  exploit Mem.alloc_result; eauto. intros RES.
  constructor. eauto. eauto.
  apply Mem.sup_include_refl.
  subst sp. rewrite SUPPORT.
  apply Mem.sup_include_refl.
  auto.
  constructor; intros. auto. eapply match_callstack_tid2; eauto.
  apply Mem.sup_include_refl.
    rewrite H3. rewrite PTree.gempty. constructor.
    rewrite PTree.gempty in H4; discriminate.
    eelim Mem.fresh_block_alloc; eauto. eapply Mem.valid_block_inject_2; eauto.
    change (Mem.valid_block tm tb). eapply Mem.valid_block_inject_2; eauto.
    apply match_callstack_inj_incr in H. inv H. unfold init_m. destruct w.
    inv H9. eauto. eapply match_callstack_tid1; eauto.
    inv H1. inv mi_thread. inv Hms. auto. inv H4.
  red; intros. rewrite PTree.gempty in H4. discriminate.
  red; intros. left. eapply Mem.perm_alloc_2; eauto.
  red. intros. inv H5.
  eapply match_callstack_invariant with (tm1 := tm); eauto.
  red. intros. congruence.   red. intros. congruence.
  intros. eapply Mem.perm_alloc_1; eauto. rewrite SUPPORT. reflexivity.
Qed.

Lemma match_callstack_alloc_left:
  forall f1 m1 tm id cenv tf e le te sp sps bes cs sz m2 b f2 ofs,
  sp = fresh_block sps ->
  match_callstack f1 m1 tm
    (Frame (PTree.remove id cenv) tf e le te sp sps bes (Mem.support m1) :: cs)
    (Mem.support m1) (Mem.support tm) ->
  Mem.alloc m1 0 sz = (m2, b) ->
  cenv!id = Some ofs ->
  inject_incr f1 f2 ->
  f2 b = Some(sp, ofs) ->
  (forall b', b' <> b -> f2 b' = f1 b') ->
  e!id = None ->
  (forall ofs1, 0 <= ofs1 < sz -> 0 <= ofs1 + ofs < tf.(fn_stackspace)) ->
  match_callstack f2 m2 tm
    (Frame cenv tf (PTree.set id (b, sz) e) le te sp sps bes (Mem.support m2) :: cs)
    (Mem.support m2) (Mem.support tm).
Proof.
  intros. inv H0.
  exploit Mem.support_alloc; eauto. intros SUPPORT.
  exploit Mem.alloc_result; eauto. intros RES.
  assert (LO: Mem.sup_include bes (Mem.support m1)).  (eapply me_sup_include; eauto).
  constructor. auto. auto.
  apply Mem.sup_include_refl. auto.
  eapply match_temps_invariant; eauto.
  eapply match_env_alloc; eauto.
  red; intros. rewrite PTree.gsspec in H. destruct (peq id0 id).
  inversion H. subst b0 sz0 id0. eapply Mem.perm_alloc_3; eauto.
  eapply BOUND0; eauto. eapply Mem.perm_alloc_4; eauto.
  exploit me_bounded; eauto. intros [A B]. intro.
  subst b0. rewrite RES in A. eapply freshness. eauto.
  red; intros. exploit PERM; eauto. intros [A|A]. auto. right.
  inv A. apply is_reachable_intro with id0 b0 sz0 delta; auto.
  rewrite PTree.gso. auto. congruence.
  red. intros. rewrite PTree.gsspec in H0. destruct (peq id0 id).
  inv H0. rewrite H4 in H. inv H. eapply H7; eauto.
  eapply RANGE; eauto. rewrite <- H5; eauto.
  exploit me_bounded; eauto. intros [A B]. intro.
  subst b1. rewrite RES in A. eapply freshness. eauto.
  eapply match_callstack_invariant with (m1 := m1); eauto.
  red. intros. destruct (eq_block b1 b). subst. split.
  eapply Mem.alloc_block_noglobal; eauto.
  rewrite H4 in H0. inv H0. unfold Genv.global_block. simpl. generalize (Mem.tid_valid sps). intro. lia.
  erewrite H5 in H0; eauto. congruence.
  red. intros. destruct (eq_block b1 b).
  subst. rewrite H4 in H0. inv H0.
  simpl.
  erewrite match_callstack_tid1; eauto.
  erewrite me_sps_tid; eauto. erewrite H5 in H0; eauto.
  congruence.
  intros. eapply Mem.perm_alloc_4; eauto.
  intro. subst b0. eapply freshness; eauto. eapply LO.
  rewrite RES in H. auto.
  intros. apply H5. intro. eapply freshness. eapply LO.
  subst b0. subst b. auto.
  intros. destruct (eq_block b0 b).
  subst b0. rewrite H4 in H. inv H. apply freshness in H0. destruct H0.
  rewrite H5 in H; auto. rewrite SUPPORT. reflexivity.
Qed.

(** * Correctness of stack allocation of local variables *)

(** This section shows the correctness of the translation of Csharpminor
  local variables as sub-blocks of the Cminor stack data.  This is the most difficult part of the proof. *)

Definition cenv_remove (cenv: compilenv) (vars: list (ident * Z)) : compilenv :=
  fold_right (fun id_lv ce => PTree.remove (fst id_lv) ce) cenv vars.

Remark cenv_remove_gso:
  forall id vars cenv,
  ~In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = PTree.get id cenv.
Proof.
  induction vars; simpl; intros.
  auto.
  rewrite PTree.gro. apply IHvars. intuition. intuition.
Qed.

Remark cenv_remove_gss:
  forall id vars cenv,
  In id (map fst vars) ->
  PTree.get id (cenv_remove cenv vars) = None.
Proof.
  induction vars; simpl; intros.
  contradiction.
  rewrite PTree.grspec. destruct (PTree.elt_eq id (fst a)). auto.
  destruct H. intuition. eauto.
Qed.

Definition cenv_compat (cenv: compilenv) (vars: list (ident * Z)) (tsz: Z) : Prop :=
  forall id sz,
  In (id, sz) vars ->
  exists ofs,
      PTree.get id cenv = Some ofs
   /\ Mem.inj_offset_aligned ofs sz
   /\ 0 <= ofs
   /\ ofs + Z.max 0 sz <= tsz.

Definition cenv_separated (cenv: compilenv) (vars: list (ident * Z)) : Prop :=
  forall id1 sz1 ofs1 id2 sz2 ofs2,
  In (id1, sz1) vars -> In (id2, sz2) vars ->
  PTree.get id1 cenv = Some ofs1 -> PTree.get id2 cenv = Some ofs2 ->
  id1 <> id2 ->
  ofs1 + sz1 <= ofs2 \/ ofs2 + sz2 <= ofs1.

Definition cenv_mem_separated (cenv: compilenv) (vars: list (ident * Z)) (f: meminj) (sp: block) (m: mem) : Prop :=
  forall id sz ofs b delta ofs' k p,
  In (id, sz) vars -> PTree.get id cenv = Some ofs ->
  f b = Some (sp, delta) ->
  Mem.perm m b ofs' k p ->
  ofs <= ofs' + delta < sz + ofs -> False.

Lemma match_callstack_alloc_variables_rec:
  forall tm sp sps tf cenv le te bes cs,
  Mem.tid sps = Mem.tid (Mem.support tm) ->
  sp = fresh_block sps ->
  Mem.valid_block tm sp ->
  fn_stackspace tf <= Ptrofs.max_unsigned ->
  (forall ofs k p, Mem.perm tm sp ofs k p -> 0 <= ofs < fn_stackspace tf) ->
  (forall ofs k p, 0 <= ofs < fn_stackspace tf -> Mem.perm tm sp ofs k p) ->
  forall e1 m1 vars e2 m2,
  alloc_variables e1 m1 vars e2 m2 ->
  forall f1,
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace tf) ->
  cenv_separated cenv vars ->
  cenv_mem_separated cenv vars f1 sp m1 ->
  (forall id sz, In (id, sz) vars -> e1!id = None) ->
  match_callstack f1 m1 tm
    (Frame (cenv_remove cenv vars) tf e1 le te sp sps bes (Mem.support m1) :: cs)
    (Mem.support m1) (Mem.support tm) ->
  Mem.inject f1 m1 tm ->
  exists f2,
    match_callstack f2 m2 tm
      (Frame cenv tf e2 le te sp sps bes (Mem.support m2) :: cs)
      (Mem.support m2) (Mem.support tm)
    /\ Mem.inject f2 m2 tm
    /\ inject_incr f1 f2
    /\ (forall b1 b2 d, f1 b1 = None -> f2 b1 = Some (b2, d) -> ~ Mem.valid_block m1 b1 /\ ~ sup_In b2 sps)
    /\ inject_incr_local f1 f2 m1.
Proof.
  intros until cs; intros THE SPS VALID REPRES STKSIZE STKPERMS.
  induction 1; intros f1 NOREPET COMPAT SEP1 SEP2 UNBOUND MCS MINJ.
  (* base case *)
  - simpl in MCS. exists f1; auto. intuition auto. congruence. congruence. congruence.
  (* inductive case *)
  - simpl in NOREPET. inv NOREPET.
(* exploit Mem.alloc_result; eauto. intros RES.
  exploit Mem.support_alloc; eauto. intros NB.*)
  exploit (COMPAT id sz). auto with coqlib. intros [ofs [CENV [ALIGNED [LOB HIB]]]].
  exploit Mem.alloc_left_mapped_inject.
    2: eexact MINJ.
    2: eexact H.
    2: eexact VALID. simpl. auto.
    instantiate (1 := ofs). zify. lia.
    intros. exploit STKSIZE; eauto. lia.
    intros. apply STKPERMS. zify. lia.
    replace (sz - 0) with sz by lia. auto.
    intros. eapply SEP2. eauto with coqlib. eexact CENV. eauto. eauto. lia.
  intros [f2 [A [B [C D]]]].
  exploit (IHalloc_variables f2); eauto.
    red; intros. eapply COMPAT. auto with coqlib.
    red; intros. eapply SEP1; eauto with coqlib.
    red; intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b b1); intros P.
    subst b. rewrite C in H5; inv H5.
    exploit SEP1. eapply in_eq. eapply in_cons; eauto. eauto. eauto.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    lia.
    eapply SEP2. apply in_cons; eauto. eauto.
    rewrite D in H5; eauto. eauto. auto.
    intros. rewrite PTree.gso. eapply UNBOUND; eauto with coqlib.
    red; intros; subst id0. elim H3. change id with (fst (id, sz0)). apply in_map; auto.
    eapply match_callstack_alloc_left; eauto.
    rewrite cenv_remove_gso; auto.
    apply UNBOUND with sz; auto with coqlib.
    intros. lia.
    intros (f3 & E & F & G & I & J).
    exists f3. repeat apply conj; eauto. eapply inject_incr_trans; eauto.
    intros. destruct (eq_block b0 b1). subst. split. eauto with mem.
    apply G in C as Heq. rewrite Heq in H2. inv H2. eapply freshness.
    erewrite <- D in H1; eauto. exploit I; eauto. intros [X Y]. split; eauto with mem.
    red. intros. destruct (eq_block b0 b1). subst.
    apply Mem.alloc_result in H. rewrite H. reflexivity.
    erewrite <- D in H1; eauto. exploit  J; eauto. intro.
    erewrite Mem.support_alloc in H5; eauto. simpl in H5. congruence.
Qed.

Lemma match_callstack_alloc_variables:
  forall tm1 sp tm2 m1 vars e m2 cenv f1 cs fn le te,
  Mem.alloc tm1 0 (fn_stackspace fn) = (tm2, sp) ->
  fn_stackspace fn <= Ptrofs.max_unsigned ->
  alloc_variables empty_env m1 vars e m2 ->
  list_norepet (map fst vars) ->
  cenv_compat cenv vars (fn_stackspace fn) ->
  cenv_separated cenv vars ->
  (forall id ofs, cenv!id = Some ofs -> In id (map fst vars)) ->
  Mem.inject f1 m1 tm1 ->
  match_callstack f1 m1 tm1 cs (Mem.support m1) (Mem.support tm1) ->
  match_temps f1 le te ->
  exists f2,
    match_callstack f2 m2 tm2 (Frame cenv fn e le te sp (Mem.support tm1) (Mem.support m1) (Mem.support m2) :: cs)
                    (Mem.support m2) (Mem.support tm2)
    /\ Mem.inject f2 m2 tm2
    /\ inject_incr f1 f2
    /\ inject_separated f1 f2 m1 tm1
    /\ inject_incr_local f1 f2 m1.
Proof.
  intros.
  eapply match_callstack_alloc_variables_rec; eauto.
  inv H. reflexivity.
  eapply Mem.alloc_result; eauto.
  eapply Mem.valid_new_block; eauto.
  intros. eapply Mem.perm_alloc_3; eauto.
  intros. apply Mem.perm_implies with Freeable; auto with mem. eapply Mem.perm_alloc_2; eauto.
  red; intros. eelim Mem.fresh_block_alloc; eauto.
  eapply Mem.valid_block_inject_2; eauto.
  eapply match_callstack_alloc_right; eauto.
  intros. destruct (In_dec peq id (map fst vars)).
  apply cenv_remove_gss; auto.
  rewrite cenv_remove_gso; auto.
  destruct (cenv!id) as [ofs|] eqn:?; auto. elim n; eauto.
  eapply Mem.alloc_right_inject; eauto.
Qed.

(** Properties of the compilation environment produced by [build_compilenv] *)

Remark block_alignment_pos:
  forall sz, block_alignment sz > 0.
Proof.
  unfold block_alignment; intros.
  destruct (zlt sz 2). lia.
  destruct (zlt sz 4). lia.
  destruct (zlt sz 8); lia.
Qed.

Remark assign_variable_incr:
  forall id sz cenv stksz cenv' stksz',
  assign_variable (cenv, stksz) (id, sz) = (cenv', stksz') -> stksz <= stksz'.
Proof.
  simpl; intros. inv H.
  generalize (align_le stksz (block_alignment sz) (block_alignment_pos sz)).
  assert (0 <= Z.max 0 sz). apply Zmax_bound_l. lia.
  lia.
Qed.

Remark assign_variables_incr:
  forall vars cenv sz cenv' sz',
  assign_variables (cenv, sz) vars = (cenv', sz') -> sz <= sz'.
Proof.
  induction vars; intros until sz'.
  simpl; intros. inv H. lia.
Opaque assign_variable.
  destruct a as [id s]. simpl. intros.
  destruct (assign_variable (cenv, sz) (id, s)) as [cenv1 sz1] eqn:?.
  apply Z.le_trans with sz1. eapply assign_variable_incr; eauto. eauto.
Transparent assign_variable.
Qed.

Remark inj_offset_aligned_block:
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) sz.
Proof.
  intros; red; intros.
  apply Z.divide_trans with (block_alignment sz).
  unfold align_chunk.  unfold block_alignment.
  generalize Z.divide_1_l; intro.
  generalize Z.divide_refl; intro.
  assert (2 | 4). exists 2; auto.
  assert (2 | 8). exists 4; auto.
  assert (4 | 8). exists 2; auto.
  destruct (zlt sz 2).
  destruct chunk; simpl in *; auto; extlia.
  destruct (zlt sz 4).
  destruct chunk; simpl in *; auto; extlia.
  destruct (zlt sz 8).
  destruct chunk; simpl in *; auto; extlia.
  destruct chunk; simpl; auto.
  apply align_divides. apply block_alignment_pos.
Qed.

Remark inj_offset_aligned_block':
  forall stacksize sz,
  Mem.inj_offset_aligned (align stacksize (block_alignment sz)) (Z.max 0 sz).
Proof.
  intros.
  replace (block_alignment sz) with (block_alignment (Z.max 0 sz)).
  apply inj_offset_aligned_block.
  rewrite Zmax_spec. destruct (zlt sz 0); auto.
  transitivity 1. reflexivity. unfold block_alignment. rewrite zlt_true. auto. lia.
Qed.

Lemma assign_variable_sound:
  forall cenv1 sz1 id sz cenv2 sz2 vars,
  assign_variable (cenv1, sz1) (id, sz) = (cenv2, sz2) ->
  ~In id (map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ (id, sz) :: nil) sz2
  /\ cenv_separated cenv2 (vars ++ (id, sz) :: nil).
Proof.
  unfold assign_variable; intros until vars; intros ASV NOREPET POS COMPAT SEP.
  inv ASV.
  assert (LE: sz1 <= align sz1 (block_alignment sz)). apply align_le. apply block_alignment_pos.
  assert (EITHER: forall id' sz',
             In (id', sz') (vars ++ (id, sz) :: nil) ->
             In (id', sz') vars /\ id' <> id \/ (id', sz') = (id, sz)).
    intros. rewrite in_app in H. destruct H.
    left; split; auto. red; intros; subst id'. elim NOREPET.
    change id with (fst (id, sz')). apply in_map; auto.
    simpl in H. destruct H. auto. contradiction.
  split; red; intros.
  apply EITHER in H. destruct H as [[P Q] | P].
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  exists ofs.
  split. rewrite PTree.gso; auto.
  split. auto. split. auto. zify; lia.
  inv P. exists (align sz1 (block_alignment sz)).
  split. apply PTree.gss.
  split. apply inj_offset_aligned_block.
  split. lia.
  lia.
  apply EITHER in H; apply EITHER in H0.
  destruct H as [[P Q] | P]; destruct H0 as [[R S] | R].
  rewrite PTree.gso in *; auto. eapply SEP; eauto.
  inv R. rewrite PTree.gso in H1; auto. rewrite PTree.gss in H2; inv H2.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  assert (ofs = ofs1) by congruence. subst ofs.
  left. zify; lia.
  inv P. rewrite PTree.gso in H2; auto. rewrite PTree.gss in H1; inv H1.
  exploit COMPAT; eauto. intros [ofs [A [B [C D]]]].
  assert (ofs = ofs2) by congruence. subst ofs.
  right. zify; lia.
  congruence.
Qed.

Lemma assign_variables_sound:
  forall vars' cenv1 sz1 cenv2 sz2 vars,
  assign_variables (cenv1, sz1) vars' = (cenv2, sz2) ->
  list_norepet (map fst vars' ++ map fst vars) ->
  0 <= sz1 ->
  cenv_compat cenv1 vars sz1 ->
  cenv_separated cenv1 vars ->
  cenv_compat cenv2 (vars ++ vars') sz2 /\ cenv_separated cenv2 (vars ++ vars').
Proof.
  induction vars'; simpl; intros.
  rewrite app_nil_r. inv H; auto.
  destruct a as [id sz].
  simpl in H0. inv H0. rewrite in_app in H6.
  rewrite list_norepet_app in H7. destruct H7 as [P [Q R]].
  destruct (assign_variable (cenv1, sz1) (id, sz)) as [cenv' sz'] eqn:?.
  exploit assign_variable_sound.
    eauto.
    instantiate (1 := vars). tauto.
    auto. auto. auto.
  intros [A B].
  exploit IHvars'.
    eauto.
    instantiate (1 := vars ++ ((id, sz) :: nil)).
    rewrite list_norepet_app. split. auto.
    split. rewrite map_app. apply list_norepet_append_commut. simpl. constructor; auto.
    rewrite map_app. simpl. red; intros. rewrite in_app in H4. destruct H4.
    eauto. simpl in H4. destruct H4. subst y. red; intros; subst x. tauto. tauto.
    generalize (assign_variable_incr _ _ _ _ _ _ Heqp). lia.
    auto. auto.
  rewrite app_ass. auto.
Qed.

Remark permutation_norepet:
  forall (A: Type) (l l': list A), Permutation l l' -> list_norepet l -> list_norepet l'.
Proof.
  induction 1; intros.
  constructor.
  inv H0. constructor; auto. red; intros; elim H3. apply Permutation_in with l'; auto. apply Permutation_sym; auto.
  inv H. simpl in H2. inv H3. constructor. simpl; intuition. constructor. intuition. auto.
  eauto.
Qed.

Lemma build_compilenv_sound:
  forall f cenv sz,
  build_compilenv f = (cenv, sz) ->
  list_norepet (map fst (Csharpminor.fn_vars f)) ->
  cenv_compat cenv (Csharpminor.fn_vars f) sz /\ cenv_separated cenv (Csharpminor.fn_vars f).
Proof.
  unfold build_compilenv; intros.
  set (vars1 := Csharpminor.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  assert (cenv_compat cenv vars2 sz /\ cenv_separated cenv vars2).
    change vars2 with (nil ++ vars2).
    eapply assign_variables_sound.
    eexact H.
    simpl. rewrite app_nil_r. apply permutation_norepet with (map fst vars1); auto.
    apply Permutation_map. auto.
    lia.
    red; intros. contradiction.
    red; intros. contradiction.
  destruct H1 as [A B]. split.
  red; intros. apply A. apply Permutation_in with vars1; auto.
  red; intros. eapply B; eauto; apply Permutation_in with vars1; auto.
Qed.

Lemma assign_variables_domain:
  forall id vars cesz,
  (fst (assign_variables cesz vars))!id <> None ->
  (fst cesz)!id <> None \/ In id (map fst vars).
Proof.
  induction vars; simpl; intros.
  auto.
  exploit IHvars; eauto. unfold assign_variable. destruct a as [id1 sz1].
  destruct cesz as [cenv stksz]. simpl.
  rewrite PTree.gsspec. destruct (peq id id1). auto. tauto.
Qed.

Lemma build_compilenv_domain:
  forall f cenv sz id ofs,
  build_compilenv f = (cenv, sz) ->
  cenv!id = Some ofs -> In id (map fst (Csharpminor.fn_vars f)).
Proof.
  unfold build_compilenv; intros.
  set (vars1 := Csharpminor.fn_vars f) in *.
  generalize (VarSort.Permuted_sort vars1). intros P.
  set (vars2 := VarSort.sort vars1) in *.
  generalize (assign_variables_domain id vars2 (PTree.empty Z, 0)).
  rewrite H. simpl. intros. destruct H1. congruence.
  rewrite PTree.gempty in H1. congruence.
  apply Permutation_in with (map fst vars2); auto.
  apply Permutation_map. apply Permutation_sym; auto.
Qed.

(** Initialization of C#minor temporaries and Cminor local variables. *)

Lemma create_undef_temps_val:
  forall id v temps, (create_undef_temps temps)!id = Some v -> In id temps /\ v = Vundef.
Proof.
  induction temps; simpl; intros.
  rewrite PTree.gempty in H. congruence.
  rewrite PTree.gsspec in H. destruct (peq id a).
  split. auto. congruence.
  exploit IHtemps; eauto. tauto.
Qed.

Fixpoint set_params' (vl: list val) (il: list ident) (te: Cminor.env) : Cminor.env :=
  match il, vl with
  | i1 :: is, v1 :: vs => set_params' vs is (PTree.set i1 v1 te)
  | i1 :: is, nil => set_params' nil is (PTree.set i1 Vundef te)
  | _, _ => te
  end.

Lemma bind_parameters_agree_rec:
  forall f vars vals tvals le1 le2 te,
  bind_parameters vars vals le1 = Some le2 ->
  Val.inject_list f vals tvals ->
  match_temps f le1 te ->
  match_temps f le2 (set_params' tvals vars te).
Proof.
Opaque PTree.set.
  induction vars; simpl; intros.
  destruct vals; try discriminate. inv H. auto.
  destruct vals; try discriminate. inv H0.
  simpl. eapply IHvars; eauto.
  red; intros. rewrite PTree.gsspec in *. destruct (peq id a).
  inv H0. exists v'; auto.
  apply H1; auto.
Qed.

Lemma set_params'_outside:
  forall id il vl te, ~In id il -> (set_params' vl il te)!id = te!id.
Proof.
  induction il; simpl; intros. auto.
  destruct vl; rewrite IHil.
  apply PTree.gso. intuition. intuition.
  apply PTree.gso. intuition. intuition.
Qed.

Lemma set_params'_inside:
  forall id il vl te1 te2,
  In id il ->
  (set_params' vl il te1)!id = (set_params' vl il te2)!id.
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct vl; destruct (List.in_dec peq id il); auto;
  repeat rewrite set_params'_outside; auto;
  assert (a = id) by intuition; subst a; repeat rewrite PTree.gss; auto.
Qed.

Lemma set_params_set_params':
  forall il vl id,
  list_norepet il ->
  (set_params vl il)!id = (set_params' vl il (PTree.empty val))!id.
Proof.
  induction il; simpl; intros.
  auto.
  inv H. destruct vl.
  rewrite PTree.gsspec. destruct (peq id a).
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto.
  rewrite PTree.gsspec. destruct (peq id a).
  subst a. rewrite set_params'_outside; auto. rewrite PTree.gss; auto.
  rewrite IHil; auto.
  destruct (List.in_dec peq id il). apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto. rewrite PTree.gso; auto.
Qed.

Lemma set_locals_outside:
  forall e id il,
  ~In id il -> (set_locals il e)!id = e!id.
Proof.
  induction il; simpl; intros.
  auto.
  rewrite PTree.gso. apply IHil. tauto. intuition.
Qed.

Lemma set_locals_inside:
  forall e id il,
  In id il -> (set_locals il e)!id = Some Vundef.
Proof.
  induction il; simpl; intros.
  contradiction.
  destruct H. subst a. apply PTree.gss.
  rewrite PTree.gsspec. destruct (peq id a). auto. auto.
Qed.

Lemma set_locals_set_params':
  forall vars vals params id,
  list_norepet params ->
  list_disjoint params vars ->
  (set_locals vars (set_params vals params)) ! id =
  (set_params' vals params (set_locals vars (PTree.empty val))) ! id.
Proof.
  intros. destruct (in_dec peq id vars).
  assert (~In id params). apply list_disjoint_notin with vars; auto. apply list_disjoint_sym; auto.
  rewrite set_locals_inside; auto. rewrite set_params'_outside; auto. rewrite set_locals_inside; auto.
  rewrite set_locals_outside; auto. rewrite set_params_set_params'; auto.
  destruct (in_dec peq id params).
  apply set_params'_inside; auto.
  repeat rewrite set_params'_outside; auto.
  rewrite set_locals_outside; auto.
Qed.

Lemma bind_parameters_agree:
  forall f params temps vals tvals le,
  bind_parameters params vals (create_undef_temps temps) = Some le ->
  Val.inject_list f vals tvals ->
  list_norepet params ->
  list_disjoint params temps ->
  match_temps f le (set_locals temps (set_params tvals params)).
Proof.
  intros; red; intros.
  exploit bind_parameters_agree_rec; eauto.
  instantiate (1 := set_locals temps (PTree.empty val)).
  red; intros. exploit create_undef_temps_val; eauto. intros [A B]. subst v0.
  exists Vundef; split. apply set_locals_inside; auto. auto.
  intros [v' [A B]]. exists v'; split; auto.
  rewrite <- A. apply set_locals_set_params'; auto.
Qed.

(** The main result in this section. *)

Theorem match_callstack_function_entry:
  forall fn cenv tf m e m' tm tm' sp f cs args targs le,
  build_compilenv fn = (cenv, tf.(fn_stackspace)) ->
  tf.(fn_stackspace) <= Ptrofs.max_unsigned ->
  list_norepet (map fst (Csharpminor.fn_vars fn)) ->
  list_norepet (Csharpminor.fn_params fn) ->
  list_disjoint (Csharpminor.fn_params fn) (Csharpminor.fn_temps fn) ->
  alloc_variables Csharpminor.empty_env m (Csharpminor.fn_vars fn) e m' ->
  bind_parameters (Csharpminor.fn_params fn) args (create_undef_temps fn.(fn_temps)) = Some le ->
  Val.inject_list f args targs ->
  Mem.alloc tm 0 tf.(fn_stackspace) = (tm', sp) ->
  match_callstack f m tm cs (Mem.support m) (Mem.support tm) ->
  Mem.inject f m tm ->
  let te := set_locals (Csharpminor.fn_temps fn) (set_params targs (Csharpminor.fn_params fn)) in
  exists f',
     match_callstack f' m' tm'
                     (Frame cenv tf e le te sp (Mem.support tm) (Mem.support m) (Mem.support m') :: cs)
                     (Mem.support m') (Mem.support tm')
     /\ Mem.inject f' m' tm'
     /\ inject_incr f f'
     /\ inject_separated f f' m tm
     /\ inject_incr_local f f' m.
Proof.
  intros.
  exploit build_compilenv_sound; eauto. intros [C1 C2].
  eapply match_callstack_alloc_variables; eauto.
  intros. eapply build_compilenv_domain; eauto.
  eapply bind_parameters_agree; eauto.
Qed.

(** * Compatibility of evaluation functions with respect to memory injections. *)

Remark val_inject_val_of_bool:
  forall f b, Val.inject f (Val.of_bool b) (Val.of_bool b).
Proof.
  intros; destruct b; constructor.
Qed.

Remark val_inject_val_of_optbool:
  forall f ob, Val.inject f (Val.of_optbool ob) (Val.of_optbool ob).
Proof.
  intros; destruct ob; simpl. destruct b; constructor. constructor.
Qed.

Ltac TrivialExists :=
  match goal with
  | [ |- exists y, Some ?x = Some y /\ Val.inject _ _ _ ] =>
      exists x; split; [auto | try(econstructor; eauto)]
  | [ |- exists y, _ /\ Val.inject _ (Vint ?x) _ ] =>
      exists (Vint x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ Val.inject _ (Vfloat ?x) _ ] =>
      exists (Vfloat x); split; [eauto with evalexpr | constructor]
  | [ |- exists y, _ /\ Val.inject _ (Vlong ?x) _ ] =>
      exists (Vlong x); split; [eauto with evalexpr | constructor]
  | _ => idtac
  end.

(** Compatibility of [eval_unop] with respect to [Val.inject]. *)

Lemma eval_unop_compat:
  forall f op v1 tv1 v,
  eval_unop op v1 = Some v ->
  Val.inject f v1 tv1 ->
  exists tv,
     eval_unop op tv1 = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct op; simpl; intros.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_int f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_intu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_int f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_intu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H; inv H0; simpl; TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_long f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float.to_longu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_long f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. destruct (Float32.to_longu f0); simpl in *; inv H1. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
  inv H0; simpl in H; inv H. simpl. TrivialExists.
Qed.

(** Compatibility of [eval_binop] with respect to [Val.inject]. *)

Lemma eval_binop_compat:
  forall f op v1 tv1 v2 tv2 v m tm,
  eval_binop op v1 v2 m = Some v ->
  Val.inject f v1 tv1 ->
  Val.inject f v2 tv2 ->
  Mem.inject f m tm ->
  exists tv,
     eval_binop op tv1 tv2 tm = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct op; simpl; intros; inv H.
- TrivialExists. apply Val.add_inject; auto.
- TrivialExists. apply Val.sub_inject; auto.
- TrivialExists. inv H0; inv H1; constructor.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H4. TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero
      || Int.eq i (Int.repr Int.min_signed) && Int.eq i0 Int.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int.eq i0 Int.zero); inv H4. TrivialExists.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int.iwordsize); constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists. apply Val.addl_inject; auto.
- TrivialExists. apply Val.subl_inject; auto.
- TrivialExists. inv H0; inv H1; constructor.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H4. TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero
      || Int64.eq i (Int64.repr Int64.min_signed) && Int64.eq i0 Int64.mone); inv H4; TrivialExists.
- inv H0; try discriminate; inv H1; try discriminate. simpl in *.
    destruct (Int64.eq i0 Int64.zero); inv H4. TrivialExists.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- TrivialExists; inv H0; inv H1; simpl; auto.
  destruct (Int.ltu i0 Int64.iwordsize'); constructor.
- (* cmp *)
  TrivialExists. inv H0; inv H1; auto. apply val_inject_val_of_optbool.
- (* cmpu *)
  TrivialExists. unfold Val.cmpu.
  destruct (Val.cmpu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  replace (Val.cmpu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  apply val_inject_val_of_optbool.
  symmetry. eapply Val.cmpu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  simpl; auto.
- (* cmpf *)
  TrivialExists. inv H0; inv H1; auto. apply val_inject_val_of_optbool.
- (* cmpfs *)
  TrivialExists. inv H0; inv H1; auto. apply val_inject_val_of_optbool.
- (* cmpl *)
  unfold Val.cmpl in *. inv H0; inv H1; simpl in H4; inv H4.
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
- (* cmplu *)
  unfold Val.cmplu in *.
  destruct (Val.cmplu_bool (Mem.valid_pointer m) c v1 v2) as [b|] eqn:E.
  simpl in H4; inv H4.
  replace (Val.cmplu_bool (Mem.valid_pointer tm) c tv1 tv2) with (Some b).
  econstructor; split. simpl; eauto. apply val_inject_val_of_bool.
  symmetry. eapply Val.cmplu_bool_inject; eauto.
  intros; eapply Mem.valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_val; eauto.
  intros; eapply Mem.weak_valid_pointer_inject_no_overflow; eauto.
  intros; eapply Mem.different_pointers_inject; eauto.
  discriminate.
Qed.

(** * Correctness of Cminor construction functions *)

(** Correctness of the variable accessor [var_addr] *)

Lemma var_addr_correct:
  forall cenv id f tf e le te sp sps bes es m cs tm b,
  match_callstack f m tm (Frame cenv tf e le te sp sps bes es :: cs) (Mem.support m) (Mem.support tm) ->
  eval_var_addr ge e id b ->
  exists tv,
     eval_expr tge (Vptr sp Ptrofs.zero) te tm (var_addr cenv id) tv
  /\ Val.inject f (Vptr b Ptrofs.zero) tv.
Proof.
  unfold var_addr; intros.
  assert (match_var f sp e!id cenv!id).
    inv H. inv MENV. auto.
  inv H1; inv H0; try congruence.
  (* local *)
  exists (Vptr sp (Ptrofs.repr ofs)); split.
  constructor. simpl. rewrite Ptrofs.add_zero_l; auto.
  congruence.
  (* global *)
  exploit match_callstack_match_globalenvs; eauto. intros MG.
  edestruct @Genv.find_symbol_match as (tb & Htb & Htid); eauto.
  exists (Vptr tb Ptrofs.zero); split.
  constructor. simpl. unfold Genv.symbol_address. 
  rewrite Htid. auto.
  econstructor; eauto.
Qed.

(** * Semantic preservation for the translation *)

(** The proof of semantic preservation uses simulation diagrams of the
  following form:
<<
       e, m1, s ----------------- sp, te1, tm1, ts
          |                                |
         t|                                |t
          v                                v
       e, m2, out --------------- sp, te2, tm2, tout
>>
  where [ts] is the Cminor statement obtained by translating the
  C#minor statement [s].  The left vertical arrow is an execution
  of a C#minor statement.  The right vertical arrow is an execution
  of a Cminor statement.  The precondition (top vertical bar)
  includes a [mem_inject] relation between the memory states [m1] and [tm1],
  and a [match_callstack] relation for any callstack having
  [e], [te1], [sp] as top frame.  The postcondition (bottom vertical bar)
  is the existence of a memory injection [f2] that extends the injection
  [f1] we started with, preserves the [match_callstack] relation for
  the transformed callstack at the final state, and validates a
  [outcome_inject] relation between the outcomes [out] and [tout].
*)

(** ** Semantic preservation for expressions *)

Remark bool_of_val_inject:
  forall f v tv b,
  Val.bool_of_val v b -> Val.inject f v tv -> Val.bool_of_val tv b.
Proof.
  intros. inv H0; inv H; constructor; auto.
Qed.

Lemma transl_constant_correct:
  forall f sp cst v,
  Csharpminor.eval_constant cst = Some v ->
  exists tv,
     eval_constant tge sp (transl_constant cst) = Some tv
  /\ Val.inject f v tv.
Proof.
  destruct cst; simpl; intros; inv H.
  exists (Vint i); auto.
  exists (Vfloat f0); auto.
  exists (Vsingle f0); auto.
  exists (Vlong i); auto.
Qed.

Lemma transl_expr_correct:
  forall f m tm cenv tf e le te sp sps bes es cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp sps bes es :: cs)
             (Mem.support m) (Mem.support tm)),
  forall a v,
  Csharpminor.eval_expr ge e le m a v ->
  forall ta
    (TR: transl_expr cenv a = OK ta),
  exists tv,
     eval_expr tge (Vptr sp Ptrofs.zero) te tm ta tv
  /\ Val.inject f v tv.
Proof.
  induction 3; intros; simpl in TR; try (monadInv TR).
  (* Etempvar *)
  inv MATCH. exploit MTMP; eauto. intros [tv [A B]].
  exists tv; split. constructor; auto. auto.
  (* Eaddrof *)
  eapply var_addr_correct; eauto.
  (* Econst *)
  exploit transl_constant_correct; eauto. intros [tv [A B]].
  exists tv; split; eauto. constructor; eauto.
  (* Eunop *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit eval_unop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split; auto. econstructor; eauto.
  (* Ebinop *)
  exploit IHeval_expr1; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit IHeval_expr2; eauto. intros [tv2 [EVAL2 INJ2]].
  exploit eval_binop_compat; eauto. intros [tv [EVAL INJ]].
  exists tv; split. econstructor; eauto. auto.
  (* Eload *)
  exploit IHeval_expr; eauto. intros [tv1 [EVAL1 INJ1]].
  exploit Mem.loadv_inject; eauto. intros [tv [LOAD INJ]].
  exists tv; split. econstructor; eauto. auto.
Qed.

Lemma transl_exprlist_correct:
  forall f m tm cenv tf e le te sp sps bes es cs
    (MINJ: Mem.inject f m tm)
    (MATCH: match_callstack f m tm
             (Frame cenv tf e le te sp sps bes es :: cs)
             (Mem.support m) (Mem.support tm)),
  forall a v,
  Csharpminor.eval_exprlist ge e le m a v ->
  forall ta
    (TR: transl_exprlist cenv a = OK ta),
  exists tv,
     eval_exprlist tge (Vptr sp Ptrofs.zero) te tm ta tv
  /\ Val.inject_list f v tv.
Proof.
  induction 3; intros; monadInv TR.
  exists (@nil val); split. constructor. constructor.
  exploit transl_expr_correct; eauto. intros [tv1 [EVAL1 VINJ1]].
  exploit IHeval_exprlist; eauto. intros [tv2 [EVAL2 VINJ2]].
  exists (tv1 :: tv2); split. constructor; auto. constructor; auto.
Qed.

(** ** Semantic preservation for statements and functions *)

Inductive match_cont: Csharpminor.cont -> Cminor.cont -> compilenv -> exit_env -> callstack -> Prop :=
  | match_Kstop: forall cenv xenv,
      match_cont Csharpminor.Kstop Kstop cenv xenv nil
  | match_Kseq: forall s k ts tk cenv xenv cs,
      transl_stmt cenv xenv s = OK ts ->
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kseq s k) (Kseq ts tk) cenv xenv cs
  | match_Kseq2: forall s1 s2 k ts1 tk cenv xenv cs,
      transl_stmt cenv xenv s1 = OK ts1 ->
      match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs ->
      match_cont (Csharpminor.Kseq (Csharpminor.Sseq s1 s2) k)
                 (Kseq ts1 tk) cenv xenv cs
  | match_Kblock: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont (Csharpminor.Kblock k) (Kblock tk) cenv (true :: xenv) cs
  | match_Kblock2: forall k tk cenv xenv cs,
      match_cont k tk cenv xenv cs ->
      match_cont k (Kblock tk) cenv (false :: xenv) cs
  | match_Kcall: forall optid fn e le k tfn sp sps te tk cenv xenv bes es cs sz cenv',
      transl_funbody cenv sz fn = OK tfn ->
      match_cont k tk cenv xenv cs ->
      sp = fresh_block sps ->
      match_cont (Csharpminor.Kcall optid fn e le k)
                 (Kcall optid tfn (Vptr sp Ptrofs.zero) te tk)
                 cenv' nil
                 (Frame cenv tfn e le te sp sps bes es :: cs).

Inductive match_states: injp_world -> Csharpminor.state -> Cminor.state -> Prop :=
  | match_state:
      forall fn s k e le m tfn ts tk sp sps te tm cenv xenv f bes es cs sz Hm wp
      (SPS: sp = fresh_block sps)
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s = OK ts)
      (ACCE: injp_acce w (injpw f m tm Hm))
      (ACCI: injp_acci wp (injpw f m tm Hm))
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp sps bes es :: cs)
               (Mem.support m) (Mem.support tm))
      (MK: match_cont k tk cenv xenv cs),
      match_states wp (Csharpminor.State fn s k e le m)
                   (State tfn ts tk (Vptr sp Ptrofs.zero) te tm)
  | match_state_seq:
      forall fn s1 s2 k e le m tfn ts1 tk sp sps te tm cenv xenv f bes es cs sz Hm wp
      (SPS: sp = fresh_block sps)
      (TRF: transl_funbody cenv sz fn = OK tfn)
      (TR: transl_stmt cenv xenv s1 = OK ts1)
      (ACCE: injp_acce w (injpw f m tm Hm))
      (ACCI: injp_acci wp (injpw f m tm Hm))
      (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp sps bes es :: cs)
               (Mem.support m) (Mem.support tm))
      (MK: match_cont (Csharpminor.Kseq s2 k) tk cenv xenv cs),
      match_states wp (Csharpminor.State fn (Csharpminor.Sseq s1 s2) k e le m)
                   (State tfn ts1 tk (Vptr sp Ptrofs.zero) te tm)
  | match_callstate:
      forall v args k m tv targs tk tm f cs cenv Hm wp
      (FINJ: Val.inject f v tv)
      (ACCE: injp_acce w (injpw f m tm Hm))
      (ACCI: injp_acci wp (injpw f m tm Hm))
      (MCS: match_callstack f m tm cs (Mem.support m) (Mem.support tm))
      (MK: match_cont k tk cenv nil cs)
      (ISCC: Csharpminor.is_call_cont k)
      (ARGSINJ: Val.inject_list f args targs),
      match_states wp (Csharpminor.Callstate v args k m)
                   (Callstate tv targs tk tm)
  | match_returnstate:
    forall v k m tv tk tm f cs cenv Hm wp
      (ACCE: injp_acce w (injpw f m tm Hm))
      (ACCI: injp_acci wp (injpw f m tm Hm))
      (MCS: match_callstack f m tm cs (Mem.support m) (Mem.support tm))
      (MK: match_cont k tk cenv nil cs)
      (RESINJ: Val.inject f v tv),
      match_states wp (Csharpminor.Returnstate v k m)
                   (Returnstate tv tk tm).

Lemma match_call_cont:
  forall k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  match_cont (Csharpminor.call_cont k) (call_cont tk) cenv nil cs.
Proof.
  induction 1; simpl; auto; econstructor; eauto.
Qed.

Lemma match_is_call_cont:
  forall tfn te sp tm k tk cenv xenv cs,
  match_cont k tk cenv xenv cs ->
  Csharpminor.is_call_cont k ->
  exists tk',
    star step tge (State tfn Sskip tk sp te tm)
               E0 (State tfn Sskip tk' sp te tm)
    /\ is_call_cont tk'
    /\ match_cont k tk' cenv nil cs.
Proof.
  induction 1; simpl; intros; try contradiction.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
  exploit IHmatch_cont; eauto.
  intros [tk' [A B]]. exists tk'; split.
  eapply star_left; eauto. constructor. traceEq. auto.
  econstructor; split. apply star_refl. split. exact I. econstructor; eauto.
Qed.

(** Properties of [switch] compilation *)

Inductive lbl_stmt_tail: lbl_stmt -> nat -> lbl_stmt -> Prop :=
  | lstail_O: forall sl,
      lbl_stmt_tail sl O sl
  | lstail_S: forall c s sl n sl',
      lbl_stmt_tail sl n sl' ->
      lbl_stmt_tail (LScons c s sl) (S n) sl'.

Lemma switch_table_default:
  forall sl base,
  exists n,
     lbl_stmt_tail sl n (select_switch_default sl)
  /\ snd (switch_table sl base) = (n + base)%nat.
Proof.
  induction sl; simpl; intros.
- exists O; split. constructor. lia.
- destruct o.
  + destruct (IHsl (S base)) as (n & P & Q). exists (S n); split.
    constructor; auto.
    destruct (switch_table sl (S base)) as [tbl dfl]; simpl in *. lia.
  + exists O; split. constructor.
    destruct (switch_table sl (S base)) as [tbl dfl]; simpl in *. auto.
Qed.

Lemma switch_table_case:
  forall i sl base dfl,
  match select_switch_case i sl with
  | None =>
      switch_target i dfl (fst (switch_table sl base)) = dfl
  | Some sl' =>
      exists n,
         lbl_stmt_tail sl n sl'
      /\ switch_target i dfl (fst (switch_table sl base)) = (n + base)%nat
  end.
Proof.
  induction sl; simpl; intros.
- auto.
- destruct (switch_table sl (S base)) as [tbl1 dfl1] eqn:ST.
  destruct o; simpl.
  rewrite dec_eq_sym. destruct (zeq i z).
  exists O; split; auto. constructor.
  specialize (IHsl (S base) dfl). rewrite ST in IHsl. simpl in *.
  destruct (select_switch_case i sl).
  destruct IHsl as (x & P & Q). exists (S x); split. constructor; auto. lia.
  auto.
  specialize (IHsl (S base) dfl). rewrite ST in IHsl. simpl in *.
  destruct (select_switch_case i sl).
  destruct IHsl as (x & P & Q). exists (S x); split. constructor; auto. lia.
  auto.
Qed.

Lemma switch_table_select:
  forall i sl,
  lbl_stmt_tail sl
                (switch_target i (snd (switch_table sl O)) (fst (switch_table sl O)))
                (select_switch i sl).
Proof.
  unfold select_switch; intros.
  generalize (switch_table_case i sl O (snd (switch_table sl O))).
  destruct (select_switch_case i sl) as [sl'|].
  intros (n & P & Q). replace (n + O)%nat with n in Q by lia. congruence.
  intros E; rewrite E.
  destruct (switch_table_default sl O) as (n & P & Q).
  replace (n + O)%nat with n in Q by lia. congruence.
Qed.

Inductive transl_lblstmt_cont(cenv: compilenv) (xenv: exit_env): lbl_stmt -> cont -> cont -> Prop :=
  | tlsc_default: forall k,
      transl_lblstmt_cont cenv xenv LSnil k (Kblock (Kseq Sskip k))
  | tlsc_case: forall i s ls k ts k',
      transl_stmt cenv (switch_env (LScons i s ls) xenv) s = OK ts ->
      transl_lblstmt_cont cenv xenv ls k k' ->
      transl_lblstmt_cont cenv xenv (LScons i s ls) k (Kblock (Kseq ts k')).

Lemma switch_descent:
  forall cenv xenv k ls body s,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK s ->
  exists k',
  transl_lblstmt_cont cenv xenv ls k k'
  /\ (forall f sp e m,
      plus step tge (State f s k sp e m) E0 (State f body k' sp e m)).
Proof.
  induction ls; intros.
- monadInv H. econstructor; split.
  econstructor.
  intros. eapply plus_two. constructor. constructor. auto.
- monadInv H. exploit IHls; eauto. intros [k' [A B]].
  econstructor; split.
  econstructor; eauto.
  intros. eapply plus_star_trans. eauto.
  eapply star_left. constructor. apply star_one. constructor.
  reflexivity. traceEq.
Qed.

Lemma switch_ascent:
  forall f sp e m cenv xenv ls n ls',
  lbl_stmt_tail ls n ls' ->
  forall k k1,
  transl_lblstmt_cont cenv xenv ls k k1 ->
  exists k2,
  star step tge (State f (Sexit n) k1 sp e m)
             E0 (State f (Sexit O) k2 sp e m)
  /\ transl_lblstmt_cont cenv xenv ls' k k2.
Proof.
  induction 1; intros.
- exists k1; split; auto. apply star_refl.
- inv H0. exploit IHlbl_stmt_tail; eauto. intros (k2 & P & Q).
  exists k2; split; auto.
  eapply star_left. constructor. eapply star_left. constructor. eexact P.
  eauto. auto.
Qed.

Lemma switch_match_cont:
  forall cenv xenv k cs tk ls tk',
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk' ->
  match_cont (Csharpminor.Kseq (seq_of_lbl_stmt ls) k) tk' cenv (false :: switch_env ls xenv) cs.
Proof.
  induction ls; intros; simpl.
  inv H0. apply match_Kblock2. econstructor; eauto.
  inv H0. apply match_Kblock2. eapply match_Kseq2. auto. eauto.
Qed.

Lemma switch_match_states:
  forall fn k e le m tfn ts tk sp sps te tm cenv xenv f bes es cs sz ls body tk' Hm wp
    (SPS: sp = fresh_block sps)
    (TRF: transl_funbody cenv sz fn = OK tfn)
    (TR: transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts)
    (ACCE: injp_acce w (injpw f m tm Hm))
    (ACCI: injp_acci wp (injpw f m tm Hm))
    (MCS: match_callstack f m tm
               (Frame cenv tfn e le te sp sps bes es :: cs)
               (Mem.support m) (Mem.support tm))
    
    (MK: match_cont k tk cenv xenv cs)
    (TK: transl_lblstmt_cont cenv xenv ls tk tk'),
  exists S,
  plus step tge (State tfn (Sexit O) tk' (Vptr sp Ptrofs.zero) te tm) E0 S
  /\ match_states wp (Csharpminor.State fn (seq_of_lbl_stmt ls) k e le m) S.
Proof.
  intros. inv TK.
- econstructor; split. eapply plus_two. constructor. constructor. auto.
  eapply match_state; eauto.
- econstructor; split. eapply plus_left. constructor. apply star_one. constructor. auto.
  simpl. eapply match_state_seq; eauto. simpl. eapply switch_match_cont; eauto.
Qed.

Lemma transl_lblstmt_suffix:
  forall cenv xenv ls n ls',
  lbl_stmt_tail ls n ls' ->
  forall body ts, transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  exists body', exists ts', transl_lblstmt cenv (switch_env ls' xenv) ls' body' = OK ts'.
Proof.
  induction 1; intros.
- exists body, ts; auto.
- monadInv H0. eauto.
Qed.

(** Commutation between [find_label] and compilation *)

Section FIND_LABEL.

Variable lbl: label.
Variable cenv: compilenv.
Variable cs: callstack.

Lemma transl_lblstmt_find_label_context:
  forall xenv ls body ts tk1 tk2 ts' tk',
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  transl_lblstmt_cont cenv xenv ls tk1 tk2 ->
  find_label lbl body tk2 = Some (ts', tk') ->
  find_label lbl ts tk1 = Some (ts', tk').
Proof.
  induction ls; intros.
- monadInv H. inv H0. simpl. rewrite H1. auto.
- monadInv H. inv H0. simpl in H6. eapply IHls; eauto.
  replace x with ts0 by congruence. simpl. rewrite H1. auto.
Qed.

Lemma transl_find_label:
  forall s k xenv ts tk,
  transl_stmt cenv xenv s = OK ts ->
  match_cont k tk cenv xenv cs ->
  match Csharpminor.find_label lbl s k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end

with transl_lblstmt_find_label:
  forall ls xenv body k ts tk tk1,
  transl_lblstmt cenv (switch_env ls xenv) ls body = OK ts ->
  match_cont k tk cenv xenv cs ->
  transl_lblstmt_cont cenv xenv ls tk tk1 ->
  find_label lbl body tk1 = None ->
  match Csharpminor.find_label_ls lbl ls k with
  | None => find_label lbl ts tk = None
  | Some(s', k') =>
      exists ts', exists tk', exists xenv',
        find_label lbl ts tk = Some(ts', tk')
     /\ transl_stmt cenv xenv' s' = OK ts'
     /\ match_cont k' tk' cenv xenv' cs
  end.
Proof.
  intros. destruct s; try (monadInv H); simpl; auto.
  (* seq *)
  exploit (transl_find_label s1). eauto. eapply match_Kseq. eexact EQ1. eauto.
  destruct (Csharpminor.find_label lbl s1 (Csharpminor.Kseq s2 k)) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto.
  (* ifthenelse *)
  exploit (transl_find_label s1). eauto. eauto.
  destruct (Csharpminor.find_label lbl s1 k) as [[s' k'] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'. intuition. rewrite A; auto.
  intro. rewrite H. apply transl_find_label with xenv; auto.
  (* loop *)
  apply transl_find_label with xenv. auto. econstructor; eauto. simpl. rewrite EQ; auto.
  (* block *)
  apply transl_find_label with (true :: xenv). auto. constructor; auto.
  (* switch *)
  simpl in H. destruct (switch_table l O) as [tbl dfl]. monadInv H.
  exploit switch_descent; eauto. intros [k' [A B]].
  eapply transl_lblstmt_find_label. eauto. eauto. eauto. reflexivity.
  (* return *)
  destruct o; monadInv H; auto.
  (* label *)
  destruct (ident_eq lbl l).
  exists x; exists tk; exists xenv; auto.
  apply transl_find_label with xenv; auto.

  intros. destruct ls; monadInv H; simpl.
  (* nil *)
  inv H1. rewrite H2. auto.
  (* cons *)
  inv H1. simpl in H7.
  exploit (transl_find_label s). eauto. eapply switch_match_cont; eauto.
  destruct (Csharpminor.find_label lbl s (Csharpminor.Kseq (seq_of_lbl_stmt ls) k)) as [[s' k''] | ].
  intros [ts' [tk' [xenv' [A [B C]]]]].
  exists ts'; exists tk'; exists xenv'; intuition.
  eapply transl_lblstmt_find_label_context; eauto.
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
  intro. eapply transl_lblstmt_find_label. eauto. auto. eauto.
  simpl. replace x with ts0 by congruence. rewrite H2. auto.
Qed.

End FIND_LABEL.

Lemma transl_find_label_body:
  forall cenv xenv size f tf k tk cs lbl s' k',
  transl_funbody cenv size f = OK tf ->
  match_cont k tk cenv xenv cs ->
  Csharpminor.find_label lbl f.(Csharpminor.fn_body) (Csharpminor.call_cont k) = Some (s', k') ->
  exists ts', exists tk', exists xenv',
     find_label lbl tf.(fn_body) (call_cont tk) = Some(ts', tk')
  /\ transl_stmt cenv xenv' s' = OK ts'
  /\ match_cont k' tk' cenv xenv' cs.
Proof.
  intros. monadInv H. simpl.
  exploit transl_find_label. eexact EQ. eapply match_call_cont. eexact H0.
  instantiate (1 := lbl). rewrite H1. auto.
Qed.

(** The simulation diagram. *)

Fixpoint seq_left_depth (s: Csharpminor.stmt) : nat :=
  match s with
  | Csharpminor.Sseq s1 s2 => S (seq_left_depth s1)
  | _ => O
  end.

Definition measure (S: Csharpminor.state) : nat :=
  match S with
  | Csharpminor.State fn s k e le m => seq_left_depth s
  | _ => O
  end.


Lemma injp_acc_small_free : forall j m tm Hm m' tm' Hm' cenv sz tfn es bes cs sps e le te f,
      Mem.free_list m (blocks_of_env e) = Some m' ->
      Mem.free tm (fresh_block sps) 0 (fn_stackspace tfn) = Some tm' ->
       match_callstack j m tm (Frame cenv tfn e le te (fresh_block sps) sps bes es :: cs) 
         (Mem.support m) (Mem.support tm) ->
       transl_funbody cenv sz f = OK tfn ->
       injp_acc_small w (injpw j m tm Hm) (injpw j m' tm' Hm').
Proof.
  intros. remember w. destruct w0.
  econstructor; eauto; try (red; intros; congruence).
  - red. intros. unfold Mem.valid_block in *. exfalso.
    apply H3. erewrite <- free_list_support; eauto.
  - red. intros. unfold Mem.valid_block in *. exfalso. 
    apply H3. erewrite <- Mem.support_free; eauto.
  - eapply Mem.ro_unchanged_free_list; eauto.
  - eapply Mem.ro_unchanged_free; eauto.
  - eapply free_list_max_perm; eauto.
  - red. intros. eauto with mem.
  - split.
    erewrite <- support_freelist; eauto.
    eapply Mem.unchanged_on_implies.
    instantiate (1:= fun b _ => j b = None /\  (fst b <> Mem.tid (Mem.support m) \/ Mem.valid_block m1 b) ).
    eapply free_list_unchanged_on; eauto.
    intros. intros [X Y]. clear X. inv H1.
    apply list_in_map_inv in H3.
    destruct H3 as [[id [b' ty]] [A B]].
    simpl in A. inv A.
    apply PTree.elements_complete in B.
    inv MENV. inv Hm. inv mi_thread. inv Hms.
    exploit me_local0; eauto. intros [L1 L2]. destruct Y. apply H4.
    inv MCS. congruence. congruence. unfold init_m in L2. rewrite <- Heqw0 in L2.
    congruence.
    eauto.
  - split. erewrite <- Mem.support_free; eauto.
    eapply Mem.free_unchanged_on; eauto.
    intros. intros [X Y]. inv H1. clear X.
    destruct Y. apply H1. inv MCS. inv Hm. inv mi_thread. inv Hms.
    rewrite H6. rewrite <- TTID0. reflexivity.
    inv Hm. inv mi_thread. inv Hms. rewrite H5. rewrite <- TTID0. reflexivity.
    eapply match_callstack_inj_incr in MCS. rewrite <- Heqw0 in MCS. inv MCS.
    eapply freshness. apply H14. eauto.
  - red. intros. inv H1. red in PERM. inv MENV.
    exploit free_list_in; eauto.
    intros (z1 & z2 & A & B).
    apply in_blocks_of_env_inv in A. destruct A as [id [A C]]. subst z1.
    specialize (me_vars0 id).
    rewrite A in me_vars0. inv me_vars0. inv H7. rewrite H3 in H11.
    inv H11. rewrite Ptrofs.add_zero_l in H13.
    eapply Mem.perm_free_2; eauto.
Qed.

Lemma alloc_variables_properties_rec: forall vars e m e' m',
    alloc_variables e m vars e' m' ->
    (forall b, ~ Mem.valid_block m b -> Mem.valid_block m' b -> fst b = Mem.tid (Mem.support m)) /\
      Mem.ro_unchanged m m' /\
      (Mem.unchanged_on_tl (fun _ _ => True) m m').
Proof.
  induction vars; intros.
  - inv H. split. intros. congruence. split. red. eauto. eauto with mem.
  - inv H.
    exploit IHvars; eauto. intros [X [Y Z]]. apply Mem.support_alloc in H4 as HSUP.
    split.
    intros. 
    destruct (Mem.sup_dec b (Mem.support m1)).
    eapply Mem.valid_block_alloc_inv in s; eauto. destruct s; try congruence.
    subst. apply Mem.alloc_result in H4.
    subst. reflexivity.
    exploit X; eauto. intro. rewrite HSUP in H1. simpl in H1. congruence.
    split. eapply Mem.ro_unchanged_trans. eapply Mem.ro_unchanged_alloc; eauto. eauto.
    rewrite HSUP. eauto. red. intros. eauto with mem.
    destruct Z.
    split. eapply Mem.match_sup_trans. 2: eauto. rewrite HSUP.
    constructor; eauto. simpl. rewrite Mem.update_list_length. reflexivity.
    eapply Mem.unchanged_on_trans; eauto. eapply Mem.alloc_unchanged_on; eauto.
Qed.

Lemma alloc_variables_properties: forall e m vars e' m',
    alloc_variables e m vars e' m' ->
    (forall b, ~ Mem.valid_block m b -> Mem.valid_block m' b -> fst b = Mem.tid (Mem.support m)) /\
      Mem.ro_unchanged m m' /\
      (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p <-> Mem.perm m' b ofs k p) /\
      (Mem.unchanged_on_tl (fun _ _ => True) m m').
Proof.
  intros. exploit alloc_variables_properties_rec; eauto.
  intros [A [B C]]. repeat apply conj; eauto.
  intros. destruct C as [_ [X Y]]. eapply Y; eauto.
Qed.

Lemma transl_step_correct:
  forall S1 t S2, Csharpminor.step ge S1 t S2 ->
  forall T1 Wp, match_states Wp S1 T1 ->
  (exists T2, plus step tge T1 t T2 /\ match_states Wp S2 T2)
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states Wp S2 T1)%nat.
Proof.
  induction 1; intros T1 Wp MSTATE; inv MSTATE.

(* skip seq *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  econstructor; split.
  apply plus_one. constructor.
  eapply match_state_seq; eauto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  auto.
(* skip block *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  auto.
(* skip call *)
  monadInv TR. left.
  exploit match_is_call_cont; eauto. intros [tk' [A [B C]]].
  exploit match_callstack_freelist; eauto. intros [tm' [P [Q R]]].
  exploit injp_acc_small_free; eauto. intro ACCS.
  econstructor; split.
  eapply plus_right. eexact A. apply step_skip_call. auto. eauto. traceEq.
  econstructor; eauto. instantiate (1:= R).
  eapply injp_acce_small; eauto.
  etransitivity. eauto. eapply injp_acc_small_acci; eauto.

(* set *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.
  eapply match_callstack_set_temp; eauto.

(* store *)
  monadInv TR.
  exploit transl_expr_correct. eauto. eauto. eexact H. eauto.
  intros [tv1 [EVAL1 VINJ1]].
  exploit transl_expr_correct. eauto. eauto. eexact H0. eauto.
  intros [tv2 [EVAL2 VINJ2]].
  exploit Mem.storev_mapped_inject; eauto. intros [tm' [STORE' MINJ']].
  exploit injp_acc_tl_storev. apply H1. apply STORE'. eauto. eauto.
  intro ACCS.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto.
  instantiate (1:= MINJ').
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto. 
  inv VINJ1; simpl in H1; try discriminate. unfold Mem.storev in STORE'.
  rewrite (Mem.support_store _ _ _ _ _ _ H1).
  rewrite (Mem.support_store _ _ _ _ _ _ STORE').
  eapply match_callstack_invariant with f0 m tm; try (red; intros; congruence); eauto.
  intros. eapply Mem.perm_store_2; eauto.
  intros. eapply Mem.perm_store_1; eauto.
  inv ACCS. destruct H13 as [[A ?] ?]. auto.
  inv ACCS. destruct H14 as [[A ?] ?]. auto.
  
(* call *)
  exploit match_callstack_match_globalenvs; eauto. intros MG.
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tvf [EVAL1 VINJ1]].
  exploit functions_translated; eauto. intros [tfd [FIND TRANS]].
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  left; econstructor; split.
  apply plus_one. eapply step_call; eauto.
  apply sig_preserved; eauto.
  econstructor; eauto.
  eapply match_Kcall with (cenv' := cenv); eauto.
  red; auto.

(* builtin *)
  monadInv TR.
  exploit transl_exprlist_correct; eauto.
  intros [tvargs [EVAL2 VINJ2]].
  exploit match_callstack_match_globalenvs; eauto. intros MG.
  exploit external_call_mem_inject; eauto.
  intros [f' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR [SEPARATED [X [Y [Z1 Z2]]]]]]]]]]]]].
  assert (ACCS: injp_acc_tl (injpw f0 m tm Hm) (injpw f' m' tm' MINJ')).
  econstructor; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  assert (MCS': match_callstack f' m' tm'
                 (Frame cenv tfn e le te (fresh_block sps) sps bes es :: cs)
                 (Mem.support m') (Mem.support tm')).
  apply match_callstack_incr_bound with (Mem.support m) (Mem.support tm).
  eapply match_callstack_external_call; eauto.
  inv ACCS. eapply unchanged_on_tl_e; eauto.
  inv ACCS. eapply unchanged_on_tl_e; eauto.
  eapply inject_incr_local_noglobal; eauto.
  inversion MINJ'. inv mi_thread. auto.
  intros. eapply external_call_max_perm; eauto.
  eapply external_call_support; eauto.
  eapply external_call_support; eauto.
  inv ACCS. destruct H11 as [[A ?] ?]. auto.
  inv ACCS. destruct H12 as [[A ?] ?]. auto.
  econstructor; eauto.
  instantiate (1:= MINJ'). etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
  Opaque PTree.set.
  unfold set_optvar. destruct optid; simpl.
  eapply match_callstack_set_temp; eauto.
  auto.

(* seq *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  econstructor; eauto.
(* seq 2 *)
  right. split. auto. split. auto. econstructor; eauto. auto.

(* ifthenelse *)
  monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  left; exists (State tfn (if b then x0 else x1) tk (Vptr (fresh_block sps) Ptrofs.zero) te tm); split.
  apply plus_one. eapply step_ifthenelse; eauto. eapply bool_of_val_inject; eauto.
  econstructor; eauto. destruct b; auto.

(* loop *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  econstructor; eauto. simpl. rewrite EQ; auto.

(* block *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.
  econstructor; eauto.

(* exit seq *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto. simpl. auto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. eapply plus_left. constructor. apply plus_star; eauto. traceEq.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. eapply plus_left.
  simpl. constructor. apply plus_star; eauto. traceEq.

(* exit block 0 *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  simpl. apply plus_one. constructor.
  econstructor; eauto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. simpl.
  eapply plus_left. constructor. apply plus_star; eauto. traceEq.

(* exit block n+1 *)
  monadInv TR. left.
  dependent induction MK.
  econstructor; split.
  simpl. apply plus_one. constructor.
  econstructor; eauto. auto.
  exploit IHMK; eauto. intros [T2 [A B]].
  exists T2; split; auto. simpl.
  eapply plus_left. constructor. apply plus_star; eauto. traceEq.

(* switch *)
  simpl in TR. destruct (switch_table cases O) as [tbl dfl] eqn:STBL. monadInv TR.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  assert (SA: switch_argument islong tv n).
  { inv H0; inv VINJ; constructor. }
  exploit switch_descent; eauto. intros [k1 [A B]].
  exploit switch_ascent; eauto. eapply (switch_table_select n).
  rewrite STBL; simpl. intros [k2 [C D]].
  exploit transl_lblstmt_suffix; eauto. eapply (switch_table_select n).
  simpl. intros [body' [ts' E]].
  exploit switch_match_states; eauto. intros [T2 [F G]].
  left; exists T2; split.
  eapply plus_star_trans. eapply B.
  eapply star_left. econstructor; eauto.
  eapply star_trans. eexact C.
  apply plus_star. eexact F.
  reflexivity. reflexivity. traceEq.
  auto.

(* return none *)
  monadInv TR. left.
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  exploit injp_acc_small_free; eauto. intro ACCS.
  econstructor; split.
  apply plus_one. eapply step_return_0. eauto.
  econstructor; eauto. instantiate (1:=C).
  eapply injp_acce_small; eauto.
  etransitivity. eauto. eapply injp_acc_small_acci; eauto.
  eapply match_call_cont; eauto.
  simpl; auto.

(* return some *)
  monadInv TR. left.
  exploit transl_expr_correct; eauto. intros [tv [EVAL VINJ]].
  exploit match_callstack_freelist; eauto. intros [tm' [A [B C]]].
  exploit injp_acc_small_free; eauto. intro ACCS.
  econstructor; split.
  apply plus_one. eapply step_return_1. eauto. eauto.
  econstructor; eauto. instantiate (1:=C).
  eapply injp_acce_small; eauto.
  etransitivity. eauto. eapply injp_acc_small_acci; eauto.
  eapply match_call_cont; eauto.

(* label *)
  monadInv TR.
  left; econstructor; split.
  apply plus_one. constructor.
  econstructor; eauto.

(* goto *)
  monadInv TR.
  exploit transl_find_label_body; eauto.
  intros [ts' [tk' [xenv' [A [B C]]]]].
  left; econstructor; split.
  apply plus_one. apply step_goto. eexact A.
  econstructor; eauto.

(* internal call *)
  exploit match_callstack_match_globalenvs; eauto. intros MG.
  exploit functions_translated; eauto. intros [tfd [TFIND TR]].
  monadInv TR. generalize EQ; clear EQ; unfold transl_function.
  caseEq (build_compilenv f). intros ce sz BC.
  destruct (zle sz Ptrofs.max_unsigned); try congruence.
  intro TRBODY.
  generalize TRBODY; intro TMP. monadInv TMP.
  set (tf := mkfunction (Csharpminor.fn_sig f)
                        (Csharpminor.fn_params f)
                        (Csharpminor.fn_temps f)
                        sz
                        x0) in *.
  caseEq (Mem.alloc tm 0 (fn_stackspace tf)). intros tm' sp ALLOC'.
  exploit match_callstack_function_entry; eauto. simpl; eauto. simpl; auto.
  intros [f2 [MCS2 [MINJ2 [INCR [SEP NOG]]]]].
  assert (ACCS: injp_acc_tl (injpw f0 m tm Hm) (injpw f2 m1 tm' MINJ2)).
  { exploit alloc_variables_properties; eauto. intros (A1 & A2 & A3 & A4).
    econstructor; eauto.
    - red. intros.
      edestruct Mem.valid_block_alloc_inv in H5; eauto. subst.
      apply Mem.alloc_result in ALLOC'. subst. reflexivity. congruence.
    - eapply Mem.ro_unchanged_alloc; eauto.
    - red. intros. eapply A3; eauto.
    - red. intros. eauto with mem.
    - destruct A4. split. auto. eapply Mem.unchanged_on_implies; eauto. intros. reflexivity.
    - split. apply Mem.support_alloc in ALLOC'. rewrite ALLOC'.
      constructor; auto. simpl. rewrite Mem.update_list_length. reflexivity.
      eapply Mem.alloc_unchanged_on; eauto.
    - red. intros. exfalso. apply H7. eapply A3; eauto with mem.
  }
  left; econstructor; split.
  apply plus_one. constructor; simpl; eauto.
  econstructor. eapply Mem.alloc_result. eauto.
  eexact TRBODY. eauto. instantiate (1:= MINJ2).
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
  eexact MCS2.
  inv MK; simpl in ISCC; contradiction || econstructor; eauto.

(* external call *)
  exploit match_callstack_match_globalenvs; eauto. intros MG.
  exploit functions_translated; eauto. intros [tfd [TFIND TR]].
  monadInv TR.
  exploit external_call_mem_inject; eauto.
  intros [f' [vres' [tm' [EC [VINJ [MINJ' [UNMAPPED [OUTOFREACH [INCR [SEPARATED [X[Y [Z1 Z2]]]]]]]]]]]]].
  assert (ACCS: injp_acc_tl (injpw f m tm Hm) (injpw f' m' tm' MINJ')).
  econstructor; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  econstructor; eauto. instantiate (1:= MINJ').
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
  apply match_callstack_incr_bound with (Mem.support m) (Mem.support tm).
  eapply match_callstack_external_call; eauto.
  inv ACCS. eapply unchanged_on_tl_e; eauto.
  inv ACCS. eapply unchanged_on_tl_e; eauto.
  eapply inject_incr_local_noglobal; eauto.
  inversion MINJ'. inv mi_thread. auto.
  intros. eapply external_call_max_perm; eauto.
  eapply external_call_support; eauto.
  eapply external_call_support; eauto.
  inv ACCS. destruct H10 as [[A ?] ?]. auto.
  inv ACCS. destruct H11 as [[A ?] ?]. auto.

(* return *)
  inv MK. simpl.
  left; econstructor; split.
  apply plus_one. econstructor; eauto.
  unfold set_optvar. destruct optid; simpl; econstructor; eauto.
  eapply match_callstack_set_temp; eauto.
Qed.

Lemma transl_initial_states:
  forall q1 q2 S, GS.match_query (c_injp) w q1 q2 -> Csharpminor.initial_state ge q1 S ->
  exists R, Cminor.initial_state tge q2 R /\ match_states w S R.
Proof.
  intros q1 q2 S Hq HS.
  inversion Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm Hvf1]. clear Hq. subst.
  inversion HS. clear HS. subst m vargs vf.  destruct w eqn: Hw.
  simpl in *. inv Hm. clear Hm2 Hm3 Hm4.
  exploit functions_translated; eauto. inv GE. auto. intros [tf [FIND TR]].
  setoid_rewrite <- (sig_preserved _ _ TR). monadInv TR. cbn.
  econstructor; split.
  econstructor; eauto.
  eapply match_callstate with (f := f0) (cs := @nil frame) (cenv := PTree.empty Z); auto.
  - rewrite <- Hw. reflexivity.
  - reflexivity.
  - apply mcs_nil. auto. auto. inversion Hm0. inv mi_thread. auto.
    unfold local_t. rewrite Hw. reflexivity.
    unfold local_t. rewrite Hw. simpl. inversion Hm0. inv mi_thread. inv Hms.
    congruence.
    rewrite Hw. econstructor; eauto; try (red; intros; congruence).
  - constructor.
  - red; auto.
Qed.

Lemma transl_final_states:
  forall gw S R r1, match_states gw S R -> Csharpminor.final_state S r1 ->
  exists r2 gw', Cminor.final_state R r2 /\ w o-> gw' /\ gw *-> gw' /\ GS.match_reply (c_injp) gw' r1 r2.
Proof.
  intros. inv H0. inv H. inv MK. inv MCS.
  eexists. exists (injpw f m tm Hm). intuition auto.
  repeat apply conj; eauto.
  econstructor; eauto. econstructor; eauto.
  constructor.
Qed.

Lemma transl_external_states:
  forall gw  S R q1, match_states gw S R -> Csharpminor.at_external ge S q1 ->
  exists wx q2, Cminor.at_external tge R q2 /\ gw *-> wx /\ GS.match_query (c_injp) wx q1 q2 /\ GS.match_senv (c_injp) wx se tse /\
  forall r1 r2 S' gw'', wx o-> gw'' -> GS.match_reply (c_injp) gw'' r1 r2 -> Csharpminor.after_external S r1 S' ->
  exists R', Cminor.after_external R r2 R' /\ match_states gw'' S' R'.
Proof.
  intros gw S R q1 HSR Hq1.
  destruct Hq1; inv HSR.
  assert (vf <> Vundef) by (intro; subst; discriminate).
  eapply functions_translated in H as (tfd & TFIND & TRFD);
    eauto using match_callstack_match_globalenvs.
  monadInv TRFD.
  eexists (injpw f m tm Hm), _. intuition idtac.
  - econstructor; eauto.
  - econstructor; eauto. constructor.
  - constructor; eauto using match_callstack_match_globalenvs.
    + inv GE. eapply Mem.sup_include_trans; eauto.
      rewrite <- H3 in ACCE. inv ACCE. destruct H14 as [_ H14]. inversion H14. auto.
    + inv GE. eapply Mem.sup_include_trans; eauto.
      rewrite <- H3 in ACCE. inv ACCE. destruct H15 as [_ H15]. inversion H15. auto.
  - inv H1. inv H4. inv H2. inv H. clear Hm4 Hm5 Hm6.
    simpl in *. eexists. split. clear Hm1.
    + econstructor; eauto.
    + econstructor; eauto. etransitivity; eauto. instantiate (1:= Hm1).
      econstructor; eauto.
      reflexivity.
      apply match_callstack_incr_bound with (Mem.support m) (Mem.support tm).
      eapply match_callstack_external_call; eauto.
      inversion Hm1. inv mi_thread. auto.
      apply H12. apply H13.
      destruct H12 as [[X ?]]. auto. destruct H13 as [[X ?]]. auto.
Qed.

End TRANSLATION.

Theorem transl_program_correct prog tprog:
  match_prog prog tprog ->
  GS.forward_simulation (c_injp) (Csharpminor.semantics prog) (Cminor.semantics tprog).
Proof.
  intros. red. constructor. econstructor.
  - fsim_skel H.
  - intros. eapply GS.forward_simulation_star; eauto.
    + intros q1 q2 Hq. destruct Hq. cbn in *. inv H0. cbn in *.
    eapply Genv.is_internal_transf_partial; eauto.
    intros [|] ? Hf; monadInv Hf; cbn; auto.
    + apply transl_initial_states; eauto.
    + apply transl_final_states; eauto.
    + apply transl_external_states; eauto.
    + apply transl_step_correct; eauto.
  - auto using well_founded_ltof.
Qed.
