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

(** Recognition of tail calls: correctness proof *)

Require Import Coqlib Maps Integers AST Linking.
Require Import Values Memory Events Globalenvs LanguageInterface Smallstep.
Require Import Op Registers RTL Conventions Tailcall.
Require Import cklr.Extends CallconvBig Ext.

(** * Syntactic properties of the code transformation *)

(** ** Measuring the number of instructions eliminated *)

(** The [return_measure c pc] function counts the number of instructions
  eliminated by the code transformation, where [pc] is the successor
  of a call turned into a tailcall.  This is the length of the
  move/nop/return sequence recognized by the [is_return] boolean function.
*)

Fixpoint return_measure_rec (n: nat) (c: code) (pc: node)
                            {struct n}: nat :=
  match n with
  | O => O
  | S n' =>
      match c!pc with
      | Some(Inop s) => S(return_measure_rec n' c s)
      | Some(Iop op args dst s) => S(return_measure_rec n' c s)
      | _ => O
      end
  end.

Definition return_measure (c: code) (pc: node) :=
  return_measure_rec niter c pc.

Lemma return_measure_bounds:
  forall f pc, (return_measure f pc <= niter)%nat.
Proof.
  intro f.
  assert (forall n pc, (return_measure_rec n f pc <= n)%nat).
    induction n; intros; simpl.
    lia.
    destruct (f!pc); try lia.
    destruct i; try lia.
    generalize (IHn n0). lia.
    generalize (IHn n0). lia.
  intros. unfold return_measure. apply H.
Qed.

Remark return_measure_rec_incr:
  forall f n1 n2 pc,
  (n1 <= n2)%nat ->
  (return_measure_rec n1 f pc <= return_measure_rec n2 f pc)%nat.
Proof.
  induction n1; intros; simpl.
  lia.
  destruct n2. extlia. assert (n1 <= n2)%nat by lia.
  simpl. destruct f!pc; try lia. destruct i; try lia.
  generalize (IHn1 n2 n H0). lia.
  generalize (IHn1 n2 n H0). lia.
Qed.

Lemma is_return_measure_rec:
  forall f n n' pc r,
  is_return n f pc r = true -> (n <= n')%nat ->
  return_measure_rec n f.(fn_code) pc = return_measure_rec n' f.(fn_code) pc.
Proof.
  induction n; simpl; intros.
  congruence.
  destruct n'. extlia. simpl.
  destruct (fn_code f)!pc; try congruence.
  destruct i; try congruence.
  decEq. apply IHn with r. auto. lia.
  destruct (is_move_operation o l); try congruence.
  destruct (Reg.eq r r1); try congruence.
  decEq. apply IHn with r0. auto. lia.
Qed.

(** ** Relational characterization of the code transformation *)

(** The [is_return_spec] characterizes the instruction sequences
  recognized by the [is_return] boolean function.  *)

Inductive is_return_spec (f:function): node -> reg -> Prop :=
  | is_return_none: forall pc r,
      f.(fn_code)!pc = Some(Ireturn None) ->
      is_return_spec f pc r
  | is_return_some: forall pc r,
      f.(fn_code)!pc = Some(Ireturn (Some r)) ->
      is_return_spec f pc r
  | is_return_nop: forall pc r s,
      f.(fn_code)!pc = Some(Inop s) ->
      is_return_spec f s r ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
      is_return_spec f pc r
  | is_return_move: forall pc r r' s,
      f.(fn_code)!pc = Some(Iop Omove (r::nil) r' s) ->
      is_return_spec f s r' ->
      (return_measure f.(fn_code) s < return_measure f.(fn_code) pc)%nat ->
     is_return_spec f pc r.

Lemma is_return_charact:
  forall f n pc rret,
  is_return n f pc rret = true -> (n <= niter)%nat ->
  is_return_spec f pc rret.
Proof.
  induction n; intros.
  simpl in H. congruence.
  generalize H. simpl.
  caseEq ((fn_code f)!pc); try congruence.
  intro i. caseEq i; try congruence.
  intros s; intros. eapply is_return_nop; eauto. eapply IHn; eauto. lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc rret); auto.
  rewrite <- (is_return_measure_rec f n niter s rret); auto.
  simpl. rewrite H2. lia. lia.

  intros op args dst s EQ1 EQ2.
  caseEq (is_move_operation op args); try congruence.
  intros src IMO. destruct (Reg.eq rret src); try congruence.
  subst rret. intro.
  exploit is_move_operation_correct; eauto. intros [A B]. subst.
  eapply is_return_move; eauto. eapply IHn; eauto. lia.
  unfold return_measure.
  rewrite <- (is_return_measure_rec f (S n) niter pc src); auto.
  rewrite <- (is_return_measure_rec f n niter s dst); auto.
  simpl. rewrite EQ2. lia. lia.

  intros or EQ1 EQ2. destruct or; intros.
  assert (r = rret). eapply proj_sumbool_true; eauto. subst r.
  apply is_return_some; auto.
  apply is_return_none; auto.
Qed.

(** The [transf_instr_spec] predicate relates one instruction in the
  initial code with its possible transformations in the optimized code. *)

Inductive transf_instr_spec (f: function): instruction -> instruction -> Prop :=
  | transf_instr_tailcall: forall sig ros args res s,
      f.(fn_stacksize) = 0 ->
      is_return_spec f s res ->
      transf_instr_spec f (Icall sig ros args res s) (Itailcall sig ros args)
  | transf_instr_default: forall i,
      transf_instr_spec f i i.

Lemma transf_instr_charact:
  forall f pc instr,
  f.(fn_stacksize) = 0 ->
  transf_instr_spec f instr (transf_instr f pc instr).
Proof.
  intros. unfold transf_instr. destruct instr; try constructor.
  destruct (is_return niter f n r && tailcall_is_possible s &&
            rettype_eq (sig_res s) (sig_res (fn_sig f))) eqn:B.
- InvBooleans. eapply transf_instr_tailcall; eauto. eapply is_return_charact; eauto.
- constructor.
Qed.

Lemma transf_instr_lookup:
  forall f pc i,
  f.(fn_code)!pc = Some i ->
  exists i',  (transf_function f).(fn_code)!pc = Some i' /\ transf_instr_spec f i i'.
Proof.
  intros. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0 && option_eq zeq (cc_vararg (sig_cc (fn_sig f))) None) eqn:B.
  InvBooleans.
  simpl. rewrite PTree.gmap. rewrite H. simpl.
  exists (transf_instr f pc i); split. auto. apply transf_instr_charact; auto.
  exists i; split. auto. constructor.
Qed.

(** * Semantic properties of the code transformation *)

(** ** The ``less defined than'' relation between register states *)

(** A call followed by a return without an argument can be turned
  into a tail call.  In this case, the original function returns
  [Vundef], while the transformed function can return any value.
  We account for this situation by using the ``less defined than''
  relation between values and between memory states.  We need to
  extend it pointwise to register states. *)

Lemma regs_lessdef_init_regs:
  forall params vl vl',
  Val.lessdef_list vl vl' ->
  regs_lessdef (init_regs vl params) (init_regs vl' params).
Proof.
  induction params; intros.
  simpl. red; intros. rewrite Regmap.gi. constructor.
  simpl. inv H.   red; intros. rewrite Regmap.gi. constructor.
  apply set_reg_lessdef. auto. auto.
Qed.

(** * Proof of semantic preservation *)

Definition match_prog (p tp: RTL.program) :=
  match_program (fun cu f tf => tf = transf_fundef f) eq p tp.

Lemma transf_program_match:
  forall p, match_prog p (transf_program p).
Proof.
  intros. apply match_transform_program; auto.
Qed.

Section PRESERVATION.

Variable prog tprog: program.
Hypothesis TRANSL: match_prog prog tprog.

Variable w : ext_world.
Variable se: Genv.symtbl.
Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv se tprog.

Definition local_tid := match w with extw m tm Hm =>
                                       Mem.tid (Mem.support m) end.
                                     
Lemma functions_translated:
  forall (v tv: val) (f: RTL.fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v tv ->
  Genv.find_funct tge tv = Some (transf_fundef f).
Proof.
  intros v tv f Hf Hv. apply (Genv.find_funct_transf_id TRANSL).
  unfold Genv.find_funct in *. destruct v; try discriminate. inv Hv. auto.
Qed.

Lemma sig_preserved:
  forall f, funsig (transf_fundef f) = funsig f.
Proof.
  destruct f; auto. simpl. unfold transf_function.
  destruct (zeq (fn_stacksize f) 0 && option_eq zeq (cc_vararg (sig_cc (fn_sig f))) None); auto.
Qed.

Lemma stacksize_preserved:
  forall f, fn_stacksize (transf_function f) = fn_stacksize f.
Proof.
  unfold transf_function. intros.
  destruct (zeq (fn_stacksize f) 0 && option_eq zeq (cc_vararg (sig_cc (fn_sig f))) None); auto.
Qed.

Lemma ros_address_translated:
  forall ros rs rs',
  regs_lessdef rs rs' ->
  Val.lessdef (ros_address ge ros rs) (ros_address tge ros rs').
Proof.
  intros. unfold ros_address, Genv.find_funct. destruct ros; auto.
Qed.

(** Consider an execution of a call/move/nop/return sequence in the
  original code and the corresponding tailcall in the transformed code.
  The transition sequences are of the following form
  (left: original code, right: transformed code).
  [f] is the calling function and [fd] the called function.
<<
     State stk f (Icall instruction)       State stk' f' (Itailcall)

     Callstate (frame::stk) fd args        Callstate stk' fd' args'
            .                                       .
            .                                       .
            .                                       .
     Returnstate (frame::stk) res          Returnstate stk' res'

     State stk f (move/nop/return seq)
            .
            .
            .
     State stk f (return instr)

     Returnstate stk res
>>
The simulation invariant must therefore account for two kinds of
mismatches between the transition sequences:
- The call stack of the original program can contain more frames
  than that of the transformed program (e.g. [frame] in the example above).
- The regular states corresponding to executing the move/nop/return
  sequence must all correspond to the single [Returnstate stk' res']
  state of the transformed program.

We first define the simulation invariant between call stacks.
The first two cases are standard, but the third case corresponds
to a frame that was eliminated by the transformation. *)

Inductive match_stackframes: list stackframe -> list stackframe -> Prop :=
  | match_stackframes_nil:
      match_stackframes nil nil
  | match_stackframes_normal: forall stk stk' res sp pc rs rs' f,
      match_stackframes stk stk' ->
      regs_lessdef rs rs' ->
      fst sp = local_tid ->
      match_stackframes
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        (Stackframe res (transf_function f) (Vptr sp Ptrofs.zero) pc rs' :: stk')
  | match_stackframes_tail: forall stk stk' res sp pc rs f,
      match_stackframes stk stk' ->
      is_return_spec f pc res ->
      f.(fn_stacksize) = 0 ->
      fst sp = local_tid ->
      match_stackframes
        (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
        stk'.

(** Here is the invariant relating two states.  The first three
  cases are standard.  Note the ``less defined than'' conditions
  over values and register states, and the corresponding ``extends''
  relation over memory states. *)

Inductive match_states: ext_world -> state -> state -> Prop :=
  | match_states_normal:
      forall s sp pc rs m s' rs' m' f wp Hm
        (STACKS: match_stackframes s s')
        (SP: fst sp = local_tid)
        (RLD: regs_lessdef rs rs')
        (ACI: ext_acci wp (extw m m' Hm))
        (ACE: ext_acce w (extw m m' Hm)),
      match_states wp (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (State s' (transf_function f) (Vptr sp Ptrofs.zero) pc rs' m')
  | match_states_call:
      forall s vf args m s' vf' args' m' wp Hm,
      match_stackframes s s' ->
      Val.lessdef vf vf' ->
      Val.lessdef_list args args' ->
      ext_acci wp (extw m m' Hm) ->
      ext_acce w (extw m m' Hm) ->
      match_states wp (Callstate s vf args m)
                   (Callstate s' vf' args' m')
  | match_states_return:
      forall s v m s' v' m' wp Hm,
      match_stackframes s s' ->
      Val.lessdef v v' ->
      ext_acci wp (extw m m' Hm) ->
      ext_acce w (extw m m' Hm) ->
      match_states wp (Returnstate s v m)
                   (Returnstate s' v' m')
  | match_states_interm:
      forall s sp pc rs m s' m' f r v' wp Hm
        (STACKS: match_stackframes s s')
        (SP: fst sp = local_tid)
        (ACI: ext_acci wp (extw m m' Hm))
        (ACE: ext_acce w (extw m m' Hm)),
      is_return_spec f pc r ->
      f.(fn_stacksize) = 0 ->
      Val.lessdef (rs#r) v' ->
      match_states wp (State s f (Vptr sp Ptrofs.zero) pc rs m)
                   (Returnstate s' v' m').

Lemma ext_acce_local_tid : forall m tm Hm,
    ext_acce w (extw m tm Hm) ->
    Mem.tid (Mem.support m) = local_tid.
Proof.
  intros. unfold local_tid. inv H. eauto.
Qed.

(** The last case of [match_states] corresponds to the execution
  of a move/nop/return sequence in the original code that was
  eliminated by the transformation:
<<
     State stk f (move/nop/return seq)  ~~  Returnstate stk' res'
            .
            .
            .
     State stk f (return instr)         ~~  Returnstate stk' res'
>>
  To preserve non-terminating behaviors, we need to make sure
  that the execution of this sequence in the original code cannot
  diverge.  For this, we introduce the following complicated
  measure over states, which will decrease strictly whenever
  the original code makes a transition but the transformed code
  does not. *)

Definition measure (st: state) : nat :=
  match st with
  | State s f sp pc rs m => (List.length s * (niter + 2) + return_measure f.(fn_code) pc + 1)%nat
  | Callstate s f args m => 0%nat
  | Returnstate s v m => (List.length s * (niter + 2))%nat
  end.

Ltac TransfInstr :=
  match goal with
  | H: (PTree.get _ (fn_code _) = _) |- _ =>
      destruct (transf_instr_lookup _ _ _ H) as [i' [TINSTR TSPEC]]; inv TSPEC
  end.

Ltac EliminatedInstr :=
  match goal with
  | H: (is_return_spec _ _ _) |- _ => inv H; try congruence
  | _ => idtac
  end.

(** The proof of semantic preservation, then, is a simulation diagram
  of the ``option'' kind. *)

Lemma transf_step_correct:
  forall s1 t s2, step ge s1 t s2 ->
  forall wp s1' (MS: match_states wp s1 s1'),
  (exists s2', step tge s1' t s2' /\ match_states wp s2 s2')
  \/ (measure s2 < measure s1 /\ t = E0 /\ match_states wp s2 s1')%nat.
Proof.
  induction 1; intros; inv MS; EliminatedInstr.

- (* nop *)
  TransfInstr. left. econstructor; split.
  eapply exec_Inop; eauto. econstructor; eauto.
- (* eliminated nop *)
  assert (s0 = pc') by congruence. subst s0.
  right. split. simpl. lia. split. auto.
  econstructor; eauto.

- (* op *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_operation_lessdef; eauto.
  intros [v' [EVAL' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#res <- v') m'); split.
  eapply exec_Iop; eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.
- (* eliminated move *)
  rewrite H1 in H. clear H1. inv H.
  right. split. simpl. lia. split. auto.
  econstructor; eauto. simpl in H0. rewrite PMap.gss. congruence.

- (* load *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.loadv_extends; eauto.
  intros [v' [LOAD' VLD]].
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (rs'#dst <- v') m'); split.
  eapply exec_Iload with (a := a'); eauto.
  econstructor; eauto. apply set_reg_lessdef; auto.

- (* store *)
  TransfInstr.
  assert (Val.lessdef_list (rs##args) (rs'##args)). apply regs_lessdef_regs; auto.
  exploit eval_addressing_lessdef; eauto.
  intros [a' [ADDR' ALD]].
  exploit Mem.storev_extends. 2: eexact H1. eauto. eauto. apply RLD.
  intros [m'1 [STORE' MLD']].
  exploit ext_acci_storev. apply H1. eauto. eauto. intro ACCI.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'1); split.
  eapply exec_Istore with (a := a'); eauto.
  econstructor; eauto. etransitivity. eauto. instantiate (1:= MLD'). eauto.
  etransitivity; eauto.

- (* call *)
  exploit (ros_address_translated ros); eauto. intros FEXT.
  exploit functions_translated; eauto using ros_address_translated. intro FIND'.
  TransfInstr.
+ (* call turned tailcall *)
  assert ({ m'' | Mem.free m' sp0 0 (fn_stacksize (transf_function f)) = Some m''}).
    apply Mem.range_perm_free. rewrite stacksize_preserved. rewrite H7.
    red; intros; extlia.
  destruct X as [m'' FREE].
  left. eexists (Callstate s' _ (rs'##args) m''); split.
  eapply exec_Itailcall; eauto. apply sig_preserved.
  exploit Mem.free_right_extends; eauto.
  rewrite stacksize_preserved. rewrite H7. intros. extlia. intro Hm'.
  assert (ACCI: ext_acci (extw m m' Hm) (extw m m'' Hm')).
  constructor; eauto; try (red; intros; congruence);
    try (erewrite <- Mem.support_free; eauto).
  red. intros. eauto with mem.
  econstructor; eauto. eapply match_stackframes_tail; eauto. apply regs_lessdef_regs; auto.
  etransitivity; eauto.  etransitivity; eauto.

  
+ (* call that remains a call *)
  left. exists (Callstate (Stackframe res (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' :: s')
                          (ros_address tge ros rs') (rs'##args) m'); split.
  eapply exec_Icall; eauto. apply sig_preserved.
  econstructor. constructor; auto.
  apply ros_address_translated; auto. apply regs_lessdef_regs; auto. eauto. eauto.

- (* tailcall *)
  exploit (ros_address_translated ros); eauto. intros FEXT.
  exploit functions_translated; eauto using ros_address_translated. intro FIND'.
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  exploit ext_acci_free. apply H2. eauto. intro ACCI.
  TransfInstr.
  left. eexists (Callstate s' _ (rs'##args) m'1); split.
  eapply exec_Itailcall; eauto. apply sig_preserved.
  rewrite stacksize_preserved; auto.
  econstructor; auto.  apply regs_lessdef_regs; auto. instantiate (1:= EXT).
  etransitivity; eauto.   etransitivity; eauto. 

- (* builtin *)
  TransfInstr.
  exploit (@eval_builtin_args_lessdef _ se (fun r => rs#r) (fun r => rs'#r)); eauto.
  intros (vargs' & P & Q).
  exploit external_call_mem_extends; eauto.
  intros [v' [m'1 [A [B [C [D E]]]]]].
  assert (ACCI: ext_acci (extw m m'0 Hm) (extw m' m'1 C)).
  econstructor; eauto using external_call_tid, external_call_support.
  red. intros. eauto using external_call_max_perm.
  red. intros. eauto using external_call_max_perm.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' (regmap_setres res v' rs') m'1); split.
  eapply exec_Ibuiltin; eauto.
  econstructor; eauto. apply set_res_lessdef; auto.
  etransitivity; eauto. etransitivity; eauto.

- (* cond *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) (if b then ifso else ifnot) rs' m'); split.
  eapply exec_Icond; eauto.
  apply eval_condition_lessdef with (rs##args) m; auto. apply regs_lessdef_regs; auto.
  econstructor; eauto.

- (* jumptable *)
  TransfInstr.
  left. exists (State s' (transf_function f) (Vptr sp0 Ptrofs.zero) pc' rs' m'); split.
  eapply exec_Ijumptable; eauto.
  generalize (RLD arg). rewrite H0. intro. inv H2. auto.
  econstructor; eauto.

- (* return *)
  exploit Mem.free_parallel_extends; eauto. intros [m'1 [FREE EXT]].
  TransfInstr.
  left. exists (Returnstate s' (regmap_optget or Vundef rs') m'1); split.
  apply exec_Ireturn; auto. rewrite stacksize_preserved; auto.
  exploit  ext_acci_free. apply H0. eauto. intro ACCI.
  econstructor. eauto.
  destruct or; simpl. apply RLD. constructor.
  etransitivity. eauto. instantiate (1:= EXT). eauto.
  etransitivity; eauto.

- (* eliminated return None *)
  assert (or = None) by congruence. subst or.
  right. split. simpl. lia. split. auto.
  exploit Mem.free_left_extends; eauto. intro Hm'.
  assert (ACCI: ext_acci (extw m m'0 Hm) (extw m' m'0 Hm')).
  constructor; eauto; try (red; intros; congruence);
    try (erewrite <- Mem.support_free; eauto).
  red. intros. eauto with mem.
  red. intros. elim H2. eapply Mem.perm_free_inv in H3; eauto.
  destruct H3; try congruence. destruct H3. subst b.
  erewrite ext_acce_local_tid; eauto.
  econstructor. eauto.
  simpl. constructor. instantiate (1:= Hm').
  etransitivity; eauto.  etransitivity; eauto.
  
- (* eliminated return Some *)
  assert (or = Some r) by congruence. subst or.
  right. split. simpl. lia. split. auto.
  exploit Mem.free_left_extends; eauto. intro Hm'.
  assert (ACCI: ext_acci (extw m m'0 Hm) (extw m' m'0 Hm')).
  constructor; eauto; try (red; intros; congruence);
    try (erewrite <- Mem.support_free; eauto).
  red. intros. eauto with mem.
  red. intros. elim H2. eapply Mem.perm_free_inv in H3; eauto.
  destruct H3; try congruence. destruct H3. subst b.
  erewrite ext_acce_local_tid; eauto.
  econstructor. eauto. simpl. auto.
  etransitivity; eauto.  etransitivity; eauto.

- (* internal call *)
  exploit functions_translated; eauto. intro FIND'.
  exploit Mem.alloc_extends; eauto.
    instantiate (1 := 0). lia.
    instantiate (1 := fn_stacksize f). lia.
  intros [m'1 [ALLOC EXT]].
  assert (fn_stacksize (transf_function f) = fn_stacksize f /\
          fn_entrypoint (transf_function f) = fn_entrypoint f /\
          fn_params (transf_function f) = fn_params f).
    unfold transf_function. destruct (zeq (fn_stacksize f) 0 && option_eq zeq (cc_vararg (sig_cc (fn_sig f))) None); auto.
  destruct H0 as [EQ1 [EQ2 EQ3]].
  exploit ext_acci_alloc. apply H. eauto. intro ACCI.
  left. econstructor; split.
  eapply exec_function_internal; eauto. rewrite EQ1; eauto.
  rewrite EQ2. rewrite EQ3. econstructor; eauto.
  apply Mem.alloc_result in H. rewrite H.
  eapply ext_acce_local_tid. eauto.
  apply regs_lessdef_init_regs. auto. instantiate (1:= EXT).
  etransitivity; eauto.  etransitivity; eauto.

- (* external call *)
  exploit functions_translated; eauto. intro FIND'.
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [A [B [C [D E]]]]]].
  assert (ACCI: ext_acci (extw m m'0 Hm) (extw m' m2' C)).
  econstructor; eauto using external_call_tid, external_call_support.
  red. intros. eauto using external_call_max_perm.
  red. intros. eauto using external_call_max_perm.
  left. exists (Returnstate s' res' m2'); split.
  simpl. econstructor; eauto.
  econstructor; eauto. etransitivity; eauto.
  etransitivity; eauto.

- (* returnstate *)
  inv H2.
+ (* synchronous return in both programs *)
  left. econstructor; split.
  apply exec_return.
  econstructor; eauto. apply set_reg_lessdef; auto.
+ (* return instr in source program, eliminated because of tailcall *)
  right. split. unfold measure. simpl length.
  change (S (length s) * (niter + 2))%nat
   with ((niter + 2) + (length s) * (niter + 2))%nat.
  generalize (return_measure_bounds (fn_code f) pc). lia.
  split. auto.
  econstructor; eauto.
  rewrite Regmap.gss. auto.
Qed.

Lemma transf_initial_states:
  forall q1 q2 st1, GS.match_query (c_ext) w q1 q2 -> initial_state ge q1 st1 ->
  exists st2, initial_state tge q2 st2 /\ match_states (get w) st1 st2.
Proof.
  intros. destruct H. inv H0. CKLR.uncklr.
  destruct H as [vf | ]; try discriminate.
  exploit functions_translated; eauto. intro FIND.
  destruct w eqn: Hw. inv H2.
  exists (Callstate nil vf vargs2 m2); split.
  setoid_rewrite <- (sig_preserved (Internal f)). econstructor; eauto.
  econstructor; eauto. constructor. simpl. reflexivity.
  rewrite Hw. reflexivity.
Qed.

Lemma transf_final_states:
  forall wp st1 st2 r1, match_states wp st1 st2 -> final_state st1 r1 ->
                   exists r2 wp', final_state st2 r2 /\ (get w) o-> wp' /\ ext_acci wp wp' /\
                                                               GS.match_reply (c_ext) (CallconvBig.set w wp') r1 r2.
Proof.
  intros. inv H0. inv H. inv H3.
  eexists. exists (extw m m' Hm). split.
  - constructor.
  - split. auto. split. auto. constructor; CKLR.uncklr; cbn; auto. constructor.
Qed.

Lemma transf_external_states:
  forall wp st1 st2 q1, match_states wp st1 st2 -> at_external ge st1 q1 ->
  exists wx q2, at_external tge st2 q2 /\ ext_acci wp (get wx) /\  GS.match_query (c_ext) wx q1 q2 /\ se = se /\
  forall r1 r2 st1' wp'', (get wx) o-> wp'' -> GS.match_reply (c_ext) (CallconvBig.set w wp'') r1 r2 -> after_external st1 r1 st1' ->
  exists st2', after_external st2 r2 st2' /\ match_states wp'' st1' st2'.
Proof.
  intros wp st1 st2 q1 Hst Hq1. destruct Hq1. inv Hst.
  exploit functions_translated; eauto. intro FIND'.
  exists (extw m m' Hm). eexists. intuition idtac.
  - econstructor; eauto.
  - destruct H6; try discriminate.
    constructor; CKLR.uncklr; auto. constructor.
    destruct v; cbn in *; congruence.
  - inv H1. inv H0. inv H5. CKLR.uncklr.
    exists (Returnstate s' vres2 m2'). split. econstructor; eauto.
    inv H2. econstructor; eauto. reflexivity. etransitivity. eauto. constructor; eauto.
Qed.

End PRESERVATION.

(** The preservation of the observable behavior of the program then
  follows. *)

Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  GS.forward_simulation (c_ext) (RTL.semantics prog) (RTL.semantics tprog).
Proof.
  intros MATCH. constructor.
  eapply GS.Forward_simulation.
  + try fsim_skel MATCH.
  + intros se1 se2 w Hse Hse1. eapply GS.forward_simulation_opt with (measure := measure); destruct Hse.
  - destruct 1. CKLR.uncklr. destruct H; try congruence.
    eapply (Genv.is_internal_transf_id MATCH). intros [|]; auto.
  - eapply transf_initial_states; eauto.
  - eapply transf_final_states; eauto.
  - eapply transf_external_states; eauto.
  - intros. exploit transf_step_correct; eauto. apply H.
    auto.
  + auto using well_founded_ltof.
Qed.
