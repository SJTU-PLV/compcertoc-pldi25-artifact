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

(** RTL function inlining: semantic preservation *)

Require Import Coqlib Wfsimpl Maps Errors Integers.
Require Import AST Linking Values Memory Globalenvs Events Smallstep.
Require Import CallconvBig.
Require Import Injp.

Require Import Op Registers RTL.
Require Import Inlining Inliningspec.
Require Import LanguageInterface cklr.Inject cklr.InjectFootprint.

Definition match_prog (prog tprog: program) :=
  match_program (fun cunit f tf => transf_fundef (funenv_program cunit) f = OK tf) eq prog tprog.

Lemma transf_program_match:
  forall prog tprog, transf_program prog = OK tprog -> match_prog prog tprog.
Proof.
  intros. eapply match_transform_partial_program_contextual; eauto.
Qed.

Section INLINING.

Variable prog: program.
Variable tprog: program.
Hypothesis TRANSF: match_prog prog tprog.
Variable w: CKLR.world injp.
Variable se: Genv.symtbl.
Variable tse: Genv.symtbl.
Let ge := Genv.globalenv se prog.
Let tge := Genv.globalenv tse tprog.

Hypothesis GE: CKLR.match_stbls injp w se tse.
Hypothesis VALID: Genv.valid_for (erase_program prog) se.

Lemma functions_translated (j: meminj):
  Genv.match_stbls j se tse ->
  forall (v tv: val) (f: fundef),
  Genv.find_funct ge v = Some f -> Val.inject j v tv ->
  exists cu f', Genv.find_funct tge tv = Some f' /\ transf_fundef (funenv_program cu) f = OK f' /\ linkorder cu prog.
Proof.
  apply (Genv.find_funct_match TRANSF).
Qed.

Lemma sig_function_translated:
  forall cu f f', transf_fundef (funenv_program cu) f = OK f' -> funsig f' = funsig f.
Proof.
  intros. destruct f; Errors.monadInv H.
  exploit transf_function_spec; eauto. intros SP; inv SP. auto.
  auto.
Qed.

(** ** Properties of contexts and relocations *)

Remark sreg_below_diff:
  forall ctx r r', Plt r' ctx.(dreg) -> sreg ctx r <> r'.
Proof.
  intros. zify. unfold sreg; rewrite shiftpos_eq. extlia.
Qed.

Remark context_below_diff:
  forall ctx1 ctx2 r1 r2,
  context_below ctx1 ctx2 -> Ple r1 ctx1.(mreg) -> sreg ctx1 r1 <> sreg ctx2 r2.
Proof.
  intros. red in H. zify. unfold sreg; rewrite ! shiftpos_eq. extlia.
Qed.

Remark context_below_lt:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Plt (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Plt; zify. unfold sreg; rewrite shiftpos_eq.
  extlia.
Qed.

(*
Remark context_below_le:
  forall ctx1 ctx2 r, context_below ctx1 ctx2 -> Ple r ctx1.(mreg) -> Ple (sreg ctx1 r) ctx2.(dreg).
Proof.
  intros. red in H. unfold Ple; zify. unfold sreg; rewrite shiftpos_eq.
  extlia.
Qed.
*)

(** ** Agreement between register sets before and after inlining. *)

Definition agree_regs (F: meminj) (ctx: context) (rs rs': regset) :=
  (forall r, Ple r ctx.(mreg) -> Val.inject F rs#r rs'#(sreg ctx r))
/\(forall r, Plt ctx.(mreg) r -> rs#r = Vundef).

Definition val_reg_charact (F: meminj) (ctx: context) (rs': regset) (v: val) (r: reg) :=
  (Plt ctx.(mreg) r /\ v = Vundef) \/ (Ple r ctx.(mreg) /\ Val.inject F v rs'#(sreg ctx r)).

Remark Plt_Ple_dec:
  forall p q, {Plt p q} + {Ple q p}.
Proof.
  intros. destruct (plt p q). left; auto. right; extlia.
Qed.

Lemma agree_val_reg_gen:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> val_reg_charact F ctx rs' rs#r r.
Proof.
  intros. destruct H as [A B].
  destruct (Plt_Ple_dec (mreg ctx) r).
  left. rewrite B; auto.
  right. auto.
Qed.

Lemma agree_val_regs_gen:
  forall F ctx rs rs' rl,
  agree_regs F ctx rs rs' -> list_forall2 (val_reg_charact F ctx rs') rs##rl rl.
Proof.
  induction rl; intros; constructor; auto. apply agree_val_reg_gen; auto.
Qed.

Lemma agree_val_reg:
  forall F ctx rs rs' r, agree_regs F ctx rs rs' -> Val.inject F rs#r rs'#(sreg ctx r).
Proof.
  intros. exploit agree_val_reg_gen; eauto. instantiate (1 := r). intros [[A B] | [A B]].
  rewrite B; auto.
  auto.
Qed.

Lemma agree_val_regs:
  forall F ctx rs rs' rl, agree_regs F ctx rs rs' -> Val.inject_list F rs##rl rs'##(sregs ctx rl).
Proof.
  induction rl; intros; simpl. constructor. constructor; auto. apply agree_val_reg; auto.
Qed.

Lemma agree_set_reg:
  forall F ctx rs rs' r v v',
  agree_regs F ctx rs rs' ->
  Val.inject F v v' ->
  Ple r ctx.(mreg) ->
  agree_regs F ctx (rs#r <- v) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gso. auto. extlia.
Qed.

Lemma agree_set_reg_undef:
  forall F ctx rs rs' r v',
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) (rs'#(sreg ctx r) <- v').
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  repeat rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. rewrite peq_true. auto.
  rewrite peq_false. auto. apply shiftpos_diff; auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_set_reg_undef':
  forall F ctx rs rs' r,
  agree_regs F ctx rs rs' ->
  agree_regs F ctx (rs#r <- Vundef) rs'.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite Regmap.gsspec.
  destruct (peq r0 r). subst r0. auto. auto.
  rewrite Regmap.gsspec. destruct (peq r0 r); auto.
Qed.

Lemma agree_regs_invariant:
  forall F ctx rs rs1 rs2,
  agree_regs F ctx rs rs1 ->
  (forall r, Ple ctx.(dreg) r -> Plt r (ctx.(dreg) + ctx.(mreg)) -> rs2#r = rs1#r) ->
  agree_regs F ctx rs rs2.
Proof.
  unfold agree_regs; intros. destruct H. split; intros.
  rewrite H0. auto.
  apply shiftpos_above.
  eapply Pos.lt_le_trans. apply shiftpos_below. extlia.
  apply H1; auto.
Qed.

Lemma agree_regs_incr:
  forall F ctx rs1 rs2 F',
  agree_regs F ctx rs1 rs2 ->
  inject_incr F F' ->
  agree_regs F' ctx rs1 rs2.
Proof.
  intros. destruct H. split; intros. eauto. auto.
Qed.

Remark agree_regs_init:
  forall F ctx rs, agree_regs F ctx (Regmap.init Vundef) rs.
Proof.
  intros; split; intros. rewrite Regmap.gi; auto. rewrite Regmap.gi; auto.
Qed.

Lemma agree_regs_init_regs:
  forall F ctx rl vl vl',
  Val.inject_list F vl vl' ->
  (forall r, In r rl -> Ple r ctx.(mreg)) ->
  agree_regs F ctx (init_regs vl rl) (init_regs vl' (sregs ctx rl)).
Proof.
  induction rl; simpl; intros.
  apply agree_regs_init.
  inv H. apply agree_regs_init.
  apply agree_set_reg; auto.
Qed.

(** ** Executing sequences of moves *)

Lemma tr_moves_init_regs:
  forall F stk f sp m ctx1 ctx2, context_below ctx1 ctx2 ->
  forall rdsts rsrcs vl pc1 pc2 rs1,
  tr_moves f.(fn_code) pc1 (sregs ctx1 rsrcs) (sregs ctx2 rdsts) pc2 ->
  (forall r, In r rdsts -> Ple r ctx2.(mreg)) ->
  list_forall2 (val_reg_charact F ctx1 rs1) vl rsrcs ->
  exists rs2,
    star step tge (State stk f sp pc1 rs1 m)
               E0 (State stk f sp pc2 rs2 m)
  /\ agree_regs F ctx2 (init_regs vl rdsts) rs2
  /\ forall r, Plt r ctx2.(dreg) -> rs2#r = rs1#r.
Proof.
  induction rdsts; simpl; intros.
(* rdsts = nil *)
  inv H0. exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
(* rdsts = a :: rdsts *)
  inv H2. inv H0.
  exists rs1; split. apply star_refl. split. apply agree_regs_init. auto.
  simpl in H0. inv H0.
  exploit IHrdsts; eauto. intros [rs2 [A [B C]]].
  exists (rs2#(sreg ctx2 a) <- (rs2#(sreg ctx1 b1))).
  split. eapply star_right. eauto. eapply exec_Iop; eauto. traceEq.
  split. destruct H3 as [[P Q] | [P Q]].
  subst a1. eapply agree_set_reg_undef; eauto.
  eapply agree_set_reg; eauto. rewrite C; auto.  apply context_below_lt; auto.
  intros. rewrite Regmap.gso. auto. apply not_eq_sym. eapply sreg_below_diff; eauto.
  destruct H2; discriminate.
Qed.

(** ** Memory invariants *)

(** A stack location is private if it is not the image of a valid
   location and we have full rights on it. *)

Definition loc_private (F: meminj) (m m': mem) (sp: block) (ofs: Z) : Prop :=
  Mem.perm m' sp ofs Cur Freeable /\
  (forall b delta, F b = Some(sp, delta) -> ~Mem.perm m b (ofs - delta) Max Nonempty).

(** Likewise, for a range of locations. *)

Definition range_private (F: meminj) (m m': mem) (sp: block) (lo hi: Z) : Prop :=
  forall ofs, lo <= ofs < hi -> loc_private F m m' sp ofs.

Lemma range_private_invariant:
  forall F m m' sp lo hi F1 m1 m1',
  range_private F m m' sp lo hi ->
  (forall b delta ofs,
      F1 b = Some(sp, delta) ->
      Mem.perm m1 b ofs Max Nonempty ->
      lo <= ofs + delta < hi ->
      F b = Some(sp, delta) /\ Mem.perm m b ofs Max Nonempty) ->
  (forall ofs, Mem.perm m' sp ofs Cur Freeable -> Mem.perm m1' sp ofs Cur Freeable) ->
  range_private F1 m1 m1' sp lo hi.
Proof.
  intros; red; intros. exploit H; eauto. intros [A B]. split; auto. 
  intros; red; intros. exploit H0; eauto. lia. intros [P Q].
  eelim B; eauto.
Qed.

Lemma range_private_perms:
  forall F m m' sp lo hi,
  range_private F m m' sp lo hi ->
  Mem.range_perm m' sp lo hi Cur Freeable.
Proof.
  intros; red; intros. eapply H; eauto.
Qed.

Lemma range_private_alloc_left:
  forall F m m' sp' base hi sz m1 sp F1,
  range_private F m m' sp' base hi ->
  Mem.alloc m 0 sz = (m1, sp) ->
  F1 sp = Some(sp', base) ->
  (forall b, b <> sp -> F1 b = F b) ->
  range_private F1 m1 m' sp' (base + Z.max sz 0) hi.
Proof.
  intros; red; intros.
  exploit (H ofs). generalize (Z.le_max_r sz 0). lia. intros [A B].
  split; auto. intros; red; intros.
  exploit Mem.perm_alloc_inv; eauto.
  destruct (eq_block b sp); intros.
  subst b. rewrite H1 in H4; inv H4.
  rewrite Zmax_spec in H3. destruct (zlt 0 sz); lia.
  rewrite H2 in H4; auto. eelim B; eauto.
Qed.

Lemma range_private_free_left:
  forall F m m' sp base sz hi b m1,
  range_private F m m' sp (base + Z.max sz 0) hi ->
  Mem.free m b 0 sz = Some m1 ->
  F b = Some(sp, base) ->
  Mem.inject F m m' ->
  range_private F m1 m' sp base hi.
Proof.
  intros; red; intros.
  destruct (zlt ofs (base + Z.max sz 0)) as [z|z].
  red; split.
  replace ofs with ((ofs - base) + base) by lia.
  eapply Mem.perm_inject; eauto.
  eapply Mem.free_range_perm; eauto.
  rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  intros; red; intros. destruct (eq_block b b0).
  subst b0. rewrite H1 in H4; inv H4.
  eelim Mem.perm_free_2; eauto. rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  exploit Mem.mi_no_overlap; eauto.
  apply Mem.perm_cur_max. apply Mem.perm_implies with Freeable; auto with mem.
  eapply Mem.free_range_perm. eauto.
  instantiate (1 := ofs - base). rewrite Zmax_spec in z. destruct (zlt 0 sz); lia.
  eapply Mem.perm_free_3; eauto.
  intros [A | A]. congruence. lia.

  exploit (H ofs). lia. intros [A B]. split. auto.
  intros; red; intros. eelim B; eauto. eapply Mem.perm_free_3; eauto.
Qed.

Lemma range_private_extcall:
  forall F F' m1 m2 m1' m2' sp base hi,
  range_private F m1 m1' sp base hi ->
  (forall b ofs p,
     Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p) ->
  Mem.unchanged_on_e (loc_out_of_reach F m1) m1' m2' ->
  Mem.inject F m1 m1' ->
  inject_incr F F' ->
  Mem.meminj_thread_local F' ->
  inject_separated_internal F F' m1 m1' ->
  Mem.valid_block m1' sp ->
  fst sp = Mem.tid (Mem.support m1') ->
  range_private F' m2 m2' sp base hi.
Proof.
  intros until hi; intros RP PERM UNCH INJ INCR TL SEP VB.
  red; intros. exploit RP; eauto. intros [A B].
  split. eapply Mem.perm_unchanged_on; eauto. eapply UNCH.
  split. auto. congruence.
  intros. red in SEP. destruct (F b) as [[sp1 delta1] |] eqn:?.
  exploit INCR; eauto. intros EQ; rewrite H1 in EQ; inv EQ.
  red; intros; eelim B; eauto. eapply PERM; eauto.
  red. destruct (Mem.sup_dec b (Mem.support m1)); auto.
  exploit Mem.mi_freeblocks; eauto. congruence.
  exploit SEP; eauto. erewrite TL; eauto. inversion INJ.
  inv mi_thread. inv Hms. congruence. tauto.
Qed.


(** ** Relating global environments *)

Lemma ros_address_agree:
  forall ros rs F ctx rs',
  agree_regs F ctx rs rs' ->
  Genv.match_stbls F se tse ->
  Val.inject F (ros_address ge ros rs) (ros_address tge (sros ctx ros) rs').
Proof.
  intros. destruct ros as [r | id]; simpl in *.
- (* register *)
  destruct H as [Hlo Hhi]. destruct (plt (mreg ctx) r).
  + rewrite Hhi by auto. constructor.
  + eapply Hlo. extlia.
- (* symbol *)
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol se id) eqn:Hb; eauto.
  edestruct @Genv.find_symbol_match as (b' & Hb' & H'); eauto.
  rewrite H'. econstructor; eauto.
Qed.

Lemma ros_address_inlined:
  forall fenv id rs fd f,
  fenv_compat prog fenv ->
  Genv.find_funct ge (ros_address ge (inr id) rs) = Some fd ->
  fenv!id = Some f ->
  fd = Internal f.
Proof.
  intros.
  apply H in H1. eapply Genv.find_def_symbol in H1; eauto. destruct H1 as (b & A & B).
  simpl in H0. unfold Genv.symbol_address, ge, fundef in *. setoid_rewrite A in H0.
  rewrite <- Genv.find_funct_ptr_iff in B. cbn in H0.
  destruct Ptrofs.eq_dec; congruence.
Qed.

(** Translation of builtin arguments. *)

Lemma tr_builtin_arg:
  forall F ctx rs rs' sp sp' m m',
  Genv.match_stbls F se tse ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F m m' ->
  forall a v,
  eval_builtin_arg ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m a v ->
  exists v', eval_builtin_arg tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' (sbuiltinarg ctx a) v'
          /\ Val.inject F v v'.
Proof.
  intros until m'; intros MG AG SP MI. induction 1; simpl.
- exists rs'#(sreg ctx x); split. constructor. eapply agree_val_reg; eauto.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- econstructor; eauto with barg.
- exploit Mem.loadv_inject; eauto.
  instantiate (1 := Vptr sp' (Ptrofs.add ofs (Ptrofs.repr (dstk ctx)))).
  simpl. econstructor; eauto. rewrite Ptrofs.add_zero_l; auto.
  intros (v' & A & B). exists v'; split; auto. constructor. simpl. rewrite Ptrofs.add_zero_l; auto.
- econstructor; split. constructor. simpl. econstructor; eauto. rewrite ! Ptrofs.add_zero_l; auto.
- assert (Val.inject F (Genv.symbol_address ge id ofs) (Genv.symbol_address tge id ofs)).
  { unfold Genv.symbol_address; simpl; unfold Genv.symbol_address.
    destruct (Genv.find_symbol se id) as [b|] eqn:FS; auto.
    edestruct @Genv.find_symbol_match as (tb & Htb & TFS); eauto. rewrite TFS.
    econstructor. eauto. rewrite Ptrofs.add_zero; auto. }
  exploit Mem.loadv_inject; eauto. intros (v' & A & B).
  exists v'; eauto with barg.
- econstructor; split. constructor.
  unfold Genv.symbol_address.
  destruct (Genv.find_symbol se id) as [b|] eqn:FS; auto.
  edestruct @Genv.find_symbol_match as (tb & Htb & TFS); eauto. rewrite TFS.
  econstructor. eauto. rewrite Ptrofs.add_zero; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg. apply Val.longofwords_inject; auto.
- destruct IHeval_builtin_arg1 as (v1' & A1 & B1).
  destruct IHeval_builtin_arg2 as (v2' & A2 & B2).
  econstructor; split. eauto with barg.
  destruct Archi.ptr64; auto using Val.add_inject, Val.addl_inject.
Qed.

Lemma tr_builtin_args:
  forall F ctx rs rs' sp sp' m m',
  Genv.match_stbls F se tse ->
  agree_regs F ctx rs rs' ->
  F sp = Some(sp', ctx.(dstk)) ->
  Mem.inject F m m' ->
  forall al vl,
  eval_builtin_args ge (fun r => rs#r) (Vptr sp Ptrofs.zero) m al vl ->
  exists vl', eval_builtin_args tge (fun r => rs'#r) (Vptr sp' Ptrofs.zero) m' (map (sbuiltinarg ctx) al) vl'
          /\ Val.inject_list F vl vl'.
Proof.
  induction 5; simpl.
- exists (@nil val); split; constructor.
- exploit tr_builtin_arg; eauto. intros (v1' & A & B).
  destruct IHlist_forall2 as (vl' & C & D).
  exists (v1' :: vl'); split; constructor; auto.
Qed.


(** ** Relating stacks *)
Definition injp_inj_world (w: injp_world) : inj_world :=
  match w with
    | injpw f m1 m2 Hm => injw f (Mem.support m1) (Mem.support m2)
  end.


Definition init_j := match w with injpw j _ _ _ => j end.
Definition init_m := match w with injpw _ m _ _ => m end.
Definition init_tm := match w with injpw _ _ tm _ => tm end.
(*
Notation init_sup := (Mem.support init_m).
Notation init_tsup := (Mem.support init_tm).
*)
Inductive inj_incr' : injp_world -> inj_world -> Prop :=
  injp_inj_incr_intro : forall f f' m1 m2 s1' s2' Hm,
      inject_incr f f' ->
      inject_separated_internal f f' m1 m2 ->
      inject_separated_noglobal f f' ->
      Mem.sup_include (Mem.support m1) s1' ->
      Mem.sup_include (Mem.support m2) s2' ->
      inj_incr' (injpw f m1 m2 Hm) (injw f' s1' s2').

Definition local_t : nat := Mem.tid (Mem.support init_m).

Inductive match_stacks (F: meminj) (m m': mem):
             list stackframe -> list stackframe -> sup -> Prop :=
  | match_stacks_nil: forall support
        (MG: inj_incr' w (injw F (Mem.support m) (Mem.support m')))
        (TID1 : Mem.tid (Mem.support m) = local_t)
        (TID2 : Mem.tid (Mem.support m') = local_t)
        (TID3 : Mem.tid support = local_t)                
        (TL: Mem.meminj_thread_local F)                
        (BELOW: Mem.sup_include (Mem.support init_tm) support),
      match_stacks F m m' nil nil support
  | match_stacks_cons: forall res f sp pc rs stk f' sp' sps' rs' stk' support fenv ctx
        (SPS': sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' stk stk' f' ctx sps' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (TID: fst sp = Mem.tid (Mem.support m))
        (NEWB: ~ Mem.valid_block init_m sp /\ ~ Mem.valid_block init_tm sp')
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RES: Ple res ctx.(mreg))
        (BELOW: Mem.sup_include (sup_incr sps') support)
        (THREAD_SPS: Mem.tid sps' = local_t)
        (THREAD_SPS': Mem.tid support = local_t),
      match_stacks F m m'
                   (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                   (Stackframe (sreg ctx res) f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' :: stk')
                   support
  | match_stacks_untailcall: forall stk res f' sps' sp' rpc rs' stk' support ctx
        (SPS': sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' stk stk' f' ctx sps' rs')
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize))
        (RET: ctx.(retinfo) = Some (rpc, res))
        (BELOW: Mem.sup_include (sup_incr sps') support)
        (THREAD_SPS: Mem.tid sps' = local_t)
        (THREAD_SPS': Mem.tid support = local_t),
      match_stacks F m m'
                   stk
                   (Stackframe res f' (Vptr sp' Ptrofs.zero) rpc rs' :: stk')
                   support

with match_stacks_inside (F: meminj) (m m': mem):
        list stackframe -> list stackframe -> function -> context -> sup -> regset -> Prop :=
  | match_stacks_inside_base: forall stk stk' f' ctx sps' rs'
        (MS: match_stacks F m m' stk stk' sps')
        (RET: ctx.(retinfo) = None)
        (DSTK: ctx.(dstk) = 0),
      match_stacks_inside F m m' stk stk' f' ctx sps' rs'
  | match_stacks_inside_inlined: forall res f sp pc rs stk stk' f' fenv ctx sps' sp' rs' ctx'
        (SPS': sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' stk stk' f' ctx' sps' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code))
        (AG: agree_regs F ctx' rs rs')
        (SP: F sp = Some(sp', ctx'.(dstk)))
        (TID: fst sp = Mem.tid (Mem.support m))
        (NEWB: ~ Mem.valid_block init_m sp /\ ~ Mem.valid_block init_tm sp')
        (PAD: range_private F m m' sp' (ctx'.(dstk) + ctx'.(mstk)) ctx.(dstk))
        (RES: Ple res ctx'.(mreg))
        (RET: ctx.(retinfo) = Some (spc ctx' pc, sreg ctx' res))
        (BELOW: context_below ctx' ctx)
        (SBELOW: context_stack_call ctx' ctx),
      match_stacks_inside F m m' (Stackframe res f (Vptr sp Ptrofs.zero) pc rs :: stk)
                                 stk' f' ctx sps' rs'.

(** Properties of match_stacks *)

Section MATCH_STACKS.

Variable F: meminj.
Variables m m': mem.

Lemma match_stacks_globalenvs:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> Genv.match_stbls F se tse
with match_stacks_inside_globalenvs:
  forall stk stk' f ctx sp rs',
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> Genv.match_stbls F se tse.
Proof.
  induction 1; eauto. inv GE. inv MG. rewrite <- H2 in H8. inv H8.
  eapply Genv.match_stbls_incr_noglobal; eauto.
  induction 1; eauto.
Qed.

Lemma match_stacks_tid1:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> Mem.tid (Mem.support m) = local_t
with match_stacks_inside_tid1:
  forall stk stk' f ctx sp rs',
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> Mem.tid (Mem.support m) = local_t.
Proof.
  induction 1; eauto. 
  induction 1; eauto.
Qed.

Lemma match_stacks_tid2:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> Mem.tid (Mem.support m') = local_t
with match_stacks_inside_tid2:
  forall stk stk' f ctx sp rs',
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> Mem.tid (Mem.support m') = local_t.
Proof.
  induction 1; eauto. 
  induction 1; eauto.
Qed.

  
Lemma match_stacks_tid3:
  forall stk stk' bound,
    match_stacks F m m' stk stk' bound -> Mem.tid (bound) = local_t
with match_stacks_inside_tid3:
  forall stk stk' f ctx sp rs',
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> Mem.tid (sp) = local_t.
Proof.
  induction 1; eauto.
  induction 1; eauto.
Qed.

Lemma match_stacks_tl:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound -> Mem.meminj_thread_local F
with match_stacks_inside_tl:
  forall stk stk' f ctx sp rs',
  match_stacks_inside F m m' stk stk' f ctx sp rs' -> Mem.meminj_thread_local F.
Proof.
  induction 1; eauto. 
  induction 1; eauto.
Qed.

Lemma match_stacks_sup_include:
  forall stk stk' support support1,
  match_stacks F m m' stk stk' support ->
  Mem.sup_include support support1 ->
  Mem.tid support = Mem.tid support1 ->
  match_stacks F m m' stk stk' support1.
Proof.
  intros. inv H.
  apply match_stacks_nil; eauto. congruence.
  eapply match_stacks_cons; eauto. congruence.
  eapply match_stacks_untailcall; eauto.
  congruence.
Qed.

Variable F1: meminj.
Variables m1 m1': mem.
Hypothesis INCR: inject_incr F F1.

Lemma mit_incr_invariant bound s1 s2 s1' s2':
  (forall b1 b2 delta, F1 b1 = Some(b2, delta) -> fst b1 = local_t -> sup_In b1 (Mem.support init_m) \/ sup_In b2 bound ->
                  F b1 = Some(b2, delta)) ->
  inject_separated_noglobal F F1 ->
  Mem.sup_include (Mem.support init_tm) bound ->
  inj_incr' w (injw F s1 s2) ->
  Mem.sup_include s1 s1' ->
  Mem.sup_include s2 s2' ->
  inj_incr' w (injw F1 s1' s2').
Proof.
  intros INJ NOG BELOW H Hs1' Hs2'. inv H. split; cbn in *; eauto; try extlia.
  eapply inject_incr_trans; eauto.
  intros b1 b2 delta Hb1 Hb1'.
  destruct (F b1) as [[xb1' xdelta]|] eqn:Hb1''.
  - rewrite (INCR _ _ _ Hb1'') in Hb1'. inv Hb1'. eauto.
  - intro. unfold local_t, init_m, init_tm in *. rewrite <- H5 in *.
    destruct (Mem.sup_dec b1 (Mem.support m0)); try (erewrite INJ in Hb1''; eauto; discriminate).
    destruct (Mem.sup_dec b2 bound); try (erewrite INJ in Hb1''; eauto; discriminate).
    split; eauto.
  - red. intros. destruct (F b1) as [[? ?]|] eqn:Hfb1. apply INCR in Hfb1 as Heq. rewrite H0 in Heq.
    inv Heq. eapply H6; eauto. eapply NOG; eauto.
Qed.

Definition inject_separated_tl (f f': meminj) := forall b1 b2 d,
    f b1 = None -> f' b1 = Some (b2, d) -> fst b1 = fst b2.

Lemma inject_incr_thread_local : forall f f',
    inject_incr f f' ->
    Mem.meminj_thread_local f ->
    inject_separated_tl f f' ->
    Mem.meminj_thread_local f'.
Proof.
  intros. red. intros. red in H0.
  destruct (f b) as [[b'' d'']|] eqn:fb.
  apply H in fb as Heq. rewrite H2 in Heq. inv Heq. eauto.
  exploit H1; eauto.
Qed.

Lemma match_stacks_invariant:
  forall stk stk' support, match_stacks F m m' stk stk' support ->
        forall (INJ: forall b1 b2 delta, F1 b1 = Some(b2, delta) -> 
                               sup_In b1 (Mem.support init_m) \/ sup_In b2 support -> F b1 = Some(b2, delta))
          (NOG: inject_separated_noglobal F F1)
          (TL: inject_separated_tl F F1)
         (NB: Mem.sup_include (Mem.support m) (Mem.support m1))
         (THE_NB: Mem.tid (Mem.support m) = Mem.tid (Mem.support m1))
         (TNB: Mem.sup_include (Mem.support m') (Mem.support m1'))
         (THE_TNB: Mem.tid (Mem.support m') = Mem.tid (Mem.support m1'))
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> sup_In b2 support ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, sup_In b support->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, sup_In b support->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks F1 m1 m1' stk stk' support

with match_stacks_inside_invariant:
  forall stk stk' f' ctx sps' rs1,
  match_stacks_inside F m m' stk stk' f' ctx sps' rs1 ->
  forall rs2 sp'
         (SPS: sp' = fresh_block sps')
         (RS: forall r, Plt r ctx.(dreg) -> rs2#r = rs1#r)
         (NB: Mem.sup_include (Mem.support m) (Mem.support m1))
         (THE_NB: Mem.tid (Mem.support m) = Mem.tid (Mem.support m1))
         (TNB: Mem.sup_include (Mem.support m') (Mem.support m1'))
         (THE_TNB: Mem.tid (Mem.support m') = Mem.tid (Mem.support m1'))
         (INJ: forall b1 b2 delta,
               F1 b1 = Some(b2, delta) -> 
               sup_In b1 (Mem.support init_m) \/ sup_In b2 (sup_incr sps') -> F b1 = Some(b2, delta))
         (NOG: inject_separated_noglobal F F1)
         (TL: inject_separated_tl F F1)
         (PERM1: forall b1 b2 delta ofs,
               F1 b1 = Some(b2, delta) -> sup_In b2 (sup_incr sps') ->
               Mem.perm m1 b1 ofs Max Nonempty -> Mem.perm m b1 ofs Max Nonempty)
         (PERM2: forall b ofs, sup_In b (sup_incr sps') ->
               Mem.perm m' b ofs Cur Freeable -> Mem.perm m1' b ofs Cur Freeable)
         (PERM3: forall b ofs k p, sup_In b (sup_incr sps') ->
               Mem.perm m1' b ofs k p -> Mem.perm m' b ofs k p),
  match_stacks_inside F1 m1 m1' stk stk' f' ctx sps' rs2.
Proof.
  induction 1; intros; subst.
  - (* nil *)
  apply match_stacks_nil; auto.
  eapply mit_incr_invariant; eauto. congruence. congruence.
  eapply inject_incr_thread_local; eauto.
  - (* cons *)
  apply match_stacks_cons with (fenv := fenv) (ctx := ctx) (sps' := sps'); auto.
  eapply match_stacks_inside_invariant; eauto.
  + intros. eapply INJ; eauto. destruct H0; auto. (* destruct H1; auto. *)
  + eapply agree_regs_incr; eauto.
  + congruence.
  + eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto.
    exploit inject_incr_thread_local. eauto. 
    eapply match_stacks_inside_tl; eauto. auto. auto. apply H. intro. simpl in H2.
    eapply PERM1; eauto.
  - (* untailcall *)
  apply match_stacks_untailcall with (ctx := ctx) (sps' := sps'); auto.
  eapply match_stacks_inside_invariant; eauto.
  + intros; eapply INJ; eauto. destruct H0; eauto.
  + eapply range_private_invariant; eauto.
    intros. split. eapply INJ; eauto.
    exploit inject_incr_thread_local. eauto. 
    eapply match_stacks_inside_tl; eauto. auto. auto. apply H. intro. simpl in H2.
    eapply PERM1; eauto.
  - induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.
  +
  intros. eapply INJ; eauto. destruct H0; eauto. right.
  apply Mem.sup_incr_in2. auto.
  + intros; eapply PERM1; eauto. apply Mem.sup_incr_in2. auto.
  + intros; eapply PERM2; eauto. apply Mem.sup_incr_in2. auto.
  + intros; eapply PERM3; eauto. apply Mem.sup_incr_in2. auto.
  (* inlined *)
  + subst sp'0.
  apply match_stacks_inside_inlined with (fenv := fenv) (ctx' := ctx') (sp' := sp'); auto.
  apply IHmatch_stacks_inside with (sp':= fresh_block sps'); auto.
  intros. apply RS. red in BELOW. extlia.
  apply agree_regs_incr with F; auto.
  apply agree_regs_invariant with rs'; auto.
  intros. apply RS. red in BELOW. extlia. congruence.
  eapply range_private_invariant; eauto.
  intros. split. eapply INJ; eauto.
  exploit inject_incr_thread_local. eauto. 
  eapply match_stacks_inside_tl; eauto. auto. auto. apply H0. intro.
  subst sp'. simpl in H3. exploit match_stacks_inside_tid3; eauto.
  subst sp'. auto. eapply PERM1; eauto. subst sp'. auto.
Qed.

Lemma match_stacks_empty:
  forall stk stk' support,
  match_stacks F m m' stk stk' support -> stk = nil -> stk' = nil
with match_stacks_inside_empty:
  forall stk stk' f ctx sp rs,
  match_stacks_inside F m m' stk stk' f ctx sp rs -> stk = nil -> stk' = nil /\ ctx.(retinfo) = None.
Proof.
  induction 1; intros.
  auto.
  discriminate.
  exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
  induction 1; intros.
  split. eapply match_stacks_empty; eauto. auto.
  discriminate.
Qed.

Lemma match_stacks_support:
  forall stk stk' bound,
  match_stacks F m m' stk stk' bound ->
  Mem.sup_include (Mem.support init_m) (Mem.support m) /\
  Mem.sup_include (Mem.support init_tm) (Mem.support m') /\
  Mem.sup_include (Mem.support init_tm) bound
with match_stacks_inside_support:
  forall stk stk' f' ctx sps' rs1,
  match_stacks_inside F m m' stk stk' f' ctx sps' rs1 ->
  Mem.sup_include (Mem.support init_m) (Mem.support m) /\
  Mem.sup_include (Mem.support init_tm) (Mem.support m') /\
  Mem.sup_include (Mem.support init_tm) sps'.
Proof.
  induction 1; eauto.
  clear - MG BELOW. inv MG. unfold init_m, init_tm in *. rewrite <- H4 in *. auto.
  exploit match_stacks_inside_support; eauto. intros (A & B &C).
  intuition auto. red. intros. apply BELOW. eapply Mem.sup_incr_in2. eauto.
  exploit match_stacks_inside_support; eauto. intros (A & B &C).
  intuition auto. red. intros. apply BELOW. eapply Mem.sup_incr_in2. eauto.
  induction 1; eauto.
Qed.

End MATCH_STACKS.

(** Preservation by assignment to a register *)

Lemma match_stacks_inside_set_reg:
  forall F m m' stk stk' f' ctx sp' rs' r v,
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' stk stk' f' ctx sp' (rs'#(sreg ctx r) <- v).
Proof.
  intros. eapply match_stacks_inside_invariant; eauto; try (red; intros; congruence).
  intros. apply Regmap.gso. zify. unfold sreg; rewrite shiftpos_eq. extlia.
Qed.

Lemma match_stacks_inside_set_res:
  forall F m m' stk stk' f' ctx sp' rs' res v,
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  match_stacks_inside F m m' stk stk' f' ctx sp' (regmap_setres (sbuiltinres ctx res) v rs').
Proof.
  intros. destruct res; simpl; auto.
  apply match_stacks_inside_set_reg; auto.
Qed.

(** Preservation by a memory store *)

Lemma match_stacks_inside_store:
  forall F m m' stk stk' f' ctx sp' rs' chunk b ofs v m1 chunk' b' ofs' v' m1',
  match_stacks_inside F m m' stk stk' f' ctx sp' rs' ->
  Mem.store chunk m b ofs v = Some m1 ->
  Mem.store chunk' m' b' ofs' v' = Some m1' ->
  match_stacks_inside F m1 m1' stk stk' f' ctx sp' rs'.
Proof.
  intros.
  eapply match_stacks_inside_invariant; eauto with mem.
  rewrite (Mem.support_store _ _ _ _ _ _ H0). eauto.
  rewrite (Mem.support_store _ _ _ _ _ _ H0). eauto.
  rewrite (Mem.support_store _ _ _ _ _ _ H1). eauto.
  rewrite (Mem.support_store _ _ _ _ _ _ H1). eauto.
  red. intros. congruence.  red. intros. congruence.
Qed.

(** Preservation by an allocation *)

Lemma match_stacks_inside_alloc_left:
  forall F m m' stk stk' f' ctx sps' sp' rs',
  match_stacks_inside F m m' stk stk' f' ctx sps' rs' ->
  sp' = fresh_block sps' ->
  forall sz m1 b F1 delta,
  Mem.alloc m 0 sz = (m1, b) ->
  inject_incr F F1 ->
  F1 b = Some(sp', delta) ->
  (forall b1, b1 <> b -> F1 b1 = F b1) ->
  delta >= ctx.(dstk) ->
  match_stacks_inside F1 m1 m' stk stk' f' ctx sps' rs'.
Proof.
  induction 1; intros.
  (* base *)
  eapply match_stacks_inside_base; eauto.
  eapply match_stacks_invariant; eauto.

  intros. destruct (eq_block b1 b).
  subst b1. rewrite H2 in H5; inv H5.
    exfalso.
    apply Mem.alloc_result in H0. subst.
    apply match_stacks_support in MS. eauto.
    destruct MS.
    destruct H6; eapply freshness; eauto.
    rewrite H3 in H5; auto.
    red. intros. destruct (eq_block b1 b). subst.
    split. eapply Mem.alloc_block_noglobal; eauto. rewrite H2 in H6.
    inv H6. eapply Genv.thread_noglobal; eauto. simpl. reflexivity. erewrite H3 in H6. congruence. eauto.
    red. intros. destruct (eq_block b1 b). subst.
    rewrite H2 in H6. inv H6. apply Mem.alloc_result in H0. rewrite H0. simpl.
    erewrite match_stacks_tid1; eauto. erewrite match_stacks_tid3; eauto.
    erewrite H3 in H6; eauto. congruence.
  rewrite (Mem.support_alloc _ _ _ _ _ H0). eauto. inv H0. reflexivity.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b1 b); intros; auto.
  subst b1. rewrite H2 in H5. inv H5. eelim freshness; eauto.
  (* inlined *)
  subst sp'0. subst sp'.
  eapply match_stacks_inside_inlined; eauto.
  eapply IHmatch_stacks_inside; eauto. destruct SBELOW. lia.
  eapply agree_regs_incr; eauto. erewrite Mem.support_alloc; eauto. simpl. auto.
  eapply range_private_invariant; eauto.
  intros. exploit Mem.perm_alloc_inv; eauto. destruct (eq_block b0 b); intros.
  subst b0. rewrite H3 in H0; inv H0. elimtype False; extlia.
  rewrite H4 in H0; auto.
Qed.

(** Preservation by freeing *)

Lemma match_stacks_free_left:
  forall F m m' stk stk' sp b lo hi m1,
  match_stacks F m m' stk stk' sp ->
  Mem.free m b lo hi = Some m1 ->
  match_stacks F m1 m' stk stk' sp.
Proof.
  intros. eapply match_stacks_invariant; eauto; try (
  red; intros; congruence). 
  rewrite (Mem.support_free _ _ _ _ _ H0). eauto.
  rewrite (Mem.support_free _ _ _ _ _ H0). eauto.
  red. intros. eapply Mem.perm_free_3; eauto.
(*  intros. eapply Mem.perm_free_3; eauto. *)
Qed.

Lemma match_stacks_free_right:
  forall F m m' stk stk' sps sp lo hi m1',
  match_stacks F m m' stk stk' sps ->
  sp = fresh_block sps ->
  Mem.free m' sp lo hi = Some m1' ->
  match_stacks F m m1' stk stk' sps.
Proof.
  intros. eapply match_stacks_invariant; eauto; try (
  red; intros; congruence).
  rewrite (Mem.support_free _ _ _ _ _ H1). eauto.
  rewrite (Mem.support_free _ _ _ _ _ H1). eauto.
(*  red. intros. eapply Mem.perm_free_3; eauto. *)
  intros. eapply Mem.perm_free_1; eauto with ordered_type.
  left.  subst sp. intro. subst b. eapply freshness; eauto.
  intros. eapply Mem.perm_free_3; eauto.
Qed.

Lemma min_alignment_sound:
  forall sz n, (min_alignment sz | n) -> Mem.inj_offset_aligned n sz.
Proof.
  intros; red; intros. unfold min_alignment in H.
  assert (2 <= sz -> (2 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). auto.
    destruct (zle sz 4). apply Z.divide_trans with 4; auto. exists 2; auto.
    apply Z.divide_trans with 8; auto. exists 4; auto.
  assert (4 <= sz -> (4 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). extlia.
    destruct (zle sz 4). auto.
    apply Z.divide_trans with 8; auto. exists 2; auto.
  assert (8 <= sz -> (8 | n)). intros.
    destruct (zle sz 1). extlia.
    destruct (zle sz 2). extlia.
    destruct (zle sz 4). extlia.
    auto.
  destruct chunk; simpl in *; auto.
  apply Z.divide_1_l.
  apply Z.divide_1_l.
  apply H2; lia.
  apply H2; lia.
Qed.

(** Preservation by external calls *)

Section EXTCALL.

Variables F1 F2: meminj.
Variables m1 m2 m1' m2': mem.
Hypothesis MAXPERM: forall b ofs p, Mem.valid_block m1 b -> Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Hypothesis MAXPERM': forall b ofs p, Mem.valid_block m1' b -> Mem.perm m2' b ofs Max p -> Mem.perm m1' b ofs Max p.
Hypothesis UNCHANGED: Mem.unchanged_on_e (loc_out_of_reach F1 m1) m1' m2'.
Hypothesis INJ: Mem.inject F1 m1 m1'.
Hypothesis INCR: inject_incr F1 F2.
Hypothesis SEP: inject_separated_internal F1 F2 m1 m1'.
Hypothesis NOG: inject_separated_noglobal F1 F2.
Hypothesis TL: Mem.meminj_thread_local F2.

Lemma match_stacks_extcall:
  forall stk stk' support,
  match_stacks F1 m1 m1' stk stk' support ->
  Mem.sup_include (Mem.support m1) (Mem.support m2) ->
  Mem.tid (Mem.support m1) = Mem.tid (Mem.support m2) ->
  Mem.sup_include support (Mem.support m1') ->
  Mem.tid support = Mem.tid (Mem.support m1')  -> 
  match_stacks F2 m2 m2' stk stk' support
with match_stacks_inside_extcall:
  forall stk stk' f' ctx sp' sps' rs',
  match_stacks_inside F1 m1 m1' stk stk' f' ctx sps' rs' ->
  sp' = fresh_block sps' ->
  Mem.sup_include (Mem.support m1) (Mem.support m2) ->
  Mem.tid (Mem.support m1) = Mem.tid (Mem.support m2) ->
  Mem.sup_include (sup_incr sps') (Mem.support m1') ->
  Mem.tid sps' = Mem.tid (Mem.support m1') ->
  match_stacks_inside F2 m2 m2' stk stk' f' ctx sps' rs'.
Proof.
  induction 1; intros.
  apply match_stacks_nil; auto.
  eapply mit_incr_invariant; eauto; try congruence.
  + intros.
    destruct (F1 b1) as [[xb2 xdelta]|] eqn:HF1.
   apply INCR in HF1. congruence.
    exploit SEP; eauto. congruence.
    unfold Mem.valid_block. inv MG.
    unfold init_m, init_tm in *. rewrite <- H11 in *. cbn in *. intros [A B].
    exfalso. destruct H5; eauto.
  + eapply Mem.unchanged_on_support. eapply UNCHANGED.
  + congruence.
  + destruct UNCHANGED as [[_ X]_]. congruence.
  +  eapply match_stacks_cons; eauto.
     eapply match_stacks_inside_extcall; eauto. congruence. 
    eapply agree_regs_incr; eauto.  congruence.
    eapply range_private_extcall; eauto. red. apply H1. subst. auto. 
    subst sp'. simpl. congruence. 
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red. apply H1. subst. auto.
  +
    eapply match_stacks_untailcall; eauto.
    eapply match_stacks_inside_extcall; eauto. congruence.
    eapply range_private_extcall; eauto. red. apply H1. subst. auto. subst sp'. simpl. congruence.
    intros. apply SSZ2; auto. apply MAXPERM'; auto. red. apply H1. subst. auto.
  + induction 1; intros.
    eapply match_stacks_inside_base; eauto.
    subst sp'0. subst sp'.
    eapply match_stacks_inside_inlined; eauto.
    eapply agree_regs_incr; eauto. congruence.
    eapply range_private_extcall; eauto.
    apply H3. auto.
Qed.

End EXTCALL.

(** Change of context corresponding to an inlined tailcall *)

Lemma align_unchanged:
  forall n amount, amount > 0 -> (amount | n) -> align n amount = n.
Proof.
  intros. destruct H0 as [p EQ]. subst n. unfold align. decEq.
  apply Zdiv_unique with (b := amount - 1). lia. lia.
Qed.
Lemma match_stacks_inside_inlined_tailcall:
  forall fenv F m m' stk stk' f' ctx sps' sp' rs' ctx' f,
  sp' = fresh_block sps' ->
  match_stacks_inside F m m' stk stk' f' ctx sps' rs' ->
  context_below ctx ctx' ->
  context_stack_tailcall ctx f ctx' ->
  ctx'.(retinfo) = ctx.(retinfo) ->
  range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize) ->
  tr_funbody fenv f'.(fn_stacksize) ctx' f f'.(fn_code) ->
  match_stacks_inside F m m' stk stk' f' ctx' sps' rs'.
Proof.
  intros. inv H0.
  (* base *)
  eapply match_stacks_inside_base.  eauto. congruence.
  rewrite H2. rewrite DSTK. apply align_unchanged. apply min_alignment_pos. apply Z.divide_0_r.
  (* inlined *)
  assert (dstk ctx <= dstk ctx'). rewrite H2. apply align_le. apply min_alignment_pos.
  eapply match_stacks_inside_inlined; eauto.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; lia. apply H4. inv H5. extlia.
  congruence.
  unfold context_below in *. extlia.
  unfold context_stack_call in *. lia.
Qed.

(** ** Relating states *)

Definition injp_tm (w: injp_world) := match w with injpw _ _ tm _ => tm end.

Inductive match_states: injp_world -> RTL.state -> RTL.state -> Prop :=
  | match_regular_states: forall stk f sp pc rs m stk' f' sps' sp' rs' m' F fenv ctx Hm wp
        (SPS: sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' stk stk' f' ctx sps' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (AG: agree_regs F ctx rs rs')
        (SP: F sp = Some(sp', ctx.(dstk)))
        (TID: fst sp = Mem.tid (Mem.support m))
        (NEWB: ~ Mem.valid_block init_m sp /\ ~ Mem.valid_block init_tm sp')
        (ACCE: injp_acce w (injpw F m m' Hm))
        (ACCI: injp_acci wp (injpw F m m' Hm))
        (VB: Mem.sup_include (sup_incr sps') (Mem.support m'))
        (THREAD_SPS: Mem.tid sps' = Mem.tid (Mem.support m'))
        (PRIV: range_private F m m' sp' (ctx.(dstk) + ctx.(mstk)) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states wp (State stk f (Vptr sp Ptrofs.zero) pc rs m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) (spc ctx pc) rs' m')
  | match_call_states: forall stk vf args m stk' vf' args' m' cunit F Hm wp
        (MS: match_stacks F m m' stk stk' (Mem.support m'))
        (LINK: linkorder cunit prog)
        (FINJ: Val.inject F vf vf')
        (VINJ: Val.inject_list F args args')
        (ACCE: injp_acce w (injpw F m m' Hm))
        (ACCI: injp_acci wp (injpw F m m' Hm)),
      match_states wp (Callstate stk vf args m)
                   (Callstate stk' vf' args' m')
  | match_call_regular_states: forall stk f vf vargs m stk' f' sps' sp' rs' m' F fenv ctx ctx' pc' pc1' rargs Hm wp
        (SPS: sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' stk stk' f' ctx sps' rs')
        (COMPAT: fenv_compat prog fenv)
        (FB: tr_funbody fenv f'.(fn_stacksize) ctx f f'.(fn_code))
        (BELOW: context_below ctx' ctx)
        (NOP: f'.(fn_code)!pc' = Some(Inop pc1'))
        (MOVES: tr_moves f'.(fn_code) pc1' (sregs ctx' rargs) (sregs ctx f.(fn_params)) (spc ctx f.(fn_entrypoint)))
        (VFIND: Genv.find_funct ge vf = Some (Internal f))
        (VINJ: list_forall2 (val_reg_charact F ctx' rs') vargs rargs)
        (NEWB: ~ Mem.valid_block init_tm sp')
        (ACCE: injp_acce w (injpw F m m' Hm))
        (ACCI: injp_acci wp (injpw F m m' Hm))
        (MINJ: Mem.inject F m m')
        (VB: Mem.sup_include (sup_incr sps') (Mem.support m'))
        (THREAD_SPS: Mem.tid sps' = Mem.tid (Mem.support m'))
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states wp (Callstate stk vf vargs m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m')
  | match_return_states: forall stk v m stk' v' m' F Hm wp
        (MS: match_stacks F m m' stk stk' (Mem.support m'))
        (VINJ: Val.inject F v v')
        (ACCE: injp_acce w (injpw F m m' Hm))
        (ACCI: injp_acci wp (injpw F m m' Hm)),
      match_states wp (Returnstate stk v m)
                   (Returnstate stk' v' m')
  | match_return_regular_states: forall stk v m stk' f' sps' sp' rs' m' F ctx pc' or rinfo Hm wp
        (SPS' : sp' = fresh_block sps')
        (MS: match_stacks_inside F m m' stk stk' f' ctx sps' rs')
        (RET: ctx.(retinfo) = Some rinfo)
        (AT: f'.(fn_code)!pc' = Some(inline_return ctx or rinfo))
        (VINJ: match or with None => v = Vundef | Some r => Val.inject F v rs'#(sreg ctx r) end)
        (NEWB: ~ Mem.valid_block init_tm sp')
        (ACCE: injp_acce w (injpw F m m' Hm))
        (ACCI: injp_acci wp (injpw F m m' Hm))
        (VB: Mem.sup_include (sup_incr sps') (Mem.support m'))
        (THREAD_SPS: Mem.tid sps' = Mem.tid (Mem.support m'))
        (PRIV: range_private F m m' sp' ctx.(dstk) f'.(fn_stacksize))
        (SSZ1: 0 <= f'.(fn_stacksize) < Ptrofs.max_unsigned)
        (SSZ2: forall ofs, Mem.perm m' sp' ofs Max Nonempty -> 0 <= ofs <= f'.(fn_stacksize)),
      match_states wp (Returnstate stk v m)
                   (State stk' f' (Vptr sp' Ptrofs.zero) pc' rs' m').

(** ** Forward simulation *)

Definition measure (S: RTL.state) : nat :=
  match S with
  | State _ _ _ _ _ _ => 1%nat
  | Callstate _ _ _ _ => 0%nat
  | Returnstate _ _ _ => 0%nat
  end.

Lemma tr_funbody_inv:
  forall fenv sz cts f c pc i,
  tr_funbody fenv sz cts f c -> f.(fn_code)!pc = Some i -> tr_instr fenv sz cts pc i c.
Proof.
  intros. inv H. eauto.
Qed.

Theorem step_simulation:
  forall S1 t S2,
  step ge S1 t S2 ->
  forall S1' Wp (MS: match_states Wp S1 S1'),
  (exists S2', plus step tge S1' t S2' /\ match_states Wp S2 S2')
  \/ (measure S2 < measure S1 /\ t = E0 /\ match_states Wp S2 S1')%nat.
Proof.
  induction 1; intros; inv MS; try congruence.

- (* nop *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto.

- (* op *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_operation_inject.
    eapply match_stacks_inside_globalenvs; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eexact Hm. eauto.
  fold (sop ctx op). intros [v' [A B]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* load *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globalenvs; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold (saddr ctx addr). intros [a' [P Q]].
  exploit Mem.loadv_inject; eauto. intros [v' [U V]].
  left; econstructor; split.
  eapply plus_one. eapply exec_Iload; eauto.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto.

- (* store *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit eval_addressing_inject.
    eapply match_stacks_inside_globalenvs; eauto.
    eexact SP.
    instantiate (2 := rs##args). instantiate (1 := rs'##(sregs ctx args)). eapply agree_val_regs; eauto.
    eauto.
  fold saddr. intros [a' [P Q]].
  exploit Mem.storev_mapped_inject; eauto. eapply agree_val_reg; eauto.
  intros [m1' [U V]].
  exploit injp_acc_tl_storev. apply H1. apply U. eauto.
  instantiate (1:= V). instantiate (1:= Hm).
  intro ACCS.
  left; econstructor; split.
  eapply plus_one. eapply exec_Istore; eauto.
  destruct a; simpl in H1; try discriminate.
  destruct a'; simpl in U; try discriminate.
  econstructor; eauto.
  eapply match_stacks_inside_store; eauto.
  erewrite Mem.support_store; eauto.
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
  erewrite Mem.support_store; eauto.
  erewrite Mem.support_store; eauto.
  eapply range_private_invariant; eauto.
  intros; split; auto. eapply Mem.perm_store_2; eauto.
  intros; eapply Mem.perm_store_1; eauto.
  intros. eapply SSZ2. eapply Mem.perm_store_2; eauto.

- (* call *)
  exploit match_stacks_inside_globalenvs; eauto. intros SEINJ.
  edestruct functions_translated with (v := vf) as (cu & fd' & A & B & C); eauto.
  eapply ros_address_agree; eauto.
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_cons; eauto.
  eapply match_stacks_inside_tid3; eauto.
  eapply match_stacks_inside_tid2; eauto.
  eapply ros_address_agree; eauto.
  eapply agree_val_regs; eauto.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply ros_address_inlined with (rs:=rs); eauto).
  subst fd.
  right; split. simpl; lia. split. auto.
  econstructor; eauto.
  eapply match_stacks_inside_inlined; eauto.
  red; intros. apply PRIV. inv H13. destruct H16. extlia.
  apply agree_val_regs_gen; auto. apply NEWB.
  red; intros; apply PRIV. destruct H16. lia.

- (* tailcall *)
  exploit match_stacks_inside_globalenvs; eauto. intros SEINJ.
  edestruct functions_translated with (v := vf) as (cu & fd' & A & B & C); eauto.
  eapply ros_address_agree; eauto.
  assert (PRIV': range_private F m' m'0 (fresh_block sps') (dstk ctx) f'.(fn_stacksize)).
  { eapply range_private_free_left; eauto. inv FB. rewrite <- H4. auto. }
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* within the original function *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 (fresh_block sps') 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by lia. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. lia.
    inv FB. eapply range_private_perms; eauto. extlia.
    destruct X as [m1' FREE].
  assert (Hm' : Mem.inject F m' m1').
  eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
    intros. rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). lia. intros [P Q].
    eelim Q; eauto. replace (ofs + delta - delta) with ofs by lia.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
    assert (ACCS: injp_acc_small w (injpw F m m'0 Hm) (injpw F m' m1' Hm')).
    {
      remember w.
      destruct w0. econstructor.
      red. intros. exfalso. apply H1. eauto with mem.
      red. intros. exfalso. apply H1. eauto with mem.
      reflexivity.
      eapply Mem.ro_unchanged_free; eauto.
      eapply Mem.ro_unchanged_free; eauto.
      red. intros. eauto with mem.
      red. intros. eauto with mem.
      split. erewrite <- Mem.support_free; eauto. eapply Mem.free_unchanged_on; eauto.
      intros. intros [X [Y|Y]]. congruence. destruct NEWB. apply H3. unfold init_m. rewrite <- Heqw0.
      auto.
      split. erewrite <- Mem.support_free; eauto. eapply Mem.free_unchanged_on; eauto.
      intros. intros [X [Y|Y]]. apply Y. inversion Hm. inv mi_thread. inv Hms.
      rewrite H4. rewrite <- THREAD_SPS. reflexivity. destruct NEWB. apply H4. unfold init_tm.
      rewrite <- Heqw0. auto.
      eauto. red. intros. congruence.
      red. intros. congruence.
      red. intros. congruence.
      red. intros. exfalso. apply H5.
      eapply Mem.perm_free_1; eauto. left. intro. subst.
      apply H3. eauto.
    }
  left; econstructor; split.
  eapply plus_one. eapply exec_Itailcall; eauto.
  eapply sig_function_translated; eauto.
  econstructor; eauto.
  eapply match_stacks_sup_include with (support := sps').
  eapply match_stacks_invariant; eauto.
  red. intros. congruence. red. intros. congruence.
  rewrite (Mem.support_free _ _ _ _ _ H2). eauto.
  rewrite (Mem.support_free _ _ _ _ _ H2). eauto.
  rewrite (Mem.support_free _ _ _ _ _ FREE). eauto.
  rewrite (Mem.support_free _ _ _ _ _ FREE). eauto.
(*
    red. intros. eapply Mem.perm_free_3; eauto.
    red. intros. eapply Mem.perm_free_3; eauto.
*)
    intros. eapply Mem.perm_free_3; eauto.
    intros. eapply Mem.perm_free_1; eauto with ordered_type.
    intros. left. intro. subst b. eapply freshness; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    erewrite Mem.support_free; eauto.
    erewrite Mem.support_free; eauto.
  eapply ros_address_agree; eauto.
  eapply agree_val_regs; eauto.
  eapply injp_acce_small; eauto.
  etransitivity. eauto. eapply injp_acc_small_acci; eauto.
+ (* turned into a call *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Icall; eauto.
  eapply sig_function_translated; eauto.
  exploit Mem.free_left_inject; eauto. intro Hm'.
  assert (injp_acc_tl (injpw F m m'0 Hm) (injpw F m' m'0 Hm')).
  {
    econstructor; eauto.
    red. intros. exfalso. apply H1. eauto with mem.
    red. intros. congruence.
    eapply Mem.ro_unchanged_free; eauto.
    red. intros. eauto.
    red. intros. eauto with mem.
    split. erewrite <- Mem.support_free; eauto. eapply Mem.free_unchanged_on; eauto.
    intros. intro. congruence.
    split; eauto. eauto with mem.
    red. intros. congruence.
    red. intros. congruence.
    red. intros. exfalso. eapply H5.
    eapply Mem.perm_free_1; eauto. left. intro. subst.
    apply H3. eauto.
  }
  econstructor; eauto.
  eapply match_stacks_untailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
  rewrite (Mem.support_free _ _ _ _ _ H2). eauto.
  rewrite (Mem.support_free _ _ _ _ _ H2). eauto.
  red. intros.  congruence.
  red. intros.  congruence.
  intros. eapply Mem.perm_free_3; eauto.
  eapply match_stacks_inside_tid3; eauto.
  eapply match_stacks_inside_tid2; eauto.
  eapply ros_address_agree; eauto.
  eapply agree_val_regs; eauto.
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
+ (* inlined *)
  assert (EQ: fd = Internal f0) by (eapply ros_address_inlined with (rs:=rs); eauto).
  subst fd.
  right; split. simpl; lia. split. auto.
  exploit Mem.free_left_inject; eauto. intro Hm'.
  assert (injp_acc_tl (injpw F m m'0 Hm) (injpw F m' m'0 Hm')).
  {
    constructor; eauto.
    red. intros. exfalso. apply H1. eauto with mem.
    red. intros. congruence.
    eapply Mem.ro_unchanged_free; eauto.
    red. intros. eauto.
    red. intros. eauto with mem.
    split. erewrite <- Mem.support_free; eauto. eapply Mem.free_unchanged_on; eauto.
    intros. intro. congruence.
    split; eauto with mem.
    red. intros. congruence.
    red. intros. congruence.
    red. intros. exfalso. eapply H9. eapply Mem.perm_free_1; eauto.
    left. intro. subst. apply H3. auto.
  }
  econstructor; eauto.
  eapply match_stacks_inside_inlined_tailcall; eauto.
  eapply match_stacks_inside_invariant; eauto.
  rewrite (Mem.support_free _ _ _ _ _ H2). eauto.
  rewrite (Mem.support_free _ _ _ _ _ H2). eauto.
  red. intros. congruence.  red. intros. congruence.
  intros. eapply Mem.perm_free_3; eauto.
  apply agree_val_regs_gen; auto. apply NEWB.
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
  red; intros; apply PRIV'.
    assert (dstk ctx <= dstk ctx'). red in H14; rewrite H14. apply align_le. apply min_alignment_pos.
    lia.

- (* builtin *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  exploit match_stacks_inside_globalenvs; eauto. intros SEINJ.
  exploit tr_builtin_args; eauto. intros (vargs' & P & Q).
  exploit external_call_mem_inject; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J [K [L [M [N O]]]]]]]]]]]]].
  assert (ACCS: injp_acc_tl (injpw F m m'0 Hm) (injpw F1 m' m1' C)).
  econstructor; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ibuiltin; eauto.
  econstructor.
    eauto.
    eapply match_stacks_inside_set_res.
    eapply match_stacks_inside_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto. eapply unchanged_on_tl_e; eauto.
    eapply inject_incr_local_noglobal; eauto.
    inversion C. inv mi_thread. auto.
    eapply external_call_support; eauto. destruct D as [[_ D]]. auto.
  auto. eauto. auto.
  destruct res; simpl; [apply agree_set_reg;auto|idtac|idtac]; eapply agree_regs_incr; eauto.
  auto. destruct D as [[_ D]]. congruence.
  auto.
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
  auto. eapply Mem.sup_include_trans; eauto. eapply Mem.unchanged_on_support. apply E. destruct E as [[X Y] _]. congruence. auto.
  eapply range_private_extcall; eauto.
  intros; eapply external_call_max_perm; eauto. eapply unchanged_on_tl_e; eauto.
  inversion C. inv mi_thread. auto.
  auto. apply VB. auto. auto.
  intros. apply SSZ2. eapply external_call_max_perm; eauto.
  apply VB.  auto.
- (* cond *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (eval_condition cond rs'##(sregs ctx args) m' = Some b).
    eapply eval_condition_inject; eauto. eapply agree_val_regs; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_Icond; eauto.
  destruct b; econstructor; eauto.

- (* jumptable *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
  assert (Val.inject F rs#arg rs'#(sreg ctx arg)). eapply agree_val_reg; eauto.
  rewrite H0 in H2; inv H2.
  left; econstructor; split.
  eapply plus_one. eapply exec_Ijumptable; eauto.
  rewrite list_nth_z_map. rewrite H1. simpl; reflexivity.
  econstructor; eauto.

- (* return *)
  exploit tr_funbody_inv; eauto. intros TR; inv TR.
+ (* not inlined *)
  inv MS0; try congruence.
  assert (X: { m1' | Mem.free m'0 (fresh_block sps') 0 (fn_stacksize f') = Some m1'}).
    apply Mem.range_perm_free. red; intros.
    destruct (zlt ofs f.(fn_stacksize)).
    replace ofs with (ofs + dstk ctx) by lia. eapply Mem.perm_inject; eauto.
    eapply Mem.free_range_perm; eauto. lia.
    inv FB. eapply range_private_perms; eauto.
    generalize (Zmax_spec (fn_stacksize f) 0). destruct (zlt 0 (fn_stacksize f)); lia.
    destruct X as [m1' FREE].
    assert (Hm' : Mem.inject F m' m1').
      eapply Mem.free_right_inject; eauto. eapply Mem.free_left_inject; eauto.
  (* show that no valid location points into the stack block being freed *)
  intros. inversion FB; subst.
  assert (PRIV': range_private F m' m'0 (fresh_block sps') (dstk ctx) f'.(fn_stacksize)).
    rewrite H8 in PRIV. eapply range_private_free_left; eauto.
  rewrite DSTK in PRIV'. exploit (PRIV' (ofs + delta)). lia. intros [A B].
  eelim B; eauto. replace (ofs + delta - delta) with ofs by lia.
  apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  assert (ACCS: injp_acc_small w (injpw F m m'0 Hm) (injpw F m' m1' Hm')).
    {
      remember w.
      destruct w0. econstructor.
      red. intros. exfalso. apply H1. eauto with mem.
      red. intros. exfalso. apply H1. eauto with mem.
      reflexivity.
      eapply Mem.ro_unchanged_free; eauto.
      eapply Mem.ro_unchanged_free; eauto.
      red. intros. eauto with mem.
      red. intros. eauto with mem.
      split. erewrite <- Mem.support_free; eauto. eapply Mem.free_unchanged_on; eauto.
      intros. intros [X [Y|Y]]. congruence. destruct NEWB. apply H3. unfold init_m. rewrite <- Heqw0.
      auto.
      split. erewrite <- Mem.support_free; eauto. eapply Mem.free_unchanged_on; eauto.
      intros. intros [X [Y|Y]]. apply Y. inversion Hm. inv mi_thread. inv Hms.
      rewrite H4. rewrite <- THREAD_SPS. reflexivity. destruct NEWB. apply H4. unfold init_tm.
      rewrite <- Heqw0. auto.
      eauto. red. intros. congruence.
      red. intros. congruence.
      red. intros. congruence.
      red. intros. exfalso. apply H6.
      eapply Mem.perm_free_1; eauto. left. intro. subst.
      apply H3. eauto.
    }
  left; econstructor; split.
  eapply plus_one. eapply exec_Ireturn; eauto.
  econstructor; eauto.
  eapply match_stacks_sup_include with (support := sps').
  eapply match_stacks_invariant; eauto.
  red. intros. congruence.  red. intros. congruence.
  rewrite (Mem.support_free _ _ _ _ _ H0). eauto.
  rewrite (Mem.support_free _ _ _ _ _ H0). eauto.
  rewrite (Mem.support_free _ _ _ _ _ FREE). eauto.
  rewrite (Mem.support_free _ _ _ _ _ FREE). eauto.
(*    red. intros. eapply Mem.perm_free_3; eauto. 
    red. intros. eapply Mem.perm_free_3; eauto.
*)
    intros. eapply Mem.perm_free_3; eauto.
    intros. eapply Mem.perm_free_1; eauto with ordered_type.
    intros. left. intro. subst b. eapply freshness; eauto.
    intros. eapply Mem.perm_free_3; eauto.
    erewrite Mem.support_free; eauto.
    erewrite Mem.support_free; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto.
  eapply injp_acce_small; eauto.
  etransitivity. eauto.  eapply injp_acc_small_acci; eauto.

+ (* inlined *)
  right. split. simpl. lia. split. auto.
  exploit Mem.free_left_inject; eauto. intro Hm'.
  assert (injp_acc_tl (injpw F m m'0 Hm) (injpw F m' m'0 Hm')).
  {
    econstructor; eauto.
    red. intros. exfalso. apply H1. eauto with mem.
    red. intros. congruence.
    eapply Mem.ro_unchanged_free; eauto.
    red. intros. eauto.
    red. intros. eauto with mem.
    split. erewrite <- Mem.support_free; eauto. eapply Mem.free_unchanged_on; eauto.
    intros. intro. congruence.
    split; eauto. eauto with mem.
    red. intros. congruence.
    red. intros. congruence.
    red. intros. exfalso. eapply H6.
    eapply Mem.perm_free_1; eauto. left. intro. subst.
    apply H3. eauto.
  }
  econstructor; eauto.
  eapply match_stacks_inside_invariant; eauto.
  rewrite (Mem.support_free _ _ _ _ _ H0). eauto.
  rewrite (Mem.support_free _ _ _ _ _ H0). eauto.
  red. intros. congruence.  red. intros. congruence.
  intros. eapply Mem.perm_free_3; eauto.
  destruct or; simpl. apply agree_val_reg; auto. auto. apply NEWB.
  etransitivity. eauto. eapply injp_acc_tl_e; eauto.
  etransitivity. eauto. eapply injp_acc_tl_i; eauto.
  inv FB. rewrite H6 in PRIV. eapply range_private_free_left; eauto.

- (* internal function, not inlined *)
  edestruct functions_translated as (cu & fd' & Hfd' & FD & Hcu); eauto.
  eapply match_stacks_globalenvs; eauto.
  assert (A: exists f', tr_function cu f f' /\ fd' = Internal f').
  { Errors.monadInv FD. exists x. split; auto. eapply transf_function_spec; eauto. }
  destruct A as [f' [TR1 EQ]].
  assert (TR: tr_function prog f f').
  { eapply tr_function_linkorder; eauto. }
  inversion TR; subst.
  exploit Mem.alloc_parallel_inject. eauto. eauto. apply Z.le_refl.
    instantiate (1 := fn_stacksize f'). inv H1. extlia.
  intros [F' [m1' [sp' [A [B [C [D E]]]]]]].
  exploit injp_acc_tl_alloc. apply H. apply A. eauto. eauto. eauto.
  instantiate (1:= B). instantiate (1:= Hm).
  intro ACCS.
  left; econstructor; split.
  eapply plus_one. eapply exec_function_internal; eauto.
  rewrite H6. econstructor.
  eapply Mem.alloc_result. eauto.
  instantiate (1 := F'). apply match_stacks_inside_base.
  assert (SPS: sp' = fresh_block (Mem.support m'0)) by (eapply Mem.alloc_result; eauto).
  eapply match_stacks_invariant; eauto.
    intros. destruct (eq_block b1 stk).
    subst b1. rewrite D in H8; inv H8.
    apply Mem.alloc_result in H. subst.
    apply match_stacks_support in MS0.
    exfalso. destruct MS0.
    destruct H9; eapply freshness; eauto.
    rewrite E in H8; auto.
    red. intros. destruct (eq_block b1 stk). subst. split.
    eapply Mem.alloc_block_noglobal; eauto. rewrite D in H9. inv H9.
    eapply Genv.thread_noglobal; eauto. simpl. reflexivity. erewrite E in H9. congruence. eauto.
    red. intros.  inversion B. inv mi_thread. eapply Hjs; eauto.
    rewrite (Mem.support_alloc _ _ _ _ _ H). eauto.
    rewrite (Mem.support_alloc _ _ _ _ _ H). eauto.
    rewrite (Mem.support_alloc _ _ _ _ _ A). eauto.
    rewrite (Mem.support_alloc _ _ _ _ _ A). eauto.
    intros. exploit Mem.perm_alloc_inv. eexact H. eauto.
    destruct (eq_block b1 stk); intros; auto.
    subst b1. rewrite D in H8; inv H8. eelim freshness; eauto.
    intros. eapply Mem.perm_alloc_1; eauto.
    intros. exploit Mem.perm_alloc_inv. eexact A. eauto.
    rewrite dec_eq_false; auto with ordered_type.
  intro. subst b. eelim freshness. rewrite SPS in H8. eauto.
  auto. auto. auto. eauto. auto.
  rewrite H5. apply agree_regs_init_regs. eauto. auto. inv H1; auto. congruence.
  erewrite Mem.support_alloc; eauto. apply Mem.alloc_result in H. rewrite H.
  reflexivity.
  apply match_stacks_support in MS0 as [SUP1 SUP2].
  split. intro. eapply Mem.fresh_block_alloc. apply H. eapply SUP1. auto.
  intro. eapply Mem.fresh_block_alloc. apply A. eapply SUP2. auto.
  etransitivity. eauto. eapply injp_acc_tl_e. eauto.
  etransitivity. eauto. eapply injp_acc_tl_i. eauto.
  rewrite Mem.support_alloc with m'0 0 (fn_stacksize f') m1' sp'.
  apply Mem.sup_include_refl. auto. 
  inv A. reflexivity. 
  red; intros. split.
  eapply Mem.perm_alloc_2; eauto. inv H1; extlia.
  intros; red; intros. exploit Mem.perm_alloc_inv. eexact H. eauto.
  destruct (eq_block b stk); intros.
  subst. rewrite D in H9; inv H9. inv H1; extlia.
  rewrite E in H9; auto. eelim Mem.fresh_block_alloc. eexact A. eapply Mem.mi_mappedblocks; eauto.
  auto.
  intros. exploit Mem.perm_alloc_inv; eauto. rewrite dec_eq_true. lia.

- (* internal function, inlined *)
  rewrite VFIND in FIND. inv FIND.
  inversion FB; subst.
  exploit Mem.alloc_left_mapped_inject.
    instantiate (1:= m'0). instantiate (1:= fresh_block sps').
    simpl. auto.
    eauto.
    eauto.
    (* sp' is valid *)
    apply VB. auto.
    (* offset is representable *)
    instantiate (1 := dstk ctx). generalize (Z.le_max_r (fn_stacksize f) 0). extlia.
    (* size of target block is representable *)
    intros. right. exploit SSZ2; eauto with mem. inv FB; lia.
    (* we have full permissions on sp' at and above dstk ctx *)
    intros. apply Mem.perm_cur. apply Mem.perm_implies with Freeable; auto with mem.
    eapply range_private_perms; eauto. extlia.
    (* offset is aligned *)
    replace (fn_stacksize f - 0) with (fn_stacksize f) by lia.
    inv FB. apply min_alignment_sound; auto.
    (* nobody maps to (sp, dstk ctx...) *)
    intros. exploit (PRIV (ofs + delta')); eauto. extlia.
    intros [A B]. eelim B; eauto.
    replace (ofs + delta' - delta') with ofs by lia.
    apply Mem.perm_max with k. apply Mem.perm_implies with p; auto with mem.
  intros [F' [A [B [C D]]]].
  exploit tr_moves_init_regs; eauto. intros [rs'' [P [Q R]]].
  assert (ACCS : injp_acc_small w (injpw F m m'0 Hm) (injpw F' m' m'0 A)).
  {
    unfold init_tm in NEWB. destruct w. simpl in NEWB.
    econstructor; eauto.
    - red. intros. 
      eapply Mem.valid_block_alloc_inv in H7; eauto. destruct H7.
      subst. eapply Mem.alloc_result in H. rewrite H. reflexivity. congruence.
    - red. intros. congruence.
    - eapply Mem.ro_unchanged_alloc; eauto.
    - red. intros. eauto.
    - red. intros. eauto with mem.
    - split. erewrite (Mem.support_alloc _ _ _ _ _ H); eauto. simpl. split; eauto.
      simpl. rewrite Mem.update_list_length. eauto.
      eapply Mem.alloc_unchanged_on; eauto.
    - split. eauto. eauto with mem.
    - red. intros. destruct (eq_block b1 stk). subst. exfalso. apply H8.
      apply Mem.alloc_result in H. rewrite H. reflexivity. erewrite D in H7; eauto.
      congruence.
    - red. intros. destruct (eq_block b1 stk). subst.
      apply Mem.alloc_result in H. rewrite H. reflexivity.
      erewrite D in H7. congruence. eauto.
    - red. intros.  destruct (eq_block b1 stk). subst. split.
      intro. eapply Mem.fresh_block_alloc; eauto.
      inv ACCE. destruct H19. inv unchanged_on_e'. apply unchanged_on_support. auto.
      rewrite C in H7. inv H7. apply NEWB.
      erewrite D in H7; eauto. congruence.
    - red. intros. eauto with mem.
  }
  left; econstructor; split.
  eapply plus_left. eapply exec_Inop; eauto. eexact P. traceEq.
  econstructor. auto.
  eapply match_stacks_inside_alloc_left; eauto.
  eapply match_stacks_inside_invariant; eauto.
  red. intros. congruence.  red. intros. congruence.
  lia. eauto. eauto.
  apply agree_regs_incr with F; auto. auto.
  erewrite Mem.support_alloc; eauto. eapply Mem.alloc_result in H.
  rewrite H. reflexivity.
  edestruct match_stacks_inside_support as [SUP1 [SUP2 SUP3]]. eauto.
  split. intro. eapply Mem.fresh_block_alloc. apply H. apply SUP1. auto.
  intro. eapply freshness. apply SUP3. auto.
  eapply injp_acce_small; eauto. etransitivity. eauto. eapply injp_acc_small_acci; eauto.
  auto. auto.
  rewrite H2. eapply range_private_alloc_left; eauto.
  auto. auto.

- (* external function *)
  exploit match_stacks_globalenvs; eauto. intros SEINJ.
  exploit external_call_mem_inject; eauto.
  intros [F1 [v1 [m1' [A [B [C [D [E [J [K [L [M [N O]]]]]]]]]]]]].
  edestruct functions_translated as (cu & fd' & Hfd' & FD & Hcu); eauto.
  simpl in FD. inv FD.
  assert (ACCS: injp_acc_tl (injpw F m m'0 Hm) (injpw F1 m' m1' C)).
  econstructor; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intro. eauto using external_call_readonly; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  red. intros. eapply external_call_max_perm; eauto.
  left; econstructor; split.
  eapply plus_one. eapply exec_function_external; eauto.
  econstructor.
    eapply match_stacks_sup_include with (Mem.support m'0).
    eapply match_stacks_extcall with (F1 := F) (F2 := F1) (m1 := m) (m1' := m'0); eauto.
    intros; eapply external_call_max_perm; eauto.
    intros; eapply external_call_max_perm; eauto.
    eapply unchanged_on_tl_e; eauto.
    eapply inject_incr_local_noglobal; eauto.
    inversion C. inv mi_thread. auto.
    eapply external_call_support; eauto. destruct D as [[_ D]]. auto.
    eapply external_call_support; eauto. destruct E as [[_ E]]. auto.
    destruct E as [[_ X] _]. auto. auto.
    etransitivity. eauto. eapply injp_acc_tl_e; eauto.
    etransitivity. eauto. eapply injp_acc_tl_i; eauto.

- (* return from noninlined function *)
  inv MS0.
+ (* normal case *)
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  econstructor; eauto.
  apply match_stacks_inside_set_reg; auto.
  apply agree_set_reg; auto. congruence.
+ (* untailcall case *)
  inv MS; try congruence.
  rewrite RET in RET0; inv RET0.
  left; econstructor; split.
  eapply plus_one. eapply exec_return.
  eapply match_regular_states. auto.
  eapply match_stacks_inside_set_reg; eauto.
  eauto. auto.
  apply agree_set_reg; auto.
  auto. eauto. eauto. eauto. eauto. eauto. eauto. congruence.
  red; intros. destruct (zlt ofs (dstk ctx)). apply PAD; lia. apply PRIV; lia.
  auto. auto.

- (* return from inlined function *)
  inv MS0; try congruence. rewrite RET0 in RET; inv RET.
  unfold inline_return in AT.
  assert (PRIV': range_private F m m' (fresh_block sps') (dstk ctx' + mstk ctx') f'.(fn_stacksize)).
    red; intros. destruct (zlt ofs (dstk ctx)). apply PAD. lia. apply PRIV. lia.
  destruct or.
+ (* with a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Iop; eauto. simpl. reflexivity.
  econstructor; eauto. apply match_stacks_inside_set_reg; auto. apply agree_set_reg; auto.
+ (* without a result *)
  left; econstructor; split.
  eapply plus_one. eapply exec_Inop; eauto.
  econstructor; eauto. subst vres. apply agree_set_reg_undef'; auto.
Qed.

Lemma transf_initial_states:
  forall q1 q2, GS.match_query (c_injp) w q1 q2 ->
  forall S, initial_state ge q1 S ->
  exists R, initial_state tge q2 R /\ match_states w S R.
Proof.
  intros q1 q2 Hq S Hi.
  inversion Hq as [vf1 vf2 sg vargs1 vargs2 m1 m2 Hvf Hvargs Hm Hvf1]. clear Hq. subst.
  inversion Hi. clear Hi. subst m vargs vf.  destruct w eqn: Hw.
  simpl in *. inv Hm. clear Hm2 Hm3 Hm4.
  eapply functions_translated in H4 as (cu & tf & FIND & TR & LINK); eauto.
  setoid_rewrite <- (sig_function_translated _ _ _ TR).
  simpl in TR. destruct transf_function eqn:Hf; try discriminate. cbn in TR. inv TR.
  exists (Callstate nil vf2 vargs2 m2); split.
  econstructor; eauto.
  econstructor; eauto. 
  apply match_stacks_nil; auto; try (unfold local_t; rewrite Hw; reflexivity).
  - rewrite Hw. constructor; eauto.
    simpl. red. intros. congruence.
    red. intros. congruence.
  - unfold local_t, init_m. rewrite Hw. reflexivity.
  - unfold local_t, init_m. rewrite Hw. inversion Hm0. destruct mi_thread. destruct Hms. auto.
  - unfold local_t, init_m. rewrite Hw. inversion Hm0. destruct mi_thread. destruct Hms. auto.
  - inversion Hm0. inv mi_thread. auto.
  - unfold init_tm. rewrite Hw. cbn. eauto.
  - rewrite Hw. reflexivity.
  - reflexivity.
  - inv GE. auto.
Qed.

Lemma transf_final_states:
  forall gw S R r1, match_states gw S R -> final_state S r1 ->
  exists r2 gw', final_state R r2 /\ w o-> gw' /\ gw *-> gw' /\ GS.match_reply (c_injp) gw' r1 r2.
Proof.
  intros. inv H0. inv H.
  - exploit match_stacks_empty; eauto. intros EQ; subst. inv MS.
    eexists. eexists. split. econstructor; eauto. split. eauto.
    split. eauto. constructor. auto. constructor; eauto.
  - exploit match_stacks_inside_empty; eauto. intros [A B]. congruence.
Qed.

Lemma transf_external_states:
  forall gw S R q1, match_states gw S R -> at_external ge S q1 ->
  exists wx q2, at_external tge R q2 /\ gw *-> wx /\ GS.match_query (c_injp) wx q1 q2 /\ match_senv (cc_c injp) wx se tse /\
  forall r1 r2 S' gw'', wx o-> gw'' -> GS.match_reply (c_injp) gw'' r1 r2 -> after_external S r1 S' ->
  exists R', after_external R r2 R' /\ match_states gw'' S' R'.
Proof.
  intros gw S R q1 HSR Hq1.
  destruct Hq1; inv HSR; try congruence.
  exploit match_stacks_globalenvs; eauto. intros SEINJ.
  edestruct functions_translated as (cu & fd' & Hfd' & FD & Hcu); eauto.
  simpl in FD. inv FD. simpl.
  eexists (injpw _ _ _ Hm), _. intuition idtac.
  - econstructor; eauto.
  - econstructor; eauto. constructor; auto.
    destruct FINJ; cbn in *; congruence.
  - constructor.
    + eapply match_stacks_globalenvs; eauto.
    + eapply match_stacks_support in MS; eauto. destruct MS. inv GE. rewrite <- H5 in ACCE. inv ACCE. destruct H16 as [? [X ?]]. eauto.
    + eapply match_stacks_support in MS; eauto. destruct MS. inv GE. rewrite <- H5 in ACCE. inv ACCE. destruct H17 as [? [X ?]]. eauto.
  - inv H1. inv H2. inv H4. simpl in *. inv H0.
    eexists; split; econstructor; eauto.
    eapply match_stacks_sup_include with (Mem.support m').
    eapply match_stacks_extcall with (F1 := F) (F2 := f) (m1 := m) (m1' := m'); eauto.
    inversion Hm2. inv mi_thread. auto.
    eapply Mem.unchanged_on_support; eauto. apply H12. destruct H12 as [[_ X]]. auto.
    eapply Mem.unchanged_on_support; eauto. apply H13. destruct H13 as [[_ X]]. auto.
    etransitivity; eauto. econstructor; eauto.
    reflexivity.
Qed.

End INLINING.

Theorem transf_program_correct prog tprog:
  match_prog prog tprog ->
  GS.forward_simulation (c_injp) (semantics prog) (semantics tprog).
Proof.
   intros. red. constructor. econstructor.
  - fsim_skel H.
  - intros. eapply GS.forward_simulation_star; eauto.
    + intros. destruct H0, H2. cbn in *.
    eapply (Genv.is_internal_match H); eauto 1.
    unfold transf_fundef, transf_partial_fundef.
    intros ? [|] [|]; cbn -[transf_function]; inversion 1; auto.
    destruct transf_function; inv H10.  
    + intros. eapply transf_initial_states; eauto.
    + intros. eapply transf_final_states; eauto.
    + intros. eapply transf_external_states; eauto.
    + apply step_simulation; eauto.
  - auto using well_founded_ltof.
Qed.

