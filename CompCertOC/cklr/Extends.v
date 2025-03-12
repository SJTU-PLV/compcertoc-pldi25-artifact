Require Import Axioms.
Require Import Events.
Require Import LanguageInterface.
Require Import CallconvAlgebra.
Require Import CKLR.
Require Import Inject.
Require Import InjectFootprint.


(** * [Mem.extends] as a CKLR *)

(** ** Preliminaries *)

Global Instance block_inject_sameofs_refl:
  Reflexive (block_inject_sameofs inject_id).
Proof.
  intros b.
  constructor.
Qed.

Global Instance ptr_inject_corefl:
  Coreflexive (ptr_inject inject_id).
Proof.
  intros ptr1 ptr2 Hptr.
  destruct Hptr.
  inv H. rewrite Z.add_0_r.
  reflexivity.
Qed.

Global Instance rptr_inject_corefl:
  Coreflexive (rptr_inject inject_id).
Proof.
  intros ptr1 ptr2 [Hptr|Hptr].
  - eapply coreflexivity; eauto.
  - destruct Hptr as [_ _ [b1 ofs1 b2 delta Hb]].
    inv Hb.
    rewrite Ptrofs.add_zero.
    reflexivity.
Qed.

Global Instance ptrrange_inject_corefl:
  Coreflexive (ptrrange_inject inject_id).
Proof.
  intros ptr1 ptr2 Hptr.
  destruct Hptr.
  apply coreflexivity in H. inv H.
  reflexivity.
Qed.

Global Instance block_inject_corefl:
  Coreflexive (block_inject inject_id).
Proof.
  intros b1 b2 Hb.
  destruct Hb.
  inv H.
  reflexivity.
Qed.

Lemma val_inject_lessdef_eqrel:
  eqrel (Val.inject inject_id) Val.lessdef.
Proof.
  split; intros x y; apply val_inject_lessdef.
Qed.

Global Instance flat_inject_id thr:
  Related (Mem.flat_inj thr) inject_id inject_incr.
Proof.
  intros b1 b2 delta.
  unfold Mem.flat_inj, inject_id.
  destruct Mem.sup_dec; try discriminate.
  auto.
Qed.

(** ** Definition *)

Inductive ext_world := extw (m1 m2 : mem) (Hm: Mem.extends m1 m2).

Inductive ext_match_mem: ext_world -> relation mem :=
  ext_match_mem_intro m1 m2 Hm:
    ext_match_mem (extw m1 m2 Hm) m1 m2.

Program Definition ext: cklr :=
  {|
    world := ext_world;
    wacc := ⊤;
    mi w := inject_id;
    match_mem := ext_match_mem;
    match_stbls w := eq;
  |}.

Next Obligation.
  repeat rstep. apply inject_incr_refl.
Qed.

Next Obligation.
  rauto.
Qed.

Next Obligation.
  repeat intro. subst. apply Genv.match_stbls_id.
Qed.

Next Obligation.
  inv H0.
  erewrite <- Mem.mext_sup; eauto.
Qed.

Next Obligation.
  intros [a b Hm] m1 m2 H lo hi. inv H.
  destruct (Mem.alloc m1 lo hi) as [m1' b1] eqn:H1.
  edestruct Mem.alloc_extends as (m2' & Hm2' & Hm'); eauto; try reflexivity.
  rewrite Hm2'.
  exists (extw m1' m2' Hm'); split. red. reflexivity.
  split. constructor. rauto.
Qed.

Next Obligation.
  intros [a b' Hm] m1 m2 H [[b lo] hi] r2 Hr. inv H.
  apply coreflexivity in Hr; subst. simpl. red.
  destruct (Mem.free m1 b lo hi) as [m1'|] eqn:Hm1'; [|constructor].
  edestruct Mem.free_parallel_extends as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. constructor.
  eexists; split. 2: econstructor. instantiate (1:= Hm'). reflexivity.
Qed.

Next Obligation.
  intros [c d Hm] chunk m1 m2 H [b ofs] p2 Hp. inv H.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.load chunk m1 b ofs) as [v1|] eqn:Hv1; [|constructor].
  edestruct Mem.load_extends as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rewrite val_inject_lessdef_eqrel. rauto.
Qed.

Next Obligation.
  intros [c d Hm] chunk m1 m2 H [b ofs] p2 Hp v1 v2 Hv. inv H.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.store chunk m1 b ofs v1) as [m1'|] eqn:Hm1'; [|constructor].
  apply val_inject_lessdef in Hv.
  edestruct Mem.store_within_extends as (m2' & Hm2' & Hm'); eauto.
  rewrite Hm2'. constructor. eexists; split. 2: econstructor.
  instantiate (1:= Hm'). reflexivity.
Qed.

Next Obligation.
  intros [c d Hm] m1 m2 H [b ofs] p2 Hp sz. inv H.
  apply coreflexivity in Hp; subst. simpl. red.
  destruct (Mem.loadbytes m1 b ofs sz) as [v1|] eqn:Hv1; [|constructor].
  edestruct Mem.loadbytes_extends as (v2 & Hv2 & Hv); eauto.
  rewrite Hv2. rauto.
Qed.

Next Obligation.
  intros [c d Hm] m1 m2 H [b1 ofs1] p2 Hp vs1 vs2 Hv. inv H.
  apply coreflexivity in Hp. subst. simpl. red.
  destruct (Mem.storebytes m1 b1 ofs1 vs1) as [m1'|] eqn:Hm1'; [|constructor].
  edestruct Mem.storebytes_within_extends as (m2' & Hm2' & Hm'); eauto.
  eapply list_rel_forall2. apply Hv.
  rewrite Hm2'. constructor. eexists; split. 2: econstructor.
  instantiate (1:= Hm'). reflexivity.
Qed.

Next Obligation.
  intros [c d Hm] m1 m2 H0 [b1 ofs1] p2 Hp p k H. inv H0.
  apply coreflexivity in Hp. subst. simpl in *.
  eapply Mem.perm_extends; eauto.
Qed.

Next Obligation.
  intros [c d Hm] m1 m2 H b1 b2 Hb. inv H.
  apply coreflexivity in Hb. subst.
  apply Mem.valid_block_extends; eauto.
Qed.

Next Obligation.
  intros b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 Hb Hb1' Hb2' Hp1 Hp2.
  inv Hb1'. inv Hb2'. eauto.
Qed.

Next Obligation.
  extlia.
Qed.

Next Obligation.
  rewrite Z.add_0_r.
  assumption.
Qed.

Next Obligation.
  intuition extlia.
Qed.

Next Obligation.
  inv H. inv H0. inv H2. rewrite Z.add_0_r in H1.
  eapply Mem.perm_extends_inv; eauto.
Qed.

Next Obligation.
  destruct H0 as (?&?&?).
  inv H. inv H1. inv Hm1. inv Hm3.
  rewrite mext_sup. rewrite mext_sup0.
  reflexivity.
Qed.

(** * Useful lemmas *)

Lemma ext_lessdef w v1 v2:
  Val.inject (mi ext w) v1 v2 <-> Val.lessdef v1 v2.
Proof.
  symmetry. apply val_inject_lessdef.
Qed.

Lemma ext_lessdef_list w vs1 vs2:
  Val.inject_list (mi ext w) vs1 vs2 <-> Val.lessdef_list vs1 vs2.
Proof.
  split; induction 1; constructor; auto; apply val_inject_lessdef; auto.
Qed.
Lemma ext_extends w m1 m2:
  match_mem ext w m1 m2 -> Mem.extends m1 m2.
Proof.
  intro. inv H. auto.
Qed.

Hint Rewrite ext_lessdef ext_lessdef_list ext_extends: cklr.


(** * Composition theorems *)

Require Import CKLRAlgebra.

Lemma compose_meminj_id_left f:
  compose_meminj inject_id f = f.
Proof.
  apply functional_extensionality. intros b.
  unfold compose_meminj, inject_id.
  destruct (f b) as [[b' delta] | ]; eauto.
Qed.

Lemma compose_meminj_id_right f:
  compose_meminj f inject_id = f.
Proof.
  apply functional_extensionality. intros b.
  unfold compose_meminj, inject_id.
  destruct (f b) as [[b' delta] | ]; eauto.
  replace (delta + 0) with delta by extlia; eauto.
Qed.
(*
Lemma ext_ext :
   eqcklr (ext @ ext) ext.
Proof.
  split.
  - intros [[ ] [ ]] se1 se3 m1 m3 (se2 & Hse12 & Hse23) (m2 & Hm12 & Hm23).
    exists tt. cbn in *. repeat apply conj.
    + congruence.
    + eauto using Mem.extends_extends_compose.
    + rewrite compose_meminj_id_left. apply inject_incr_refl.
    + intros [ ] m1' m3' Hm _.
      exists (tt, tt). intuition auto.
      * exists m1'; eauto using Mem.extends_refl.
      * rauto.
  - intros [ ] se1 se2 m1 m2 Hse Hm.
    exists (tt, tt). cbn. repeat apply conj.
    + ercompose; eauto.
    + exists m1; eauto using Mem.extends_refl.
    + rewrite compose_meminj_id_left. apply inject_incr_refl.
    + intros [[ ] [ ]] m1' m3' (m2' & Hm12' & Hm23') _.
      exists tt. intuition auto.
      * eauto using Mem.extends_extends_compose.
      * rauto.
Qed.

Lemma ext_inj :
  eqcklr (ext @ inj) inj.
Proof.
  split.
  - intros [[ ] f] se1 se3 m1 m3 (se2 & Hse12 & Hse23) (m2 & Hm12 & Hm23).
    exists f. cbn in *. repeat apply conj; eauto.
    + congruence.
    + destruct Hm23. erewrite <- Mem.mext_sup; eauto.
      constructor; eauto.
      eapply Mem.extends_inject_compose; eauto.
    + rewrite compose_meminj_id_left. apply inject_incr_refl.
    + intros f' m1' m3' Hm' Hincr.
      exists (tt, f'). intuition auto; cbn.
      * exists m1'. eauto using Mem.extends_refl.
      * rauto.
      * rewrite compose_meminj_id_left. apply inject_incr_refl.
  - intros w se1 se2 m1 m2 Hse Hm.
    exists (tt, w). cbn. repeat apply conj.
    + ercompose; eauto.
    + exists m1. split; auto. apply Mem.extends_refl.
    + rewrite compose_meminj_id_left. apply inject_incr_refl.
    + intros [[ ] f'] m1' m2' (mi & Hm1i & Hmi2) [_ Hf']. cbn in *.
      exists f'. intuition auto.
      * destruct Hmi2. erewrite <- Mem.mext_sup; eauto.
        constructor; auto.
        eapply Mem.extends_inject_compose; eauto.
      * rewrite compose_meminj_id_left. apply inject_incr_refl.
Qed.

Lemma inj_ext :
  eqcklr (inj @ ext) inj.
Proof.
  split.
  - intros [f [ ]] se1 se3 m1 m3 (se2 & Hse12 & Hse23) (m2 & Hm12 & Hm23).
    exists f. cbn in *. repeat apply conj; eauto.
    + congruence.
    + destruct Hm12.
      erewrite (Mem.mext_sup m2 m3); eauto.
      constructor; eauto.
      eapply Mem.inject_extends_compose; eauto.
    + rewrite compose_meminj_id_right. apply inject_incr_refl.
    + intros f' m1' m3' Hm' Hincr.
      exists (f', tt). intuition auto; cbn.
      * exists m3'. eauto using Mem.extends_refl.
      * rauto.
      * rewrite compose_meminj_id_right. apply inject_incr_refl.
  - intros w se1 se2 m1 m2 Hse Hm.
    exists (w, tt). cbn. repeat apply conj.
    + ercompose; eauto.
    + exists m2. split; auto. apply Mem.extends_refl.
    + rewrite compose_meminj_id_right. apply inject_incr_refl.
    + intros [f' [ ]] m1' m2' (mi & Hm1i & Hmi2) [Hf' _]. cbn in *.
      exists f'. intuition auto.
      * destruct Hm1i.
        erewrite (Mem.mext_sup m3 m2'); eauto.
        constructor; auto.
        eapply Mem.inject_extends_compose; eauto.
      * rewrite compose_meminj_id_right. apply inject_incr_refl.
Qed.

Lemma injp__injp_ext_injp:
  subcklr injp (injp @ ext @ injp).
Proof.
  intros [f m1 m4 Hm14] se1 se4 ? ? STBL MEM. inv MEM.
  inv STBL. clear Hm0 Hm1 Hm2 Hm3 Hm4 Hm5. rename m2 into m4. rename m0 into m1.
  generalize (mem_inject_dom f m1 m4 Hm14). intro Hm12.
  exists (injpw (meminj_dom f) m1 m1 (mem_inject_dom f m1 m4 Hm14),(tt,
            injpw f m1 m4 Hm14)).
  simpl.
  repeat apply conj.
  - exists se1. split. constructor; eauto.
    eapply match_stbls_dom; eauto.
    exists se1. split. auto. constructor; eauto.
  - exists m1; split.
    constructor.
    exists m1; split. apply Mem.extends_refl.
    constructor; eauto.
  - rewrite compose_meminj_id_left.
    rewrite !meminj_dom_compose.
    apply inject_incr_refl.
  - intros (w12' & w23' & w34') m1' m4'.
    intros (m2' & Hm12' & m3' & Hm23' & Hm34').
    intros (H12 & H23 & H34). simpl in *.
    destruct Hm12' as [f12 m1' m2' Hm12'].
    destruct Hm34' as [f34 m3' m4' Hm34'].
    inv H12.
    inv H23.
    inv H34.
    assert (Hm14' :  Mem.inject (compose_meminj f12 f34) m1' m4').
    eapply Mem.inject_compose; eauto.
    eapply Mem.extends_inject_compose; eauto.
    eexists (injpw (compose_meminj f12 f34) m1' m4' Hm14').
    repeat apply conj.
    + constructor; eauto.
    + constructor; eauto.
      * inv H13. split. auto. eapply Mem.unchanged_on_implies; eauto.
        intros. apply loc_unmapped_dom; eauto.
      * rewrite <- (meminj_dom_compose f).
        rauto.
      * red. intros b1 b4 d f14 INJ. unfold compose_meminj in INJ.
        destruct (f12 b1) as [[b2 d1]|] eqn: INJ1; try congruence.
        destruct (f34 b2) as [[b3 d3]|] eqn: INJ3; try congruence. inv INJ.
        exploit H16; eauto. unfold meminj_dom. rewrite f14. auto.
        intros [A B].
        exploit H23. 2: eauto. inversion Hm14. apply mi_freeblocks; eauto.
        intros [E F]. split; eauto.
    + rewrite compose_meminj_id_left.
      repeat rstep; eauto.
Qed.
*)
