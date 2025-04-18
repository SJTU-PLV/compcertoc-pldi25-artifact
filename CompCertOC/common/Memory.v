(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Sandrine Blazy, ENSIIE and INRIA Paris-Rocquencourt        *)
(*          with contributions from Andrew Appel, Rob Dockins,         *)
(*          and Gordon Stewart (Princeton University)                  *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** This file develops the memory model that is used in the dynamic
  semantics of all the languages used in the compiler.
  It defines a type [mem] of memory states, the following 4 basic
  operations over memory states, and their properties:
- [load]: read a memory chunk at a given address;
- [store]: store a memory chunk at a given address;
- [alloc]: allocate a fresh memory block;
- [free]: invalidate a memory block.
*)

Require Import Zwf.
Require Import Axioms.
Require Import Classical. (* for mix; could avoid *)
Require Import Coqlib.
Require Intv.
Require Import Maps.
Require Archi.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Export Memdata.
Require Export Memtype.

(* To avoid useless definitions of inductors in extracted code. *)
Local Unset Elimination Schemes.
Local Unset Case Analysis Schemes.

Module NMap.
  Definition elt := block.
  Definition elt_eq := eq_block.
  Definition t (A: Type) := block -> A.
  Definition init (A: Type) (v: A) := fun (_: block) => v.
  Definition get (A: Type) (x: block) (m: t A) := m x.
  Definition set (A: Type) (x: block) (v: A) (m: t A) :=
    fun (y: block) => if eq_block y x then v else m y.

  Lemma gi:
    forall (A: Type) (i: elt) (x: A), (init A x) i = x.
Proof.
    intros. reflexivity.
Qed.
  Lemma gss:
    forall (A: Type) (i: elt) (x: A) (m: t A), (set A i x m) i = x.
Proof.
    intros. unfold set. case (eq_block i i); intro.
    reflexivity. tauto.
Qed.
  Lemma gso:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    i <> j -> (set A j x m) i = m i.
Proof.
    intros. unfold set. case (eq_block i j); intro.
    congruence. reflexivity.
Qed.
  Lemma gsspec:
    forall (A: Type) (i j: elt) (x: A) (m: t A),
    get A i (set A j x m) = if elt_eq i j then x else get A i m.
Proof.
    intros. unfold get, set, elt_eq. reflexivity.
Qed.
  Lemma gsident:
    forall (A: Type) (i j: elt) (m: t A), get A j (set A  i (get A i m) m) = get A j m.
Proof.
    intros. unfold get, set. case (eq_block j i); intro.
    congruence. reflexivity.
Qed.
  Definition map (A B: Type) (f: A -> B) (m: t A) :=
    fun (x: block) => f(m x).
  Lemma gmap:
    forall (A B: Type) (f: A -> B) (i: elt) (m: t A),
     get B i (map A B f m ) = f(get A i m).
  Proof.
    intros. unfold get, map. reflexivity.
  Qed.
  Lemma set2:
    forall (A: Type) (i: elt) (x y: A) (m: t A),
      set A i y (set A i x m) = set A i y m.
  Proof.
    intros. apply extensionality.
    intros. unfold set. case (eq_block x0 i); auto.
  Qed.

  Lemma set3:
    forall (A:Type) (i:elt) (m: t A),
      m = set A i (m i) m.
  Proof.
    intros. apply extensionality.
    intros. unfold set. case (eq_block x i); auto.
    intro. subst. auto.
  Qed.
End NMap.


(* Declare Module Sup: SUP. *)

Module Sup <: SUP.

  (* thread_destroy may be burdensome, use PMap? or
     a fixed size of threads, like 100 threads, use bool flags to indicate liveness *)
Record sup' : Type :=
  mksup
    {
      stacks : list (list positive);
      tid : nat;
      
      tid_valid: (0 < tid < (length stacks))%nat;
    }.

Definition sup := sup'.

Definition next_tid (s:sup) := length (stacks s).

Program Definition sup_empty : sup :=
  mksup (nil :: nil :: nil) (1%nat) _.

(*
Inductive sup_In' : block -> sup -> Prop :=
|sup_in_intro : forall (tid:nat) pos s pl,
    nth_error (stacks s) tid = Some pl ->
    In pos pl ->
    sup_In' (tid,pos) s.
*)
Inductive stacks_In : block -> list (list positive) -> Prop :=
|stacksin : forall tid pos pl st,
    nth_error st tid = Some pl ->
    In pos pl ->
    stacks_In (tid,pos) st.


Definition sup_In (b:block) (s:sup) := stacks_In b (stacks s).

Definition empty_in: forall b, ~ sup_In b sup_empty.
Proof.
  intros. intro. inv H.
  simpl in H0. destruct tid0; inv H0. inv H1.
  destruct tid0; inv H2. inv H1. destruct tid0; inv H0.
Qed.

Definition sup_dec : forall b s, {sup_In b s}+{~sup_In b s}.
Proof.
  intros. destruct b as [tid pos].
  destruct (le_lt_dec (length (stacks s)) tid).
  - right. intro. inv H.
    apply nth_error_None in l. congruence.
  - destruct (nth_error (stacks s) tid) eqn:NTH.
    + 
      destruct (in_dec peq pos l0).
      -- left. econstructor; eauto.
      -- right. intro. inv H. rewrite NTH in H2. inv H2. congruence.
    + exfalso. apply nth_error_Some in l. congruence.
Qed.

Fixpoint find_max_pos (l: list positive) : positive :=
  match l with
  |nil => 1
  |hd::tl => let m' := find_max_pos tl in
             match plt hd m' with
             |left _ => m'
             |right _ => hd
             end
  end.

Theorem Lessthan: forall p l, In p l -> Ple p (find_max_pos l).
Proof.
  intros.
  induction l.
  destruct H.
  destruct H;simpl.
  - destruct (plt a (find_max_pos l)); subst a.
    + apply Plt_Ple. assumption.
    + apply Ple_refl.
  - destruct (plt a (find_max_pos l)); apply IHl in H.
    + auto.
    + eapply Ple_trans. eauto.  apply Pos.le_nlt. apply n.
Qed.

Definition fresh_pos (pl : list positive) := Pos.succ (find_max_pos pl).
Lemma freshness_pos : forall pl, ~ In (fresh_pos pl) pl.
Proof.
  intros. unfold fresh_pos.
  intro.
  apply Lessthan in H.
  assert (Plt (find_max_pos pl) (Pos.succ (find_max_pos pl))). apply Plt_succ.
  assert (Plt (find_max_pos pl) (find_max_pos pl)). eapply Plt_Ple_trans. eauto. auto.
  apply Plt_strict in H1.
  auto.
Qed.

(* This will result in a opaque fresh_block *)
(*
Program Definition fresh_block (s:sup) : block.
Proof.
  destruct s as [stacks tid].
  destruct (nth_error stacks tid) as [pl|] eqn:NTH.
  exact (tid, fresh_pos pl).
  apply nth_error_None in NTH. extlia.
Qed.
 *)

Definition fresh_block (s : sup) : block :=
  let pl := nth (tid s) (stacks s) nil in
  ((tid s), fresh_pos pl).

Theorem freshness : forall s, ~sup_In (fresh_block s) s.
Proof.
  intros. destruct s as [stacks tid].
  intro. inv H. simpl in H2.
  erewrite nth_error_nth in H4; eauto.
  apply freshness_pos in H4. eauto.
Qed.

Fixpoint update_list {A: Type} (n: nat) (l: list A) (a : A):=
  match n,l with
  | O, hd :: tl => a :: tl
  | S n' , hd :: tl => hd :: (update_list n' tl a)
  | _, list => list
  end.

Lemma update_list_length : forall {A:Type} n l (a:A),
    length (update_list n l a) = length l.
Proof.
  induction n; induction l; intros; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - erewrite IHn; eauto.
Qed.

Program Definition sup_incr(s:sup) :=
  let tid := tid s in let stacks := stacks s in
  let pl := nth tid stacks nil in
  mksup (update_list tid stacks ((fresh_pos pl) :: pl)) tid _.
Next Obligation.
  rewrite update_list_length. destruct s. auto.
Qed.

(** increase for different threads *)

Definition fresh_block_tid (s : sup) (tid : nat) :=
  let pl := nth tid (stacks s) nil in (tid, fresh_pos pl).

Program Definition sup_incr_tid (s: sup) (t : nat) :=
  let pl := nth t (stacks s) nil in
  mksup (update_list t (stacks s) (fresh_pos pl :: pl)) (tid s) _.
Next Obligation.
  rewrite update_list_length. destruct s. auto.
Qed.

Definition valid_t_sup (s: sup) (tid : nat) := (0 <= tid < length (stacks s))%nat.

Definition sup_include(s1 s2:sup) := forall b, sup_In b s1 -> sup_In b s2.

(** proof of sup_include_dec *)

Program Definition sup_tl (s : sup) : sup :=
  match (tid s) with
  |O | (S O) => s
  |_ =>
     mksup (tl (stacks s)) (tid s -1) _
  end.
Next Obligation.
  generalize (tid_valid s).
  intros. destruct (stacks s); simpl in *.
  - extlia.
  - destruct (tid s); simpl in *. extlia.
    destruct n; simpl in *. extlia. lia.
Qed.


Lemma incl_dec : forall (l1 l2: list positive), {incl l1 l2} + {~ incl l1 l2}.
Proof.
  induction l1. left. unfold incl. intro. intro. inv H.
  intro l2. destruct (In_dec peq a l2).
  - destruct (IHl1 l2).
    + left. intro. intros. inv H; auto.
    + right. intro. apply n. intro. intro. apply H. right. auto.
  - right. intro. apply n. apply H. left. auto.
Qed.

Definition stacks_include (st1 st2: list (list positive)) : Prop :=
  forall b, stacks_In b st1 -> stacks_In b st2.

Lemma stacks_include_dec' : forall n st1 st2, length st1 = n ->
                                         {stacks_include st1 st2} + { ~stacks_include st1 st2}.
Proof.
  induction n.
  - intros. left. red. intros. inv H0. unfold next_tid in H.
    destruct (st1). destruct tid0. inv H1. inv H1. inv H.
  - intros. destruct st1. inv H. destruct st2.
    + (*st2 is empty*)
      destruct l; simpl in *.
      -- 
     (*the first list, i.e. global blocks, is empty*)
        edestruct (IHn st1 nil). lia.
        ++ 
          left. red. intros. red in s. inv H0. destruct tid0.
          inv H1. inv H2. simpl in H1.
          exploit s. econstructor; eauto. intros. inv H0.
          destruct tid0; inv H5.
        ++ right. intro. apply n0.
           red. intros. red in H0.
           inv H1. exploit H0. econstructor. instantiate (2:= S tid0).
           simpl. eauto. eauto. intros.
           inv H1. inv H6.
      --  (*the first list is not empty*)
        right. intro. red in H0. exploit H0.
        instantiate (1:= (O,p)). econstructor; simpl; eauto.
        left. auto. intros. inv H1. inv H4.
    + (*st2 is not empty*)
      simpl in *.
      destruct (incl_dec l l0).
      -- (*the global list is included *)
        destruct (IHn st1 st2). lia.
        ++ left.
           red. intros. inv H0. destruct tid0; simpl in *.
           inv H1. econstructor; simpl; eauto.
           exploit s. econstructor; eauto. intros.
           inv H0.
           econstructor; simpl; eauto.
        ++ right.
           intro. apply n0. red. intros. inv H1.
           exploit H0. econstructor; eauto. instantiate (1:= S tid0).
           simpl. eauto.
           intros. inv H1. simpl in H6. econstructor; eauto.
      -- right. intro. apply n0.
         red. intros. exploit H0. instantiate (1:= (O,a)).
         econstructor; simpl; eauto. intro. inv H2.
         simpl in H5. inv H5. auto.
Qed.
                                                              
Theorem sup_include_dec' :
  forall s1 s2,
    {sup_include s1 s2} + {~sup_include s1 s2}.
Proof.
  intros.
  destruct (stacks_include_dec' (length (stacks s1)) (stacks s1) (stacks s2)).
  reflexivity.
  left. red. intros. apply s. auto.
  right. red. intros. apply n. red. intros. apply H. auto.
Qed.


Theorem sup_include_dec : forall s1 s2, {sup_include s1 s2} + {~sup_include s1 s2}.
Proof.
  intros. eapply sup_include_dec'; eauto.
Qed.


(* proof sup_incr_in *)

Lemma nth_error_update_list_diff {A: Type}: forall (l : list A) id1 id2 a,
    (id1 < length l)%nat ->
    id1 <> id2 ->
    nth_error (update_list id1 l a) id2 =
    nth_error l id2.
Proof.
  induction l; intros; simpl in *.
  - extlia.
  - destruct id2; simpl.
    +  destruct id1; simpl. extlia. auto.
    + destruct id1; simpl. auto. apply IHl; lia.
Qed.

Lemma nth_error_update_list_same {A: Type}: forall (l : list A) id a,
   (id < length l)%nat ->
   nth_error (update_list id l a) id = Some a.
Proof.
  induction l; intros.
  - simpl in H. extlia.
  - destruct id. simpl; eauto.
    simpl. eapply IHl. simpl in H. lia.
Qed.

Theorem sup_incr_in : forall b s, sup_In b (sup_incr s) <-> b = (fresh_block s) \/ sup_In b s.
Proof.
  intros. split.
  - destruct s. unfold sup_In, sup_incr. simpl.
  intros. inv H. simpl in *. unfold fresh_block.
  simpl.
  destruct (Nat.eq_dec tid1 tid0).
    + subst.
      rewrite nth_error_update_list_same in H0; eauto. inv H0. destruct H1.
      left. subst. reflexivity.
      right. econstructor; eauto. simpl.
      erewrite nth_error_nth'; eauto. lia.
      lia.
    + right. econstructor. simpl.
      erewrite <- nth_error_update_list_diff; eauto. lia. auto.
  - intros. destruct H.
    destruct s. simpl in *. unfold sup_incr. simpl.
    unfold fresh_block in H. simpl in *. subst.
    econstructor; simpl; eauto.
    apply nth_error_update_list_same; eauto. lia.
    left. auto.
    destruct s. unfold sup_incr. inv H. simpl.
    destruct (Nat.eq_dec tid1 tid0).
    subst.
    econstructor; simpl.
    rewrite nth_error_update_list_same; eauto. lia. simpl in H0.
    erewrite nth_error_nth; eauto.
    right. auto.
    econstructor; simpl in *; eauto.
    erewrite nth_error_update_list_diff; eauto. lia.
Qed.

Theorem sup_incr_in1 : forall s, sup_In (fresh_block s) (sup_incr s).
Proof. intros. apply sup_incr_in. left. auto. Qed.
Theorem sup_incr_in2 : forall s, sup_include s (sup_incr s).
Proof. intros. intro. intro. apply sup_incr_in. right. auto. Qed.

Theorem sup_incr_tid_in : forall b s t,
    valid_t_sup s t ->
    sup_In b (sup_incr_tid s t) <-> b = (fresh_block_tid s t) \/ sup_In b s.
Proof.
  intros b s t Hv. red in Hv. split.
  - destruct s. unfold sup_In, sup_incr_tid. simpl.
  intros. inv H. simpl in *. unfold fresh_block_tid.
  simpl.
  destruct (Nat.eq_dec t tid1).
    + subst.
      rewrite nth_error_update_list_same in H0; eauto. inv H0. destruct H1.
      left. subst. reflexivity.
      right. econstructor; eauto. simpl.
      erewrite nth_error_nth'; eauto.
      lia.
      lia.
    + right. econstructor. simpl.
      erewrite <- nth_error_update_list_diff; eauto. lia. auto.
  - intros. destruct H.
    destruct s. simpl in *. unfold sup_incr_tid. simpl.
    unfold fresh_block_tid in H. simpl in *. subst.
    econstructor; simpl; eauto.
    apply nth_error_update_list_same; eauto. lia.
    left. auto.
    destruct s. unfold sup_incr_tid. inv H. simpl.
    destruct (Nat.eq_dec t tid1).
    subst.
    econstructor; simpl.
    rewrite nth_error_update_list_same; eauto. simpl in Hv. lia. simpl in H0.
    erewrite nth_error_nth; eauto.
    right. auto.
    econstructor; simpl in *; eauto.
    erewrite nth_error_update_list_diff; eauto. lia.
Qed.

Theorem sup_incr_tid_in1 : forall s t, valid_t_sup s t -> sup_In (fresh_block_tid s t) (sup_incr_tid s t).
Proof. intros. apply sup_incr_tid_in; auto. Qed.
Theorem sup_incr_tid_in2 : forall s t, valid_t_sup s t -> sup_include s (sup_incr_tid s t).
Proof. intros. intro. intro. apply sup_incr_tid_in; auto. Qed.

Theorem freshness_tid : forall s t, ~sup_In (fresh_block_tid s t) s.
Proof.
  intros. destruct s as [stacks tid].
  intro. inv H. simpl in H2.
  erewrite nth_error_nth in H4; eauto.
  apply freshness_pos in H4. eauto.
Qed.

Lemma sup_include_refl : forall s:sup, sup_include s s.
Proof. intro. intro. auto. Qed.

Lemma sup_include_trans:
  forall p q r:sup,sup_include p q-> sup_include q r -> sup_include p r.
Proof.
  intros. intro. intro.  auto.
Qed.

Lemma sup_include_incr:
  forall s, sup_include s (sup_incr s).
Proof.
  intros. apply sup_incr_in2.
Qed.


(* for iteration of all valid blocks *)

Fixpoint concat_stacks (stacks: list (list positive)) (tid: nat) : list block :=
  match stacks with
  | nil => nil
  | hd :: tl => (map (fun pos => (tid, pos)) hd) ++ (concat_stacks tl (tid + 1))
  end.

Definition sup_list (s:sup) : list block := concat_stacks (stacks s) O.


Lemma concat_stacks_incr : forall st n p m,
    In (n,p) (concat_stacks st m) ->
    In (S n,p) (concat_stacks st (S m)).
Proof.
  induction st; intros.
  - inv H.
  - simpl in *. 
    apply in_or_app.
    apply in_app_or in H.
    destruct H.
    left. apply in_map_iff. apply in_map_iff in H.
    destruct H as [x [A B]]. exists x. split; auto. congruence.
    right. apply IHst; auto.
Qed.

Lemma concat_stacks_dec : forall st b m,
    In b (concat_stacks st (S m)) ->
    exists n p, b = (S n, p) /\ In (n,p) (concat_stacks st m).
Proof.
  induction st; intros.
  - inv H.
  - simpl in *. 
    apply in_app_or in H.
    destruct H.
    + destruct b. destruct n. exfalso.
      apply in_map_iff in H. destruct H as [x [A B]]. inv A.
      exists n, p. split. auto. apply in_or_app. left.
      apply in_map_iff. apply in_map_iff in H.
      destruct H as [x [A B]]. exists x. split; eauto. congruence.
    + exploit IHst; eauto.
      intros [n [p [A B]]].
      exists n,p. split. congruence.
      apply in_or_app. right. auto.
Qed.

Lemma stacks_list_in : forall st b, stacks_In b st <-> In b (concat_stacks st 0).
Proof.
  induction st.
  - intros. split; intro H; inv H. destruct tid0; inv H0.
  - intros. split; intro H.
    + inv H. destruct tid0; simpl in *. inv H0.
      apply in_or_app. left.
      rewrite in_map_iff. exists pos. split; auto.
      apply in_or_app. right.
      assert (stacks_In (tid0, pos) st). econstructor;eauto.
      apply IHst in H. apply concat_stacks_incr. auto.
    + simpl in H.
      apply in_app_or in H. destruct H.
      rewrite in_map_iff in H. destruct H as [pos [A B]]. subst b.
      econstructor; eauto. simpl. reflexivity.
      apply concat_stacks_dec in H. destruct H as [n [p [A B]]].
      subst b. 
      apply IHst in B. inv B.
      econstructor; simpl; eauto.
Qed.
      
Lemma sup_list_in : forall b s, sup_In b s <-> In b (sup_list s).
Proof.
  intros. apply stacks_list_in.
Qed.

Definition range_prop (t: nat) (s : sup) :=
  (1 <= t < next_tid s)%nat.

Program Definition sup_yield (s: sup)(n:nat) (p: range_prop n s) :=
  mksup (stacks s) n _.

Lemma sup_yield_in : forall b s n p,
    sup_In b s <-> sup_In b (sup_yield s n p).
Proof.
  intros. unfold sup_In. split; intro.
  inv H. econstructor; eauto.
  inv H. econstructor; eauto.
Qed.
  
Program Definition sup_create (s: sup) :=
  mksup ((stacks s) ++ (nil :: nil)) (tid s) _.
Next Obligation.
  generalize (tid_valid s).
  intro.
  rewrite app_length. simpl. lia.
Qed.

Lemma sup_create_in : forall b s,
    sup_In b s <-> sup_In b (sup_create s).
Proof.
  intros. split; intro. 
  inv H. econstructor; eauto. unfold sup_create. simpl.
  rewrite nth_error_app1. eauto.
  apply nth_error_Some. congruence.
  inv H. simpl in H0.
  destruct (Nat.eq_dec tid0 (length (stacks s))).
  - rewrite nth_error_app2 in H0. 2: lia. subst. simpl in H0.
    rewrite Nat.sub_diag in H0. simpl in H0. inv H0. inv H1.
  - econstructor; eauto.
    rewrite nth_error_app1 in H0. eauto.
    assert (tid0 < length (stacks s ++ nil :: nil))%nat.
    apply nth_error_Some. congruence. rewrite app_length in H. simpl in H.
    lia.
Qed.

Definition match_sup (s1 s2: sup) :=
  length (stacks s1) = length (stacks s2) /\ tid s1 = tid s2.

Lemma match_sup_refl : forall s, match_sup s s.
Proof. intros. red. auto. Qed.

Lemma match_sup_trans : forall s1 s2 s3, match_sup s1 s2 -> match_sup s2 s3 -> match_sup s1 s3.
Proof. intros. destruct H, H0. red. split; congruence. Qed.

Lemma match_sup_symm : forall s1 s2, match_sup s1 s2 -> match_sup s2 s1.
Proof. intros. red in H. red. destruct H. eauto. Qed.

End Sup.

Module Mem <: MEM.
Include Sup.
Local Notation "a # b" := (NMap.get _ b a) (at level 1).
Local Notation "a ## b" := (ZMap.get b a) (at level 1).

Definition perm_order' (po: option permission) (p: permission) :=
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Definition perm_order'' (po1 po2: option permission) :=
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
 end.

Definition memperm : Type := perm_kind -> option permission.


Record mem' : Type := mkmem {
  mem_contents: NMap.t (ZMap.t memval);  (**r [block -> offset -> memval] *)
  mem_access: NMap.t (ZMap.t memperm);
                                         (**r [block -> offset -> kind -> option permission] *)
  support: sup;

  access_max:
    forall b ofs, perm_order'' (mem_access#b##ofs Max) (mem_access#b ## ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(sup_In b support) -> mem_access#b##ofs k = None;
  contents_default:
    forall b, fst (mem_contents#b) = Undef;
  access_default:
    forall b, fst (mem_access#b) = fun p => None
}.

Definition mem := mem'.

Definition nextblock (m:mem) := fresh_block (support m).

Lemma mksup_ext:
  forall stack1 stack2 tid1 tid2 a1 a2,
    stack1 = stack2 -> tid1 = tid2 ->
    Mem.mksup stack1 tid1 a1 = Mem.mksup stack2 tid2 a2.
Proof.
  intros. subst. f_equal; apply Axioms.proof_irr.
Qed.
   
Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 sup1 sup2 a1 a2 b1 b2 c1 c2 d1 d2,
  cont1=cont2 -> acc1=acc2 -> sup1=sup2 ->
  mkmem cont1 acc1 sup1 a1 b1 c1 d1= mkmem cont2 acc2 sup2 a2 b2 c2 d2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

(** * Validity of blocks and accesses *)

(** A block address is valid if it was previously allocated. It remains valid
  even after being freed. *)

Definition valid_block (m: mem) (b: block) := sup_In b (support m).

Theorem valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.
Proof.
  intros; red; intros. subst b'. contradiction.
Qed.

Local Hint Resolve valid_not_valid_diff: mem.

(** Permissions *)

Definition perm (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission) : Prop :=
   perm_order' (m.(mem_access)#b ##ofs k) p.

Theorem perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.
Proof.
  unfold perm, perm_order'; intros.
  destruct (m.(mem_access)#b## ofs k); auto.
  eapply perm_order_trans; eauto.
Qed.

Local Hint Resolve perm_implies: mem.

Theorem perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Proof.
  assert (forall po1 po2 p,
          perm_order' po2 p -> perm_order'' po1 po2 -> perm_order' po1 p).
  unfold perm_order', perm_order''. intros.
  destruct po2; try contradiction.
  destruct po1; try contradiction.
  eapply perm_order_trans; eauto.
  unfold perm; intros.
  generalize (access_max m b ofs). eauto.
Qed.

Theorem perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Theorem perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.
Proof.
  intros. destruct k; auto. apply perm_cur_max. auto.
Qed.

Local Hint Resolve perm_cur perm_max: mem.

Theorem perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.
Proof.
  unfold perm; intros.
  destruct (sup_dec b m.(support)).
  auto.
  assert (m.(mem_access)#b## ofs k = None).
  eapply nextblock_noaccess; eauto.
  rewrite H0 in H.
  contradiction.
Qed.

Local Hint Resolve perm_valid_block: mem.

Remark perm_order_dec:
  forall p1 p2, {perm_order p1 p2} + {~perm_order p1 p2}.
Proof.
  intros. destruct p1; destruct p2; (left; constructor) || (right; intro PO; inversion PO).
Defined.

Remark perm_order'_dec:
  forall op p, {perm_order' op p} + {~perm_order' op p}.
Proof.
  intros. destruct op; unfold perm_order'.
  apply perm_order_dec.
  right; tauto.
Defined.

Theorem perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
Proof.
  unfold perm; intros.
  apply perm_order'_dec.
Defined.

Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Theorem range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_cur:
  forall m b lo hi k p,
  range_perm m b lo hi Cur p -> range_perm m b lo hi k p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Theorem range_perm_max:
  forall m b lo hi k p,
  range_perm m b lo hi k p -> range_perm m b lo hi Max p.
Proof.
  unfold range_perm; intros; eauto with mem.
Qed.

Local Hint Resolve range_perm_implies range_perm_cur range_perm_max: mem.

Lemma range_perm_dec:
  forall m b lo hi k p, {range_perm m b lo hi k p} + {~ range_perm m b lo hi k p}.
Proof.
  intros.
  induction lo using (well_founded_induction_type (Zwf_up_well_founded hi)).
  destruct (zlt lo hi).
  destruct (perm_dec m b lo k p).
  destruct (H (lo + 1)). red. lia.
  left; red; intros. destruct (zeq lo ofs). congruence. apply r. lia.
  right; red; intros. elim n. red; intros; apply H0; lia.
  right; red; intros. elim n. apply H0. lia.
  left; red; intros. extlia.
Defined.

(** [valid_access m chunk b ofs p] holds if a memory access
    of the given chunk is possible in [m] at address [b, ofs]
    with current permissions [p].
    This means:
- The range of bytes accessed all have current permission [p].
- The offset [ofs] is aligned.
*)

Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

Theorem valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.
Proof.
  intros. inv H. constructor; eauto with mem.
Qed.

Theorem valid_access_freeable_any:
  forall m chunk b ofs p,
  valid_access m chunk b ofs Freeable ->
  valid_access m chunk b ofs p.
Proof.
  intros.
  eapply valid_access_implies; eauto. constructor.
Qed.

Local Hint Resolve valid_access_implies: mem.

Theorem valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.
Proof.
  intros. destruct H.
  assert (perm m b ofs Cur Nonempty).
    apply H. generalize (size_chunk_pos chunk). lia.
  eauto with mem.
Qed.

Local Hint Resolve valid_access_valid_block: mem.

Lemma valid_access_perm:
  forall m chunk b ofs k p,
  valid_access m chunk b ofs p ->
  perm m b ofs k p.
Proof.
  intros. destruct H. apply perm_cur. apply H. generalize (size_chunk_pos chunk). lia.
Qed.

Lemma valid_access_compat:
  forall m chunk1 chunk2 b ofs p,
  size_chunk chunk1 = size_chunk chunk2 ->
  align_chunk chunk2 <= align_chunk chunk1 ->
  valid_access m chunk1 b ofs p->
  valid_access m chunk2 b ofs p.
Proof.
  intros. inv H1. rewrite H in H2. constructor; auto.
  eapply Z.divide_trans; eauto. eapply align_le_divides; eauto.
Qed.

Lemma valid_access_dec:
  forall m chunk b ofs p,
  {valid_access m chunk b ofs p} + {~ valid_access m chunk b ofs p}.
Proof.
  intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur p).
  destruct (Zdivide_dec (align_chunk chunk) ofs).
  left; constructor; auto.
  right; red; intro V; inv V; contradiction.
  right; red; intro V; inv V; contradiction.
Defined.

(** [valid_pointer m b ofs] returns [true] if the address [b, ofs]
  is nonempty in [m] and [false] if it is empty. *)
Definition valid_pointer (m: mem) (b: block) (ofs: Z): bool :=
  perm_dec m b ofs Cur Nonempty.

Theorem valid_pointer_nonempty_perm:
  forall m b ofs,
  valid_pointer m b ofs = true <-> perm m b ofs Cur Nonempty.
Proof.
  intros. unfold valid_pointer.
  destruct (perm_dec m b ofs Cur Nonempty); simpl;
  intuition congruence.
Qed.

Theorem valid_pointer_valid_access:
  forall m b ofs,
  valid_pointer m b ofs = true <-> valid_access m Mint8unsigned b ofs Nonempty.
Proof.
  intros. rewrite valid_pointer_nonempty_perm.
  split; intros.
  split. simpl; red; intros. replace ofs0 with ofs by lia. auto.
  simpl. apply Z.divide_1_l.
  destruct H. apply H. simpl. lia.
Qed.

(** C allows pointers one past the last element of an array.  These are not
  valid according to the previously defined [valid_pointer]. The property
  [weak_valid_pointer m b ofs] holds if address [b, ofs] is a valid pointer
  in [m], or a pointer one past a valid block in [m].  *)

Definition weak_valid_pointer (m: mem) (b: block) (ofs: Z) :=
  valid_pointer m b ofs || valid_pointer m b (ofs - 1).

Lemma weak_valid_pointer_spec:
  forall m b ofs,
  weak_valid_pointer m b ofs = true <->
    valid_pointer m b ofs = true \/ valid_pointer m b (ofs - 1) = true.
Proof.
  intros. unfold weak_valid_pointer. now rewrite orb_true_iff.
Qed.
Lemma valid_pointer_implies:
  forall m b ofs,
  valid_pointer m b ofs = true -> weak_valid_pointer m b ofs = true.
Proof.
  intros. apply weak_valid_pointer_spec. auto.
Qed.

(** * Operations over memory stores *)

(** The initial store *)

Program Definition empty: mem :=
  mkmem (NMap.init _ (ZMap.init Undef))
        (NMap.init _ (ZMap.init (fun k => None)))
        sup_empty  _ _ _ _.

(** Allocation of a fresh block with the given bounds.  Return an updated
  memory state and the address of the fresh block, which initially contains
  undefined cells.  Note that allocation never fails: we model an
  infinite memory. *)
Lemma mem_incr_1: forall m, sup_In (nextblock m) (sup_incr (m.(support))).
Proof.
  intros. unfold nextblock. unfold sup_incr. apply sup_incr_in1.
Qed.

Lemma mem_incr_2: forall m b, sup_In b (m.(support)) -> sup_In b (sup_incr (m.(support))).
Proof.
  intros. unfold sup_incr. apply sup_incr_in2. auto.
Qed.

(** Writing N adjacent bytes in a block memperm. *)

Definition interval_length (lo: Z) (hi: Z) : nat :=
  if (lo <? hi) then Z.to_nat (hi - lo) else 0.

Fixpoint setpermN' (length: nat) (lo: Z) (p: option permission) (c: ZMap.t memperm): ZMap.t memperm :=
  match length with
    | O => c
    | S l => setpermN' l (lo + 1) p (ZMap.set lo (fun k => p) c)
  end.

Definition setpermN (lo: Z) (hi: Z) (p: option permission) (c: ZMap.t memperm): ZMap.t memperm :=
  setpermN' (interval_length lo hi) lo p c.

Remark setpermN'_other:
  forall length lo c p ofs,
  (forall ofs', lo <= ofs' < lo + (Z.of_nat length) -> ofs' <> ofs) ->
  ZMap.get ofs (setpermN' length lo p c) = ZMap.get ofs c.
Proof.
  induction length; intros; simpl.
  auto.
  rewrite Nat2Z.inj_succ in H.
  transitivity (ZMap.get ofs (ZMap.set lo (fun _ => p) c)).
  apply IHlength. intros. apply H. lia.
  apply ZMap.gso. apply not_eq_sym. apply H. lia.
Qed.

Remark setpermN_other:
  forall lo hi c p q,
  (forall r, lo <= r < hi -> r <> q) ->
  ZMap.get q (setpermN lo hi p c) = ZMap.get q c.
Proof.
  intros. eapply setpermN'_other; eauto.
  intros. unfold interval_length in H0.
  destruct (lo <? hi) eqn: Hlohi.
  apply Z.ltb_lt in Hlohi.
  - rewrite Z_to_nat_max in H0.
    rewrite Z.max_l in H0.
    apply H. lia. lia.
  - extlia.
Qed.

Remark setpermN_outside:
  forall lo hi c p q,
  q < lo \/ q >= hi ->
  ZMap.get q (setpermN lo hi p c) = ZMap.get q c.
Proof.
  intros. apply setpermN_other.
  intros. lia.
Qed.

Remark setpermN'_inside :
  forall length lo p c ofs,
    lo <= ofs < lo + (Z.of_nat length) ->
    ZMap.get ofs (setpermN' length lo p c) = (fun k => p).
Proof.
  induction length; simpl; intros. extlia.
  destruct (Z.eq_dec lo ofs).
  + subst.
    transitivity (ZMap.get ofs (ZMap.set ofs (fun _ => p) c)).
    rewrite setpermN'_other. auto.
    intros. extlia. rewrite ZMap.gss. auto.
  + rewrite IHlength. auto. lia.
Qed.

Remark setpermN_inside:
  forall lo hi c p q,
    (lo <= q < hi) ->
    ZMap.get q (setpermN lo hi p c) = (fun k => p).
Proof.
  intros. eapply setpermN'_inside; eauto.
  unfold interval_length. destruct (lo <? hi) eqn: Hlohi.
  - apply Z.ltb_lt in Hlohi. rewrite Z_to_nat_max.
    rewrite Z.max_l. lia. lia.
  - apply Z.ltb_ge in Hlohi. extlia.
Qed.

Remark setpermN_inv:
  forall lo hi c p ofs,
    ZMap.get ofs (setpermN lo hi p c) =
    if (zle lo ofs && zlt ofs hi) then (fun k => p) else
      ZMap.get ofs c.
Proof.
  intros.
  destruct (zle lo ofs); destruct (zlt ofs hi); simpl.
  rewrite setpermN_inside. auto. lia.
  rewrite setpermN_outside. auto. lia.
  rewrite setpermN_outside. auto. lia.
  rewrite setpermN_outside. auto. lia.
Qed.

Remark setpermN'_default :
  forall length lo p c,
    fst (setpermN' length lo p c) = fst c.
Proof.
  induction length; simpl; intros. auto. rewrite IHlength. auto.
Qed.

Remark setpermN_default:
  forall lo hi q c, fst (setpermN lo hi q c) = fst c.
Proof.
  intros.
  eapply setpermN'_default; eauto.
Qed.


Program Definition yield (m:mem) (n: nat) (p : range_prop n (Mem.support m)) :=
  mkmem m.(mem_contents) m.(mem_access) (sup_yield m.(support) n p) _ _ _ _.
Next Obligation.
  apply access_max.
Qed.
Next Obligation.
  apply nextblock_noaccess.
  rewrite <- sup_yield_in in H. auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply access_default.
Qed.

Program Definition thread_create (m:mem) :=
  ((mkmem m.(mem_contents) m.(mem_access) (sup_create m.(support)) _ _ _ _), next_tid m.(support)).
Next Obligation.
  apply access_max.
Qed.
Next Obligation.
  apply nextblock_noaccess.
  rewrite <- sup_create_in in H. auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  apply access_default.
Qed.

Definition nextblock_global (m : mem) := fresh_block_tid (Mem.support m) O.

Program Definition alloc_global (m: mem) (lo hi: Z) :=
  (mkmem (NMap.set _ (nextblock_global m)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (NMap.set _ (nextblock_global m)
                   (setpermN lo hi (Some Freeable) (ZMap.init (fun k => None)))
                   m.(mem_access))
         (sup_incr_tid (m.(support)) O)
         _ _ _ _,
   (nextblock_global m)).
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock_global m)).
  subst b. rewrite setpermN_inv.
  destruct (zle lo ofs && zlt ofs hi). constructor.
  simpl. auto.
  apply access_max.
Qed.
Next Obligation.
  generalize (tid_valid (Mem.support m)). intro Htv.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock_global m)).
  subst b. elim H. apply sup_incr_tid_in1. red. lia.
  apply nextblock_noaccess. red; intros; elim H.
  apply sup_incr_tid_in2. red. lia. auto.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock_global m)). auto. apply contents_default.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock_global m)). auto.
  rewrite setpermN_default. auto. apply access_default.
Qed.

Program Definition alloc (m: mem) (lo hi: Z) :=
  (mkmem (NMap.set _ (nextblock m)
                   (ZMap.init Undef)
                   m.(mem_contents))
         (NMap.set _ (nextblock m)
                   (setpermN lo hi (Some Freeable) (ZMap.init (fun k => None)))
                   m.(mem_access))
         (sup_incr (m.(support)))
         _ _ _ _,
   (nextblock m)).
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)).
  subst b. rewrite setpermN_inv.
  destruct (zle lo ofs && zlt ofs hi). constructor.
  simpl. auto.
  apply access_max.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)).
  subst b. elim H. apply mem_incr_1.
  apply nextblock_noaccess. red; intros; elim H.
  apply mem_incr_2. auto.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)). auto. apply contents_default.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b (nextblock m)). auto.
  rewrite setpermN_default. auto. apply access_default.
Qed.

(** Freeing a block between the given bounds.
  Return the updated memory state where the given range of the given block
  has been invalidated: future reads and writes to this
  range will fail.  Requires freeable permission on the given range. *)

Program Definition unchecked_free (m: mem) (b: block) (lo hi: Z): mem :=
  mkmem m.(mem_contents)
        (NMap.set _ b
                (setpermN lo hi None (m.(mem_access)#b))
                m.(mem_access))
        m.(support) _ _ _ _.
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b).
  subst.
  rewrite setpermN_inv.
  destruct (zle lo ofs && zlt ofs hi). constructor.
  apply access_max.  apply access_max.
Qed.
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b). subst.
  destruct (Z_le_dec lo ofs); destruct (Z_lt_dec ofs hi).
  rewrite setpermN_inside. constructor. lia.
  rewrite setpermN_outside. apply nextblock_noaccess; auto. lia.
  rewrite setpermN_outside. apply nextblock_noaccess; auto. lia.
  rewrite setpermN_outside. apply nextblock_noaccess; auto. lia.
  apply nextblock_noaccess; auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b). subst.
  rewrite setpermN_default.
  apply access_default.
  apply access_default.
Qed.


Definition free (m: mem) (b: block) (lo hi: Z): option mem :=
  if range_perm_dec m b lo hi Cur Freeable
  then Some(unchecked_free m b lo hi)
  else None.

Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** Memory reads. *)

(** Reading N adjacent bytes in a block content. *)

Fixpoint getN {A:Type} (n: nat) (p: Z) (c: ZMap.t A) {struct n}: list A :=
  match n with
  | O => nil
  | S n' => ZMap.get p c :: getN n' (p + 1) c
  end.

(** [load chunk m b ofs] perform a read in memory state [m], at address
  [b] and offset [ofs].  It returns the value of the memory chunk
  at that address.  [None] is returned if the accessed bytes
  are not readable. *)

Definition load (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z): option val :=
  if valid_access_dec m chunk b ofs Readable
  then Some(decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)))
  else None.

(** [loadv chunk m addr] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end.

(** [loadbytes m b ofs n] reads [n] consecutive bytes starting at
  location [(b, ofs)].  Returns [None] if the accessed locations are
  not readable. *)

Definition loadbytes (m: mem) (b: block) (ofs n: Z): option (list memval) :=
  if range_perm_dec m b ofs (ofs + n) Cur Readable
  then Some (getN (Z.to_nat n) ofs (m.(mem_contents)#b))
  else None.

(** Memory stores. *)

(** Writing N adjacent bytes in a block content. *)

Fixpoint setN {A:Type} (vl: list A) (p: Z) (c: ZMap.t A) {struct vl}: ZMap.t A :=
  match vl with
  | nil => c
  | v :: vl' => setN vl' (p + 1) (ZMap.set p v c)
  end.

Remark setN_other:
  forall A vl (c: ZMap.t A) p q,
  (forall r, p <= r < p + Z.of_nat (length vl) -> r <> q) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  induction vl; intros; simpl.
  auto.
  simpl length in H. rewrite Nat2Z.inj_succ in H.
  transitivity (ZMap.get q (ZMap.set p a c)).
  apply IHvl. intros. apply H. lia.
  apply ZMap.gso. apply not_eq_sym. apply H. lia.
Qed.

Remark setN_outside:
  forall A vl (c: ZMap.t A) p q,
  q < p \/ q >= p + Z.of_nat (length vl) ->
  ZMap.get q (setN vl p c) = ZMap.get q c.
Proof.
  intros. apply setN_other.
  intros. lia.
Qed.

Remark getN_setN_same:
  forall A vl p (c: ZMap.t A),
  getN (length vl) p (setN vl p c) = vl.
Proof.
  induction vl; intros; simpl.
  auto.
  decEq.
  rewrite setN_outside. apply ZMap.gss. lia.
  apply IHvl.
Qed.

Remark getN_exten:
  forall A (c1 c2: ZMap.t A) n p,
  (forall i, p <= i < p + Z.of_nat n -> ZMap.get i c1 = ZMap.get i c2) ->
  getN n p c1 = getN n p c2.
Proof.
  induction n; intros. auto. rewrite Nat2Z.inj_succ in H. simpl. decEq.
  apply H. lia. apply IHn. intros. apply H. lia.
Qed.

Remark getN_setN_disjoint:
  forall A vl q (c: ZMap.t A) n p,
  Intv.disjoint (p, p + Z.of_nat n) (q, q + Z.of_nat (length vl)) ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_exten. intros. apply setN_other.
  intros; red; intros; subst r. eelim H; eauto.
Qed.

Remark getN_setN_outside:
  forall A vl q (c: ZMap.t A) n p,
  p + Z.of_nat n <= q \/ q + Z.of_nat (length vl) <= p ->
  getN n p (setN vl q c) = getN n p c.
Proof.
  intros. apply getN_setN_disjoint. apply Intv.disjoint_range. auto.
Qed.

Remark setN_default:
  forall (A:Type) vl q (c: ZMap.t A), fst (setN vl q c) = fst c.
Proof.
  induction vl; simpl; intros. auto. rewrite IHvl. auto.
Qed.

(** [store chunk m b ofs v] perform a write in memory state [m].
  Value [v] is stored at address [b] and offset [ofs].
  Return the updated memory store, or [None] if the accessed bytes
  are not writable. *)

Program Definition store (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val): option mem :=
  if valid_access_dec m chunk b ofs Writable then
    Some (mkmem (NMap.set _ b
                          (setN (encode_val chunk v) ofs (m.(mem_contents)#b))
                          m.(mem_contents))
                m.(mem_access)
                m.(support)
                _ _ _ _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation. apply access_default. Qed.

(** [storev chunk m addr v] is similar, but the address and offset are given
  as a single value [addr], which must be a pointer value. *)

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end.

Theorem support_storev: forall chunk m addr v m',
    storev chunk m addr v = Some m' -> support m = support m'.
Proof.
  intros.
  unfold storev in H.
  unfold store in H.
  destruct addr; try congruence.
  destruct (valid_access_dec m chunk b (Ptrofs.unsigned i) Writable).
  inv H.
  auto.
  congruence.
Qed.

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)

Program Definition storebytes (m: mem) (b: block) (ofs: Z) (bytes: list memval) : option mem :=
  if range_perm_dec m b ofs (ofs + Z.of_nat (length bytes)) Cur Writable then
    Some (mkmem
             (NMap.set _ b (setN bytes ofs (m.(mem_contents)#b)) m.(mem_contents))
             m.(mem_access)
             m.(support)
             _ _ _ _)
  else
    None.
Next Obligation. apply access_max. Qed.
Next Obligation. apply nextblock_noaccess; auto. Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Qed.
Next Obligation. apply access_default. Qed.

(** [drop_perm m b lo hi p] sets the max permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have current permissions
    [Freeable] in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Program Definition drop_perm (m: mem) (b: block) (lo hi: Z) (p: permission): option mem :=
  if range_perm_dec m b lo hi Cur Freeable then
    Some (mkmem m.(mem_contents)
                (NMap.set _ b
                        (setpermN lo hi (Some p) (mem_access m) # b)
                        m.(mem_access))
                m.(support) _ _ _ _)
  else None.
Next Obligation.
  repeat rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b). subst b0.
  rewrite setpermN_inv. destruct (zle lo ofs && zlt ofs hi).
  constructor. apply access_max. apply access_max.
Qed.
Next Obligation.
  specialize (nextblock_noaccess m b0 ofs k H0). intros.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b). subst b0.
  rewrite setpermN_inv.
  destruct (zle lo ofs); destruct (zlt ofs hi); simpl.
  assert (perm m b ofs k Freeable). apply perm_cur. apply H; auto.
  unfold perm in H2. rewrite H1 in H2. contradiction.
  auto. auto. auto. auto.
Qed.
Next Obligation.
  apply contents_default.
Qed.
Next Obligation.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b0 b). subst b0.
  rewrite setpermN_default.
  apply access_default. apply access_default.
Qed.

(** * Properties of the memory operations *)

(** Properties of the empty store. *)
Theorem support_empty : support empty = sup_empty.
Proof.
  reflexivity.
Qed.
Theorem perm_empty: forall b ofs k p, ~perm empty b ofs k p.
Proof.
  intros. unfold perm, empty; simpl. tauto.
Qed.

Theorem valid_access_empty: forall chunk b ofs p, ~valid_access empty chunk b ofs p.
Proof.
  intros. red; intros. elim (perm_empty b ofs Cur p). apply H.
  generalize (size_chunk_pos chunk); lia.
Qed.

(** ** Properties related to [load] *)

Theorem valid_access_load:
  forall m chunk b ofs,
  valid_access m chunk b ofs Readable ->
  exists v, load chunk m b ofs = Some v.
Proof.
  intros. econstructor. unfold load. rewrite pred_dec_true; eauto.
Qed.

Theorem load_valid_access:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  valid_access m chunk b ofs Readable.
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  auto.
  congruence.
Qed.

Lemma load_result:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  v = decode_val chunk (getN (size_chunk_nat chunk) ofs (m.(mem_contents)#b)).
Proof.
  intros until v. unfold load.
  destruct (valid_access_dec m chunk b ofs Readable); intros.
  congruence.
  congruence.
Qed.

Local Hint Resolve load_valid_access valid_access_load: mem.

Theorem load_type:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_type v (type_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_type.
Qed.

Theorem load_rettype:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  Val.has_rettype v (rettype_of_chunk chunk).
Proof.
  intros. exploit load_result; eauto; intros. rewrite H0.
  apply decode_val_rettype.
Qed.

Theorem load_cast:
  forall m chunk b ofs v,
  load chunk m b ofs = Some v ->
  match chunk with
  | Mint8signed => v = Val.sign_ext 8 v
  | Mint8unsigned => v = Val.zero_ext 8 v
  | Mint16signed => v = Val.sign_ext 16 v
  | Mint16unsigned => v = Val.zero_ext 16 v
  | _ => True
  end.
Proof.
  intros. exploit load_result; eauto.
  set (l := getN (size_chunk_nat chunk) ofs m.(mem_contents)#b).
  intros. subst v. apply decode_val_cast.
Qed.

Theorem load_int8_signed_unsigned:
  forall m b ofs,
  load Mint8signed m b ofs = option_map (Val.sign_ext 8) (load Mint8unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint8signed) with (size_chunk_nat Mint8unsigned).
  set (cl := getN (size_chunk_nat Mint8unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint8signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

Theorem load_int16_signed_unsigned:
  forall m b ofs,
  load Mint16signed m b ofs = option_map (Val.sign_ext 16) (load Mint16unsigned m b ofs).
Proof.
  intros. unfold load.
  change (size_chunk_nat Mint16signed) with (size_chunk_nat Mint16unsigned).
  set (cl := getN (size_chunk_nat Mint16unsigned) ofs m.(mem_contents)#b).
  destruct (valid_access_dec m Mint16signed b ofs Readable).
  rewrite pred_dec_true; auto. unfold decode_val.
  destruct (proj_bytes cl); auto.
  simpl. decEq. decEq. rewrite Int.sign_ext_zero_ext. auto. compute; auto.
  rewrite pred_dec_false; auto.
Qed.

(** ** Properties related to [loadbytes] *)

Theorem range_perm_loadbytes:
  forall m b ofs len,
  range_perm m b ofs (ofs + len) Cur Readable ->
  exists bytes, loadbytes m b ofs len = Some bytes.
Proof.
  intros. econstructor. unfold loadbytes. rewrite pred_dec_true; eauto.
Qed.

Theorem loadbytes_range_perm:
  forall m b ofs len bytes,
  loadbytes m b ofs len = Some bytes ->
  range_perm m b ofs (ofs + len) Cur Readable.
Proof.
  intros until bytes. unfold loadbytes.
  destruct (range_perm_dec m b ofs (ofs + len) Cur Readable). auto. congruence.
Qed.

Theorem loadbytes_load:
  forall chunk m b ofs bytes,
  loadbytes m b ofs (size_chunk chunk) = Some bytes ->
  (align_chunk chunk | ofs) ->
  load chunk m b ofs = Some(decode_val chunk bytes).
Proof.
  unfold loadbytes, load; intros.
  destruct (range_perm_dec m b ofs (ofs + size_chunk chunk) Cur Readable);
  try congruence.
  inv H. rewrite pred_dec_true. auto.
  split; auto.
Qed.

Theorem load_loadbytes:
  forall chunk m b ofs v,
  load chunk m b ofs = Some v ->
  exists bytes, loadbytes m b ofs (size_chunk chunk) = Some bytes
             /\ v = decode_val chunk bytes.
Proof.
  intros. exploit load_valid_access; eauto. intros [A B].
  exploit load_result; eauto. intros.
  exists (getN (size_chunk_nat chunk) ofs m.(mem_contents)#b); split.
  unfold loadbytes. rewrite pred_dec_true; auto.
  auto.
Qed.

Lemma getN_length:
  forall A (c: ZMap.t A) n p, length (getN n p c) = n.
Proof.
  induction n; simpl; intros. auto. decEq; auto.
Qed.

Theorem loadbytes_length:
  forall m b ofs n bytes,
  loadbytes m b ofs n = Some bytes ->
  length bytes = Z.to_nat n.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable); try congruence.
  inv H. apply getN_length.
Qed.

Theorem loadbytes_empty:
  forall m b ofs n,
  n <= 0 -> loadbytes m b ofs n = Some nil.
Proof.
  intros. unfold loadbytes. rewrite pred_dec_true. rewrite Z_to_nat_neg; auto.
  red; intros. extlia.
Qed.

Lemma getN_concat:
  forall A (c: ZMap.t A) n1 n2 p,
  getN (n1 + n2)%nat p c = getN n1 p c ++ getN n2 (p + Z.of_nat n1) c.
Proof.
  induction n1; intros.
  simpl. decEq. lia.
  rewrite Nat2Z.inj_succ. simpl. decEq.
  replace (p + Z.succ (Z.of_nat n1)) with ((p + 1) + Z.of_nat n1) by lia.
  auto.
Qed.

Theorem loadbytes_concat:
  forall m b ofs n1 n2 bytes1 bytes2,
  loadbytes m b ofs n1 = Some bytes1 ->
  loadbytes m b (ofs + n1) n2 = Some bytes2 ->
  n1 >= 0 -> n2 >= 0 ->
  loadbytes m b ofs (n1 + n2) = Some(bytes1 ++ bytes2).
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + n1) Cur Readable); try congruence.
  destruct (range_perm_dec m b (ofs + n1) (ofs + n1 + n2) Cur Readable); try congruence.
  rewrite pred_dec_true. rewrite Z2Nat.inj_add by lia.
  rewrite getN_concat. rewrite Z2Nat.id by lia.
  congruence.
  red; intros.
  assert (ofs0 < ofs + n1 \/ ofs0 >= ofs + n1) by lia.
  destruct H4. apply r; lia. apply r0; lia.
Qed.

Theorem loadbytes_split:
  forall m b ofs n1 n2 bytes,
  loadbytes m b ofs (n1 + n2) = Some bytes ->
  n1 >= 0 -> n2 >= 0 ->
  exists bytes1, exists bytes2,
     loadbytes m b ofs n1 = Some bytes1
  /\ loadbytes m b (ofs + n1) n2 = Some bytes2
  /\ bytes = bytes1 ++ bytes2.
Proof.
  unfold loadbytes; intros.
  destruct (range_perm_dec m b ofs (ofs + (n1 + n2)) Cur Readable);
  try congruence.
  rewrite Z2Nat.inj_add in H by lia. rewrite getN_concat in H.
  rewrite Z2Nat.id in H by lia.
  repeat rewrite pred_dec_true.
  econstructor; econstructor.
  split. reflexivity. split. reflexivity. congruence.
  red; intros; apply r; lia.
  red; intros; apply r; lia.
Qed.

Theorem load_rep:
 forall ch m1 m2 b ofs v1 v2,
  (forall z, 0 <= z < size_chunk ch -> ZMap.get (ofs + z) m1.(mem_contents)#b = ZMap.get (ofs + z) m2.(mem_contents)#b) ->
  load ch m1 b ofs = Some v1 ->
  load ch m2 b ofs = Some v2 ->
  v1 = v2.
Proof.
  intros.
  apply load_result in H0.
  apply load_result in H1.
  subst.
  f_equal.
  rewrite size_chunk_conv in H.
  remember (size_chunk_nat ch) as n; clear Heqn.
  revert ofs H; induction n; intros; simpl; auto.
  f_equal.
  rewrite Nat2Z.inj_succ in H.
  replace ofs with (ofs+0) by lia.
  apply H; lia.
  apply IHn.
  intros.
  rewrite <- Z.add_assoc.
  apply H.
  rewrite Nat2Z.inj_succ. lia.
Qed.

Theorem load_int64_split:
  forall m b ofs v,
  load Mint64 m b ofs = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     load Mint32 m b ofs = Some (if Archi.big_endian then v1 else v2)
  /\ load Mint32 m b (ofs + 4) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros.
  exploit load_valid_access; eauto. intros [A B]. simpl in *.
  exploit load_loadbytes. eexact H. simpl. intros [bytes [LB EQ]].
  change 8 with (4 + 4) in LB.
  exploit loadbytes_split. eexact LB. lia. lia.
  intros (bytes1 & bytes2 & LB1 & LB2 & APP).
  change 4 with (size_chunk Mint32) in LB1.
  exploit loadbytes_load. eexact LB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  intros L1.
  change 4 with (size_chunk Mint32) in LB2.
  exploit loadbytes_load. eexact LB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
  intros L2.
  exists (decode_val Mint32 (if Archi.big_endian then bytes1 else bytes2));
  exists (decode_val Mint32 (if Archi.big_endian then bytes2 else bytes1)).
  split. destruct Archi.big_endian; auto.
  split. destruct Archi.big_endian; auto.
  rewrite EQ. rewrite APP. apply decode_val_int64; auto.
  erewrite loadbytes_length; eauto. reflexivity.
  erewrite loadbytes_length; eauto. reflexivity.
Qed.

Lemma addressing_int64_split:
  forall i,
  Archi.ptr64 = false ->
  (8 | Ptrofs.unsigned i) ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4.
Proof.
  intros.
  rewrite Ptrofs.add_unsigned.
  replace (Ptrofs.unsigned (Ptrofs.of_int (Int.repr 4))) with (Int.unsigned (Int.repr 4))
    by (symmetry; apply Ptrofs.agree32_of_int; auto).
  change (Int.unsigned (Int.repr 4)) with 4.
  apply Ptrofs.unsigned_repr.
  exploit (Zdivide_interval (Ptrofs.unsigned i) Ptrofs.modulus 8).
  lia. apply Ptrofs.unsigned_range. auto.
  exists (two_p (Ptrofs.zwordsize - 3)).
  unfold Ptrofs.modulus, Ptrofs.zwordsize, Ptrofs.wordsize.
  unfold Wordsize_Ptrofs.wordsize. destruct Archi.ptr64; reflexivity.
  unfold Ptrofs.max_unsigned. lia.
Qed.

Theorem loadv_int64_split:
  forall m a v,
  loadv Mint64 m a = Some v -> Archi.ptr64 = false ->
  exists v1 v2,
     loadv Mint32 m a = Some (if Archi.big_endian then v1 else v2)
  /\ loadv Mint32 m (Val.add a (Vint (Int.repr 4))) = Some (if Archi.big_endian then v2 else v1)
  /\ Val.lessdef v (Val.longofwords v1 v2).
Proof.
  intros. destruct a; simpl in H; inv H.
  exploit load_int64_split; eauto. intros (v1 & v2 & L1 & L2 & EQ).
  unfold Val.add; rewrite H0.
  assert (NV: Ptrofs.unsigned (Ptrofs.add i (Ptrofs.of_int (Int.repr 4))) = Ptrofs.unsigned i + 4).
  { apply addressing_int64_split; auto.
    exploit load_valid_access. eexact H2. intros [P Q]. auto. }
  exists v1, v2.
Opaque Ptrofs.repr.
  split. auto.
  split. simpl. rewrite NV. auto.
  auto.
Qed.

(** ** Properties related to [store] *)

Theorem valid_access_store:
  forall m1 chunk b ofs v,
  valid_access m1 chunk b ofs Writable ->
  { m2: mem | store chunk m1 b ofs v = Some m2 }.
Proof.
  intros.
  unfold store.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  eauto.
  contradiction.
Defined.

Local Hint Resolve valid_access_store: mem.

Section STORE.
Variable chunk: memory_chunk.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable v: val.
Variable m2: mem.
Hypothesis STORE: store chunk m1 b ofs v = Some m2.

Lemma store_access: mem_access m2 = mem_access m1.
Proof.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Lemma store_mem_contents:
  mem_contents m2 = NMap.set _ b (setN (encode_val chunk v) ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem perm_store_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros.
 unfold perm in *. rewrite store_access; auto.
Qed.

Theorem perm_store_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *.  rewrite store_access in H; auto.
Qed.

Local Hint Resolve perm_store_1 perm_store_2: mem.

Theorem nextblock_store:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem support_store:
  support m2 = support m1.
Proof.
  intros.
  unfold store in STORE. destruct ( valid_access_dec m1 chunk b ofs Writable); inv STORE.
  auto.
Qed.

Theorem store_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite support_store; auto.
Qed.

Theorem store_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite support_store in H; auto.
Qed.

Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.

Theorem store_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem store_valid_access_3:
  valid_access m1 chunk b ofs Writable.
Proof.
  unfold store in STORE. destruct (valid_access_dec m1 chunk b ofs Writable).
  auto.
  congruence.
Qed.

Local Hint Resolve store_valid_access_1 store_valid_access_2 store_valid_access_3: mem.

Theorem load_store_similar:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  exists v', load chunk' m2 b ofs = Some v' /\ decode_encode_val v chunk chunk' v'.
Proof.
  intros.
  exploit (valid_access_load m2 chunk').
    eapply valid_access_compat. symmetry; eauto. auto. eauto with mem.
  intros [v' LOAD].
  exists v'; split; auto.
  exploit load_result; eauto. intros B.
  rewrite B. rewrite store_mem_contents; simpl.
  setoid_rewrite NMap.gss.
  replace (size_chunk_nat chunk') with (length (encode_val chunk v)).
  rewrite getN_setN_same. apply decode_encode_val_general.
  rewrite encode_val_length. repeat rewrite size_chunk_conv in H.
  apply Nat2Z.inj; auto.
Qed.

Theorem load_store_similar_2:
  forall chunk',
  size_chunk chunk' = size_chunk chunk ->
  align_chunk chunk' <= align_chunk chunk ->
  type_of_chunk chunk' = type_of_chunk chunk ->
  load chunk' m2 b ofs = Some (Val.load_result chunk' v).
Proof.
  intros. destruct (load_store_similar chunk') as [v' [A B]]; auto.
  rewrite A. decEq. eapply decode_encode_val_similar with (chunk1 := chunk); eauto.
Qed.

Theorem load_store_same:
  load chunk m2 b ofs = Some (Val.load_result chunk v).
Proof.
  apply load_store_similar_2; auto. lia.
Qed.

Theorem load_store_other:
  forall chunk' b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk' <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  load chunk' m2 b' ofs' = load chunk' m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk' b' ofs' Readable).
  rewrite pred_dec_true.
  decEq. decEq. rewrite store_mem_contents; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  apply getN_setN_outside. rewrite encode_val_length. repeat rewrite <- size_chunk_conv.
  intuition.
  auto.
  eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem loadbytes_store_same:
  loadbytes m2 b ofs (size_chunk chunk) = Some(encode_val chunk v).
Proof.
  intros.
  assert (valid_access m2 chunk b ofs Readable) by eauto with mem.
  unfold loadbytes. rewrite pred_dec_true. rewrite store_mem_contents; simpl.
  setoid_rewrite NMap.gss.
  replace (Z.to_nat (size_chunk chunk)) with (length (encode_val chunk v)).
  rewrite getN_setN_same. auto.
  rewrite encode_val_length. auto.
  apply H.
Qed.

Theorem loadbytes_store_other:
  forall b' ofs' n,
  b' <> b
  \/ n <= 0
  \/ ofs' + n <= ofs
  \/ ofs + size_chunk chunk <= ofs' ->
  loadbytes m2 b' ofs' n = loadbytes m1 b' ofs' n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + n) Cur Readable).
  rewrite pred_dec_true.
  decEq. rewrite store_mem_contents; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  destruct H. congruence.
  destruct (zle n 0) as [z | n0].
  rewrite (Z_to_nat_neg _ z). auto.
  destruct H. extlia.
  apply getN_setN_outside. rewrite encode_val_length. rewrite <- size_chunk_conv.
  rewrite Z2Nat.id. auto. lia.
  auto.
  red; intros. eauto with mem.
  rewrite pred_dec_false. auto.
  red; intro; elim n0; red; intros; eauto with mem.
Qed.

Lemma setN_in:
  forall A vl p q (c: ZMap.t A),
  p <= q < p + Z.of_nat (length vl) ->
  In (ZMap.get q (setN vl p c)) vl.
Proof.
  induction vl; intros.
  simpl in H. extlia.
  simpl length in H. rewrite Nat2Z.inj_succ in H. simpl.
  destruct (zeq p q). subst q. rewrite setN_outside. rewrite ZMap.gss.
  auto with coqlib. lia.
  right. apply IHvl. lia.
Qed.

Lemma getN_in:
  forall A (c: ZMap.t A) q n p,
  p <= q < p + Z.of_nat n ->
  In (ZMap.get q c) (getN n p c).
Proof.
  induction n; intros.
  simpl in H; extlia.
  rewrite Nat2Z.inj_succ in H. simpl. destruct (zeq p q).
  subst q. auto.
  right. apply IHn. lia.
Qed.


End STORE.

Local Hint Resolve perm_store_1 perm_store_2: mem.
Local Hint Resolve store_valid_block_1 store_valid_block_2: mem.
Local Hint Resolve store_valid_access_1 store_valid_access_2
  store_valid_access_3: mem.
Local Hint Resolve support_store support_storev : mem.

Lemma load_store_overlap:
  forall chunk m1 b ofs v m2 chunk' ofs' v',
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b ofs' = Some v' ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  exists mv1 mvl mv1' mvl',
      shape_encoding chunk v (mv1 :: mvl)
  /\  shape_decoding chunk' (mv1' :: mvl') v'
  /\  (   (ofs' = ofs /\ mv1' = mv1)
       \/ (ofs' > ofs /\ In mv1' mvl)
       \/ (ofs' < ofs /\ In mv1 mvl')).
Proof.
  intros.
  exploit load_result; eauto. erewrite store_mem_contents by eauto; simpl.
  setoid_rewrite NMap.gss.
  set (c := (mem_contents m1)#b). intros V'.
  destruct (size_chunk_nat_pos chunk) as [sz SIZE].
  destruct (size_chunk_nat_pos chunk') as [sz' SIZE'].
  destruct (encode_val chunk v) as [ | mv1 mvl] eqn:ENC.
  generalize (encode_val_length chunk v); rewrite ENC; simpl; congruence.
  set (c' := setN (mv1::mvl) ofs c) in *.
  exists mv1, mvl, (ZMap.get ofs' c'), (getN sz' (ofs' + 1) c').
  split. rewrite <- ENC. apply encode_val_shape.
  split. rewrite V', SIZE'. apply decode_val_shape.
  destruct (zeq ofs' ofs).
- subst ofs'. left; split. auto. unfold c'. simpl.
  rewrite setN_outside by lia. apply ZMap.gss.
- right. destruct (zlt ofs ofs').
(* If ofs < ofs':  the load reads (at ofs') a continuation byte from the write.
       ofs   ofs'   ofs+|chunk|
        [-------------------]       write
             [-------------------]  read
*)
+ left; split. lia. unfold c'. simpl. apply setN_in.
  assert (Z.of_nat (length (mv1 :: mvl)) = size_chunk chunk).
  { rewrite <- ENC; rewrite encode_val_length. rewrite size_chunk_conv; auto. }
  simpl length in H3. rewrite Nat2Z.inj_succ in H3. lia.
(* If ofs > ofs':  the load reads (at ofs) the first byte from the write.
       ofs'   ofs   ofs'+|chunk'|
               [-------------------]  write
         [----------------]           read
*)
+ right; split. lia. replace mv1 with (ZMap.get ofs c').
  apply getN_in.
  assert (size_chunk chunk' = Z.succ (Z.of_nat sz')).
  { rewrite size_chunk_conv. rewrite SIZE'. rewrite Nat2Z.inj_succ; auto. }
  lia.
  unfold c'. simpl. rewrite setN_outside by lia. apply ZMap.gss.
Qed.

Definition compat_pointer_chunks (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | (Mint32 | Many32), (Mint32 | Many32) => True
  | (Mint64 | Many64), (Mint64 | Many64) => True
  | _, _ => False
  end.

Lemma compat_pointer_chunks_true:
  forall chunk1 chunk2,
  (chunk1 = Mint32 \/ chunk1 = Many32 \/ chunk1 = Mint64 \/ chunk1 = Many64) ->
  (chunk2 = Mint32 \/ chunk2 = Many32 \/ chunk2 = Mint64 \/ chunk2 = Many64) ->
  quantity_chunk chunk1 = quantity_chunk chunk2 ->
  compat_pointer_chunks chunk1 chunk2.
Proof.
  intros. destruct H as [P|[P|[P|P]]]; destruct H0 as [Q|[Q|[Q|Q]]];
  subst; red; auto; discriminate.
Qed.

Theorem load_pointer_store:
  forall chunk m1 b ofs v m2 chunk' b' ofs' v_b v_o,
  store chunk m1 b ofs v = Some m2 ->
  load chunk' m2 b' ofs' = Some(Vptr v_b v_o) ->
  (v = Vptr v_b v_o /\ compat_pointer_chunks chunk chunk' /\ b' = b /\ ofs' = ofs)
  \/ (b' <> b \/ ofs' + size_chunk chunk' <= ofs \/ ofs + size_chunk chunk <= ofs').
Proof.
  intros.
  destruct (NMap.elt_eq b' b); auto. subst b'.
  destruct (zle (ofs' + size_chunk chunk') ofs); auto.
  destruct (zle (ofs + size_chunk chunk) ofs'); auto.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  inv DEC; try contradiction.
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- (* Same offset *)
  subst. inv ENC.
  assert (chunk = Mint32 \/ chunk = Many32 \/ chunk = Mint64 \/ chunk = Many64)
  by (destruct chunk; auto || contradiction).
  left; split. rewrite H3.
  destruct H4 as [P|[P|[P|P]]]; subst chunk'; destruct v0; simpl in H3;
  try congruence; destruct Archi.ptr64; congruence.
  split. apply compat_pointer_chunks_true; auto.
  auto.
- (* ofs' > ofs *)
  inv ENC.
  + exploit H10; eauto. intros (j & P & Q). inv P. congruence.
  + exploit H8; eauto. intros (n & P); congruence.
  + exploit H2; eauto. congruence.
- (* ofs' < ofs *)
  exploit H7; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
Qed.

Theorem load_store_pointer_overlap:
  forall chunk m1 b ofs v_b v_o m2 chunk' ofs' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs' = Some v ->
  ofs' <> ofs ->
  ofs' + size_chunk chunk' > ofs ->
  ofs + size_chunk chunk > ofs' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]].
- congruence.
- inv ENC.
  + exploit H9; eauto. intros (j & P & Q). subst mv1'. inv DEC. congruence. auto.
  + contradiction.
  + exploit H5; eauto. intros; subst. inv DEC; auto.
- inv DEC.
  + exploit H10; eauto. intros (j & P & Q). subst mv1. inv ENC. congruence.
  + exploit H8; eauto. intros (n & P). subst mv1. inv ENC. contradiction.
  + auto.
Qed.

Theorem load_store_pointer_mismatch:
  forall chunk m1 b ofs v_b v_o m2 chunk' v,
  store chunk m1 b ofs (Vptr v_b v_o) = Some m2 ->
  load chunk' m2 b ofs = Some v ->
  ~compat_pointer_chunks chunk chunk' ->
  v = Vundef.
Proof.
  intros.
  exploit load_store_overlap; eauto.
  generalize (size_chunk_pos chunk'); lia.
  generalize (size_chunk_pos chunk); lia.
  intros (mv1 & mvl & mv1' & mvl' & ENC & DEC & CASES).
  destruct CASES as [(A & B) | [(A & B) | (A & B)]]; try extlia.
  inv ENC; inv DEC; auto.
- elim H1. apply compat_pointer_chunks_true; auto.
- contradiction.
Qed.

Lemma store_similar_chunks:
  forall chunk1 chunk2 v1 v2 m b ofs,
  encode_val chunk1 v1 = encode_val chunk2 v2 ->
  align_chunk chunk1 = align_chunk chunk2 ->
  store chunk1 m b ofs v1 = store chunk2 m b ofs v2.
Proof.
  intros. unfold store.
  assert (size_chunk chunk1 = size_chunk chunk2).
    repeat rewrite size_chunk_conv.
    rewrite <- (encode_val_length chunk1 v1).
    rewrite <- (encode_val_length chunk2 v2).
    congruence.
  unfold store.
  destruct (valid_access_dec m chunk1 b ofs Writable);
  destruct (valid_access_dec m chunk2 b ofs Writable); auto.
  f_equal. apply mkmem_ext; auto. congruence.
  elim n. apply valid_access_compat with chunk1; auto. lia.
  elim n. apply valid_access_compat with chunk2; auto. lia.
Qed.

Theorem store_signed_unsigned_8:
  forall m b ofs v,
  store Mint8signed m b ofs v = store Mint8unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int8_signed_unsigned. auto. Qed.

Theorem store_signed_unsigned_16:
  forall m b ofs v,
  store Mint16signed m b ofs v = store Mint16unsigned m b ofs v.
Proof. intros. apply store_similar_chunks. apply encode_val_int16_signed_unsigned. auto. Qed.

Theorem store_int8_zero_ext:
  forall m b ofs n,
  store Mint8unsigned m b ofs (Vint (Int.zero_ext 8 n)) =
  store Mint8unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_zero_ext. auto. Qed.

Theorem store_int8_sign_ext:
  forall m b ofs n,
  store Mint8signed m b ofs (Vint (Int.sign_ext 8 n)) =
  store Mint8signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int8_sign_ext. auto. Qed.

Theorem store_int16_zero_ext:
  forall m b ofs n,
  store Mint16unsigned m b ofs (Vint (Int.zero_ext 16 n)) =
  store Mint16unsigned m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_zero_ext. auto. Qed.

Theorem store_int16_sign_ext:
  forall m b ofs n,
  store Mint16signed m b ofs (Vint (Int.sign_ext 16 n)) =
  store Mint16signed m b ofs (Vint n).
Proof. intros. apply store_similar_chunks. apply encode_val_int16_sign_ext. auto. Qed.

(*
Theorem store_float64al32:
  forall m b ofs v m',
  store Mfloat64 m b ofs v = Some m' -> store Mfloat64al32 m b ofs v = Some m'.
Proof.
  unfold store; intros.
  destruct (valid_access_dec m Mfloat64 b ofs Writable); try discriminate.
  destruct (valid_access_dec m Mfloat64al32 b ofs Writable).
  rewrite <- H. f_equal. apply mkmem_ext; auto.
  elim n. apply valid_access_compat with Mfloat64; auto. simpl; lia.
Qed.

Theorem storev_float64al32:
  forall m a v m',
  storev Mfloat64 m a v = Some m' -> storev Mfloat64al32 m a v = Some m'.
Proof.
  unfold storev; intros. destruct a; auto. apply store_float64al32; auto.
Qed.
*)

(** ** Properties related to [storebytes]. *)

Theorem range_perm_storebytes:
  forall m1 b ofs bytes,
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ->
  { m2 : mem | storebytes m1 b ofs bytes = Some m2 }.
Proof.
  intros. unfold storebytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable).
  econstructor; reflexivity.
  contradiction.
Defined.

Theorem storebytes_store:
  forall m1 b ofs chunk v m2,
  storebytes m1 b ofs (encode_val chunk v) = Some m2 ->
  (align_chunk chunk | ofs) ->
  store chunk m1 b ofs v = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable); inv H.
  destruct (valid_access_dec m1 chunk b ofs Writable).
  f_equal. apply mkmem_ext; auto.
  elim n. constructor; auto.
  rewrite encode_val_length in r. rewrite size_chunk_conv. auto.
Qed.

Theorem store_storebytes:
  forall m1 b ofs chunk v m2,
  store chunk m1 b ofs v = Some m2 ->
  storebytes m1 b ofs (encode_val chunk v) = Some m2.
Proof.
  unfold storebytes, store. intros.
  destruct (valid_access_dec m1 chunk b ofs Writable); inv H.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length (encode_val chunk v))) Cur Writable).
  f_equal. apply mkmem_ext; auto.
  destruct v0.  elim n.
  rewrite encode_val_length. rewrite <- size_chunk_conv. auto.
Qed.

Section STOREBYTES.
Variable m1: mem.
Variable b: block.
Variable ofs: Z.
Variable bytes: list memval.
Variable m2: mem.
Hypothesis STORE: storebytes m1 b ofs bytes = Some m2.

Lemma storebytes_empty : bytes = nil -> m1 = m2.
  intro. subst. inv STORE. unfold storebytes in H0.
  destruct range_perm_dec; try congruence.
  inv H0. destruct m1.
  apply mkmem_ext; eauto. cbn.
  apply NMap.set3.
Qed.

Lemma storebytes_access: mem_access m2 = mem_access m1.
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Lemma storebytes_mem_contents:
   mem_contents m2 = NMap.set _ b (setN bytes ofs m1.(mem_contents)#b) m1.(mem_contents).
Proof.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem perm_storebytes_1:
  forall b' ofs' k p, perm m1 b' ofs' k p -> perm m2 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access; auto.
Qed.

Theorem perm_storebytes_2:
  forall b' ofs' k p, perm m2 b' ofs' k p -> perm m1 b' ofs' k p.
Proof.
  intros. unfold perm in *. rewrite storebytes_access in H; auto.
Qed.

Local Hint Resolve perm_storebytes_1 perm_storebytes_2: mem.

Theorem storebytes_valid_access_1:
  forall chunk' b' ofs' p,
  valid_access m1 chunk' b' ofs' p -> valid_access m2 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Theorem storebytes_valid_access_2:
  forall chunk' b' ofs' p,
  valid_access m2 chunk' b' ofs' p -> valid_access m1 chunk' b' ofs' p.
Proof.
  intros. inv H. constructor; try red; auto with mem.
Qed.

Local Hint Resolve storebytes_valid_access_1 storebytes_valid_access_2: mem.

Theorem nextblock_storebytes:
  nextblock m2 = nextblock m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem support_storebytes:
  support m2 = support m1.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem storebytes_valid_block_1:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite support_storebytes; auto.
Qed.

Theorem storebytes_valid_block_2:
  forall b', valid_block m2 b' -> valid_block m1 b'.
Proof.
  unfold valid_block; intros. rewrite support_storebytes in H; auto.
Qed.

Local Hint Resolve storebytes_valid_block_1 storebytes_valid_block_2: mem.

Theorem storebytes_range_perm:
  range_perm m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable.
Proof.
  intros.
  unfold storebytes in STORE.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  inv STORE.
  auto.
Qed.

Theorem loadbytes_storebytes_same:
  loadbytes m2 b ofs (Z.of_nat (length bytes)) = Some bytes.
Proof.
  intros. assert (STORE2:=STORE). unfold storebytes in STORE2. unfold loadbytes.
  destruct (range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable);
  try discriminate.
  rewrite pred_dec_true.
  decEq. inv STORE2; simpl. setoid_rewrite NMap.gss. rewrite Nat2Z.id.
  apply getN_setN_same.
  red; eauto with mem.
Qed.

Theorem loadbytes_storebytes_disjoint:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b \/ Intv.disjoint (ofs', ofs' + len) (ofs, ofs + Z.of_nat (length bytes)) ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs' (ofs' + len) Cur Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  apply getN_setN_disjoint. rewrite Z2Nat.id by lia. intuition congruence.
  auto.
  red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. red; auto with mem.
Qed.

Theorem loadbytes_storebytes_other:
  forall b' ofs' len,
  len >= 0 ->
  b' <> b
  \/ ofs' + len <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  loadbytes m2 b' ofs' len = loadbytes m1 b' ofs' len.
Proof.
  intros. apply loadbytes_storebytes_disjoint; auto.
  destruct H0; auto. right. apply Intv.disjoint_range; auto.
Qed.

Theorem load_storebytes_other:
  forall chunk b' ofs',
  b' <> b
  \/ ofs' + size_chunk chunk <= ofs
  \/ ofs + Z.of_nat (length bytes) <= ofs' ->
  load chunk m2 b' ofs' = load chunk m1 b' ofs'.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m1 chunk b' ofs' Readable).
  rewrite pred_dec_true.
  rewrite storebytes_mem_contents. decEq.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  rewrite getN_setN_outside. auto. rewrite <- size_chunk_conv. intuition congruence.
  auto.
  destruct v; split; auto. red; auto with mem.
  apply pred_dec_false.
  red; intros; elim n. destruct H0. split; auto. red; auto with mem.
Qed.

End STOREBYTES.

Lemma setN_concat:
  forall A bytes1 bytes2 ofs (c:ZMap.t A),
  setN (bytes1 ++ bytes2) ofs c = setN bytes2 (ofs + Z.of_nat (length bytes1)) (setN bytes1 ofs c).
Proof.
  induction bytes1; intros.
  simpl. decEq. lia.
  simpl length. rewrite Nat2Z.inj_succ. simpl. rewrite IHbytes1. decEq. lia.
Qed.

Theorem storebytes_concat:
  forall m b ofs bytes1 m1 bytes2 m2,
  storebytes m b ofs bytes1 = Some m1 ->
  storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2 ->
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2.
Proof.
  intros. generalize H; intro ST1. generalize H0; intro ST2.
  unfold storebytes; unfold storebytes in ST1; unfold storebytes in ST2.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat(length bytes1)) Cur Writable); try congruence.
  destruct (range_perm_dec m1 b (ofs + Z.of_nat(length bytes1)) (ofs + Z.of_nat(length bytes1) + Z.of_nat(length bytes2)) Cur Writable); try congruence.
  destruct (range_perm_dec m b ofs (ofs + Z.of_nat (length (bytes1 ++ bytes2))) Cur Writable).
  inv ST1; inv ST2; simpl. decEq. apply mkmem_ext; auto.
  setoid_rewrite NMap.gss.  rewrite setN_concat. symmetry. apply NMap.set2.
  elim n.
  rewrite app_length. rewrite Nat2Z.inj_add. red; intros.
  destruct (zlt ofs0 (ofs + Z.of_nat(length bytes1))).
  apply r. lia.
  eapply perm_storebytes_2; eauto. apply r0. lia.
Qed.

Theorem storebytes_split:
  forall m b ofs bytes1 bytes2 m2,
  storebytes m b ofs (bytes1 ++ bytes2) = Some m2 ->
  exists m1,
     storebytes m b ofs bytes1 = Some m1
  /\ storebytes m1 b (ofs + Z.of_nat(length bytes1)) bytes2 = Some m2.
Proof.
  intros.
  destruct (range_perm_storebytes m b ofs bytes1) as [m1 ST1].
  red; intros. exploit storebytes_range_perm; eauto. rewrite app_length.
  rewrite Nat2Z.inj_add. lia.
  destruct (range_perm_storebytes m1 b (ofs + Z.of_nat (length bytes1)) bytes2) as [m2' ST2].
  red; intros. eapply perm_storebytes_1; eauto. exploit storebytes_range_perm.
  eexact H. instantiate (1 := ofs0). rewrite app_length. rewrite Nat2Z.inj_add. lia.
  auto.
  assert (Some m2 = Some m2').
  rewrite <- H. eapply storebytes_concat; eauto.
  inv H0.
  exists m1; split; auto.
Qed.

Theorem store_int64_split:
  forall m b ofs v m',
  store Mint64 m b ofs v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     store Mint32 m b ofs (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ store Mint32 m1 b (ofs + 4) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros.
  exploit store_valid_access_3; eauto. intros [A B]. simpl in *.
  exploit store_storebytes. eexact H. intros SB.
  rewrite encode_val_int64 in SB by auto.
  exploit storebytes_split. eexact SB. intros [m1 [SB1 SB2]].
  rewrite encode_val_length in SB2. simpl in SB2.
  exists m1; split.
  apply storebytes_store. exact SB1.
  simpl. apply Z.divide_trans with 8; auto. exists 2; auto.
  apply storebytes_store. exact SB2.
  simpl. apply Z.divide_add_r. apply Z.divide_trans with 8; auto. exists 2; auto. exists 1; auto.
Qed.

Theorem storev_int64_split:
  forall m a v m',
  storev Mint64 m a v = Some m' -> Archi.ptr64 = false ->
  exists m1,
     storev Mint32 m a (if Archi.big_endian then Val.hiword v else Val.loword v) = Some m1
  /\ storev Mint32 m1 (Val.add a (Vint (Int.repr 4))) (if Archi.big_endian then Val.loword v else Val.hiword v) = Some m'.
Proof.
  intros. destruct a; simpl in H; inv H. rewrite H2.
  exploit store_int64_split; eauto. intros [m1 [A B]].
  exists m1; split.
  exact A.
  unfold storev, Val.add. rewrite H0.
  rewrite addressing_int64_split; auto.
  exploit store_valid_access_3. eexact H2. intros [P Q]. exact Q.
Qed.

(** ** Properties related to [alloc]. *)

Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc m1 lo hi = (m2, b).

Theorem nextblock_alloc:
  nextblock m2 = fresh_block (sup_incr(support m1)).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem support_alloc:
  support m2 = sup_incr(support m1).
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem alloc_result:
  b = nextblock m1.
Proof.
  injection ALLOC; auto.
Qed.

Theorem alloc_block_noglobal:
  fst b <> O.
Proof.
  rewrite alloc_result. simpl. intro.
  generalize (tid_valid (support m1)).
  intro. extlia.
Qed.

Theorem valid_block_alloc:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite support_alloc.
  apply mem_incr_2. auto.
Qed.

Theorem fresh_block_alloc:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_result. apply freshness.
Qed.

Theorem valid_new_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_result. rewrite support_alloc. apply mem_incr_1.
Qed.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.

Theorem valid_block_alloc_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros.
  rewrite support_alloc in H. rewrite alloc_result.
  apply sup_incr_in. auto.
Qed.

Theorem perm_alloc_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite NMap.gsspec. destruct (NMap.elt_eq b' (nextblock m1)); auto.
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply freshness.
Qed.

Theorem perm_alloc_2:
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. unfold NMap.get. rewrite NMap.gss.
  rewrite setpermN_inside. simpl. auto with mem. lia.
Qed.

Theorem perm_alloc_inv:
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite NMap.gsspec.  destruct (NMap.elt_eq b' (nextblock m1)); intros.
  assert (zle lo ofs && zlt ofs hi = true).
    rewrite setpermN_inv in H.
    destruct(zle lo ofs && zlt ofs hi). reflexivity. contradiction.
  - destruct(eq_block b' (nextblock m1)).
    rewrite setpermN_inv in H.
    + split. destruct (zle lo ofs); try auto. try contradiction.
    destruct (zlt ofs hi). try auto. simpl in H.
    destruct (zle lo ofs); simpl in H; contradiction.
    + congruence.
  - destruct (eq_block b' (nextblock m1)).
    + congruence.
    + auto.
Qed.

Theorem perm_alloc_3:
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_true; auto.
Qed.

Theorem perm_alloc_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Proof.
  intros. exploit perm_alloc_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_1 perm_alloc_2 perm_alloc_3 perm_alloc_4: mem.

Theorem valid_access_alloc_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_2. lia.
Qed.

Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.

Theorem valid_access_alloc_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b' b). subst b'.
  assert (perm m2 b ofs Cur p). apply H0. lia.
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. lia.
  exploit perm_alloc_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_inv. eexact H3. rewrite dec_eq_true. intro.
  intuition lia.
  split; auto. red; intros.
  exploit perm_alloc_inv. apply H0. eauto. rewrite dec_eq_false; auto.
Qed.

Theorem load_alloc_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. exfalso. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  setoid_rewrite NMap.gso. auto. rewrite H1. apply not_eq_sym; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_unchanged. eauto with mem.
Qed.

Theorem load_alloc_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  setoid_rewrite NMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef.
Qed.

Theorem load_alloc_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_2. lia. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_same; eauto.
Qed.

Theorem loadbytes_alloc_unchanged:
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  setoid_rewrite NMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_1; eauto.
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_4; eauto. eauto with mem.
Qed.

Theorem loadbytes_alloc_same:
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. setoid_rewrite NMap.gss.
  generalize (Z.to_nat n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H. destruct H; eauto.
Qed.

End ALLOC.

Local Hint Resolve valid_block_alloc fresh_block_alloc valid_new_block: mem.
Local Hint Resolve valid_access_alloc_other valid_access_alloc_same: mem.
Local Hint Resolve support_alloc : mem.

(** ** Properties related to [alloc]. *)

Section ALLOCGLOBAL.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: block.
Hypothesis ALLOC: alloc_global m1 lo hi = (m2, b).

Theorem support_alloc_global:
  support m2 = sup_incr_tid (support m1) O.
Proof.
  injection ALLOC; intros. rewrite <- H0; auto.
Qed.

Theorem alloc_global_result:
  b = nextblock_global m1.
Proof.
  injection ALLOC; auto.
Qed.

Theorem valid_block_alloc_global:
  forall b', valid_block m1 b' -> valid_block m2 b'.
Proof.
  unfold valid_block; intros. rewrite support_alloc_global.
  apply sup_incr_tid_in2. red. generalize (tid_valid (support m1)). lia. auto.
Qed.

Theorem fresh_block_alloc_global:
  ~(valid_block m1 b).
Proof.
  unfold valid_block. rewrite alloc_global_result. apply freshness_tid.
Qed.

Theorem valid_new_global_block:
  valid_block m2 b.
Proof.
  unfold valid_block. rewrite alloc_global_result. rewrite support_alloc_global.
  apply sup_incr_tid_in1. red. generalize (tid_valid (support m1)). lia.
Qed.

Local Hint Resolve valid_block_alloc_global fresh_block_alloc_global
  valid_new_global_block: mem.

Theorem valid_block_alloc_global_inv:
  forall b', valid_block m2 b' -> b' = b \/ valid_block m1 b'.
Proof.
  unfold valid_block; intros.
  rewrite support_alloc_global in H. rewrite alloc_global_result.
  apply sup_incr_tid_in. red.  generalize (tid_valid (support m1)). lia. auto.
Qed.

Theorem perm_alloc_global_1:
  forall b' ofs k p, perm m1 b' ofs k p -> perm m2 b' ofs k p.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. rewrite NMap.gsspec. destruct (NMap.elt_eq b' (nextblock_global m1)); auto.
  rewrite nextblock_noaccess in H. contradiction. subst b'. apply freshness_tid.
Qed.

Theorem perm_alloc_global_2:
  forall ofs k, lo <= ofs < hi -> perm m2 b ofs k Freeable.
Proof.
  unfold perm; intros. injection ALLOC; intros. rewrite <- H1; simpl.
  subst b. unfold NMap.get. rewrite NMap.gss.
  rewrite setpermN_inside. simpl. auto with mem. lia.
Qed.

Theorem perm_alloc_global_inv:
  forall b' ofs k p,
  perm m2 b' ofs k p ->
  if eq_block b' b then lo <= ofs < hi else perm m1 b' ofs k p.
Proof.
  intros until p; unfold perm. inv ALLOC. simpl.
  rewrite NMap.gsspec.  destruct (NMap.elt_eq b' (nextblock_global m1)); intros.
  assert (zle lo ofs && zlt ofs hi = true).
    rewrite setpermN_inv in H.
    destruct(zle lo ofs && zlt ofs hi). reflexivity. contradiction.
  - destruct(eq_block b' (nextblock_global m1)).
    rewrite setpermN_inv in H.
    + split. destruct (zle lo ofs); try auto. try contradiction.
    destruct (zlt ofs hi). try auto. simpl in H.
    destruct (zle lo ofs); simpl in H; contradiction.
    + congruence.
  - destruct (eq_block b' (nextblock_global m1)).
    + congruence.
    + auto.
Qed.

Theorem perm_alloc_global_3:
  forall ofs k p, perm m2 b ofs k p -> lo <= ofs < hi.
Proof.
  intros. exploit perm_alloc_global_inv; eauto. rewrite dec_eq_true; auto.
Qed.

Theorem perm_alloc_global_4:
  forall b' ofs k p, perm m2 b' ofs k p -> b' <> b -> perm m1 b' ofs k p.
Proof.
  intros. exploit perm_alloc_global_inv; eauto. rewrite dec_eq_false; auto.
Qed.

Local Hint Resolve perm_alloc_global_1 perm_alloc_global_2
  perm_alloc_global_3 perm_alloc_global_4: mem.

Theorem valid_access_alloc_global_other:
  forall chunk b' ofs p,
  valid_access m1 chunk b' ofs p ->
  valid_access m2 chunk b' ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; auto with mem.
Qed.

Theorem valid_access_alloc_global_same:
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  valid_access m2 chunk b ofs Freeable.
Proof.
  intros. constructor; auto with mem.
  red; intros. apply perm_alloc_global_2. lia.
Qed.

Local Hint Resolve valid_access_alloc_global_other valid_access_alloc_global_same: mem.

Theorem valid_access_alloc_global_inv:
  forall chunk b' ofs p,
  valid_access m2 chunk b' ofs p ->
  if eq_block b' b
  then lo <= ofs /\ ofs + size_chunk chunk <= hi /\ (align_chunk chunk | ofs)
  else valid_access m1 chunk b' ofs p.
Proof.
  intros. inv H.
  generalize (size_chunk_pos chunk); intro.
  destruct (eq_block b' b). subst b'.
  assert (perm m2 b ofs Cur p). apply H0. lia.
  assert (perm m2 b (ofs + size_chunk chunk - 1) Cur p). apply H0. lia.
  exploit perm_alloc_global_inv. eexact H2. rewrite dec_eq_true. intro.
  exploit perm_alloc_global_inv. eexact H3. rewrite dec_eq_true. intro.
  intuition lia.
  split; auto. red; intros.
  exploit perm_alloc_global_inv. apply H0. eauto. rewrite dec_eq_false; auto.
Qed.

Theorem load_alloc_global_unchanged:
  forall chunk b' ofs,
  valid_block m1 b' ->
  load chunk m2 b' ofs = load chunk m1 b' ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b' ofs Readable).
  exploit valid_access_alloc_global_inv; eauto. destruct (eq_block b' b); intros.
  subst b'. exfalso. eauto with mem.
  rewrite pred_dec_true; auto.
  injection ALLOC; intros. rewrite <- H2; simpl.
  setoid_rewrite NMap.gso. auto. rewrite H1. apply not_eq_sym; eauto with mem.
  rewrite pred_dec_false. auto.
  eauto with mem.
Qed.

Theorem load_alloc_global_other:
  forall chunk b' ofs v,
  load chunk m1 b' ofs = Some v ->
  load chunk m2 b' ofs = Some v.
Proof.
  intros. rewrite <- H. apply load_alloc_global_unchanged. eauto with mem.
Qed.

Theorem load_alloc_global_same:
  forall chunk ofs v,
  load chunk m2 b ofs = Some v ->
  v = Vundef.
Proof.
  intros. exploit load_result; eauto. intro. rewrite H0.
  injection ALLOC; intros. rewrite <- H2; simpl. rewrite <- H1.
  setoid_rewrite NMap.gss. destruct (size_chunk_nat_pos chunk) as [n E]. rewrite E. simpl.
  rewrite ZMap.gi. apply decode_val_undef.
Qed.

Theorem load_alloc_global_same':
  forall chunk ofs,
  lo <= ofs -> ofs + size_chunk chunk <= hi -> (align_chunk chunk | ofs) ->
  load chunk m2 b ofs = Some Vundef.
Proof.
  intros. assert (exists v, load chunk m2 b ofs = Some v).
    apply valid_access_load. constructor; auto.
    red; intros. eapply perm_implies. apply perm_alloc_global_2. lia. auto with mem.
  destruct H2 as [v LOAD]. rewrite LOAD. decEq.
  eapply load_alloc_global_same; eauto.
Qed.

Theorem loadbytes_alloc_global_unchanged:
  forall b' ofs n,
  valid_block m1 b' ->
  loadbytes m2 b' ofs n = loadbytes m1 b' ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m1 b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  injection ALLOC; intros A B. rewrite <- B; simpl.
  setoid_rewrite NMap.gso. auto. rewrite A. eauto with mem.
  red; intros. eapply perm_alloc_global_1; eauto.
  rewrite pred_dec_false; auto.
  red; intros; elim n0. red; intros. eapply perm_alloc_global_4; eauto. eauto with mem.
Qed.

Theorem loadbytes_alloc_global_same:
  forall n ofs bytes byte,
  loadbytes m2 b ofs n = Some bytes ->
  In byte bytes -> byte = Undef.
Proof.
  unfold loadbytes; intros. destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  revert H0.
  injection ALLOC; intros A B. rewrite <- A; rewrite <- B; simpl. setoid_rewrite NMap.gss.
  generalize (Z.to_nat n) ofs. induction n0; simpl; intros.
  contradiction.
  rewrite ZMap.gi in H. destruct H; eauto.
Qed.

End ALLOCGLOBAL.


(** ** Properties related to [free]. *)


Theorem range_perm_free:
  forall m1 b lo hi,
  range_perm m1 b lo hi Cur Freeable ->
  { m2: mem | free m1 b lo hi = Some m2 }.
Proof.
  intros; unfold free. rewrite pred_dec_true; auto. econstructor; eauto.
Defined.

Section FREE.

Variable m1: mem.
Variable bf: block.
Variables lo hi: Z.
Variable m2: mem.
Hypothesis FREE: free m1 bf lo hi = Some m2.

Theorem free_range_perm:
  range_perm m1 bf lo hi Cur Freeable.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable); auto.
  congruence.
Qed.

Lemma free_result:
  m2 = unchecked_free m1 bf lo hi.
Proof.
  unfold free in FREE. destruct (range_perm_dec m1 bf lo hi Cur Freeable).
  congruence. congruence.
Qed.

Theorem nextblock_free:
  nextblock m2 = nextblock m1.
Proof.
  rewrite free_result; reflexivity.
Qed.

Theorem support_free:
  support m2 = support m1.
Proof.
  rewrite free_result; reflexivity.
Qed.


Theorem valid_block_free_1:
  forall b, valid_block m1 b -> valid_block m2 b.
Proof.
  intros. rewrite free_result. assumption.
Qed.

Theorem valid_block_free_2:
  forall b, valid_block m2 b -> valid_block m1 b.
Proof.
  intros. rewrite free_result in H. assumption.
Qed.

Local Hint Resolve valid_block_free_1 valid_block_free_2: mem.

Theorem perm_free_1:
  forall b ofs k p,
  b <> bf \/ ofs < lo \/ hi <= ofs ->
  perm m1 b ofs k p ->
  perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf). subst b.
  rewrite setpermN_inv.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl.
  exfalso; intuition.
  auto. auto.
  auto.
Qed.

Theorem perm_free_2:
  forall ofs k p, lo <= ofs < hi -> ~ perm m2 bf ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  unfold NMap.get. rewrite NMap.gss.
  rewrite setpermN_inv. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true.
  simpl. tauto. lia. lia.
Qed.

Theorem perm_free_3:
  forall b ofs k p,
  perm m2 b ofs k p -> perm m1 b ofs k p.
Proof.
  intros until p. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf). subst b.
  rewrite setpermN_inv.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  auto. auto. auto.
Qed.

Theorem perm_free_4:
  forall b ofs k p,
    perm m2 b ofs k p -> b <> bf \/ ofs < lo \/ hi <= ofs.
Proof.
  intros until p.
  rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf). subst b.
  - 
  rewrite setpermN_inv.
  destruct (zle lo ofs); simpl.
  destruct (zlt ofs hi); simpl. tauto.
  intros. lia. intros. lia.
  - intros. left.  auto.
Qed.

Theorem perm_free_inv:
  forall b ofs k p,
  perm m1 b ofs k p ->
  (b = bf /\ lo <= ofs < hi) \/ perm m2 b ofs k p.
Proof.
  intros. rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf); auto. subst b.
  rewrite setpermN_inv.
  destruct (zle lo ofs); simpl; auto.
  destruct (zlt ofs hi); simpl; auto.
Qed.

Theorem valid_access_free_1:
  forall chunk b ofs p,
  valid_access m1 chunk b ofs p ->
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. constructor; auto with mem.
  red; intros. eapply perm_free_1; eauto.
  destruct (zlt lo hi). intuition. right. lia.
Qed.

Theorem valid_access_free_2:
  forall chunk ofs p,
  lo < hi -> ofs + size_chunk chunk > lo -> ofs < hi ->
  ~(valid_access m2 chunk bf ofs p).
Proof.
  intros; red; intros. inv H2.
  generalize (size_chunk_pos chunk); intros.
  destruct (zlt ofs lo).
  elim (perm_free_2 lo Cur p).
  lia. apply H3. lia.
  elim (perm_free_2 ofs Cur p).
  lia. apply H3. lia.
Qed.

Theorem valid_access_free_inv_1:
  forall chunk b ofs p,
  valid_access m2 chunk b ofs p ->
  valid_access m1 chunk b ofs p.
Proof.
  intros. destruct H. split; auto.
  red; intros. generalize (H ofs0 H1).
  rewrite free_result. unfold perm, unchecked_free; simpl.
  rewrite NMap.gsspec. destruct (NMap.elt_eq b bf). subst b.
  rewrite setpermN_inv.
  destruct (zle lo ofs0); simpl.
  destruct (zlt ofs0 hi); simpl.
  tauto. auto. auto. auto.
Qed.

Theorem valid_access_free_inv_2:
  forall chunk ofs p,
  valid_access m2 chunk bf ofs p ->
  lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs.
Proof.
  intros.
  destruct (zlt lo hi); auto.
  destruct (zle (ofs + size_chunk chunk) lo); auto.
  destruct (zle hi ofs); auto.
  elim (valid_access_free_2 chunk ofs p); auto. lia.
Qed.

Theorem load_free:
  forall chunk b ofs,
  b <> bf \/ lo >= hi \/ ofs + size_chunk chunk <= lo \/ hi <= ofs ->
  load chunk m2 b ofs = load chunk m1 b ofs.
Proof.
  intros. unfold load.
  destruct (valid_access_dec m2 chunk b ofs Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  eapply valid_access_free_inv_1; eauto.
  rewrite pred_dec_false; auto.
  red; intro; elim n. eapply valid_access_free_1; eauto.
Qed.

Theorem load_free_2:
  forall chunk b ofs v,
  load chunk m2 b ofs = Some v -> load chunk m1 b ofs = Some v.
Proof.
  intros. unfold load. rewrite pred_dec_true.
  rewrite (load_result _ _ _ _ _ H). rewrite free_result; auto.
  apply valid_access_free_inv_1. eauto with mem.
Qed.

Theorem loadbytes_free:
  forall b ofs n,
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  loadbytes m2 b ofs n = loadbytes m1 b ofs n.
Proof.
  intros. unfold loadbytes.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  rewrite free_result; auto.
  red; intros. eapply perm_free_3; eauto.
  rewrite pred_dec_false; auto.
  red; intros. elim n0; red; intros.
  eapply perm_free_1; eauto. destruct H; auto. right; lia.
Qed.

Theorem loadbytes_free_2:
  forall b ofs n bytes,
  loadbytes m2 b ofs n = Some bytes -> loadbytes m1 b ofs n = Some bytes.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m2 b ofs (ofs + n) Cur Readable); inv H.
  rewrite pred_dec_true. rewrite free_result; auto.
  red; intros. apply perm_free_3; auto.
Qed.

End FREE.

Local Hint Resolve valid_block_free_1 valid_block_free_2
             perm_free_1 perm_free_2 perm_free_3
             valid_access_free_1 valid_access_free_inv_1
             support_free : mem.

(** ** Properties related to [drop_perm] *)

Theorem range_perm_drop_1:
  forall m b lo hi p m', drop_perm m b lo hi p = Some m' -> range_perm m b lo hi Cur Freeable.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). auto. discriminate.
Qed.

Theorem range_perm_drop_2:
  forall m b lo hi p,
  range_perm m b lo hi Cur Freeable -> {m' | drop_perm m b lo hi p = Some m' }.
Proof.
  unfold drop_perm; intros.
  destruct (range_perm_dec m b lo hi Cur Freeable). econstructor. eauto. contradiction.
Defined.

Section DROP.

Variable m: mem.
Variable b: block.
Variable lo hi: Z.
Variable p: permission.
Variable m': mem.
Hypothesis DROP: drop_perm m b lo hi p = Some m'.

Theorem nextblock_drop:
  nextblock m' = nextblock m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto.
Qed.

Theorem support_drop:
  support m' = support m.
Proof.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP; auto.
Qed.

Theorem drop_perm_valid_block_1:
  forall b', valid_block m b' -> valid_block m' b'.
Proof.
  unfold valid_block; rewrite support_drop; auto.
Qed.

Theorem drop_perm_valid_block_2:
  forall b', valid_block m' b' -> valid_block m b'.
Proof.
  unfold valid_block; rewrite support_drop; auto.
Qed.

Theorem perm_drop_1:
  forall ofs k, lo <= ofs < hi -> perm m' b ofs k p.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm. simpl. unfold NMap.get. rewrite NMap.gss.
  rewrite setpermN_inv. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. constructor.
  lia. lia.
Qed.

Theorem perm_drop_2:
  forall ofs k p', lo <= ofs < hi -> perm m' b ofs k p' -> perm_order p p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H0. unfold perm; simpl. unfold NMap.get. rewrite NMap.gss.
  rewrite setpermN_inv. unfold proj_sumbool.
  rewrite zle_true. rewrite zlt_true. simpl. auto.
  lia. lia.
Qed.

Theorem perm_drop_3:
  forall b' ofs k p', b' <> b \/ ofs < lo \/ hi <= ofs -> perm m b' ofs k p' -> perm m' b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  unfold perm; simpl. rewrite NMap.gsspec. destruct (NMap.elt_eq b' b). subst b'.
  rewrite setpermN_inv.
  unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  byContradiction. intuition lia.
  auto. auto. auto.
Qed.

Theorem perm_drop_4:
  forall b' ofs k p', perm m' b' ofs k p' -> perm m b' ofs k p'.
Proof.
  intros.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP.
  revert H. unfold perm; simpl. rewrite NMap.gsspec. destruct (NMap.elt_eq b' b).
  subst b'.  rewrite setpermN_inv. unfold proj_sumbool. destruct (zle lo ofs). destruct (zlt ofs hi).
  simpl. intros. apply perm_implies with p. apply perm_implies with Freeable. apply perm_cur.
  apply r. tauto. auto with mem. auto.
  auto. auto. auto.
Qed.

Lemma valid_access_drop_1:
  forall chunk b' ofs p',
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p p' ->
  valid_access m chunk b' ofs p' -> valid_access m' chunk b' ofs p'.
Proof.
  intros. destruct H0. split; auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia.
  generalize (size_chunk_pos chunk); intros. intuition.
  eapply perm_drop_3; eauto.
Qed.

Lemma valid_access_drop_2:
  forall chunk b' ofs p',
  valid_access m' chunk b' ofs p' -> valid_access m chunk b' ofs p'.
Proof.
  intros. destruct H; split; auto.
  red; intros. eapply perm_drop_4; eauto.
Qed.

Theorem load_drop:
  forall chunk b' ofs,
  b' <> b \/ ofs + size_chunk chunk <= lo \/ hi <= ofs \/ perm_order p Readable ->
  load chunk m' b' ofs = load chunk m b' ofs.
Proof.
  intros.
  unfold load.
  destruct (valid_access_dec m chunk b' ofs Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  eapply valid_access_drop_1; eauto.
  rewrite pred_dec_false. auto.
  red; intros; elim n. eapply valid_access_drop_2; eauto.
Qed.

Theorem loadbytes_drop:
  forall b' ofs n,
  b' <> b \/ ofs + n <= lo \/ hi <= ofs \/ perm_order p Readable ->
  loadbytes m' b' ofs n = loadbytes m b' ofs n.
Proof.
  intros.
  unfold loadbytes.
  destruct (range_perm_dec m b' ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true.
  unfold drop_perm in DROP. destruct (range_perm_dec m b lo hi Cur Freeable); inv DROP. simpl. auto.
  red; intros.
  destruct (eq_block b' b). subst b'.
  destruct (zlt ofs0 lo). eapply perm_drop_3; eauto.
  destruct (zle hi ofs0). eapply perm_drop_3; eauto.
  apply perm_implies with p. eapply perm_drop_1; eauto. lia. intuition.
  eapply perm_drop_3; eauto.
  rewrite pred_dec_false; eauto.
  red; intros; elim n0; red; intros.
  eapply perm_drop_4; eauto.
Qed.

End DROP.

(** * Generic injections *)

(** A memory state [m1] generically injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address.
*)

Record mem_inj (f: meminj) (m1 m2: mem) : Prop :=
  mk_mem_inj {
    mi_perm:
      forall b1 b2 delta ofs k p,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs k p ->
      perm m2 b2 (ofs + delta) k p;
    mi_align:
      forall b1 b2 delta chunk ofs p,
      f b1 = Some(b2, delta) ->
      range_perm m1 b1 ofs (ofs + size_chunk chunk) Max p ->
      (align_chunk chunk | delta);
    mi_memval:
      forall b1 ofs b2 delta,
      f b1 = Some(b2, delta) ->
      perm m1 b1 ofs Cur Readable ->
      memval_inject f (ZMap.get ofs m1.(mem_contents)#b1) (ZMap.get (ofs+delta) m2.(mem_contents)#b2)
  }.

(** Preservation of permissions *)

Lemma perm_inj:
  forall f m1 m2 b1 ofs k p b2 delta,
  mem_inj f m1 m2 ->
  perm m1 b1 ofs k p ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p.
Proof.
  intros. eapply mi_perm; eauto.
Qed.

Lemma range_perm_inj:
  forall f m1 m2 b1 lo hi k p b2 delta,
  mem_inj f m1 m2 ->
  range_perm m1 b1 lo hi k p ->
  f b1 = Some(b2, delta) ->
  range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros; red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. apply H0. lia.
Qed.

Lemma valid_access_inj:
  forall f m1 m2 b1 b2 delta chunk ofs p,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. destruct H1 as [A B]. constructor.
  replace (ofs + delta + size_chunk chunk)
     with ((ofs + size_chunk chunk) + delta) by lia.
  eapply range_perm_inj; eauto.
  apply Z.divide_add_r; auto. eapply mi_align; eauto with mem.
Qed.

(** Preservation of loads. *)

Lemma getN_inj:
  forall f m1 m2 b1 b2 delta,
  mem_inj f m1 m2 ->
  f b1 = Some(b2, delta) ->
  forall n ofs,
  range_perm m1 b1 ofs (ofs + Z.of_nat n) Cur Readable ->
  list_forall2 (memval_inject f)
               (getN n ofs (m1.(mem_contents)#b1))
               (getN n (ofs + delta) (m2.(mem_contents)#b2)).
Proof.
  induction n; intros; simpl.
  constructor.
  rewrite Nat2Z.inj_succ in H1.
  constructor.
  eapply mi_memval; eauto.
  apply H1. lia.
  replace (ofs + delta + 1) with ((ofs + 1) + delta) by lia.
  apply IHn. red; intros; apply H1; lia.
Qed.

Lemma load_inj:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  mem_inj f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros.
  exists (decode_val chunk (getN (size_chunk_nat chunk) (ofs + delta) (m2.(mem_contents)#b2))).
  split. unfold load. apply pred_dec_true.
  eapply valid_access_inj; eauto with mem.
  exploit load_result; eauto. intro. rewrite H2.
  apply decode_val_inject. apply getN_inj; auto.
  rewrite <- size_chunk_conv. exploit load_valid_access; eauto. intros [A B]. auto.
Qed.

Lemma loadbytes_inj:
  forall f m1 m2 len b1 ofs b2 delta bytes1,
  mem_inj f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. unfold loadbytes in *.
  destruct (range_perm_dec m1 b1 ofs (ofs + len) Cur Readable); inv H0.
  exists (getN (Z.to_nat len) (ofs + delta) (m2.(mem_contents)#b2)).
  split. apply pred_dec_true.
  replace (ofs + delta + len) with ((ofs + len) + delta) by lia.
  eapply range_perm_inj; eauto with mem.
  apply getN_inj; auto.
  destruct (zle 0 len). rewrite Z2Nat.id by lia. auto.
  rewrite Z_to_nat_neg by lia. simpl. red; intros; extlia.
Qed.

(** Preservation of stores. *)

Lemma setN_inj:
  forall (access: Z -> Prop) delta f vl1 vl2,
  list_forall2 (memval_inject f) vl1 vl2 ->
  forall p c1 c2,
  (forall q, access q -> memval_inject f (ZMap.get q c1) (ZMap.get (q + delta) c2)) ->
  (forall q, access q -> memval_inject f (ZMap.get q (setN vl1 p c1))
                                         (ZMap.get (q + delta) (setN vl2 (p + delta) c2))).
Proof.
  induction 1; intros; simpl.
  auto.
  replace (p + delta + 1) with ((p + 1) + delta) by lia.
  apply IHlist_forall2; auto.
  intros. rewrite ZMap.gsspec at 1. destruct (ZIndexed.eq q0 p). subst q0.
  rewrite ZMap.gss. auto.
  rewrite ZMap.gso. auto. unfold ZIndexed.t in *. lia.
Qed.

Definition meminj_no_overlap (f: meminj) (m: mem) : Prop :=
  forall b1 b1' delta1 b2 b2' delta2 ofs1 ofs2,
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m b1 ofs1 Max Nonempty ->
  perm m b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.

Lemma neq_true : forall (A:Type)(b:block)(a1 a2:A),
    (if eq_block b b then a1 else a2) =a1.
Proof.
  intros. destruct (eq_block b b).
  auto. congruence.
Qed.

Lemma neq_false : forall (A:Type) (b1 b2:block) (a1 a2:A),
    (b1<>b2)->(if eq_block b1 b2 then a1 else a2) = a2.
Proof.
  intros. destruct (eq_block b1 b2).
  congruence. auto.
Qed.

Lemma store_mapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros.
  assert (valid_access m2 chunk b2 (ofs + delta) Writable).
    eapply valid_access_inj; eauto with mem.
  destruct (valid_access_store _ _ _ _ v2 H4) as [n2 STORE].
  exists n2; split. auto.
  constructor.
(* perm *)
  intros. eapply perm_store_1; [eexact STORE|].
  eapply mi_perm; eauto.
  eapply perm_store_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  rewrite ! NMap.gsspec.
  destruct (NMap.elt_eq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite neq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
  apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem.
  destruct (NMap.elt_eq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. eapply mi_memval; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto. eauto 6 with mem.
    exploit store_valid_access_3. eexact H0. intros [A B].
    eapply perm_implies. apply perm_cur_max. apply A. lia. auto with mem.
  destruct H8. congruence. lia.
  (* block <> b1, block <> b2 *)
  eapply mi_memval; eauto. eauto with mem.
Qed.

Lemma store_mapped_inj_rev:
  forall f chunk m1 b1 ofs v1 n2 m2 b2 delta v2,
    mem_inj f m1 m2 ->
    valid_access m1 chunk b1 ofs Writable ->
    store chunk m2 b2 (ofs + delta) v2 = Some n2 ->
    meminj_no_overlap f m1 ->
    f b1 = Some (b2, delta) ->
    Val.inject f v1 v2 ->
    exists n1,
      store chunk m1 b1 ofs v1 = Some n1
      /\ mem_inj f n1 n2.
Proof.
  intros.
  destruct (valid_access_store _ _ _ _ v1 H0) as [n1 STORE].
  exists n1; split. auto.
  constructor.
(* perm *)
  intros. eapply perm_store_1; [eexact H1|].
  eapply mi_perm; eauto.
  eapply perm_store_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ STORE).
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  rewrite ! NMap.gsspec.
  destruct (NMap.elt_eq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite neq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable).
  apply encode_val_inject; auto. intros. eapply mi_memval; eauto. eauto with mem.
  destruct (NMap.elt_eq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. eapply mi_memval; eauto. eauto with mem.
  rewrite encode_val_length. rewrite <- size_chunk_conv. intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H2; eauto. eauto 6 with mem.
    exploit store_valid_access_3. eexact STORE. intros [A B].
    eapply perm_implies. apply perm_cur_max. apply A. lia. auto with mem.
  destruct H8. congruence. lia.
  (* block <> b1, block <> b2 *)
  eapply mi_memval; eauto. eauto with mem.
Qed.

Lemma store_unmapped_inj:
  forall f chunk m1 b1 ofs v1 n1 m2,
  mem_inj f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. constructor.
(* perm *)
  intros. eapply mi_perm; eauto with mem.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros; eauto with mem.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H0).
  setoid_rewrite NMap.gso. eapply mi_memval; eauto with mem.
  congruence.
Qed.

Lemma store_outside_inj:
  forall f m1 m2 chunk b ofs v m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
(* perm *)
  eauto with mem.
(* access *)
  intros; eapply mi_align0; eauto.
(* mem_contents *)
  intros.
  rewrite (store_mem_contents _ _ _ _ _ _ H1).
  rewrite NMap.gsspec. destruct (NMap.elt_eq b2 b). subst b2.
  rewrite setN_outside. auto.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + size_chunk chunk) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_mapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  meminj_no_overlap f m1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ mem_inj f n1 n2.
Proof.
  intros. inversion H.
  assert (range_perm m2 b2 (ofs + delta) (ofs + delta + Z.of_nat (length bytes2)) Cur Writable).
    replace (ofs + delta + Z.of_nat (length bytes2))
       with ((ofs + Z.of_nat (length bytes1)) + delta).
    eapply range_perm_inj; eauto with mem.
    eapply storebytes_range_perm; eauto.
    rewrite (list_forall2_length H3). lia.
  destruct (range_perm_storebytes _ _ _ _ H4) as [n2 STORE].
  exists n2; split. eauto.
  constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; [apply STORE |].
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs0 Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ STORE).
  rewrite ! NMap.gsspec. destruct (NMap.elt_eq b0 b1). subst b0.
  (* block = b1, block = b2 *)
  assert (b3 = b2) by congruence. subst b3.
  assert (delta0 = delta) by congruence. subst delta0.
  rewrite neq_true.
  apply setN_inj with (access := fun ofs => perm m1 b1 ofs Cur Readable); auto.
  destruct (NMap.elt_eq b3 b2). subst b3.
  (* block <> b1, block = b2 *)
  rewrite setN_other. auto.
  intros.
  assert (b2 <> b2 \/ ofs0 + delta0 <> (r - delta) + delta).
    eapply H1; eauto 6 with mem.
    exploit storebytes_range_perm. eexact H0.
    instantiate (1 := r - delta).
    rewrite (list_forall2_length H3). lia.
    eauto 6 with mem.
  destruct H9. congruence. lia.
  (* block <> b1, block <> b2 *)
  eauto.
Qed.

Lemma storebytes_unmapped_inj:
  forall f m1 b1 ofs bytes1 n1 m2,
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  mem_inj f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align with (ofs := ofs0) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  setoid_rewrite NMap.gso. eapply mi_memval0; eauto. eapply perm_storebytes_2; eauto.
  congruence.
Qed.

Lemma storebytes_outside_inj:
  forall f m1 m2 b ofs bytes2 m2',
  mem_inj f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  mem_inj f m1 m2'.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. eapply perm_storebytes_1; eauto with mem.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  rewrite NMap.gsspec. destruct (NMap.elt_eq b2 b). subst b2.
  rewrite setN_outside. auto.
  destruct (zlt (ofs0 + delta) ofs); auto.
  destruct (zle (ofs + Z.of_nat (length bytes2)) (ofs0 + delta)). lia.
  byContradiction. eapply H0; eauto. lia.
  eauto with mem.
Qed.

Lemma storebytes_empty_inj:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  mem_inj f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  mem_inj f m1' m2'.
Proof.
  intros. destruct H. constructor.
(* perm *)
  intros.
  eapply perm_storebytes_1; eauto.
  eapply mi_perm0; eauto.
  eapply perm_storebytes_2; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_storebytes_2; eauto.
(* mem_contents *)
  intros.
  assert (perm m1 b0 ofs Cur Readable). eapply perm_storebytes_2; eauto.
  rewrite (storebytes_mem_contents _ _ _ _ _ H0).
  rewrite (storebytes_mem_contents _ _ _ _ _ H1).
  simpl. rewrite ! NMap.gsspec.
  destruct (NMap.elt_eq b0 b1); destruct (NMap.elt_eq b3 b2); subst; eapply mi_memval0; eauto.
Qed.

(** Preservation of allocations *)

Lemma alloc_right_inj:
  forall f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* perm *)
  intros. eapply perm_alloc_1; eauto.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  assert (perm m2 b0 (ofs + delta) Cur Readable).
    eapply mi_perm0; eauto.
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. setoid_rewrite NMap.gso. eauto with mem.
  rewrite NEXT. eauto with mem.
Qed.

Lemma alloc_left_unmapped_inj:
  forall f m1 m2 lo hi m1' b1,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  f b1 = None ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros. exploit perm_alloc_inv; eauto. intros.
  destruct (eq_block b0 b1). congruence. eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. exploit perm_alloc_inv; eauto.
  destruct (eq_block b0 b1); auto. congruence.
(* mem_contents *)
  injection H0; intros NEXT MEM. intros.
  rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite NMap.gsspec. (*unfold eq_block in H4.*) destruct (NMap.elt_eq b0 b1).
  rewrite ZMap.gi. constructor. apply mi_memval0. auto. eapply perm_alloc_4 in H0. apply H0. auto. auto.
Qed.

Definition inj_offset_aligned (delta: Z) (size: Z) : Prop :=
  forall chunk, size_chunk chunk <= size -> (align_chunk chunk | delta).

Lemma alloc_left_mapped_inj:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  f b1 = Some(b2, delta) ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros.
  exploit perm_alloc_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
  rewrite H4 in H5; inv H5. eauto. eauto.
(* align *)
  intros. destruct (eq_block b0 b1).
  subst b0. assert (delta0 = delta) by congruence. subst delta0.
  assert (lo <= ofs < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  assert (lo <= ofs + size_chunk chunk - 1 < hi).
  { eapply perm_alloc_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  apply H2. lia.
  eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_alloc_4; eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM.
  intros. rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_inv; eauto. intros.
  rewrite NMap.gsspec.
  destruct (NMap.elt_eq b0 b1). rewrite ZMap.gi. constructor.
  apply mi_memval. auto. auto. eapply perm_alloc_4 in H0. eauto. auto. auto.
Qed.

Lemma free_left_inj:
  forall f m1 m2 b lo hi m1',
  mem_inj f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  mem_inj f m1' m2.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H. constructor.
(* perm *)
  intros. eauto with mem.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros; eapply perm_free_3; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto with mem.
Qed.

Lemma free_right_inj:
  forall f m1 m2 b lo hi m2',
  mem_inj f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. exploit free_result; eauto. intro FREE. inversion H.
  assert (PERM:
    forall b1 b2 delta ofs k p,
    f b1 = Some (b2, delta) ->
    perm m1 b1 ofs k p -> perm m2' b2 (ofs + delta) k p).
  intros.
  intros. eapply perm_free_1; eauto.
  destruct (eq_block b2 b); auto. subst b. right.
  assert (~ (lo <= ofs + delta < hi)). red; intros; eapply H1; eauto.
  lia.
  constructor.
(* perm *)
  auto.
(* align *)
  eapply mi_align0; eauto.
(* mem_contents *)
  intros. rewrite FREE; simpl. eauto.
Qed.

(** Preservation of [drop_perm] operations. *)

Lemma drop_unmapped_inj:
  forall f m1 m2 b lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b lo hi p = Some m1' ->
  f b = None ->
  mem_inj f m1' m2.
Proof.
  intros. inv H. constructor.
(* perm *)
  intros. eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* contents *)
  intros.
  replace (ZMap.get ofs m1'.(mem_contents)#b1) with (ZMap.get ofs m1.(mem_contents)#b1).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b lo hi Cur Freeable); inv H0; auto.
Qed.

Lemma drop_mapped_inj:
  forall f m1 m2 b1 b2 delta lo hi p m1',
  mem_inj f m1 m2 ->
  drop_perm m1 b1 lo hi p = Some m1' ->
  meminj_no_overlap f m1 ->
  f b1 = Some(b2, delta) ->
  exists m2',
      drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2'
   /\ mem_inj f m1' m2'.
Proof.
  intros.
  assert ({ m2' | drop_perm m2 b2 (lo + delta) (hi + delta) p = Some m2' }).
  apply range_perm_drop_2. red; intros.
  replace ofs with ((ofs - delta) + delta) by lia.
  eapply perm_inj; eauto. eapply range_perm_drop_1; eauto. lia.
  destruct X as [m2' DROP]. exists m2'; split; auto.
  inv H.
  constructor.
(* perm *)
  intros.
  assert (perm m2 b3 (ofs + delta0) k p0).
    eapply mi_perm0; eauto. eapply perm_drop_4; eauto.
  destruct (eq_block b1 b0).
  (* b1 = b0 *)
  subst b0. rewrite H2 in H; inv H.
  destruct (zlt (ofs + delta0) (lo + delta0)). eapply perm_drop_3; eauto.
  destruct (zle (hi + delta0) (ofs + delta0)). eapply perm_drop_3; eauto.
  assert (perm_order p p0).
    eapply perm_drop_2.  eexact H0. instantiate (1 := ofs). lia. eauto.
  apply perm_implies with p; auto.
  eapply perm_drop_1. eauto. lia.
  (* b1 <> b0 *)
  eapply perm_drop_3; eauto.
  destruct (eq_block b3 b2); auto.
  destruct (zlt (ofs + delta0) (lo + delta)); auto.
  destruct (zle (hi + delta) (ofs + delta0)); auto.
  exploit H1; eauto.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable.
  eapply range_perm_drop_1; eauto. lia. auto with mem.
  eapply perm_drop_4; eauto. eapply perm_max. apply perm_implies with p0. eauto.
  eauto with mem.
  intuition.
(* align *)
  intros. eapply mi_align0 with (ofs := ofs) (p := p0); eauto.
  red; intros; eapply perm_drop_4; eauto.
(* memval *)
  intros.
  replace (m1'.(mem_contents)#b0) with (m1.(mem_contents)#b0).
  replace (m2'.(mem_contents)#b3) with (m2.(mem_contents)#b3).
  apply mi_memval0; auto. eapply perm_drop_4; eauto.
  unfold drop_perm in DROP; destruct (range_perm_dec m2 b2 (lo + delta) (hi + delta) Cur Freeable); inv DROP; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m1 b1 lo hi Cur Freeable); inv H0; auto.
Qed.

Lemma drop_outside_inj: forall f m1 m2 b lo hi p m2',
  mem_inj f m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs' k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs' k p ->
    lo <= ofs' + delta < hi -> False) ->
  mem_inj f m1 m2'.
Proof.
  intros. inv H. constructor.
  (* perm *)
  intros. eapply perm_drop_3; eauto.
  destruct (eq_block b2 b); auto. subst b2. right.
  destruct (zlt (ofs + delta) lo); auto.
  destruct (zle hi (ofs + delta)); auto.
  byContradiction. exploit H1; eauto. lia.
  (* align *)
  eapply mi_align0; eauto.
  (* contents *)
  intros.
  replace (m2'.(mem_contents)#b2) with (m2.(mem_contents)#b2).
  apply mi_memval0; auto.
  unfold drop_perm in H0; destruct (range_perm_dec m2 b lo hi Cur Freeable); inv H0; auto.
Qed.

(** * Memory extensions *)

(**  A store [m2] extends a store [m1] if [m2] can be obtained from [m1]
  by increasing the sizes of the memory blocks of [m1] (decreasing
  the low bounds, increasing the high bounds), and replacing some of
  the [Vundef] values stored in [m1] by more defined values stored
  in [m2] at the same locations. *)

Record extends' (m1 m2: mem) : Prop :=
  mk_extends {
    mext_sup: support m1 = support m2;
    mext_inj:  mem_inj inject_id m1 m2;
    mext_perm_inv: forall b ofs k p,
      perm m2 b ofs k p ->
      perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty
  }.

Definition extends := extends'.

Theorem extends_refl:
  forall m, extends m m.
Proof.
  intros. constructor. auto. constructor.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia. auto.
  intros. unfold inject_id in H; inv H. apply Z.divide_0_r.
  intros. unfold inject_id in H; inv H. replace (ofs + 0) with ofs by lia.
  apply memval_lessdef_refl.
  tauto.
Qed.

Theorem load_extends:
  forall chunk m1 m2 b ofs v1,
  extends m1 m2 ->
  load chunk m1 b ofs = Some v1 ->
  exists v2, load chunk m2 b ofs = Some v2 /\ Val.lessdef v1 v2.
Proof.
  intros. inv H. exploit load_inj; eauto. unfold inject_id; reflexivity.
  intros [v2 [A B]]. exists v2; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  rewrite val_inject_id in B. auto.
Qed.

Theorem loadv_extends:
  forall chunk m1 m2 addr1 addr2 v1,
  extends m1 m2 ->
  loadv chunk m1 addr1 = Some v1 ->
  Val.lessdef addr1 addr2 ->
  exists v2, loadv chunk m2 addr2 = Some v2 /\ Val.lessdef v1 v2.
Proof.
  unfold loadv; intros. inv H1.
  destruct addr2; try congruence. eapply load_extends; eauto.
  congruence.
Qed.

Theorem loadbytes_extends:
  forall m1 m2 b ofs len bytes1,
  extends m1 m2 ->
  loadbytes m1 b ofs len = Some bytes1 ->
  exists bytes2, loadbytes m2 b ofs len = Some bytes2
              /\ list_forall2 memval_lessdef bytes1 bytes2.
Proof.
  intros. inv H.
  replace ofs with (ofs + 0) by lia. eapply loadbytes_inj; eauto.
Qed.

Theorem store_within_extends:
  forall chunk m1 m2 b ofs v1 m1' v2,
  extends m1 m2 ->
  store chunk m1 b ofs v1 = Some m1' ->
  Val.lessdef v1 v2 ->
  exists m2',
     store chunk m2 b ofs v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
    rewrite val_inject_id. eauto.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (support_store _ _ _ _ _ _ H0).
  rewrite (support_store _ _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_within_extends_rev:
  forall chunk m1 m2 b ofs v1 m2' v2,
  extends m1 m2 ->
  valid_access m1 chunk b ofs Writable ->
  store chunk m2 b ofs v2 = Some m2' ->
  Val.lessdef v1 v2 ->
  exists m1',
     store chunk m1 b ofs v1 = Some m1'
  /\ extends m1' m2'.
Proof.
  intros. inversion H. replace (ofs) with (ofs + 0) in H1 by lia.
  exploit store_mapped_inj_rev. 3: eauto. eauto. eauto.
  unfold inject_id. red; intros. inv H4; inv H5. auto.
  unfold inject_id; reflexivity.
  rewrite val_inject_id. eauto.
  intros [m1' [A B]].
  exists m1'; split. eauto.
  constructor; auto.
  rewrite (support_store _ _ _ _ _ _ H1).
  rewrite (support_store _ _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_extends:
  forall chunk m1 m2 b ofs v m2',
  extends m1 m2 ->
  store chunk m2 b ofs v = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + size_chunk chunk -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (support_store _ _ _ _ _ _ H0). auto.
  eapply store_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_store_2.
Qed.


Theorem storev_extends:
  forall chunk m1 m2 addr1 v1 m1' addr2 v2,
  extends m1 m2 ->
  storev chunk m1 addr1 v1 = Some m1' ->
  Val.lessdef addr1 addr2 ->
  Val.lessdef v1 v2 ->
  exists m2',
     storev chunk m2 addr2 v2 = Some m2'
  /\ extends m1' m2'.
Proof.
  unfold storev; intros. inv H1.
  destruct addr2; try congruence. eapply store_within_extends; eauto.
  congruence.
Qed.


Lemma storev_extends_rev :
  forall chunk m1 m2 v1 m2' addr2 v2 b i,
    extends m1 m2 ->
    storev chunk m2 addr2 v2 = Some m2' ->
    Val.lessdef (Vptr b i) addr2 ->
    valid_access m1 chunk b (Ptrofs.unsigned i) Writable ->
    Val.lessdef v1 v2 ->
    exists m1' : mem, Mem.storev chunk m1 (Vptr b i) v1 = Some m1' /\ Mem.extends m1' m2'.
Proof.
  unfold storev; intros. inv H1.
  eapply store_within_extends_rev; eauto.
Qed.
  
Theorem storebytes_within_extends:
  forall m1 m2 b ofs bytes1 m1' bytes2,
  extends m1 m2 ->
  storebytes m1 b ofs bytes1 = Some m1' ->
  list_forall2 memval_lessdef bytes1 bytes2 ->
  exists m2',
     storebytes m2 b ofs bytes2 = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto.
    unfold inject_id; red; intros. inv H3; inv H4. auto.
    unfold inject_id; reflexivity.
  intros [m2' [A B]].
  exists m2'; split.
  replace (ofs + 0) with ofs in A by lia. auto.
  constructor; auto.
  rewrite (support_storebytes _ _ _ _ _ H0).
  rewrite (support_storebytes _ _ _ _ _ A).
  auto.
  intros. exploit mext_perm_inv0; intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_outside_extends:
  forall m1 m2 b ofs bytes2 m2',
  extends m1 m2 ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  (forall ofs', perm m1 b ofs' Cur Readable -> ofs <= ofs' < ofs + Z.of_nat (length bytes2) -> False) ->
  extends m1 m2'.
Proof.
  intros. inversion H. constructor.
  rewrite (support_storebytes _ _ _ _ _ H0). auto.
  eapply storebytes_outside_inj; eauto.
  unfold inject_id; intros. inv H2. eapply H1; eauto. lia.
  intros. eauto using perm_storebytes_2.
Qed.

Theorem alloc_extends:
  forall m1 m2 lo1 hi1 b m1' lo2 hi2,
  extends m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists m2',
     alloc m2 lo2 hi2 = (m2', b)
  /\ extends m1' m2'.
Proof.
  intros. inv H.
  case_eq (alloc m2 lo2 hi2); intros m2' b' ALLOC.
  assert (b' = b).
    rewrite (alloc_result _ _ _ _ _ H0).
    rewrite (alloc_result _ _ _ _ _ ALLOC).
    auto.
  unfold nextblock. congruence. subst b'.
  exists m2'; split; auto.
  constructor.
  rewrite (support_alloc _ _ _ _ _ H0).
  rewrite (support_alloc _ _ _ _ _ ALLOC).
  unfold nextblock. congruence.
  eapply alloc_left_mapped_inj with (m1 := m1) (m2 := m2') (b2 := b) (delta := 0); eauto.
  eapply alloc_right_inj; eauto.
  eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  eapply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto.
  lia.
  intros. eapply perm_alloc_inv in H; eauto.
  generalize (perm_alloc_inv _ _ _ _ _ H0 b0 ofs Max Nonempty); intros PERM.
  destruct (eq_block b0 b).
  subst b0.
  assert (EITHER: lo1 <= ofs < hi1 \/ ~(lo1 <= ofs < hi1)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; tauto.
  exploit mext_perm_inv0; intuition eauto using perm_alloc_1, perm_alloc_4.
Qed.

Theorem free_left_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  extends m1' m2.
Proof.
  intros. inv H. constructor.
  rewrite (support_free _ _ _ _ _ H0). auto.
  eapply free_left_inj; eauto.
  intros. exploit mext_perm_inv0; eauto. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  intuition eauto using perm_free_3.
Qed.

Theorem free_right_extends:
  forall m1 m2 b lo hi m2',
  extends m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall ofs k p, perm m1 b ofs k p -> lo <= ofs < hi -> False) ->
  extends m1 m2'.
Proof.
  intros. inv H. constructor.
  rewrite (support_free _ _ _ _ _ H0). auto.
  eapply free_right_inj; eauto.
  unfold inject_id; intros. inv H. eapply H1; eauto. lia.
  intros. eauto using perm_free_3.
Qed.

Theorem free_parallel_extends:
  forall m1 m2 b lo hi m1',
  extends m1 m2 ->
  free m1 b lo hi = Some m1' ->
  exists m2',
     free m2 b lo hi = Some m2'
  /\ extends m1' m2'.
Proof.
  intros. inversion H.
  assert ({ m2': mem | free m2 b lo hi = Some m2' }).
    apply range_perm_free. red; intros.
    replace ofs with (ofs + 0) by lia.
    eapply perm_inj with (b1 := b); eauto.
    eapply free_range_perm; eauto.
  destruct X as [m2' FREE]. exists m2'; split; auto.
  constructor.
  rewrite (support_free _ _ _ _ _ H0).
  rewrite (support_free _ _ _ _ _ FREE). auto.
  eapply free_right_inj with (m1 := m1'); eauto.
  eapply free_left_inj; eauto.
  unfold inject_id; intros. inv H1.
  eapply perm_free_2. eexact H0. instantiate (1 := ofs); lia. eauto.
  intros. exploit mext_perm_inv0; eauto using perm_free_3. intros [A|A].
  eapply perm_free_inv in A; eauto. destruct A as [[A B]|A]; auto.
  subst b0. right; eapply perm_free_2; eauto.
  right; intuition eauto using perm_free_3.
Qed.

Theorem valid_block_extends:
  forall m1 m2 b,
  extends m1 m2 ->
  (valid_block m1 b <-> valid_block m2 b).
Proof.
  intros. inv H. unfold valid_block. rewrite mext_sup0. tauto.
Qed.

Theorem perm_extends:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m1 b ofs k p -> perm m2 b ofs k p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply perm_inj; eauto.
Qed.

Theorem perm_extends_inv:
  forall m1 m2 b ofs k p,
  extends m1 m2 -> perm m2 b ofs k p -> perm m1 b ofs k p \/ ~perm m1 b ofs Max Nonempty.
Proof.
  intros. inv H; eauto.
Qed.

Theorem valid_access_extends:
  forall m1 m2 chunk b ofs p,
  extends m1 m2 -> valid_access m1 chunk b ofs p -> valid_access m2 chunk b ofs p.
Proof.
  intros. inv H. replace ofs with (ofs + 0) by lia.
  eapply valid_access_inj; eauto. auto.
Qed.

Theorem valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 -> valid_pointer m1 b ofs = true -> valid_pointer m2 b ofs = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in *.
  eapply valid_access_extends; eauto.
Qed.

Theorem weak_valid_pointer_extends:
  forall m1 m2 b ofs,
  extends m1 m2 ->
  weak_valid_pointer m1 b ofs = true -> weak_valid_pointer m2 b ofs = true.
Proof.
  intros until 1. unfold weak_valid_pointer. rewrite !orb_true_iff.
  intros []; eauto using valid_pointer_extends.
Qed.

(** * Memory injections *)

(** A memory state [m1] injects into another memory state [m2] via the
  memory injection [f] if the following conditions hold:
- each access in [m2] that corresponds to a valid access in [m1]
  is itself valid;
- the memory value associated in [m1] to an accessible address
  must inject into [m2]'s memory value at the corersponding address;
- unallocated blocks in [m1] must be mapped to [None] by [f];
- if [f b = Some(b', delta)], [b'] must be valid in [m2];
- distinct blocks in [m1] are mapped to non-overlapping sub-blocks in [m2];
- the sizes of [m2]'s blocks are representable with unsigned machine integers;
- pointers that could be represented using unsigned machine integers remain
  representable after the injection.
*)

Definition meminj_thread_local (f:meminj) : Prop := forall b b' d, f b = Some (b',d) -> fst b = fst b'.
Inductive mem_inj_thread : meminj -> mem -> mem -> Prop :=
|inject_thread_intro f m1 m2
   (Hms: match_sup (Mem.support m1) (Mem.support m2))
   (Hjs: meminj_thread_local f):
  mem_inj_thread f m1 m2.

Record inject' (f: meminj) (m1 m2: mem) : Prop :=
  mk_inject {
    mi_thread:
      mem_inj_thread f m1 m2;
    mi_inj:
      mem_inj f m1 m2;
    mi_freeblocks:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap:
      meminj_no_overlap f m1;
    mi_representable:
      forall b b' delta ofs,
      f b = Some(b', delta) ->
      perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
      delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
  }.
Definition inject := inject'.

Record inject_nothread (f: meminj) (m1 m2: mem) : Prop :=
  mk_inject_nothread {
    mi_inj_nt:
      mem_inj f m1 m2;
    mi_freeblocks_nt:
      forall b, ~(valid_block m1 b) -> f b = None;
    mi_mappedblocks_nt:
      forall b b' delta, f b = Some(b', delta) -> valid_block m2 b';
    mi_no_overlap_nt:
      meminj_no_overlap f m1;
    mi_representable_nt:
      forall b b' delta ofs,
      f b = Some(b', delta) ->
      perm m1 b (Ptrofs.unsigned ofs) Max Nonempty \/ perm m1 b (Ptrofs.unsigned ofs - 1) Max Nonempty ->
      delta >= 0 /\ 0 <= Ptrofs.unsigned ofs + delta <= Ptrofs.max_unsigned;
    mi_perm_inv_nt:
      forall b1 ofs b2 delta k p,
      f b1 = Some(b2, delta) ->
      perm m2 b2 (ofs + delta) k p ->
      perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty
    }.

Lemma inject_nothread_inv : forall f m1 m2,
    inject f m1 m2 <-> inject_nothread f m1 m2 /\ mem_inj_thread f m1 m2.
Proof.
  intros. split; intros.
  inv H. split. constructor; eauto. auto.
  inv H. inv H0. constructor; eauto.
Qed.
  
Local Hint Resolve mi_mappedblocks: mem.

(** Preservation of access validity and pointer validity *)

Theorem valid_block_inject_1:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m1 b1.
Proof.
  intros. inv H. destruct (sup_dec b1 (support m1)). auto.
  assert (f b1 = None). eapply mi_freeblocks; eauto. congruence.
Qed.

Theorem valid_block_inject_2:
  forall f m1 m2 b1 b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_block m2 b2.
Proof.
  intros. eapply mi_mappedblocks; eauto.
Qed.

Local Hint Resolve valid_block_inject_1 valid_block_inject_2: mem.

Theorem perm_inject:
  forall f m1 m2 b1 b2 delta ofs k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  perm m1 b1 ofs k p -> perm m2 b2 (ofs + delta) k p.
Proof.
  intros. inv H0. eapply perm_inj; eauto.
Qed.

Theorem perm_inject_inv:
  forall f m1 m2 b1 ofs b2 delta k p,
  inject f m1 m2 ->
  f b1 = Some(b2, delta) ->
  perm m2 b2 (ofs + delta) k p ->
  perm m1 b1 ofs k p \/ ~perm m1 b1 ofs Max Nonempty.
Proof.
  intros. eapply mi_perm_inv; eauto.
Qed.

Theorem range_perm_inject:
  forall f m1 m2 b1 b2 delta lo hi k p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  range_perm m1 b1 lo hi k p -> range_perm m2 b2 (lo + delta) (hi + delta) k p.
Proof.
  intros. inv H0. eapply range_perm_inj; eauto.
Qed.

Theorem valid_access_inject:
  forall f m1 m2 chunk b1 ofs b2 delta p,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_access m1 chunk b1 ofs p ->
  valid_access m2 chunk b2 (ofs + delta) p.
Proof.
  intros. eapply valid_access_inj; eauto. apply mi_inj; auto.
Qed.

Theorem valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  valid_pointer m1 b1 ofs = true ->
  valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access.
  eapply valid_access_inject; eauto.
Qed.

Theorem weak_valid_pointer_inject:
  forall f m1 m2 b1 ofs b2 delta,
  f b1 = Some(b2, delta) ->
  inject f m1 m2 ->
  weak_valid_pointer m1 b1 ofs = true ->
  weak_valid_pointer m2 b2 (ofs + delta) = true.
Proof.
  intros until 2. unfold weak_valid_pointer. rewrite !orb_true_iff.
  replace (ofs + delta - 1) with ((ofs - 1) + delta) by lia.
  intros []; eauto using valid_pointer_inject.
Qed.

(** The following lemmas establish the absence of machine integer overflow
  during address computations. *)

Lemma address_inject:
  forall f m1 m2 b1 ofs1 b2 delta p,
  inject f m1 m2 ->
  perm m1 b1 (Ptrofs.unsigned ofs1) Cur p ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros.
  assert (perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty) by eauto with mem.
  exploit mi_representable; eauto. intros [A B].
  assert (0 <= delta <= Ptrofs.max_unsigned).
    generalize (Ptrofs.unsigned_range ofs1). lia.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; lia.
Qed.

Lemma address_inject':
  forall f m1 m2 chunk b1 ofs1 b2 delta,
  inject f m1 m2 ->
  valid_access m1 chunk b1 (Ptrofs.unsigned ofs1) Nonempty ->
  f b1 = Some (b2, delta) ->
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)) = Ptrofs.unsigned ofs1 + delta.
Proof.
  intros. destruct H0. eapply address_inject; eauto.
  apply H0. generalize (size_chunk_pos chunk). lia.
Qed.

Theorem weak_valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  intros. rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  rewrite Ptrofs.unsigned_repr; lia.
Qed.

Theorem valid_pointer_inject_no_overflow:
  forall f m1 m2 b ofs b' delta,
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  f b = Some(b', delta) ->
  0 <= Ptrofs.unsigned ofs + Ptrofs.unsigned (Ptrofs.repr delta) <= Ptrofs.max_unsigned.
Proof.
  eauto using weak_valid_pointer_inject_no_overflow, valid_pointer_implies.
Qed.

Theorem valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  erewrite address_inject'; eauto.
  eapply valid_pointer_inject; eauto.
  rewrite valid_pointer_valid_access in H0. eauto.
Qed.

Theorem weak_valid_pointer_inject_val:
  forall f m1 m2 b ofs b' ofs',
  inject f m1 m2 ->
  weak_valid_pointer m1 b (Ptrofs.unsigned ofs) = true ->
  Val.inject f (Vptr b ofs) (Vptr b' ofs') ->
  weak_valid_pointer m2 b' (Ptrofs.unsigned ofs') = true.
Proof.
  intros. inv H1.
  exploit weak_valid_pointer_inject; eauto. intros W.
  rewrite weak_valid_pointer_spec in H0.
  rewrite ! valid_pointer_nonempty_perm in H0.
  exploit mi_representable; eauto. destruct H0; eauto with mem.
  intros [A B].
  pose proof (Ptrofs.unsigned_range ofs).
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; auto; lia.
Qed.

Theorem inject_no_overlap:
  forall f m1 m2 b1 b2 b1' b2' delta1 delta2 ofs1 ofs2,
  inject f m1 m2 ->
  b1 <> b2 ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  perm m1 b1 ofs1 Max Nonempty ->
  perm m1 b2 ofs2 Max Nonempty ->
  b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
Proof.
  intros. inv H. eapply mi_no_overlap0; eauto.
Qed.

Theorem different_pointers_inject:
  forall f m m' b1 ofs1 b2 ofs2 b1' delta1 b2' delta2,
  inject f m m' ->
  b1 <> b2 ->
  valid_pointer m b1 (Ptrofs.unsigned ofs1) = true ->
  valid_pointer m b2 (Ptrofs.unsigned ofs2) = true ->
  f b1 = Some (b1', delta1) ->
  f b2 = Some (b2', delta2) ->
  b1' <> b2' \/
  Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta1)) <>
  Ptrofs.unsigned (Ptrofs.add ofs2 (Ptrofs.repr delta2)).
Proof.
  intros.
  rewrite valid_pointer_valid_access in H1.
  rewrite valid_pointer_valid_access in H2.
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H1 H3).
  rewrite (address_inject' _ _ _ _ _ _ _ _ H H2 H4).
  inv H1. simpl in H5. inv H2. simpl in H1.
  eapply mi_no_overlap; eauto.
  apply perm_cur_max. apply (H5 (Ptrofs.unsigned ofs1)). lia.
  apply perm_cur_max. apply (H1 (Ptrofs.unsigned ofs2)). lia.
Qed.

Theorem disjoint_or_equal_inject:
  forall f m m' b1 b1' delta1 b2 b2' delta2 ofs1 ofs2 sz,
  inject f m m' ->
  f b1 = Some(b1', delta1) ->
  f b2 = Some(b2', delta2) ->
  range_perm m b1 ofs1 (ofs1 + sz) Max Nonempty ->
  range_perm m b2 ofs2 (ofs2 + sz) Max Nonempty ->
  sz > 0 ->
  b1 <> b2 \/ ofs1 = ofs2 \/ ofs1 + sz <= ofs2 \/ ofs2 + sz <= ofs1 ->
  b1' <> b2' \/ ofs1 + delta1 = ofs2 + delta2
             \/ ofs1 + delta1 + sz <= ofs2 + delta2
             \/ ofs2 + delta2 + sz <= ofs1 + delta1.
Proof.
  intros.
  destruct (eq_block b1 b2).
  assert (b1' = b2') by congruence. assert (delta1 = delta2) by congruence. subst.
  destruct H5. congruence. right. destruct H5. left; congruence. right. lia.
  destruct (eq_block b1' b2'); auto. subst. right. right.
  set (i1 := (ofs1 + delta1, ofs1 + delta1 + sz)).
  set (i2 := (ofs2 + delta2, ofs2 + delta2 + sz)).
  change (snd i1 <= fst i2 \/ snd i2 <= fst i1).
  apply Intv.range_disjoint'; simpl; try lia.
  unfold Intv.disjoint, Intv.In; simpl; intros. red; intros.
  exploit mi_no_overlap; eauto.
  instantiate (1 := x - delta1). apply H2. lia.
  instantiate (1 := x - delta2). apply H3. lia.
  intuition.
Qed.

Theorem aligned_area_inject:
  forall f m m' b ofs al sz b' delta,
  inject f m m' ->
  al = 1 \/ al = 2 \/ al = 4 \/ al = 8 -> sz > 0 ->
  (al | sz) ->
  range_perm m b ofs (ofs + sz) Cur Nonempty ->
  (al | ofs) ->
  f b = Some(b', delta) ->
  (al | ofs + delta).
Proof.
  intros.
  assert (P: al > 0) by lia.
  assert (Q: Z.abs al <= Z.abs sz). apply Zdivide_bounds; auto. lia.
  rewrite Z.abs_eq in Q; try lia. rewrite Z.abs_eq in Q; try lia.
  assert (R: exists chunk, al = align_chunk chunk /\ al = size_chunk chunk).
    destruct H0. subst; exists Mint8unsigned; auto.
    destruct H0. subst; exists Mint16unsigned; auto.
    destruct H0. subst; exists Mint32; auto.
    subst; exists Mint64; auto.
  destruct R as [chunk [A B]].
  assert (valid_access m chunk b ofs Nonempty).
    split. red; intros; apply H3. lia. congruence.
  exploit valid_access_inject; eauto. intros [C D].
  congruence.
Qed.

(** Preservation of loads *)

Theorem load_inject:
  forall f m1 m2 chunk b1 ofs b2 delta v1,
  inject f m1 m2 ->
  load chunk m1 b1 ofs = Some v1 ->
  f b1 = Some (b2, delta) ->
  exists v2, load chunk m2 b2 (ofs + delta) = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H. eapply load_inj; eauto.
Qed.

Theorem loadv_inject:
  forall f m1 m2 chunk a1 a2 v1,
  inject f m1 m2 ->
  loadv chunk m1 a1 = Some v1 ->
  Val.inject f a1 a2 ->
  exists v2, loadv chunk m2 a2 = Some v2 /\ Val.inject f v1 v2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  exploit load_inject; eauto. intros [v2 [LOAD INJ]].
  exists v2; split; auto. unfold loadv.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
     with (Ptrofs.unsigned ofs1 + delta).
  auto. symmetry. eapply address_inject'; eauto with mem.
Qed.

Theorem loadbytes_inject:
  forall f m1 m2 b1 ofs len b2 delta bytes1,
  inject f m1 m2 ->
  loadbytes m1 b1 ofs len = Some bytes1 ->
  f b1 = Some (b2, delta) ->
  exists bytes2, loadbytes m2 b2 (ofs + delta) len = Some bytes2
              /\ list_forall2 (memval_inject f) bytes1 bytes2.
Proof.
  intros. inv H. eapply loadbytes_inj; eauto.
Qed.

(** Preservation of stores *)

Theorem store_mapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  exists n2,
    store chunk m2 b2 (ofs + delta) v2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
  (* thread*)
  inv mi_thread0.
  econstructor; auto.
  erewrite support_store; eauto.
  rewrite (support_store _ _ _ _ _ _ STORE); eauto. 
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H4; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_mapped_inject_rev:
  forall f chunk m1 b1 ofs v1 n2 m2 b2 delta v2,
  inject f m1 m2 ->
  store chunk m2 b2 (ofs + delta) v2 = Some n2 ->
  f b1 = Some (b2, delta) ->
  Val.inject f v1 v2 ->
  valid_access m1 chunk b1 ofs Writable ->
  exists n1,
    store chunk m1 b1 ofs v1 = Some n1
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit store_mapped_inj_rev; eauto. intros [n1 [STORE MI]].
  exists n1; split. eauto. constructor.
  (* thread*)
  inv mi_thread0.
  econstructor; auto.
  erewrite support_store; eauto.
  rewrite (support_store _ _ _ _ _ _ H0); eauto. 
(* inj *)
  auto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H4; eauto with mem.
(* perm inv *)
  intros. simpl. 
  intuition eauto using perm_store_1, perm_store_2.
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_unmapped_inject:
  forall f chunk m1 b1 ofs v1 n1 m2,
  inject f m1 m2 ->
  store chunk m1 b1 ofs v1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
(* thread *)
  inv mi_thread0. econstructor; auto.
  erewrite support_store; eauto.
(* inj *)
  eapply store_unmapped_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable; try eassumption.
  destruct H3; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_store_2.
  intuition eauto using perm_store_1, perm_store_2.
Qed.

Theorem store_outside_inject:
  forall f m1 m2 chunk b ofs v m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + size_chunk chunk -> False) ->
  store chunk m2 b ofs v = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
  inv mi_thread0. constructor; auto.
  rewrite (support_store _ _ _ _ _ _ H1); eauto.
(* inj *)
  eapply store_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  eauto with mem.
(* perm inv *)
  intros. eauto using perm_store_2.
Qed.

Theorem storev_mapped_inject:
  forall f chunk m1 a1 v1 n1 m2 a2 v2,
  inject f m1 m2 ->
  storev chunk m1 a1 v1 = Some n1 ->
  Val.inject f a1 a2 ->
  Val.inject f v1 v2 ->
  exists n2,
    storev chunk m2 a2 v2 = Some n2 /\ inject f n1 n2.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  unfold storev.
  replace (Ptrofs.unsigned (Ptrofs.add ofs1 (Ptrofs.repr delta)))
    with (Ptrofs.unsigned ofs1 + delta).
  eapply store_mapped_inject; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.

Lemma storev_mapped_inject_rev : forall f chunk m1 b i v1 m2 m2' a2 v2,
    inject f m1 m2 ->
    storev chunk m2 a2 v2 = Some m2' ->
    Val.inject f (Vptr b i) a2 -> Val.inject f v1 v2 ->
    valid_access m1 chunk b (Ptrofs.unsigned i) Writable ->    
    exists m1', Mem.storev chunk m1 (Vptr b i) v1 = Some m1' /\ Mem.inject f m1' m2'.
Proof.
  intros. inv H1; simpl in H0; try discriminate.
  unfold storev.
  replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr delta)))
    with (Ptrofs.unsigned i + delta) in H0.
  eapply store_mapped_inject_rev; eauto.
  symmetry. eapply address_inject'; eauto with mem.
Qed.
   
Theorem storebytes_mapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2 b2 delta bytes2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = Some (b2, delta) ->
  list_forall2 (memval_inject f) bytes1 bytes2 ->
  exists n2,
    storebytes m2 b2 (ofs + delta) bytes2 = Some n2
    /\ inject f n1 n2.
Proof.
  intros. inversion H.
  exploit storebytes_mapped_inj; eauto. intros [n2 [STORE MI]].
  exists n2; split. eauto. constructor.
  inv mi_thread0. constructor; auto.
  erewrite support_storebytes; eauto.
  rewrite (support_storebytes _ _ _ _ _ STORE); eauto.
(* inj *)
  auto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H3; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H4; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_unmapped_inject:
  forall f m1 b1 ofs bytes1 n1 m2,
  inject f m1 m2 ->
  storebytes m1 b1 ofs bytes1 = Some n1 ->
  f b1 = None ->
  inject f n1 m2.
Proof.
  intros. inversion H.
  constructor.
  inv mi_thread0. constructor; auto.
  erewrite support_storebytes; eauto.
(* inj *)
  eapply storebytes_unmapped_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

Theorem storebytes_outside_inject:
  forall f m1 m2 b ofs bytes2 m2',
  inject f m1 m2 ->
  (forall b' delta ofs',
    f b' = Some(b, delta) ->
    perm m1 b' ofs' Cur Readable ->
    ofs <= ofs' + delta < ofs + Z.of_nat (length bytes2) -> False) ->
  storebytes m2 b ofs bytes2 = Some m2' ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
  inv mi_thread0. constructor; auto.
  rewrite (support_storebytes _ _ _ _ _ H1); eauto.
(* inj *)
  eapply storebytes_outside_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply mi_perm_inv0; eauto using perm_storebytes_2.
Qed.

Theorem storebytes_empty_inject:
  forall f m1 b1 ofs1 m1' m2 b2 ofs2 m2',
  inject f m1 m2 ->
  storebytes m1 b1 ofs1 nil = Some m1' ->
  storebytes m2 b2 ofs2 nil = Some m2' ->
  inject f m1' m2'.
Proof.
  intros. inversion H. constructor; intros.
  inv mi_thread0. constructor; auto.
  erewrite support_storebytes; eauto.
  rewrite (support_storebytes _ _ _ _ _ H1); eauto.
(* inj *)
  eapply storebytes_empty_inj; eauto.
(* freeblocks *)
  intros. apply mi_freeblocks0. red; intros; elim H2; eapply storebytes_valid_block_1; eauto.
(* mappedblocks *)
  intros. eapply storebytes_valid_block_1; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_storebytes_2; eauto.
(* representable *)
  intros. eapply mi_representable0; eauto.
  destruct H3; eauto using perm_storebytes_2.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto using perm_storebytes_2.
  intuition eauto using perm_storebytes_1, perm_storebytes_2.
Qed.

(* Preservation of allocations *)

Theorem alloc_right_inject:
  forall f m1 m2 lo hi b2 m2',
  inject f m1 m2 ->
  alloc m2 lo hi = (m2', b2) ->
  inject f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
  inv mi_thread0. constructor; auto.
  rewrite (support_alloc _ _ _ _ _ H0); eauto.
  red. simpl. rewrite update_list_length. eauto.
(* inj *)
  eapply alloc_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eapply perm_alloc_inv in H2; eauto. destruct (eq_block b0 b2).
  subst b0. eelim fresh_block_alloc; eauto.
  eapply mi_perm_inv0; eauto.
Qed.

Theorem alloc_left_unmapped_inject:
  forall f m1 m2 lo hi m1' b1,
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = None
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then None else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence. eauto.
    unfold f'; intros. destruct (eq_block b0 b1). congruence.
    apply memval_inject_incr with f; auto.
    exists f'; split. constructor.
    inv mi_thread0. constructor; auto.
  erewrite support_alloc; eauto. red. simpl. rewrite update_list_length.
  auto. red. intros. subst f'. simpl in H3. destruct (eq_block b b1); try congruence.
  eapply Hjs; eauto.
(* inj *)
  eapply alloc_left_unmapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  intros. unfold f'. destruct (eq_block b b1). auto.
  apply mi_freeblocks0. red; intro; elim H3. eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* no overlap *)
  unfold f'; red; intros.
  destruct (eq_block b0 b1); destruct (eq_block b2 b1); try congruence.
  eapply mi_no_overlap0. eexact H3. eauto. eauto.
  exploit perm_alloc_inv. eauto. eexact H6. rewrite dec_eq_false; auto.
  exploit perm_alloc_inv. eauto. eexact H7. rewrite dec_eq_false; auto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1); try discriminate.
  eapply mi_representable0; try eassumption.
  destruct H4; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H3; destruct (eq_block b0 b1); try discriminate.
  exploit mi_perm_inv0; eauto.
  intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image *)
  split. unfold f'; apply dec_eq_true.
(* incr *)
  intros; unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_left_mapped_inject:
  forall f m1 m2 lo hi m1' b1 b2 delta
  (Htb2: fst b2 = Mem.tid (Mem.support m2)),
  inject f m1 m2 ->
  alloc m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  0 <= delta <= Ptrofs.max_unsigned ->
  (forall ofs k p, perm m2 b2 ofs k p -> delta = 0 \/ 0 <= ofs < Ptrofs.max_unsigned) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  inj_offset_aligned delta (hi-lo) ->
  (forall b delta' ofs k p,
   f b = Some (b2, delta') ->
   perm m1 b ofs k p ->
   lo + delta <= ofs + delta' < hi + delta -> False) ->
  exists f',
     inject f' m1' m2
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, delta)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros. inversion H.
  set (f' := fun b => if eq_block b b1 then Some(b2, delta) else f b).
  assert (inject_incr f f').
    red; unfold f'; intros. destruct (eq_block b b1). subst b.
    assert (f b1 = None). eauto with mem. congruence.
    auto.
  assert (mem_inj f' m1 m2).
    inversion mi_inj0; constructor; eauto with mem.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0).
      eapply perm_valid_block with (ofs := ofs). apply H9. generalize (size_chunk_pos chunk); lia.
      eauto.
    unfold f'; intros. destruct (eq_block b0 b1).
      inversion H8. subst b0 b3 delta0.
      elim (fresh_block_alloc _ _ _ _ _ H0). eauto with mem.
      apply memval_inject_incr with f; auto.
      exists f'. split. constructor.
  inv mi_thread0. constructor; auto.
  erewrite support_alloc; eauto. red. simpl. rewrite update_list_length.
  auto. red. intros. subst f'. simpl in H9. destruct (eq_block b b1); inv H9.
  rewrite Htb2. apply alloc_result in H0; eauto. inv Hms. simpl. auto.
  eapply Hjs; eauto.
(* inj *)
  eapply alloc_left_mapped_inj; eauto. unfold f'; apply dec_eq_true.
(* freeblocks *)
  unfold f'; intros. destruct (eq_block b b1). subst b.
  elim H9. eauto with mem.
  eauto with mem.
(* mappedblocks *)
  unfold f'; intros. destruct (eq_block b b1). congruence. eauto.
(* overlap *)
  unfold f'; red; intros.
  exploit perm_alloc_inv. eauto. eexact H12. intros P1.
  exploit perm_alloc_inv. eauto. eexact H13. intros P2.
  destruct (eq_block b0 b1); destruct (eq_block b3 b1).
  congruence.
  inversion H10; subst b0 b1' delta1.
    destruct (eq_block b2 b2'); auto. subst b2'. right; red; intros.
    eapply H6; eauto. lia.
  inversion H11; subst b3 b2' delta2.
    destruct (eq_block b1' b2); auto. subst b1'. right; red; intros.
    eapply H6; eauto. lia.
  eauto.
(* representable *)
  unfold f'; intros.
  destruct (eq_block b b1).
   subst. injection H9; intros; subst b' delta0. destruct H10.
    exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
    exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
    generalize (Ptrofs.unsigned_range_2 ofs). lia.
   exploit perm_alloc_inv; eauto; rewrite dec_eq_true; intro.
   exploit H3. apply H4 with (k := Max) (p := Nonempty); eauto.
   generalize (Ptrofs.unsigned_range_2 ofs). lia.
  eapply mi_representable0; try eassumption.
  destruct H10; eauto using perm_alloc_4.
(* perm inv *)
  intros. unfold f' in H9; destruct (eq_block b0 b1).
  inversion H9; clear H9; subst b0 b3 delta0.
  assert (EITHER: lo <= ofs < hi \/ ~(lo <= ofs < hi)) by lia.
  destruct EITHER.
  left. apply perm_implies with Freeable; auto with mem. eapply perm_alloc_2; eauto.
  right; intros A. eapply perm_alloc_inv in A; eauto. rewrite dec_eq_true in A. tauto.
  exploit mi_perm_inv0; eauto. intuition eauto using perm_alloc_1, perm_alloc_4.
(* incr *)
  split. auto.
(* image of b1 *)
  split. unfold f'; apply dec_eq_true.
(* image of others *)
  intros. unfold f'; apply dec_eq_false; auto.
Qed.

Theorem alloc_parallel_inject:
  forall f m1 m2 lo1 hi1 m1' b1 lo2 hi2,
  inject f m1 m2 ->
  alloc m1 lo1 hi1 = (m1', b1) ->
  lo2 <= lo1 -> hi1 <= hi2 ->
  exists f', exists m2', exists b2,
  alloc m2 lo2 hi2 = (m2', b2)
  /\ inject f' m1' m2'
  /\ inject_incr f f'
  /\ f' b1 = Some(b2, 0)
  /\ (forall b, b <> b1 -> f' b = f b).
Proof.
  intros.
  case_eq (alloc m2 lo2 hi2). intros m2' b2 ALLOC.
  exploit alloc_left_mapped_inject.
  2: eapply alloc_right_inject; eauto.
  apply alloc_result in ALLOC as RES. instantiate (1:= b2). rewrite RES. simpl.
  inv ALLOC. reflexivity.
  eauto.
  eauto with mem.
  instantiate (1 := 0). unfold Ptrofs.max_unsigned. generalize Ptrofs.modulus_pos; lia.
  auto.
  intros. apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. lia.
  red; intros. apply Z.divide_0_r.
  intros. apply (valid_not_valid_diff m2 b2 b2); eauto with mem.
  intros [f' [A [B [C D]]]].
  exists f'; exists m2'; exists b2; auto.
Qed.

(** Preservation of [free] operations *)

Lemma free_left_inject:
  forall f m1 m2 b lo hi m1',
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  inject f m1' m2.
Proof.
  intros. inversion H. constructor.
  inv mi_thread0. constructor; auto.
  erewrite support_free; eauto.
(* inj *)
  eapply free_left_inj; eauto.
(* freeblocks *)
  eauto with mem.
(* mappedblocks *)
  auto.
(* no overlap *)
  red; intros. eauto with mem.
(* representable *)
  intros. eapply mi_representable0; try eassumption.
  destruct H2; eauto with mem.
(* perm inv *)
  intros. exploit mi_perm_inv0; eauto. intuition eauto using perm_free_3.
  eapply perm_free_inv in H4; eauto. destruct H4 as [[A B] | A]; auto.
  subst b1. right; eapply perm_free_2; eauto.
Qed.

Lemma free_list_left_inject:
  forall f m2 l m1 m1',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  inject f m1' m2.
Proof.
  induction l; simpl; intros.
  inv H0. auto.
  destruct a as [[b lo] hi].
  destruct (free m1 b lo hi) as [m11|] eqn:E; try discriminate.
  apply IHl with m11; auto. eapply free_left_inject; eauto.
Qed.

Lemma free_right_inject:
  forall f m1 m2 b lo hi m2',
  inject f m1 m2 ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) -> perm m1 b1 ofs k p ->
    lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. inversion H. constructor.
  inv mi_thread0. constructor; auto.
  erewrite (support_free _ _ _ _ _ H0); eauto.
(* inj *)
  eapply free_right_inj; eauto.
(* freeblocks *)
  auto.
(* mappedblocks *)
  eauto with mem.
(* no overlap *)
  auto.
(* representable *)
  auto.
(* perm inv *)
  intros. eauto using perm_free_3.
Qed.

Lemma perm_free_list:
  forall l m m' b ofs k p,
  free_list m l = Some m' ->
  perm m' b ofs k p ->
  perm m b ofs k p /\
  (forall lo hi, In (b, lo, hi) l -> lo <= ofs < hi -> False).
Proof.
  induction l; simpl; intros.
  inv H. auto.
  destruct a as [[b1 lo1] hi1].
  destruct (free m b1 lo1 hi1) as [m1|] eqn:E; try discriminate.
  exploit IHl; eauto. intros [A B].
  split. eauto with mem.
  intros. destruct H1. inv H1.
  elim (perm_free_2 _ _ _ _ _ E ofs k p). auto. auto.
  eauto.
Qed.

Theorem free_inject:
  forall f m1 l m1' m2 b lo hi m2',
  inject f m1 m2 ->
  free_list m1 l = Some m1' ->
  free m2 b lo hi = Some m2' ->
  (forall b1 delta ofs k p,
    f b1 = Some(b, delta) ->
    perm m1 b1 ofs k p -> lo <= ofs + delta < hi ->
    exists lo1, exists hi1, In (b1, lo1, hi1) l /\ lo1 <= ofs < hi1) ->
  inject f m1' m2'.
Proof.
  intros.
  eapply free_right_inject; eauto.
  eapply free_list_left_inject; eauto.
  intros. exploit perm_free_list; eauto. intros [A B].
  exploit H2; eauto. intros [lo1 [hi1 [C D]]]. eauto.
Qed.

Theorem free_parallel_inject:
  forall f m1 m2 b lo hi m1' b' delta,
  inject f m1 m2 ->
  free m1 b lo hi = Some m1' ->
  f b = Some(b', delta) ->
  exists m2',
     free m2 b' (lo + delta) (hi + delta) = Some m2'
  /\ inject f m1' m2'.
Proof.
  intros.
  destruct (range_perm_free m2 b' (lo + delta) (hi + delta)) as [m2' FREE].
  eapply range_perm_inject; eauto. eapply free_range_perm; eauto.
  exists m2'; split; auto.
  eapply free_inject with (m1 := m1) (l := (b,lo,hi)::nil); eauto.
  simpl; rewrite H0; auto.
  intros. destruct (eq_block b1 b).
  subst b1. rewrite H1 in H2; inv H2.
  exists lo, hi; split; auto with coqlib. lia.
  exploit mi_no_overlap. eexact H. eexact n. eauto. eauto.
  eapply perm_max. eapply perm_implies. eauto. auto with mem.
  instantiate (1 := ofs + delta0 - delta).
  apply perm_cur_max. apply perm_implies with Freeable; auto with mem.
  eapply free_range_perm; eauto. lia.
  intros [A|A]. congruence. lia.
Qed.

Lemma drop_outside_inject: forall f m1 m2 b lo hi p m2',
  inject f m1 m2 ->
  drop_perm m2 b lo hi p = Some m2' ->
  (forall b' delta ofs k p,
    f b' = Some(b, delta) ->
    perm m1 b' ofs k p -> lo <= ofs + delta < hi -> False) ->
  inject f m1 m2'.
Proof.
  intros. destruct H. constructor; eauto.
  inv mi_thread0. constructor; auto.
  erewrite (support_drop _ _ _ _ _ _ H0); eauto.
  eapply drop_outside_inj; eauto.
  intros. unfold valid_block in *. erewrite support_drop; eauto.
  intros. eapply mi_perm_inv0; eauto using perm_drop_4.
Qed.

(** Composing two memory injections. *)

Lemma mem_inj_compose:
  forall f f' m1 m2 m3,
  mem_inj f m1 m2 -> mem_inj f' m2 m3 -> mem_inj (compose_meminj f f') m1 m3.
Proof.
  intros. unfold compose_meminj. inv H; inv H0; constructor; intros.
  (* perm *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
  eauto.
  (* align *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  apply Z.divide_add_r.
  eapply mi_align0; eauto.
  eapply mi_align1 with (ofs := ofs + delta') (p := p); eauto.
  red; intros. replace ofs0 with ((ofs0 - delta') + delta') by lia.
  eapply mi_perm0; eauto. apply H0. lia.
  (* memval *)
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; inv H.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') by lia.
  eapply memval_inject_compose; eauto.
Qed.

Theorem inject_compose:
  forall f f' m1 m2 m3,
  inject f m1 m2 -> inject f' m2 m3 ->
  inject (compose_meminj f f') m1 m3.
Proof.
  unfold compose_meminj; intros.
  inv H; inv H0. constructor.
  inv mi_thread0. inv mi_thread1.
  constructor. auto.
  red. destruct Hms, Hms0. split; congruence.
  red. intros. destruct (f b) as [[bi ?]|] eqn:Hj1; try congruence.
  destruct (f' bi) as [[? ?]|] eqn:Hj2; inv H. apply Hjs in Hj1. apply Hjs0 in Hj2. congruence.
(* inj *)
  eapply mem_inj_compose; eauto.
(* unmapped *)
  intros. erewrite mi_freeblocks0; eauto.
(* mapped *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  eauto.
(* no overlap *)
  red; intros.
  destruct (f b1) as [[b1x delta1x] |] eqn:?; try discriminate.
  destruct (f' b1x) as [[b1y delta1y] |] eqn:?; inv H0.
  destruct (f b2) as [[b2x delta2x] |] eqn:?; try discriminate.
  destruct (f' b2x) as [[b2y delta2y] |] eqn:?; inv H1.
  exploit mi_no_overlap0; eauto. intros A.
  destruct (eq_block b1x b2x).
  subst b1x. destruct A. congruence.
  assert (delta1y = delta2y) by congruence. right; lia.
  exploit mi_no_overlap1. eauto. eauto. eauto.
    eapply perm_inj. eauto. eexact H2. eauto.
    eapply perm_inj. eauto. eexact H3. eauto.
  intuition lia.
(* representable *)
  intros.
  destruct (f b) as [[b1 delta1] |] eqn:?; try discriminate.
  destruct (f' b1) as [[b2 delta2] |] eqn:?; inv H.
  exploit mi_representable0; eauto. intros [A B].
  set (ofs' := Ptrofs.repr (Ptrofs.unsigned ofs + delta1)).
  assert (Ptrofs.unsigned ofs' = Ptrofs.unsigned ofs + delta1).
    unfold ofs'; apply Ptrofs.unsigned_repr. auto.
  exploit mi_representable1. eauto. instantiate (1 := ofs').
  rewrite H.
  replace (Ptrofs.unsigned ofs + delta1 - 1) with
    ((Ptrofs.unsigned ofs - 1) + delta1) by lia.
  destruct H0; eauto using perm_inj.
  rewrite H. lia.
(* perm inv *)
  intros.
  destruct (f b1) as [[b' delta'] |] eqn:?; try discriminate.
  destruct (f' b') as [[b'' delta''] |] eqn:?; try discriminate.
  inversion H; clear H; subst b'' delta.
  replace (ofs + (delta' + delta'')) with ((ofs + delta') + delta'') in H0 by lia.
  exploit mi_perm_inv1; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros. elim A. eapply perm_inj; eauto.
Qed.

Lemma val_lessdef_inject_compose:
  forall f v1 v2 v3,
  Val.lessdef v1 v2 -> Val.inject f v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H. auto. auto.
Qed.

Lemma val_inject_lessdef_compose:
  forall f v1 v2 v3,
  Val.inject f v1 v2 -> Val.lessdef v2 v3 -> Val.inject f v1 v3.
Proof.
  intros. inv H0. auto. inv H. auto.
Qed.

Lemma extends_inject_compose:
  forall f m1 m2 m3,
  extends m1 m2 -> inject f m2 m3 -> inject f m1 m3.
Proof.
  intros. inversion H; inv H0. constructor; intros.
  inv mi_thread0. constructor; auto.
  congruence.
(* inj *)
  replace f with (compose_meminj inject_id f). eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto.
(* unmapped *)
  eapply mi_freeblocks0. erewrite <- valid_block_extends; eauto.
(* mapped *)
  eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto; eapply perm_extends; eauto.
(* representable *)
  eapply mi_representable0; eauto.
  destruct H1; eauto using perm_extends.
(* perm inv *)
  exploit mi_perm_inv0; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
Qed.

Lemma inject_extends_compose:
  forall f m1 m2 m3,
  inject f m1 m2 -> extends m2 m3 -> inject f m1 m3.
Proof.
  intros. inv H; inversion H0. constructor; intros.
  inv mi_thread0. constructor; auto.
  congruence.
(* inj *)
  replace f with (compose_meminj f inject_id). eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id.
  destruct (f x) as [[y delta] | ]; auto. decEq. decEq. lia.
(* unmapped *)
  eauto.
(* mapped *)
  erewrite <- valid_block_extends; eauto.
(* no overlap *)
  red; intros. eapply mi_no_overlap0; eauto.
(* representable *)
  eapply mi_representable0; eauto.
(* perm inv *)
  exploit mext_perm_inv0; eauto. intros [A|A].
  eapply mi_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_inj; eauto.
Qed.

Lemma extends_extends_compose:
  forall m1 m2 m3,
  extends m1 m2 -> extends m2 m3 -> extends m1 m3.
Proof.
  intros. inversion H; subst; inv H0; constructor; intros.
  (* nextblock *)
  congruence.
  (* meminj *)
  replace inject_id with (compose_meminj inject_id inject_id).
  eapply mem_inj_compose; eauto.
  apply extensionality; intros. unfold compose_meminj, inject_id. auto.
  (* perm inv *)
  exploit mext_perm_inv1; eauto. intros [A|A].
  eapply mext_perm_inv0; eauto.
  right; red; intros; elim A. eapply perm_extends; eauto.
Qed.

(** Injecting a memory into itself. *)

Definition flat_inj (s: sup) : meminj :=
  fun (b: block) => if sup_dec b s then Some(b, 0) else None.

Definition inject_neutral (s: sup) (m: mem) :=
  mem_inj (flat_inj s) m m.

Remark flat_inj_no_overlap:
  forall s m, meminj_no_overlap (flat_inj s) m.
Proof.
  unfold flat_inj; intros; red; intros.
  destruct (sup_dec b1 s); inversion H0; subst.
  destruct (sup_dec b2 s); inversion H1; subst.
  auto.
Qed.

Theorem neutral_inject:
  forall m, inject_neutral (support m) m -> inject (flat_inj (support m)) m m.
Proof.
  intros. constructor.
  constructor.
  split; eauto. red. intros. unfold flat_inj in H0.
  destruct sup_dec; inv H0. reflexivity.
(* meminj *)
  auto.
(* freeblocks *)
  unfold flat_inj, valid_block; intros.
  apply pred_dec_false. auto.
(* mappedblocks *)
  unfold flat_inj, valid_block; intros.
  destruct (sup_dec b (support m)); inversion H0; subst. auto.
(* no overlap *)
  apply flat_inj_no_overlap.
(* range *)
  unfold flat_inj; intros.
  destruct (sup_dec b (support m)); inv H0. generalize (Ptrofs.unsigned_range_2 ofs); lia.
(* perm inv *)
  unfold flat_inj; intros.
  destruct (sup_dec b1 (support m)); inv H0.
  rewrite Z.add_0_r in H1; auto.
Qed.

Theorem empty_inject_neutral:
  forall s, inject_neutral s empty.
Proof.
  intros; red; constructor.
(* perm *)
  unfold flat_inj; intros. destruct (sup_dec b1 s); inv H.
  replace (ofs + 0) with ofs by lia; auto.
(* align *)
  unfold flat_inj; intros. destruct (sup_dec b1 s); inv H. apply Z.divide_0_r.
(* mem_contents *)
  intros; simpl. unfold NMap.get. rewrite ! NMap.gi. rewrite ! ZMap.gi. constructor.
Qed.

Theorem alloc_inject_neutral:
  forall s m lo hi b m',
  alloc m lo hi = (m', b) ->
  inject_neutral s m ->
  sup_include (sup_incr (support m)) s ->
  inject_neutral s m'.
Proof.
  intros; red.
  eapply alloc_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0).
  eapply alloc_right_inj; eauto. eauto. eauto with mem.
  red. intros. apply Z.divide_0_r.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_2; eauto. lia.
  unfold flat_inj. apply pred_dec_true.
  apply H1. apply alloc_result in H. subst.
  apply sup_incr_in1.
Qed.

Lemma alloc_global_right_inj:
  forall f m1 m2 lo hi b2 m2',
  mem_inj f m1 m2 ->
  alloc_global m2 lo hi = (m2', b2) ->
  mem_inj f m1 m2'.
Proof.
  intros. injection H0. intros NEXT MEM.
  inversion H. constructor.
(* perm *)
  intros. eapply perm_alloc_global_1; eauto.
(* align *)
  eauto.
(* mem_contents *)
  intros.
  assert (perm m2 b0 (ofs + delta) Cur Readable).
    eapply mi_perm0; eauto.
  assert (valid_block m2 b0) by eauto with mem.
  rewrite <- MEM; simpl. setoid_rewrite NMap.gso. eauto with mem.
  rewrite NEXT. eapply valid_not_valid_diff; eauto with mem. eapply fresh_block_alloc_global; eauto.
Qed.

Lemma alloc_global_left_mapped_inj:
  forall f m1 m2 lo hi m1' b1 b2 delta,
  mem_inj f m1 m2 ->
  alloc_global m1 lo hi = (m1', b1) ->
  valid_block m2 b2 ->
  inj_offset_aligned delta (hi-lo) ->
  (forall ofs k p, lo <= ofs < hi -> perm m2 b2 (ofs + delta) k p) ->
  f b1 = Some(b2, delta) ->
  mem_inj f m1' m2.
Proof.
  intros. inversion H. constructor.
(* perm *)
  intros.
  exploit perm_alloc_global_inv; eauto. intros. destruct (eq_block b0 b1). subst b0.
  rewrite H4 in H5; inv H5. eauto. eauto.
(* align *)
  intros. destruct (eq_block b0 b1).
  subst b0. assert (delta0 = delta) by congruence. subst delta0.
  assert (lo <= ofs < hi).
  { eapply perm_alloc_global_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  assert (lo <= ofs + size_chunk chunk - 1 < hi).
  { eapply perm_alloc_global_3; eauto. apply H6. generalize (size_chunk_pos chunk); lia. }
  apply H2. lia.
  eapply mi_align0 with (ofs := ofs) (p := p); eauto.
  red; intros. eapply perm_alloc_global_4; eauto.
(* mem_contents *)
  injection H0; intros NEXT MEM.
  intros. rewrite <- MEM; simpl. rewrite NEXT.
  exploit perm_alloc_global_inv; eauto. intros.
  rewrite NMap.gsspec.
  destruct (NMap.elt_eq b0 b1). rewrite ZMap.gi. constructor.
  apply mi_memval. auto. auto. eapply perm_alloc_global_4 in H0. eauto. auto. auto.
Qed.

Theorem alloc_global_inject_neutral:
  forall s m lo hi b m',
  alloc_global m lo hi = (m', b) ->
  inject_neutral s m ->
  sup_include (sup_incr_tid (support m) 0) s ->
  inject_neutral s m'.
Proof.
  intros; red.
  eapply alloc_global_left_mapped_inj with (m1 := m) (b2 := b) (delta := 0).
  eapply alloc_global_right_inj; eauto. eauto.
  eapply valid_new_global_block; eauto.
  red. intros. apply Z.divide_0_r.
  intros.
  apply perm_implies with Freeable; auto with mem.
  eapply perm_alloc_global_2; eauto. lia.
  unfold flat_inj. apply pred_dec_true.
  apply H1. apply alloc_global_result in H. subst.
  apply sup_incr_tid_in1. red. generalize (tid_valid (support m)). lia.
Qed.

Theorem store_inject_neutral:
  forall chunk m b ofs v m' s,
  store chunk m b ofs v = Some m' ->
  inject_neutral s m ->
  sup_In b s->
  Val.inject (flat_inj s) v v ->
  inject_neutral s m'.
Proof.
  intros; red.
  exploit store_mapped_inj. eauto. eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; auto. eauto.
  replace (ofs + 0) with ofs by lia.
  intros [m'' [A B]]. congruence.
Qed.

Theorem drop_inject_neutral:
  forall m b lo hi p m' s,
  drop_perm m b lo hi p = Some m' ->
  inject_neutral s m ->
  sup_In b s ->
  inject_neutral s m'.
Proof.
  unfold inject_neutral; intros.
  exploit drop_mapped_inj; eauto. apply flat_inj_no_overlap.
  unfold flat_inj. apply pred_dec_true; eauto.
  repeat rewrite Z.add_0_r. intros [m'' [A B]]. congruence.
Qed.

(** * Invariance properties between two memory states *)

Section UNCHANGED_ON.

Variable P: block -> Z -> Prop.

Record unchanged_on (m_before m_after: mem) : Prop := mk_unchanged_on {
  unchanged_on_support:
    sup_include (support m_before) (support m_after);
  unchanged_on_perm:
    forall b ofs k p,
    P b ofs -> valid_block m_before b ->
    (perm m_before b ofs k p <-> perm m_after b ofs k p);
  unchanged_on_contents:
    forall b ofs,
    P b ofs -> perm m_before b ofs Cur Readable ->
    ZMap.get ofs (NMap.get _ b m_after.(mem_contents)) =
    ZMap.get ofs (NMap.get _ b m_before.(mem_contents))
}.

Lemma unchanged_on_refl:
  forall m, unchanged_on m m.
Proof.
  intros; constructor. auto. apply sup_include_refl. tauto. tauto.
Qed.

Lemma valid_block_unchanged_on:
  forall m m' b,
  unchanged_on m m' -> valid_block m b -> valid_block m' b.
Proof.
  unfold valid_block; intros. apply unchanged_on_support in H. auto.
Qed.

Lemma perm_unchanged_on:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs ->
  perm m b ofs k p -> perm m' b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto. eapply perm_valid_block; eauto.
Qed.

Lemma perm_unchanged_on_2:
  forall m m' b ofs k p,
  unchanged_on m m' -> P b ofs -> valid_block m b ->
  perm m' b ofs k p -> perm m b ofs k p.
Proof.
  intros. destruct H. apply unchanged_on_perm0; auto.
Qed.

Lemma unchanged_on_trans:
  forall m1 m2 m3, unchanged_on m1 m2 -> unchanged_on m2 m3 -> unchanged_on m1 m3.
Proof.
  intros; constructor.
- apply sup_include_trans with (support m2); apply unchanged_on_support; auto.
- intros. transitivity (perm m2 b ofs k p); apply unchanged_on_perm; auto.
  eapply valid_block_unchanged_on; eauto.
- intros. transitivity (ZMap.get ofs (mem_contents m2)#b); apply unchanged_on_contents; auto.
  eapply perm_unchanged_on; eauto.
Qed.

Lemma loadbytes_unchanged_on_1:
  forall m m' b ofs n,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m' b ofs n = loadbytes m b ofs n.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite ! loadbytes_empty by assumption. auto.
+ unfold loadbytes. destruct H.
  destruct (range_perm_dec m b ofs (ofs + n) Cur Readable).
  rewrite pred_dec_true. f_equal.
  apply getN_exten. intros. rewrite Z2Nat.id in H by lia.
  apply unchanged_on_contents0; auto.
  red; intros. apply unchanged_on_perm0; auto.
  rewrite pred_dec_false. auto.
  red; intros; elim n0; red; intros. apply <- unchanged_on_perm0; auto.
Qed.

Lemma loadbytes_unchanged_on:
  forall m m' b ofs n bytes,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + n -> P b i) ->
  loadbytes m b ofs n = Some bytes ->
  loadbytes m' b ofs n = Some bytes.
Proof.
  intros.
  destruct (zle n 0).
+ erewrite loadbytes_empty in * by assumption. auto.
+ rewrite <- H1. apply loadbytes_unchanged_on_1; auto.
  exploit loadbytes_range_perm; eauto. instantiate (1 := ofs). lia.
  intros. eauto with mem.
Qed.

Lemma load_unchanged_on_1:
  forall m m' chunk b ofs,
  unchanged_on m m' ->
  valid_block m b ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m' b ofs = load chunk m b ofs.
Proof.
  intros. unfold load. destruct (valid_access_dec m chunk b ofs Readable).
  destruct v. rewrite pred_dec_true. f_equal. f_equal. apply getN_exten. intros.
  rewrite <- size_chunk_conv in H4. eapply unchanged_on_contents; eauto.
  split; auto. red; intros. eapply perm_unchanged_on; eauto.
  rewrite pred_dec_false. auto.
  red; intros [A B]; elim n; split; auto. red; intros; eapply perm_unchanged_on_2; eauto.
Qed.

Lemma load_unchanged_on:
  forall m m' chunk b ofs v,
  unchanged_on m m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> P b i) ->
  load chunk m b ofs = Some v ->
  load chunk m' b ofs = Some v.
Proof.
  intros. rewrite <- H1. eapply load_unchanged_on_1; eauto with mem.
Qed.

Lemma store_unchanged_on:
  forall chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_store _ _ _ _ _ _ H). apply sup_include_refl.
- split; intros; eauto with mem.
- erewrite store_mem_contents; eauto. rewrite NMap.gsspec.
  destruct (NMap.elt_eq b0 b); auto. subst b0. apply setN_outside.
  rewrite encode_val_length. rewrite <- size_chunk_conv.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + size_chunk chunk)); auto.
  elim (H0 ofs0). lia. auto.
Qed.

Lemma storebytes_unchanged_on:
  forall m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_storebytes _ _ _ _ _ H). apply sup_include_refl.
- split; intros. eapply perm_storebytes_1; eauto. eapply perm_storebytes_2; eauto.
- erewrite storebytes_mem_contents; eauto. rewrite NMap.gsspec.
  destruct (NMap.elt_eq b0 b); auto. subst b0. apply setN_outside.
  destruct (zlt ofs0 ofs); auto.
  destruct (zlt ofs0 (ofs + Z.of_nat (length bytes))); auto.
  elim (H0 ofs0). lia. auto.
Qed.


Lemma alloc_unchanged_on:
  forall m lo hi m' b,
  alloc m lo hi = (m', b) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_alloc _ _ _ _ _ H). intro. intro. apply sup_incr_in2. auto.
- split; intros.
  eapply perm_alloc_1; eauto.
  eapply perm_alloc_4; eauto.
  eapply valid_not_valid_diff; eauto with mem.
- injection H; intros A B. rewrite <- B; simpl.
  setoid_rewrite NMap.gso; auto. rewrite A.  eapply valid_not_valid_diff; eauto with mem.
Qed.

Lemma alloc_global_unchanged_on:
  forall m lo hi m' b,
  alloc_global m lo hi = (m', b) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_alloc_global _ _ _ _ _ H). intro. intro. apply sup_incr_tid_in2.
  red. generalize (tid_valid (support m)). lia. auto.
- split; intros.
  eapply perm_alloc_global_1; eauto.
  eapply perm_alloc_global_4; eauto.
  eapply valid_not_valid_diff. eauto. eapply fresh_block_alloc_global; eauto.
- injection H; intros A B. rewrite <- B; simpl.
  setoid_rewrite NMap.gso; auto. rewrite A.  eapply valid_not_valid_diff. eauto with mem.
  eapply fresh_block_alloc_global; eauto.
Qed.

Lemma free_unchanged_on:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_free _ _ _ _ _ H). apply sup_include_refl.
- split; intros.
  eapply perm_free_1; eauto.
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
  subst b0. elim (H0 ofs). lia. auto.
  eapply perm_free_3; eauto.
- unfold free in H. destruct (range_perm_dec m b lo hi Cur Freeable); inv H.
  simpl. auto.
Qed.

Lemma free_unchanged_on':
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m' m.
Proof.
  intros; constructor; intros.
- rewrite (support_free _ _ _ _ _ H). apply sup_include_refl.
- split; intros.
  eapply perm_free_3; eauto.
  eapply perm_free_1; eauto.
  destruct (eq_block b0 b); auto. destruct (zlt ofs lo); auto. destruct (zle hi ofs); auto.
  subst b0. elim (H0 ofs). lia. auto.
- unfold free in H. destruct (range_perm_dec m b lo hi Cur Freeable); inv H.
  simpl. auto.
Qed.

Lemma drop_perm_unchanged_on:
  forall m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_drop _ _ _ _ _ _ H). apply sup_include_refl.
- split; intros. eapply perm_drop_3; eauto.
  destruct (eq_block b0 b); auto.
  subst b0.
  assert (~ (lo <= ofs < hi)). { red; intros; eelim H0; eauto. }
  right; lia.
  eapply perm_drop_4; eauto.
- unfold drop_perm in H.
  destruct (range_perm_dec m b lo hi Cur Freeable); inv H; simpl. auto.
Qed.

Lemma setN_remain_same: forall A vl ofs ofs0 (c1 c2: ZMap.t A),
      c1 ## ofs0 = c2 ## ofs0 ->
      (setN vl ofs c1) ## ofs0 = (setN vl ofs c2) ## ofs0.
Proof.
  induction vl; intros; simpl; eauto.
  eapply IHvl; eauto.
  destruct (ZMap.elt_eq ofs ofs0).
  subst. rewrite !ZMap.gss; eauto.
  rewrite !ZMap.gso; eauto.
Qed.

Lemma store_mapped_unchanged_on:
  forall (chunk : memory_chunk) (m1 : mem) (b : block) (ofs : Z) (v : val)
    (n1 m2 : mem),
    unchanged_on m1 m2 ->
    (forall ofs', P b ofs') ->
    store chunk m1 b ofs v = Some n1 ->
    exists n2 : mem, store chunk m2 b ofs v = Some n2 /\
                unchanged_on n1 n2.
Proof.
  intros chunk m1 b ofs v n1 m2 UNC1 HP STORE1.
  assert ({n2| store chunk m2 b ofs v = Some n2}).
  { apply valid_access_store.
    apply store_valid_access_3 in STORE1 as ACC1.
    destruct ACC1 as [RANGE1 ALIGN].
    split; eauto.
    red. red in RANGE1.
    intros.
    inversion UNC1.
    eapply unchanged_on_perm0; eauto.
    eapply perm_valid_block. eapply RANGE1. instantiate (1:= ofs). lia.
  }
  destruct X as [n2 STORE2].
  apply support_store in STORE1 as SUP1. apply support_store in STORE2 as SUP2.
  exists n2. split. auto. inversion UNC1.
  constructor.
  - rewrite SUP1, SUP2. eauto.
  - intros. split; intros.
    eapply perm_store_1; eauto. eapply unchanged_on_perm0; eauto.
    unfold valid_block in *. congruence. eapply perm_store_2; eauto.
    eapply perm_store_1; eauto. eapply unchanged_on_perm0; eauto.
    unfold valid_block in *. congruence. eapply perm_store_2; eauto.
  - intros.
    exploit unchanged_on_contents0; eauto.
    eapply Mem.perm_store_2; eauto.
    intros.
    unfold store in STORE1, STORE2.
    destruct valid_access_dec in STORE1; try congruence.
    destruct valid_access_dec in STORE2; try congruence.
    inv STORE1. inv STORE2. cbn in *.
    unfold perm in H0. simpl in H0.
    destruct (eq_block b b0). subst.
    rewrite !NMap.gss.
    eapply setN_remain_same; eauto.
    rewrite !NMap.gso; eauto.
Qed.

Lemma free_mapped_unchanged_on : forall m1 b lo hi m2 n1,
           unchanged_on m1 m2 ->
           (forall ofs, lo <= ofs < hi -> P b ofs) ->
           free m1 b lo hi = Some n1 ->
           exists n2, free m2 b lo hi = Some n2
                 /\ unchanged_on n1 n2.
Proof.
  intros m1 b lo hi m2 n1 UNC1 HP FREE1.
  assert ({n2| free m2 b lo hi  = Some n2}).
  { apply range_perm_free.
    apply free_range_perm in FREE1 as RANGE1.
    red. red in RANGE1.
    intros.
    inversion UNC1.
    eapply unchanged_on_perm0; eauto.
    eapply perm_valid_block. eapply RANGE1. instantiate (1:= ofs). lia.
  }
  destruct X as [n2 FREE2].
  apply support_free in FREE1 as SUP1. apply support_free in FREE2 as SUP2.
  exists n2. split. auto. inversion UNC1.
  constructor.
  - rewrite SUP1, SUP2. eauto.
  - intros.
    apply free_result in FREE1. apply free_result in FREE2.
    subst. unfold perm. cbn.
    destruct (eq_block b0 b); auto.
    + (*same block*) subst.
       rewrite !NMap.gss.
      destruct (zle lo ofs); destruct (zle hi ofs); auto.
      -- rewrite !setpermN_outside; try lia. eauto.
      -- rewrite !setpermN_inside; try lia. reflexivity.
      -- rewrite !setpermN_outside; try lia. eauto.
      -- rewrite !setpermN_outside; try lia. eauto.
    + rewrite !NMap.gso; eauto.
  - intros. apply free_result in FREE1 as RES1. apply free_result in FREE2.
    subst. simpl. eapply unchanged_on_contents0; eauto.
    eapply Mem.perm_free_3; eauto.
Qed.

End UNCHANGED_ON.

Section UNCHANGED_ON_THREAD.

Variable P: block -> Z -> Prop.
  
(** the unchanged_on relations for multi-threading,
    used for small-step internal execution and big-step context switch *)

(** The P is interpreted as [private] memory regions according to injp *)
Definition thread_internal_P (m : mem) :=
  fun b ofs => P b ofs /\ fst b = tid (support m).

Definition thread_external_P (m: mem) :=
  fun b ofs => P b ofs /\ fst b <> tid (support m).

(** Thread-local accessbility, no more threads are introduced *)
(** can be used for builtin calls in Events.v *)
Record unchanged_on_tl (m_before m_after: mem) : Prop := mk_unchanged_on_tl {
  unchanged_on_thread_tl:
    match_sup (support m_before) (support m_after);
  unchanged_on_tl':
    unchanged_on P m_before m_after
}.

(** A general big_step accessbility, more threads can be introduced. 
     *)
Record unchanged_on_big (m_before m_after: mem) : Prop := mk_unchanged_on_big {
  unchanged_on_thread_big:
    tid (support m_before) = tid (support m_after);
  unchanged_on_big':
    unchanged_on P m_before m_after
}.

(** The internal execution of a thread: all private memory of [other] threads *)
Record unchanged_on_i (m_before m_after: mem) : Prop := mk_unchanged_on_i {
  unchanged_on_thread_i:
    match_sup (support m_before) (support m_after);
  unchanged_on_i':
    unchanged_on (thread_external_P m_before) m_before m_after
}.

Definition match_sup_e (s1 s2 : sup) :=
  (length (stacks s1) <= length (stacks s2))%nat /\ tid s1 = tid s2.

(** The external context switch : other threads should not modify [my] private memory *)
Record unchanged_on_e (m_before m_after: mem) : Prop := mk_unchanged_on_e {
  unchanged_on_thread_e:
    match_sup_e (support m_before) (support m_after);
  unchanged_on_e':
    unchanged_on (thread_internal_P m_before) m_before m_after
}.


Lemma unchanged_on_refl_i: 
  forall m, unchanged_on_i m m.
Proof.
  intros; constructor. apply match_sup_refl. apply unchanged_on_refl.
Qed.

Lemma unchanged_on_refl_tl: 
  forall m, unchanged_on_tl m m.
Proof.
  intros; constructor. apply match_sup_refl. apply unchanged_on_refl.
Qed.

Lemma store_unchanged_on_tl:
  forall chunk m b ofs v m',
  store chunk m b ofs v = Some m' ->
  (forall i, ofs <= i < ofs + size_chunk chunk -> ~ P b i) ->
  unchanged_on_tl m m'.
Proof.
  intros; constructor; intros.
  - rewrite (support_store _ _ _ _ _ _ H); eauto. apply match_sup_refl.
  - eapply store_unchanged_on; eauto.
Qed.

Lemma storebytes_unchanged_on_tl:
  forall m b ofs bytes m',
  storebytes m b ofs bytes = Some m' ->
  (forall i, ofs <= i < ofs + Z.of_nat (length bytes) -> ~ P b i) ->
  unchanged_on_tl m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_storebytes _ _ _ _ _ H). red. auto.
- eapply storebytes_unchanged_on; eauto.
Qed.

Lemma alloc_unchanged_on_tl:
  forall m lo hi m' b,
  alloc m lo hi = (m', b) ->
  unchanged_on_tl m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_alloc _ _ _ _ _ H). red. simpl. rewrite update_list_length. auto.
- eapply alloc_unchanged_on; eauto.
Qed.

Lemma free_unchanged_on_tl:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on_tl m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_free _ _ _ _ _ H). apply match_sup_refl.
- eapply free_unchanged_on; eauto. 
Qed.

Lemma free_unchanged_on'_tl:
  forall m b lo hi m',
  free m b lo hi = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on_tl m' m.
Proof.
  intros; constructor; intros.
- rewrite (support_free _ _ _ _ _ H). apply match_sup_refl.
- eapply free_unchanged_on'; eauto.
Qed.

Lemma drop_perm_unchanged_on_tl:
  forall m b lo hi p m',
  drop_perm m b lo hi p = Some m' ->
  (forall i, lo <= i < hi -> ~ P b i) ->
  unchanged_on_tl m m'.
Proof.
  intros; constructor; intros.
- rewrite (support_drop _ _ _ _ _ _ H). apply match_sup_refl.
- eapply drop_perm_unchanged_on; eauto.
Qed.

Lemma unchanged_on_tl_big : forall m1 m2,
    unchanged_on_tl m1 m2 ->
    unchanged_on_big m1 m2.
Proof.
  intros. inv H. constructor; auto.
  inv unchanged_on_thread_tl0. auto.
Qed.

End UNCHANGED_ON_THREAD.

Lemma unchanged_on_implies:
  forall (P Q: block -> Z -> Prop) m m',
  unchanged_on P m m' ->
  (forall b ofs, Q b ofs -> valid_block m b -> P b ofs) ->
  unchanged_on Q m m'.
Proof.
  intros. destruct H. constructor; intros.
  - auto.
  - apply unchanged_on_perm0; auto.
  - apply unchanged_on_contents0; auto.
    apply H0; auto. eapply perm_valid_block; eauto.
Qed.

(** * memory accessibility relations that remain valid during memory operations *)

(** ro_unchanged *)
Definition ro_unchanged m1 m2 : Prop :=
   forall b ofs n bytes, valid_block m1 b ->
                      loadbytes m2 b ofs n = Some bytes ->
                      (forall i, ofs <= i < ofs + n -> ~ perm m1 b i Max Writable) ->
                      loadbytes m1 b ofs n = Some bytes.

Definition ro_unchanged_memval m m' : Prop :=
    forall b ofs,
      valid_block m b ->
      perm m' b ofs Cur Readable ->
      ~ perm m b ofs Max Writable ->
      perm m b ofs Cur Readable /\
        ZMap.get ofs (NMap.get _ b (mem_contents m)) = ZMap.get ofs (NMap.get _ b (mem_contents m')).

Lemma ro_unchanged_memval_bytes: forall m m',
    ro_unchanged m m' <-> ro_unchanged_memval m m'.
Proof.
  intros. split.
  - intros. red in H. red. intros.
    exploit H. eauto. instantiate (2:= 1).
    instantiate (2:= ofs). instantiate (1:= ZMap.get ofs (NMap.get _ b (mem_contents m')) :: nil).
    unfold loadbytes. destruct range_perm_dec.
    simpl. reflexivity. exfalso. apply n. red.
    intros. destruct (zeq ofs0 ofs). subst. eauto. extlia.
    intros. destruct (zeq i ofs). subst. eauto. extlia.
    intro LOAD.
    unfold loadbytes in LOAD. destruct range_perm_dec; try congruence.
    split. apply r. lia. simpl in LOAD. congruence.
  - intros. red in H. red. intros. destruct (zlt 0 n).
    + (* n ≥ 0 *)
      unfold loadbytes in *; simpl in H1. destruct range_perm_dec; try congruence.
      rewrite pred_dec_true. inv H1. f_equal.
      apply getN_exten. intros. rewrite Z2Nat.id in H1; try lia.
      exploit H; eauto. intros [A B]. eauto.
      red. intros. exploit H. eauto. eapply r. instantiate (1:= ofs0). lia.
      eapply H2; eauto. intros [A B]. eauto.
    + (* n < 0 *)
      unfold loadbytes in *; simpl in H1. destruct range_perm_dec; try congruence.
      rewrite Z_to_nat_neg in H1; try lia. simpl in H1. inv H1.
      rewrite pred_dec_true. rewrite Z_to_nat_neg. simpl. reflexivity. lia.
      red. intros. extlia.
Qed.

Lemma ro_unchanged_alloc : forall m m' lo hi b,
    alloc m lo hi = (m',b) -> ro_unchanged m m'.
Proof.
  intros. red. intros. erewrite <- Mem.loadbytes_alloc_unchanged; eauto.
Qed.

Lemma ro_unchanged_free : forall m m' b lo hi,
    free m b lo hi = Some m' -> ro_unchanged m m'.
Proof.
  intros. red. intros. eapply loadbytes_free_2; eauto.
Qed.

Lemma ro_unchanged_free_list : forall l m m',
    free_list m l = Some m' -> ro_unchanged m m'.
Proof.
  induction l; intros; simpl in H.
  inv H. red. intros. eauto.
  destruct a. destruct p. destruct free eqn:F; inv H.
  red. intros. apply ro_unchanged_free in F as FUNC.
  eapply FUNC; eauto. eapply IHl in H0; eauto.
  eapply H0; eauto. intros.
  intro. eapply H2; eauto. eapply perm_free_3; eauto.
  eapply valid_block_free_1; eauto.
Qed.
  
Lemma ro_unchanged_store : forall m m' chunk ofs b v,
    store chunk m b ofs v = Some m' -> ro_unchanged m m'.
Proof.
  intros. red. intros. erewrite <- loadbytes_store_other; eauto.
  apply store_valid_access_3 in H. destruct H. red in H.
  destruct (eq_block b b0).
    + subst. right.
      destruct (Z_le_gt_dec n 0). left. auto.
      right.
      destruct (Z_le_gt_dec (ofs0+n) ofs).
      left. auto.
      destruct (Z_le_gt_dec (ofs + size_chunk chunk) ofs0).
      right. auto.
      exfalso.
      destruct (Z_le_gt_dec ofs ofs0).
      exploit H. instantiate (1:= ofs0). lia. intro PERM.
      exploit H2. instantiate (1:= ofs0). lia.  eauto with mem. auto.
      exploit H. instantiate (1:= ofs). destruct chunk; simpl; lia. intro PERM.
      exploit H2. instantiate (1:= ofs). lia. eauto with mem. auto.
    + left. auto.
Qed.

Lemma ro_unchanged_storebytes :forall m m' b ofs bytes,
    storebytes m b ofs bytes = Some m' -> ro_unchanged m m'.
Proof.
  intros. red. intros.
  destruct (Z_le_gt_dec n 0).
    rewrite Mem.loadbytes_empty in H1; eauto. inv H1.
    rewrite Mem.loadbytes_empty. eauto. auto.
    destruct (Z_le_gt_dec (Z.of_nat (Datatypes.length bytes)) 0).
    destruct bytes. simpl in l. inv H.
    assert (m = m'). {
      eapply Mem.storebytes_empty; eauto.
    }
    subst. eauto. cbn in l. extlia.
    erewrite <- Mem.loadbytes_storebytes_other; eauto. lia.
    apply Mem.storebytes_range_perm in H. red in H.
    destruct (eq_block b0 b). subst. right.
    destruct (Z_le_gt_dec (ofs0+n) ofs).
    left. auto.
    destruct (Z_le_gt_dec (ofs + Z.of_nat (Datatypes.length bytes)) ofs0).
    right. auto.
    exfalso.
    destruct (Z_le_gt_dec ofs ofs0).
    exploit H. instantiate (1:= ofs0). lia. intro PERM.
    exploit H2. instantiate (1:= ofs0). lia.  eauto with mem. auto.
    exploit H. instantiate (1:= ofs). lia. intro PERM.
    exploit H2. instantiate (1:= ofs). lia. eauto with mem. auto.
    left. auto.
Qed.

Definition max_perm_decrease (m m': mem) :=
  forall b ofs p,
    Mem.valid_block m b ->
    Mem.perm m' b ofs Max p ->
    Mem.perm m b ofs Max p.

Lemma ro_unchanged_trans: forall m1 m2 m3,
    ro_unchanged m1 m2 -> ro_unchanged m2 m3 ->
    sup_include (support m1) (support m2) ->
    max_perm_decrease m1 m2 ->
    ro_unchanged m1 m3.
Proof.
  intros. red. intros. eapply H; eauto.
  eapply H0; eauto. eapply H1; eauto.
  intros. intro. eapply H5; eauto.
Qed.

(** max_perm_decrease *)

(** sup_include *)

(* All these three relations can be combind together to form a PreOrder,
  which can be further used to state a invariant (self-sim) for all internal
  semantics. Later we may need this.
*)
                           






(** * setN' operation on ZMap.t *)

Fixpoint setN' {A:Type} (elements : list (Z*A)) (c: ZMap.t A) {struct elements} :=
  match elements with
    | nil => c
    | (z, a) :: elements' => setN' elements' (ZMap.set z a c)
  end.

Remark setN'_default:
  forall (A:Type) vl (c: ZMap.t A), fst (setN' vl c) = fst c.
Proof.
  induction vl; simpl; intros. auto. destruct a. rewrite IHvl. auto.
Qed.

Lemma setN'_outside:
  forall (A:Type) vl (c:ZMap.t A) (z: Z),
    ~ In z (List.map fst vl) -> ZMap.get z (setN' vl c) = ZMap.get z c.
Proof.
  induction vl; intros; simpl; auto.
  destruct a. simpl in *.
  transitivity (ZMap.get z (ZMap.set z0 a c)).
  apply IHvl. intro. apply H. eauto.
  apply ZMap.gso. apply not_eq_sym. intro. apply H. eauto.
Qed.

Lemma setN'_inside:
    forall (A:Type) vl (c:ZMap.t A) (z: Z) (a : A),
    list_norepet (List.map fst vl) -> In (z,a) vl
    -> ZMap.get z (setN' vl c) = a.
Proof.
  induction vl; intros; simpl; auto.
  - inv H0.
  - destruct a. simpl in *. inv H. destruct H0.
    + inv H.
      rewrite setN'_outside; eauto.
      apply ZMap.gss.
    + eapply IHvl; eauto.
Qed.

(* how to proof :
 1. unrep of elements,
 2. perdicate b <-> In b (List.map fst elements)
 3. (from 2 and 1) In b (List.map fst elements) -> In (b, some specific value) elements
 4. (from 2 and 1) map2' # b = some specific value
*)
(** * Memory mixing *)

(** [mix m' b lo hi m] copies the region indicated by [b], [lo], [hi]
  from [m] into [m']. *)

Definition pmap_update {A} b (f : A -> A) (t : NMap.t A) : NMap.t A :=
  NMap.set A b (f (NMap.get A b t)) t.

Fixpoint update_elements' (lo:Z) (l:nat) (pm: ZMap.t (perm_kind -> option permission)) :=
  match l with
    |O => nil
    |S l' => (lo, pm##lo) :: update_elements' (lo+1) l' pm
  end.

Definition update_elements lo hi pm :=
  update_elements' lo (Z.to_nat (hi - lo)) pm.

Lemma update_elements'_inv : forall n lo pm ofs,
    if (zle lo ofs && zlt ofs (lo + Z.of_nat n)) then
        In (ofs, pm##ofs) (update_elements' lo n pm)
    else ~ In ofs (List.map fst (update_elements' lo n pm)).
Proof.
  induction n; intros; simpl.
  - replace (lo + 0) with lo by lia.
    destruct (zle lo ofs); destruct (zlt ofs lo); simpl; eauto.
    extlia.
  - generalize (IHn (lo+1) pm ofs). intro.
    destruct (zeq lo ofs).
    + destruct (zle lo ofs); simpl; try extlia.
      destruct (zlt ofs (lo + Z.pos (Pos.of_succ_nat n))); simpl.
      left. congruence. extlia.
    + assert (zle (lo + 1) ofs && zlt ofs (lo + 1 + Z.of_nat n) =
             zle lo ofs && zlt ofs (lo + Z.pos (Pos.of_succ_nat n))).
      f_equal.
      destruct (zle lo ofs); destruct (zle (lo + 1) ofs); simpl; auto; extlia.
      rewrite Zpos_P_of_succ_nat.
      rewrite <- Z.add_assoc. rewrite Z.add_1_l.
      auto.
      destruct (zle lo ofs && zlt ofs (lo + Z.pos (Pos.of_succ_nat n))).
      rewrite H0 in H. right. auto.
      rewrite H0 in H. intro. apply H. destruct H1. extlia. auto.
Qed.

Lemma update_elements_inv : forall lo hi pm ofs,
      if (zle lo ofs && zlt ofs hi) then
        In (ofs, pm##ofs) (update_elements lo hi pm)
      else ~ In ofs (List.map fst (update_elements lo hi pm)).
Proof.
  intros.
  destruct (zle lo hi).
  -
  unfold update_elements.
  set (n:= Z.to_nat (hi - lo)).
  assert (hi = (lo + Z.of_nat n)). unfold n.
  rewrite Z_to_nat_max.
  rewrite Z.max_l. lia. lia. rewrite H.
  eapply update_elements'_inv.
  - destruct (zle lo ofs); destruct (zlt ofs hi); try extlia; simpl.
    unfold update_elements.
    rewrite Z_to_nat_neg. simpl. auto. lia.
    unfold update_elements.
    rewrite Z_to_nat_neg. simpl. auto. lia.
    unfold update_elements.
    rewrite Z_to_nat_neg. simpl. auto. lia.
Qed.

Lemma update_elements_norepet: forall n lo pm,
    list_norepet (map fst (update_elements' lo n pm)).
Proof.
  induction n; intros; simpl; auto.
  constructor.
  constructor. simpl.
  generalize (update_elements'_inv n (lo+1) pm lo).
  destruct zle. extlia. simpl. auto.
  eauto.
Qed.

Definition mix_perms lo hi (pm pm' : ZMap.t (perm_kind -> option permission)) := setN' (update_elements lo hi pm) pm'.

Remark mix_perms_result lo hi (pm pm' : ZMap.t (perm_kind -> option permission)) ofs k :
  (mix_perms lo hi pm pm')##ofs k =
  if zle lo ofs && zlt ofs hi then pm##ofs k else pm'##ofs k.
Proof.
  intros. unfold mix_perms.
  destruct (zle lo ofs && zlt ofs hi) eqn: Range.
  - generalize (update_elements_inv lo hi pm ofs).
    rewrite Range. intro.
    erewrite setN'_inside; eauto.
    eapply update_elements_norepet.
  - generalize (update_elements_inv lo hi pm ofs).
    rewrite Range. intro.
    erewrite setN'_outside; eauto.
Qed.

Definition mixable m' b m :=
  sup_include (support m) (support m') /\
  Mem.valid_block m b.

Lemma mixable_dec m' b m :
  {mixable m' b m} + {~ mixable m' b m}.
Proof.
  unfold mixable, valid_block.
  destruct (sup_include_dec (support m) (support m')).
  - destruct (sup_dec b (support m)).
    + left. auto.
    + right. intro. apply n. apply H.
  - right. intro. apply n. apply H.
Qed.

Program Definition mix m' b lo hi m : option mem :=
  if mixable_dec m' b m then
    Some {|
      mem_contents :=
        let bytes := Mem.getN (Z.to_nat (hi - lo)) lo (NMap.get _ b (Mem.mem_contents m)) in
        pmap_update b (Mem.setN bytes lo) (Mem.mem_contents m');
      mem_access :=
        let perms := NMap.get _ b (Mem.mem_access m) in
        pmap_update b (mix_perms lo hi perms) (Mem.mem_access m');
      support :=
        Mem.support m';
    |}
  else
    None.
Next Obligation.
  unfold pmap_update. destruct (eq_block b0 b); subst.
  - rewrite NMap.gsspec.
    rewrite pred_dec_true.
    repeat rewrite mix_perms_result.
    destruct (_ && _); apply Mem.access_max. auto.
  - rewrite NMap.gsspec. rewrite pred_dec_false.
    apply Mem.access_max. auto.
Qed.
Next Obligation.
  unfold pmap_update. destruct H as [? ?]. unfold valid_block in *.
  rewrite NMap.gsspec. rewrite pred_dec_false.
  apply Mem.nextblock_noaccess; auto.
  intro. subst. apply H0. apply H,H1.
Qed.
Next Obligation.
  unfold pmap_update. destruct (eq_block b0 b); subst.
  - rewrite NMap.gsspec. rewrite pred_dec_true; auto.
    rewrite Mem.setN_default. apply Mem.contents_default.
  - rewrite NMap.gsspec. rewrite pred_dec_false; auto.
    apply Mem.contents_default.
Qed.
Next Obligation.
  unfold pmap_update. destruct (eq_block b0 b); subst.
  - rewrite NMap.gsspec. rewrite pred_dec_true; auto.
    unfold mix_perms.
    rewrite Mem.setN'_default. apply Mem.access_default.
  - rewrite NMap.gsspec. rewrite pred_dec_false; auto.
    apply Mem.access_default.
Qed.

(** ** Properties *)

Theorem mixable_mix:
  forall m' b lo hi m,
  mixable m' b m ->
  exists m'', mix m' b lo hi m = Some m''.
Proof.
  intros. unfold mix.
  destruct mixable_dec; intuition eauto.
Qed.

Theorem valid_block_mix:
  forall m' b lo hi m,
  sup_include (support m) (support m') ->
  valid_block m b ->
  exists m'', mix m' b lo hi m = Some m''.
Proof.
  unfold mix, valid_block. intros.
  destruct mixable_dec; unfold mixable in *; intuition eauto.
Qed.

Theorem mix_valid_block:
  forall m' b lo hi m m'',
  mix m' b lo hi m = Some m'' ->
  Mem.valid_block m b.
Proof.
  unfold mix. intros. destruct mixable_dec; try discriminate.
  unfold mixable in *. apply m0.
Qed.

Theorem valid_block_mix_1:
  forall m' b lo hi m m'',
  mix m' b lo hi m = Some m'' ->
  forall b, valid_block m' b -> valid_block m'' b.
Proof.
  unfold mix. intros. destruct mixable_dec; inv H.
  unfold valid_block. cbn. auto.
Qed.

Theorem valid_block_mix_2:
  forall m' b lo hi m m'',
  mix m' b lo hi m = Some m'' ->
  forall b, valid_block m'' b -> valid_block m' b.
Proof.
  unfold mix. intros. destruct mixable_dec; inv H.
  unfold valid_block in *. cbn in *. auto.
Qed.

Theorem support_mix:
  forall m' b lo hi m m'',
  mix m' b lo hi m = Some m'' ->
  support m'' = support m'.
Proof.
  unfold mix. intros. destruct mixable_dec; inv H. reflexivity.
Qed.

Theorem mix_unchanged:
  forall m' b lo hi m m'',
  mix m' b lo hi m = Some m'' ->
  unchanged_on (fun b1 ofs1 => ~ (b = b1 /\ lo <= ofs1 < hi)) m' m''.
Proof.
  intros. unfold mix in H. destruct mixable_dec as [[SUP VALID] | ]; inv H.
  constructor; cbn.
  - apply sup_include_refl.
  - unfold perm; cbn. intros b1 ofs1 k p H ?.
    unfold pmap_update.
    destruct (eq_block b1 b); subst; rewrite ?NMap.gss, ?NMap.gso; auto using iff_refl.
    rewrite mix_perms_result.
    destruct zle, zlt; cbn; auto using iff_refl.
    elim H; auto.
  - intros b1 ofs1 H Hp.
    unfold pmap_update.
    destruct (eq_block b1 b); subst; rewrite ?NMap.gss, ?NMap.gso; auto.
    rewrite setN_outside; auto.
    destruct (zlt ofs1 lo); auto. right.
    destruct (zlt ofs1 hi); try (elim H; split; auto; extlia).
    rewrite getN_length, Z_to_nat_max, <- Z.add_max_distr_l.
    rewrite Zmax_spec. destruct zlt; extlia.
Qed.

Lemma get_setN_getN_at A lo k n (x: ZMap.t A) y:
  ZMap.get (lo + Z.of_nat k) (setN (getN (k + S n) lo x) lo y) =
  ZMap.get (lo + Z.of_nat k) x.
Proof.
  revert lo n x y. induction k; cbn; intros.
  - rewrite setN_outside by extlia.
    replace (lo + 0) with lo by extlia.
    rewrite ZMap.gss; auto.
  - specialize (IHk (lo + 1)).
    rewrite Zpos_P_of_succ_nat, <- Z.add_1_r.
    replace (lo + _) with (lo + 1 + Z.of_nat k) by extlia.
    rewrite IHk. reflexivity.
Qed.

Lemma get_setN_getN A lo hi ofs (x y: ZMap.t A):
  lo <= ofs < hi ->
  ZMap.get ofs (setN (getN (Z.to_nat (hi - lo)) lo x) lo y) = ZMap.get ofs x.
Proof.
  intros Hofs.
  set (k := Z.to_nat (ofs - lo)).
  set (n := Z.to_nat (hi - ofs - 1)).
  replace (Z.to_nat (hi - lo)) with (k + S n)%nat.
  replace ofs with (lo + Z.of_nat k).
  - apply get_setN_getN_at.
  - subst k n.
    rewrite Z2Nat.id; extlia.
  - subst k n.
    rewrite <- Z2Nat.inj_succ by extlia.
    rewrite <- Z2Nat.inj_add by extlia.
    f_equal. extlia.
Qed.


Theorem mix_updated:
  forall m' b lo hi m m'',
  mix m' b lo hi m = Some m'' ->
  unchanged_on (fun b1 ofs1 => b = b1 /\ lo <= ofs1 < hi) m m''.
Proof.
  intros. unfold mix in H. destruct mixable_dec as [[NB VALID] | ]; inv H.
  constructor; cbn.
  - auto.
  - intros _ ofs k p [[ ] Hofs] Hb. unfold perm; cbn.
    unfold pmap_update. rewrite NMap.gss.
    rewrite mix_perms_result.
    destruct zle, zlt; try extlia; cbn. reflexivity.
  - intros _ ofs [[ ] Hofs] Hp.
    unfold pmap_update. rewrite NMap.gss.
    rewrite get_setN_getN; auto.
Qed.

Lemma mix_left_mem_inj:
  forall f f' m1 m2 m1' m2' b1 b2 delta lo hi m1'',
  mix m1' b1 lo hi m1 = Some m1'' ->
  mem_inj f m1 m2 ->
  mem_inj f' m1' m2' ->
  f b1 = Some (b2, delta) ->
  inject_incr f f' ->
  Mem.unchanged_on (fun b ofs => b = b2 /\ lo + delta <= ofs < hi + delta) m2 m2' ->
  valid_block m2 b2 ->
  (8 | delta) ->
  mem_inj f' m1'' m2'.
Proof.
  intros f f' m1 m2 m1' m2' b1 b2 delta lo hi m1'' Hm1'' Hm Hm' Hb Hf' Hm2'.
  split.
  - (* perm *)
    intros b1' b2' delta' ofs k p Hb' Hp.
    destruct (classic (b1 = b1' /\ lo <= ofs < hi)) as [[? ?] | ?].
    + (* updated *)
      subst. erewrite Hf' in Hb'; eauto. inv Hb'.
      erewrite <- unchanged_on_perm; eauto.
      * erewrite <- unchanged_on_perm in Hp; eauto using mix_updated.
        -- eapply mi_perm; eauto.
        -- cbn. auto.
        -- eapply mix_valid_block; eauto.
      * cbn. split; auto. extlia.
    + (* unchanged *)
      eapply mi_perm; eauto.
      erewrite <- unchanged_on_perm in Hp; eauto using mix_unchanged.
      eapply valid_block_mix_2; eauto.
      eapply perm_valid_block; eauto.
  - (* align *)
    intros b1' b2' delta' chunk ofs p Hb' Hp.
    destruct (eq_block b1' b1); subst.
    + erewrite Hf' in Hb'; eauto. inv Hb'.
      etransitivity; eauto.
      assert (2 | 8) by (exists 4; extlia).
      assert (4 | 8) by (exists 2; extlia).
      destruct chunk; cbn; auto using Z.divide_1_l, Z.divide_refl.
    + eapply mi_align with f' m1' m2' b1' b2' ofs p; eauto.
      intros i Hi.
      erewrite unchanged_on_perm; eauto using mix_unchanged.
      * cbn. intros [? ?]. congruence.
      * eapply valid_block_mix_2; eauto.
        eapply perm_valid_block, (Hp ofs).
        pose proof (size_chunk_pos chunk). extlia.
  - (* contents *)
    intros b1' ofs b2' delta' Hb' Hp.
    destruct (classic (b1 = b1' /\ lo <= ofs < hi)) as [[? ?] | ?].
    + (* updated *)
      subst. erewrite Hf' in Hb'; eauto. inv Hb'.
      erewrite <- unchanged_on_perm in Hp; eauto using mix_updated, mix_valid_block.
      2: cbn; auto.
      erewrite unchanged_on_contents; eauto using mix_updated.
      2: cbn; auto.
      erewrite unchanged_on_contents with _ m2 m2' _ _; eauto.
      * eapply memval_inject_incr; eauto.
        eapply mi_memval; eauto.
      * cbn. split; auto. extlia.
      * eapply mi_perm; eauto.
    + (* unchanged *)
      erewrite <- unchanged_on_perm in Hp;
        eauto using mix_unchanged, valid_block_mix_2, perm_valid_block;
        cbn; eauto.
      erewrite unchanged_on_contents; eauto using mix_unchanged; cbn; eauto.
      eapply mi_memval; eauto.
Qed.

Lemma mix_left_extends:
  forall m1 m2 m1' m2' b lo hi m1'',
  mix m1' b lo hi m1 = Some m1'' ->
  extends m1 m2 ->
  extends m1' m2' ->
  unchanged_on (fun b' ofs => b' = b /\ lo <= ofs < hi) m2 m2' ->
  extends m1'' m2'.
Proof.
  intros m1 m2 m1' m2' b lo hi m1'' Hm1'' [NB INJ PINV] [NB' INJ' PINV'] UNCH.
  assert (valid_block m1 b) by eauto using mix_valid_block.
  assert (valid_block m2 b) by (unfold valid_block in *; congruence).
  constructor.
  - erewrite support_mix; eauto.
  - eapply mix_left_mem_inj; eauto.
    + reflexivity.
    + replace (lo + 0) with lo by extlia.
      replace (hi + 0) with hi by extlia.
      auto.
    + apply Z.divide_0_r.
  - intros b' ofs k p Hp.
    destruct (classic (b = b' /\ lo <= ofs < hi)) as [[? ?] | ?].
    + subst. rewrite <- unchanged_on_perm in Hp; [ | eauto.. ]; cbn; auto.
      erewrite <- !(unchanged_on_perm _ m1 m1''); [ | eauto using mix_updated ..]; cbn; auto.
    + assert (valid_block m1' b').
       { unfold valid_block in *; apply perm_valid_block in Hp. unfold valid_block in Hp. congruence. }
      erewrite <- !(unchanged_on_perm _ m1' m1''); [ | eauto using mix_unchanged ..]; cbn; auto.
Qed.

Lemma mix_left_inject:
  forall f f' m1 m2 m1' m2' b1 b2 delta lo hi m1'',
  mix m1' b1 lo hi m1 = Some m1'' ->
  inject f m1 m2 ->
  inject f' m1' m2' ->
  f b1 = Some (b2, delta) ->
  inject_incr f f' ->
  Mem.unchanged_on (fun b ofs => b = b2 /\ lo + delta <= ofs < hi + delta) m2 m2' ->
  (forall b1' delta' ofs p k,
      f' b1' = Some (b2, delta') -> lo <= ofs - delta < hi ->
      ~ Mem.perm m1' b1' (ofs - delta') p k) ->
  (8 | delta) ->
  inject f' m1'' m2'.
Proof.
  intros f f' m1 m2 m1' m2' b1 b2 delta lo hi m1'' Hm1'' H H' Hb Hf Hm2' OOR AL.
  constructor.
  - inv H'. inv mi_thread0. constructor. erewrite support_mix; eauto. auto.
  - eapply mix_left_mem_inj; eauto using mi_inj.
    eapply valid_block_inject_2; eauto.
  - intros. eapply mi_freeblocks; eauto.
    intro. eauto using valid_block_mix_1.
  - eauto using mi_mappedblocks.
  - red.
    intros x1 x2 xd y1 y2 yd xofs yofs H1 Hx Hy Hpx Hpy.
    assert (Mem.valid_block m1' x1) by eauto using valid_block_inject_1.
    assert (Mem.valid_block m1' y1) by eauto using valid_block_inject_1.
    destruct (classic (b1 = x1 /\ lo <= xofs < hi)).
    + destruct H3; subst x1.
      erewrite Hf in Hx; eauto. inversion Hx; clear Hx; subst x2 xd.
      destruct (classic (b1 = y1 /\ lo <= yofs < hi)).
      * intuition congruence.
      * rewrite <- unchanged_on_perm in Hpy; eauto using mix_unchanged.
        replace yofs with (yofs + yd - yd) in Hpy by extlia.
        destruct (eq_block b2 y2); auto; subst y2. right.
        intros Hofs. eapply (OOR y1 yd (yofs + yd)); eauto. extlia.
    + rewrite <- unchanged_on_perm in Hpx; eauto using mix_unchanged.
      destruct (classic (b1 = y1 /\ lo <= yofs < hi)).
      * destruct H4; subst y1.
        replace xofs with (xofs + xd - xd) in Hpx by extlia.
        erewrite Hf in Hy; eauto. inversion Hy; clear Hy; subst y2 yd.
        destruct (eq_block x2 b2); auto; subst x2. right.
        intros Hofs. eapply (OOR x1 xd (xofs + xd)); eauto. extlia.
      * rewrite <- unchanged_on_perm in Hpy; eauto using mix_unchanged.
        eapply mi_no_overlap; eauto.
  - intros b b' delta' ofs Hb' [Hp | Hp].
    + destruct (classic (b1 = b /\ lo <= Ptrofs.unsigned ofs < hi)).
      * assert (b1 = b) by intuition auto. subst b.
        erewrite Hf in Hb'; eauto. inversion Hb'; clear Hb'; subst b' delta.
        assert (Mem.valid_block m1 b1) by eauto using valid_block_inject_1.
        rewrite <- unchanged_on_perm in Hp; eauto using mix_updated.
        eapply (mi_representable f); eauto.
      * assert (Mem.valid_block m1' b) by eauto using valid_block_inject_1.
        rewrite <- unchanged_on_perm in Hp; eauto using mix_unchanged.
        eapply (mi_representable f'); eauto.
    + destruct (classic (b1 = b /\ lo <= Ptrofs.unsigned ofs - 1 < hi)).
      * assert (b1 = b) by intuition auto. subst b.
        erewrite Hf in Hb'; eauto. inversion Hb'; clear Hb'; subst b' delta.
        assert (Mem.valid_block m1 b1) by eauto using valid_block_inject_1.
        rewrite <- unchanged_on_perm in Hp; eauto using mix_updated.
        eapply (mi_representable f); eauto.
      * assert (Mem.valid_block m1' b) by eauto using valid_block_inject_1.
        rewrite <- unchanged_on_perm in Hp; eauto using mix_unchanged.
        eapply (mi_representable f'); eauto.
  - intros x1 ofs x2 xd k p Hx Hp.
    destruct (classic (b1 = x1 /\ lo <= ofs < hi)).
    + assert (b1 = x1) by intuition auto. subst x1.
      erewrite Hf in Hx; eauto. inversion Hx; clear Hx; subst x2 xd.
      assert (valid_block m1 b1) by eauto using valid_block_inject_1.
      assert (valid_block m2 b2) by eauto using valid_block_inject_2.
      rewrite <- unchanged_on_perm in Hp; eauto; cbn; try (split; auto; extlia).
      erewrite <- !(unchanged_on_perm _ m1 m1''); eauto using mix_updated.
      eapply mi_perm_inv; eauto.
    + assert (valid_block m1' x1) by eauto using valid_block_inject_1.
      assert (valid_block m2' x2) by eauto using valid_block_inject_2.
      erewrite <- !(unchanged_on_perm _ m1' m1''); eauto using mix_unchanged.
      eapply mi_perm_inv; eauto.
Qed.

(** Memory support extension *)

Program Definition supext (s:sup) (m:mem) : mem :=
  if (sup_include_dec (Mem.support m) s) then
    {|
      mem_contents := (mem_contents m);
      mem_access := (mem_access m);
      support := s
    |} else
    m.
Next Obligation.
   apply access_max; eauto.
Qed.
Next Obligation.
   apply nextblock_noaccess; eauto.
Qed.
Next Obligation.
   apply contents_default; eauto.
Qed.
Next Obligation.
   apply access_default; eauto.
Qed.

(** update permission *)

Definition perm_map := ZMap.t (perm_kind -> option permission).

Definition perm_check_any (pmap : perm_map ) ofs : bool :=
  match (pmap ## ofs) Max with
    |None => false
    |Some _ => true
  end.

Definition perm_check_readable (pmap : perm_map) ofs : bool :=
  match (pmap ## ofs) Cur with
    | None | Some Nonempty => false
    | _ => true
  end.


Definition pair_delta {A: Type} (delta: Z) (pair: Z * A) : Z * A :=
  (fst pair + delta, snd pair).

Fixpoint perm_elements_any (elements : list (Z * (perm_kind -> option permission))) {struct elements} :=
  match elements with
    | nil => nil
    | (z , perm) :: elements' =>
      let l :=  perm_elements_any elements' in
      if perm Max then (z,perm)::l else l
  end.

Definition update_mem_access (delta : Z) (map1 map2 : perm_map) : perm_map :=
  let elements := perm_elements_any (ZMap.elements map1) in
  let elements_delta := List.map (pair_delta delta) elements in
  setN' elements_delta map2.

(* lemmas about elements of ZMap *)
Lemma fst_pair_delta_norepet: forall (A :Type) (l: list (Z*A)) delta,
    list_norepet (List.map fst l) ->
    list_norepet (List.map fst (List.map (pair_delta delta) l)).
Proof.
  induction l; intros; simpl.
  - constructor.
  - inv H. constructor; eauto. intro. apply H2.
    simpl. induction l.
    + simpl. auto.
    + simpl. simpl in H. destruct H.
      left. unfold pair_delta in H. inv H. lia.
      right. eapply IHl0.
      intros. apply IHl with delta0 in H3. inv H3. auto.
      intro. apply H2. right. auto.
      inv H3. eauto.
    eauto.
Qed.

Lemma In_fst_perm_any : forall z l,
    In z (map fst (perm_elements_any l)) -> In z (map fst l).
Proof.
  induction l; intros. inv H.
  simpl in H. destruct a.  destruct (o Max).
  destruct H. left. auto. right.  eauto.
  right. eauto.
Qed.

Lemma fst_perm_any_norepet: forall l,
    list_norepet (List.map fst l) ->
    list_norepet (List.map fst (perm_elements_any l)).
Proof.
  induction l; intros; simpl.
  - constructor.
  - inv H. destruct a. destruct (o Max).
    + simpl. constructor; eauto.
      simpl in H2. intro. apply H2.
      eapply In_fst_perm_any; eauto.
    + simpl. auto.
Qed.

(** 
ZMap.elements m contains all (i,a) such that a <> fst m. It is also possible for
some (i,fst m) in it.
For mem_access, ZMap.elements pmap contains all nonempty positions in pmap.
For mem_contents, ZMap.elements vmap contains all positions where the value is not Vundef
*)
Lemma elements_correct' :
forall (A : Type) (i : ZMap.elt) (m : ZMap.t A),
  m ## i <> fst m -> In (i, m ## i) (ZMap.elements m).
Proof.
  intros. eapply ZMap.elements_correct; eauto.
Qed.

Lemma in_pair_delta : forall (A: Type) d (a:A) l ofs,
    In (ofs - d,a) l <->
    In (ofs, a) (map (pair_delta d) l).
Proof.
  induction l; intros.
  split; intro. inv H. inv H.
  destruct a0. simpl. split; intros [B | B].
  inv B. left.  unfold pair_delta. simpl.
  f_equal. lia.
  right. eapply IHl; eauto.
  left. inv B. f_equal. lia.
  right. eapply IHl; eauto.
Qed.

Lemma in_map_fst:
  forall (A B:Type) (a:A) (l: list (A*B)),
    In a (List.map fst l) ->
    exists b, In (a,b) l.
Proof.
  induction l; intros.
  - inv H.
  - simpl in H. destruct H. destruct a0.
    inv H.
    exists b. simpl. eauto. exploit IHl; eauto.
    intros (b & H0).
    exists b. right. auto.
Qed.

Lemma in_map_fst_1:
  forall (A B:Type) (a:A) (b b':B) (l: list (A*B)),
    In (a,b) (List.map (fun p => (fst p, b')) l) ->
    In a (List.map fst l).
Proof.
  induction l; intros.
  - inv H.
  - simpl in H. destruct H. destruct a0.
    inv H. simpl. eauto.
    simpl. right. eauto.
Qed.

Lemma in_map_fst_2:
    forall (A B:Type) (a:A) b (l: list (A*B)),
    In (a,b) l ->
    In a (List.map fst l).
Proof.
    induction l; intros.
  - inv H.
  - simpl in H. destruct H. destruct a0.
    inv H. simpl. eauto.
    simpl. right. eauto.
Qed.

Lemma in_map_none:
  forall (A B:Type) (a:A) (b b0:B) (l: list (A*B)),
    In (a,b0) l ->
    In (a,b) (List.map (fun p => (fst p, b)) l).
Proof.
  induction l; intros.
  - inv H.
  - simpl in H. destruct H.
    + destruct a0. simpl in H.
    inv H. simpl. eauto.
    + exploit IHl; eauto.
      simpl. eauto.
Qed.

Lemma in_perm_any : forall ofs perm p l,
    In (ofs, perm) l -> perm Max = Some p ->
    In (ofs, perm) (perm_elements_any l).
Proof.
  induction l; intros.
  inv H.
  simpl. destruct a.
  destruct H.
  - inv H. rewrite H0. left. auto.
  - destruct (o Max).
    right. eauto.
    eauto.
Qed.

Lemma in_perm_any_1 : forall ofs perm l,
    In (ofs,perm) (perm_elements_any l) ->
    perm Max <> None /\ In (ofs,perm) l.
Proof.
  induction l; intros.
  inv H. simpl in H.
  destruct a. destruct (o Max) eqn:Hp.
  - destruct H.
    + inv H. split. congruence. left. auto.
    + exploit IHl; eauto. intros [A B]. split; eauto. right. eauto.
  - exploit IHl; eauto. intros [A B]. split; eauto. right. eauto.
Qed.

(* result of ZMap update *)
Lemma update_mem_access_result:
  forall d map1 map2 ofs2 p,
    (fst map1 = fun k => None) ->
    ((update_mem_access d map1 map2)##ofs2) p = if (perm_check_any) map1 (ofs2 - d) then map1##(ofs2 - d) p
                      else map2##ofs2 p.
Proof.
  intros. destruct (perm_check_any) eqn: Hperm.
  - unfold update_mem_access.
    erewrite setN'_inside. reflexivity.
    apply fst_pair_delta_norepet.
    apply fst_perm_any_norepet.
    eapply ZMap.elements_keys_norepet.
    generalize (elements_correct' _ (ofs2 - d) map1).
    intros. exploit H0. rewrite H. intro.
    destruct (map1 ## (ofs2 - d) Max) eqn : Hnone. rewrite H1 in Hnone.
    congruence.
    unfold perm_check_any in Hperm. rewrite Hnone in Hperm.
    congruence.
    intro.
    apply in_pair_delta.
    unfold perm_check_any in Hperm.
    destruct (map1 ## (ofs2 -d) Max) eqn : Hsome.
    eapply in_perm_any; eauto. congruence.
  - unfold update_mem_access.
    erewrite setN'_outside. reflexivity.
    unfold perm_check_any in Hperm. destruct (ZMap.get) eqn: Hperm1.
    congruence.
    intro. apply in_map_fst in H0.
    destruct H0 as [p0 H0].
    apply in_pair_delta in H0.
    apply in_perm_any_1 in H0. destruct H0 as [A B].
    apply ZMap.elements_complete in B. congruence.
Qed.

(** update content *)

Definition memval_map (f:meminj) (mv:memval) : memval :=
  match mv with
  |Fragment (Vptr b ofs) q n =>
       match (f b) with
       |Some (b', delta) =>
          let v' := Vptr b' (Ptrofs.add ofs (Ptrofs.repr delta)) in
          Fragment v' q n
       |None => Undef
       end
  |_ => mv
  end.

Definition perm_check_readable' (perm: perm_kind -> option permission) :=
  match perm Cur with
    | Some Nonempty | None => false
    | _ => true
  end.
Fixpoint perm_elements_readable (elements : list (Z * (perm_kind -> option permission))) {struct elements} : list Z :=
  match elements with
    | nil => nil
    | (z , perm) :: elements' =>
      let l :=  perm_elements_readable elements' in
      if perm_check_readable' perm then z::l else l
  end.

Fixpoint ofs_elements_val (elements : list Z) (vmap1 : ZMap.t memval) (f: meminj) :=
  match elements with
    | nil => nil
    | z :: elements' =>
      let mapvalue := memval_map f (vmap1##z) in
      (z, mapvalue) :: ofs_elements_val elements' vmap1 f
  end.

Definition update_mem_content (pmap1 : perm_map) (f:meminj) (delta: Z) (vmap1 vmap2: ZMap.t memval):=
    let elements := ZMap.elements pmap1 in
    let ofs_elements := perm_elements_readable elements in
    let val_elements1 := ofs_elements_val ofs_elements vmap1 f in
    let val_elements2 := List.map (pair_delta delta) val_elements1 in
    setN' val_elements2 vmap2.

Lemma fst_ofs_elements_norepet : forall vmap j vl,
    list_norepet vl ->
    list_norepet (map fst (ofs_elements_val vl vmap j)).
Proof.
  induction vl; intros; simpl.
  constructor.
  inv H.
  constructor; eauto.
  induction vl; simpl.
  auto. intro. apply H2.
  destruct H. left. auto. exfalso.
  apply IHvl0; eauto.
  intro. apply IHvl in H3. inv H3. auto.
  intro. apply H2. right. auto.
  inv H3. auto.
Qed.

Lemma perm_readable_norepet: forall vl,
    list_norepet (map fst vl) ->
    list_norepet (perm_elements_readable vl).
Proof.
  induction vl; intros; simpl.
  constructor. destruct a. inv H.
  destruct (perm_check_readable'); eauto.
  constructor; eauto.
  intro. apply H2.
  induction vl; simpl.
  auto. simpl in H.
  apply IHvl in H3 as H4.
  destruct a. destruct perm_check_readable'; eauto.
  - destruct H. left. simpl. congruence.
    right. eapply IHvl0; eauto.
    intro. simpl in H4. destruct perm_check_readable'; eauto.
    inv H4. eauto.
    intro. apply H2. right. auto.
    inv H3. auto.
  -right. eapply IHvl0; eauto.
    intro. simpl in H4. destruct perm_check_readable'; eauto.
    inv H4. eauto.
    intro. apply H2. right. auto.
    inv H3. auto.
Qed.

Lemma in_ofs_elements_val : forall ofs vl j vmap,
    In ofs vl <->
    In (ofs,memval_map j vmap##ofs) (ofs_elements_val vl vmap j).
Proof.
  induction vl; intros; simpl. reflexivity.
  split; intros [A | B].
  left. inv A. reflexivity.
  right. eapply IHvl; eauto.
  left. inv A. reflexivity.
  right. eapply IHvl; eauto.
Qed.

Lemma in_ofs_elements_val1 : forall vl ofs val j vmap,
    In (ofs, val) (ofs_elements_val vl vmap j) ->
    val = memval_map j vmap##ofs.
Proof.
  induction vl; intros; simpl. inv H.
  simpl in H. destruct H. inv H. auto.
  eauto.
Qed.

Lemma in_perm_read : forall ofs perm l,
    In (ofs, perm) l -> perm_check_readable' perm = true ->
    In ofs (perm_elements_readable l).
Proof.
  induction l; intros.
  inv H.
  simpl. destruct a.
  destruct H.
  - inv H. rewrite H0. left. auto.
  - destruct (perm_check_readable' o).
    right. eauto.
    eauto.
Qed.

Lemma in_perm_read_1 : forall ofs l,
    In ofs (perm_elements_readable l) ->
    exists perm, perm_check_readable' perm =true  /\ In (ofs,perm) l.
Proof.
  induction l; intros.
  inv H. simpl in H.
  destruct a. destruct (perm_check_readable' o) eqn:Hp.
  - destruct H.
    + inv H. exists o. split. congruence. left. auto.
    + exploit IHl; eauto. intros [p [A B]]. exists p. split; eauto. right. eauto.
  - exploit IHl; eauto. intros [p [A B]]. exists p. split; eauto. right. eauto.
Qed.

Lemma update_mem_content_result: forall b1 b2 j1' delta vmap1 vmap2 pmap1 (ofs2:Z),
    fst pmap1 = (fun k => None) ->
    j1' b1 = Some (b2,delta) ->
    ZMap.get ofs2 (Mem.update_mem_content pmap1 j1' delta vmap1 vmap2) =
    if (Mem.perm_check_readable pmap1 (ofs2 - delta)) then
      Mem.memval_map j1' (ZMap.get (ofs2 - delta) vmap1) else
          ZMap.get ofs2 vmap2.
Proof.
  intros. destruct (perm_check_readable) eqn: Hperm.
  - unfold update_mem_content.
    erewrite setN'_inside. reflexivity.
    + apply fst_pair_delta_norepet.
      apply fst_ofs_elements_norepet.
      apply perm_readable_norepet.
      apply ZMap.elements_keys_norepet.
    +
      generalize (elements_correct' _ (ofs2 -delta) pmap1).
      intros. exploit H1.
      { unfold perm_check_readable in Hperm.
      destruct (pmap1 ## (ofs2 - delta) Cur) eqn:Hsome; try congruence.
      destruct p; try congruence.
      intro. rewrite H2,H in Hsome. congruence.
      intro. rewrite H2,H in Hsome. congruence.
      intro. rewrite H2,H in Hsome. congruence.
      }
      intro IN.
      apply in_pair_delta.
      apply in_ofs_elements_val.
      eapply in_perm_read; eauto.
  - unfold update_mem_content.
    erewrite setN'_outside. reflexivity.
    unfold perm_check_readable in Hperm. destruct (pmap1 ## (ofs2 - delta) Cur) eqn: Hperm1. destruct p.
    congruence.
    congruence.
    congruence.
    + intro.
      apply in_map_fst in H1.
      destruct H1 as [p0 H1].
      apply in_pair_delta in H1.
      apply in_ofs_elements_val1 in H1 as H2. subst p0.
      apply in_ofs_elements_val in H1.
      apply in_perm_read_1 in H1. destruct H1 as [p [A B]].
      apply ZMap.elements_complete in B. subst p.
      unfold perm_check_readable' in A. rewrite Hperm1 in A.
      congruence.
    + intro.
      apply in_map_fst in H1.
      destruct H1 as [p0 H1].
      apply in_pair_delta in H1.
      apply in_ofs_elements_val1 in H1 as H2. subst p0.
      apply in_ofs_elements_val in H1.
      apply in_perm_read_1 in H1. destruct H1 as [p [A B]].
      apply ZMap.elements_complete in B. subst p.
      unfold perm_check_readable' in A. rewrite Hperm1 in A.
      congruence.
Qed.

(** loc_in_reach_dec *)
Definition loc_in_reach (f:meminj) m b ofs k p: Prop :=
  exists b0 delta, f b0 = Some (b,delta) /\ Mem.perm m b0 (ofs - delta) k p.

Definition loc_out_of_reach (f: meminj) (m: mem) (b: block) (ofs: Z): Prop :=
  forall b0 delta,
  f b0 = Some(b, delta) -> ~Mem.perm m b0 (ofs - delta) Max Nonempty.

Lemma out_of_reach_reverse: forall f m b ofs,
    loc_out_of_reach f m b ofs <-> ~ loc_in_reach f m b ofs Max Nonempty.
Proof.
  intros. split; intro.
  - intro. red in H. red in H0. destruct H0 as (b0 & delta & A & B).
    exploit H; eauto.
  - red. intros. intro.
    apply H. red. eauto.
Qed.

Definition inject_dom_in (f:meminj) s : Prop :=
  forall b b' o, f b = Some (b',o) -> sup_In b s.

(**  proof of loc_in_reach_dec which is contained by 
     properties about loc_in_reach_find presented later *)
(*
Definition meminj_sub (j:meminj) (b:block) :=
  fun b0 => if (eq_block b b0) then None else j b0.


Lemma meminj_sub_diff: forall j a b,
    a <> b -> meminj_sub j a b = j b.
Proof.
  intros. unfold meminj_sub. destruct eq_block; congruence.
Qed.

Lemma inject_dom_in_sub: forall j a s,
    inject_dom_in j (a::s) ->
    inject_dom_in (meminj_sub j a) s.
Proof.
  intros.
  red. red in H. intros. unfold meminj_sub in H0.
  destruct eq_block in H0. congruence. exploit H; eauto.
  intros [A|A]. congruence. auto.
Qed.

Lemma loc_in_reach_dec: forall s m f b ofs k p,
    inject_dom_in f s ->
    {loc_in_reach f m b ofs k p}+{~ loc_in_reach f m b ofs k p}.
Proof.
  induction s; intros.
  - right. intros (b0 & delta & A & B).
    apply H in A. inv A.
  - apply inject_dom_in_sub in H as H'.
    eapply (IHs m (meminj_sub f a) b ofs) in H'.
    destruct H'.
    + left. red. red in l. destruct l as (b0 & d & A & B).
      exists b0,d. split; auto. unfold meminj_sub in A.
      destruct eq_block; eauto. congruence. eauto.
    +
    destruct (f a) as [[a' delta]|] eqn : Hfa.
    * destruct (eq_block a' b).
      -- subst.
         destruct (Mem.perm_dec m a (ofs-delta) k p).
         left. exists a,delta. eauto.
         right.
         intros (b0 & d & A & B).
         destruct (eq_block b0 a). subst. congruence.
         apply n. red.
         exists b0,d. split.
         rewrite meminj_sub_diff; auto. eauto.
      -- right. intros (b0 & d & A & B).
         destruct (eq_block b0 a). subst. congruence.
         apply n. red.
         exists b0,d. split.
         rewrite meminj_sub_diff; auto. eauto.
    * right.  intros (b0 & d & A & B).
         destruct (eq_block b0 a). subst. congruence.
         apply n. red.
         exists b0,d. split.
         rewrite meminj_sub_diff; auto. eauto.
Qed.
 *)


Section STEP23.
  
Variable m1 m2 m3 m1' : mem.
Variable s2' : sup.  
Variable j12 j23 j12' j23': meminj.

Hypothesis INJ1: inject j12 m1 m2.
Hypothesis INJ2: inject j23 m2 m3.
Hypothesis SUPINCR2 : sup_include (support m2) s2'.

(** The construction step (2) in appendix *)

 Program Definition map_block (b1:block) (m:mem) :=
  match j12' b1 with
  |Some (b2,delta) =>
     if j12 b1 then m else
       if (sup_dec b2 (Mem.support m)) then (* well-typeness constrain *)
     {|
       mem_contents :=
           pmap_update b2 (update_mem_content ((mem_access m1')#b1) j12' delta (mem_contents m1')#b1)
                       (mem_contents m);
       mem_access :=
           pmap_update b2 (update_mem_access delta (mem_access m1')#b1) (mem_access m);
       support := (Mem.support m);
     |} else m
  |None => m
  end.
Next Obligation.
    unfold pmap_update. destruct (eq_block b b2); subst.
  - rewrite NMap.gsspec. rewrite pred_dec_true; auto.
    generalize (update_mem_access_result delta ).
    intros. erewrite H0; eauto.
    erewrite update_mem_access_result; eauto.
    destruct perm_check_any;
    apply Mem.access_max; eauto.
    apply Mem.access_default.
    apply Mem.access_default.
  - rewrite NMap.gsspec. rewrite pred_dec_false; auto.
    apply Mem.access_max; auto.
Qed.
Next Obligation.
  unfold pmap_update. destruct (eq_block b b2); subst.
  - congruence.
  - rewrite NMap.gsspec. rewrite pred_dec_false; auto.
    apply Mem.nextblock_noaccess. auto.
Qed.
Next Obligation.
    unfold pmap_update. destruct (eq_block b b2); subst.
  - rewrite NMap.gsspec. rewrite pred_dec_true; auto. unfold update_mem_content.
    rewrite setN'_default. apply Mem.contents_default.
  - rewrite NMap.gsspec. rewrite pred_dec_false; auto.
    apply Mem.contents_default.
Qed.
Next Obligation.
    unfold pmap_update. destruct (eq_block b b2); subst.
  - rewrite NMap.gsspec. rewrite pred_dec_true; auto. unfold update_mem_access.
    rewrite setN'_default. apply Mem.access_default.
  - rewrite NMap.gsspec. rewrite pred_dec_false; auto.
    apply Mem.access_default.
Qed.

Fixpoint map_sup' (bl:list block) (m:mem) :=
  match bl with
  |nil => m
  |hd:: tl => map_block hd (map_sup' tl m)
  end.

Definition map_sup (s: sup) (m:mem) :=
  map_sup' (sup_list s) m.

(** step2, with the extension of support s2' which is constructed in step (1) *)
Definition step2 := 
  map_sup (support m1') (supext s2' m2).

(** properties of step2 *)

Lemma map_block_support : forall b m,
  support (map_block b m) = support m.
Proof.
  intros. unfold map_block.
  destruct (j12' b); auto.
  destruct p.
  destruct (sup_dec); auto;
  destruct (j12 b); auto.
Qed.

Lemma map_sup_support' : forall bl m,
    support (map_sup' bl m) = support m.
Proof.
   induction bl; intros; simpl; eauto.
   rewrite map_block_support. eauto.
Qed.

Lemma map_sup_support : forall s m,
    support (map_sup s m) = support m.
Proof.
  intros.
  apply map_sup_support'.
Qed.

Lemma step2_support :
  support step2 = s2'.
Proof.
  unfold step2. rewrite map_sup_support.
  unfold supext.
  destruct sup_include_dec; eauto.
  congruence.
Qed.

(** construction step3 *)

(* find (b_1,o_1) from (b_2,o_2) *)
Section REVERSE.
  Variable b2: block.
  Variable o2: Z.
  (* Hypothesis PERM2 : perm m2 b2 o2 Max Nonempty. *)

  Lemma DOMIN: inject_dom_in j12 (Mem.support m1).
  Proof.
    red. intros. inv INJ1.
    destruct (sup_dec b (Mem.support m1)).
    auto. exploit mi_freeblocks0; eauto.
    intro. congruence.
  Qed.

  
  Definition check_position o1 (pos1: Z * memperm) : bool :=
    if (zeq o1 (fst pos1)) then true
    else false.

  (* find (b_1,o_1) in block b_1 *)
  Definition block_find b1 b2 o2 : option (block * Z) :=
    match j12 b1 with
    |Some (b2',delta) =>
       if eq_block b2 b2' then
         let pmap1 := (mem_access m1 b1) in
         let elements := perm_elements_any (ZMap.elements pmap1) in
         match find (check_position (o2 - delta)) elements with
         |Some (o1,_) => Some (b1,o2 - delta)
         |None => None
         end
       else None
    |_ => None
    end.

  (* find (b_1,o_1) in all blocks in s *)
  Fixpoint loc_in_reach_find' (b2: block) (o2: Z) (bl : list block ): option (block * Z) :=
    match bl with
    | nil => None
    | hd :: tl =>
        match block_find hd b2 o2 with
        | Some a => Some a
        | None => loc_in_reach_find' b2 o2 tl
        end
    end.

  (*specific find function, find (b_1,o_1) in sup(m_1)*)
  Definition loc_in_reach_find (b2: block) (o2: Z) :=
    loc_in_reach_find' b2 o2 (sup_list (Mem.support m1)).

  Lemma block_find_valid: forall b b2 o2 b1 o1,
      block_find b b2 o2 = Some (b1, o1) ->
      j12 b1 = Some (b2, o2 - o1) /\ perm m1 b1 o1 Max Nonempty.
  Proof.
    intros. unfold block_find in H.
    destruct (j12 b) as [[b2' d]|] eqn:Hj; try congruence.
    destruct eq_block; try congruence.
    destruct find eqn:FIND; try congruence.
    destruct p. inv H.
    apply find_some in FIND. unfold check_position in FIND.
    destruct FIND.
    destruct zeq; try congruence. inv e. simpl in H1. inv H1.
    split. replace (o0 - (o0 - d)) with d by lia. eauto.
    unfold perm. unfold perm_order'.
    apply in_perm_any_1 in H.
    destruct H as [PERM IN].
    apply ZMap.elements_complete in IN.
    unfold NMap.get.
    rewrite IN. destruct (m Max); eauto.
    constructor.
  Qed.
  
  Lemma loc_in_reach_find'_rec: forall s b2 o2 b1 o1,
      loc_in_reach_find' b2 o2 s = Some (b1, o1) ->
      j12 b1 = Some (b2, o2 - o1) /\ perm m1 b1 o1 Max Nonempty.
  Proof.
    induction s; intros; subst; simpl; eauto.
    - inv H.
    - simpl in H. destruct block_find eqn:BLOCK. destruct p.
      inv H. eapply block_find_valid; eauto.
      eauto.
  Qed.

  Lemma loc_in_reach_find_valid: forall b2 o2 b1 o1,
      loc_in_reach_find b2 o2 = Some (b1,o1) ->
      j12 b1 = Some (b2,o2 - o1)
      /\ perm m1 b1 o1 Max Nonempty.
  Proof.
    intros. unfold loc_in_reach_find in H.
    eapply loc_in_reach_find'_rec; eauto.
  Qed.

  Lemma block_find_none : forall b b2 o2 d,
      block_find b b2 o2 = None ->
      j12 b = Some (b2,d) -> ~ perm m1 b (o2 - d) Max Nonempty.
  Proof.
    intros. unfold block_find in H.
    destruct (j12 b) as [[b2' d']|] eqn:Hj; try congruence. inv H0.
    rewrite pred_dec_true in H; eauto.
    destruct find eqn:FIND; try congruence.
    destruct p. inv H.

    assert (forall z, In z (perm_elements_any (ZMap.elements (mem_access m1 b)))
                 -> check_position (o0 - d) z = false).
    apply find_none. eauto.
    unfold perm. unfold perm_order'.
    destruct (((mem_access m1) # b) ## (o0 - d) Max) eqn:PERM.
    exploit H0. eapply in_perm_any; eauto.
    eapply elements_correct'. setoid_rewrite access_default.
    unfold NMap.get in PERM. intro. rewrite H1 in PERM. congruence.
    unfold check_position. simpl.
    rewrite pred_dec_true; eauto. intro. congruence. eauto.
  Qed.
  
  Lemma loc_in_reach_find'_none_rec : forall s b2 o2,
      loc_in_reach_find' b2 o2 s = None ->
      forall b1 d1, j12 b1 = Some (b2,d1) -> In b1 s -> ~ perm m1 b1 (o2 - d1) Max Nonempty.
  Proof.
    induction s; intros.
    - inv H1.
    - simpl in *. destruct block_find eqn:FIND. congruence.
      destruct H1. subst.
      eapply block_find_none; eauto. eauto.
Qed.
      
  Lemma loc_in_reach_find_none:
    forall b o, loc_in_reach_find b o = None -> loc_out_of_reach j12 m1 b o.
  Proof.
    intros. unfold loc_in_reach_find in H.
    red. intros. eapply loc_in_reach_find'_none_rec; eauto.
    inv INJ1. destruct (sup_dec b0 (support m1)). apply sup_list_in. auto.
    exploit mi_freeblocks0; eauto.
    intro. congruence.
  Qed.

End REVERSE.
(* update_mem_access *)

Fixpoint access_filter' (vl2 : list (Z * memperm)) (b2: block): list (Z * memperm) :=
  match vl2 with
  | nil => nil
  | (o2,_) :: tl =>
      match (loc_in_reach_find b2 o2) with
      |Some (b1,o1) => (o2,((mem_access m1')#b1)##o1) :: (access_filter' tl b2)
      |None => (access_filter' tl b2)
      end
  end.

Definition access_filter (b2 : block) :=
  let elements := ZMap.elements ((mem_access m2) # b2) in
  access_filter' elements b2.

Lemma access_filter'_none: forall map b2 o2,
    loc_in_reach_find b2 o2 = None ->   
   ~ In o2 (List.map fst (access_filter' (ZMap.elements map) b2)).
Proof.
  intros.
  induction (ZMap.elements map); intros.
  - simpl. eauto.
  - simpl. destruct a.
    destruct (loc_in_reach_find b2 t) eqn:FIND.
    + destruct p. intro. destruct H0.
      inv H0. simpl in H. congruence. eapply IHl; eauto.
    + eauto.
Qed.


Lemma access_filter_none: forall b2 o2,
    loc_in_reach_find b2 o2 = None ->   
   ~ In o2 (List.map fst (access_filter b2)).
Proof.
  intros.
  eapply access_filter'_none; eauto.
Qed.

Lemma access_filter'_rec : forall vl b2 o2 b1 o1,
    loc_in_reach_find b2 o2 = Some (b1, o1) ->
    In o2 (List.map fst vl) ->
    In (o2, ((mem_access m1') # b1) ##o1) (access_filter' vl b2).
Proof.
  induction vl; intros.
  - inv H0.
  - simpl in *. destruct a.
    destruct (loc_in_reach_find b2 z) eqn:FIND'.
    + destruct p. destruct H0. simpl in H0. inv H0.
      left. rewrite H in FIND'. inv FIND'. reflexivity.
      right. eauto.
    + destruct H0; eauto. simpl in H0. inv H0. congruence.
Qed.

Lemma access_filter_some: forall b2 o2 b1 o1,
    loc_in_reach_find b2 o2 = Some (b1, o1) ->
    In (o2, ((mem_access m1') # b1) ##o1) (access_filter b2).
Proof.
  intros.
  eapply access_filter'_rec; eauto.
  apply loc_in_reach_find_valid in H as H'. destruct H' as [MAP PERM1].
  exploit Mem.perm_inject; eauto. intro PERM2.
  replace (o1 + (o2 - o1)) with o2 in PERM2 by lia.
  unfold perm in PERM2.
  eapply in_map_fst_2.
  apply elements_correct'.
  intro. rewrite H0 in PERM2. rewrite access_default in PERM2.
  inv PERM2.
Qed.

(** update permission of all positions with nonempty permission of block b_2 *)
Definition copy_access_block (b2: block) (map2: perm_map) :=
  let elements2 := access_filter b2 in
  setN' elements2 map2.

Lemma In_access_filter'_any : forall vl b z,
    In z (List.map fst (access_filter' vl b)) -> In z (List.map fst vl).
Proof.
  induction vl; intros.
  - inv H.
  - simpl in H. destruct a. destruct loc_in_reach_find; eauto.
    destruct p. destruct H. simpl in H. subst.
    left. reflexivity. right. eauto. right. eauto.
Qed.

Lemma list_norepet_fst_access_filter':
  forall vl b,
    list_norepet (List.map fst vl) ->
    list_norepet (List.map fst (access_filter' vl b)).
Proof.
  induction vl; intros.
  - constructor.
  - simpl in H. inv H. simpl. destruct a.
    destruct loc_in_reach_find. destruct p.
    simpl. constructor.
    intro. apply H2. simpl.
    eapply In_access_filter'_any; eauto.
    eauto. eauto.
Qed.

Lemma access_filter_norepet: forall b2,
    list_norepet (List.map fst (access_filter b2)).
Proof.
  intros.
  eapply list_norepet_fst_access_filter'; eauto.
  eapply ZMap.elements_keys_norepet.
Qed.

Lemma copy_access_block_result:
  forall b2 map2 o2 p,
(*    (fst map2 = fun k => None) -> *)
    ((copy_access_block b2 map2)##o2) p =
      match (loc_in_reach_find b2 o2) with
      | Some (b1,o1) => ((mem_access m1')#b1)##o1 p
      | None =>  map2##o2 p
   end.
Proof.
  intros. unfold copy_access_block.
  destruct (loc_in_reach_find) as [[b1 o1]|] eqn:FIND.
  - erewrite setN'_inside; eauto.
    apply access_filter_norepet.
    apply access_filter_some; eauto.
  - erewrite setN'_outside; eauto.
    eapply access_filter_none; eauto.
Qed.

Definition is_Undef (mv : memval) : bool :=
  match mv with
  |Undef => true
  |_ => false
  end.


Fixpoint content_filter' (vl2 : list (Z * memperm)) (b2: block): list (Z * memval) :=
  match vl2 with
  | nil => nil
  | (o2,_) :: tl =>
      match (loc_in_reach_find b2 o2) with
      |Some (b1,o1) => if perm_dec m1' b1 o1 Cur Readable then
                          if perm_dec m1 b1 o1 Max Writable then
                           (o2, memval_map j12' ((mem_contents m1')#b1)##o1)
                             :: (content_filter' tl b2)
                             else (content_filter' tl b2)
                      else (content_filter' tl b2)
      |None => (content_filter' tl b2)
      end
  end.

Definition content_filter (b2 : block) :=
  let elements := ZMap.elements ((mem_access m2) # b2) in
  content_filter' elements b2.

Lemma content_filter'_none: forall map b2 o2,
    (loc_in_reach_find b2 o2 = None) ->   
   ~ In o2 (List.map fst (content_filter' (ZMap.elements map) b2)).
Proof.
  intros.
  induction (ZMap.elements map); intros.
  - simpl. eauto.
  - simpl. destruct a.
    destruct (loc_in_reach_find b2 t) eqn:FIND; eauto.
    destruct p. destruct perm_dec; eauto.
    destruct perm_dec; eauto.
    intro. destruct H0. inv H0. simpl in H. congruence.
    eapply IHl; eauto.
Qed.

Lemma content_filter'_none': forall map b2 o2 b1 o1,
    loc_in_reach_find b2 o2 = Some (b1, o1) ->
    (~ perm m1' b1 o1 Cur Readable \/ ~perm m1 b1 o1 Max Writable) ->
   ~ In o2 (List.map fst (content_filter' (ZMap.elements map) b2)).
Proof.
  intros.
  induction (ZMap.elements map); intros.
  - simpl. eauto.
  - simpl. destruct a.
    destruct (loc_in_reach_find b2 t) eqn:FIND; eauto.
    destruct p. destruct perm_dec; eauto. destruct perm_dec; eauto.
    intro. destruct H1. inv H1. simpl in H. rewrite H in FIND. inv FIND.
    destruct H0; try congruence. eapply IHl; eauto.
Qed.

Lemma content_filter_none: forall b2 o2,
    loc_in_reach_find b2 o2 = None ->   
   ~ In o2 (List.map fst (content_filter b2)).
Proof.
  intros.
  eapply content_filter'_none; eauto.
Qed.

Lemma content_filter_none': forall b2 o2 b1 o1,
    loc_in_reach_find b2 o2 = Some (b1,o1) ->
    (~ perm m1' b1 o1 Cur Readable \/ ~ perm m1 b1 o1 Max Writable) ->
   ~ In o2 (List.map fst (content_filter b2)).
Proof.
  intros.
  eapply content_filter'_none'; eauto.
Qed.

Lemma content_filter'_rec : forall vl b2 o2 b1 o1,
    loc_in_reach_find b2 o2 = Some (b1, o1) ->
    perm m1' b1 o1 Cur Readable -> perm m1 b1 o1 Max Writable ->
    In o2 (List.map fst vl) ->
    In (o2, memval_map j12' ((mem_contents m1')#b1)##o1) (content_filter' vl b2).
Proof.
  induction vl; intros.
  - inv H2.
  - simpl in *. destruct a.
    destruct H2.
    + simpl in H2. subst.
      rewrite H. destruct perm_dec; try congruence.
      destruct perm_dec; try congruence.
      left. eauto.
    + destruct (loc_in_reach_find b2 z) eqn:FIND'.
      * destruct p. destruct perm_dec; eauto.
        destruct perm_dec; eauto.
        right. eauto.
      * eauto.
Qed.

Lemma content_filter_some: forall b2 o2 b1 o1,
    loc_in_reach_find b2 o2 = Some (b1, o1) ->
    perm m1' b1 o1 Cur Readable -> perm m1 b1 o1 Max Writable ->
    In (o2, memval_map j12' ((mem_contents m1')#b1)##o1) (content_filter b2).
Proof.
  intros.
  eapply content_filter'_rec; eauto.
  apply loc_in_reach_find_valid in H as H'. destruct H' as [MAP PERM1].
  exploit Mem.perm_inject; eauto. intro PERM2.
  replace (o1 + (o2 - o1)) with o2 in PERM2 by lia.
  unfold perm in PERM2.
  eapply in_map_fst_2.
  apply elements_correct'.
  intro. rewrite H2 in PERM2. rewrite access_default in PERM2.
  inv PERM2.
Qed.

(* update contents of all positions with nonempty permission in block b_2 *)
Definition copy_content_block (b2: block) (vmap2: ZMap.t memval) :=
  let elements2 := content_filter b2 in
  setN' elements2 vmap2.

(* Lemma copy_content_block_default:
  forall b2 map2 vmap2, fst (copy_content_block b2 map2 vmap2) = fst vmap2.
Proof.
  intros. unfold copy_content_block.
  rewrite setN'_default. reflexivity.
Qed.
 *)

Lemma In_content_filter'_any : forall vl b z,
    In z (List.map fst (content_filter' vl b)) -> In z (List.map fst vl).
Proof.
  induction vl; intros.
  - inv H.
  - simpl in H. destruct a.
    destruct loc_in_reach_find; eauto. 2: right; eauto.
    destruct p. destruct perm_dec. 2: right; eauto.
    destruct perm_dec. 2: right; eauto.
    destruct H. simpl in H. subst.
    left. reflexivity. right. eauto.
Qed.

Lemma list_norepet_fst_content_filter':
  forall vl b,
    list_norepet (List.map fst vl) ->
    list_norepet (List.map fst (content_filter' vl b)).
Proof.
  induction vl; intros.
  - constructor.
  - simpl in H. inv H. simpl. destruct a.
    destruct loc_in_reach_find; eauto. destruct p.
    destruct perm_dec; eauto.
    destruct perm_dec; eauto.
    simpl. constructor.
    intro. apply H2. simpl.
    eapply In_content_filter'_any; eauto.
    eauto.
Qed.

Lemma content_filter_norepet: forall b2,
    list_norepet (List.map fst (content_filter b2)).
Proof.
  intros.
  eapply list_norepet_fst_content_filter'; eauto.
  eapply ZMap.elements_keys_norepet.
Qed.

Lemma copy_content_block_result:
  forall b2 vmap2 o2,
(*    (fst map2 = fun k => None) -> *)
    (copy_content_block b2 vmap2)##o2=
      match (loc_in_reach_find b2 o2) with
      | Some (b1,o1) =>
          let mv := ((mem_contents m1')#b1)##o1 in
          if perm_dec m1' b1 o1 Cur Readable then
            if perm_dec m1 b1 o1 Max Writable then memval_map j12' mv
            else vmap2##o2 else vmap2##o2
      | None =>  vmap2##o2
   end.
Proof.
  intros. unfold copy_content_block.
  destruct (loc_in_reach_find) as [[b1 o1]|] eqn:FIND.
  destruct (perm_dec m1' b1 o1 Cur Readable).
  - destruct (perm_dec m1 b1 o1 Max Writable).
    + erewrite setN'_inside; eauto.
      apply content_filter_norepet.
      apply content_filter_some; eauto.
    + erewrite setN'_outside; eauto.
      eapply content_filter'_none'; eauto.
  - erewrite setN'_outside; eauto.
    eapply content_filter'_none'; eauto.
  - erewrite setN'_outside; eauto.
    eapply content_filter_none; eauto.
Qed.

Lemma loc_in_reach_notin2:
  forall b o, ~ sup_In b (support m2) -> loc_in_reach_find b o = None.
Proof.
  intros. destruct (loc_in_reach_find b o) as [[b1 o1]|] eqn:FIND; eauto.
  exfalso. apply loc_in_reach_find_valid in FIND. destruct FIND as [A B].
  exploit Mem.perm_inject; eauto. replace (o1 + (o - o1)) with o by lia.
  intro. exploit nextblock_noaccess; eauto.
  intro. unfold perm in H0. rewrite H1 in H0. inv H0.
Qed.

 Program Definition copy_block b2 m : mem :=
   if j23 b2 then
      if (sup_dec b2 (Mem.support m)) then
      {|
        mem_contents := pmap_update b2
                          (copy_content_block b2)
                          (mem_contents m);
        mem_access := pmap_update b2
                        (copy_access_block b2)
                        (mem_access m);
        support := (Mem.support m);
      |}
        else m
   else m.
 Next Obligation.
   unfold pmap_update. rewrite NMap.gsspec.
   destruct NMap.elt_eq.
   - repeat rewrite copy_access_block_result.
     destruct loc_in_reach_find.
     + destruct p. apply access_max.
     + apply access_max.
   - apply access_max.
 Qed.
 Next Obligation.
   unfold pmap_update. rewrite NMap.gsspec.
   destruct NMap.elt_eq.
   - subst. congruence.
   - apply nextblock_noaccess; eauto.
 Qed.
 Next Obligation.
   unfold pmap_update. rewrite NMap.gsspec.
   destruct NMap.elt_eq.
   - subst. unfold copy_content_block. rewrite setN'_default.
     apply contents_default.
   - apply contents_default.
 Qed.
 Next Obligation.
   unfold pmap_update. rewrite NMap.gsspec.
   destruct eq_block; try apply access_default.
   unfold copy_access_block. rewrite setN'_default.
   apply access_default.
 Qed.
 
 Fixpoint copy_sup' (bl:list block) m : mem :=
   match bl with
   | nil => m
   | hd :: tl => copy_block hd (copy_sup' tl m)
   end.

 Definition copy_sup (s: sup) m : mem := copy_sup' (sup_list s) m.
 
 (** lemmas about step3 *)
 Lemma copy_block_support : forall b m m',
     copy_block b m = m' ->
     support m' = support m.
 Proof.
   intros. subst. unfold copy_block.
   destruct (j23 b); auto.
   destruct (sup_dec); auto.
 Qed.

 Lemma copy_sup_support' : forall s m m',
     copy_sup' s m = m' ->
     support m' = support m.
 Proof.
   induction s; intros; subst; simpl; eauto.
   erewrite copy_block_support. 2: eauto.
   eauto.
 Qed.

 Lemma copy_sup_support : forall s m m',
     copy_sup s m = m' ->
     support m' = support m.
 Proof.
   intros. eapply copy_sup_support'. eauto.
 Qed.

End STEP23.

End Mem.

Notation mem := Mem.mem.
Notation sup := Mem.sup.
Notation sup_In := Mem.sup_In.
Notation sup_incr := Mem.sup_incr.
Notation sup_empty := Mem.sup_empty.
Notation fresh_block := Mem.fresh_block.
Notation freshness := Mem.freshness.
Global Opaque Mem.alloc Mem.alloc_global Mem.free Mem.store Mem.load Mem.storebytes Mem.loadbytes.


Global Hint Resolve
  Mem.sup_incr_in1
  Mem.sup_incr_in2
  Mem.sup_incr_tid_in1
  Mem.sup_incr_tid_in2
  Mem.sup_list_in
  Mem.sup_include_refl
  Mem.sup_include_trans
  Mem.sup_include_incr
  Mem.match_sup_refl
  Mem.match_sup_trans
  : core.
Global Hint Resolve
  Mem.valid_not_valid_diff
  Mem.perm_implies
  Mem.perm_cur
  Mem.perm_max
  Mem.perm_valid_block
  Mem.range_perm_implies
  Mem.range_perm_cur
  Mem.range_perm_max
  Mem.valid_access_implies
  Mem.valid_access_valid_block
  Mem.valid_access_perm
  Mem.valid_access_load
  Mem.load_valid_access
  Mem.loadbytes_range_perm
  Mem.valid_access_store
  Mem.perm_store_1
  Mem.perm_store_2
  Mem.nextblock_store
  Mem.store_valid_block_1
  Mem.store_valid_block_2
  Mem.store_valid_access_1
  Mem.store_valid_access_2
  Mem.store_valid_access_3
  Mem.storebytes_range_perm
  Mem.perm_storebytes_1
  Mem.perm_storebytes_2
  Mem.storebytes_valid_access_1
  Mem.storebytes_valid_access_2
  Mem.nextblock_storebytes
  Mem.storebytes_valid_block_1
  Mem.storebytes_valid_block_2
  Mem.nextblock_alloc
  Mem.alloc_result
  Mem.valid_block_alloc
  Mem.fresh_block_alloc
  Mem.valid_new_block
  Mem.perm_alloc_1
  Mem.perm_alloc_2
  Mem.perm_alloc_3
  Mem.perm_alloc_4
  Mem.perm_alloc_inv
  Mem.valid_access_alloc_other
  Mem.valid_access_alloc_same
  Mem.valid_access_alloc_inv
  Mem.range_perm_free
  Mem.free_range_perm
  Mem.nextblock_free
  Mem.valid_block_free_1
  Mem.valid_block_free_2
  Mem.perm_free_1
  Mem.perm_free_2
  Mem.perm_free_3
  Mem.valid_access_free_1
  Mem.valid_access_free_2
  Mem.valid_access_free_inv_1
  Mem.valid_access_free_inv_2
  Mem.unchanged_on_refl
  Mem.unchanged_on_refl_tl
: mem.
