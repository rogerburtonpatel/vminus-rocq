Require Export stlc.syntax.
Require Export stlc.red.

Import RedNotations.
Import ScopedNotations. 

(** Proof that the small step relation is deterministic. *)


(* We know that if a term is a value then it cannot take a step. 
   This tactic automates that reasoning. *)
Ltac invert_value_step := 
  match goal with 
  | [H : Small.step (abs ?e1) ?e2 |- _ ] => inversion H
  | [H : Small.step (lit ?k) ?e2 |- _ ] => inversion H 
  | [H : Small.step (var ?x) ?e2 |- _ ] => inversion H
  | [H1 : is_value ?v = true, H2 : Small.step ?v ?e2 |- _] => 
      inversion H2; subst; cbn in H1 ; done
  end.

Lemma small_step_determinism : 
  forall e1 e2 , e1 ⤳ e2 -> forall e2', e1 ⤳ e2' -> e2 = e2'.
Proof.
  intros e1 e2 h1.
  induction h1; intros e3 h2; inversion h2; subst.
  all: eauto.
  all: try invert_value_step.
  all: try (erewrite IHh1; eauto).
Qed.

(* Lemma multi_step_value_determinism : 
  forall e1 e2 v1 v2, 
  is_value v1 = true -> is_value v2 = true -> 
  e1 ⤳* v1 -> e2 ⤳* v2 -> v1 = v2 -> e1 ⤳* e2.
Proof.
  intros.
  induction H2. 
  - rewrite <- H3. auto. 
  - specialize (IHmulti H0 H3). 
      

Qed. *)

(* ---------------------------------------------------------------------------- *)

(** Multi-step versions of each of the congruence 
   rules of the small step semantics. 
   
   For example, recall rule s_app_cong1 of the small-step relation:


           e1 ⤳ e1' 
    -------------------------- :: s_app_cong1
         e1 e2 ⤳ e1' e2

   In this module, we define lemma that creates a 
   "virtual rule" of the multi-step relation.

           e1 ⤳* e1' 
    -------------------------- :: ms_app_cong1
       e1 e2 ⤳* e1' e2

*)

(*
Small.s_app_cong1
  : forall e1 e1' e2 : Tm 0, e1 ⤳ e1' -> app e1 e2 ⤳ app e1' e2
*)

Lemma ms_app_cong1 e1 e1' e2 :  e1 ⤳* e1' ->  app e1 e2 ⤳* app e1' e2.
Proof.
  induction 1.
  eapply ms_refl.
  eapply ms_trans.
  eapply Small.s_app_cong1. eassumption.
  eapply IHmulti.
Qed.


(*
Small.s_app_cong2
  : forall v e2 e2' : Tm 0, is_value v = true -> e2 ⤳ e2' -> app v e2 ⤳ app v e2'
*)

Lemma ms_app_cong2 v e2 e2' : 
  is_value v = true ->  e2 ⤳* e2' ->  app v e2 ⤳* app v e2'.
Proof.
  intros h1 h2. 
  induction h2.
  eapply ms_refl.
  eapply ms_trans.
  eapply Small.s_app_cong2. 
  assumption. eassumption.
  eapply IHh2.
Qed.

(* Small.s_beta
     : forall (e : Tm 1) (v : Tm 0),
is_value v = true -> app (abs e) v ⤳ e [v..] *)

Lemma ms_beta : forall (e : Tm 1) (v : Tm 0),
is_value v = true -> app (abs e) v ⤳* e [v..].
Proof. 
  intros. apply ms_one. apply Small.s_beta. auto. 
Qed. 

Lemma ms_succ_cong e e' : 
  e ⤳* e' ->  succ e ⤳* succ e'.
Proof.
  induction 1. 
  eapply ms_refl.
  eapply ms_trans.
  eapply Small.s_succ_cong. 
  eauto. eassumption.
Qed.

(* Small.s_nrec_zero
     : forall (e0 : Tm 0) (e1 : Tm 1), nrec (lit 0) e0 e1
⤳ e0 *)

(* Lemma ms_subst e v v1 : 
is_value v = true -> is_value v1 = true -> (e [v1..] ⤳* v) -> app (abs e) v1 ⤳* v. 
Proof. 
  intros. 
  apply ms_one. 
  Search (multi).  *)

Lemma ms_nrec_zero e0 e1 e0' :
  e0 ⤳* e0' -> nrec (lit 0) e0 e1 ⤳* e0'. 
Proof. 
  intros. 
  specialize (Small.s_nrec_zero e0 e1) as nrec0. 
  apply ms_one in nrec0. 
  apply (ms_app nrec0 H). 
Qed. 



(* Small.s_nrec_cong
     : forall (e e' e0 : Tm 0) (e1 : Tm 1),
e ⤳ e' -> nrec e e0 e1 ⤳ nrec e' e0 e1 *)

(* paper: State lemma. Proof: By induction on 
e e ⤳* e' *)

Lemma ms_nrec_cong e e' e0 e1 :
  e ⤳* e' -> nrec e e0 e1 ⤳* nrec e' e0 e1. 
Proof. 
  induction 1. 
  - apply ms_refl. 
  - specialize (Small.s_nrec_cong e2 e3 e0 e1 H) as nrec_cong.
    apply (ms_trans nrec_cong IHmulti).
Qed. 

(* Small.s_nrec_succ
     : forall (k : nat) (e0 : Tm 0) (e1 : Tm 1),
nrec (lit (S k)) e0 e1
⤳ app (subst1 (scons (lit k) ids) e1)
(nrec (lit k) e0 e1) *)

(* Lemma ms_nrec_succ :
  forall (k : nat) (e0 : Tm 0) (e1 : Tm 1),
  nrec (lit (S k)) e0 e1
  ⤳* app (subst1 (scons (lit k) ids) e1)
  (nrec (lit k) e0 e1). 
Proof. 
  intros. apply ms_one. apply Small.s_nrec_succ. 
Qed.  *)

(* questions: 

2. lifting to multi- manual is tedious. alternative? *)
Lemma ms_nrec_succ : forall e e' e0 e1 v1 v k, 
is_value v1 = true -> is_value v = true -> 
(e ⤳* lit (S k)) -> 
(e1 [(lit k)..] ⤳* abs e') -> 
(nrec (lit k) e0 e1 ⤳* v1) -> 
(e' [v1..] ⤳* v)  -> 
  nrec e e0 e1
  ⤳* v. 
Proof. 
- intros. 

  specialize (ms_nrec_cong e (lit (S k)) e0 e1 H1) as nrec_cong.

  specialize (Small.s_nrec_succ k e0 e1) as nrec_succ.
  apply ms_one in nrec_succ. 

  specialize (ms_app nrec_cong nrec_succ) as nrec_app. 

  specialize (ms_app_cong1 (e1 [(lit k)..]) (abs e') (nrec (lit k) e0 e1) H2) as app_cong1.
  
  destruct (is_value (abs e')) eqn:abs_value; try easy. 

  specialize (ms_app_cong2 _ _ _ abs_value H3) as app_cong2. 

  specialize (ms_beta e' v H0) as beta.

  specialize (ms_app nrec_app app_cong1) as step2. 
  specialize (ms_app step2 app_cong2) as step3. 
  specialize (ms_app step3 (ms_beta _ _ H)) as step4. 
  specialize (ms_app step4 H4) as step5. 
  apply step5. 
Qed. 
(* bless *)

(* Small.s_letv
     : forall (v : Tm 0) (e : Tm 1),
is_value v = true -> let_ v e ⤳ e [v..] *)

(* not necessary but good for consistency. *)

Lemma ms_letv : 
forall (v : Tm 0) (e : Tm 1),
  is_value v = true -> let_ v e ⤳* e [v..]. 
Proof. 
  intros. apply ms_one. apply Small.s_letv. auto.  
Qed. 

Lemma ms_let_cong e1 e2 v1 v2 :
is_value v1 = true -> is_value v2 = true -> 
(e1 ⤳* v1) -> 
(e2 [v1..] ⤳* v2) -> 
let_ e1 e2 ⤳* v2.  
Proof. 
  intros.   
  induction H1.
  - apply (ms_app (ms_letv e e2 H) H2). 
  - apply (IHmulti H) in H2.
    specialize (Small.s_let_cong e1 e0 e2 H1) as H5. 
    apply (ms_trans H5 H2).
Qed.


