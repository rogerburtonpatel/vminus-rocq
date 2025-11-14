(* Show that small-step and big-step are equivalent. *)
Require Import stlc.red.
Require Import stlc.typing.
Require Import stlc.small_step.

Import TypingNotations.
Import RedNotations.

(** Our goal for this section is to prove that if e ~>* v then e ⇓ v.
To do so, we need to look at each big step rule and derive a corresponding 
small step rule of the semantics. *)

Module BigSmall.

(* Big.s_val
     : forall v : Tm 0, is_value v = true -> v ⇓ v *)

Lemma s_val : forall v, is_value v = true -> v ⟱ v.
Proof.
  intros v h.
  split; eauto. 
  eapply ms_refl; eauto.
Qed.

(* Big.s_app
     : forall (e1 : Tm 0) (e1' : Tm 1) (e2 v1 v2 : Tm 0), 
       e1 ⇓ abs e1' -> e2 ⇓ v1 -> e1'[v1..] ⇓ v2 -> app e1 e2 ⇓ v2 *)

Lemma s_app : 
  forall (e1 : Tm 0) (e1' : Tm 1) (e2 v1 v2 : Tm 0), 
      e1 ⟱ abs e1' -> e2 ⟱ v1 -> e1'[v1 ..] ⟱ v2 -> app e1 e2 ⟱ v2.
Proof.
  intros e1 e1' e2 v1 v2 [h1 _] [h2 Vv1] [h3 Vv2].
  split; auto.
  eapply @ms_app with (e2 := app (abs e1') e2).
  { eapply ms_app_cong1; eauto. }
  eapply @ms_app with (e2 := app (abs e1') v1).
  { eapply ms_app_cong2; eauto. }
  eapply ms_trans. eapply Small.s_beta. auto. auto.
Qed.

Lemma s_succ : 
  forall (e : Tm 0) (k : nat),
  e ⟱ (lit k) -> succ e ⟱ lit (S k). 
  Proof. 
    intros. destruct H.
    split; auto. 
    specialize (ms_succ_cong e (lit k) H) as succ_mstep. 
    specialize (Small.s_succ_lit k) as succ_step. 
    specialize (ms_add_single Small.step succ_mstep succ_step).
    trivial. 
Qed. 

Lemma s_nrec_0 : 
  forall (e e0 v : Tm 0) (e1 : Tm 1),
  e ⟱ (lit 0) -> e0 ⟱ v -> nrec e e0 e1 ⟱ v. 
  Proof. 
    intros.
    destruct H0. 
    split; auto. 
    destruct H. 
    specialize (ms_nrec_cong e (lit 0) e0 e1 H) as nrec_cong. 
    specialize (ms_nrec_zero e0 e1 v H0) as nrec_0.
    apply (ms_app nrec_cong nrec_0). 
Qed. 

Lemma s_nrec_succ : 
  forall (e e0 v v1 : Tm 0) (e' e1 : Tm 1) (k : nat),
is_value v1 = true -> is_value v = true -> 
(e ⟱ lit (S k)) -> 
(e1 [(lit k)..] ⟱ abs e') -> 
(nrec (lit k) e0 e1 ⟱ v1) -> 
(e' [v1..] ⟱ v)  -> 
  nrec e e0 e1
  ⟱ v. 
Proof.
  intros. 
  destruct H1, H2, H3, H4. 
  split; auto. 
  apply (ms_nrec_succ _ _ _ _ _ _ _ H H0 H1 H2 H3 H4).
Qed. 

Lemma s_let_cong e1 e2 v1 v2 :
(e1 ⟱ v1) -> 
(e2 [v1..] ⟱ v2) -> 
let_ e1 e2 ⟱ v2.  
Proof.
  intros. 
  destruct H, H0. 
  split; auto. 
  apply (ms_let_cong e1 e2 v1 v2 H1 H2 H H0). 
Qed. 
  
Lemma same_semantics : 
  (forall e v, e ⇓ v  -> e ⟱ v).
Proof.
  intros e v h. induction h. 
  - eapply s_val; auto.
  - eapply s_app; eauto.
  - eapply s_succ; eauto. 
  - eapply s_nrec_0; eauto. 
  - destruct IHh3. destruct IHh4. 
    eapply (s_nrec_succ e e0 v v1); eauto.  
  - eapply s_let_cong; eauto.  
Qed. 
End BigSmall.

Module SmallBig.

Lemma same_semantics_step : 
  (forall e e', (e ⤳ e') -> forall v, e' ⇓ v -> e ⇓ v).
Proof.
  intros e e' h1.
  induction h1.
  all: intros w h2.
  - eapply Big.s_app. eapply Big.s_val; auto.
       eapply Big.s_val; eauto.
       eauto.
  - inversion h2; try done. subst. clear h2.
    eapply Big.s_app; eauto.
  - inversion h2; try done. subst. clear h2.
    eapply Big.s_app; eauto.
  - inversion h2; try done. subst. clear h2. 
    eapply Big.s_succ; eauto. 
    destruct (@is_value 0 (lit k)) eqn:litkval; try easy.
    apply Big.s_val; auto. 
  - inversion h2; try done. subst. clear h2. 
    apply IHh1 in H0. 
    apply Big.s_succ. auto. 
  - apply Big.s_nrec_zero; auto using Big.s_val. 
  - inversion h2; try done. subst. clear h2. 
    eapply Big.s_nrec_succ; eauto.   
    apply Big.s_val; auto. 
  - inversion h2; try done. subst. clear h2. 
    apply IHh1 in H3. apply Big.s_nrec_zero; eauto. 
    eapply Big.s_nrec_succ; eauto. 
  - apply (Big.s_let _ _ v w); auto using Big.s_val. 
  - inversion h2. try done. subst. clear h2. 
    eapply Big.s_let; eauto. 
Qed. 
    

Lemma same_semantics : forall e v,  e ⟱ v -> e ⇓ v.
Proof.
  intros e v [h V].
  induction h.
  - eapply Big.s_val; auto.
  - eapply same_semantics_step; eauto.
Qed.

End SmallBig.

