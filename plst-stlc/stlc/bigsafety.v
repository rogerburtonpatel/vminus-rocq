From Stdlib Require Export ssreflect.
From Stdlib Require Export Program.Equality.
Require Export common.fintype.
Require Export common.core.

(**
   This file considers two alternative versions of type safety for 
   the core STLC language (not include lit/nrec).
 *)
Require Export stlc.syntax.

(* This line imports the tactic 'lia' for reasoning about linear integer 
   arithmetic. It can solve goals that involve natural numbers and basic 
   operations *)
From Stdlib Require Import Psatz.

(* We will use a little more automation in this example. *)
Create HintDb bigstep.

Import ScopedNotations. 
Module SyntaxNotations.
Notation "⇑ σ" := (var var_zero .: σ >> ren_Tm ↑) (at level 70) : subst_scope.
End SyntaxNotations.
Import SyntaxNotations.

(** test the form of a term *)
Definition is_abs (e : Tm 0) := 
  match e with 
  | abs _ => true
  | _ => false
  end.

Definition is_lit (e : Tm 0) := 
  match e with 
  | lit _ => true
  | _ => false
  end.

(** decide whether a term is a value *)
Definition is_value {n} (e : Tm n) : bool := 
  match e with 
  | abs _ => true
  | lit k => true
  | _ => false
  end.

(** Typing relation *)

Definition Ctx (n : nat) := fin n -> Ty.

Inductive typing {n} (Γ : Ctx n) : Tm n -> Ty -> Prop := 
  | t_var x : 
    typing Γ (var x) (Γ x)

  | t_abs e τ1 τ2 : 
    typing (τ1 .: Γ) e τ2 -> 
    typing Γ (abs e) (Arr τ1 τ2)

  | t_app e1 e2 τ1 τ2 : 
    typing Γ e1 (Arr τ1 τ2) -> 
    typing Γ e2 τ1 -> 
    typing Γ (app e1 e2) τ2

  | t_lit k : 
    typing Γ (lit k) Nat
.

Module TypingNotations.
Export ScopedNotations.
Export SyntaxNotations.
Notation "Γ |- e ∈ τ" := (typing Γ e τ) (at level 70).
End TypingNotations.
Import TypingNotations.

Definition typing_renaming {A}{n} (Δ : fin n -> A) {m} (δ : fin m -> fin n)
  (Γ : fin m -> A) : Prop := 
  forall x, Γ x = Δ (δ x).

(** The identity renaming preserves the context *)
Lemma typing_renaming_id {A}{n} (Δ : fin n -> A) :
  typing_renaming Δ id Δ.
Proof. unfold typing_renaming. intros x. done. Qed.

(** Extend a renaming with a new definition *)
Lemma typing_renaming_cons {A}{n} (Δ : fin n -> A) 
  {m} (Γ : fin m -> A) (δ : fin m -> fin n) (τ : A) (x : fin n) :
  typing_renaming Δ δ Γ ->
  typing_renaming Δ (x .: δ) (Δ x .: Γ).
Proof. intro h. unfold typing_renaming in *. auto_case. Qed.

(** Lift a renaming to a new scope *)
Lemma typing_renaming_lift {A}{n} (Δ : fin n -> A) 
  {m} (Γ : fin m -> A) (δ : fin m -> fin n) (τ : A) :
  typing_renaming Δ δ Γ ->
  typing_renaming (τ .: Δ) (up_ren δ) (τ .: Γ).
Proof. intro h. unfold typing_renaming in *. auto_case. Qed.

(** The typing judgement is stable under renaming *)
Lemma renaming {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ : 
  Γ |- e ∈ τ -> typing_renaming Δ δ Γ -> Δ |- e⟨δ⟩ ∈ τ.
Proof.
  intros h.
  (* ssreflect tactic for generalization. We need a strong IH. *)
  move: m Δ δ.
  induction h.
  all: intros m Δ δ tS.
  all: asimpl.
  - unfold typing_renaming in tS.
    rewrite tS.
    eapply t_var; eauto.
  - eapply t_abs; eauto.
    eapply IHh.
    eapply typing_renaming_lift; auto.
  - eapply t_app; eauto.
  - eapply t_lit; eauto.
Qed. 

(* Here's a more automated proof of the renaming lemma. *)
Example renaming' {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) δ : 
  Γ |- e ∈ τ -> typing_renaming Δ δ Γ -> Δ |- e⟨δ⟩ ∈ τ.
Proof.
  move=> h. move: m Δ δ. 
  (* every case except var *)
  induction h; intros; asimpl; 
    try econstructor; eauto using typing_renaming_lift.
  (* var case *)
  unfold typing_renaming in *; rewrite H; econstructor; eauto.
Qed.

(** A substitution transforms terms from context Γ to context Δ when the types
    declared in Γ are consistent with the types in Δ. *)
Definition typing_subst {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) : Prop := 
  forall x, typing Δ (σ x) (Γ x).

(** The empty substitution closes the term *)
Lemma typing_subst_null {n} (Δ : Ctx n) :
  typing_subst Δ null null.
Proof. unfold typing_subst. auto_case. Qed.

(** The identity substitution preserves the context *)
Lemma typing_subst_id {n} (Δ : Ctx n) :
  typing_subst Δ var Δ.
Proof. unfold typing_subst. intro x. econstructor. Qed.

Lemma typing_subst_cons {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) e τ : 
 typing Δ e τ ->
 typing_subst Δ σ Γ ->
 typing_subst Δ (e .: σ) (τ .: Γ).
Proof.
  intros tE tS.
  unfold typing_subst in *.
  intro x. destruct x as [y|].
  asimpl. eauto.
  asimpl. eauto.
Qed.

Lemma typing_subst_lift {n} (Δ : Ctx n) {m} (σ : fin m -> Tm n)
  (Γ : Ctx m) τ : 
  typing_subst Δ σ Γ ->
  typing_subst (τ .: Δ) (⇑ σ) (τ .: Γ).
Proof.
  unfold typing_subst in *.
  intros h.
  auto_case.
  + unfold_funcomp.
    eapply renaming; eauto. 
    unfold typing_renaming. asimpl. done.
  + asimpl. eapply t_var.
Qed.

Lemma substitution {n} (Γ : Ctx n) e τ {m} (Δ:Ctx m) σ : 
  typing Γ e τ -> typing_subst Δ σ Γ -> typing Δ e[σ] τ.
Proof.
  move=> h.
  move: m Δ σ.
  induction h.
  all: intros m Δ σ tS.
  all: asimpl.
  - eauto. 
  - eapply t_abs.
    eapply IHh.
    eapply typing_subst_lift. auto.
  - eapply t_app; eauto.
  - eapply t_lit; eauto.
Qed.

Corollary single_substitution {n}{Γ : Ctx n}{e v τ τ1}:
  typing (τ1 .: Γ) e τ -> typing Γ v τ1 -> 
  typing Γ e[v..] τ.
Proof. 
  intros h1 h2.
  eapply substitution; eauto.
  eapply typing_subst_cons; eauto.
  eapply typing_subst_id; eauto.
Qed.

Corollary single_weakening {n}{Γ : Ctx n}{ e τ τ1 } : 
  typing Γ e τ -> typing (τ1 .: Γ) e⟨↑⟩ τ.
Proof. 
  intros h1.
  eapply renaming. eauto.
  unfold typing_renaming.
  intro x. asimpl.
  done.
Qed.

Lemma canonical_forms_Arr e τ1 τ2 : 
  null |- e ∈ Arr τ1 τ2 ->
  is_value e = true ->
  exists e', e = abs e'.
Proof.
  intros h V.
  destruct e; cbn in h; try done.
  all: inversion h.
  eexists. eauto.
Qed.


(** ---------- a big step semantics w/type errors -------------- *)

(* The problem with a big-step semantics is that it doesn't distinguish 
   between a program getting stuck and failing to terminate. 

   This module refines that semantics so that we now have two possible 
   results: either we get a value, or the program could get stuck.
*)

Module NotStuck.

Variant Result := Stuck | Value of Tm 0.

Inductive step : Tm 0 -> Result -> Prop := 

  (* Same two rules as before *)
  | ts_val e : 
    is_value e = true -> 
    step e (Value e)

  | ts_app e1 e1' e2 v1 r :
    step e1 (Value (abs e1')) -> 
    step e2 (Value v1) -> 
    step (e1'[v1..]) r -> 
    step (app e1 e2) r
         
  (* An application to a value that is *not* an abstraction
     is stuck *)
  | ts_app_stuck e1 v e2 : 
    step e1 (Value v) -> 
    negb (is_abs v) = true ->
    step (app e1 e2) Stuck

  (* If the first part of an application is stuck, the whole 
     application is stuck. *)
  | ts_app1 e1 e2 :
    step e1 Stuck -> 
    step (app e1 e2) Stuck

  (* If the second part of an application is stuck, the whole 
     application is stuck. Note that we need the first one to 
     produce a value. The reason for this is subtle, but we 
     need to make sure that e1 does not diverge.
     If it diverges, we want the entire expression to diverge.
     *)
  | ts_app2 e1 e2 v :
    step e1 (Value v) -> 
    step e2 Stuck -> 
    step (app e1 e2) Stuck
.      

Hint Constructors step : bigstep.

(** STATE and PROVE type safety (not stuck) here *)

(* Lemma typing_arr_steps : forall e1 τ1 τ2, 
  null |- e1 ∈ Arr τ1 τ2 -> exists r, step e1 r. 
Proof. 
  intros. 
   dependent induction e1; try easy.
   - exists (Value (abs e1)). 
     apply ts_val. auto. 
     - 
     inversion H. 
     edestruct (IHe1_1 e1_1 eq_refl JMeq_refl); eauto.
     (* edestruct (IHe1_2 e1_2 eq_refl JMeq_refl); eauto. *)
      destruct x eqn:eq.
      -- exists Stuck. apply ts_app1. auto. 
      -- exists (Value t).  *)

  (* intros. destruct (is_value e1) eqn:eq. 
  - specialize (canonical_forms_Arr _ _ _ H eq). intros [e' H0].
  exists e'. subst. apply ts_val. auto. 
  -  *)

  

Lemma Value_value : forall e v, 
    step e (Value v) -> is_value v = true. 
Proof. 
  intros. dependent induction H; auto.
Qed. 

Lemma NotStuckTyping : forall e τ r, 
  null |- e ∈ τ /\ step e r -> exists v, r = Value v /\ null |- v ∈ τ.

  Proof. 
    intros. destruct H. 
    generalize dependent τ. 
    dependent induction H0; intros. 
    - exists e. 
    split; auto. 
    - inversion H; subst.
      apply IHstep3. 
      eapply substitution.  
      -- apply IHstep1 in H2 as (v' & [= <-] & teq).
         inversion teq; subst; eauto.  
      -- apply typing_subst_cons.
        --- specialize (IHstep2 τ1 H4) as (v' & [= <-] & teq); auto. 
        --- apply typing_subst_id.
    - inversion H1; subst. 
      specialize (IHstep _ H4) as (v' & [= <-] & teq).
      apply canonical_forms_Arr in teq as (e' & [= ->]).
      discriminate H. 
      apply Value_value in H0. auto. 
    - inversion H. 
      specialize (IHstep (Arr τ1 τ) H3) as (v' & contra & _).
      discriminate contra. 
    - inversion H. 
      specialize (IHstep2 τ1 H4) as (v' & contra & _).
      discriminate contra. 
  Qed. 
       


Theorem NotStuck : forall e τ r, 
  null |- e ∈ τ /\ step e r -> r <> Stuck.
  Proof. 
    intros. 
    specialize (NotStuckTyping e τ r H) as (v & Val & _). 
    unfold not. intros; subst; easy. 
  Qed.  
    
    (* unfold not. intros. subst. 
      inversion H1.
    -- 
    apply canonical_forms_Arr in H as [e' H].     *)
      
       

CoInductive diverges : Tm 0 -> Prop := 
  | d_app_1 : forall (e1 : Tm 0) (e2  : Tm 0), 
    diverges e1 ->
    diverges (app e1 e2)
  | d_app_2 : forall e1 e2 e1', 
    step e1 (Value (abs e1')) -> 
    diverges e2 ->
    diverges (app e1 e2)
  | d_app_3 : forall e1 e2 e1' v1, 
    step e1 (Value (abs e1')) -> 
    step e2 (Value v1) -> 
    diverges (e1'[v1..]) ->
    diverges (app e1 e2).

Lemma deterministic : forall e r1, 
    step e r1 -> forall r2, step e r2 -> r1 = r2.
Proof. 
  intros e r1 h1. 
  induction h1.
  - intros r2 h2. inversion h2; subst; cbn in H; done.
  - intros r2 h2. 
    inversion h2; subst; try cbn in H; try done.
    + specialize (IHh1_1 _ H1). inversion IHh1_1; subst.
      specialize (IHh1_2 _ H2). inversion IHh1_2; subst.
      specialize (IHh1_3 _ H4). done.
    + specialize (IHh1_1 _ H1). inversion IHh1_1; subst.
      cbn in H3. done.
    + specialize (IHh1_1 _ H2). inversion IHh1_1; subst.
    + specialize (IHh1_1 _ H1). inversion IHh1_1; subst.
      specialize (IHh1_2 _ H3). inversion IHh1_2; subst.
  - intros r2 h2.
    inversion h2; subst; try cbn in H; try done.
    specialize (IHh1 _ H2). inversion IHh1; subst.
    cbn in H. done.
  - intros r2 h2. 
    inversion h2; subst; try cbn in H; try done.
    specialize (IHh1 _ H1). inversion IHh1; subst.
  - intros r2 h2.
    inversion h2; subst; try cbn in H; try done.
    specialize (IHh1_2 _ H2). inversion IHh1_2; subst.
Qed.    


Lemma diverges_nostep : 
  forall e, diverges e -> forall r, not (step e r).
Proof.
  intros e D r h.
  induction h.
  - destruct D; cbn in H; done.
  - inversion D; subst.
    + done.
    + done.
    + move: (deterministic _ _ h1 _ H1) => EQ. inversion EQ. subst. clear EQ.
      move: (deterministic _ _ h2 _ H2) => EQ.  inversion EQ. subst. clear EQ.
      done.
  - (* case ts_app_stuck. e gets stuck, so it cannot diverge *)
    inversion D; subst.
    + done.
    + move: (deterministic _ _ h _ H2) => EQ. inversion EQ. subst. clear EQ.
      done.
    + move: (deterministic _ _ h _ H2) => EQ. inversion EQ. subst. clear EQ.
      done.
  - (* case ts_app1 *)
    inversion D; subst.
    + done.
    + move: (deterministic _ _ h _ H1) => EQ. inversion EQ. 
    + move: (deterministic _ _ h _ H1) => EQ. inversion EQ. 
  - (* case ts_app2 *)
    inversion D; subst.
    + done.
    + done.  
    + move: (deterministic _ _ h2 _ H2) => EQ. inversion EQ. 
Qed. 

(* We would like to prove this opposite. But this is impossible to 
   prove without using classical logic. *)
Lemma nostep_diverge : forall e, (forall r, not (step e r)) -> diverges e.
Proof.
Abort.



End NotStuck.

(* ---------- a stepped big step semantics w/timeout ---------- *)

Module RunsSafely.

Variant Result := Timeout | Value of Tm 0.

(* A program evaluates safely for k steps, if it either 
   halts with a *value* for some number of steps < k, or 
   if it steps for exactly k steps (i.e. doesn't get stuck). *)

Inductive step_k : nat -> Tm 0 -> Result -> Prop := 

  | ts_timeout e : 
    (* Must use *all* of the fuel to time out *)
    step_k 0 e Timeout

  | ts_val e n : 
    (* Must have some fuel left to produce a value *)
    is_value e = true -> 
    step_k (S n) e (Value e)

  | ts_app : forall n (e1 : Tm 0) (e1' : Tm 1) (e2 v1 v2 : Tm 0) r, 
    (* normal application rule *)
    step_k n e1 (Value (abs e1')) -> 
    step_k n e2 (Value v1) -> 
    step_k n (e1'[v1..]) r -> 
    step_k (S n) (app e1 e2) r

  | ts_app1 : forall n (e1 : Tm 0) (e2  : Tm 0), 
    (* argument takes too long *)
    step_k n e1 Timeout -> 
    step_k (S n) (app e1 e2) Timeout

  | ts_app2 : forall n (e1 : Tm 0) (e2 : Tm 0), 
    (* result takes too long *)
    step_k n e2 Timeout -> 
    step_k (S n) (app e1 e2) Timeout
.

(* Lemma step_dclosed : forall (e v : Tm 0) (k : nat) (τ : Ty), 
null |- e ∈ τ -> 
step_k (S k) e (Value v) -> step_k k e (Value v). 
Proof. 
  intros. 
  dependent induction H0. 
  destruct τ.  *)
  
Lemma Value_value : forall e v k, 
    step_k k e (Value v) -> is_value v = true. 
Proof. 
  intros. dependent induction H; auto.
Qed. 

(* another version of this *)
Lemma steps_to_value : forall (e v : Tm 0) (k : nat), 
step_k k e (Value v) -> is_value v = true. 
Proof. 
  intros.
  generalize dependent e. 
  induction k; intros. 
  (* H0 can't be true *)
  - easy. 
  - inversion H; subst. 
  -- assumption. 
  -- apply IHk in H3; auto. 
Qed.  

Lemma preservation : forall e v k τ,
null |- e ∈ τ ->  
step_k k e (Value v) -> null |- v ∈ τ.
Proof. 
  intros. 
  generalize dependent τ. 
  dependent induction H0; intros. 
  - auto.
  - inversion H; subst.
    (* auto removes trivial dependent cases *)
    apply IHstep_k3; auto. 
    eapply substitution. 
    (* we know e1' has type τ by IH1 *)
    -- specialize (IHstep_k1 (abs e1') eq_refl _ H2) as IHe1. 
       inversion IHe1. eauto. 
    -- apply typing_subst_cons.
    (* we know v1 has type τ1 by IH2 *)
       specialize (IHstep_k2 v1 eq_refl _ H4) as IHe2. 
       auto. 
    apply typing_subst_id.
Qed.   
    


  Theorem timeout_safety : forall k e τ, null |- e ∈ τ ->  
    exists r, step_k k e r. 
  Proof.
   induction k; intros. 
   (* base case: always timeout. *)
   - exists Timeout. apply ts_timeout.
   - destruct e.
   (* no term has type 0__Tm. *)
    + destruct f.  
    (* lambdas step to themselves. *)
    + eexists. constructor. 
      reflexivity. 
    (* app case *)
    + inversion H; subst.
      apply IHk in H2 as H3; destruct H3 as [r1 H3].
      apply IHk in H4 as H5; destruct H5 as [r2 H5].
      destruct r1; 
      (* any case in which either e1 or e2 times out 
      is trivial. *)
      try solve [exists Timeout; constructor ; auto].
      destruct r2; 
      try solve [exists Timeout; constructor ; auto].
    (* interesting case: e1 and and e2 step to values. *)
    apply steps_to_value in H3 as H6.
    (* know t is abs *)
    specialize (preservation e1 t k _ H2 H3) as pres_e1. 
    assert (t_abs: exists e', t = abs e'). 
    { eapply canonical_forms_Arr; eauto. } 
    destruct t_abs as (e' & ->).
    specialize (IHk (e' [t0..]) τ).
    assert (subst_typing: null |- e' [t0..] ∈ τ).
    {
      eapply substitution.
      inversion pres_e1. eauto. 
      apply typing_subst_cons. 
      eapply preservation; eauto.
      apply typing_subst_id.  
    }
    apply IHk in subst_typing as (r & subst_step).
    exists r. 
    apply (ts_app _ _ _ _ _ t0 _ H3 H5).
    auto. 
    (* lit case; easy *)
    + exists (Value (lit n)). constructor. reflexivity. 
    (* succ, nrec: need to add rules *)
    + admit. 
    + admit. 
  Admitted.  
End RunsSafely.
