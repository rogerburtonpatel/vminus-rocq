Require Import stlc.typing.
Require Import stlc.red.
Require Import stlc.safety.

Import TypingNotations.
Import RedNotations.

(* ----------------------------------------------------- *)

Module Big.
Import red.Big.

(* Exercise: where does the following proof go wrong? *)

Lemma type_safety : forall e τ, null |- e ∈ τ -> exists v, e ⇓ v.
Proof.
  intros e τ h.
  dependent induction h.
Abort.

(* ----------------------------------------------------- *)


(* We cannot state type safety for a big step semantics. 
   But, we can prove a *stronger* theorem: that all 
   well-typed programs terminate. *)

(** Value set: a Semantic sets of values, indexed by type.
    
    We represent the set as a characteristic function; i.e. 
    a function from the term to the proposition that holds
    when the term is in the set.
 *)
Fixpoint V (τ : Ty) : Tm 0 -> Prop := 
  match τ with 
  | Nat => 
      (* all terms v that are equal to some literal *)
      fun v =>
        exists k, v = lit k
  | Arr τ1 τ2 =>
      fun v => 
        exists e', v = abs e' /\
                  forall w1, V τ1 w1 -> 
                     exists w2, e'[w1..] ⇓ w2 /\ V τ2 w2
  end.


(** Computation set: the set of terms that evaluate to values in the value set. *)
Definition C (τ : Ty) : Tm 0 -> Prop := 
  fun e =>  exists v, e ⇓ v /\ V τ v.

(* We want to prove that all well typed terms are in the Comp set. But we need 
 to extend to open terms. *)

Definition Env n := fin n -> Tm 0.

Definition semantic_subst {n} (Γ : Ctx n) (ρ : Env n) := 
  forall x, V (Γ x) (ρ x). 

Definition semantic_typing {n} (Γ : Ctx n) e τ :=
  forall ρ, semantic_subst Γ ρ -> C τ e[ρ].

Module SoundnessNotation.
Notation "V⟦ τ ⟧" := (V τ).
Notation "C⟦ τ ⟧" := (C τ).
Notation "Γ⟦ Γ ⟧" := (semantic_subst Γ). 
Notation "Γ ⊨ e ∈ τ" := (semantic_typing Γ e τ) (at level 70).
End SoundnessNotation.

Import SoundnessNotation.

(* All elements of the value set are values *)
Lemma is_value_V τ v : V⟦ τ ⟧ v -> is_value v = true. 
Proof.
  induction τ.
  - (* nat type *) 
    intro h. 
    destruct h as [k h].
    subst. done.
  - (* arrow type *)
    cbn.
    intros [e' [-> h]].
    cbn. done.
Qed.

Lemma semantic_subst_cons {τ v} {n} {Γ : Ctx n} {ρ} : 
  V⟦ τ ⟧ v ->
  Γ⟦ Γ ⟧ ρ -> 
  Γ⟦ τ .: Γ ⟧ (v .: ρ).
Proof.
  unfold semantic_subst.
  intros Vv h.
  (* talk to me about this tactic *)
  auto_case.
Qed.


Lemma semantic_var {n} (Γ : Ctx n) x : 
  Γ ⊨ var x ∈ Γ x.
Proof. 
  unfold semantic_typing.
  intros ρ ρH.
  specialize (ρH x). exists (ρ x). 
(*  destruct ρH as [VV IV]. *)
  split; auto.
  asimpl.
  eapply s_val; auto.
  eapply is_value_V; eauto.
Qed.

Lemma semantic_abs {n} (Γ : Ctx n) e τ1 τ2 : 
  τ1 .: Γ ⊨ e ∈ τ2 -> 
  Γ ⊨ abs e ∈ Arr τ1 τ2.
Proof.
  intros IH.
  unfold semantic_typing in *.
  intros ρ ρH.
  unfold C.
  exists ((abs e)[ρ]).
  split. 
  eapply s_val. done.
  (* question: tell me about this. *)
  unfold V. fold V.
  exists e[⇑ρ]. 
  split; auto.
  intros w1 Vw1.
  destruct (IH (w1 .: ρ)) as [v2 [Ev2 Vv2]].
  eapply semantic_subst_cons; auto.
  exists v2. 
  asimpl.
  split; auto.
Qed.

(* Lemma uncons : forall {n} (e : Tm n) (v1 : Tm 0) (v2 : Tm 0) ρ, 
  e [v1 .: ρ] ⇓ v2 -> (e [v1]) [ρ] ⇓ v2.  *)

Lemma semantic_let {n} {Γ : Ctx n} (e1 : Tm n) (e2 : Tm (S n)) τ1 τ2:
  Γ ⊨ e1 ∈ τ1 -> 
  τ1 .: Γ ⊨ e2 ∈ τ2 -> 
  Γ ⊨ let_ e1 e2 ∈ τ2.
Proof.
  unfold semantic_typing in *.
  intros h1 h2 ρ ρH1.
  (* specialize (h1 ρ ρH1) as h1'.  *)

  destruct (h1 ρ ρH1) as [v1 [Sv1 Vv1]].
  Search V.
  specialize (semantic_subst_cons Vv1 ρH1) as ssc.
  destruct (h2 (v1 .: ρ) ssc) as [v2 [Sv2 Vv2]].
  unfold C.
  exists v2.
  split.   
  Search [_ ".:" _].
  - asimpl. 
    apply (s_let _ _ v1 v2).
  -- apply Sv1.
  -- asimpl. 
    apply Sv2.
  - assumption. 

    
  (* specialize (is_value_V τ2 v2 Vv2) as val_v2. *)
    
    (* Search [_..].   *)
  (* Search is_value.  *)
  (* - inversion Sv2.   *)
Qed.
  (* - asimpl. apply Sv2.  
  - assumption. 
Qed.  *)
  (* destruct Vv1 as [k' v1lit]. 
  (* not sure why -> didn't work here. *)
  subst. 
  unfold C. 
  exists (lit (S k')). 
  cbn. 
  split; eauto.
  eapply s_succ; eauto. 
Qed. *)

Lemma semantic_app {n} (Γ : Ctx n) e1 e2 τ1 τ2 : 
  Γ ⊨ e1 ∈ Arr τ1 τ2 -> 
  Γ ⊨ e2 ∈ τ1 -> 
  Γ ⊨ app e1 e2 ∈ τ2.
Proof.
  unfold semantic_typing in *.
  intros h1 h2 ρ ρh.
  destruct (h1 ρ ρh) as [v1 [Sv1 Vv1]].
  destruct (h2 ρ ρh) as [v2 [Sv2 Vv2]].
  destruct Vv1 as [e' [-> h]].
  destruct (h _ Vv2) as [v3 [Sv3 Vv3]].
  exists v3. split. eapply s_app; eauto. auto.
Qed.


Lemma semantic_lit {n} {Γ : Ctx n} {k:nat} :
   Γ ⊨ lit k ∈ Nat.
Proof.
  unfold semantic_typing.
  intros ρ ρH.
  unfold C. 
  exists (lit k). 
  cbn. 
  split; eauto.
  eapply s_val; eauto.
Qed.

Lemma semantic_succ {n} {Γ : Ctx n} e :
  Γ ⊨ e ∈ Nat -> 
  Γ ⊨ succ e ∈ Nat.
Proof.
  unfold semantic_typing in *.
  intros h1 ρ ρH. 
  destruct (h1 ρ ρH) as [v1 [Sv1 Vv1]].
  destruct Vv1 as [k' v1lit]. 
  (* not sure why -> didn't work here. *)
  subst. 
  unfold C. 
  exists (lit (S k')). 
  cbn. 
  split; eauto.
  eapply s_succ; eauto. 
Qed.



(*     typing Γ e Nat -> 
    typing Γ e0 τ -> 
    typing (Nat .: Γ) e1 (Arr τ τ) -> 
    typing Γ (nrec e e0 e1) τ *)

Lemma semantic_nrec {n} {Γ : Ctx n} e e0 e1 τ:
  Γ ⊨ e ∈ Nat -> 
  Γ ⊨ e0 ∈ τ -> 
  (Nat .: Γ) ⊨ e1 ∈ (Arr τ τ) -> 
  Γ ⊨ nrec e e0 e1 ∈ τ.
Proof.
  unfold semantic_typing in *.
  intros h1 h2 h3 ρ ρH1. 
  destruct (h1 ρ ρH1) as [v0 [Sv1 Vv1]].
  destruct (h2 ρ ρH1) as [v2 [Sv2 Vv2]].
  unfold C. 
  inversion Vv1; subst.
  generalize dependent e.  
  induction x as [| k]. 
  - exists v2. split; auto.   
    asimpl. 
    apply s_nrec_zero; eauto. 
  -  
  (* prepare our IH *)
  assert (Hk: V⟦ Nat ⟧ (lit k)).
  { unfold V. exists k. reflexivity. }
  (* prepare rest of nrec steps *)
    specialize (semantic_subst_cons Hk ρH1) as ssc.
    destruct (h3 _ ssc) as [v [Sv3 Vv3]].
    destruct Vv3 as [e' [-> e'_subst]].
    assert ((lit k) [ρ] ⇓ lit k) by (apply s_val; auto). 
    specialize (IHk Hk (lit k) semantic_lit (s_val (lit k) eq_refl))
    as (v1' & nrec_lit_step & Vv1').
    intros. 
    specialize (e'_subst _ Vv1') as (v & e'_subst_v & Vv). 
   
    exists v. 
    split; auto. 
    asimpl.
    eapply s_nrec_succ; eauto. 
    asimpl. auto. 
Qed. 
  
Lemma soundness n (Γ : Ctx n) e τ : 
  Γ |- e ∈ τ -> Γ ⊨ e ∈ τ.
Proof.
  intros h. induction h.
  all: intros ρ ρH.
  - eapply semantic_var; eauto.
  - eapply semantic_abs; eauto.
  - eapply semantic_app; eauto.
  - eapply semantic_lit; eauto.
  - eapply semantic_succ; eauto. 
  - eapply semantic_nrec; eauto. 
  - eapply semantic_let; eauto. 
Qed. 



End Big.

