
(* For meeting: 
- how to enforce language difference? idea: pass around predicates
about syntax: "this is vminus, so there is no 'case'"... etc. 
- comparing arbitrary terms in an equation- is this the way? 
What do we think of this program? 
x = K 1 2 
if 
∃ a b. x = (if 
            -> K a b
           fi)
         -> OK 
fi 

What about this one? 
if 
∃ x. x = 2; x = if ... fi -> OK 
fi 
*)

From Stdlib Require Import List. 
From Stdlib Require Import String. 
Import ListNotations.
From Stdlib Require Import Datatypes. (* option *)
Require Import Maps.

Definition name := string. 
Definition vconname := nat. 

Inductive Val : Type :=
| vcon : vconname -> list Val -> Val    (* K v1 v2 ... *)
| fail : Val.                     (* fail *)


Inductive Tm : Type :=
| var : name -> Tm                
| vconapp : vconname -> list Tm -> Tm 
| iffi : list IffiBranch -> Tm
(* if 
     ∃ x1 x2 ... . g1; g2; ... -> e1
     ∃ x1' x2' ... . g1'; g2'; ... -> e2
     ... 
   fi 
*)
| case : Tm -> list CaseBranch -> Tm 
(* case e of 
| p1 -> e1 
| p2 -> e2 
... *)
| tree : Tree -> Tm 
(* test x {K a b c -> ... | C y z -> ...} *)

(***************** IF-FI, GUARDS *****************)

with IffiBranch : Type := 
| iffibranch : list name -> GuardedExp -> IffiBranch
            (* ∃ x1 x2 ... . g1; g2; ... -> e *)
with GuardedExp : Type :=
| guardedexp : list Guard -> Tm -> GuardedExp

with Guard : Type :=
| comp : Tm -> Guard        (* a computation. if it fails, the branch is ignored. *)
| eqn : Tm -> Tm -> Guard    (* t1 = t2 *)
| choice : list Guard -> list Guard -> Guard 
                                (* g* | g*  *)

(***************** CASE, PATTERNS *****************)

with CaseBranch : Type := 
| casebranch : Pat -> Tm -> CaseBranch

with Pat : Type :=
| pname : Tm -> Pat           (* (bind Tm in Tm) represented as body Tm for now *)
| pvconapp : vconname -> list Pat -> Pat
| por : Pat -> Pat -> Pat
| pguard : Pat -> Pat -> Pat
| pwhen : Pat -> Tm -> Pat   (* pwhen pat when_tm ; note: may involve scoping of when_tm *)

(***************** DECISION TREES *****************)
with Tree : Type :=
| tfail : Tree
| tmatch : Tm -> Tree                          (* renamed from 'match' to avoid Coq keyword clash *)
| ifx : name -> Tm -> Tree -> Tree -> Tree            (* ifx x then t1 else t2; how to "use" a name recorded in x is a binding concern *)
| letx : name -> Tm -> Tree -> option Tree -> Tree
| test : name -> list TestBranch -> option Tree -> Tree

with  TestBranch : Type :=
| testbranch : vconname -> list name -> Tree -> TestBranch. 

(***************** EVALUATION RESULTS *****************)

Inductive MaybeVal : Type := 
| V : Val -> MaybeVal 
| Bot : MaybeVal.

(***************** ENVIRONMENTS *****************)

(* steal sf partial maps *)
(* lookup x env = None when x not in env 
   lookup x env = Bot when x ∈ dom env and not bound
   lookup x env = V v for some v when x ∈ dom env and bound  *)
Definition env := partial_map MaybeVal. 

(***************** EVALUATION AND UNIFICATION *****************)

(* Helpers *)

Definition not_in_dom (x : name) (ρ : env) := 
   ρ x = None. 

Notation " x '∉' ρ " := (not_in_dom x ρ) 
(at level 70, ρ at level 70, no associativity).

Definition unknown_in (x : name) (ρ : env) := 
   ρ x = Some Bot. 

Notation "ρ x '=' '⊥' " := (unknown_in x ρ) 
(at level 70, no associativity).

Definition known_in (x : name) (ρ : env) := 
   exists v, ρ x = Some (V v). 

Notation "ρ x '=' 'known' " := (known_in x ρ) 
(at level 70, no associativity).

Definition x_is_v_in_rho (x : name) (ρ : env) (v : Val) := 
   ρ x = Some (V v). 

Notation "ρ x '=' v" := (x_is_v_in_rho x ρ v) 
(at level 70, no associativity).

Notation "'if_' gs 'fi'" := (iffi gs)
(at level 0, no associativity).

Definition extend : env -> list name -> env := 
fun ρ xs => 
  fold_left (fun ρ x => update ρ x Bot) xs ρ. 

(* ask about levels, best practice *)
Notation "ρ '<+>' xs" := (extend ρ xs)
(at level 71, left associativity).

Inductive UnificationResult : Type :=
| refined : env -> UnificationResult 
| failed  : UnificationResult. Notation "†" := failed (at level 0).

(* this is probably somewhere... *)

(* semantics *)

Definition unifyval : Val -> Val -> Prop := 
fun v1 v2 =>    
match v1, v2 with 
| vcon K1 vs1, vcon K2 vs2 => K1 = K2 /\ vs1 = vs2
| fail, _ => False 
| _, fail => False
end. 

(* ask about typeclass notation *)

(* RESOLVE NONDETERMINISM *)
(* picks a guard and returns the rest of the list *)
Definition pick_a_guard : list Guard -> option Guard * list Guard := 
   fun gs => 
   match gs with 
   | [] => (None, [])
   | g :: gs => (Some g, gs)
end. 

Inductive eval : env -> Tm -> Val -> Prop := 
| e_name ρ x v : ρ x = Some (V v) -> eval ρ (var x) v

| e_vconapp ρ K es vs : 

   eval_all ρ es vs 
   (*******************) -> 
   eval ρ (vconapp K es) (vcon K vs)

| e_iffi_fail ρ : eval ρ (if_ [] fi) fail

| e_iffi_first ρ G GS v : 

   eval_iffi_branch ρ G v 
  (************************) ->
   eval ρ (if_ G::GS fi) v

| e_iffi_rec ρ G GS v : 

  eval_iffi_branch ρ G fail -> 
  eval ρ (if_ GS fi) v 
  (*****************************) ->
  eval ρ (if_ G::GS fi) v

with eval_iffi_branch : env -> IffiBranch -> Val -> Prop := 
| ebr_names ρ xs ge v : 
  
      eval_gexp (ρ <+> xs) ge v
    (*******************************) ->
    eval_iffi_branch ρ (iffibranch xs ge) v 

with eval_gexp : env -> GuardedExp -> Val -> Prop := 
| eg_gs_fail ρ ρ' gs e v : 

            solve_guards ρ gs failed -> 
            eval ρ' e v 
     (************************************) ->
      eval_gexp ρ' (guardedexp gs e) fail 


| eg_gs_succ ρ ρ' gs e v : 

            solve_guards ρ gs (refined ρ') -> 
            eval ρ' e v 
     (************************************) ->
      eval_gexp ρ' (guardedexp gs e) v 


with solve_guards : env -> list Guard -> UnificationResult -> Prop := 
| sgs_empty ρ : solve_guards ρ [] (refined ρ) 

(* adding a rule for None means that 'compiler stuck' failure is 
expected stepping behavior *)
| sgs_fail ρ g gs gs' : 

    pick_a_guard gs = (Some g, gs') -> 
      solve_guard ρ g failed
   (*********************************) ->
      solve_guards ρ gs failed

| sgs_rec ρ ρ' g gs gs' r : 

    pick_a_guard gs = (Some g, gs') -> 
      solve_guard ρ g (refined ρ') -> 
    solve_guards ρ' gs' r 
   (*********************************) ->
      solve_guards ρ gs r


with solve_guard : env -> Guard -> UnificationResult -> Prop := 
| s_comp_fail ρ e : 
   eval ρ e fail -> 
   solve_guard ρ (comp e) †
   
(* success does not change the environment. *)
| s_comp_succ ρ e v : 
   eval ρ e v -> 
   v <> fail -> 
   solve_guard ρ (comp e) (refined ρ)

| s_eqn ρ e1 e2 r : 
   unify e1 e2 r -> 
   solve_guard ρ (eqn e1 e2) r

| s_choice_empty1 ρ gs2 : 
   solve_guard ρ (choice [] gs2 ) (refined ρ)

| s_choice_empty2 ρ gs1 : 
   solve_guard ρ (choice gs1 []) (refined ρ)

(* choice should go either way *)
| s_choice_fail_l ρ gs1 gs2 r : 
   solve_guards ρ gs1 failed -> 
   solve_guards ρ gs2 r -> 
   solve_guard ρ (choice gs1 gs2) r  

| s_choice_fail_r ρ gs1 gs2 r : 
   solve_guards ρ gs2 failed -> 
   solve_guards ρ gs1 r -> 
   solve_guard ρ (choice gs1 gs2) r  

| s_choice_succ_l ρ ρ' gs1 gs2 : 
   solve_guards ρ gs1 (refined ρ') -> 
   solve_guard ρ (choice gs1 gs2) (refined ρ')

| s_choice_succ_r ρ ρ' gs1 gs2 : 
   solve_guards ρ gs2 (refined ρ') -> 
   solve_guard ρ (choice gs1 gs2) (refined ρ')

   
with unify : Tm -> Tm -> UnificationResult -> Prop := 



with eval_all : env -> list Tm -> list Val -> Prop := 
| eall_nil ρ : eval_all ρ [] []
| eall_cons ρ e es v vs : 

       eval ρ e v -> eval_all ρ es vs 
      (******************************) ->
       eval_all ρ (e :: es) (v :: vs).



(* reserved notation *)


