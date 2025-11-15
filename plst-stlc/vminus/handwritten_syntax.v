
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
| tvar : name -> Tm                
| ret : Val -> Tm                  
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
| g_comp : Val -> Guard        (* a computation. if it fails, the branch is ignored. *)
| g_eqn : Tm -> Tm -> Guard    (* t1 = t2 *)
| g_choice : Guard -> list Guard -> Guard -> list Guard -> Guard 
                                (* g+ | g+. nonempty lists?  *)

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
Inductive eval : env -> Tm -> Val -> Prop := 
| E_fail : forall rho v, eval rho (ret v) v

with unify : env -> Tm -> Tm -> Prop :=
| U_foo : forall rho e1 e2, unify rho e1 e2. 

(* reserved notation *)

(* Inductive UnificationResult : Type := *)


(* Inductive unify : Guard -> Guard -> Prop := 
|  *)