-- For meeting: 
-- Talk about bind
-- talk about how to use names

-- Specification of the syntax of VMinus, PPlus, and D for the autosubst-ocaml tool
-- https://github.com/uds-psl/autosubst-ocaml

-- Bring nat, list into scope
nat : Type
list : Functor 
option : Functor 

Val     : Type
Tm(var) : Type


-- Values
vcon : nat -> "list" (Val) -> Val
fail : Val

-- Terms / Computations
ret     : Val -> Tm
vconapp : nat -> "list" (Tm) -> Tm

-- VMinus
Guard        : Type
Guards       : Type
GuardedExp   : Type
IffiBranch   : Type 

comp   : Val -> Guard
eqn    : Tm -> Tm -> Guard
-- two nonempty lists of guards: not a better way to do this unfortunately
choice : Guard -> "list" (Guard) -> Guard -> "list" (Guard) -> Guard

guards     : "list" (Guard) -> Guards 

guardedexp : Guards -> Tm -> GuardedExp

iffibranch (p : nat) : (bind <p, Tm> in GuardedExp) -> GuardedExp -> IffiBranch

iffi   : "list" (IffiBranch) -> Tm


-- PPlus

Pat          : Type 
CaseBranch   : Type 

-- what to bind in   ↓ here? Currently using Tm but maybe should be Pat?  
pname : (bind Tm in Tm) -> Pat
pvconapp : nat -> "list" (Pat) -> Pat
por : Pat -> Pat -> Pat 
pguard : Pat -> Pat -> Pat 
-- might need some special scoping here
pwhen : Pat -> Tm -> Pat  
-- CaseBranch
casebranch : Pat -> Tm -> CaseBranch 
-- Finally, case 
case : Val -> "list" (CaseBranch) -> Tm 

-- D 

TestBranch   : Type
Tree : Type

tfail : Tree 
match : Tm -> Tree 
-- should be `if x = e then t1 else t2`. How do I "use" a name here?
ifx : Tm -> Tree -> Tree -> Tree 
letx : Tm -> (bind Tm in Tm) -> Tree -> "option" (Tree) -> Tree
-- TODO: really not sure what            ↓ or   ↓ should be
testbranch (p : nat) : nat -> (bind <p, Tm> in Tree) -> Tree -> TestBranch
test : (bind Tm in Tree) -> "list" (TestBranch) -> "option" (Tree) -> Tree