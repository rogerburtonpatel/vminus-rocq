Require Import core fintype.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive Val : Type :=
  | vcon : nat -> list (Val) -> Val
  | fail : Val.

Lemma congr_vcon {s0 : nat} {s1 : list (Val)} {t0 : nat} {t1 : list (Val)}
  (H0 : s0 = t0) (H1 : s1 = t1) : vcon s0 s1 = vcon t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => vcon x s1) H0))
         (ap (fun x => vcon t0 x) H1)).
Qed.

Lemma congr_fail : fail = fail.
Proof.
exact (eq_refl).
Qed.

Inductive Tm (n_Tm : nat) : Type :=
  | var : fin n_Tm -> Tm n_Tm
  | ret : Val -> Tm n_Tm
  | vconapp : nat -> list (Tm n_Tm) -> Tm n_Tm
  | iffi : list (IffiBranch n_Tm) -> Tm n_Tm
  | case : Val -> list (CaseBranch n_Tm) -> Tm n_Tm
with Guard (n_Tm : nat) : Type :=
  | comp : Val -> Guard n_Tm
  | eqn : Tm n_Tm -> Tm n_Tm -> Guard n_Tm
  | choice :
      Guard n_Tm ->
      list (Guard n_Tm) -> Guard n_Tm -> list (Guard n_Tm) -> Guard n_Tm
with Guards (n_Tm : nat) : Type :=
    guards : list (Guard n_Tm) -> Guards n_Tm
with GuardedExp (n_Tm : nat) : Type :=
    guardedexp : Guards n_Tm -> Tm n_Tm -> GuardedExp n_Tm
with IffiBranch (n_Tm : nat) : Type :=
    iffibranch :
      forall p : nat,
      GuardedExp (plus p n_Tm) -> GuardedExp n_Tm -> IffiBranch n_Tm
with Pat (n_Tm : nat) : Type :=
  | pname : Tm (S n_Tm) -> Pat n_Tm
  | pvconapp : nat -> list (Pat n_Tm) -> Pat n_Tm
  | por : Pat n_Tm -> Pat n_Tm -> Pat n_Tm
  | pguard : Pat n_Tm -> Pat n_Tm -> Pat n_Tm
  | pwhen : Pat n_Tm -> Tm n_Tm -> Pat n_Tm
with CaseBranch (n_Tm : nat) : Type :=
    casebranch : Pat n_Tm -> Tm n_Tm -> CaseBranch n_Tm.

Lemma congr_ret {m_Tm : nat} {s0 : Val} {t0 : Val} (H0 : s0 = t0) :
  ret m_Tm s0 = ret m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ret m_Tm x) H0)).
Qed.

Lemma congr_vconapp {m_Tm : nat} {s0 : nat} {s1 : list (Tm m_Tm)} {t0 : nat}
  {t1 : list (Tm m_Tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  vconapp m_Tm s0 s1 = vconapp m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => vconapp m_Tm x s1) H0))
         (ap (fun x => vconapp m_Tm t0 x) H1)).
Qed.

Lemma congr_iffi {m_Tm : nat} {s0 : list (IffiBranch m_Tm)}
  {t0 : list (IffiBranch m_Tm)} (H0 : s0 = t0) : iffi m_Tm s0 = iffi m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => iffi m_Tm x) H0)).
Qed.

Lemma congr_case {m_Tm : nat} {s0 : Val} {s1 : list (CaseBranch m_Tm)}
  {t0 : Val} {t1 : list (CaseBranch m_Tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  case m_Tm s0 s1 = case m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => case m_Tm x s1) H0))
         (ap (fun x => case m_Tm t0 x) H1)).
Qed.

Lemma congr_comp {m_Tm : nat} {s0 : Val} {t0 : Val} (H0 : s0 = t0) :
  comp m_Tm s0 = comp m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => comp m_Tm x) H0)).
Qed.

Lemma congr_eqn {m_Tm : nat} {s0 : Tm m_Tm} {s1 : Tm m_Tm} {t0 : Tm m_Tm}
  {t1 : Tm m_Tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  eqn m_Tm s0 s1 = eqn m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => eqn m_Tm x s1) H0))
         (ap (fun x => eqn m_Tm t0 x) H1)).
Qed.

Lemma congr_choice {m_Tm : nat} {s0 : Guard m_Tm} {s1 : list (Guard m_Tm)}
  {s2 : Guard m_Tm} {s3 : list (Guard m_Tm)} {t0 : Guard m_Tm}
  {t1 : list (Guard m_Tm)} {t2 : Guard m_Tm} {t3 : list (Guard m_Tm)}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) :
  choice m_Tm s0 s1 s2 s3 = choice m_Tm t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans eq_refl (ap (fun x => choice m_Tm x s1 s2 s3) H0))
               (ap (fun x => choice m_Tm t0 x s2 s3) H1))
            (ap (fun x => choice m_Tm t0 t1 x s3) H2))
         (ap (fun x => choice m_Tm t0 t1 t2 x) H3)).
Qed.

Lemma congr_guards {m_Tm : nat} {s0 : list (Guard m_Tm)}
  {t0 : list (Guard m_Tm)} (H0 : s0 = t0) : guards m_Tm s0 = guards m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => guards m_Tm x) H0)).
Qed.

Lemma congr_guardedexp {m_Tm : nat} {s0 : Guards m_Tm} {s1 : Tm m_Tm}
  {t0 : Guards m_Tm} {t1 : Tm m_Tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  guardedexp m_Tm s0 s1 = guardedexp m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => guardedexp m_Tm x s1) H0))
         (ap (fun x => guardedexp m_Tm t0 x) H1)).
Qed.

Lemma congr_iffibranch {p : nat} {m_Tm : nat} {s0 : GuardedExp (plus p m_Tm)}
  {s1 : GuardedExp m_Tm} {t0 : GuardedExp (plus p m_Tm)}
  {t1 : GuardedExp m_Tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  iffibranch m_Tm p s0 s1 = iffibranch m_Tm p t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => iffibranch m_Tm p x s1) H0))
         (ap (fun x => iffibranch m_Tm p t0 x) H1)).
Qed.

Lemma congr_pname {m_Tm : nat} {s0 : Tm (S m_Tm)} {t0 : Tm (S m_Tm)}
  (H0 : s0 = t0) : pname m_Tm s0 = pname m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => pname m_Tm x) H0)).
Qed.

Lemma congr_pvconapp {m_Tm : nat} {s0 : nat} {s1 : list (Pat m_Tm)}
  {t0 : nat} {t1 : list (Pat m_Tm)} (H0 : s0 = t0) (H1 : s1 = t1) :
  pvconapp m_Tm s0 s1 = pvconapp m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pvconapp m_Tm x s1) H0))
         (ap (fun x => pvconapp m_Tm t0 x) H1)).
Qed.

Lemma congr_por {m_Tm : nat} {s0 : Pat m_Tm} {s1 : Pat m_Tm} {t0 : Pat m_Tm}
  {t1 : Pat m_Tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  por m_Tm s0 s1 = por m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => por m_Tm x s1) H0))
         (ap (fun x => por m_Tm t0 x) H1)).
Qed.

Lemma congr_pguard {m_Tm : nat} {s0 : Pat m_Tm} {s1 : Pat m_Tm}
  {t0 : Pat m_Tm} {t1 : Pat m_Tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  pguard m_Tm s0 s1 = pguard m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pguard m_Tm x s1) H0))
         (ap (fun x => pguard m_Tm t0 x) H1)).
Qed.

Lemma congr_pwhen {m_Tm : nat} {s0 : Pat m_Tm} {s1 : Tm m_Tm} {t0 : Pat m_Tm}
  {t1 : Tm m_Tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  pwhen m_Tm s0 s1 = pwhen m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pwhen m_Tm x s1) H0))
         (ap (fun x => pwhen m_Tm t0 x) H1)).
Qed.

Lemma congr_casebranch {m_Tm : nat} {s0 : Pat m_Tm} {s1 : Tm m_Tm}
  {t0 : Pat m_Tm} {t1 : Tm m_Tm} (H0 : s0 = t0) (H1 : s1 = t1) :
  casebranch m_Tm s0 s1 = casebranch m_Tm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => casebranch m_Tm x s1) H0))
         (ap (fun x => casebranch m_Tm t0 x) H1)).
Qed.

Lemma upRen_Tm_Tm {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (S m) -> fin (S n).
Proof.
exact (up_ren xi).
Defined.

Lemma upRen_list_Tm_Tm (p : nat) {m : nat} {n : nat} (xi : fin m -> fin n) :
  fin (plus p m) -> fin (plus p n).
Proof.
exact (upRen_p p xi).
Defined.

Fixpoint ren_Tm {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(s : Tm m_Tm) {struct s} : Tm n_Tm :=
  match s with
  | var _ s0 => var n_Tm (xi_Tm s0)
  | ret _ s0 => ret n_Tm s0
  | vconapp _ s0 s1 => vconapp n_Tm s0 (list_map (ren_Tm xi_Tm) s1)
  | iffi _ s0 => iffi n_Tm (list_map (ren_IffiBranch xi_Tm) s0)
  | case _ s0 s1 => case n_Tm s0 (list_map (ren_CaseBranch xi_Tm) s1)
  end
with ren_Guard {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(s : Guard m_Tm) {struct s} : Guard n_Tm :=
  match s with
  | comp _ s0 => comp n_Tm s0
  | eqn _ s0 s1 => eqn n_Tm (ren_Tm xi_Tm s0) (ren_Tm xi_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      choice n_Tm (ren_Guard xi_Tm s0) (list_map (ren_Guard xi_Tm) s1)
        (ren_Guard xi_Tm s2) (list_map (ren_Guard xi_Tm) s3)
  end
with ren_Guards {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(s : Guards m_Tm) {struct s} : Guards n_Tm :=
  match s with
  | guards _ s0 => guards n_Tm (list_map (ren_Guard xi_Tm) s0)
  end
with ren_GuardedExp {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(s : GuardedExp m_Tm) {struct s} : GuardedExp n_Tm :=
  match s with
  | guardedexp _ s0 s1 =>
      guardedexp n_Tm (ren_Guards xi_Tm s0) (ren_Tm xi_Tm s1)
  end
with ren_IffiBranch {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(s : IffiBranch m_Tm) {struct s} : IffiBranch n_Tm :=
  match s with
  | iffibranch _ p s0 s1 =>
      iffibranch n_Tm p (ren_GuardedExp (upRen_list_Tm_Tm p xi_Tm) s0)
        (ren_GuardedExp xi_Tm s1)
  end
with ren_Pat {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(s : Pat m_Tm) {struct s} : Pat n_Tm :=
  match s with
  | pname _ s0 => pname n_Tm (ren_Tm (upRen_Tm_Tm xi_Tm) s0)
  | pvconapp _ s0 s1 => pvconapp n_Tm s0 (list_map (ren_Pat xi_Tm) s1)
  | por _ s0 s1 => por n_Tm (ren_Pat xi_Tm s0) (ren_Pat xi_Tm s1)
  | pguard _ s0 s1 => pguard n_Tm (ren_Pat xi_Tm s0) (ren_Pat xi_Tm s1)
  | pwhen _ s0 s1 => pwhen n_Tm (ren_Pat xi_Tm s0) (ren_Tm xi_Tm s1)
  end
with ren_CaseBranch {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(s : CaseBranch m_Tm) {struct s} : CaseBranch n_Tm :=
  match s with
  | casebranch _ s0 s1 =>
      casebranch n_Tm (ren_Pat xi_Tm s0) (ren_Tm xi_Tm s1)
  end.

Lemma up_Tm_Tm {m : nat} {n_Tm : nat} (sigma : fin m -> Tm n_Tm) :
  fin (S m) -> Tm (S n_Tm).
Proof.
exact (scons (var (S n_Tm) var_zero) (funcomp (ren_Tm shift) sigma)).
Defined.

Lemma up_list_Tm_Tm (p : nat) {m : nat} {n_Tm : nat}
  (sigma : fin m -> Tm n_Tm) : fin (plus p m) -> Tm (plus p n_Tm).
Proof.
exact (scons_p p (funcomp (var (plus p n_Tm)) (zero_p p))
         (funcomp (ren_Tm (shift_p p)) sigma)).
Defined.

Fixpoint subst_Tm {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(s : Tm m_Tm) {struct s} : Tm n_Tm :=
  match s with
  | var _ s0 => sigma_Tm s0
  | ret _ s0 => ret n_Tm s0
  | vconapp _ s0 s1 => vconapp n_Tm s0 (list_map (subst_Tm sigma_Tm) s1)
  | iffi _ s0 => iffi n_Tm (list_map (subst_IffiBranch sigma_Tm) s0)
  | case _ s0 s1 => case n_Tm s0 (list_map (subst_CaseBranch sigma_Tm) s1)
  end
with subst_Guard {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(s : Guard m_Tm) {struct s} : Guard n_Tm :=
  match s with
  | comp _ s0 => comp n_Tm s0
  | eqn _ s0 s1 => eqn n_Tm (subst_Tm sigma_Tm s0) (subst_Tm sigma_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      choice n_Tm (subst_Guard sigma_Tm s0)
        (list_map (subst_Guard sigma_Tm) s1) (subst_Guard sigma_Tm s2)
        (list_map (subst_Guard sigma_Tm) s3)
  end
with subst_Guards {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(s : Guards m_Tm) {struct s} : Guards n_Tm :=
  match s with
  | guards _ s0 => guards n_Tm (list_map (subst_Guard sigma_Tm) s0)
  end
with subst_GuardedExp {m_Tm : nat} {n_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm n_Tm) (s : GuardedExp m_Tm) {struct s} :
GuardedExp n_Tm :=
  match s with
  | guardedexp _ s0 s1 =>
      guardedexp n_Tm (subst_Guards sigma_Tm s0) (subst_Tm sigma_Tm s1)
  end
with subst_IffiBranch {m_Tm : nat} {n_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm n_Tm) (s : IffiBranch m_Tm) {struct s} :
IffiBranch n_Tm :=
  match s with
  | iffibranch _ p s0 s1 =>
      iffibranch n_Tm p (subst_GuardedExp (up_list_Tm_Tm p sigma_Tm) s0)
        (subst_GuardedExp sigma_Tm s1)
  end
with subst_Pat {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(s : Pat m_Tm) {struct s} : Pat n_Tm :=
  match s with
  | pname _ s0 => pname n_Tm (subst_Tm (up_Tm_Tm sigma_Tm) s0)
  | pvconapp _ s0 s1 => pvconapp n_Tm s0 (list_map (subst_Pat sigma_Tm) s1)
  | por _ s0 s1 => por n_Tm (subst_Pat sigma_Tm s0) (subst_Pat sigma_Tm s1)
  | pguard _ s0 s1 =>
      pguard n_Tm (subst_Pat sigma_Tm s0) (subst_Pat sigma_Tm s1)
  | pwhen _ s0 s1 =>
      pwhen n_Tm (subst_Pat sigma_Tm s0) (subst_Tm sigma_Tm s1)
  end
with subst_CaseBranch {m_Tm : nat} {n_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm n_Tm) (s : CaseBranch m_Tm) {struct s} :
CaseBranch n_Tm :=
  match s with
  | casebranch _ s0 s1 =>
      casebranch n_Tm (subst_Pat sigma_Tm s0) (subst_Tm sigma_Tm s1)
  end.

Lemma upId_Tm_Tm {m_Tm : nat} (sigma : fin m_Tm -> Tm m_Tm)
  (Eq : forall x, sigma x = var m_Tm x) :
  forall x, up_Tm_Tm sigma x = var (S m_Tm) x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upId_list_Tm_Tm {p : nat} {m_Tm : nat} (sigma : fin m_Tm -> Tm m_Tm)
  (Eq : forall x, sigma x = var m_Tm x) :
  forall x, up_list_Tm_Tm p sigma x = var (plus p m_Tm) x.
Proof.
exact (fun n =>
       scons_p_eta (var (plus p m_Tm))
         (fun n => ap (ren_Tm (shift_p p)) (Eq n)) (fun n => eq_refl)).
Qed.

Fixpoint idSubst_Tm {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : Tm m_Tm) {struct s} :
subst_Tm sigma_Tm s = s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | ret _ s0 => congr_ret (eq_refl s0)
  | vconapp _ s0 s1 =>
      congr_vconapp (eq_refl s0) (list_id (idSubst_Tm sigma_Tm Eq_Tm) s1)
  | iffi _ s0 => congr_iffi (list_id (idSubst_IffiBranch sigma_Tm Eq_Tm) s0)
  | case _ s0 s1 =>
      congr_case (eq_refl s0)
        (list_id (idSubst_CaseBranch sigma_Tm Eq_Tm) s1)
  end
with idSubst_Guard {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : Guard m_Tm) {struct s} :
subst_Guard sigma_Tm s = s :=
  match s with
  | comp _ s0 => congr_comp (eq_refl s0)
  | eqn _ s0 s1 =>
      congr_eqn (idSubst_Tm sigma_Tm Eq_Tm s0) (idSubst_Tm sigma_Tm Eq_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      congr_choice (idSubst_Guard sigma_Tm Eq_Tm s0)
        (list_id (idSubst_Guard sigma_Tm Eq_Tm) s1)
        (idSubst_Guard sigma_Tm Eq_Tm s2)
        (list_id (idSubst_Guard sigma_Tm Eq_Tm) s3)
  end
with idSubst_Guards {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : Guards m_Tm) {struct s} :
subst_Guards sigma_Tm s = s :=
  match s with
  | guards _ s0 => congr_guards (list_id (idSubst_Guard sigma_Tm Eq_Tm) s0)
  end
with idSubst_GuardedExp {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : GuardedExp m_Tm) {struct s}
   :
subst_GuardedExp sigma_Tm s = s :=
  match s with
  | guardedexp _ s0 s1 =>
      congr_guardedexp (idSubst_Guards sigma_Tm Eq_Tm s0)
        (idSubst_Tm sigma_Tm Eq_Tm s1)
  end
with idSubst_IffiBranch {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : IffiBranch m_Tm) {struct s}
   :
subst_IffiBranch sigma_Tm s = s :=
  match s with
  | iffibranch _ p s0 s1 =>
      congr_iffibranch
        (idSubst_GuardedExp (up_list_Tm_Tm p sigma_Tm)
           (upId_list_Tm_Tm _ Eq_Tm) s0)
        (idSubst_GuardedExp sigma_Tm Eq_Tm s1)
  end
with idSubst_Pat {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : Pat m_Tm) {struct s} :
subst_Pat sigma_Tm s = s :=
  match s with
  | pname _ s0 =>
      congr_pname (idSubst_Tm (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s0)
  | pvconapp _ s0 s1 =>
      congr_pvconapp (eq_refl s0) (list_id (idSubst_Pat sigma_Tm Eq_Tm) s1)
  | por _ s0 s1 =>
      congr_por (idSubst_Pat sigma_Tm Eq_Tm s0)
        (idSubst_Pat sigma_Tm Eq_Tm s1)
  | pguard _ s0 s1 =>
      congr_pguard (idSubst_Pat sigma_Tm Eq_Tm s0)
        (idSubst_Pat sigma_Tm Eq_Tm s1)
  | pwhen _ s0 s1 =>
      congr_pwhen (idSubst_Pat sigma_Tm Eq_Tm s0)
        (idSubst_Tm sigma_Tm Eq_Tm s1)
  end
with idSubst_CaseBranch {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : CaseBranch m_Tm) {struct s}
   :
subst_CaseBranch sigma_Tm s = s :=
  match s with
  | casebranch _ s0 s1 =>
      congr_casebranch (idSubst_Pat sigma_Tm Eq_Tm s0)
        (idSubst_Tm sigma_Tm Eq_Tm s1)
  end.

Lemma upExtRen_Tm_Tm {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_Tm_Tm xi x = upRen_Tm_Tm zeta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap shift (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExtRen_list_Tm_Tm {p : nat} {m : nat} {n : nat} (xi : fin m -> fin n)
  (zeta : fin m -> fin n) (Eq : forall x, xi x = zeta x) :
  forall x, upRen_list_Tm_Tm p xi x = upRen_list_Tm_Tm p zeta x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl) (fun n => ap (shift_p p) (Eq n))).
Qed.

Fixpoint extRen_Tm {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(zeta_Tm : fin m_Tm -> fin n_Tm) (Eq_Tm : forall x, xi_Tm x = zeta_Tm x)
(s : Tm m_Tm) {struct s} : ren_Tm xi_Tm s = ren_Tm zeta_Tm s :=
  match s with
  | var _ s0 => ap (var n_Tm) (Eq_Tm s0)
  | ret _ s0 => congr_ret (eq_refl s0)
  | vconapp _ s0 s1 =>
      congr_vconapp (eq_refl s0)
        (list_ext (extRen_Tm xi_Tm zeta_Tm Eq_Tm) s1)
  | iffi _ s0 =>
      congr_iffi (list_ext (extRen_IffiBranch xi_Tm zeta_Tm Eq_Tm) s0)
  | case _ s0 s1 =>
      congr_case (eq_refl s0)
        (list_ext (extRen_CaseBranch xi_Tm zeta_Tm Eq_Tm) s1)
  end
with extRen_Guard {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(zeta_Tm : fin m_Tm -> fin n_Tm) (Eq_Tm : forall x, xi_Tm x = zeta_Tm x)
(s : Guard m_Tm) {struct s} : ren_Guard xi_Tm s = ren_Guard zeta_Tm s :=
  match s with
  | comp _ s0 => congr_comp (eq_refl s0)
  | eqn _ s0 s1 =>
      congr_eqn (extRen_Tm xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      congr_choice (extRen_Guard xi_Tm zeta_Tm Eq_Tm s0)
        (list_ext (extRen_Guard xi_Tm zeta_Tm Eq_Tm) s1)
        (extRen_Guard xi_Tm zeta_Tm Eq_Tm s2)
        (list_ext (extRen_Guard xi_Tm zeta_Tm Eq_Tm) s3)
  end
with extRen_Guards {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(zeta_Tm : fin m_Tm -> fin n_Tm) (Eq_Tm : forall x, xi_Tm x = zeta_Tm x)
(s : Guards m_Tm) {struct s} : ren_Guards xi_Tm s = ren_Guards zeta_Tm s :=
  match s with
  | guards _ s0 =>
      congr_guards (list_ext (extRen_Guard xi_Tm zeta_Tm Eq_Tm) s0)
  end
with extRen_GuardedExp {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (zeta_Tm : fin m_Tm -> fin n_Tm)
(Eq_Tm : forall x, xi_Tm x = zeta_Tm x) (s : GuardedExp m_Tm) {struct s} :
ren_GuardedExp xi_Tm s = ren_GuardedExp zeta_Tm s :=
  match s with
  | guardedexp _ s0 s1 =>
      congr_guardedexp (extRen_Guards xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  end
with extRen_IffiBranch {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (zeta_Tm : fin m_Tm -> fin n_Tm)
(Eq_Tm : forall x, xi_Tm x = zeta_Tm x) (s : IffiBranch m_Tm) {struct s} :
ren_IffiBranch xi_Tm s = ren_IffiBranch zeta_Tm s :=
  match s with
  | iffibranch _ p s0 s1 =>
      congr_iffibranch
        (extRen_GuardedExp (upRen_list_Tm_Tm p xi_Tm)
           (upRen_list_Tm_Tm p zeta_Tm) (upExtRen_list_Tm_Tm _ _ Eq_Tm) s0)
        (extRen_GuardedExp xi_Tm zeta_Tm Eq_Tm s1)
  end
with extRen_Pat {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(zeta_Tm : fin m_Tm -> fin n_Tm) (Eq_Tm : forall x, xi_Tm x = zeta_Tm x)
(s : Pat m_Tm) {struct s} : ren_Pat xi_Tm s = ren_Pat zeta_Tm s :=
  match s with
  | pname _ s0 =>
      congr_pname
        (extRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upExtRen_Tm_Tm _ _ Eq_Tm) s0)
  | pvconapp _ s0 s1 =>
      congr_pvconapp (eq_refl s0)
        (list_ext (extRen_Pat xi_Tm zeta_Tm Eq_Tm) s1)
  | por _ s0 s1 =>
      congr_por (extRen_Pat xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Pat xi_Tm zeta_Tm Eq_Tm s1)
  | pguard _ s0 s1 =>
      congr_pguard (extRen_Pat xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Pat xi_Tm zeta_Tm Eq_Tm s1)
  | pwhen _ s0 s1 =>
      congr_pwhen (extRen_Pat xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  end
with extRen_CaseBranch {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (zeta_Tm : fin m_Tm -> fin n_Tm)
(Eq_Tm : forall x, xi_Tm x = zeta_Tm x) (s : CaseBranch m_Tm) {struct s} :
ren_CaseBranch xi_Tm s = ren_CaseBranch zeta_Tm s :=
  match s with
  | casebranch _ s0 s1 =>
      congr_casebranch (extRen_Pat xi_Tm zeta_Tm Eq_Tm s0)
        (extRen_Tm xi_Tm zeta_Tm Eq_Tm s1)
  end.

Lemma upExt_Tm_Tm {m : nat} {n_Tm : nat} (sigma : fin m -> Tm n_Tm)
  (tau : fin m -> Tm n_Tm) (Eq : forall x, sigma x = tau x) :
  forall x, up_Tm_Tm sigma x = up_Tm_Tm tau x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma upExt_list_Tm_Tm {p : nat} {m : nat} {n_Tm : nat}
  (sigma : fin m -> Tm n_Tm) (tau : fin m -> Tm n_Tm)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_list_Tm_Tm p sigma x = up_list_Tm_Tm p tau x.
Proof.
exact (fun n =>
       scons_p_congr (fun n => eq_refl)
         (fun n => ap (ren_Tm (shift_p p)) (Eq n))).
Qed.

Fixpoint ext_Tm {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(tau_Tm : fin m_Tm -> Tm n_Tm) (Eq_Tm : forall x, sigma_Tm x = tau_Tm x)
(s : Tm m_Tm) {struct s} : subst_Tm sigma_Tm s = subst_Tm tau_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | ret _ s0 => congr_ret (eq_refl s0)
  | vconapp _ s0 s1 =>
      congr_vconapp (eq_refl s0) (list_ext (ext_Tm sigma_Tm tau_Tm Eq_Tm) s1)
  | iffi _ s0 =>
      congr_iffi (list_ext (ext_IffiBranch sigma_Tm tau_Tm Eq_Tm) s0)
  | case _ s0 s1 =>
      congr_case (eq_refl s0)
        (list_ext (ext_CaseBranch sigma_Tm tau_Tm Eq_Tm) s1)
  end
with ext_Guard {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(tau_Tm : fin m_Tm -> Tm n_Tm) (Eq_Tm : forall x, sigma_Tm x = tau_Tm x)
(s : Guard m_Tm) {struct s} : subst_Guard sigma_Tm s = subst_Guard tau_Tm s
:=
  match s with
  | comp _ s0 => congr_comp (eq_refl s0)
  | eqn _ s0 s1 =>
      congr_eqn (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      congr_choice (ext_Guard sigma_Tm tau_Tm Eq_Tm s0)
        (list_ext (ext_Guard sigma_Tm tau_Tm Eq_Tm) s1)
        (ext_Guard sigma_Tm tau_Tm Eq_Tm s2)
        (list_ext (ext_Guard sigma_Tm tau_Tm Eq_Tm) s3)
  end
with ext_Guards {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(tau_Tm : fin m_Tm -> Tm n_Tm) (Eq_Tm : forall x, sigma_Tm x = tau_Tm x)
(s : Guards m_Tm) {struct s} :
subst_Guards sigma_Tm s = subst_Guards tau_Tm s :=
  match s with
  | guards _ s0 =>
      congr_guards (list_ext (ext_Guard sigma_Tm tau_Tm Eq_Tm) s0)
  end
with ext_GuardedExp {m_Tm : nat} {n_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm n_Tm) (tau_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : GuardedExp m_Tm) {struct s} :
subst_GuardedExp sigma_Tm s = subst_GuardedExp tau_Tm s :=
  match s with
  | guardedexp _ s0 s1 =>
      congr_guardedexp (ext_Guards sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  end
with ext_IffiBranch {m_Tm : nat} {n_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm n_Tm) (tau_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : IffiBranch m_Tm) {struct s} :
subst_IffiBranch sigma_Tm s = subst_IffiBranch tau_Tm s :=
  match s with
  | iffibranch _ p s0 s1 =>
      congr_iffibranch
        (ext_GuardedExp (up_list_Tm_Tm p sigma_Tm) (up_list_Tm_Tm p tau_Tm)
           (upExt_list_Tm_Tm _ _ Eq_Tm) s0)
        (ext_GuardedExp sigma_Tm tau_Tm Eq_Tm s1)
  end
with ext_Pat {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(tau_Tm : fin m_Tm -> Tm n_Tm) (Eq_Tm : forall x, sigma_Tm x = tau_Tm x)
(s : Pat m_Tm) {struct s} : subst_Pat sigma_Tm s = subst_Pat tau_Tm s :=
  match s with
  | pname _ s0 =>
      congr_pname
        (ext_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s0)
  | pvconapp _ s0 s1 =>
      congr_pvconapp (eq_refl s0)
        (list_ext (ext_Pat sigma_Tm tau_Tm Eq_Tm) s1)
  | por _ s0 s1 =>
      congr_por (ext_Pat sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Pat sigma_Tm tau_Tm Eq_Tm s1)
  | pguard _ s0 s1 =>
      congr_pguard (ext_Pat sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Pat sigma_Tm tau_Tm Eq_Tm s1)
  | pwhen _ s0 s1 =>
      congr_pwhen (ext_Pat sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  end
with ext_CaseBranch {m_Tm : nat} {n_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm n_Tm) (tau_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : CaseBranch m_Tm) {struct s} :
subst_CaseBranch sigma_Tm s = subst_CaseBranch tau_Tm s :=
  match s with
  | casebranch _ s0 s1 =>
      congr_casebranch (ext_Pat sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm sigma_Tm tau_Tm Eq_Tm s1)
  end.

Lemma up_ren_ren_Tm_Tm {k : nat} {l : nat} {m : nat} (xi : fin k -> fin l)
  (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x, funcomp (upRen_Tm_Tm zeta) (upRen_Tm_Tm xi) x = upRen_Tm_Tm rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Lemma up_ren_ren_list_Tm_Tm {p : nat} {k : nat} {l : nat} {m : nat}
  (xi : fin k -> fin l) (zeta : fin l -> fin m) (rho : fin k -> fin m)
  (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_list_Tm_Tm p zeta) (upRen_list_Tm_Tm p xi) x =
  upRen_list_Tm_Tm p rho x.
Proof.
exact (up_ren_ren_p Eq).
Qed.

Fixpoint compRenRen_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(rho_Tm : fin m_Tm -> fin l_Tm)
(Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x) (s : Tm m_Tm) {struct
 s} :
ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm rho_Tm s :=
  match s with
  | var _ s0 => ap (var l_Tm) (Eq_Tm s0)
  | ret _ s0 => congr_ret (eq_refl s0)
  | vconapp _ s0 s1 =>
      congr_vconapp (eq_refl s0)
        (list_comp (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm) s1)
  | iffi _ s0 =>
      congr_iffi
        (list_comp (compRenRen_IffiBranch xi_Tm zeta_Tm rho_Tm Eq_Tm) s0)
  | case _ s0 s1 =>
      congr_case (eq_refl s0)
        (list_comp (compRenRen_CaseBranch xi_Tm zeta_Tm rho_Tm Eq_Tm) s1)
  end
with compRenRen_Guard {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(rho_Tm : fin m_Tm -> fin l_Tm)
(Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x) (s : Guard m_Tm)
{struct s} : ren_Guard zeta_Tm (ren_Guard xi_Tm s) = ren_Guard rho_Tm s :=
  match s with
  | comp _ s0 => congr_comp (eq_refl s0)
  | eqn _ s0 s1 =>
      congr_eqn (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      congr_choice (compRenRen_Guard xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (list_comp (compRenRen_Guard xi_Tm zeta_Tm rho_Tm Eq_Tm) s1)
        (compRenRen_Guard xi_Tm zeta_Tm rho_Tm Eq_Tm s2)
        (list_comp (compRenRen_Guard xi_Tm zeta_Tm rho_Tm Eq_Tm) s3)
  end
with compRenRen_Guards {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(rho_Tm : fin m_Tm -> fin l_Tm)
(Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x) (s : Guards m_Tm)
{struct s} : ren_Guards zeta_Tm (ren_Guards xi_Tm s) = ren_Guards rho_Tm s :=
  match s with
  | guards _ s0 =>
      congr_guards
        (list_comp (compRenRen_Guard xi_Tm zeta_Tm rho_Tm Eq_Tm) s0)
  end
with compRenRen_GuardedExp {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(rho_Tm : fin m_Tm -> fin l_Tm)
(Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x) (s : GuardedExp m_Tm)
{struct s} :
ren_GuardedExp zeta_Tm (ren_GuardedExp xi_Tm s) = ren_GuardedExp rho_Tm s :=
  match s with
  | guardedexp _ s0 s1 =>
      congr_guardedexp (compRenRen_Guards xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  end
with compRenRen_IffiBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(rho_Tm : fin m_Tm -> fin l_Tm)
(Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x) (s : IffiBranch m_Tm)
{struct s} :
ren_IffiBranch zeta_Tm (ren_IffiBranch xi_Tm s) = ren_IffiBranch rho_Tm s :=
  match s with
  | iffibranch _ p s0 s1 =>
      congr_iffibranch
        (compRenRen_GuardedExp (upRen_list_Tm_Tm p xi_Tm)
           (upRen_list_Tm_Tm p zeta_Tm) (upRen_list_Tm_Tm p rho_Tm)
           (up_ren_ren_p Eq_Tm) s0)
        (compRenRen_GuardedExp xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  end
with compRenRen_Pat {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(rho_Tm : fin m_Tm -> fin l_Tm)
(Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x) (s : Pat m_Tm) {struct
 s} :
ren_Pat zeta_Tm (ren_Pat xi_Tm s) = ren_Pat rho_Tm s :=
  match s with
  | pname _ s0 =>
      congr_pname
        (compRenRen_Tm (upRen_Tm_Tm xi_Tm) (upRen_Tm_Tm zeta_Tm)
           (upRen_Tm_Tm rho_Tm) (up_ren_ren _ _ _ Eq_Tm) s0)
  | pvconapp _ s0 s1 =>
      congr_pvconapp (eq_refl s0)
        (list_comp (compRenRen_Pat xi_Tm zeta_Tm rho_Tm Eq_Tm) s1)
  | por _ s0 s1 =>
      congr_por (compRenRen_Pat xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Pat xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  | pguard _ s0 s1 =>
      congr_pguard (compRenRen_Pat xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Pat xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  | pwhen _ s0 s1 =>
      congr_pwhen (compRenRen_Pat xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  end
with compRenRen_CaseBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(rho_Tm : fin m_Tm -> fin l_Tm)
(Eq_Tm : forall x, funcomp zeta_Tm xi_Tm x = rho_Tm x) (s : CaseBranch m_Tm)
{struct s} :
ren_CaseBranch zeta_Tm (ren_CaseBranch xi_Tm s) = ren_CaseBranch rho_Tm s :=
  match s with
  | casebranch _ s0 s1 =>
      congr_casebranch (compRenRen_Pat xi_Tm zeta_Tm rho_Tm Eq_Tm s0)
        (compRenRen_Tm xi_Tm zeta_Tm rho_Tm Eq_Tm s1)
  end.

Lemma up_ren_subst_Tm_Tm {k : nat} {l : nat} {m_Tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> Tm m_Tm) (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x, funcomp (up_Tm_Tm tau) (upRen_Tm_Tm xi) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma up_ren_subst_list_Tm_Tm {p : nat} {k : nat} {l : nat} {m_Tm : nat}
  (xi : fin k -> fin l) (tau : fin l -> Tm m_Tm) (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_list_Tm_Tm p tau) (upRen_list_Tm_Tm p xi) x =
  up_list_Tm_Tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr (fun z => scons_p_head' _ _ z)
            (fun z =>
             eq_trans (scons_p_tail' _ _ (xi z))
               (ap (ren_Tm (shift_p p)) (Eq z))))).
Qed.

Fixpoint compRenSubst_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Tm m_Tm) {struct
 s} :
subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | ret _ s0 => congr_ret (eq_refl s0)
  | vconapp _ s0 s1 =>
      congr_vconapp (eq_refl s0)
        (list_comp (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm) s1)
  | iffi _ s0 =>
      congr_iffi
        (list_comp (compRenSubst_IffiBranch xi_Tm tau_Tm theta_Tm Eq_Tm) s0)
  | case _ s0 s1 =>
      congr_case (eq_refl s0)
        (list_comp (compRenSubst_CaseBranch xi_Tm tau_Tm theta_Tm Eq_Tm) s1)
  end
with compRenSubst_Guard {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Guard m_Tm)
{struct s} : subst_Guard tau_Tm (ren_Guard xi_Tm s) = subst_Guard theta_Tm s
:=
  match s with
  | comp _ s0 => congr_comp (eq_refl s0)
  | eqn _ s0 s1 =>
      congr_eqn (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      congr_choice (compRenSubst_Guard xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (list_comp (compRenSubst_Guard xi_Tm tau_Tm theta_Tm Eq_Tm) s1)
        (compRenSubst_Guard xi_Tm tau_Tm theta_Tm Eq_Tm s2)
        (list_comp (compRenSubst_Guard xi_Tm tau_Tm theta_Tm Eq_Tm) s3)
  end
with compRenSubst_Guards {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Guards m_Tm)
{struct s} :
subst_Guards tau_Tm (ren_Guards xi_Tm s) = subst_Guards theta_Tm s :=
  match s with
  | guards _ s0 =>
      congr_guards
        (list_comp (compRenSubst_Guard xi_Tm tau_Tm theta_Tm Eq_Tm) s0)
  end
with compRenSubst_GuardedExp {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : GuardedExp m_Tm)
{struct s} :
subst_GuardedExp tau_Tm (ren_GuardedExp xi_Tm s) =
subst_GuardedExp theta_Tm s :=
  match s with
  | guardedexp _ s0 s1 =>
      congr_guardedexp (compRenSubst_Guards xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  end
with compRenSubst_IffiBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : IffiBranch m_Tm)
{struct s} :
subst_IffiBranch tau_Tm (ren_IffiBranch xi_Tm s) =
subst_IffiBranch theta_Tm s :=
  match s with
  | iffibranch _ p s0 s1 =>
      congr_iffibranch
        (compRenSubst_GuardedExp (upRen_list_Tm_Tm p xi_Tm)
           (up_list_Tm_Tm p tau_Tm) (up_list_Tm_Tm p theta_Tm)
           (up_ren_subst_list_Tm_Tm _ _ _ Eq_Tm) s0)
        (compRenSubst_GuardedExp xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  end
with compRenSubst_Pat {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : Pat m_Tm)
{struct s} : subst_Pat tau_Tm (ren_Pat xi_Tm s) = subst_Pat theta_Tm s :=
  match s with
  | pname _ s0 =>
      congr_pname
        (compRenSubst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_ren_subst_Tm_Tm _ _ _ Eq_Tm) s0)
  | pvconapp _ s0 s1 =>
      congr_pvconapp (eq_refl s0)
        (list_comp (compRenSubst_Pat xi_Tm tau_Tm theta_Tm Eq_Tm) s1)
  | por _ s0 s1 =>
      congr_por (compRenSubst_Pat xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Pat xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  | pguard _ s0 s1 =>
      congr_pguard (compRenSubst_Pat xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Pat xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  | pwhen _ s0 s1 =>
      congr_pwhen (compRenSubst_Pat xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  end
with compRenSubst_CaseBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp tau_Tm xi_Tm x = theta_Tm x) (s : CaseBranch m_Tm)
{struct s} :
subst_CaseBranch tau_Tm (ren_CaseBranch xi_Tm s) =
subst_CaseBranch theta_Tm s :=
  match s with
  | casebranch _ s0 s1 =>
      congr_casebranch (compRenSubst_Pat xi_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compRenSubst_Tm xi_Tm tau_Tm theta_Tm Eq_Tm s1)
  end.

Lemma up_subst_ren_Tm_Tm {k : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma : fin k -> Tm l_Tm) (zeta_Tm : fin l_Tm -> fin m_Tm)
  (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp (ren_Tm zeta_Tm) sigma x = theta x) :
  forall x,
  funcomp (ren_Tm (upRen_Tm_Tm zeta_Tm)) (up_Tm_Tm sigma) x =
  up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenRen_Tm shift (upRen_Tm_Tm zeta_Tm)
                (funcomp shift zeta_Tm) (fun x => eq_refl) (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compRenRen_Tm zeta_Tm shift (funcomp shift zeta_Tm)
                      (fun x => eq_refl) (sigma fin_n)))
                (ap (ren_Tm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_ren_list_Tm_Tm {p : nat} {k : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma : fin k -> Tm l_Tm) (zeta_Tm : fin l_Tm -> fin m_Tm)
  (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp (ren_Tm zeta_Tm) sigma x = theta x) :
  forall x,
  funcomp (ren_Tm (upRen_list_Tm_Tm p zeta_Tm)) (up_list_Tm_Tm p sigma) x =
  up_list_Tm_Tm p theta x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ _ n)
         (scons_p_congr
            (fun x => ap (var (plus p m_Tm)) (scons_p_head' _ _ x))
            (fun n =>
             eq_trans
               (compRenRen_Tm (shift_p p) (upRen_list_Tm_Tm p zeta_Tm)
                  (funcomp (shift_p p) zeta_Tm)
                  (fun x => scons_p_tail' _ _ x) (sigma n))
               (eq_trans
                  (eq_sym
                     (compRenRen_Tm zeta_Tm (shift_p p)
                        (funcomp (shift_p p) zeta_Tm) (fun x => eq_refl)
                        (sigma n)))
                  (ap (ren_Tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstRen_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x)
(s : Tm m_Tm) {struct s} :
ren_Tm zeta_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | ret _ s0 => congr_ret (eq_refl s0)
  | vconapp _ s0 s1 =>
      congr_vconapp (eq_refl s0)
        (list_comp (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm) s1)
  | iffi _ s0 =>
      congr_iffi
        (list_comp (compSubstRen_IffiBranch sigma_Tm zeta_Tm theta_Tm Eq_Tm)
           s0)
  | case _ s0 s1 =>
      congr_case (eq_refl s0)
        (list_comp (compSubstRen_CaseBranch sigma_Tm zeta_Tm theta_Tm Eq_Tm)
           s1)
  end
with compSubstRen_Guard {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x)
(s : Guard m_Tm) {struct s} :
ren_Guard zeta_Tm (subst_Guard sigma_Tm s) = subst_Guard theta_Tm s :=
  match s with
  | comp _ s0 => congr_comp (eq_refl s0)
  | eqn _ s0 s1 =>
      congr_eqn (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      congr_choice (compSubstRen_Guard sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (list_comp (compSubstRen_Guard sigma_Tm zeta_Tm theta_Tm Eq_Tm) s1)
        (compSubstRen_Guard sigma_Tm zeta_Tm theta_Tm Eq_Tm s2)
        (list_comp (compSubstRen_Guard sigma_Tm zeta_Tm theta_Tm Eq_Tm) s3)
  end
with compSubstRen_Guards {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x)
(s : Guards m_Tm) {struct s} :
ren_Guards zeta_Tm (subst_Guards sigma_Tm s) = subst_Guards theta_Tm s :=
  match s with
  | guards _ s0 =>
      congr_guards
        (list_comp (compSubstRen_Guard sigma_Tm zeta_Tm theta_Tm Eq_Tm) s0)
  end
with compSubstRen_GuardedExp {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x)
(s : GuardedExp m_Tm) {struct s} :
ren_GuardedExp zeta_Tm (subst_GuardedExp sigma_Tm s) =
subst_GuardedExp theta_Tm s :=
  match s with
  | guardedexp _ s0 s1 =>
      congr_guardedexp
        (compSubstRen_Guards sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  end
with compSubstRen_IffiBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x)
(s : IffiBranch m_Tm) {struct s} :
ren_IffiBranch zeta_Tm (subst_IffiBranch sigma_Tm s) =
subst_IffiBranch theta_Tm s :=
  match s with
  | iffibranch _ p s0 s1 =>
      congr_iffibranch
        (compSubstRen_GuardedExp (up_list_Tm_Tm p sigma_Tm)
           (upRen_list_Tm_Tm p zeta_Tm) (up_list_Tm_Tm p theta_Tm)
           (up_subst_ren_list_Tm_Tm _ _ _ Eq_Tm) s0)
        (compSubstRen_GuardedExp sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  end
with compSubstRen_Pat {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x)
(s : Pat m_Tm) {struct s} :
ren_Pat zeta_Tm (subst_Pat sigma_Tm s) = subst_Pat theta_Tm s :=
  match s with
  | pname _ s0 =>
      congr_pname
        (compSubstRen_Tm (up_Tm_Tm sigma_Tm) (upRen_Tm_Tm zeta_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_ren_Tm_Tm _ _ _ Eq_Tm) s0)
  | pvconapp _ s0 s1 =>
      congr_pvconapp (eq_refl s0)
        (list_comp (compSubstRen_Pat sigma_Tm zeta_Tm theta_Tm Eq_Tm) s1)
  | por _ s0 s1 =>
      congr_por (compSubstRen_Pat sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Pat sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  | pguard _ s0 s1 =>
      congr_pguard (compSubstRen_Pat sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Pat sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  | pwhen _ s0 s1 =>
      congr_pwhen (compSubstRen_Pat sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  end
with compSubstRen_CaseBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (ren_Tm zeta_Tm) sigma_Tm x = theta_Tm x)
(s : CaseBranch m_Tm) {struct s} :
ren_CaseBranch zeta_Tm (subst_CaseBranch sigma_Tm s) =
subst_CaseBranch theta_Tm s :=
  match s with
  | casebranch _ s0 s1 =>
      congr_casebranch (compSubstRen_Pat sigma_Tm zeta_Tm theta_Tm Eq_Tm s0)
        (compSubstRen_Tm sigma_Tm zeta_Tm theta_Tm Eq_Tm s1)
  end.

Lemma up_subst_subst_Tm_Tm {k : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma : fin k -> Tm l_Tm) (tau_Tm : fin l_Tm -> Tm m_Tm)
  (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp (subst_Tm tau_Tm) sigma x = theta x) :
  forall x,
  funcomp (subst_Tm (up_Tm_Tm tau_Tm)) (up_Tm_Tm sigma) x = up_Tm_Tm theta x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n =>
           eq_trans
             (compRenSubst_Tm shift (up_Tm_Tm tau_Tm)
                (funcomp (up_Tm_Tm tau_Tm) shift) (fun x => eq_refl)
                (sigma fin_n))
             (eq_trans
                (eq_sym
                   (compSubstRen_Tm tau_Tm shift
                      (funcomp (ren_Tm shift) tau_Tm) (fun x => eq_refl)
                      (sigma fin_n)))
                (ap (ren_Tm shift) (Eq fin_n)))
       | None => eq_refl
       end).
Qed.

Lemma up_subst_subst_list_Tm_Tm {p : nat} {k : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma : fin k -> Tm l_Tm) (tau_Tm : fin l_Tm -> Tm m_Tm)
  (theta : fin k -> Tm m_Tm)
  (Eq : forall x, funcomp (subst_Tm tau_Tm) sigma x = theta x) :
  forall x,
  funcomp (subst_Tm (up_list_Tm_Tm p tau_Tm)) (up_list_Tm_Tm p sigma) x =
  up_list_Tm_Tm p theta x.
Proof.
exact (fun n =>
       eq_trans
         (scons_p_comp' (funcomp (var (plus p l_Tm)) (zero_p p)) _ _ n)
         (scons_p_congr
            (fun x => scons_p_head' _ (fun z => ren_Tm (shift_p p) _) x)
            (fun n =>
             eq_trans
               (compRenSubst_Tm (shift_p p) (up_list_Tm_Tm p tau_Tm)
                  (funcomp (up_list_Tm_Tm p tau_Tm) (shift_p p))
                  (fun x => eq_refl) (sigma n))
               (eq_trans
                  (eq_sym
                     (compSubstRen_Tm tau_Tm (shift_p p) _
                        (fun x => eq_sym (scons_p_tail' _ _ x)) (sigma n)))
                  (ap (ren_Tm (shift_p p)) (Eq n)))))).
Qed.

Fixpoint compSubstSubst_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Tm m_Tm) {struct s} :
subst_Tm tau_Tm (subst_Tm sigma_Tm s) = subst_Tm theta_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | ret _ s0 => congr_ret (eq_refl s0)
  | vconapp _ s0 s1 =>
      congr_vconapp (eq_refl s0)
        (list_comp (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm) s1)
  | iffi _ s0 =>
      congr_iffi
        (list_comp (compSubstSubst_IffiBranch sigma_Tm tau_Tm theta_Tm Eq_Tm)
           s0)
  | case _ s0 s1 =>
      congr_case (eq_refl s0)
        (list_comp (compSubstSubst_CaseBranch sigma_Tm tau_Tm theta_Tm Eq_Tm)
           s1)
  end
with compSubstSubst_Guard {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Guard m_Tm) {struct s} :
subst_Guard tau_Tm (subst_Guard sigma_Tm s) = subst_Guard theta_Tm s :=
  match s with
  | comp _ s0 => congr_comp (eq_refl s0)
  | eqn _ s0 s1 =>
      congr_eqn (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      congr_choice (compSubstSubst_Guard sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (list_comp (compSubstSubst_Guard sigma_Tm tau_Tm theta_Tm Eq_Tm) s1)
        (compSubstSubst_Guard sigma_Tm tau_Tm theta_Tm Eq_Tm s2)
        (list_comp (compSubstSubst_Guard sigma_Tm tau_Tm theta_Tm Eq_Tm) s3)
  end
with compSubstSubst_Guards {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Guards m_Tm) {struct s} :
subst_Guards tau_Tm (subst_Guards sigma_Tm s) = subst_Guards theta_Tm s :=
  match s with
  | guards _ s0 =>
      congr_guards
        (list_comp (compSubstSubst_Guard sigma_Tm tau_Tm theta_Tm Eq_Tm) s0)
  end
with compSubstSubst_GuardedExp {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : GuardedExp m_Tm) {struct s} :
subst_GuardedExp tau_Tm (subst_GuardedExp sigma_Tm s) =
subst_GuardedExp theta_Tm s :=
  match s with
  | guardedexp _ s0 s1 =>
      congr_guardedexp
        (compSubstSubst_Guards sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  end
with compSubstSubst_IffiBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : IffiBranch m_Tm) {struct s} :
subst_IffiBranch tau_Tm (subst_IffiBranch sigma_Tm s) =
subst_IffiBranch theta_Tm s :=
  match s with
  | iffibranch _ p s0 s1 =>
      congr_iffibranch
        (compSubstSubst_GuardedExp (up_list_Tm_Tm p sigma_Tm)
           (up_list_Tm_Tm p tau_Tm) (up_list_Tm_Tm p theta_Tm)
           (up_subst_subst_list_Tm_Tm _ _ _ Eq_Tm) s0)
        (compSubstSubst_GuardedExp sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  end
with compSubstSubst_Pat {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Pat m_Tm) {struct s} :
subst_Pat tau_Tm (subst_Pat sigma_Tm s) = subst_Pat theta_Tm s :=
  match s with
  | pname _ s0 =>
      congr_pname
        (compSubstSubst_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s0)
  | pvconapp _ s0 s1 =>
      congr_pvconapp (eq_refl s0)
        (list_comp (compSubstSubst_Pat sigma_Tm tau_Tm theta_Tm Eq_Tm) s1)
  | por _ s0 s1 =>
      congr_por (compSubstSubst_Pat sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Pat sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  | pguard _ s0 s1 =>
      congr_pguard (compSubstSubst_Pat sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Pat sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  | pwhen _ s0 s1 =>
      congr_pwhen (compSubstSubst_Pat sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  end
with compSubstSubst_CaseBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : CaseBranch m_Tm) {struct s} :
subst_CaseBranch tau_Tm (subst_CaseBranch sigma_Tm s) =
subst_CaseBranch theta_Tm s :=
  match s with
  | casebranch _ s0 s1 =>
      congr_casebranch (compSubstSubst_Pat sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
  end.

Lemma renRen_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Tm m_Tm) :
  ren_Tm zeta_Tm (ren_Tm xi_Tm s) = ren_Tm (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Tm_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (ren_Tm xi_Tm))
    (ren_Tm (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Tm xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen_Guard {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Guard m_Tm) :
  ren_Guard zeta_Tm (ren_Guard xi_Tm s) = ren_Guard (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Guard xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Guard_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq (funcomp (ren_Guard zeta_Tm) (ren_Guard xi_Tm))
    (ren_Guard (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Guard xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen_Guards {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Guards m_Tm) :
  ren_Guards zeta_Tm (ren_Guards xi_Tm s) =
  ren_Guards (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Guards xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Guards_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq (funcomp (ren_Guards zeta_Tm) (ren_Guards xi_Tm))
    (ren_Guards (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Guards xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen_GuardedExp {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : GuardedExp m_Tm) :
  ren_GuardedExp zeta_Tm (ren_GuardedExp xi_Tm s) =
  ren_GuardedExp (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_GuardedExp xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_GuardedExp_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq
    (funcomp (ren_GuardedExp zeta_Tm) (ren_GuardedExp xi_Tm))
    (ren_GuardedExp (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_GuardedExp xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen_IffiBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : IffiBranch m_Tm) :
  ren_IffiBranch zeta_Tm (ren_IffiBranch xi_Tm s) =
  ren_IffiBranch (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_IffiBranch xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_IffiBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq
    (funcomp (ren_IffiBranch zeta_Tm) (ren_IffiBranch xi_Tm))
    (ren_IffiBranch (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_IffiBranch xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen_Pat {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Pat m_Tm) :
  ren_Pat zeta_Tm (ren_Pat xi_Tm s) = ren_Pat (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_Pat xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_Pat_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq (funcomp (ren_Pat zeta_Tm) (ren_Pat xi_Tm))
    (ren_Pat (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_Pat xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen_CaseBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : CaseBranch m_Tm) :
  ren_CaseBranch zeta_Tm (ren_CaseBranch xi_Tm s) =
  ren_CaseBranch (funcomp zeta_Tm xi_Tm) s.
Proof.
exact (compRenRen_CaseBranch xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_CaseBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq
    (funcomp (ren_CaseBranch zeta_Tm) (ren_CaseBranch xi_Tm))
    (ren_CaseBranch (funcomp zeta_Tm xi_Tm)).
Proof.
exact (fun s => compRenRen_CaseBranch xi_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) (s : Tm m_Tm)
  : subst_Tm tau_Tm (ren_Tm xi_Tm s) = subst_Tm (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Tm_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (ren_Tm xi_Tm))
    (subst_Tm (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Tm xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Guard {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Guard m_Tm) :
  subst_Guard tau_Tm (ren_Guard xi_Tm s) =
  subst_Guard (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Guard xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Guard_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Guard tau_Tm) (ren_Guard xi_Tm))
    (subst_Guard (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Guard xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Guards {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Guards m_Tm) :
  subst_Guards tau_Tm (ren_Guards xi_Tm s) =
  subst_Guards (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Guards xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Guards_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Guards tau_Tm) (ren_Guards xi_Tm))
    (subst_Guards (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Guards xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_GuardedExp {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : GuardedExp m_Tm) :
  subst_GuardedExp tau_Tm (ren_GuardedExp xi_Tm s) =
  subst_GuardedExp (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_GuardedExp xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_GuardedExp_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_GuardedExp tau_Tm) (ren_GuardedExp xi_Tm))
    (subst_GuardedExp (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_GuardedExp xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_IffiBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : IffiBranch m_Tm) :
  subst_IffiBranch tau_Tm (ren_IffiBranch xi_Tm s) =
  subst_IffiBranch (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_IffiBranch xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_IffiBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_IffiBranch tau_Tm) (ren_IffiBranch xi_Tm))
    (subst_IffiBranch (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_IffiBranch xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Pat {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Pat m_Tm) :
  subst_Pat tau_Tm (ren_Pat xi_Tm s) = subst_Pat (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_Pat xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_Pat_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Pat tau_Tm) (ren_Pat xi_Tm))
    (subst_Pat (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_Pat xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_CaseBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : CaseBranch m_Tm) :
  subst_CaseBranch tau_Tm (ren_CaseBranch xi_Tm s) =
  subst_CaseBranch (funcomp tau_Tm xi_Tm) s.
Proof.
exact (compRenSubst_CaseBranch xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_CaseBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (xi_Tm : fin m_Tm -> fin k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_CaseBranch tau_Tm) (ren_CaseBranch xi_Tm))
    (subst_CaseBranch (funcomp tau_Tm xi_Tm)).
Proof.
exact (fun s => compRenSubst_CaseBranch xi_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Tm m_Tm) :
  ren_Tm zeta_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Tm_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq (funcomp (ren_Tm zeta_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Tm sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Guard {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Guard m_Tm) :
  ren_Guard zeta_Tm (subst_Guard sigma_Tm s) =
  subst_Guard (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Guard sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Guard_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq
    (funcomp (ren_Guard zeta_Tm) (subst_Guard sigma_Tm))
    (subst_Guard (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Guard sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Guards {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Guards m_Tm) :
  ren_Guards zeta_Tm (subst_Guards sigma_Tm s) =
  subst_Guards (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Guards sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Guards_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq
    (funcomp (ren_Guards zeta_Tm) (subst_Guards sigma_Tm))
    (subst_Guards (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Guards sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_GuardedExp {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : GuardedExp m_Tm) :
  ren_GuardedExp zeta_Tm (subst_GuardedExp sigma_Tm s) =
  subst_GuardedExp (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_GuardedExp sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_GuardedExp_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq
    (funcomp (ren_GuardedExp zeta_Tm) (subst_GuardedExp sigma_Tm))
    (subst_GuardedExp (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s =>
       compSubstRen_GuardedExp sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_IffiBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : IffiBranch m_Tm) :
  ren_IffiBranch zeta_Tm (subst_IffiBranch sigma_Tm s) =
  subst_IffiBranch (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_IffiBranch sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_IffiBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq
    (funcomp (ren_IffiBranch zeta_Tm) (subst_IffiBranch sigma_Tm))
    (subst_IffiBranch (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s =>
       compSubstRen_IffiBranch sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Pat {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : Pat m_Tm) :
  ren_Pat zeta_Tm (subst_Pat sigma_Tm s) =
  subst_Pat (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_Pat sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_Pat_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq (funcomp (ren_Pat zeta_Tm) (subst_Pat sigma_Tm))
    (subst_Pat (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstRen_Pat sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_CaseBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm)
  (s : CaseBranch m_Tm) :
  ren_CaseBranch zeta_Tm (subst_CaseBranch sigma_Tm s) =
  subst_CaseBranch (funcomp (ren_Tm zeta_Tm) sigma_Tm) s.
Proof.
exact (compSubstRen_CaseBranch sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substRen_CaseBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (zeta_Tm : fin k_Tm -> fin l_Tm) :
  pointwise_relation _ eq
    (funcomp (ren_CaseBranch zeta_Tm) (subst_CaseBranch sigma_Tm))
    (subst_CaseBranch (funcomp (ren_Tm zeta_Tm) sigma_Tm)).
Proof.
exact (fun s =>
       compSubstRen_CaseBranch sigma_Tm zeta_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Tm m_Tm) :
  subst_Tm tau_Tm (subst_Tm sigma_Tm s) =
  subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tm_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm tau_Tm) (subst_Tm sigma_Tm))
    (subst_Tm (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Tm sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Guard {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Guard m_Tm) :
  subst_Guard tau_Tm (subst_Guard sigma_Tm s) =
  subst_Guard (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Guard sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Guard_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_Guard tau_Tm) (subst_Guard sigma_Tm))
    (subst_Guard (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Guard sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Guards {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Guards m_Tm) :
  subst_Guards tau_Tm (subst_Guards sigma_Tm s) =
  subst_Guards (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Guards sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Guards_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_Guards tau_Tm) (subst_Guards sigma_Tm))
    (subst_Guards (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Guards sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_GuardedExp {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : GuardedExp m_Tm) :
  subst_GuardedExp tau_Tm (subst_GuardedExp sigma_Tm s) =
  subst_GuardedExp (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_GuardedExp sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_GuardedExp_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_GuardedExp tau_Tm) (subst_GuardedExp sigma_Tm))
    (subst_GuardedExp (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s =>
       compSubstSubst_GuardedExp sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_IffiBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : IffiBranch m_Tm) :
  subst_IffiBranch tau_Tm (subst_IffiBranch sigma_Tm s) =
  subst_IffiBranch (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_IffiBranch sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_IffiBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_IffiBranch tau_Tm) (subst_IffiBranch sigma_Tm))
    (subst_IffiBranch (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s =>
       compSubstSubst_IffiBranch sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Pat {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Pat m_Tm) :
  subst_Pat tau_Tm (subst_Pat sigma_Tm s) =
  subst_Pat (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Pat sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Pat_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Pat tau_Tm) (subst_Pat sigma_Tm))
    (subst_Pat (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Pat sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_CaseBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : CaseBranch m_Tm) :
  subst_CaseBranch tau_Tm (subst_CaseBranch sigma_Tm s) =
  subst_CaseBranch (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_CaseBranch sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_CaseBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_CaseBranch tau_Tm) (subst_CaseBranch sigma_Tm))
    (subst_CaseBranch (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s =>
       compSubstSubst_CaseBranch sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_Tm_Tm {m : nat} {n_Tm : nat} (xi : fin m -> fin n_Tm)
  (sigma : fin m -> Tm n_Tm)
  (Eq : forall x, funcomp (var n_Tm) xi x = sigma x) :
  forall x, funcomp (var (S n_Tm)) (upRen_Tm_Tm xi) x = up_Tm_Tm sigma x.
Proof.
exact (fun n =>
       match n with
       | Some fin_n => ap (ren_Tm shift) (Eq fin_n)
       | None => eq_refl
       end).
Qed.

Lemma rinstInst_up_list_Tm_Tm {p : nat} {m : nat} {n_Tm : nat}
  (xi : fin m -> fin n_Tm) (sigma : fin m -> Tm n_Tm)
  (Eq : forall x, funcomp (var n_Tm) xi x = sigma x) :
  forall x,
  funcomp (var (plus p n_Tm)) (upRen_list_Tm_Tm p xi) x =
  up_list_Tm_Tm p sigma x.
Proof.
exact (fun n =>
       eq_trans (scons_p_comp' _ _ (var (plus p n_Tm)) n)
         (scons_p_congr (fun z => eq_refl)
            (fun n => ap (ren_Tm (shift_p p)) (Eq n)))).
Qed.

Fixpoint rinst_inst_Tm {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (sigma_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, funcomp (var n_Tm) xi_Tm x = sigma_Tm x) (s : Tm m_Tm)
{struct s} : ren_Tm xi_Tm s = subst_Tm sigma_Tm s :=
  match s with
  | var _ s0 => Eq_Tm s0
  | ret _ s0 => congr_ret (eq_refl s0)
  | vconapp _ s0 s1 =>
      congr_vconapp (eq_refl s0)
        (list_ext (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm) s1)
  | iffi _ s0 =>
      congr_iffi (list_ext (rinst_inst_IffiBranch xi_Tm sigma_Tm Eq_Tm) s0)
  | case _ s0 s1 =>
      congr_case (eq_refl s0)
        (list_ext (rinst_inst_CaseBranch xi_Tm sigma_Tm Eq_Tm) s1)
  end
with rinst_inst_Guard {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (sigma_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, funcomp (var n_Tm) xi_Tm x = sigma_Tm x) (s : Guard m_Tm)
{struct s} : ren_Guard xi_Tm s = subst_Guard sigma_Tm s :=
  match s with
  | comp _ s0 => congr_comp (eq_refl s0)
  | eqn _ s0 s1 =>
      congr_eqn (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  | choice _ s0 s1 s2 s3 =>
      congr_choice (rinst_inst_Guard xi_Tm sigma_Tm Eq_Tm s0)
        (list_ext (rinst_inst_Guard xi_Tm sigma_Tm Eq_Tm) s1)
        (rinst_inst_Guard xi_Tm sigma_Tm Eq_Tm s2)
        (list_ext (rinst_inst_Guard xi_Tm sigma_Tm Eq_Tm) s3)
  end
with rinst_inst_Guards {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (sigma_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, funcomp (var n_Tm) xi_Tm x = sigma_Tm x) (s : Guards m_Tm)
{struct s} : ren_Guards xi_Tm s = subst_Guards sigma_Tm s :=
  match s with
  | guards _ s0 =>
      congr_guards (list_ext (rinst_inst_Guard xi_Tm sigma_Tm Eq_Tm) s0)
  end
with rinst_inst_GuardedExp {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (sigma_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, funcomp (var n_Tm) xi_Tm x = sigma_Tm x)
(s : GuardedExp m_Tm) {struct s} :
ren_GuardedExp xi_Tm s = subst_GuardedExp sigma_Tm s :=
  match s with
  | guardedexp _ s0 s1 =>
      congr_guardedexp (rinst_inst_Guards xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  end
with rinst_inst_IffiBranch {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (sigma_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, funcomp (var n_Tm) xi_Tm x = sigma_Tm x)
(s : IffiBranch m_Tm) {struct s} :
ren_IffiBranch xi_Tm s = subst_IffiBranch sigma_Tm s :=
  match s with
  | iffibranch _ p s0 s1 =>
      congr_iffibranch
        (rinst_inst_GuardedExp (upRen_list_Tm_Tm p xi_Tm)
           (up_list_Tm_Tm p sigma_Tm) (rinstInst_up_list_Tm_Tm _ _ Eq_Tm) s0)
        (rinst_inst_GuardedExp xi_Tm sigma_Tm Eq_Tm s1)
  end
with rinst_inst_Pat {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
(sigma_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, funcomp (var n_Tm) xi_Tm x = sigma_Tm x) (s : Pat m_Tm)
{struct s} : ren_Pat xi_Tm s = subst_Pat sigma_Tm s :=
  match s with
  | pname _ s0 =>
      congr_pname
        (rinst_inst_Tm (upRen_Tm_Tm xi_Tm) (up_Tm_Tm sigma_Tm)
           (rinstInst_up_Tm_Tm _ _ Eq_Tm) s0)
  | pvconapp _ s0 s1 =>
      congr_pvconapp (eq_refl s0)
        (list_ext (rinst_inst_Pat xi_Tm sigma_Tm Eq_Tm) s1)
  | por _ s0 s1 =>
      congr_por (rinst_inst_Pat xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Pat xi_Tm sigma_Tm Eq_Tm s1)
  | pguard _ s0 s1 =>
      congr_pguard (rinst_inst_Pat xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Pat xi_Tm sigma_Tm Eq_Tm s1)
  | pwhen _ s0 s1 =>
      congr_pwhen (rinst_inst_Pat xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  end
with rinst_inst_CaseBranch {m_Tm : nat} {n_Tm : nat}
(xi_Tm : fin m_Tm -> fin n_Tm) (sigma_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, funcomp (var n_Tm) xi_Tm x = sigma_Tm x)
(s : CaseBranch m_Tm) {struct s} :
ren_CaseBranch xi_Tm s = subst_CaseBranch sigma_Tm s :=
  match s with
  | casebranch _ s0 s1 =>
      congr_casebranch (rinst_inst_Pat xi_Tm sigma_Tm Eq_Tm s0)
        (rinst_inst_Tm xi_Tm sigma_Tm Eq_Tm s1)
  end.

Lemma rinstInst'_Tm {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
  (s : Tm m_Tm) : ren_Tm xi_Tm s = subst_Tm (funcomp (var n_Tm) xi_Tm) s.
Proof.
exact (rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Tm_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (ren_Tm xi_Tm)
    (subst_Tm (funcomp (var n_Tm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Tm xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Guard {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) (s : Guard m_Tm) :
  ren_Guard xi_Tm s = subst_Guard (funcomp (var n_Tm) xi_Tm) s.
Proof.
exact (rinst_inst_Guard xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Guard_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (ren_Guard xi_Tm)
    (subst_Guard (funcomp (var n_Tm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Guard xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Guards {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) (s : Guards m_Tm) :
  ren_Guards xi_Tm s = subst_Guards (funcomp (var n_Tm) xi_Tm) s.
Proof.
exact (rinst_inst_Guards xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Guards_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (ren_Guards xi_Tm)
    (subst_Guards (funcomp (var n_Tm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Guards xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_GuardedExp {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) (s : GuardedExp m_Tm) :
  ren_GuardedExp xi_Tm s = subst_GuardedExp (funcomp (var n_Tm) xi_Tm) s.
Proof.
exact (rinst_inst_GuardedExp xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_GuardedExp_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (ren_GuardedExp xi_Tm)
    (subst_GuardedExp (funcomp (var n_Tm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_GuardedExp xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_IffiBranch {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) (s : IffiBranch m_Tm) :
  ren_IffiBranch xi_Tm s = subst_IffiBranch (funcomp (var n_Tm) xi_Tm) s.
Proof.
exact (rinst_inst_IffiBranch xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_IffiBranch_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (ren_IffiBranch xi_Tm)
    (subst_IffiBranch (funcomp (var n_Tm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_IffiBranch xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Pat {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
  (s : Pat m_Tm) : ren_Pat xi_Tm s = subst_Pat (funcomp (var n_Tm) xi_Tm) s.
Proof.
exact (rinst_inst_Pat xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_Pat_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (ren_Pat xi_Tm)
    (subst_Pat (funcomp (var n_Tm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_Pat xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_CaseBranch {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) (s : CaseBranch m_Tm) :
  ren_CaseBranch xi_Tm s = subst_CaseBranch (funcomp (var n_Tm) xi_Tm) s.
Proof.
exact (rinst_inst_CaseBranch xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_CaseBranch_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (ren_CaseBranch xi_Tm)
    (subst_CaseBranch (funcomp (var n_Tm) xi_Tm)).
Proof.
exact (fun s => rinst_inst_CaseBranch xi_Tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm {m_Tm : nat} (s : Tm m_Tm) : subst_Tm (var m_Tm) s = s.
Proof.
exact (idSubst_Tm (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tm_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_Tm (var m_Tm)) id.
Proof.
exact (fun s => idSubst_Tm (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Guard {m_Tm : nat} (s : Guard m_Tm) :
  subst_Guard (var m_Tm) s = s.
Proof.
exact (idSubst_Guard (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Guard_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_Guard (var m_Tm)) id.
Proof.
exact (fun s => idSubst_Guard (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Guards {m_Tm : nat} (s : Guards m_Tm) :
  subst_Guards (var m_Tm) s = s.
Proof.
exact (idSubst_Guards (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Guards_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_Guards (var m_Tm)) id.
Proof.
exact (fun s => idSubst_Guards (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_GuardedExp {m_Tm : nat} (s : GuardedExp m_Tm) :
  subst_GuardedExp (var m_Tm) s = s.
Proof.
exact (idSubst_GuardedExp (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_GuardedExp_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_GuardedExp (var m_Tm)) id.
Proof.
exact (fun s => idSubst_GuardedExp (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_IffiBranch {m_Tm : nat} (s : IffiBranch m_Tm) :
  subst_IffiBranch (var m_Tm) s = s.
Proof.
exact (idSubst_IffiBranch (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_IffiBranch_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_IffiBranch (var m_Tm)) id.
Proof.
exact (fun s => idSubst_IffiBranch (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Pat {m_Tm : nat} (s : Pat m_Tm) : subst_Pat (var m_Tm) s = s.
Proof.
exact (idSubst_Pat (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Pat_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_Pat (var m_Tm)) id.
Proof.
exact (fun s => idSubst_Pat (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_CaseBranch {m_Tm : nat} (s : CaseBranch m_Tm) :
  subst_CaseBranch (var m_Tm) s = s.
Proof.
exact (idSubst_CaseBranch (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_CaseBranch_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_CaseBranch (var m_Tm)) id.
Proof.
exact (fun s => idSubst_CaseBranch (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_Tm {m_Tm : nat} (s : Tm m_Tm) : ren_Tm id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma rinstId'_Tm_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (@ren_Tm m_Tm m_Tm id) id.
Proof.
exact (fun s => eq_ind_r (fun t => t = s) (instId'_Tm s) (rinstInst'_Tm id s)).
Qed.

Lemma rinstId'_Guard {m_Tm : nat} (s : Guard m_Tm) : ren_Guard id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Guard s) (rinstInst'_Guard id s)).
Qed.

Lemma rinstId'_Guard_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (@ren_Guard m_Tm m_Tm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_Guard s) (rinstInst'_Guard id s)).
Qed.

Lemma rinstId'_Guards {m_Tm : nat} (s : Guards m_Tm) : ren_Guards id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Guards s) (rinstInst'_Guards id s)).
Qed.

Lemma rinstId'_Guards_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (@ren_Guards m_Tm m_Tm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_Guards s) (rinstInst'_Guards id s)).
Qed.

Lemma rinstId'_GuardedExp {m_Tm : nat} (s : GuardedExp m_Tm) :
  ren_GuardedExp id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_GuardedExp s)
         (rinstInst'_GuardedExp id s)).
Qed.

Lemma rinstId'_GuardedExp_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (@ren_GuardedExp m_Tm m_Tm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_GuardedExp s)
         (rinstInst'_GuardedExp id s)).
Qed.

Lemma rinstId'_IffiBranch {m_Tm : nat} (s : IffiBranch m_Tm) :
  ren_IffiBranch id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_IffiBranch s)
         (rinstInst'_IffiBranch id s)).
Qed.

Lemma rinstId'_IffiBranch_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (@ren_IffiBranch m_Tm m_Tm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_IffiBranch s)
         (rinstInst'_IffiBranch id s)).
Qed.

Lemma rinstId'_Pat {m_Tm : nat} (s : Pat m_Tm) : ren_Pat id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_Pat s) (rinstInst'_Pat id s)).
Qed.

Lemma rinstId'_Pat_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (@ren_Pat m_Tm m_Tm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_Pat s) (rinstInst'_Pat id s)).
Qed.

Lemma rinstId'_CaseBranch {m_Tm : nat} (s : CaseBranch m_Tm) :
  ren_CaseBranch id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_CaseBranch s)
         (rinstInst'_CaseBranch id s)).
Qed.

Lemma rinstId'_CaseBranch_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (@ren_CaseBranch m_Tm m_Tm id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_CaseBranch s)
         (rinstInst'_CaseBranch id s)).
Qed.

Lemma varL'_Tm {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
  (x : fin m_Tm) : subst_Tm sigma_Tm (var m_Tm x) = sigma_Tm x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_Tm_pointwise {m_Tm : nat} {n_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm n_Tm) :
  pointwise_relation _ eq (funcomp (subst_Tm sigma_Tm) (var m_Tm)) sigma_Tm.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_Tm {m_Tm : nat} {n_Tm : nat} (xi_Tm : fin m_Tm -> fin n_Tm)
  (x : fin m_Tm) : ren_Tm xi_Tm (var m_Tm x) = var n_Tm (xi_Tm x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_Tm_pointwise {m_Tm : nat} {n_Tm : nat}
  (xi_Tm : fin m_Tm -> fin n_Tm) :
  pointwise_relation _ eq (funcomp (ren_Tm xi_Tm) (var m_Tm))
    (funcomp (var n_Tm) xi_Tm).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive TestBranch (n_Tm : nat) : Type :=
    testbranch :
      forall p : nat,
      nat -> Tree (plus p n_Tm) -> Tree n_Tm -> TestBranch n_Tm
with Tree (n_Tm : nat) : Type :=
  | tfail : Tree n_Tm
  | match : Tm n_Tm -> Tree n_Tm
  | ifx : Tm n_Tm -> Tree n_Tm -> Tree n_Tm -> Tree n_Tm
  | letx :
      Tm n_Tm -> Tm (S n_Tm) -> Tree n_Tm -> option (Tree n_Tm) -> Tree n_Tm
  | test :
      Tree (S n_Tm) ->
      list (TestBranch n_Tm) -> option (Tree n_Tm) -> Tree n_Tm.

Lemma congr_testbranch {p : nat} {m_Tm : nat} {s0 : nat}
  {s1 : Tree (plus p m_Tm)} {s2 : Tree m_Tm} {t0 : nat}
  {t1 : Tree (plus p m_Tm)} {t2 : Tree m_Tm} (H0 : s0 = t0) (H1 : s1 = t1)
  (H2 : s2 = t2) : testbranch m_Tm p s0 s1 s2 = testbranch m_Tm p t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans eq_refl (ap (fun x => testbranch m_Tm p x s1 s2) H0))
            (ap (fun x => testbranch m_Tm p t0 x s2) H1))
         (ap (fun x => testbranch m_Tm p t0 t1 x) H2)).
Qed.

Lemma congr_tfail {m_Tm : nat} : tfail m_Tm = tfail m_Tm.
Proof.
exact (eq_refl).
Qed.

Lemma congr_match {m_Tm : nat} {s0 : Tm m_Tm} {t0 : Tm m_Tm} (H0 : s0 = t0) :
  match m_Tm s0 = match m_Tm t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => match m_Tm x) H0)).
Qed.

Lemma congr_ifx {m_Tm : nat} {s0 : Tm m_Tm} {s1 : Tree m_Tm} {s2 : Tree m_Tm}
  {t0 : Tm m_Tm} {t1 : Tree m_Tm} {t2 : Tree m_Tm} (H0 : s0 = t0)
  (H1 : s1 = t1) (H2 : s2 = t2) : ifx m_Tm s0 s1 s2 = ifx m_Tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => ifx m_Tm x s1 s2) H0))
            (ap (fun x => ifx m_Tm t0 x s2) H1))
         (ap (fun x => ifx m_Tm t0 t1 x) H2)).
Qed.

Lemma congr_letx {m_Tm : nat} {s0 : Tm m_Tm} {s1 : Tm (S m_Tm)}
  {s2 : Tree m_Tm} {s3 : option (Tree m_Tm)} {t0 : Tm m_Tm}
  {t1 : Tm (S m_Tm)} {t2 : Tree m_Tm} {t3 : option (Tree m_Tm)}
  (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) (H3 : s3 = t3) :
  letx m_Tm s0 s1 s2 s3 = letx m_Tm t0 t1 t2 t3.
Proof.
exact (eq_trans
         (eq_trans
            (eq_trans
               (eq_trans eq_refl (ap (fun x => letx m_Tm x s1 s2 s3) H0))
               (ap (fun x => letx m_Tm t0 x s2 s3) H1))
            (ap (fun x => letx m_Tm t0 t1 x s3) H2))
         (ap (fun x => letx m_Tm t0 t1 t2 x) H3)).
Qed.

Lemma congr_test {m_Tm : nat} {s0 : Tree (S m_Tm)}
  {s1 : list (TestBranch m_Tm)} {s2 : option (Tree m_Tm)}
  {t0 : Tree (S m_Tm)} {t1 : list (TestBranch m_Tm)}
  {t2 : option (Tree m_Tm)} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  test m_Tm s0 s1 s2 = test m_Tm t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => test m_Tm x s1 s2) H0))
            (ap (fun x => test m_Tm t0 x s2) H1))
         (ap (fun x => test m_Tm t0 t1 x) H2)).
Qed.

Fixpoint subst_TestBranch {m_Tm : nat} {n_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm n_Tm) (s : TestBranch m_Tm) {struct s} :
TestBranch n_Tm :=
  match s with
  | testbranch _ p s0 s1 s2 =>
      testbranch n_Tm p s0 (subst_Tree (up_list_Tm_Tm p sigma_Tm) s1)
        (subst_Tree sigma_Tm s2)
  end
with subst_Tree {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(s : Tree m_Tm) {struct s} : Tree n_Tm :=
  match s with
  | tfail _ => tfail n_Tm
  | match _ s0 => match n_Tm (subst_Tm sigma_Tm s0)
  | ifx _ s0 s1 s2 =>
      ifx n_Tm (subst_Tm sigma_Tm s0) (subst_Tree sigma_Tm s1)
        (subst_Tree sigma_Tm s2)
  | letx _ s0 s1 s2 s3 =>
      letx n_Tm (subst_Tm sigma_Tm s0) (subst_Tm (up_Tm_Tm sigma_Tm) s1)
        (subst_Tree sigma_Tm s2) (option_map (subst_Tree sigma_Tm) s3)
  | test _ s0 s1 s2 =>
      test n_Tm (subst_Tree (up_Tm_Tm sigma_Tm) s0)
        (list_map (subst_TestBranch sigma_Tm) s1)
        (option_map (subst_Tree sigma_Tm) s2)
  end.

Fixpoint idSubst_TestBranch {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : TestBranch m_Tm) {struct s}
   :
subst_TestBranch sigma_Tm s = s :=
  match s with
  | testbranch _ p s0 s1 s2 =>
      congr_testbranch (eq_refl s0)
        (idSubst_Tree (up_list_Tm_Tm p sigma_Tm) (upId_list_Tm_Tm _ Eq_Tm) s1)
        (idSubst_Tree sigma_Tm Eq_Tm s2)
  end
with idSubst_Tree {m_Tm : nat} (sigma_Tm : fin m_Tm -> Tm m_Tm)
(Eq_Tm : forall x, sigma_Tm x = var m_Tm x) (s : Tree m_Tm) {struct s} :
subst_Tree sigma_Tm s = s :=
  match s with
  | tfail _ => congr_tfail
  | match _ s0 => congr_match (idSubst_Tm sigma_Tm Eq_Tm s0)
  | ifx _ s0 s1 s2 =>
      congr_ifx (idSubst_Tm sigma_Tm Eq_Tm s0)
        (idSubst_Tree sigma_Tm Eq_Tm s1) (idSubst_Tree sigma_Tm Eq_Tm s2)
  | letx _ s0 s1 s2 s3 =>
      congr_letx (idSubst_Tm sigma_Tm Eq_Tm s0)
        (idSubst_Tm (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s1)
        (idSubst_Tree sigma_Tm Eq_Tm s2)
        (option_id (idSubst_Tree sigma_Tm Eq_Tm) s3)
  | test _ s0 s1 s2 =>
      congr_test (idSubst_Tree (up_Tm_Tm sigma_Tm) (upId_Tm_Tm _ Eq_Tm) s0)
        (list_id (idSubst_TestBranch sigma_Tm Eq_Tm) s1)
        (option_id (idSubst_Tree sigma_Tm Eq_Tm) s2)
  end.

Fixpoint ext_TestBranch {m_Tm : nat} {n_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm n_Tm) (tau_Tm : fin m_Tm -> Tm n_Tm)
(Eq_Tm : forall x, sigma_Tm x = tau_Tm x) (s : TestBranch m_Tm) {struct s} :
subst_TestBranch sigma_Tm s = subst_TestBranch tau_Tm s :=
  match s with
  | testbranch _ p s0 s1 s2 =>
      congr_testbranch (eq_refl s0)
        (ext_Tree (up_list_Tm_Tm p sigma_Tm) (up_list_Tm_Tm p tau_Tm)
           (upExt_list_Tm_Tm _ _ Eq_Tm) s1)
        (ext_Tree sigma_Tm tau_Tm Eq_Tm s2)
  end
with ext_Tree {m_Tm : nat} {n_Tm : nat} (sigma_Tm : fin m_Tm -> Tm n_Tm)
(tau_Tm : fin m_Tm -> Tm n_Tm) (Eq_Tm : forall x, sigma_Tm x = tau_Tm x)
(s : Tree m_Tm) {struct s} : subst_Tree sigma_Tm s = subst_Tree tau_Tm s :=
  match s with
  | tfail _ => congr_tfail
  | match _ s0 => congr_match (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
  | ifx _ s0 s1 s2 =>
      congr_ifx (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tree sigma_Tm tau_Tm Eq_Tm s1)
        (ext_Tree sigma_Tm tau_Tm Eq_Tm s2)
  | letx _ s0 s1 s2 s3 =>
      congr_letx (ext_Tm sigma_Tm tau_Tm Eq_Tm s0)
        (ext_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm) (upExt_Tm_Tm _ _ Eq_Tm)
           s1)
        (ext_Tree sigma_Tm tau_Tm Eq_Tm s2)
        (option_ext (ext_Tree sigma_Tm tau_Tm Eq_Tm) s3)
  | test _ s0 s1 s2 =>
      congr_test
        (ext_Tree (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (upExt_Tm_Tm _ _ Eq_Tm) s0)
        (list_ext (ext_TestBranch sigma_Tm tau_Tm Eq_Tm) s1)
        (option_ext (ext_Tree sigma_Tm tau_Tm Eq_Tm) s2)
  end.

Fixpoint compSubstSubst_TestBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : TestBranch m_Tm) {struct s} :
subst_TestBranch tau_Tm (subst_TestBranch sigma_Tm s) =
subst_TestBranch theta_Tm s :=
  match s with
  | testbranch _ p s0 s1 s2 =>
      congr_testbranch (eq_refl s0)
        (compSubstSubst_Tree (up_list_Tm_Tm p sigma_Tm)
           (up_list_Tm_Tm p tau_Tm) (up_list_Tm_Tm p theta_Tm)
           (up_subst_subst_list_Tm_Tm _ _ _ Eq_Tm) s1)
        (compSubstSubst_Tree sigma_Tm tau_Tm theta_Tm Eq_Tm s2)
  end
with compSubstSubst_Tree {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
(sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
(theta_Tm : fin m_Tm -> Tm l_Tm)
(Eq_Tm : forall x, funcomp (subst_Tm tau_Tm) sigma_Tm x = theta_Tm x)
(s : Tree m_Tm) {struct s} :
subst_Tree tau_Tm (subst_Tree sigma_Tm s) = subst_Tree theta_Tm s :=
  match s with
  | tfail _ => congr_tfail
  | match _ s0 =>
      congr_match (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
  | ifx _ s0 s1 s2 =>
      congr_ifx (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tree sigma_Tm tau_Tm theta_Tm Eq_Tm s1)
        (compSubstSubst_Tree sigma_Tm tau_Tm theta_Tm Eq_Tm s2)
  | letx _ s0 s1 s2 s3 =>
      congr_letx (compSubstSubst_Tm sigma_Tm tau_Tm theta_Tm Eq_Tm s0)
        (compSubstSubst_Tm (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s1)
        (compSubstSubst_Tree sigma_Tm tau_Tm theta_Tm Eq_Tm s2)
        (option_comp (compSubstSubst_Tree sigma_Tm tau_Tm theta_Tm Eq_Tm) s3)
  | test _ s0 s1 s2 =>
      congr_test
        (compSubstSubst_Tree (up_Tm_Tm sigma_Tm) (up_Tm_Tm tau_Tm)
           (up_Tm_Tm theta_Tm) (up_subst_subst_Tm_Tm _ _ _ Eq_Tm) s0)
        (list_comp (compSubstSubst_TestBranch sigma_Tm tau_Tm theta_Tm Eq_Tm)
           s1)
        (option_comp (compSubstSubst_Tree sigma_Tm tau_Tm theta_Tm Eq_Tm) s2)
  end.

Lemma substSubst_TestBranch {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : TestBranch m_Tm) :
  subst_TestBranch tau_Tm (subst_TestBranch sigma_Tm s) =
  subst_TestBranch (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_TestBranch sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_TestBranch_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq
    (funcomp (subst_TestBranch tau_Tm) (subst_TestBranch sigma_Tm))
    (subst_TestBranch (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s =>
       compSubstSubst_TestBranch sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tree {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm)
  (s : Tree m_Tm) :
  subst_Tree tau_Tm (subst_Tree sigma_Tm s) =
  subst_Tree (funcomp (subst_Tm tau_Tm) sigma_Tm) s.
Proof.
exact (compSubstSubst_Tree sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_Tree_pointwise {k_Tm : nat} {l_Tm : nat} {m_Tm : nat}
  (sigma_Tm : fin m_Tm -> Tm k_Tm) (tau_Tm : fin k_Tm -> Tm l_Tm) :
  pointwise_relation _ eq (funcomp (subst_Tree tau_Tm) (subst_Tree sigma_Tm))
    (subst_Tree (funcomp (subst_Tm tau_Tm) sigma_Tm)).
Proof.
exact (fun s => compSubstSubst_Tree sigma_Tm tau_Tm _ (fun n => eq_refl) s).
Qed.

Lemma instId'_TestBranch {m_Tm : nat} (s : TestBranch m_Tm) :
  subst_TestBranch (var m_Tm) s = s.
Proof.
exact (idSubst_TestBranch (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_TestBranch_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_TestBranch (var m_Tm)) id.
Proof.
exact (fun s => idSubst_TestBranch (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tree {m_Tm : nat} (s : Tree m_Tm) : subst_Tree (var m_Tm) s = s.
Proof.
exact (idSubst_Tree (var m_Tm) (fun n => eq_refl) s).
Qed.

Lemma instId'_Tree_pointwise {m_Tm : nat} :
  pointwise_relation _ eq (subst_Tree (var m_Tm)) id.
Proof.
exact (fun s => idSubst_Tree (var m_Tm) (fun n => eq_refl) s).
Qed.

Class Up_Tree X Y :=
    up_Tree : X -> Y.

Class Up_TestBranch X Y :=
    up_TestBranch : X -> Y.

Class Up_CaseBranch X Y :=
    up_CaseBranch : X -> Y.

Class Up_Pat X Y :=
    up_Pat : X -> Y.

Class Up_IffiBranch X Y :=
    up_IffiBranch : X -> Y.

Class Up_GuardedExp X Y :=
    up_GuardedExp : X -> Y.

Class Up_Guards X Y :=
    up_Guards : X -> Y.

Class Up_Guard X Y :=
    up_Guard : X -> Y.

Class Up_Tm X Y :=
    up_Tm : X -> Y.

#[global]
Instance Subst_Tree  {m_Tm n_Tm : nat}: (Subst1 _ _ _) :=
 (@subst_Tree m_Tm n_Tm).

#[global]
Instance Subst_TestBranch  {m_Tm n_Tm : nat}: (Subst1 _ _ _) :=
 (@subst_TestBranch m_Tm n_Tm).

#[global]
Instance Subst_CaseBranch  {m_Tm n_Tm : nat}: (Subst1 _ _ _) :=
 (@subst_CaseBranch m_Tm n_Tm).

#[global]
Instance Subst_Pat  {m_Tm n_Tm : nat}: (Subst1 _ _ _) :=
 (@subst_Pat m_Tm n_Tm).

#[global]
Instance Subst_IffiBranch  {m_Tm n_Tm : nat}: (Subst1 _ _ _) :=
 (@subst_IffiBranch m_Tm n_Tm).

#[global]
Instance Subst_GuardedExp  {m_Tm n_Tm : nat}: (Subst1 _ _ _) :=
 (@subst_GuardedExp m_Tm n_Tm).

#[global]
Instance Subst_Guards  {m_Tm n_Tm : nat}: (Subst1 _ _ _) :=
 (@subst_Guards m_Tm n_Tm).

#[global]
Instance Subst_Guard  {m_Tm n_Tm : nat}: (Subst1 _ _ _) :=
 (@subst_Guard m_Tm n_Tm).

#[global]
Instance Subst_Tm  {m_Tm n_Tm : nat}: (Subst1 _ _ _) := (@subst_Tm m_Tm n_Tm).

#[global]
Instance Up_Tm_Tm  {m n_Tm : nat}: (Up_Tm _ _) := (@up_Tm_Tm m n_Tm).

#[global]
Instance Ren_CaseBranch  {m_Tm n_Tm : nat}: (Ren1 _ _ _) :=
 (@ren_CaseBranch m_Tm n_Tm).

#[global]
Instance Ren_Pat  {m_Tm n_Tm : nat}: (Ren1 _ _ _) := (@ren_Pat m_Tm n_Tm).

#[global]
Instance Ren_IffiBranch  {m_Tm n_Tm : nat}: (Ren1 _ _ _) :=
 (@ren_IffiBranch m_Tm n_Tm).

#[global]
Instance Ren_GuardedExp  {m_Tm n_Tm : nat}: (Ren1 _ _ _) :=
 (@ren_GuardedExp m_Tm n_Tm).

#[global]
Instance Ren_Guards  {m_Tm n_Tm : nat}: (Ren1 _ _ _) :=
 (@ren_Guards m_Tm n_Tm).

#[global]
Instance Ren_Guard  {m_Tm n_Tm : nat}: (Ren1 _ _ _) := (@ren_Guard m_Tm n_Tm).

#[global]
Instance Ren_Tm  {m_Tm n_Tm : nat}: (Ren1 _ _ _) := (@ren_Tm m_Tm n_Tm).

#[global]
Instance VarInstance_Tm  {n_Tm : nat}: (Var _ _) := (@var n_Tm).

Notation "s [ sigma_Tm ]" := (subst_Tree sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Tree" := up_Tree (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_TestBranch sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__TestBranch" := up_TestBranch (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_CaseBranch sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__CaseBranch" := up_CaseBranch (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_Pat sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Pat" := up_Pat (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_IffiBranch sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__IffiBranch" := up_IffiBranch (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_GuardedExp sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__GuardedExp" := up_GuardedExp (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_Guards sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Guards" := up_Guards (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_Guard sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Guard" := up_Guard (only printing)  : subst_scope.

Notation "s [ sigma_Tm ]" := (subst_Tm sigma_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm (only printing)  : subst_scope.

Notation "↑__Tm" := up_Tm_Tm (only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_CaseBranch xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Pat xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_IffiBranch xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_GuardedExp xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Guards xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Guard xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "s ⟨ xi_Tm ⟩" := (ren_Tm xi_Tm s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var ( at level 1, only printing)  : subst_scope.

Notation "x '__Tm'" := (@ids _ _ VarInstance_Tm x)
( at level 5, format "x __Tm", only printing)  : subst_scope.

Notation "x '__Tm'" := (var x) ( at level 5, format "x __Tm")  : subst_scope.

#[global]
Instance subst_Tree_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Tree m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Tree f_Tm s = subst_Tree g_Tm t')
         (ext_Tree f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Tree_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Tree m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Tree f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_TestBranch_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_TestBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s
         (fun t' => subst_TestBranch f_Tm s = subst_TestBranch g_Tm t')
         (ext_TestBranch f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_TestBranch_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_TestBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_TestBranch f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_CaseBranch_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_CaseBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s
         (fun t' => subst_CaseBranch f_Tm s = subst_CaseBranch g_Tm t')
         (ext_CaseBranch f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_CaseBranch_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_CaseBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_CaseBranch f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_Pat_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Pat m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Pat f_Tm s = subst_Pat g_Tm t')
         (ext_Pat f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Pat_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Pat m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Pat f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_IffiBranch_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_IffiBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s
         (fun t' => subst_IffiBranch f_Tm s = subst_IffiBranch g_Tm t')
         (ext_IffiBranch f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_IffiBranch_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_IffiBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_IffiBranch f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_GuardedExp_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_GuardedExp m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s
         (fun t' => subst_GuardedExp f_Tm s = subst_GuardedExp g_Tm t')
         (ext_GuardedExp f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_GuardedExp_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_GuardedExp m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_GuardedExp f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_Guards_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Guards m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Guards f_Tm s = subst_Guards g_Tm t')
         (ext_Guards f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Guards_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Guards m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Guards f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_Guard_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Guard m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Guard f_Tm s = subst_Guard g_Tm t')
         (ext_Guard f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Guard_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Guard m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Guard f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance subst_Tm_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_Tm m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => subst_Tm f_Tm s = subst_Tm g_Tm t')
         (ext_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance subst_Tm_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_Tm m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => ext_Tm f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_CaseBranch_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_CaseBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_CaseBranch f_Tm s = ren_CaseBranch g_Tm t')
         (extRen_CaseBranch f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_CaseBranch_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_CaseBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_CaseBranch f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Pat_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Pat m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Pat f_Tm s = ren_Pat g_Tm t')
         (extRen_Pat f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Pat_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Pat m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Pat f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_IffiBranch_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_IffiBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_IffiBranch f_Tm s = ren_IffiBranch g_Tm t')
         (extRen_IffiBranch f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_IffiBranch_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_IffiBranch m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_IffiBranch f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_GuardedExp_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_GuardedExp m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_GuardedExp f_Tm s = ren_GuardedExp g_Tm t')
         (extRen_GuardedExp f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_GuardedExp_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_GuardedExp m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_GuardedExp f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Guards_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Guards m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Guards f_Tm s = ren_Guards g_Tm t')
         (extRen_Guards f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Guards_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Guards m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Guards f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Guard_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Guard m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Guard f_Tm s = ren_Guard g_Tm t')
         (extRen_Guard f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Guard_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Guard m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Guard f_Tm g_Tm Eq_Tm s).
Qed.

#[global]
Instance ren_Tm_morphism  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_Tm m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s t Eq_st =>
       eq_ind s (fun t' => ren_Tm f_Tm s = ren_Tm g_Tm t')
         (extRen_Tm f_Tm g_Tm Eq_Tm s) t Eq_st).
Qed.

#[global]
Instance ren_Tm_morphism2  {m_Tm : nat} {n_Tm : nat}:
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_Tm m_Tm n_Tm)).
Proof.
exact (fun f_Tm g_Tm Eq_Tm s => extRen_Tm f_Tm g_Tm Eq_Tm s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_Tm, Var, ids, Ren_Tm, Ren1, ren1,
                      Ren_Guard, Ren1, ren1, Ren_Guards, Ren1, ren1,
                      Ren_GuardedExp, Ren1, ren1, Ren_IffiBranch, Ren1, ren1,
                      Ren_Pat, Ren1, ren1, Ren_CaseBranch, Ren1, ren1,
                      Up_Tm_Tm, Up_Tm, up_Tm, Subst_Tm, Subst1, subst1,
                      Subst_Guard, Subst1, subst1, Subst_Guards, Subst1,
                      subst1, Subst_GuardedExp, Subst1, subst1,
                      Subst_IffiBranch, Subst1, subst1, Subst_Pat, Subst1,
                      subst1, Subst_CaseBranch, Subst1, subst1,
                      Subst_TestBranch, Subst1, subst1, Subst_Tree, Subst1,
                      subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_Tm, Var, ids,
                                            Ren_Tm, Ren1, ren1, Ren_Guard,
                                            Ren1, ren1, Ren_Guards, Ren1,
                                            ren1, Ren_GuardedExp, Ren1, ren1,
                                            Ren_IffiBranch, Ren1, ren1,
                                            Ren_Pat, Ren1, ren1,
                                            Ren_CaseBranch, Ren1, ren1,
                                            Up_Tm_Tm, Up_Tm, up_Tm, Subst_Tm,
                                            Subst1, subst1, Subst_Guard,
                                            Subst1, subst1, Subst_Guards,
                                            Subst1, subst1, Subst_GuardedExp,
                                            Subst1, subst1, Subst_IffiBranch,
                                            Subst1, subst1, Subst_Pat,
                                            Subst1, subst1, Subst_CaseBranch,
                                            Subst1, subst1, Subst_TestBranch,
                                            Subst1, subst1, Subst_Tree,
                                            Subst1, subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_Tree_pointwise
                 | progress setoid_rewrite substSubst_Tree
                 | progress setoid_rewrite substSubst_TestBranch_pointwise
                 | progress setoid_rewrite substSubst_TestBranch
                 | progress setoid_rewrite substSubst_CaseBranch_pointwise
                 | progress setoid_rewrite substSubst_CaseBranch
                 | progress setoid_rewrite substSubst_Pat_pointwise
                 | progress setoid_rewrite substSubst_Pat
                 | progress setoid_rewrite substSubst_IffiBranch_pointwise
                 | progress setoid_rewrite substSubst_IffiBranch
                 | progress setoid_rewrite substSubst_GuardedExp_pointwise
                 | progress setoid_rewrite substSubst_GuardedExp
                 | progress setoid_rewrite substSubst_Guards_pointwise
                 | progress setoid_rewrite substSubst_Guards
                 | progress setoid_rewrite substSubst_Guard_pointwise
                 | progress setoid_rewrite substSubst_Guard
                 | progress setoid_rewrite substSubst_Tm_pointwise
                 | progress setoid_rewrite substSubst_Tm
                 | progress setoid_rewrite substRen_CaseBranch_pointwise
                 | progress setoid_rewrite substRen_CaseBranch
                 | progress setoid_rewrite substRen_Pat_pointwise
                 | progress setoid_rewrite substRen_Pat
                 | progress setoid_rewrite substRen_IffiBranch_pointwise
                 | progress setoid_rewrite substRen_IffiBranch
                 | progress setoid_rewrite substRen_GuardedExp_pointwise
                 | progress setoid_rewrite substRen_GuardedExp
                 | progress setoid_rewrite substRen_Guards_pointwise
                 | progress setoid_rewrite substRen_Guards
                 | progress setoid_rewrite substRen_Guard_pointwise
                 | progress setoid_rewrite substRen_Guard
                 | progress setoid_rewrite substRen_Tm_pointwise
                 | progress setoid_rewrite substRen_Tm
                 | progress setoid_rewrite renSubst_CaseBranch_pointwise
                 | progress setoid_rewrite renSubst_CaseBranch
                 | progress setoid_rewrite renSubst_Pat_pointwise
                 | progress setoid_rewrite renSubst_Pat
                 | progress setoid_rewrite renSubst_IffiBranch_pointwise
                 | progress setoid_rewrite renSubst_IffiBranch
                 | progress setoid_rewrite renSubst_GuardedExp_pointwise
                 | progress setoid_rewrite renSubst_GuardedExp
                 | progress setoid_rewrite renSubst_Guards_pointwise
                 | progress setoid_rewrite renSubst_Guards
                 | progress setoid_rewrite renSubst_Guard_pointwise
                 | progress setoid_rewrite renSubst_Guard
                 | progress setoid_rewrite renSubst_Tm_pointwise
                 | progress setoid_rewrite renSubst_Tm
                 | progress setoid_rewrite renRen'_CaseBranch_pointwise
                 | progress setoid_rewrite renRen_CaseBranch
                 | progress setoid_rewrite renRen'_Pat_pointwise
                 | progress setoid_rewrite renRen_Pat
                 | progress setoid_rewrite renRen'_IffiBranch_pointwise
                 | progress setoid_rewrite renRen_IffiBranch
                 | progress setoid_rewrite renRen'_GuardedExp_pointwise
                 | progress setoid_rewrite renRen_GuardedExp
                 | progress setoid_rewrite renRen'_Guards_pointwise
                 | progress setoid_rewrite renRen_Guards
                 | progress setoid_rewrite renRen'_Guard_pointwise
                 | progress setoid_rewrite renRen_Guard
                 | progress setoid_rewrite renRen'_Tm_pointwise
                 | progress setoid_rewrite renRen_Tm
                 | progress setoid_rewrite instId'_Tree_pointwise
                 | progress setoid_rewrite instId'_Tree
                 | progress setoid_rewrite instId'_TestBranch_pointwise
                 | progress setoid_rewrite instId'_TestBranch
                 | progress setoid_rewrite varLRen'_Tm_pointwise
                 | progress setoid_rewrite varLRen'_Tm
                 | progress setoid_rewrite varL'_Tm_pointwise
                 | progress setoid_rewrite varL'_Tm
                 | progress setoid_rewrite rinstId'_CaseBranch_pointwise
                 | progress setoid_rewrite rinstId'_CaseBranch
                 | progress setoid_rewrite rinstId'_Pat_pointwise
                 | progress setoid_rewrite rinstId'_Pat
                 | progress setoid_rewrite rinstId'_IffiBranch_pointwise
                 | progress setoid_rewrite rinstId'_IffiBranch
                 | progress setoid_rewrite rinstId'_GuardedExp_pointwise
                 | progress setoid_rewrite rinstId'_GuardedExp
                 | progress setoid_rewrite rinstId'_Guards_pointwise
                 | progress setoid_rewrite rinstId'_Guards
                 | progress setoid_rewrite rinstId'_Guard_pointwise
                 | progress setoid_rewrite rinstId'_Guard
                 | progress setoid_rewrite rinstId'_Tm_pointwise
                 | progress setoid_rewrite rinstId'_Tm
                 | progress setoid_rewrite instId'_CaseBranch_pointwise
                 | progress setoid_rewrite instId'_CaseBranch
                 | progress setoid_rewrite instId'_Pat_pointwise
                 | progress setoid_rewrite instId'_Pat
                 | progress setoid_rewrite instId'_IffiBranch_pointwise
                 | progress setoid_rewrite instId'_IffiBranch
                 | progress setoid_rewrite instId'_GuardedExp_pointwise
                 | progress setoid_rewrite instId'_GuardedExp
                 | progress setoid_rewrite instId'_Guards_pointwise
                 | progress setoid_rewrite instId'_Guards
                 | progress setoid_rewrite instId'_Guard_pointwise
                 | progress setoid_rewrite instId'_Guard
                 | progress setoid_rewrite instId'_Tm_pointwise
                 | progress setoid_rewrite instId'_Tm
                 | progress
                    unfold up_list_Tm_Tm, up_Tm_Tm, upRen_list_Tm_Tm,
                     upRen_Tm_Tm, up_ren
                 | progress
                    cbn[subst_Tree subst_TestBranch subst_CaseBranch
                       subst_Pat subst_IffiBranch subst_GuardedExp
                       subst_Guards subst_Guard subst_Tm ren_CaseBranch
                       ren_Pat ren_IffiBranch ren_GuardedExp ren_Guards
                       ren_Guard ren_Tm]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_Tm, Var, ids, Ren_Tm, Ren1, ren1,
                  Ren_Guard, Ren1, ren1, Ren_Guards, Ren1, ren1,
                  Ren_GuardedExp, Ren1, ren1, Ren_IffiBranch, Ren1, ren1,
                  Ren_Pat, Ren1, ren1, Ren_CaseBranch, Ren1, ren1, Up_Tm_Tm,
                  Up_Tm, up_Tm, Subst_Tm, Subst1, subst1, Subst_Guard,
                  Subst1, subst1, Subst_Guards, Subst1, subst1,
                  Subst_GuardedExp, Subst1, subst1, Subst_IffiBranch, Subst1,
                  subst1, Subst_Pat, Subst1, subst1, Subst_CaseBranch,
                  Subst1, subst1, Subst_TestBranch, Subst1, subst1,
                  Subst_Tree, Subst1, subst1 in *;
                asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold;
                  try setoid_rewrite rinstInst'_CaseBranch_pointwise;
                  try setoid_rewrite rinstInst'_CaseBranch;
                  try setoid_rewrite rinstInst'_Pat_pointwise;
                  try setoid_rewrite rinstInst'_Pat;
                  try setoid_rewrite rinstInst'_IffiBranch_pointwise;
                  try setoid_rewrite rinstInst'_IffiBranch;
                  try setoid_rewrite rinstInst'_GuardedExp_pointwise;
                  try setoid_rewrite rinstInst'_GuardedExp;
                  try setoid_rewrite rinstInst'_Guards_pointwise;
                  try setoid_rewrite rinstInst'_Guards;
                  try setoid_rewrite rinstInst'_Guard_pointwise;
                  try setoid_rewrite rinstInst'_Guard;
                  try setoid_rewrite rinstInst'_Tm_pointwise;
                  try setoid_rewrite rinstInst'_Tm.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_CaseBranch_pointwise;
                  try setoid_rewrite_left rinstInst'_CaseBranch;
                  try setoid_rewrite_left rinstInst'_Pat_pointwise;
                  try setoid_rewrite_left rinstInst'_Pat;
                  try setoid_rewrite_left rinstInst'_IffiBranch_pointwise;
                  try setoid_rewrite_left rinstInst'_IffiBranch;
                  try setoid_rewrite_left rinstInst'_GuardedExp_pointwise;
                  try setoid_rewrite_left rinstInst'_GuardedExp;
                  try setoid_rewrite_left rinstInst'_Guards_pointwise;
                  try setoid_rewrite_left rinstInst'_Guards;
                  try setoid_rewrite_left rinstInst'_Guard_pointwise;
                  try setoid_rewrite_left rinstInst'_Guard;
                  try setoid_rewrite_left rinstInst'_Tm_pointwise;
                  try setoid_rewrite_left rinstInst'_Tm.

End Core.

Module Extra.

Import
Core.

Arguments test {n_Tm}.

Arguments letx {n_Tm}.

Arguments ifx {n_Tm}.

Arguments match {n_Tm}.

Arguments tfail {n_Tm}.

Arguments testbranch {n_Tm}.

Arguments casebranch {n_Tm}.

Arguments pwhen {n_Tm}.

Arguments pguard {n_Tm}.

Arguments por {n_Tm}.

Arguments pvconapp {n_Tm}.

Arguments pname {n_Tm}.

Arguments iffibranch {n_Tm}.

Arguments guardedexp {n_Tm}.

Arguments guards {n_Tm}.

Arguments choice {n_Tm}.

Arguments eqn {n_Tm}.

Arguments comp {n_Tm}.

Arguments var {n_Tm}.

Arguments case {n_Tm}.

Arguments iffi {n_Tm}.

Arguments vconapp {n_Tm}.

Arguments ret {n_Tm}.

#[global] Hint Opaque subst_Tree: rewrite.

#[global] Hint Opaque subst_TestBranch: rewrite.

#[global] Hint Opaque subst_CaseBranch: rewrite.

#[global] Hint Opaque subst_Pat: rewrite.

#[global] Hint Opaque subst_IffiBranch: rewrite.

#[global] Hint Opaque subst_GuardedExp: rewrite.

#[global] Hint Opaque subst_Guards: rewrite.

#[global] Hint Opaque subst_Guard: rewrite.

#[global] Hint Opaque subst_Tm: rewrite.

#[global] Hint Opaque ren_CaseBranch: rewrite.

#[global] Hint Opaque ren_Pat: rewrite.

#[global] Hint Opaque ren_IffiBranch: rewrite.

#[global] Hint Opaque ren_GuardedExp: rewrite.

#[global] Hint Opaque ren_Guards: rewrite.

#[global] Hint Opaque ren_Guard: rewrite.

#[global] Hint Opaque ren_Tm: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

