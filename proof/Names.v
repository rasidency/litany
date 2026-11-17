From Stdlib Require Import Lists.List Strings.Ascii.
Require Import Core.
Import ListNotations.

Definition identifier := list ascii.

Fixpoint lookup (x : identifier) (env : list identifier) : option nat :=
  match env with
  | [] => None
  | y :: rest =>
      if list_eq_dec ascii_dec x y then Some 0 else option_map S (lookup x rest)
  end.

Inductive binding (x : identifier) : list identifier -> nat -> Prop :=
| Nearest env : binding x (x :: env) 0
| Outer y env n : x <> y -> binding x env n -> binding x (y :: env) (S n).

Lemma lookup_sound x env n : lookup x env = Some n -> binding x env n.
Proof.
  revert n.
  induction env as [|y env IH]; intros n H; cbn in H; [discriminate|].
  destruct (list_eq_dec ascii_dec x y) as [->|Hxy].
  - injection H as <-. constructor.
  - destruct (lookup x env) as [m|] eqn:E; [|discriminate].
    injection H as <-. constructor; auto.
Qed.

Lemma lookup_complete x env n : binding x env n -> lookup x env = Some n.
Proof.
  induction 1 as [env | y env n Hxy H IH]; cbn.
  - destruct (list_eq_dec ascii_dec x x); congruence.
  - destruct (list_eq_dec ascii_dec x y); [contradiction|now rewrite IH].
Qed.

Inductive named (location : Type) :=
| NamedLit (z : BinNums.Z) | NamedInt | NamedFail
| NamedVar (pos : location) (x : identifier)
| NamedRange (f : named location)
| NamedApply (f x : named location)
| NamedChoice (l r : named location)
| NamedLambda (x : identifier) (d b : named location).

Arguments NamedLit {location}.
Arguments NamedInt {location}.
Arguments NamedFail {location}.
Arguments NamedVar {location}.
Arguments NamedRange {location}.
Arguments NamedApply {location}.
Arguments NamedChoice {location}.
Arguments NamedLambda {location}.

Inductive resolution (location : Type) :=
| Resolved (e : term)
| Unbound (pos : location) (x : identifier).

Arguments Resolved {location}.
Arguments Unbound {location}.

Definition bind {L} (m : resolution L) (k : term -> resolution L) :=
  match m with Resolved e => k e | Unbound pos x => Unbound pos x end.

Fixpoint resolve {L} env (e : named L) : resolution L :=
  match e with
  | NamedLit z => Resolved (Lit z)
  | NamedInt => Resolved Int
  | NamedFail => Resolved Fail
  | NamedVar pos x =>
      match lookup x env with
      | Some n => Resolved (Var n)
      | None => Unbound pos x
      end
  | NamedRange f => bind (resolve env f) (fun f => Resolved (Range f))
  | NamedApply f x =>
      bind (resolve env f) (fun f =>
      bind (resolve env x) (fun x => Resolved (Apply f x)))
  | NamedChoice l r =>
      bind (resolve env l) (fun l =>
      bind (resolve env r) (fun r => Resolved (Choice l r)))
  | NamedLambda x d b =>
      bind (resolve env d) (fun d =>
      bind (resolve (x :: env) b) (fun b => Resolved (Lambda d b)))
  end.

Inductive resolves {L} : list identifier -> named L -> term -> Prop :=
| ResolvesLit env z : resolves env (NamedLit z) (Lit z)
| ResolvesInt env : resolves env NamedInt Int
| ResolvesFail env : resolves env NamedFail Fail
| ResolvesVar env pos x n : binding x env n -> resolves env (NamedVar pos x) (Var n)
| ResolvesRange env f F : resolves env f F -> resolves env (NamedRange f) (Range F)
| ResolvesApply env f x F X :
    resolves env f F -> resolves env x X -> resolves env (NamedApply f x) (Apply F X)
| ResolvesChoice env l r A B :
    resolves env l A -> resolves env r B -> resolves env (NamedChoice l r) (Choice A B)
| ResolvesLambda env x d b D B :
    resolves env d D -> resolves (x :: env) b B ->
    resolves env (NamedLambda x d b) (Lambda D B).

Theorem resolve_sound L (e : named L) env t :
  resolve env e = Resolved t -> resolves env e t.
Proof.
  revert env t. induction e; intros env t H; cbn in H.
  - injection H as <-. constructor.
  - injection H as <-. constructor.
  - injection H as <-. constructor.
  - destruct (lookup x env) eqn:E; [|discriminate].
    injection H as <-. constructor. now apply lookup_sound.
  - destruct (resolve env e) eqn:E; [|discriminate].
    injection H as <-. constructor. now apply IHe.
  - destruct (resolve env e1) eqn:E1; [|discriminate].
    destruct (resolve env e2) eqn:E2; [|discriminate].
    injection H as <-. constructor; auto.
  - destruct (resolve env e1) eqn:E1; [|discriminate].
    destruct (resolve env e2) eqn:E2; [|discriminate].
    injection H as <-. constructor; auto.
  - destruct (resolve env e1) eqn:E1; [|discriminate].
    destruct (resolve (x :: env) e2) eqn:E2; [|discriminate].
    injection H as <-. constructor; auto.
Qed.

Theorem resolve_complete L (e : named L) env t :
  resolves env e t -> resolve env e = Resolved t.
Proof.
  induction 1; cbn; auto;
    now rewrite ?IHresolves, ?IHresolves1, ?IHresolves2, ?(lookup_complete x env n).
Qed.
