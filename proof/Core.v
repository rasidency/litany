From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith micromega.Lia.
From Corelib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import Numbers.DecimalString extraction.ExtrOcamlString.
Import ListNotations.

Inductive term :=
| Lit (z : Z) | Int | Var (index : nat) | Fail
| Range (graph : term) | Apply (graph arg : term)
| Choice (left right : term) | Lambda (domain body : term).

Inductive block :=
| Yield (value : nat)
| Constant (z : Z) (rest : block)
| Identity (rest : block)
| Empty (rest : block)
| Project (graph : nat) (rest : block)
| Call (graph arg : nat) (rest : block)
| Union (left right : nat) (rest : block)
| Abstract (domain : nat) (body rest : block).

Fixpoint lower (e : term) (names : list nat) (next : nat)
    (k : nat -> nat -> block) : block :=
  match e with
  | Lit z => Constant z (k next (S next))
  | Int => Identity (k next (S next))
  | Fail => Empty (k next (S next))
  | Var i => match nth_error names i with
             | Some ref => k ref next
             | None => Empty (k next (S next))
             end
  | Range f => lower f names next (fun ref n => Project ref (k n (S n)))
  | Apply f x =>
      lower f names next (fun rf n =>
      lower x names n (fun rx m => Call rf rx (k m (S m))))
  | Choice l r =>
      lower l names next (fun rl n =>
      lower r names n (fun rr m => Union rl rr (k m (S m))))
  | Lambda d b =>
      lower d names next (fun rd n =>
      Abstract rd (lower b (n :: names) (S n) (fun r _ => Yield r))
                  (k n (S n)))
  end.

Definition compile e := lower e [] 0 (fun r _ => Yield r).

Fixpoint scoped next code : Prop :=
  match code with
  | Yield r => r < next
  | Constant _ rest | Identity rest | Empty rest => scoped (S next) rest
  | Project f rest => f < next /\ scoped (S next) rest
  | Call f x rest | Union f x rest => f < next /\ x < next /\ scoped (S next) rest
  | Abstract d body rest => d < next /\ scoped (S next) body /\ scoped (S next) rest
  end.

Lemma bounded_later names n m :
  Forall (fun r => r < n) names -> n <= m -> Forall (fun r => r < m) names.
Proof. intros H E. induction H; constructor; auto; lia. Qed.

Lemma lower_scoped e names next k :
  Forall (fun r => r < next) names ->
  (forall r n, next <= n -> r < n -> scoped n (k r n)) ->
  scoped next (lower e names next k).
Proof.
  revert names next k.
  induction e; intros names next k Hnames Hk; cbn [lower scoped].
  - apply Hk; lia.
  - apply Hk; lia.
  - destruct (nth_error names index) eqn:E; cbn [scoped].
    + apply Hk; [lia|]. rewrite Forall_forall in Hnames. apply Hnames.
      exact (nth_error_In names index E).
    + apply Hk; lia.
  - apply Hk; lia.
  - apply IHe; [exact Hnames|].
    intros r n Hn Hr. cbn [scoped]. split; [exact Hr|apply Hk; lia].
  - apply IHe1; [exact Hnames|].
    intros rf n Hn Hf. apply IHe2; [exact (bounded_later names next n Hnames Hn)|].
    intros rx m Hm Hx. cbn [scoped]. split; [lia|].
    split; [exact Hx|apply Hk; lia].
  - apply IHe1; [exact Hnames|].
    intros rl n Hn Hl. apply IHe2; [exact (bounded_later names next n Hnames Hn)|].
    intros rr m Hm Hr. cbn [scoped]. split; [lia|].
    split; [exact Hr|apply Hk; lia].
  - apply IHe1; [exact Hnames|].
    intros rd n Hn Hd. cbn [scoped]. split; [exact Hd|].
    split; [|apply Hk; lia].
    apply IHe2.
    + constructor; [lia|eapply bounded_later; [exact Hnames|lia]].
    + intros r m _ Hr. exact Hr.
Qed.

Theorem compile_scoped e : scoped 0 (compile e).
Proof. unfold compile. apply lower_scoped; [constructor|]. auto. Qed.

Section Denotation.
Context {value : Type}.
Variable integer : Z -> value.
Variable edge : value -> value -> value -> Prop.
Variable graph : value -> Prop.
Variable int : value.

Definition members := value -> Prop.
Definition none : members := fun _ => False.
Definition one (a : value) : members := fun b => a = b.
Definition join (A B : members) : members := fun v => A v \/ B v.
Definition range (F : members) : members :=
  fun b => exists f a, F f /\ edge f a b.
Definition apply (F A : members) : members :=
  fun b => exists f a, F f /\ A a /\ edge f a b.
Definition pi (A : members) (B : value -> members) : members :=
  fun f => graph f /\
    (forall a b c, edge f a b -> edge f a c -> b = c) /\
    (forall a, A a -> exists b, edge f a b) /\
    (forall a b, edge f a b -> A a /\ B a b).

Fixpoint denote (e : term) (env : list members) : members :=
  match e with
  | Lit z => one (integer z)
  | Int => one int
  | Var i => nth i env none
  | Fail => none
  | Range f => range (denote f env)
  | Apply f x => apply (denote f env) (denote x env)
  | Choice l r => join (denote l env) (denote r env)
  | Lambda d b => pi (denote d env) (fun a => denote b (one a :: env))
  end.

Fixpoint eval (code : block) (env : list members) : members :=
  let get i := nth i env none in
  let push A := env ++ [A] in
  match code with
  | Yield i => get i
  | Constant z rest => eval rest (push (one (integer z)))
  | Identity rest => eval rest (push (one int))
  | Empty rest => eval rest (push none)
  | Project f rest => eval rest (push (range (get f)))
  | Call f x rest => eval rest (push (apply (get f) (get x)))
  | Union l r rest => eval rest (push (join (get l) (get r)))
  | Abstract d body rest =>
      eval rest (push (pi (get d) (fun a => eval body (push (one a)))))
  end.

Definition equiv (A B : members) := forall v, A v <-> B v.
Definition holds ir i A :=
  exists B, nth_error ir i = Some B /\ equiv B A.
Definition agrees names src ir := Forall2 (holds ir) names src.

Lemma holds_append ir extra i A : holds ir i A -> holds (ir ++ extra) i A.
Proof.
  intros (B & HB & HE). exists B. split; [|exact HE].
  rewrite nth_error_app1; [exact HB|apply nth_error_Some; now rewrite HB].
Qed.

Lemma agrees_append names src ir extra :
  agrees names src ir -> agrees names src (ir ++ extra).
Proof. induction 1; constructor; auto using holds_append. Qed.

Lemma get_holds ir i A : holds ir i A -> equiv (nth i ir none) A.
Proof. intros (B & H & E). now erewrite nth_error_nth by exact H. Qed.

Lemma fresh ir A B : equiv A B -> holds (ir ++ [A]) (length ir) B.
Proof.
  intros H. exists A. split; [|exact H].
  rewrite nth_error_app2 by lia. now rewrite Nat.sub_diag.
Qed.

Lemma finish ir extra k A B out :
  equiv A B ->
  (forall suffix r, holds (ir ++ suffix) r B ->
     equiv (eval (k r (length (ir ++ suffix))) (ir ++ suffix)) out) ->
  equiv (eval (k (length (ir ++ extra)) (S (length (ir ++ extra))))
              ((ir ++ extra) ++ [A])) out.
Proof.
  intros E H.
  replace (S (length (ir ++ extra))) with (length ((ir ++ extra) ++ [A]))
    by (rewrite length_app; cbn; lia).
  rewrite <- app_assoc. apply H.
  rewrite app_assoc. now apply fresh.
Qed.

Lemma finish_here ir k A B out :
  equiv A B ->
  (forall suffix r, holds (ir ++ suffix) r B ->
     equiv (eval (k r (length (ir ++ suffix))) (ir ++ suffix)) out) ->
  equiv (eval (k (length ir) (S (length ir))) (ir ++ [A])) out.
Proof. intros E H. pose proof (finish ir [] k A B out E H) as F.
  now rewrite app_nil_r in F.
Qed.

Lemma lower_correct e names src ir k out :
  agrees names src ir ->
  (forall extra r, holds (ir ++ extra) r (denote e src) ->
     equiv (eval (k r (length (ir ++ extra))) (ir ++ extra)) out) ->
  equiv (eval (lower e names (length ir) k) ir) out.
Proof.
  revert names src ir k out.
  induction e; intros names src ir k out Henv Hk; cbn [lower denote].
  - cbn [eval]. eapply (finish_here ir k _ _ out); [|exact Hk]. firstorder.
  - cbn [eval]. eapply (finish_here ir k _ _ out); [|exact Hk]. firstorder.
  - revert index Hk. induction Henv; intros [|i] Hk;
      cbn [lower nth_error nth eval] in *.
    all: try (eapply (finish_here ir k _ _ out); [|exact Hk]; firstorder).
    + specialize (Hk [] x). rewrite app_nil_r in Hk. now apply Hk.
    + now apply IHHenv.
  - cbn [eval]. eapply (finish_here ir k _ _ out); [|exact Hk]. firstorder.
  - eapply (IHe names src ir _ out); [exact Henv|].
    intros extra r Hr. cbn [eval].
    apply get_holds in Hr.
    eapply (finish ir extra k _ _ out); [|exact Hk]. unfold equiv, range in *. firstorder.
  - eapply (IHe1 names src ir _ out); [exact Henv|].
    intros extra rf Hf. eapply (IHe2 names src (ir ++ extra) _ out); [now apply agrees_append|].
    intros more rx Hx. cbn [eval].
    pose proof (get_holds _ _ _ (holds_append _ more _ _ Hf)) as Ef.
    apply get_holds in Hx.
    eapply (finish (ir ++ extra) more k _ (apply (denote e1 src) (denote e2 src)) out).
    + unfold equiv, apply in *. firstorder.
    + intros suffix r Hr. rewrite <- app_assoc in Hr |- *. now apply Hk.
  - eapply (IHe1 names src ir _ out); [exact Henv|].
    intros extra rl Hl. eapply (IHe2 names src (ir ++ extra) _ out); [now apply agrees_append|].
    intros more rr Hr. cbn [eval].
    pose proof (get_holds _ _ _ (holds_append _ more _ _ Hl)) as El.
    apply get_holds in Hr.
    eapply (finish (ir ++ extra) more k _ (join (denote e1 src) (denote e2 src)) out).
    + unfold equiv, join in *. firstorder.
    + intros suffix r Hresult. rewrite <- app_assoc in Hresult |- *. now apply Hk.
  - eapply (IHe1 names src ir _ out); [exact Henv|].
    intros extra rd Hd. cbn [eval].
    pose proof (get_holds _ _ _ Hd) as Ed.
    assert (Hbody : forall a,
       equiv (eval (lower e2 (length (ir ++ extra) :: names) (S (length (ir ++ extra)))
          (fun r _ => Yield r)) ((ir ++ extra) ++ [one a]))
       (denote e2 (one a :: src))).
    { intros a. replace (S (length (ir ++ extra))) with
        (length ((ir ++ extra) ++ [one a])) by (rewrite length_app; cbn; lia).
      eapply (IHe2 (_ :: names) (one a :: src) ((ir ++ extra) ++ [one a]) _ _).
      - constructor.
        + apply fresh. firstorder.
        + now repeat apply agrees_append.
      - intros suffix r Hr. cbn [eval]. now apply get_holds in Hr. }
    eapply (finish ir extra k _ _ out); [|exact Hk].
    intros f. unfold pi. split.
    + intros (Hgraph & Hfun & Hdom & Hbody').
      split; [exact Hgraph|]. split; [exact Hfun|]. split.
      * intros a Ha. apply Hdom. now apply Ed.
      * intros a b Hab. destruct (Hbody' a b Hab) as [Ha Hb].
        split; [now apply Ed|now apply Hbody].
    + intros (Hgraph & Hfun & Hdom & Hbody').
      split; [exact Hgraph|]. split; [exact Hfun|]. split.
      * intros a Ha. apply Hdom. now apply Ed.
      * intros a b Hab. destruct (Hbody' a b Hab) as [Ha Hb].
        split; [now apply Ed|now apply Hbody].
Qed.

Theorem compile_correct e : forall v, eval (compile e) [] v <-> denote e [] v.
Proof.
  change (equiv (eval (compile e) []) (denote e [])).
  unfold compile. eapply (lower_correct e [] [] [] _ (denote e [])); [constructor|].
  intros extra r Hr. cbn [eval]. now apply get_holds in Hr.
Qed.
End Denotation.

Print Assumptions compile_correct.
Print Assumptions compile_scoped.

Definition parse_integer s := option_map Z.of_int (NilZero.int_of_string s).
Definition print_integer z := NilZero.string_of_int (Z.to_int z).


From Stdlib Require Import Numbers.DecimalZ Numbers.DecimalPos ZArith.Zpow_facts.

Theorem integer_text_roundtrip z : parse_integer (print_integer z) = Some z.
Proof.
  unfold parse_integer, print_integer.
  rewrite NilZero.isi.
  - cbn [option_map]. now rewrite DecimalZ.of_to.
  - destruct z; cbn [Z.to_int]; try discriminate.
    intros H. injection H as H. exact (DecimalPos.Unsigned.to_uint_nonnil _ H).
  - destruct z; cbn [Z.to_int]; try discriminate.
    intros H. injection H as H. exact (DecimalPos.Unsigned.to_uint_nonnil _ H).
Qed.

Definition integer_width z :=
  match z with
  | Z0 => 1%nat
  | Zpos p | Zneg p => S (Pos.size_nat p)
  end.

Theorem integer_width_fits z :
  let limit := (2 ^ Z.of_nat (Nat.pred (integer_width z)))%Z in
  (- limit <= z < limit)%Z.
Proof.
  destruct z as [|p|p]; cbn [integer_width Nat.pred].
  - cbn. lia.
  - pose proof (proj2 (Zpower2_Psize (Pos.size_nat p) p) (Nat.le_refl _)). lia.
  - pose proof (proj2 (Zpower2_Psize (Pos.size_nat p) p) (Nat.le_refl _)). lia.
Qed.

Print Assumptions integer_text_roundtrip.
Print Assumptions integer_width_fits.
