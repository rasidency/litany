From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith Bool.Bool micromega.Lia
  Relations.Relation_Operators.
Require Import Core Names Target.
Import ListNotations.

Definition bit i := S i - 2 * Nat.div2 (S i).
Definition key i := Nat.div2 (S i) - 1.

Lemma decompose i : 0 < i -> i = 2 * key i + 1 + bit i /\ bit i <= 1.
Proof.
  intros H. unfold key, bit.
  pose proof (Nat.div2_odd (S i)) as E.
  destruct (Nat.odd (S i)); cbn [Nat.b2n] in E; lia.
Qed.

Inductive trie (A : Type) := Tip | Bin (stem : option A) (evens odds : trie A).
Arguments Tip {A}.
Arguments Bin {A}.

Fixpoint find {A} (t : trie A) (i : nat) : option A :=
  match t with
  | Tip => None
  | Bin h z o =>
      match i with
      | 0 => h
      | S _ => if Nat.eqb (bit i) 0 then find z (key i) else find o (key i)
      end
  end.

Definition stem {A} (t : trie A) := match t with Tip => None | Bin h _ _ => h end.
Definition evens {A} (t : trie A) := match t with Tip => Tip | Bin _ z _ => z end.
Definition odds {A} (t : trie A) := match t with Tip => Tip | Bin _ _ o => o end.

Fixpoint put {A} (fuel : nat) (t : trie A) (i : nat) (x : A) : trie A :=
  match i, fuel with
  | 0, _ => Bin (Some x) (evens t) (odds t)
  | S _, 0 => t
  | S _, S f =>
      if Nat.eqb (bit i) 0 then Bin (stem t) (put f (evens t) (key i) x) (odds t)
      else Bin (stem t) (evens t) (put f (odds t) (key i) x)
  end.

Lemma find_split {A} (t : trie A) i :
  find t i = match i with
             | 0 => stem t
             | S _ => if Nat.eqb (bit i) 0 then find (evens t) (key i) else find (odds t) (key i)
             end.
Proof.
  destruct t as [|h z o], i as [|i]; cbn [find stem evens odds]; try reflexivity.
  destruct (Nat.eqb (bit (S i)) 0); reflexivity.
Qed.

Ltac settle :=
  repeat match goal with
  | |- context [Nat.eqb ?a ?b] =>
      let E := fresh in
      destruct (Nat.eqb a b) eqn:E; [apply Nat.eqb_eq in E|apply Nat.eqb_neq in E]
  end; try reflexivity; exfalso; lia.

Lemma put_spec {A} fuel : forall (t : trie A) i x j,
  i <= fuel -> find (put fuel t i x) j = if Nat.eqb i j then Some x else find t j.
Proof.
  induction fuel as [|f IH]; intros t i x j Hi.
  - assert (i = 0) as -> by lia. cbn [put].
    destruct j as [|j]; cbn [find Nat.eqb]; [reflexivity|].
    now rewrite (find_split t (S j)).
  - destruct i as [|i].
    + cbn [put]. destruct j as [|j]; cbn [find Nat.eqb]; [reflexivity|].
      now rewrite (find_split t (S j)).
    + cbn [put]. destruct (decompose (S i)) as [Di Bi]; [lia|].
      assert (Hk : key (S i) <= f) by lia.
      destruct j as [|j].
      * cbn [Nat.eqb]. rewrite (find_split t 0).
        destruct (Nat.eqb (bit (S i)) 0); reflexivity.
      * destruct (decompose (S j)) as [Dj Bj]; [lia|].
        rewrite (find_split t (S j)).
        destruct (Nat.eqb (bit (S i)) 0) eqn:Ei, (Nat.eqb (bit (S j)) 0) eqn:Ej;
          cbn [find]; rewrite Ej;
          [apply Nat.eqb_eq in Ei, Ej|apply Nat.eqb_eq in Ei; apply Nat.eqb_neq in Ej
          |apply Nat.eqb_neq in Ei; apply Nat.eqb_eq in Ej|apply Nat.eqb_neq in Ei, Ej];
          try rewrite IH by exact Hk; settle.
Qed.

Inductive shape :=
| Literal (z : Z) | Ident | Nothing | Argument (level : nat)
| Image (graph : shape) | Applied (graph arg : shape)
| Either (left right : shape) | Abstraction (level : nat) (domain body : shape).

Fixpoint same (a b : shape) : bool :=
  match a, b with
  | Literal x, Literal y => Z.eqb x y
  | Ident, Ident | Nothing, Nothing => true
  | Argument i, Argument j => Nat.eqb i j
  | Image f, Image g => same f g
  | Applied f x, Applied g y | Either f x, Either g y => same f g && same x y
  | Abstraction i d b, Abstraction j e c => Nat.eqb i j && same d e && same b c
  | _, _ => false
  end.

Lemma same_eq a b : same a b = true -> a = b.
Proof.
  revert b. induction a; destruct b; cbn; intros H; try discriminate;
    rewrite ?andb_true_iff in H.
  - now apply Z.eqb_eq in H as ->.
  - reflexivity.
  - reflexivity.
  - now apply Nat.eqb_eq in H as ->.
  - now rewrite (IHa _ H).
  - destruct H as [H1 H2]. now rewrite (IHa1 _ H1), (IHa2 _ H2).
  - destruct H as [H1 H2]. now rewrite (IHa1 _ H1), (IHa2 _ H2).
  - destruct H as [[H0 H1] H2]. apply Nat.eqb_eq in H0 as ->.
    now rewrite (IHa1 _ H1), (IHa2 _ H2).
Qed.

Lemma same_refl a : same a a = true.
Proof.
  induction a; cbn; rewrite ?andb_true_iff; auto using Z.eqb_refl, Nat.eqb_refl.
Qed.

Fixpoint closed (depth : nat) (s : shape) : Prop :=
  match s with
  | Literal _ | Ident | Nothing => True
  | Argument l => l < depth
  | Image f => closed depth f
  | Applied f x | Either f x => closed depth f /\ closed depth x
  | Abstraction l d b => l <= depth /\ closed depth d /\ closed (S l) b
  end.

Lemma closed_later s : forall depth depth', depth <= depth' -> closed depth s -> closed depth' s.
Proof.
  induction s; intros d d' H Hc; cbn in Hc |- *.
  - exact I.
  - exact I.
  - exact I.
  - lia.
  - eauto.
  - destruct Hc. split; eauto.
  - destruct Hc. split; eauto.
  - destruct Hc as (Hl & Hd & Hb). split; [lia|]. split; [eauto|exact Hb].
Qed.

Definition failing s := match s with Nothing => true | _ => false end.

Lemma failing_nothing s : failing s = true -> s = Nothing.
Proof. now destruct s. Qed.

Definition fold_image f := if failing f then Nothing else Image f.
Definition fold_applied f x := if failing f || failing x then Nothing else Applied f x.
Definition fold_either l r :=
  if failing l then r else if failing r then l else if same l r then l else Either l r.

Lemma fold_image_closed d f : closed d f -> closed d (fold_image f).
Proof. unfold fold_image. now destruct (failing f). Qed.

Lemma fold_applied_closed d f x : closed d f -> closed d x -> closed d (fold_applied f x).
Proof. unfold fold_applied. destruct (failing f || failing x); cbn; tauto. Qed.

Lemma fold_either_closed d l r : closed d l -> closed d r -> closed d (fold_either l r).
Proof.
  unfold fold_either. intros. destruct (failing l), (failing r); auto.
  destruct (same l r); cbn; auto.
Qed.

Definition entry (defs : trie shape) i := match find defs i with Some s => s | None => Nothing end.

Fixpoint lift (code : block) (defs : trie shape) (next depth : nat) : shape :=
  let get := entry defs in
  let push s := put next defs next s in
  match code with
  | Yield i => get i
  | Constant z rest => lift rest (push (Literal z)) (S next) depth
  | Identity rest => lift rest (push Ident) (S next) depth
  | Empty rest => lift rest (push Nothing) (S next) depth
  | Project f rest => lift rest (push (fold_image (get f))) (S next) depth
  | Call f x rest => lift rest (push (fold_applied (get f) (get x))) (S next) depth
  | Union l r rest => lift rest (push (fold_either (get l) (get r))) (S next) depth
  | Abstract d body rest =>
      let inner := lift body (put next defs next (Argument depth)) (S next) (S depth) in
      lift rest (push (Abstraction depth (get d) inner)) (S next) depth
  end.

Definition validate (source target : region) : bool :=
  match decode 0 source, decode 0 target with
  | Some a, Some b => same (lift a Tip 0 0) (lift b Tip 0 0)
  | _, _ => false
  end.

Definition scoped_defs defs n depth :=
  (forall i, i < n -> closed depth (entry defs i)) /\ (forall i, n <= i -> find defs i = None).

Lemma entry_put defs n s i : entry (put n defs n s) i = if Nat.eqb n i then s else entry defs i.
Proof. unfold entry. rewrite put_spec by lia. now destruct (Nat.eqb n i). Qed.

Lemma entry_closed defs n depth i : scoped_defs defs n depth -> closed depth (entry defs i).
Proof.
  intros [Hc Hn]. destruct (Nat.lt_ge_cases i n) as [H|H]; [now apply Hc|].
  unfold entry. now rewrite (Hn i H).
Qed.

Lemma scoped_push defs n depth s :
  scoped_defs defs n depth -> closed depth s -> scoped_defs (put n defs n s) (S n) depth.
Proof.
  intros [Hc Hn] Hs. split; intros i Hi.
  - rewrite entry_put. destruct (Nat.eqb n i) eqn:E; [exact Hs|].
    apply Nat.eqb_neq in E. apply Hc. lia.
  - rewrite put_spec by lia. replace (Nat.eqb n i) with false
      by (symmetry; apply Nat.eqb_neq; lia). apply Hn. lia.
Qed.

Lemma scoped_enter defs n depth :
  scoped_defs defs n depth -> scoped_defs (put n defs n (Argument depth)) (S n) (S depth).
Proof.
  intros [Hc Hn]. apply scoped_push; [|cbn; lia].
  split; [|exact Hn]. intros i Hi. eapply closed_later; [|apply Hc; exact Hi]. lia.
Qed.

Lemma lift_closed code : forall defs n depth,
  scoped_defs defs n depth -> closed depth (lift code defs n depth).
Proof.
  induction code as [i|z rest IH|rest IH|rest IH|f rest IH|f x rest IH|l r rest IH
    |d body IHbody rest IH]; intros defs n depth Hs; cbn [lift].
  - now apply (entry_closed defs n).
  - apply IH, scoped_push; [exact Hs|exact I].
  - apply IH, scoped_push; [exact Hs|exact I].
  - apply IH, scoped_push; [exact Hs|exact I].
  - apply IH, scoped_push; [exact Hs|]. apply fold_image_closed. now apply (entry_closed defs n).
  - apply IH, scoped_push; [exact Hs|].
    apply fold_applied_closed; now apply (entry_closed defs n).
  - apply IH, scoped_push; [exact Hs|].
    apply fold_either_closed; now apply (entry_closed defs n).
  - apply IH, scoped_push; [exact Hs|]. cbn. split; [lia|]. split.
    + now apply (entry_closed defs n).
    + apply IHbody. now apply scoped_enter.
Qed.

Section Validation.
Context {value : Type}.
Variable integer : Z -> value.
Variable edge : value -> value -> value -> Prop.
Variable graph : value -> Prop.
Variable int : value.

Abbreviation E := (eval integer edge graph int).

Definition update (args : nat -> @members value) l A := fun k => if Nat.eqb k l then A else args k.

Fixpoint picture (s : shape) (args : nat -> @members value) : @members value :=
  match s with
  | Literal z => one (integer z)
  | Ident => one int
  | Nothing => none
  | Argument l => args l
  | Image f => range edge (picture f args)
  | Applied f x => apply edge (picture f args) (picture x args)
  | Either l r => join (picture l args) (picture r args)
  | Abstraction l d b =>
      pi edge graph (picture d args) (fun a => picture b (update args l (one a)))
  end.

Lemma equiv_refl (A : @members value) : equiv A A.
Proof. intros v. reflexivity. Qed.

Lemma equiv_sym (A B : @members value) : equiv A B -> equiv B A.
Proof. intros H v. symmetry. apply H. Qed.

Lemma equiv_trans (A B C : @members value) : equiv A B -> equiv B C -> equiv A C.
Proof. intros H1 H2 v. rewrite (H1 v). apply H2. Qed.

Lemma range_equiv A A' : equiv A A' -> equiv (range edge A) (range edge A').
Proof. unfold equiv, range. firstorder. Qed.

Lemma apply_equiv F F' A A' :
  equiv F F' -> equiv A A' -> equiv (apply edge F A) (apply edge F' A').
Proof. unfold equiv, apply. firstorder. Qed.

Lemma join_equiv (A A' B B' : @members value) :
  equiv A A' -> equiv B B' -> equiv (join A B) (join A' B').
Proof. unfold equiv, join. firstorder. Qed.

Lemma pi_equiv A A' B B' :
  equiv A A' -> (forall a, equiv (B a) (B' a)) ->
  equiv (pi edge graph A B) (pi edge graph A' B').
Proof.
  intros HA HB f. unfold pi. split.
  - intros (Hg & Hf & Hd & Hb). split; [exact Hg|]. split; [exact Hf|]. split.
    + intros a Ha. apply Hd. now apply HA.
    + intros a b Hab. destruct (Hb a b Hab) as [Ha Hb'].
      split; [now apply HA|now apply HB].
  - intros (Hg & Hf & Hd & Hb). split; [exact Hg|]. split; [exact Hf|]. split.
    + intros a Ha. apply Hd. now apply HA.
    + intros a b Hab. destruct (Hb a b Hab) as [Ha Hb'].
      split; [now apply HA|now apply HB].
Qed.

Lemma picture_agree s : forall depth args args',
  closed depth s -> (forall l, l < depth -> equiv (args l) (args' l)) ->
  equiv (picture s args) (picture s args').
Proof.
  induction s; intros depth args args' Hc Ha; cbn in Hc |- *.
  - exact (equiv_refl _).
  - exact (equiv_refl _).
  - exact (equiv_refl _).
  - now apply Ha.
  - eapply range_equiv, IHs; eauto.
  - destruct Hc. eapply apply_equiv; [eapply IHs1|eapply IHs2]; eauto.
  - destruct Hc. eapply join_equiv; [eapply IHs1|eapply IHs2]; eauto.
  - destruct Hc as (Hl & Hd & Hb). apply pi_equiv; [eapply IHs1; eauto|].
    intros a. apply (IHs2 (S level)); [exact Hb|].
    intros m Hm. unfold update. destruct (Nat.eqb m level) eqn:E; [exact (equiv_refl _)|].
    apply Nat.eqb_neq in E. apply Ha. lia.
Qed.

Lemma fold_image_picture f args :
  equiv (picture (fold_image f) args) (range edge (picture f args)).
Proof.
  unfold fold_image. destruct (failing f) eqn:E; [|exact (equiv_refl _)].
  apply failing_nothing in E as ->. cbn. unfold equiv, range, none. firstorder.
Qed.

Lemma fold_applied_picture f x args :
  equiv (picture (fold_applied f x) args) (apply edge (picture f args) (picture x args)).
Proof.
  unfold fold_applied. destruct (failing f) eqn:Ef; [|destruct (failing x) eqn:Ex];
    cbn [orb]; try exact (equiv_refl _).
  - apply failing_nothing in Ef as ->. cbn. unfold equiv, apply, none. firstorder.
  - apply failing_nothing in Ex as ->. cbn. unfold equiv, apply, none. firstorder.
Qed.

Lemma fold_either_picture l r args :
  equiv (picture (fold_either l r) args) (join (picture l args) (picture r args)).
Proof.
  unfold fold_either. destruct (failing l) eqn:El.
  - apply failing_nothing in El as ->. cbn. unfold equiv, join, none. firstorder.
  - destruct (failing r) eqn:Er.
    + apply failing_nothing in Er as ->. cbn. unfold equiv, join, none. firstorder.
    + destruct (same l r) eqn:Es; [|exact (equiv_refl _)].
      apply same_eq in Es as ->. unfold equiv, join. firstorder.
Qed.

Definition related (env : list (@members value)) defs args depth :=
  scoped_defs defs (length env) depth /\
  forall i, i < length env -> equiv (nth i env none) (picture (entry defs i) args).

Lemma related_get env defs args depth i :
  related env defs args depth -> equiv (nth i env none) (picture (entry defs i) args).
Proof.
  intros [[_ Hn] Hs]. destruct (Nat.lt_ge_cases i (length env)) as [H|H]; [now apply Hs|].
  unfold entry. rewrite (Hn i H), nth_overflow by exact H. exact (equiv_refl _).
Qed.

Lemma step (env : list (@members value)) A : S (length env) = length (env ++ [A]).
Proof. rewrite length_app. cbn. lia. Qed.

Lemma related_push env defs args depth A s :
  related env defs args depth -> equiv A (picture s args) -> closed depth s ->
  related (env ++ [A]) (put (length env) defs (length env) s) args depth.
Proof.
  intros [Hs Hsem] HA Hc. split.
  - rewrite <- step. now apply scoped_push.
  - intros i Hi. rewrite <- step in Hi. rewrite entry_put.
    destruct (Nat.eqb (length env) i) eqn:E.
    + apply Nat.eqb_eq in E as <-. now rewrite nth_middle.
    + apply Nat.eqb_neq in E. rewrite app_nth1 by lia. apply Hsem. lia.
Qed.

Lemma related_enter env defs args depth a :
  related env defs args depth ->
  related (env ++ [one a]) (put (length env) defs (length env) (Argument depth))
    (update args depth (one a)) (S depth).
Proof.
  intros [Hs Hsem]. split.
  - rewrite <- step. now apply scoped_enter.
  - intros i Hi. rewrite <- step in Hi. rewrite entry_put.
    destruct (Nat.eqb (length env) i) eqn:E.
    + apply Nat.eqb_eq in E as <-. rewrite nth_middle. cbn. unfold update.
      rewrite Nat.eqb_refl. exact (equiv_refl _).
    + apply Nat.eqb_neq in E. rewrite app_nth1 by lia.
      eapply equiv_trans; [apply Hsem; lia|].
      eapply picture_agree; [exact (entry_closed _ _ _ i Hs)|].
      intros l Hl. unfold update. replace (Nat.eqb l depth) with false
        by (symmetry; apply Nat.eqb_neq; lia). exact (equiv_refl _).
Qed.

Lemma lift_correct code : forall env defs args depth,
  related env defs args depth ->
  equiv (E code env) (picture (lift code defs (length env) depth) args).
Proof.
  induction code as [i|z rest IH|rest IH|rest IH|f rest IH|f x rest IH|l r rest IH
    |d body IHbody rest IH]; intros env defs args depth Hrel; cbn [eval lift].
  - exact (related_get _ _ _ _ _ Hrel).
  - rewrite (step env (one (integer z))).
    apply IH, related_push; [exact Hrel|exact (equiv_refl _)|exact I].
  - rewrite (step env (one int)).
    apply IH, related_push; [exact Hrel|exact (equiv_refl _)|exact I].
  - rewrite (step env none).
    apply IH, related_push; [exact Hrel|exact (equiv_refl _)|exact I].
  - rewrite (step env (range edge (nth f env none))).
    apply IH, related_push; [exact Hrel| |].
    + eapply equiv_trans; [apply range_equiv, (related_get _ _ _ _ _ Hrel)|].
      apply equiv_sym, fold_image_picture.
    + apply fold_image_closed. exact (entry_closed _ _ _ f (proj1 Hrel)).
  - rewrite (step env (apply edge (nth f env none) (nth x env none))).
    apply IH, related_push; [exact Hrel| |].
    + eapply equiv_trans;
        [apply apply_equiv; apply (related_get _ _ _ _ _ Hrel)|].
      apply equiv_sym, fold_applied_picture.
    + apply fold_applied_closed; exact (entry_closed _ _ _ _ (proj1 Hrel)).
  - rewrite (step env (join (nth l env none) (nth r env none))).
    apply IH, related_push; [exact Hrel| |].
    + eapply equiv_trans;
        [apply join_equiv; apply (related_get _ _ _ _ _ Hrel)|].
      apply equiv_sym, fold_either_picture.
    + apply fold_either_closed; exact (entry_closed _ _ _ _ (proj1 Hrel)).
  - set (inner := lift body (put (length env) defs (length env) (Argument depth))
                    (S (length env)) (S depth)).
    assert (Hbody : forall a, equiv (E body (env ++ [one a]))
                              (picture inner (update args depth (one a)))).
    { intros a. unfold inner. rewrite (step env (one a)).
      apply IHbody. now apply related_enter. }
    assert (Hinner : closed (S depth) inner).
    { apply lift_closed, scoped_enter. exact (proj1 Hrel). }
    rewrite (step env (pi edge graph (nth d env none) (fun a => E body (env ++ [one a])))).
    apply IH, related_push; [exact Hrel| |].
    + cbn [picture]. apply pi_equiv; [apply (related_get _ _ _ _ _ Hrel)|exact Hbody].
    + cbn. split; [lia|]. split; [exact (entry_closed _ _ _ d (proj1 Hrel))|exact Hinner].
Qed.

Theorem lift_sound code : equiv (E code []) (picture (lift code Tip 0 0) (fun _ => none)).
Proof.
  apply (lift_correct code [] Tip (fun _ => none) 0).
  split; [split; [intros i Hi; cbn in Hi; lia|reflexivity]|].
  intros i Hi. cbn in Hi. lia.
Qed.
End Validation.

Theorem validate_sound source target :
  validate source target = true ->
  exists a b, decode 0 source = Some a /\ decode 0 target = Some b /\ scoped 0 b /\
    forall (V : Type) (integer : Z -> V) edge graph int v,
      eval integer edge graph int b [] v <-> eval integer edge graph int a [] v.
Proof.
  unfold validate.
  destruct (decode 0 source) as [a|] eqn:Ea; [|discriminate].
  destruct (decode 0 target) as [b|] eqn:Eb; [|discriminate].
  intros H. apply same_eq in H.
  exists a, b. split; [reflexivity|]. split; [reflexivity|].
  split; [exact (proj1 (decode_canonical _ _ _ Eb))|].
  intros V integer edge graph int v.
  rewrite (lift_sound integer edge graph int b v), (lift_sound integer edge graph int a v).
  now rewrite H.
Qed.

Theorem validate_reflexive r code : decode 0 r = Some code -> validate r r = true.
Proof. intros H. unfold validate. rewrite H. apply same_refl. Qed.

Theorem optimisation_verified L (source : named L) target optimised :
  translate source = Compiled target -> validate target optimised = true ->
  exists e code, resolves [] source e /\ decode 0 optimised = Some code /\ scoped 0 code /\
    forall (V : Type) (integer : Z -> V) edge graph int v,
      eval integer edge graph int code [] v <-> denote integer edge graph int e [] v.
Proof.
  intros Ht Hv.
  destruct (translate_verified L source target Ht) as (e & a & He & Ha & _ & Hsem).
  destruct (validate_sound target optimised Hv) as (a' & b & Ha' & Hb & Hscoped & Hval).
  rewrite Ha in Ha'. injection Ha' as <-.
  exists e, b. split; [exact He|]. split; [exact Hb|]. split; [exact Hscoped|].
  intros V integer edge graph int v. now rewrite Hval, Hsem.
Qed.

Fixpoint occurs (k : nat) (code : block) : bool :=
  match code with
  | Yield i => Nat.eqb i k
  | Constant _ rest | Identity rest | Empty rest => occurs k rest
  | Project f rest => Nat.eqb f k || occurs k rest
  | Call f x rest | Union f x rest => Nat.eqb f k || Nat.eqb x k || occurs k rest
  | Abstract d body rest => Nat.eqb d k || occurs k body || occurs k rest
  end.

Fixpoint rename (rho : nat -> nat) (from to : nat) (code : block) : block :=
  let rho' k := if Nat.eqb k from then to else rho k in
  match code with
  | Yield i => Yield (rho i)
  | Constant z rest => Constant z (rename rho' (S from) (S to) rest)
  | Identity rest => Identity (rename rho' (S from) (S to) rest)
  | Empty rest => Empty (rename rho' (S from) (S to) rest)
  | Project f rest => Project (rho f) (rename rho' (S from) (S to) rest)
  | Call f x rest => Call (rho f) (rho x) (rename rho' (S from) (S to) rest)
  | Union l r rest => Union (rho l) (rho r) (rename rho' (S from) (S to) rest)
  | Abstract d body rest =>
      Abstract (rho d) (rename rho' (S from) (S to) body) (rename rho' (S from) (S to) rest)
  end.

Definition faithful (rho : nat -> nat) nB nA (A B : trie shape) code :=
  forall k, k < nB -> occurs k code = true -> rho k < nA /\ entry A (rho k) = entry B k.

Lemma faithful_extend rho nB nA A B code rest s :
  faithful rho nB nA A B code ->
  (forall k, occurs k rest = true -> k < nB -> occurs k code = true) ->
  faithful (fun k => if Nat.eqb k nB then nA else rho k) (S nB) (S nA)
    (put nA A nA s) (put nB B nB s) rest.
Proof.
  intros H Hsub k Hk Ho. rewrite !entry_put.
  destruct (Nat.eqb k nB) eqn:E.
  - apply Nat.eqb_eq in E as ->. rewrite !Nat.eqb_refl. split; [lia|reflexivity].
  - apply Nat.eqb_neq in E. destruct (H k ltac:(lia) (Hsub k Ho ltac:(lia))) as [Hlt He].
    replace (Nat.eqb nA (rho k)) with false by (symmetry; apply Nat.eqb_neq; lia).
    replace (Nat.eqb nB k) with false by (symmetry; apply Nat.eqb_neq; lia).
    split; [lia|exact He].
Qed.

Ltac occurring := intros ? Ho ?; cbn [occurs]; rewrite ?Ho, ?orb_true_r; reflexivity.

Lemma operand rho nB nA A B code f :
  faithful rho nB nA A B code -> f < nB -> occurs f code = true ->
  entry A (rho f) = entry B f.
Proof. intros H Hf Ho. exact (proj2 (H f Hf Ho)). Qed.

Lemma lift_rename code : forall rho nB nA A B depth,
  scoped nB code -> faithful rho nB nA A B code ->
  lift (rename rho nB nA code) A nA depth = lift code B nB depth.
Proof.
  induction code as [i|z rest IH|rest IH|rest IH|f rest IH|f x rest IH|l r rest IH
    |d body IHbody rest IH]; intros rho nB nA A B depth Hs Hf;
    cbn [scoped] in Hs; cbn [rename lift].
  - apply (operand rho nB nA A B (Yield i)); [exact Hf|exact Hs|cbn; apply Nat.eqb_refl].
  - apply IH; [exact Hs|]. eapply faithful_extend; [exact Hf|]. occurring.
  - apply IH; [exact Hs|]. eapply faithful_extend; [exact Hf|]. occurring.
  - apply IH; [exact Hs|]. eapply faithful_extend; [exact Hf|]. occurring.
  - destruct Hs as [Hf' Hs].
    rewrite (operand _ _ _ _ _ _ f Hf Hf') by (cbn; now rewrite Nat.eqb_refl).
    apply IH; [exact Hs|]. eapply faithful_extend; [exact Hf|]. occurring.
  - destruct Hs as (Hf' & Hx & Hs).
    rewrite (operand _ _ _ _ _ _ f Hf Hf') by (cbn; now rewrite Nat.eqb_refl).
    rewrite (operand _ _ _ _ _ _ x Hf Hx) by (cbn; now rewrite Nat.eqb_refl, ?orb_true_r).
    apply IH; [exact Hs|]. eapply faithful_extend; [exact Hf|]. occurring.
  - destruct Hs as (Hl & Hr & Hs).
    rewrite (operand _ _ _ _ _ _ l Hf Hl) by (cbn; now rewrite Nat.eqb_refl).
    rewrite (operand _ _ _ _ _ _ r Hf Hr) by (cbn; now rewrite Nat.eqb_refl, ?orb_true_r).
    apply IH; [exact Hs|]. eapply faithful_extend; [exact Hf|]. occurring.
  - destruct Hs as (Hd & Hb & Hs).
    rewrite (operand _ _ _ _ _ _ d Hf Hd) by (cbn; now rewrite Nat.eqb_refl).
    rewrite (IHbody _ (S nB) (S nA) _ _ _ Hb) by (eapply faithful_extend; [exact Hf|]; occurring).
    apply IH; [exact Hs|]. eapply faithful_extend; [exact Hf|]. occurring.
Qed.

Lemma below_extend rho nB nA code rest :
  (forall k, k < nB -> occurs k code = true -> rho k < nA) ->
  (forall k, occurs k rest = true -> k < nB -> occurs k code = true) ->
  forall k, k < S nB -> occurs k rest = true -> (if Nat.eqb k nB then nA else rho k) < S nA.
Proof.
  intros Hr Hsub k Hk Ho. destruct (Nat.eqb k nB) eqn:E; [lia|].
  apply Nat.eqb_neq in E. enough (rho k < nA) by lia. apply Hr; [lia|]. apply Hsub; [exact Ho|lia].
Qed.

Lemma rename_scoped code : forall rho nB nA,
  scoped nB code ->
  (forall k, k < nB -> occurs k code = true -> rho k < nA) ->
  scoped nA (rename rho nB nA code).
Proof.
  induction code as [i|z rest IH|rest IH|rest IH|f rest IH|f x rest IH|l r rest IH
    |d body IHbody rest IH]; intros rho nB nA Hs Hr; cbn [scoped] in Hs; cbn [rename scoped].
  - apply Hr; [exact Hs|cbn; apply Nat.eqb_refl].
  - apply IH; [exact Hs|]. eapply below_extend; [exact Hr|]. occurring.
  - apply IH; [exact Hs|]. eapply below_extend; [exact Hr|]. occurring.
  - apply IH; [exact Hs|]. eapply below_extend; [exact Hr|]. occurring.
  - destruct Hs as [Hf Hs]. split.
    + apply Hr; [exact Hf|cbn; now rewrite Nat.eqb_refl].
    + apply IH; [exact Hs|]. eapply below_extend; [exact Hr|]. occurring.
  - destruct Hs as (Hf & Hx & Hs). split; [|split].
    + apply Hr; [exact Hf|cbn; now rewrite Nat.eqb_refl].
    + apply Hr; [exact Hx|cbn; now rewrite Nat.eqb_refl, ?orb_true_r].
    + apply IH; [exact Hs|]. eapply below_extend; [exact Hr|]. occurring.
  - destruct Hs as (Hl & Hr' & Hs). split; [|split].
    + apply Hr; [exact Hl|cbn; now rewrite Nat.eqb_refl].
    + apply Hr; [exact Hr'|cbn; now rewrite Nat.eqb_refl, ?orb_true_r].
    + apply IH; [exact Hs|]. eapply below_extend; [exact Hr|]. occurring.
  - destruct Hs as (Hd & Hb & Hs). split; [|split].
    + apply Hr; [exact Hd|cbn; now rewrite Nat.eqb_refl].
    + apply IHbody; [exact Hb|]. eapply below_extend; [exact Hr|]. occurring.
    + apply IH; [exact Hs|]. eapply below_extend; [exact Hr|]. occurring.
Qed.

Definition rest_of (code : block) : option block :=
  match code with
  | Yield _ => None
  | Constant _ r | Identity r | Empty r | Project _ r | Call _ _ r | Union _ _ r
  | Abstract _ _ r => Some r
  end.

Definition with_rest (code r : block) : block :=
  match code with
  | Yield i => Yield i
  | Constant z _ => Constant z r
  | Identity _ => Identity r
  | Empty _ => Empty r
  | Project f _ => Project f r
  | Call f x _ => Call f x r
  | Union l l' _ => Union l l' r
  | Abstract d body _ => Abstract d body r
  end.

Definition shape_of code defs n depth :=
  match code with
  | Yield _ => Nothing
  | Constant z _ => Literal z
  | Identity _ => Ident
  | Empty _ => Nothing
  | Project f _ => fold_image (entry defs f)
  | Call f x _ => fold_applied (entry defs f) (entry defs x)
  | Union l r _ => fold_either (entry defs l) (entry defs r)
  | Abstract d body _ =>
      Abstraction depth (entry defs d) (lift body (put n defs n (Argument depth)) (S n) (S depth))
  end.

Lemma lift_unfold code r defs n depth :
  rest_of code = Some r ->
  lift code defs n depth = lift r (put n defs n (shape_of code defs n depth)) (S n) depth.
Proof. intros H. destruct code; cbn in *; try discriminate; injection H as <-; reflexivity. Qed.

Lemma scoped_rest code r n : rest_of code = Some r -> scoped n code -> scoped (S n) r.
Proof. intros H. destruct code; cbn in *; try discriminate; injection H as <-; tauto. Qed.

Lemma scoped_with code r r' n :
  rest_of code = Some r -> scoped n code -> scoped (S n) r' -> scoped n (with_rest code r').
Proof. intros H. destruct code; cbn in *; try discriminate; injection H as <-; tauto. Qed.

Inductive rewrites : trie shape -> nat -> nat -> block -> block -> Prop :=
| Redirect defs n depth code p q :
    p < n -> entry defs p = entry defs q ->
    rewrites defs n depth code (rename (fun k => if Nat.eqb k q then p else k) n n code)
| Drop defs n depth code r :
    rest_of code = Some r -> occurs n r = false ->
    rewrites defs n depth code (rename (fun k => k) (S n) n r)
| Later defs n depth code r r' :
    rest_of code = Some r ->
    rewrites (put n defs n (shape_of code defs n depth)) (S n) depth r r' ->
    rewrites defs n depth code (with_rest code r')
| Inside defs n depth d body body' rest :
    rewrites (put n defs n (Argument depth)) (S n) (S depth) body body' ->
    rewrites defs n depth (Abstract d body rest) (Abstract d body' rest).

Lemma rewrites_lift defs n depth a b :
  rewrites defs n depth a b -> scoped n a ->
  lift a defs n depth = lift b defs n depth /\ scoped n b.
Proof.
  induction 1 as [defs n depth code p q Hp He|defs n depth code r Hr Hn
    |defs n depth code r r' Hr Hrw IH|defs n depth d body body' rest Hrw IH]; intros Hs.
  - assert (Hf : faithful (fun k => if Nat.eqb k q then p else k) n n defs defs code).
    { intros k Hk _. destruct (Nat.eqb k q) eqn:E; [|split; [lia|reflexivity]].
      apply Nat.eqb_eq in E as ->. split; [lia|exact He]. }
    split; [symmetry; now apply lift_rename|].
    apply rename_scoped; [exact Hs|]. intros k Hk Ho. exact (proj1 (Hf k Hk Ho)).
  - pose proof (scoped_rest _ _ _ Hr Hs) as Hs'.
    assert (Hf : faithful (fun k => k) (S n) n defs
                   (put n defs n (shape_of code defs n depth)) r).
    { intros k Hk Ho. assert (k <> n) by (intros ->; congruence).
      rewrite entry_put. replace (Nat.eqb n k) with false
        by (symmetry; apply Nat.eqb_neq; lia). split; [lia|reflexivity]. }
    rewrite (lift_unfold _ _ _ _ _ Hr). split; [symmetry; now apply lift_rename|].
    apply rename_scoped; [exact Hs'|]. intros k Hk Ho. exact (proj1 (Hf k Hk Ho)).
  - destruct (IH (scoped_rest _ _ _ Hr Hs)) as [He Hs'].
    assert (Hr' : rest_of (with_rest code r') = Some r') by (destruct code; cbn in *; congruence).
    rewrite (lift_unfold _ _ _ _ _ Hr), (lift_unfold _ _ _ _ _ Hr'), He.
    replace (shape_of (with_rest code r') defs n depth) with (shape_of code defs n depth)
      by (destruct code; reflexivity).
    split; [reflexivity|]. exact (scoped_with _ _ _ _ Hr Hs Hs').
  - cbn [scoped] in Hs. destruct Hs as (Hd & Hb & Hrest).
    destruct (IH Hb) as [He Hb']. cbn [lift]. rewrite He.
    split; [reflexivity|]. cbn [scoped]. tauto.
Qed.

Lemma optimises_lift a b :
  clos_refl_trans _ (rewrites Tip 0 0) a b -> scoped 0 a ->
  lift a Tip 0 0 = lift b Tip 0 0 /\ scoped 0 b.
Proof.
  induction 1 as [a b H|a|a b c _ IH1 _ IH2]; intros Hs.
  - now apply rewrites_lift.
  - now split.
  - destruct (IH1 Hs) as [E1 S1]. destruct (IH2 S1) as [E2 S2].
    split; [congruence|exact S2].
Qed.

Theorem validate_complete source a b :
  decode 0 source = Some a -> clos_refl_trans _ (rewrites Tip 0 0) a b ->
  validate source (encode 0 b) = true.
Proof.
  intros Ha Hab.
  destruct (optimises_lift a b Hab (proj1 (decode_canonical _ _ _ Ha))) as [E Hb].
  unfold validate. rewrite Ha, (encode_roundtrip b 0 Hb), E. apply same_refl.
Qed.

Lemma folds_agree l r f x :
  fold_either Nothing r = r /\ fold_either l Nothing = l /\ fold_either l l = l /\
  fold_image Nothing = Nothing /\ fold_applied Nothing x = Nothing /\
  fold_applied f Nothing = Nothing.
Proof.
  unfold fold_either, fold_image, fold_applied. split; [reflexivity|]. split.
  { destruct (failing l) eqn:E; [now apply failing_nothing in E as ->|reflexivity]. }
  split.
  { destruct (failing l) eqn:E; [now apply failing_nothing in E as ->|]. now rewrite same_refl. }
  split; [reflexivity|]. split; [reflexivity|]. cbn [failing]. now rewrite orb_true_r.
Qed.

Print Assumptions put_spec.
Print Assumptions validate_sound.
Print Assumptions validate_reflexive.
Print Assumptions optimisation_verified.
Print Assumptions validate_complete.
Print Assumptions folds_agree.

From Corelib Require Import extraction.ExtrOcamlBasic.
From Stdlib Require Import extraction.ExtrOcamlString extraction.ExtrOcamlNatInt.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "core.ml" translate validate parse_integer print_integer integer_width.
