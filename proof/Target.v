From Stdlib Require Import Lists.List Arith.Arith ZArith.ZArith.
Open Scope bool_scope.
Require Import Core Names.
Import ListNotations.

Inductive opcode := Const_op | Int_op | Fail_op | Range_op | Apply_op | Choice_op | Lambda_op.

#[warnings="-register-all"] Inductive region :=
| Return (operand : nat)
| Operation (op : opcode) (result : nat) (operands : list nat)
    (literal : option Z) (body : option (nat * region)) (rest : region).

Fixpoint encode next code : region :=
  let emit op operands literal body rest :=
    Operation op next operands literal body (encode (S next) rest) in
  match code with
  | Yield r => Return r
  | Constant z rest => emit Const_op [] (Some z) None rest
  | Identity rest => emit Int_op [] None None rest
  | Empty rest => emit Fail_op [] None None rest
  | Project f rest => emit Range_op [f] None None rest
  | Call f x rest => emit Apply_op [f; x] None None rest
  | Union l r rest => emit Choice_op [l; r] None None rest
  | Abstract d body rest => emit Lambda_op [d] None (Some (next, encode (S next) body)) rest
  end.

Fixpoint decode next (r : region) : option block :=
  match r with
  | Return v => if v <? next then Some (Yield v) else None
  | Operation op result args attr body rest =>
      if (result =? next) && forallb (fun v => v <? next) args then
        match decode (S next) rest with
        | None => None
        | Some tail =>
            match op, args, attr, body with
            | Const_op, [], Some z, None => Some (Constant z tail)
            | Int_op, [], None, None => Some (Identity tail)
            | Fail_op, [], None, None => Some (Empty tail)
            | Range_op, [f], None, None => Some (Project f tail)
            | Apply_op, [f; x], None, None => Some (Call f x tail)
            | Choice_op, [l; r], None, None => Some (Union l r tail)
            | Lambda_op, [d], None, Some (arg, nested) =>
                if arg =? next then
                  option_map (fun b => Abstract d b tail) (decode (S next) nested)
                else None
            | _, _, _, _ => None
            end
        end
      else None
  end.

Theorem encode_roundtrip code n :
  scoped n code -> decode n (encode n code) = Some code.
Proof.
  revert n. induction code; intros n H; cbn [scoped] in H; cbn [encode decode forallb andb].
  - apply Nat.ltb_lt in H. now rewrite H. 
  - now rewrite Nat.eqb_refl, (IHcode _ H).
  - now rewrite Nat.eqb_refl, (IHcode _ H).
  - now rewrite Nat.eqb_refl, (IHcode _ H).
  - destruct H as [H Hrest]. apply Nat.ltb_lt in H.
    now rewrite Nat.eqb_refl, H, (IHcode _ Hrest).
  - destruct H as (Hf & Hx & Hrest). apply Nat.ltb_lt in Hf, Hx.
    now rewrite Nat.eqb_refl, Hf, Hx, (IHcode _ Hrest).
  - destruct H as (Hl & Hr & Hrest). apply Nat.ltb_lt in Hl, Hr.
    now rewrite Nat.eqb_refl, Hl, Hr, (IHcode _ Hrest).
  - destruct H as (Hd & Hbody & Hrest). apply Nat.ltb_lt in Hd.
    now rewrite Nat.eqb_refl, Hd, (IHcode2 _ Hrest), (IHcode1 _ Hbody).
Qed.

Theorem decode_canonical r n code :
  decode n r = Some code -> scoped n code /\ encode n code = r.
Proof.
  revert r n code. fix IH 1. intros r n code H.
  destruct r as [v | op result args literal body rest]; cbn [decode] in H.
  - destruct (v <? n) eqn:E; [|discriminate].
    injection H as <-. cbn. now apply Nat.ltb_lt in E.
  - destruct ((result =? n) && forallb (fun v => v <? n) args) eqn:E;
      [|discriminate].
    apply Bool.andb_true_iff in E as [Er Ea]. apply Nat.eqb_eq in Er. subst result.
    destruct (decode (S n) rest) as [tail|] eqn:Et; [|discriminate].
    destruct (IH rest _ _ Et) as [Htail Rtail].
    assert (Hargs : forall v, In v args -> v < n).
    { intros v Hv. apply Nat.ltb_lt. now apply (proj1 (forallb_forall _ _) Ea). }
    destruct op; destruct args as [|f [|x [|y args]]];
      destruct literal; destruct body as [[arg nested]|]; try discriminate;
      try (injection H as <-; cbn [scoped encode]; rewrite Rtail;
           repeat split; auto with datatypes).
    destruct (arg =? n) eqn:Earg; [|discriminate].
    apply Nat.eqb_eq in Earg. subst arg.
    destruct (decode (S n) nested) as [inside|] eqn:En; [|discriminate].
    destruct (IH nested _ _ En) as [Hinside Rinside].
    injection H as <-. cbn [scoped encode]. rewrite Rinside, Rtail.
    repeat split; auto with datatypes.
Qed.

Inductive compilation (L : Type) :=
| Compiled (code : region)
| Rejected (pos : L) (x : identifier).

Arguments Compiled {L}.
Arguments Rejected {L}.

Definition translate {L} (source : named L) : compilation L :=
  match resolve [] source with
  | Resolved e => Compiled (encode 0 (compile e))
  | Unbound pos x => Rejected pos x
  end.

Theorem translate_exact L (source : named L) target :
  translate source = Compiled target <->
  exists e, resolves [] source e /\ target = encode 0 (compile e).
Proof.
  unfold translate. split.
  - destruct (resolve [] source) eqn:E; [|discriminate].
    intros H. injection H as <-. exists e. split; auto using resolve_sound.
  - intros (e & H & ->). now rewrite (resolve_complete _ _ _ _ H).
Qed.

Theorem translate_verified L (source : named L) target :
  translate source = Compiled target ->
  exists e code, resolves [] source e /\ decode 0 target = Some code /\ scoped 0 code /\
    forall (V : Type) (integer : Z -> V) edge graph int v,
      eval integer edge graph int code [] v <-> denote integer edge graph int e [] v.
Proof.
  intros H. apply translate_exact in H. destruct H as (e & H & ->).
  exists e, (compile e). split; [exact H|].
  split; [apply encode_roundtrip, compile_scoped|].
  split; [apply compile_scoped|]. intros. apply compile_correct.
Qed.

Definition example := Apply (Lambda (Range Int) (Var 0)) (Lit 7%Z).

Theorem example_denotes_seven
    (V : Type) (integer : Z -> V) edge graph identity
    (Hgraph : graph identity)
    (Hidentity : forall a b, edge identity a b <->
      exists z, a = integer z /\ b = integer z) v :
  eval integer edge graph identity (compile example) [] v <-> v = integer 7%Z.
Proof.
  rewrite compile_correct.
  cbn [example denote]. unfold apply, pi, range, one.
  split.
  - intros (f & a & (_ & _ & _ & Hbody) & <- & Hstep).
    destruct (Hbody _ _ Hstep) as [_ H]. cbn in H. congruence.
  - intros ->. exists identity, (integer 7%Z).
    split.
    + split; [exact Hgraph|]. split.
      * intros a b c Hb Hc. apply Hidentity in Hb, Hc.
        destruct Hb as (z & Ha & Hb), Hc as (w & Ha' & Hc). congruence.
      * split.
        -- intros a (f & input & <- & E).
           apply Hidentity in E. destruct E as (z & _ & ->).
           exists (integer z). apply Hidentity. now exists z.
        -- intros a b E. apply Hidentity in E. destruct E as (z & -> & ->).
           split; [|reflexivity].
           exists identity, (integer z). split; [reflexivity|].
           apply Hidentity. now exists z.
    + split; [reflexivity|]. apply Hidentity. now exists 7%Z.
Qed.

Print Assumptions lookup_sound.
Print Assumptions lookup_complete.
Print Assumptions resolve_sound.
Print Assumptions resolve_complete.
Print Assumptions encode_roundtrip.
Print Assumptions decode_canonical.
Print Assumptions translate_verified.
Print Assumptions example_denotes_seven.
