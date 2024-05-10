From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import List.
Import ListNotations.
From FirstProject Require Import Imp Maps.
Require Import Coq.Unicode.Utf8.

Inductive interpreter_result : Type :=
  | Success (s: state * (list (state*com)))
  | Fail
  | OutOfGas.

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)
Notation "'LETOPT' st cont <== e1 'IN' e2"
  := (match e1 with
          | Success (st, cont) => e2
          | Fail => Fail
          | OutOfGas => OutOfGas
       end)
  (right associativity, at level 60, st ident, cont ident).

(**
  2.1. TODO: Implement ceval_step as specified. To improve readability,
             you are strongly encouraged to define auxiliary notation.
             See the notation LETOPT in the ImpCEval chapter.
*)
Fixpoint ceval_step_suf (st : state) (c : com) (continuation: list (state * com)) (i : nat) (suf : option com)
                      : interpreter_result :=
  match i with
  | 0 => OutOfGas
  | S n => match c with
          | <{ skip }> => Success (st, continuation)
          | <{ x := a }> => Success ((x !-> (aeval st a) ; st), continuation) (* Update total_map st with binding *)
          | <{ c1 ; c2 }> =>
            LETOPT st' continuation' <== ceval_step_suf st c1 continuation n
              (match suf with
              | Some suf => Some <{ c2; suf }>
              | None => Some c2
              end)
            IN ceval_step_suf st' c2 continuation' n suf
          | <{ if b then c1 else c2 end }> =>
            if beval st b
            then ceval_step_suf st c1 continuation n suf
            else ceval_step_suf st c2 continuation n suf
          | <{ while b do c1 end }> =>
            if beval st b
            then
              LETOPT st' continuation' <== ceval_step_suf st c1 continuation n suf
              IN ceval_step_suf st' c continuation' n suf (* Repeat while with new state *)
            else Success (st, continuation)
          | <{ c1 !! c2 }> =>
              let c2' := match suf with
                         | Some suf => <{ c2; suf }>
                         | None => c2
                         end
              in ceval_step_suf st c1 ( (st, c2') :: continuation) n suf
          | <{ b -> c1 }> =>
            if (beval st b)
              then ceval_step_suf st c1 continuation n suf
              else match continuation with (* Backtrack non-deterministic choice *)
                | [] => Fail (* No remaining non-deterministic choices to execute *)
                | (st', c') :: continuation' => ceval_step_suf st' c' continuation' n suf
              end
          end
  end.

Definition ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  ceval_step_suf st c continuation i None.

(* EXTRA: optimizes a given arithmetic expression *)
Fixpoint optimize_aexp (a: aexp) : aexp :=
  match a with
  | <{a1 + a2}> =>
    match (optimize_aexp a1, optimize_aexp a2) with
    | (ANum a1, ANum a2) => ANum (a1 + a2)
    | (a1, a2) => <{a1 + a2}>
    end
  | <{a1 - a2}> =>
    match (optimize_aexp a1, optimize_aexp a2) with
    | (ANum a1, ANum a2) => ANum (a1 - a2)
    | (a1, a2) => <{a1 - a2}>
    end
  | <{a1 * a2}> => 
    match (optimize_aexp a1, optimize_aexp a2) with
    | (ANum a1, ANum a2) => ANum (a1 * a2)
    | (a1, a2) => <{a1 * a2}>
    end
  | a => a
  end.


(* EXTRA: optimizes a given boolean expression *)
Fixpoint optimize_bexp (b: bexp) : bexp :=
  match b with
  | <{a1 = a2}> =>
    match (optimize_aexp a1, optimize_aexp a2) with
    | (ANum a1, ANum a2) => if a1 =? a2 then <{true}> else <{false}>
    | (a1, a2) => <{a1 = a2}>
    end
  | <{a1 <= a2}> =>
    match (optimize_aexp a1, optimize_aexp a2) with
    | (ANum a1, ANum a2) => if a1 <=? a2 then <{true}> else <{false}>
    | (a1, a2) => <{a1 <= a2}>
    end
  | <{~ b}> =>
    match optimize_bexp b with
    | <{true}> => <{false}>
    | <{false}> => <{true}>
    | b => <{~ b}>
    end
  | <{b1 && b2}> =>
    match (optimize_bexp b1, optimize_bexp b2) with
    | (<{true}>, <{true}>) => <{true}>
    | (<{true}>, <{false}>) => <{false}>
    | (<{false}>, <{true}>) => <{false}>
    | (<{false}>, <{false}>) => <{false}>
    | (b1, b2) => <{b1 && b2}>
    end
  | b => b
  end.

(* EXTRA: optimizes a given command *)
Fixpoint optimize_com (c : com) : com :=
  match c with
  | <{ x := a }> => <{ x := optimize_aexp a }>
  | <{ c1 ; c2 }> => <{ optimize_com c1 ; optimize_com c2 }>
  | <{ if b then c1 else c2 end }> => <{ if optimize_bexp b then optimize_com c1 else optimize_com c2 end }>
  | <{ while b do c1 end }> => <{ while optimize_bexp b do optimize_com c1 end }>
  | <{ c1 !! c2 }> => <{ optimize_com c1 !! optimize_com c2 }>
  | <{ b -> c1 }> => <{ optimize_bexp b -> optimize_com c1 }>
  | c => c
  end.

(* Helper functions that help with running the interpreter *)
Inductive show_result : Type :=
  | OK (st: list (string*nat))
  | KO
  | OOG.

Open Scope string_scope.
Definition run_interpreter (st: state) (c:com) (n:nat) :=
  match (ceval_step st c [] n) with
    | OutOfGas => OOG
    | Fail => KO
    | Success (st', _) => OK [("X", st' X); ("Y", st' Y); ("Z", st' Z)]
  end.

(* Tests are provided to ensure that your interpreter is working for these examples *)
Example test_1: 
  run_interpreter (X !-> 5) <{skip}> 1 = OK [("X", 5); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_2: 
  run_interpreter (X !-> 5) <{ X:= X+1 }> 1 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_3: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 3 = OK [("X", 8); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_4: 
  run_interpreter (X !-> 5) <{ X:= X+1; X:=X+2; Y:=Y+1 }> 2 = OOG.
Proof. auto. Qed.

Example test_5:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 2 = KO.
Proof. auto. Qed.

Example test_6:
  run_interpreter (X !-> 5) <{ X:= X+1; X=5 -> skip }> 1 = OOG.
Proof. auto. Qed.

Example test_7:
  run_interpreter (X !-> 5) <{ X:= X+1; X=6 -> skip }> 3 = OK [("X", 6); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_8:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 4 = OOG.
Proof. auto. Qed.

Example test_9:
  run_interpreter (X !-> 5) <{ (X := 1 !! X := 2); (X = 2) -> X:=3 }> 5 = OK [("X", 3); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

Example test_10:
  run_interpreter (X !-> 5) <{ (X:=1 !! (X:=2; Y:=1)); X=2 -> skip }> 5 = OK [("X", 2); ("Y", 1); ("Z", 0)].
Proof. auto. Qed.

Example test_11:
  run_interpreter (X !-> 5) 
  <{  while ~(X = 0) do 
        X:=X-1; Y:=Y+1
      end;
      Y=5 -> skip
  }>
  8 
  = OK [("X", 0); ("Y", 5); ("Z", 0)].
Proof. auto. Qed.

Example test_12:
  run_interpreter (X !-> 0) 
  <{(X := 0 !! X := 1);
     X := X + 1;
     X = 2 -> skip
  }>
  8 
  = OK [("X", 2); ("Y", 0); ("Z", 0)].
Proof. auto. Qed.

(**
  2.2. TODO: Prove p1_equals_p2. Recall that p1 and p2 are defined in Imp.v
*)

(* c1 and c2 are considered equivalent if, given the same initial state 
and the same number of steps, they produce the same result *)
Definition cequiv (c1 c2 : com) : Prop :=
  ∀ (st st' : state),
    (∀ (X : string), st X = st' X) ->
    ∀ (i : nat), ceval_step st c1 [] i = ceval_step st' c2 [] i.

Lemma basic_assignment: forall (st : state) cont
  (n : nat) (x : string) (i : nat),
  i >= 1 ->
  ceval_step st <{ x := n }> cont i = Success ((x !-> n ; st), cont).
Proof.
  intros st cont n x i H.
  induction i.
  - lia.
  - simpl. reflexivity.
Qed.

(* Given any command, if there is no gas, then the evaluation returns
outOfGas *)
Lemma out_of_gas: forall (st : state) cont (c : com)
  (n : nat) (x : string) (i : nat),
  i = 0 ->
  ceval_step st c cont i = OutOfGas.
Proof.
  intros st cont c n x i H.
  rewrite H. reflexivity.
Qed.

Lemma seq_assoc: forall st cont c1 c2 c3
  (n : nat) (x : string) (i : nat),
  ceval_step st <{ c1 ; c2 ; c3 }> cont i = ceval_step st <{ c1 ; (c2 ; c3) }> cont i.
Proof.
  intros st cont c1 c2 c3 n x i.
  induction i.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* For all possible states and continuations, there exists an amount of gas i0,
such that any amount of gas i1 greater than or equal to i0, is enough for the evaluation
(with ceval_step) of p1 and p2 to be the same. *)
Theorem p1_equals_p2: forall st cont,
  (exists i0,
    (forall i1, i1 >= i0 -> ceval_step st p1 cont i1 = ceval_step st p2 cont i1)).
Proof.
  intros st cont. exists 5. intros i1 H.
  do 5 (destruct i1; try lia).
  reflexivity.
Qed.

Theorem ceval_step_suf_more: forall i1 i2 st st' c suf cont cont',
  i1 <= i2 ->
  ceval_step_suf st c cont i1 suf = Success (st', cont') ->
  ceval_step_suf st c cont i2 suf = Success (st', cont').
Proof.
  induction i1 as [|i1' IHi1']; intros i2 st st' c suf cont cont' Hle Hceval.
    - (* i1 = 0 *)
      simpl in Hceval.
      discriminate Hceval.
    - (* i1 = S i1 *)
      destruct i2 as [|i2']. inversion Hle.
      assert (Hle': i1' <= i2') by lia.
      destruct c.
      + (* skip *)
        simpl in Hceval. inversion Hceval. reflexivity.
      + (* := *)
        simpl in Hceval. inversion Hceval. reflexivity.
      + (* ; *)
        simpl in Hceval. simpl.
        destruct (ceval_step_suf st c1 cont i1') eqn:Heqst1'o.
        * (* st1'o = Success *)
          destruct s.
          apply (IHi1' i2') in Heqst1'o; try assumption.
          rewrite Heqst1'o. apply (IHi1' i2') in Hceval; assumption.
        * (* st1'o = Fail *)
          discriminate Hceval.
        * (* st1'o = OutOfGas *)
          discriminate Hceval.
      + (* if *)
        simpl in Hceval. simpl.
        destruct (beval st b); apply (IHi1' i2') in Hceval; assumption.
      + (* while *)
        simpl in Hceval. simpl.
        destruct (beval st b); try assumption.
        destruct (ceval_step_suf st c cont i1') eqn:Heqst1'o.
        * (* st1'o = Success *)
          destruct s. apply (IHi1' i2') in Heqst1'o; try assumption.
          rewrite Heqst1'o. apply (IHi1' i2') in Hceval; assumption.
        * (* st1'o = Fail *)
          discriminate Hceval.
        * (* st1'o = Fail *)
          discriminate Hceval.
      + (* !! *)
        apply (IHi1' i2') in Hceval; assumption.
      + (* -> *)
        simpl in Hceval. simpl.
        destruct (beval st b).
        * apply (IHi1' i2') in Hceval; assumption.
        * destruct cont; try discriminate.
          destruct p.
          apply (IHi1' i2') in Hceval; assumption.
Qed.

(**
  2.3. TODO: Prove ceval_step_more.
*)
(* For any two executions of the same program c, starting in the same state st
and with the same list of continuations cont, with different amounts of gas
i1 <= i2, if the execution with i1 succeeds, then the execution with i2
will also succeed, with the same end state and list of continuations *)
Theorem ceval_step_more: forall i1 i2 st st' c cont cont',
  i1 <= i2 ->
  ceval_step st c cont i1 = Success (st', cont') ->
  ceval_step st c cont i2 = Success (st', cont').
Proof.
  unfold ceval_step.
  intros i1 i2 st st' c cont cont' Hle Hceval.
  apply ceval_step_suf_more with (i1:=i1) (i2:=i2) (st:=st) (st':=st') (c:=c) (suf:=None) (cont:=cont) (cont':=cont'); assumption.
Qed.

(* EXTRA: evaluating an arithmetic expression is equivalent to evaluating its optimized counterpart *)
Theorem optimize_aexp_equiv: forall st a,
  aeval st a = aeval st (optimize_aexp a).
Proof.
  intros. induction a; try reflexivity;
  simpl; rewrite IHa1; rewrite IHa2;
  destruct (optimize_aexp a1); try reflexivity;
  destruct (optimize_aexp a2); reflexivity.
Qed.

(* EXTRA: evaluating a boolean expression is equivalent to evaluating its optimized counterpart *)
Theorem optimize_bexp_equiv: forall st b,
  beval st b = beval st (optimize_bexp b).
Proof.
  intros. induction b; try reflexivity.
  - (* = *)
    simpl.
    rewrite optimize_aexp_equiv.
    replace (aeval st a2) with (aeval st (optimize_aexp a2)) by (symmetry; rewrite optimize_aexp_equiv; reflexivity).
    destruct (optimize_aexp a1); try reflexivity.
    destruct (optimize_aexp a2); try reflexivity.
    simpl. destruct (n =? n0)%nat; reflexivity.
  - (* <= *)
    simpl.
    rewrite optimize_aexp_equiv.
    replace (aeval st a2) with (aeval st (optimize_aexp a2)) by (symmetry; rewrite optimize_aexp_equiv; reflexivity).
    destruct (optimize_aexp a1); try reflexivity.
    destruct (optimize_aexp a2); try reflexivity.
    simpl. destruct (n <=? n0)%nat; reflexivity.
  - (* ~ *)
    simpl. rewrite IHb.
    destruct (optimize_bexp b); reflexivity.
  - (* && *)
    simpl. rewrite IHb1. rewrite IHb2.
    destruct (optimize_bexp b1); destruct (optimize_bexp b2); reflexivity.
Qed.

Definition com_equiv (c1 c2 : com) : Prop := forall st i cont suf,
  match (ceval_step_suf st c1 cont i suf, ceval_step_suf st c2 cont i suf) with
  | (Success (st1, _), Success (st2, _)) => st1 = st2
  | (Fail, Fail) => True
  | (OutOfGas, OutOfGas) => True
  | _ => False
  end.

Lemma com_equiv_seq : forall c1 c2 c3 c4,
  com_equiv c1 c3 /\ com_equiv c2 c4 ->
  com_equiv <{c1; c2}> <{c3; c4}>.
Proof.
Admitted.

Theorem optimize_com_equiv: forall c,
  com_equiv c (optimize_com c).
Proof.
  intros.
  induction c; intros.
  - (* skip *)
    unfold com_equiv. destruct i; reflexivity.
  - (* := *)
    unfold com_equiv.
    destruct i; try reflexivity. simpl.
    rewrite optimize_aexp_equiv. reflexivity.
  - (* ; *)
    apply com_equiv_seq. split; assumption.
  - (* if *)
    simpl. unfold com_equiv.
    destruct i; try reflexivity. simpl.
    rewrite <- optimize_bexp_equiv.
    destruct (beval st b).
    + admit.
    + admit.
  - (* while *)
    unfold com_equiv.
    destruct i; try reflexivity. simpl.
    rewrite <- optimize_bexp_equiv.
    destruct (beval st b).
    + admit.
    + reflexivity.
  - (* !! *)
    admit.
  - (* -> *)
    unfold com_equiv.
    destruct i; try reflexivity. simpl.
    rewrite <- optimize_bexp_equiv.
    destruct (beval st b).
    + admit.
    + admit.
Admitted.
