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

(*Fixpoint ceval_step_inner (st : state) (c : com) (continuation: list (state * com)) (i : nat) (suffix: option com)
                          : interpreter_result :=
  match i with
  | 0 => OutOfGas
  | S n => match c with
          | <{ skip }> => Success (st, continuation)
          | <{ x := a }> => Success ((x !-> (aeval st a) ; st), continuation) (* Update total_map st with binding *)
          | <{ c1 ; c2 }> =>
              let suffix' := match suffix with
                | Some c' => Some <{ c2; c' }>
                | None => Some c2
              end in match ceval_tep_inner st c1 continuation n suffix' with (* TODO - use LETOPT notations *)
              | Success (st', continuation') => ceval_step_inner st' c2 continuation' n suffix
              | Fail => Fail
              | OutOfGas => OutOfGas
              end
          | CIf b c1 c2 => (* TODO use the Imp language notation *)
              if (beval st b)
                then ceval_step_inner st c1 continuation n suffix
                else ceval_step_inner st c2 continuation n suffix
          | CWhile b c1 => (* TODO use the Imp language notation *)
              if (beval st b)
                then match ceval_step_inner st c1 continuation n suffix with (* TODO use the Imp Notation *)
                | Success (st', continuation') => ceval_step_inner st' c continuation' n suffix (* Repeat while with new state *)
                | Fail => Fail
                | OutOfGas => OutOfGas
                end
                else Success (st, continuation)
          | <{ c1 !! c2 }> =>  ceval_step_inner st c1 ( (st, match suffix with
            | Some c' => <{ (c2; c') }>
            | None => c2
            end) :: continuation) n suffix
          | <{ b -> c1 }> =>
            if (beval st b)
              then ceval_step_inner st c1 continuation n suffix
              else match continuation with (* Backtrack non-deterministic choice *)
                | [] => Fail (* No remaining non-deterministic choices to execute *)
                | (st', c') :: continuation' => ceval_step_inner st' c' continuation' n suffix
              end
          end
  end.

Definition ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  ceval_step_inner st c continuation i None.      
*)

Fixpoint ceval_step (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  match i with
  | 0 => OutOfGas
  | S n => match c with
          | <{ skip }> => Success (st, continuation)
          | <{ x := a }> => Success ((x !-> (aeval st a) ; st), continuation) (* Update total_map st with binding *)
          | <{ c1 ; c2 }> =>
            LETOPT st' continuation' <== ceval_step st c1 continuation n
            IN ceval_step st' c2 continuation' n
          | <{ if b then c1 else c2 end }> =>
            if beval st b
            then ceval_step st c1 continuation n
            else ceval_step st c2 continuation n
          | <{ while b do c1 end }> => (* TODO use the Imp language notation *)
            if beval st b
            then
              LETOPT st' continuation' <== ceval_step st c1 continuation n
              IN ceval_step st' c continuation' n (* Repeat while with new state *)
            else Success (st, continuation)
          | <{ c1 !! c2 }> => ceval_step st c1 ( (st, c2) :: continuation) n
          | <{ b -> c1 }> =>
            if (beval st b)
              then ceval_step st c1 continuation n
              else match continuation with (* Backtrack non-deterministic choice *)
                | [] => Fail (* No remaining non-deterministic choices to execute *)
                | (st', c') :: continuation' => ceval_step st' <{ c'; c }> continuation' n
              end
          end
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

Lemma skip_always_succeeds: forall (st : state) cont (c : com) (c1 : com)
  (n : nat) (x : string) (i : nat),
  ceval_step st c cont i = Success (st, cont) ->
  c1 = <{ skip }> ->
  i >= 1 ->
  ceval_step st <{ c ; c1 }> cont i = Success (st, cont).
Proof.
  intros st cont c c1 n x i H H0 H1.
  induction c.
  - simpl. rewrite H0. destruct i.
    -- lia.
    -- 
Admitted.

Lemma seq_assoc: forall st cont c1 c2 c3
  (n : nat) (x : string) (i : nat),
  ceval_step st <{ c1 ; c2 ; c3 }> cont i = ceval_step st <{ c1 ; (c2 ; c3) }> cont i.
Proof.
  intros st cont c1 c2 c3 n x i.
  induction i.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma seq_skip: forall st cont c1
  (n : nat) (x : string) (i : nat),
  i >= 1 ->
  ceval_step st <{ c1 ; skip }> cont i = ceval_step st c1 cont i.
Proof.
  intros st cont c1 n x i H.
  induction i.
  - simpl. reflexivity.
  - destruct c1.
    -- simpl.
  (* TODO *)
Admitted.

Lemma seq_skip_commutativity: forall st cont c1
  (n : nat) (x : string) (i : nat),
  ceval_step st <{ c1 ; skip }> cont i = ceval_step st <{ skip ; c1 }> cont i.
Proof.
  intros st cont c1 n x i.
  induction i.
  - simpl. reflexivity.
  (* TODO *)
Admitted.


Lemma non_det_assignment : forall st cont
  (n1 n2 : nat) (x1 x2 : string) (i : nat),
  i >= 1 ->
  ceval_step st <{ x1 := n1 !! x2 := n2 }> cont i = Success ((x1 !-> n1 ; st), cont).
Proof.
  intros st cont n1 n2 x1 x2 i H.
  induction i.
  - lia.
  - rewrite <- IHi.
  (* TODO *)
Admitted.

(* Lemma seq_cond_guard: forall st cont c
  (n : nat) (x : string) (i : nat),
  ceval_step st <{ x := n ; x = n -> skip }> cont i = ceval_step st <{ x := n; skip }> cont i.
Proof.
  intros st cont c n x i. *)

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

(*
  assert (H1: exists i2, i1 = S (S (S (S (S i2))))). {
    destruct i1.
    - lia.
    - destruct i1.
      + lia.
      + destruct i1.
        * lia.
        * destruct i1.
          -- lia.
          -- destruct i1.
            ++ lia.
            ++ exists i1. reflexivity.
  }
  destruct H1 as [i2 H1].
  rewrite H1.
  induction i2.
  - simpl.
Admitted.*)

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
  induction i1 as [|i1' IHi1']; intros i2 st st' c cont cont' Hle Hceval.
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
        destruct (ceval_step st c1 cont i1') eqn:Heqst1'o.
        * (* st1'o = Success *)
          destruct s. apply (IHi1' i2') in Heqst1'o; try assumption.
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
        destruct (ceval_step st c cont i1') eqn:Heqst1'o.
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
