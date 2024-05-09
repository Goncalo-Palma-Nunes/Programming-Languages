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

Fixpoint ceval_step_opt (st : state) (c : com) (continuation: list (state * com)) (i : nat)
                    : interpreter_result :=
  (* Note: Most of these optimizations are commented out, because
  we wanted to prove them incrementally *)
  match i with
  | 0 => OutOfGas
  | S n => match c with
          | <{ skip }> => Success (st, continuation)

          (* Use optimized aeval *)
          | <{ x := a }> => Success ((x !-> (aeval_opt st a) ; st), continuation) (* Update total_map st with binding *)
          (* | <{ skip; c1 }> => ceval_step_opt st c1 continuation n *)
          (* | <{ c1 ; skip }> => ceval_step_opt st c1 continuation n *)
          | <{ c1 ; c2 }> =>
            LETOPT st' continuation' <== ceval_step_opt st c1 continuation n
            IN ceval_step_opt st' c2 continuation' n
          | <{ if b then c1 else c2 end }> =>
            if beval_opt st b (* Use optimized beval *)
            then ceval_step_opt st c1 continuation n
            else ceval_step_opt st c2 continuation n
          (* | <{ while b do <{ skip }> end }> => 
            if beval_opt st b (* Use optimized beval *)
            then OutOfGas (* Infinite loop *)
            else Success (st, continuation) *)
          | <{ while b do c1 end }> =>
            if beval_opt st b (* Use optimized beval *)
            then
              LETOPT st' continuation' <== ceval_step_opt st c1 continuation n
              IN ceval_step_opt st' c continuation' n (* Repeat while with new state *)
            else Success (st, continuation)
          | <{ c1 !! c2 }> => ceval_step_opt st c1 ( (st, c2) :: continuation) n
          (* | <{ b -> <{ skip }> }> =>
            if (beval_opt st b) (* Use optimized beval *)
              then Success (st, continuation)
              else match continuation with (* Backtrack non-deterministic choice *)
                | [] => Fail (* No remaining non-deterministic choices to execute *)
                | (st', c') :: continuation' => ceval_step_opt st' c' continuation' n
              end *)
          | <{ b -> c1 }> =>
            if (beval_opt st b) (* Use optimized beval *)
              then ceval_step_opt st c1 continuation n
              else match continuation with (* Backtrack non-deterministic choice *)
                | [] => Fail (* No remaining non-deterministic choices to execute *)
                | (st', c') :: continuation' => ceval_step_opt st' <{ c'; c }> continuation' n
              end
          end
  end.

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
          | <{ while b do c1 end }> =>
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


(* Theorem ceval_opt_equals_ceval: forall st c cont n,
  ceval_step st c cont n = ceval_step_opt st c cont n.
Proof.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - destruct c.
    + (* skip *)
      simpl. reflexivity.
    + (* := *)
      simpl. rewrite aeval_equiv with (st:=st) (a:=a). reflexivity.
    + (* ; *)
      admit.
Admitted. *)