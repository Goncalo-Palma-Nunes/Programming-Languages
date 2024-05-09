From FirstProject Require Import Maps Imp.
From Coq Require Import Lists.List. Import ListNotations.

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".


(* ================================================================= *)
(** ** Evaluation as a Relation *)

(** We'll use the notation [st1 / q1 =[ c ]=> st2 / q2 / r] for the [ceval] relation:
    [st1 / q1 =[ c ]=> st2 / q2 / r] means that executing program [c] in a starting
    state [st1] with continuations [q1] results in an ending state [st2] with unexplored
    continuations [q2]. Moreover the result of the computation will be [r].*)

(* Type of result *)
Inductive result : Type :=
| Success
| Fail.

(* Notation that we use *)
Reserved Notation "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r"
(at level 40,
 q1 constr at next level,
 c custom com at level 99, 
 st2 constr at next level,
 q2 constr at next level,
 r constr at next level).

(* 
3. TODO: Define the relational semantics (ceval) to support the required constructs.
*)

Inductive ceval : com -> state -> list (state * com) -> 
          result -> state -> list (state * com) -> Prop :=
| E_Skip : forall st q,
  (* Skip always succeeds *)
 st / q =[ skip ]=> st / q / Success

| E_Asgn : forall st q X a,
  (* Assignment always succeeds *)
 st / q =[ X := a ]=> (X !-> aeval st a ; st) / q / Success

(*************************************
        Sequence Rules
**************************************)

| E_Seq : forall st1 q1 c1 st2 q2 c2 st3 q3 r,
  (* if first command succeeds, the end result is the same as the result
   or running the second command after the first *)
  st1 / q1 =[ c1 ]=> st2 / q2 / Success ->
  st2 / q2 =[ c2 ]=> st3 / q3 / r ->
  st1 / q1 =[ c1 ; c2 ]=> st3 / q3 / r

| E_SeqFT : forall st1 q1 c1 st2 q2 c2,
  (* if first command fails, the sequence fails *)
  st1 / q1 =[ c1 ]=> st2 / q2 / Fail ->
  st1 / q1 =[ c1 ; c2 ]=> st2 / q2 / Fail

(*************************************
              If Rules
**************************************)

| E_IfTrue : forall st st' q q' b c1 c2 r,
  (* if the condition is true, the result is the same as running the first command *)
  beval st b = true ->
  st / q =[ c1 ]=> st' / q' / r ->
  st / q =[ if b then c1 else c2 end ]=> st' / q' / r

| E_IfFalse : forall st st' q q' b c1 c2 r,
  (* if the condition is false, the result is the same as running the second command *)
  beval st b = false ->
  st / q =[ c2 ]=> st' / q' / r ->
  st / q =[ if b then c1 else c2 end ]=> st' / q' / r

(*************************************
              While Rules
**************************************)

| E_WhileFalse : forall b st q c,
  (* if the condition is false, the result is success and neither the
  state nor the continuation list are changed *)
  beval st b = false ->
  st / q =[ while b do c end ]=> st / q / Success

| E_WhileTrueSucceed : forall b st1 q1 c st2 q2 st3 q3 r,
  (* if the condition is true and the command succeeds, the result is the same as
  running the command again with the new state *)
  beval st1 b = true -> (* If true *)
  st1 / q1 =[ c ]=> st2 / q2 / Success -> (* Execute c *)
  st2 / q2 =[ while b do c end ]=> st3 / q3 / r -> (* Start next iteration with new state *)
  st1 / q1 =[ while b do c end ]=> st3 / q3 / r

| E_WhileTrueFail : forall b st1 q1 c st2 q2,
  (* if the condition is true and the command fails, the result is fail *)
  beval st1 b = true -> (* If true *)
  st1 / q1 =[ c ]=> st2 / q2 / Fail -> (* Execute c *)
  st1 / q1 =[ while b do c end ]=> st2 / q2 / Fail

(*************************************
        Non Deterministic Choice
               Rules
**************************************)

| E_NonDet1 : forall st st' q q'' c1 c2 r,
(* Result is the same as the result of running the command picked
non deterministically, with state st and continuation list q *)
  st / q =[ c1 ]=> st' / q'' / r -> (* Should q = ((st, c2) :: q) *)
  st / q =[ c1 !! c2 ]=> st' / ((st, c2) :: q'') / r

| E_NonDet2 : forall st st' q q'' c1 c2 r,
(* Result is the same as the result of running the command picked
non deterministically, with state st and continuation list q *)
  st / q =[ c2 ]=> st' / q'' / r ->
  st / q =[ c1 !! c2 ]=> st' / ((st, c1) :: q'') / r

(*************************************
          Conditional Guard
               Rules
**************************************)

| E_GuardTrue : forall st st' q q' b c r,
  beval st b = true -> (* if the guard condition is true *)
  st / q =[ c ]=> st' / q' / r ->
  st / q =[ (b -> c) ]=> st' / q' / r

| E_GuardFalse_NoCont : forall st st' q b c,
  beval st b = false -> (* if the guard condition is false *)
  q = [] -> (* No remaining non-deterministic choices to execute *)
  st / q =[ (b -> c) ]=> st' / q / Fail

| E_GuardFalse_Cont : forall st st' st'' st''' q q' q'' q''' b c c' r,
  beval st b = false -> (* if the guard condition is false *)
  q = (st'', c') :: q'' -> (* Get the next state and command *)
  st / q'' =[ c' ]=> st''' / q''' / r -> (* Backtrack *)
  st''' / q''' =[ (b -> c) ]=> st' / q' / r -> (* Retry with new state *)
  st / q =[ (b -> c) ]=> st' / q' / r (* Success depends on result of backtracking*)
(*
  We ought to:
    - start at state st / q
    - See that beval st b = false
    - backtrack to state st / q' and execute command c
        - q' is q without the state we are now backtracking to 
    - Get to a new state st' / q'
  *)


(* TODO. Hint: follow the same structure as shown in the chapter Imp *)
where "st1 '/' q1 '=[' c ']=>' st2 '/' q2 '/' r" := (ceval c st1 q1 r st2 q2).


(**
  3.1. TODO: Use the new relational semantics to prove the examples
             ceval_example_if, ceval_example_guard1, ceval_example_guard2,
             ceval_example_guard3 and ceval_example_guard4.
*)

Example ceval_example_seq_asgn:
empty_st / [] =[
X := 2;
Y := 3;
Z := 4
]=> (Z !-> 4 ; Y !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* Sequence command *)
    apply E_Seq with (Y !-> 3; X !-> 2) [].
    + (* Assignment command *)
      apply E_Asgn.
    + (* Assignment command *)
      apply E_Asgn.
Qed.

Example ceval_example_seq_asgn':
empty_st / [] =[
X := 2;
Y := 3;
Z := 4
]=> (Z !-> 4 ; Y !-> 3 ; X !-> 2) / [] / Success.
Proof.
  repeat econstructor.
Qed.

Example ceval_example_if:
empty_st / [] =[
X := 2;
if (X <= 1)
  then Y := 3
  else Z := 4
end
]=> (Z !-> 4 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* If command *)
    apply E_IfFalse.
    -- (* Condition evaluation *)
      reflexivity.
    -- (* Else command *)
      apply E_Asgn. 
Qed.

Example ceval_example_if2:
empty_st / [] =[
X := 2;
if (X = 2)
  then Y := 3
  else Z := 4
end
]=> (Y !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* If command *)
    apply E_IfTrue.
    -- (* Condition evaluation *)
      reflexivity.
    -- (* Then command *)
      apply E_Asgn.
Qed.

Example ceval_example_if2':
empty_st / [] =[
X := 2;
if (X = 2)
  then Y := 3
  else Z := 4
end
]=> (Y !-> 3 ; X !-> 2) / [] / Success.
Proof.
  repeat econstructor.
Qed.

Example ceval_example_guard0:
empty_st / [] =[
   X := 4;
   (X = 1) -> X:=3;
   X := 2
]=> (X !-> 4) / [] / Fail. (* also works if end state is empty_st *)
Proof.
  apply E_Seq with (X !-> 4; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* Guard command *)
    apply E_SeqFT.
    apply E_GuardFalse_NoCont.
    -- reflexivity.
    -- reflexivity.
Qed.

Example ceval_example_guard1:
empty_st / [] =[
   X := 2;
   (X = 1) -> X:=3
]=> (empty_st) / [] / Fail.
Proof.
  apply E_Seq with (X !-> 2; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* Guard command *)
    apply E_GuardFalse_NoCont.
    -- reflexivity.
    -- reflexivity.
Qed.

Example ceval_example_guard2:
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  apply E_Seq with (X !-> 2; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* Guard command *)
    apply E_GuardTrue.
    + (* Guard condition *)
      reflexivity.
    + (* Assignment command *)
      apply E_Asgn.
Qed.

Example ceval_example_guard2':
empty_st / [] =[
   X := 2;
   (X = 2) -> X:=3
]=> (X !-> 3 ; X !-> 2) / [] / Success.
Proof.
  repeat econstructor.
Qed. 

(* Pick second command in non-deterministic constructor *)
Example ceval_example_guard3: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  replace (X !-> 3) with (X !-> 3; X !-> 2);
  try apply t_update_shadow. (* Update map with final state *)
  exists [(empty_st, CAsgn X 1)]. (* Final continuation list *)
  apply E_Seq with (X !-> 2; empty_st) [(empty_st, CAsgn X 1)].
  - (* Non-deterministic choice *)
    apply E_NonDet2. 
    apply E_Asgn. (* result depends on result of the command picked *)
  - (* Guard command *)
    apply E_GuardTrue.
    + (* Guard condition *)
      reflexivity.
    + (* Guard assignment *)
      apply E_Asgn.
Qed.

(* Pick first command in non-deterministic constructor *)  
Example ceval_example_guard4: exists q,
empty_st / [] =[
   (X := 1 !! X := 2);
   (X = 2) -> X:=3
]=> (X !-> 3) / q / Success.
Proof.
  exists []. (* Final continuation list *)
  replace (X !-> 3) with (X !-> 3; X !-> 2) by apply t_update_shadow. (* Update map with final state *)
  replace (X !-> 2) with (X !-> 2; X !-> 1) by apply t_update_shadow.
  apply E_Seq with (X !-> 1; empty_st) [(empty_st, CAsgn X 2)].
  - (* Non-deterministic choice *)
    apply E_NonDet1.
    apply E_Asgn. (* result depends on result of the command picked *)
  - (* Guard command *)
    apply E_GuardFalse_Cont with empty_st (X !-> 2; X !-> 1) [] [] <{X := 2}>.
      + reflexivity. (* Guard is false *)
      + reflexivity. (* State to backtrack to *)
      + apply E_Asgn. (* Execute with new context *)
      + apply E_GuardTrue.
        * reflexivity.
        * apply E_Asgn.
Qed.

Example ceval_example_seq_fail: exists q,
empty_st / [] =[
   X := 1;
   (Y := 2; Y := 2);
   (Y = 3) -> Z := 4
]=> (Y !-> 2; X !-> 1) / q / Fail.
Proof.
  exists []. (* Final continuation list *)
  apply E_Seq with (X !-> 1; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* Sequence command *)
    apply E_Seq with (Y !-> 2; Y !-> 2; X !-> 1) [].
    + (* Assignment command *)
      apply E_Seq with (Y !-> 2; X !-> 1) [].
      * (* Assignment command *)
        apply E_Asgn.
      * (* Assignment command *)
        apply E_Asgn.
    + (* Guard command *)
      apply E_GuardFalse_NoCont.
      * reflexivity.
      * reflexivity.
Qed.

Example ceval_example_while1: exists q,
empty_st / [] =[
   X := 1;
    while (X = 5) do X := X + 1 end
]=> (X !-> 1) / q / Success.
Proof.
  exists []. (* Final continuation list *)
  apply E_Seq with (X !-> 1; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* While command *)
    apply E_WhileFalse. reflexivity.
Qed.

Example ceval_example_while2: exists q,
empty_st / [] =[
   X := 1;
    while (X <= 2) do X := X + 1 end
]=> (X !-> 3; X !-> 2; X !-> 1) / q / Success.
Proof.
  exists []. (* Final continuation list *)
  apply E_Seq with (X !-> 1; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* While command *)
    apply E_WhileTrueSucceed with (X !-> 2; X !-> 1; empty_st) [].
    + reflexivity.
    + apply E_Asgn.
    + apply E_WhileTrueSucceed with (X !-> 3; X !-> 2; X !-> 1; empty_st) [].
      * reflexivity.
      * apply E_Asgn.
      * apply E_WhileFalse. reflexivity.
Qed.

Example ceval_example_while3: exists q,
empty_st / [] =[
   X := 1;
    while (X <= 2) do (X = 1) -> (X := X + 1) end
]=> (X !-> 3; X !-> 2; X !-> 1) / q / Fail.
Proof.
  exists []. (* Final continuation list *)
  apply E_Seq with (X !-> 1; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* While command *)
    apply E_WhileTrueSucceed with (X !-> 2; X !-> 1; empty_st) [].
    + reflexivity. (* Condition is true *)
    + apply E_GuardTrue. (* Guard is true *)
      * (* Guard condition *)
        reflexivity.
      * (* Assignment command *)
        apply E_Asgn.
    + apply E_WhileTrueFail. (* Guard is true, but command fails *)
      -- reflexivity. (* Condition is true *)
      -- apply E_GuardFalse_NoCont.
        ++ reflexivity. (* Guard is false *)
        ++ reflexivity. (* No remaining non-deterministic choices *)
Qed.

Example ceval_example_guard_inside_nonDet: exists q,
empty_st / [] =[
   X := 1;
   (((X = 2) -> X := 3) !! ((X = 3) -> X := 2))
]=> (X !-> 1) / q / Fail.
Proof.
  exists [(X !-> 1, <{ X = 3 -> X := 2 }>)]. (* Final continuation list *)
  apply E_Seq with (X !-> 1; empty_st) [].
  - (* Assignment command *)
    apply E_Asgn.
  - (* Non-deterministic choice *)
    apply E_NonDet1.
    apply E_GuardFalse_NoCont.
    + reflexivity. (* Guard is false *)
    + reflexivity. (* No remaining non-deterministic choices *)
Qed.

(* 3.2. Behavioral equivalence *)

(* Two imp commands are said to be equivalent, if, when executed with the same
initial state st1 and continuation list q1, they both reach the same end state
st2 and result, but with different continuation lists *)
Definition cequiv_imp (c1 c2 : com) : Prop := 
forall (st1 st2 : state) q1 q2 result,
(st1 / q1 =[ c1 ]=> st2 / q2 / result) ->
exists q3, 
(st1 / q1 =[ c2 ]=> st2 / q3 / result).

(* Commutativity of program equivalence *)
Definition cequiv (c1 c2 : com) : Prop :=
cequiv_imp c1 c2 /\ cequiv_imp c2 c1.

Infix "==" := cequiv (at level 99).


(**
  3.2. TODO: Prove the properties below.
*)

Property asgn_always_succeeds: forall (st : state) cont
  (n : nat) (x : string) result (st' : state),
  st' = (x !-> n ; st) ->
  st / cont =[ x := n ]=> st' / cont / result ->
  st / cont =[ x := n ]=> st' / cont / Success.
Proof.
  intros st cont n x result st' H H0.
  inversion H0; subst.
  apply H0.
Qed.

Lemma cequiv_ex1:
<{ X := 2; X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  apply conj; (* Prove each side of the /\ in cequiv *)
  unfold cequiv_imp;
  intros st1 st2 q1 q2 result H;
  exists q1.
  - inversion H; subst.
    + inversion H2. subst.
      simpl in *.
      destruct result.
      * inversion H8; subst.
        -- inversion H10. apply E_Asgn.
        -- inversion H3.
      * inversion H8.
        -- inversion H10.
        -- inversion H3.
        -- inversion H3.
    + inversion H7.
  - inversion H. subst.
    simpl in *.
    apply E_Seq with (X !-> 2; st1) q2.
    + assumption.
    + apply E_GuardTrue.
      * reflexivity.
      * apply E_Skip.
Qed.

Lemma cequiv_ex2:
<{ (X := 1 !! X := 2); X = 2 -> skip }> == 
<{ X := 2 }>.
Proof.
  apply conj; (* Prove each side of the /\ in cequiv *)
  unfold cequiv_imp;
  intros st1 st2 q1 q2 result H;  exists q1.
  - inversion H; subst.
    + inversion H2; subst.
      * inversion H9. subst.
        simpl in *.
        inversion H8; subst.
        -- inversion H3.
        -- inversion H11.
        -- inversion H4. subst.
           inversion H5. subst.
           simpl in *.
           inversion H13; subst.
           ++ inversion H15. subst.
              replace (X !-> 2; X !-> 1; st'') with (X !-> 2; st'') by (symmetry; apply t_update_shadow).
              apply E_Asgn.
           ++ inversion H6.
      * inversion H9. subst.
        simpl in *.
        inversion H8; subst; try inversion H3.
        inversion H11. subst.
        apply E_Asgn.
    + inversion H7; subst; inversion H8.
  - inversion H. subst.
    simpl in *.
    apply E_Seq with (X !-> 1; st1) ((st1, <{X := 2}>) :: q2).
    + apply E_NonDet1.
      apply E_Asgn.
    + apply E_GuardFalse_Cont with st1 (X !-> 2; st1) q2 q2 <{X := 2}>.
      * reflexivity.
      * reflexivity.
      * replace (X !-> 2; st1) with (X !-> 2; X !-> 1; st1) by apply t_update_shadow.
        apply E_Asgn.
      * apply E_GuardTrue.
        -- reflexivity.
        -- apply E_Skip.
Qed.

Lemma choice_idempotent: forall c,
<{ c !! c }> == <{ c }>.
Proof.
  intros c.
  apply conj;
  unfold cequiv_imp;
  intros st1 st2 q1 q2 result H.
  - inversion H; subst; eexists; apply H7.
  - eexists. apply E_NonDet1. apply H. 
Qed.

Lemma choice_comm: forall c1 c2,
<{ c1 !! c2 }> == <{ c2 !! c1 }>.
Proof.
  intros c1 c2. (*take c1, c2, without loss of generality *)
  unfold cequiv.
  apply conj;
  unfold cequiv_imp;
  intros st1 st2 q1 q2 result H.
  - inversion H; subst; eexists. (* Right side *)
    + (* Case 1: c1 is chosen *)
      apply E_NonDet2. (* Apply the second choice *)
      apply H7.
    + (* Case 2: c2 is chosen *)
      apply E_NonDet1. (* Apply the first choice *)
      apply H7.
  - inversion H; subst; eexists. (* Left side *)
    + (* Case 1: c2 is chosen *)
      apply E_NonDet2. (* Apply the second choice *)
      apply H7.
    + (* Case 2: c1 is chosen *)
      apply E_NonDet1. (* Apply the first choice *)
      apply H7.
Qed.

Lemma choice_assoc: forall c1 c2 c3,
<{ (c1 !! c2) !! c3 }> == <{ c1 !! (c2 !! c3) }>.
Proof.
  intros c1 c2 c3.
  apply conj;
  unfold cequiv_imp;
  intros st1 st2 q1 q2 result H.
  - inversion H; subst. inversion H7; subst; eexists. (* Right side *)
    +
      apply E_NonDet1. (* Apply the first choice *)
      apply H8.
    +
      apply E_NonDet2. (* Apply the second choice *)
      apply E_NonDet1.
      apply H8.
    +
      eexists.
      apply E_NonDet2. (* Apply the second choice *)
      apply E_NonDet2.
      apply H7.
  - inversion H; subst.
    + eexists.
      apply E_NonDet1.
      apply E_NonDet1.
      apply H7.
    + inversion H7; subst; eexists.
      -- 
        apply E_NonDet1.
        apply E_NonDet2.
        apply H8.
      -- 
        apply E_NonDet2.
        apply H8.
Qed.


Lemma choice_seq_distr_l: forall c1 c2 c3,
<{ c1 ; (c2 !! c3)}> == <{ (c1;c2) !! (c1;c3) }>.
Proof.
  intros c1 c2 c3.
  apply conj;
  unfold cequiv_imp;
  intros st1 st2 q1 q2 result H; inversion H; subst.
  - 
    inversion H8; subst.
    + eexists.
      apply E_NonDet1.
      apply E_Seq with st3 q3.
      * assumption.
      * apply H9.
    + eexists.
      apply E_NonDet2.
      apply E_Seq with st3 q3.
      * assumption.
      * apply H9.
  - 
    eexists.
    apply E_NonDet2.
    apply E_SeqFT.
    apply H7.
  - 
    inversion H7; subst.
    + eexists.
      apply E_Seq with st3 q2.
      * apply H2.
      * apply E_NonDet1.
        apply H9.
    + eexists.
      apply E_SeqFT.
      apply H8.
  - 
    inversion H7; subst.
    + eexists.
      apply E_Seq with st3 q2.
      * apply H2.
      * apply E_NonDet2.
        apply H9.
    + eexists.
      apply E_SeqFT.
      apply H8.
Qed.

Lemma choice_congruence: forall c1 c1' c2 c2',
c1 == c1' -> c2 == c2' ->
<{ c1 !! c2 }> == <{ c1' !! c2' }>.
Proof.
  intros c1 c1' c2 c2' H1 H2.
  apply conj;
  unfold cequiv_imp;
  intros st1 st2 q1 q2 result H; inversion H; subst; eexists.
  + apply E_NonDet1.
    replace c1' with c1.
    -- apply H9.
    -- admit. 
  + apply E_NonDet2.
    replace c2' with c2.
    -- apply H9.
    -- admit.
  + apply E_NonDet1.
    replace c1 with c1'.
    -- apply H9.
    -- admit.
  + apply E_NonDet2.
    replace c2 with c2'.
    -- apply H9.
    -- admit.
Admitted.

Theorem skip_left : forall c,
  <{ skip ; c }> == c.
Proof.
  intros c.
  apply conj;
  unfold cequiv_imp;
  intros st1 st2 q1 q2 result H.
  - inversion H; subst.
    + inversion H2; subst.
      exists q2.
      apply H8.
    + inversion H7.
  - exists q2.
    apply E_Seq with st1 q1.
    + apply E_Skip.
    + apply H.
Qed.