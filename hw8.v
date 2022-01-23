(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Turing.Turing.
Require Import Turing.LangRed.
Require Import Turing.LangDec.

(* ---------------------------------------------------------------------------*)

(* ------------------------ BEGIN UTILITY RESULTS ---------------------- *)
(** See Example 5.26 (pp 237):
    Let <M> = p.

    Function F3 (defined below) maps the input <M> to the output <M, M1>,
    where M1 is the machine that rejects all inputs.
*)

Definition F3 p :=
    encode_pair (p , [[ Build (fun _ => REJECT) ]]).

Lemma false_equiv_reject:
    PRecognizes (fun _ => REJECT) (fun _ => False).
Proof.
    intros.
    apply p_recognizes_def; intros; run_simpl_all.
Qed.

Lemma E_tm_inv:
    forall w,
    E_tm w ->
    exists m, m = decode_machine w /\
    forall i, run m i <> Accept.
Proof.
    intros.
    unfold E_tm in *.
    rewrite is_empty_never_accept_rw in H.
    unfold NeverAccept in *.
    eauto.
Qed.

Lemma EQ_tm_inv:
    forall w,
    EQ_tm w ->
    exists m1 m2, w = encode_pair (encode_machine m1, encode_machine m2) /\
    forall i, run m1 i = Accept <-> run m2 i = Accept.
Proof.
    intros.
    unfold EQ_tm in *.
    destruct (decode_pair w) as (w1, w2) eqn:Hr.
    exists (decode_machine w1).
    exists (decode_machine w2).
    split. {
    run_simpl_all.
    rewrite <- Hr.
    run_simpl_all.
    reflexivity.
    }
    intros.
    unfold Lang, Equiv in *.
    auto.
Qed.


(* Given two machines m1 m2 you will need to show:
    1. Whenever m1 accepts, m2 accepts.
    2. Whenever m2 accepts, m1 accepts.
    Then EQ_tm (m1, m2) holds.
*)
Lemma EQ_tm_def:
    forall m1 m2 w,
    w = encode_pair (encode_machine m1, encode_machine m2) ->
    (forall i, run m1 i = Accept -> run m2 i = Accept) ->
    (forall i, run m2 i = Accept -> run m1 i = Accept) ->
    EQ_tm w.
Proof.
    intros.
    unfold EQ_tm in *.
    destruct (decode_pair w) as (w1, w2) eqn:Hr.
    rewrite H in *.
    run_simpl_all.
    inversion Hr; subst; clear Hr.
    unfold Equiv.
    unfold Lang.
    run_simpl_all.
    split; intros; auto.
Qed.

(**
  To construct a term of E_tm we must show that the machine
  does _not_ accept any input.
  *)
Lemma E_tm_def:
    forall m w,
    w = encode_machine m ->
    (forall i, run m i <> Accept) ->
    E_tm w.
Proof.
    intros.
    unfold E_tm.
    unfold IsEmpty, Empty, Recognizes.
    subst.
    run_simpl_all.
    split; intros. {
    assert (Hx := H0 i).
    contradiction.
    }
    contradiction.
Qed.

Lemma f3_rw:
    forall w,
    F3 w = encode_pair ([[decode_machine w]], [[Build (fun _ => REJECT)]]).
Proof.
    intros.
    run_simpl_all.
    unfold F3.
    reflexivity.
Qed.

Lemma f3_inv:
    forall w m1 m2,
    F3 w = encode_pair ([[m1]], [[m2]]) ->
    w = [[m1]] /\ m2 = Build (fun _ => REJECT).
Proof.
    unfold F3; intros.
    apply encode_pair_ext in H.
    inversion H; subst; clear H.
    apply encode_machine_ext in H2.
    auto.
Qed.
(* -------------------------- END OF UTILITY RESULTS ---------------------- *)



(**

Medium.
* Use E_def, EQ_tm_def to construct an EQ_tm/E_tm.
* Use E_tm_inv, EQ_tm_inv to destruct an EQ/E assumption.
* Use run_simpl_all to simplify assumptions `run (Build _)`.
 *)
Theorem E_tm_red_EQ_tm_1:
  forall w, E_tm w -> EQ_tm (F3 w).
Proof.
  intros. 
  apply E_tm_inv in H. 
  destruct H. destruct H.
  Search EQ_tm.
  apply EQ_tm_def with (m1:= x) (m2:= Build (fun _ : input => REJECT)).
- rewrite f3_rw. 
  rewrite H. 
  reflexivity.
- intros. 
  run_simpl_all. Search Run. 
  assert (Hx:= H0 i).
  contradiction.
- intros. 
  run_simpl_all.
Qed.

(**

Medium.

* Use E_def, EQ_tm_def to construct an EQ_tm/E_tm.
* Use E_tm_inv, EQ_tm_inv to destruct an EQ/E assumption.
* Use run_simpl_all to simplify assumptions `run (Build _)`.


 *)
Theorem E_tm_red_EQ_tm_2:
  forall w, EQ_tm (F3 w) -> E_tm w.
Proof.

Admitted.

(**

Easy. Solve Exercise 5.26 of the book (pp 237).

 *)
Theorem E_tm_red_EQ_tm:
  E_tm <=m EQ_tm.
Proof.
  Search (Reduction). 
  apply reducible_def with (f:= F3).
  split.
- apply E_tm_red_EQ_tm_1.
- apply E_tm_red_EQ_tm_2.

Qed.

(**

Easy. Prove Theorem 5.4 (pp 220) using map-reducibility (Exercise 5.26).

 *)
Theorem thm_5_4:
  ~ Decidable EQ_tm.
Proof.
  apply reducible_undecidable with (A:=E_tm).
  - apply E_tm_red_EQ_tm.
  - apply E_tm_undecidable.
Qed.

(**

Easy. Solve Exercise 5.6 (pp 239; solution in pp 242). You should use `reducible_def` and then unfold Reduction.


 *)
Theorem ex_5_6:
  forall A B C, A <=m B -> B <=m C -> A <=m C.
Proof.
  intros A B C (f, Hab) (g, Hbc).
  apply reducible_def with (f := fun w => g (f w)).
  split; intros.
  - apply Hbc, Hab, H.
  - apply Hbc in H.
    apply Hab in H.
    apply H.
Qed.


(**

Solve Exercise 5.7 (pp 239; solution in pp 242).


 *)
Theorem ex_5_7:
  forall A, Recognizable A -> A <=m compl A -> Decidable A.
Proof.
  intros. 
  Search (Decidable).
  apply recognizable_co_recognizable_to_decidable.
  apply H.
  Search Recognizable. Search compl. 
  apply co_red_2 in H0.
  apply reducible_recognizable in H0.
  apply H0.
  apply H.

Qed.

(**

Easy. Show that every recognizable language is map-reducible to A_tm.


 *)
Theorem ex_5_22_a:
  forall A, Recognizable A -> A <=m A_tm.
Proof.
intros A (M, Hd). apply reducible_def with (f:= fun w => <[ M, w ]> ).
  split.
  - apply accept_to_a_tm. 
    apply Hd.
  - apply a_tm_accept_iff. 
    apply Hd.
Qed.

(**

Easy. Show that every language map-reducible to A_tm is recognizable.

 *)
Theorem ex_5_22_b:
  forall A, A <=m A_tm -> Recognizable A.
Proof.
 intros.
  Search (Recognizable). 
  apply reducible_recognizable in H.
  apply H.
  apply a_tm_recognizable.
Qed.

(**

Easy. Show that A is Turing-recognizable iff A <=m ATM (Exercise 5.22, pp 240).


 *)
Theorem ex_5_22:
  forall A, Recognizable A <-> A <=m A_tm.
Proof.
  split.
  - apply ex_5_22_a.
  - apply ex_5_22_b.
Qed.

(**

Easy. One theorem can help you solve this result.

 *)
Theorem not_dec_to_not_rec:
  forall L, ~ Decidable L -> Recognizable (compl L) -> ~ Recognizable L.
Proof.
  intros.
  unfold not, Recognizable.
  intros.
  apply recognizable_co_recognizable_to_decidable in H1.
  - apply H. contradiction.
  - apply H0.
Qed.


(**

Hard. Easy to solve if done in pen-and-paper first.
Some results needed to prove Exercise 5.22 are helpful here.


 *)
Theorem a_red_not_a_tm:
  forall A B, compl A <=m B -> Recognizable B -> A <=m compl A_tm.
Proof.
  intros. 
  apply ex_5_22 in H0.
  apply co_red_1. apply ex_5_6 with (B:= B).
  apply H.
  apply H0.
Qed.
