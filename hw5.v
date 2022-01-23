(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope char_scope.
Require Import Hw5Util.

(* ---------------------------------------------------------------------------*)




(**

Use `yield_def`.
 *)
Theorem yield_eq: forall G A w, List.In (A, w) (Hw5Util.grammar_rules G) -> Hw5Util.Yield G [A] w.
Proof.
  intros.
  apply yield_def with (u:=[]) (v:=[]) (w:=w) (A:=A).
  - apply H.
  - reflexivity.
  - apply app_nil_end.
Qed.

(**
Use `yield_def` and `app_assoc` to correct the parenthesis.
 *)
Theorem yield_right: forall G w1 w2 r w3 w4, Hw5Util.Yield G w1 w2 -> w3 = w1 ++ r -> w4 = w2 ++ r -> Hw5Util.Yield G w3 w4.
Proof.
  intros.
  inversion H; subst; clear H.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  apply yield_def with (u:=u) (v:=v++r) (w:=w) (A:=A).
  - apply H2.
  - reflexivity.
  - reflexivity.
Qed.

(**
Similar proof than `yield_right`, but you should rewrite with
`app_assoc` after using `yield_def`, not before.
 *)
Theorem yield_left: forall G w1 w2 l w3 w4, Hw5Util.Yield G w1 w2 -> w3 = l ++ w1 -> w4 = l ++ w2 -> Hw5Util.Yield G w3 w4.
Proof.
  intros.
  inversion H; subst; clear H.
  apply yield_def with (u:=l++u) (v:=v) (w:=w) (A:=A).
  - apply H2.
  - rewrite app_assoc.
    reflexivity.
  - rewrite app_assoc.
    reflexivity.
Qed.

(**
Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.
 *)
Theorem g1_rule_1: Hw5Util.Yield g1 ["C"] ["{"; "C"; "}"].
Proof.
  apply yield_def with (u:=[]) (v:=[]) (w:=["{"; "C"; "}"]) (A:="C").
  - simpl; auto.
  - reflexivity.
  - reflexivity.
Qed.

(**
Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.
 *)
Theorem g1_rule_2: Hw5Util.Yield g1 ["C"] ["C"; "C"].
Proof.
  apply yield_def with (u:=[]) (v:=[]) (w:=["C"; "C"]) (A:="C").
  - simpl; auto.
  - reflexivity.
  - reflexivity.
Qed.

(**
Consider using one of the lemmas you have just proved.
When your goal is `In ("C", ...) (grammar_rules g1)`, `simpl; auto`
should solve it.
 *)
Theorem g1_rule_3: Hw5Util.Yield g1 ["C"] [].
Proof.
  apply yield_def with (u:=[]) (v:=[]) (w:=[]) (A:="C").
  - simpl; auto.
  - reflexivity.
  - reflexivity.
Qed.

(**
The proof should proceed by inversion and then case analysis on
string `u`.
 *)
Theorem yield_inv_start: forall G w, Hw5Util.Yield G [Hw5Util.grammar_start G] w -> In (Hw5Util.grammar_start G, w) (Hw5Util.grammar_rules G).
Proof.
  intros.
  inversion H; subst; clear H.
  induction u.
  - simpl in *.
    inversion H1; subst; clear H1.
    rewrite <- app_nil_end. 
    apply H0.
  - induction u.
    + inversion H1.
    + inversion H1.
Qed.

(**
You will want to use `yield_inv_start`. Recall that that `List.In`
simplifies to a series of disjunctions.
 *)
Theorem g1_ex1: ~ Hw5Util.Yield g1 ["C"] ["{"].
Proof.
  unfold not.
  intros.
  apply yield_inv_start in H.
  destruct H.
  - inversion H.
  - unfold In in *.
    inversion H.
    + inversion H0.
    + inversion H0.
      * inversion H1.
      * assumption. 
Qed.

(**
The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.
 *)
Theorem g1_step_1: Hw5Util.Yield g1 ["C"; "C"] ["{"; "C"; "}"; "C"].
Proof.
  apply yield_def with (u:=[]) (v:=["C"]) (w:=["{";"C";"}"]) (A:="C").
  - simpl; auto.
  - reflexivity.
  - reflexivity.
Qed.

(**
The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.
 *)
Theorem g1_step_2: Hw5Util.Yield g1 ["{"; "C"; "}"; "C"] ["{"; "}"; "C"].
Proof.
  apply yield_left with (w1:=["C"; "}"; "C"]) (w2:=["}";"C"]) (l:=["{"]).
  - apply yield_def with (u:=[]) (v:=["}";"C"]) (w:=[]) (A:="C").
    + simpl; auto.
    + simpl; auto.
    + simpl. auto. 
  - reflexivity.
  - reflexivity.
Qed.

(**
The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.
 *)
Theorem g1_step_3: Hw5Util.Yield g1 ["{"; "}"; "C"] ["{"; "}"; "{"; "C"; "}"].
Proof.
  apply yield_left with (w1:=["C"]) (w2:=["{"; "C"; "}"]) (l:=["{";"}"]).
  - apply g1_rule_1.
  - reflexivity.
  - reflexivity.
Qed.

(**
The idea is to use either: `yield_left`, `yield_right`, or `yield_def`.
 *)

Theorem g1_step_4: Hw5Util.Yield g1 ["{"; "}"; "{"; "C"; "}"] ["{"; "}"; "{"; "}"].
Proof.

Admitted.

(**
Use either `derivation_nil` or `derivation_cons`.
 *)
Theorem g1_der_1: Hw5Util.Derivation g1 [["C"]].
Proof.
  apply derivation_nil.
Qed.

(**
Use either `derivation_nil` or `derivation_cons`.
 *)
Theorem g1_der_2: Hw5Util.Derivation g1 [["C"; "C"]; ["C"]].
Proof.
  apply derivation_cons.
  - apply derivation_nil.
  - apply g1_rule_2.
Qed.

(**
Use either `derivation_nil` or `derivation_cons`.
 *)
Theorem g1_der_3: Hw5Util.Derivation g1 [["{"; "C"; "}"; "C"]; ["C"; "C"]; ["C"]].
Proof.
  apply derivation_cons.
  - apply g1_der_2.
  - apply g1_step_1.
Qed.


Theorem g1_der_4: Hw5Util.Derivation g1 [
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
  apply derivation_cons.
  - apply g1_der_3.
  - apply g1_step_2.
Qed.


Theorem g1_der_5: Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
  apply derivation_cons.
  - apply g1_der_4.
  - apply g1_step_3.
Qed.


Theorem g1_der_6: Hw5Util.Derivation g1 [
    ["{"; "}"; "{"; "}"];
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
].
Proof.
  apply derivation_cons.
  - apply g1_der_5.
  - apply g1_step_4.
Qed.

(**
Use `g1_der_6`.
 *)



Theorem ex1: Accept g1 ["{"; "}"; "{"; "}"].
Proof.
  apply accept_def with 
  (w:=["{"; "}"; "{"; "}"])
  (ws:= [
    ["{"; "}"; "{"; "C"; "}"];
    ["{"; "}"; "C"];
    ["{"; "C"; "}"; "C"];
    ["C"; "C"];
    ["C"]
  ]).
  - apply g1_der_6.
  - apply Forall_cons.
    + simpl; auto.
    + apply Forall_cons. 
      * simpl; auto.
      * simpl; auto.
Qed.
