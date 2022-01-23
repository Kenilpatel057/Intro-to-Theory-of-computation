(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Turing.Util.
Require Import Coq.Lists.List.
Import ListNotations.

(* ---------------------------------------------------------------------------*)




(**

Study the definition of [Turing.Util.pow] and [Turing.Util.pow1]
and then show that [Turing.Util.pow1] can be formulated in terms of
[Turing.Util.pow].
Material: https://gitlab.com/cogumbreiro/turing/blob/master/src/Util.v


 *)
(* I base the solution of this exercise on the material that is given
on the above comment.*) 
Theorem ex1:
  forall (A:Type) (x:A) n, Util.pow [x] n = Util.pow1 x n.
Proof.
   intros.
   induction n.
    - reflexivity.
    - simpl.
      rewrite IHn.
      reflexivity.
Qed.

(**

Study recursive definition of [List.In] and the inductive definition of
[List.Exists]. Then show that [List.In] can be formulated in terms
of [List.Exists].

Material: https://coq.inria.fr/library/Coq.Lists.List.html


 *)
(* Using Exist_cons.*)
Theorem ex2:
  forall (A:Type) (x:A) l, List.Exists (eq x) l <-> List.In x l.
Proof.
  split.
 + intros.
   unfold In.
   induction l.
  - inversion H.
  - apply Exists_cons in H. 
    intuition.
 + intros.  
   induction l.
   - inversion H.
   - apply Exists_cons.
     unfold In in H.
     intuition.
Qed. 
(**

Create an inductive relation that holds if, and only if, element 'x'
appears before element 'y' in the given list.
We can define `succ` inductively as follows:

                                (x, y) succ l
-----------------------R1     ------------------R2
(x, y) succ x :: y :: l       (x, y) succ z :: l

Rule R1 says that x succeeds y in the list that starts with [x, y].

Rule R2 says that if x succeeds y in list l then x succeeds y in a list
the list that results from adding z to list l.


 *)

Inductive succ {X : Type} (x:X) (y:X): list X -> Prop :=
    | cons (l: list X) : succ x y (x :: y :: l) 
    | bills (z: X) (l: list X): succ x y l -> succ x y (z::l).




Theorem succ1:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 3 [1;2;3;4]
     2) ~ succ 2 3 [1;2;3;4]
     *)
     succ 2 3 [1;2;3;4].
Proof.
  apply bills.
  apply cons.
Qed.


Theorem succ2:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 3 []
     2) ~ succ 2 3 []
     *)
     ~ succ 2 3 [].
Proof.
  unfold not.
  intros.
  inversion H.
Qed.


Theorem succ3:
    (* Only one of the following propositions is provable.
       Replace 'False' by the only provable proposition and then prove it:
     1) succ 2 4 [1;2;3;4]
     2) ~ succ 2 4 [1;2;3;4]
     *)
    ~ succ 2 4 [1;2;3;4].
Proof.
  unfold not.
  intros.
  inversion H.
  subst.
  inversion H1.
  subst.
  inversion H2.
  subst.
  inversion H3.
  subst.
  inversion H4.
Qed.


Theorem succ4:
  forall (X:Type) (x y : Type), succ x y [x;y].
Proof.
intros.
constructor.
Qed.


Theorem ex3:
  forall (X:Type) (l1 l2:list X) (x y:X), succ x y (l1 ++ (x :: y :: l2)).
Proof.
intros.
induction l1.
- constructor.
- constructor.
  intuition.
Qed.

Theorem ex4:
  forall (X:Type) (x y:X) (l:list X), succ x y l -> exists l1 l2, l1 ++ (x:: y:: l2) = l.
Proof.
intros.
induction l.
- inversion H.
- inversion H.
  + subst.
    exists [].
    exists l0.
    apply app_nil_l.
  + subst.
    destruct IHl.
    * intuition.
    * destruct H0.
      exists (a::x0).
      exists x1.
      rewrite <- H0.
      intuition.
Qed.



