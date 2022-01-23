(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)
Require Import Turing.Turing.

(* ---------------------------------------------------------------------------*)

(* ------------------------ BEGIN OF SAMPLE CODE ---------------------- *)
(* Feel free to delete sample code, it is here merely to give you examples
   of usage. *)
(** When the objective is to show that a language is decidable.
    Write the program Prog that decides that language.
    
    First, show that Prog is a recognizer.
    Second, show that the language accepted by Prog is recognizable.
    Third, show that Prog is a decider.
    *)

Lemma reject_rejects_all:
    PRecognizes (fun _ : input => REJECT)
            (fun _ : input => False).
Proof.
    apply p_recognizes_def.
    - intros.
    (* The program REJECT cannot accept, thus we have a contradiction. *)
    inversion H.
    (* run_simpl_all also takes care of absurd cases for us. *)
    - intros.
    (* This is trivial because False in assumptions *) 
    inversion H. (* run_simpl_all would also work *)
Qed.

Lemma void_is_recognizable:
    Recognizable (fun w => False).
Proof.
    (* If a program P-recognizes a language, then that language
    is also recognizable. *)
    apply p_recognizable_def with (fun i => REJECT).
    apply reject_rejects_all.
Qed.

Lemma void_is_decidable:
    Decidable (fun w => False).
Proof.
    apply p_decidable_def with (p:=fun i => REJECT).
    apply p_decides_def.
    + apply reject_rejects_all.
    + apply p_decider_def.
    intros.
    apply p_halts_reject.
    apply run_ret.
Qed.

Lemma decidable_conj:
    forall L1 L2,
    Decidable L1 ->
    Decidable L2 ->
    Decidable (fun w => L1 w /\ L2 w).
Proof.
    intros.
    (* Get the turing machines out of each decidable *)
    destruct H as (m1, H1).
    destruct H0 as (m2, H2).
    (* Since we need to prove that it is decidable, use definition lemma.
    You must provide the program that decides it. *)
    apply p_decidable_def with (p:=(fun w=> 
    mlet r1 <- Call m1 w in
    mlet r2 <- Call m2 w in
    halt_with (r1 && r2))
    ).
    (* Apply the definition lemma of decides *)
    apply p_decides_def. {
    (* Again, use the definiton lemma for recognizes *) 
    apply p_recognizes_def. {
        intros.
        (* First goal is to show that if the program accepts, then it is in
        the language. *)
        (* Note that run_simpl_all does not handle mlet, so we must use
        inversion directly *)
        inversion H; subst; clear H.
        (* Apply inversion to the second mlet *)
        inversion H7; subst; clear H7.
        (* Now we are ready to simplify our assumptions with run_simpl_all. *)
        run_simpl_all.
        (* We need to prove a conjuction, thus we use split to prove each subgoal. *)
        split.
        - (* Since m1 decides L1 and run accepts i, then i is in L1 *) 
        apply decides_run_accept with (m:=m1); auto.
        - apply decides_run_accept with (m:=m2); auto.
    }
    (* Second goal of recognizing is to show that if the words are in the
        language, we must show that they are accepted by our program.
        It is crucial to understand the definition of Run. *)
    intros.
    (* We have a conjuntion in an assumption, simplify it. *)
    destruct H as (Ha, Hb).
    (* When we have an mlet we must use the constructor that acts according to
        the first operation we are evaluating, in this case [Call m1 i]. 
        Since L1 accepts, we know that we can only apply run_seq_accept *)
    apply run_seq_accept. {
        (* We could prove this with run_call, but then the proof would be longer *)
        Search (Run (Call _ _) Accept). (* A simple search gives us the solution *)
        apply run_call_decides_accept with (L:=L1); auto.
    }
    (* Again we have [mlet r2 <- Call m2 i in ...] *)
    (* We must ask ourselves: is [Call m2 i] accepting, rejecting, or looping?
        Since we have [L2 i], we know that [run m2 i] is accepting it. *)
    apply run_seq_accept. {
        apply run_call_decides_accept with (L:=L2); auto.
    }
    (* Our goal has [halt_with (true && true)]. We must simplify the goal
    then, because [true && true] can still evaluate. *)
    simpl.
    (* We are finally ready to conclude. *)
    Search (Run (halt_with _) _).
    apply run_halt_with_true.
    }
    (* We must now show that our program is a decider. Apply the decider
    definition lemma. *)
    apply p_decider_def.
    intros.
    (* When the goal has a mlet, you will need to search for Seq.
    Unfortunately searching for mlet yields no results. *)
    Search (PHalts (Seq _ _)).
    apply p_halts_seq_call_decider; eauto using decides_to_decider.
    intros.
    apply p_halts_seq_call_decider; eauto using decides_to_decider.
    intros.
    apply p_halts_halt_with.
Qed.
(* -------------------------- END OF SAMPLE CODE ---------------------- *)



(**

Easy.  Show that the language that accepts all words is decidable.

 *)
Theorem ex1:
  Decidable (fun w => True).
Proof.
  apply p_decidable_def with (p := fun _ => ACCEPT).
  apply p_decides_def; intros.
  - apply p_recognizes_def.
    + intros.
      apply I.
    + intros. 
      apply run_ret. 
  - intros.
    apply p_decider_def.
    intros.
    apply p_halts_accept. 
    apply run_ret.
Qed.

(**

Easy. Prove that the program LOOP rejects all words.

 *)
Theorem ex2:
  PRecognizes (fun w=>LOOP) (fun w =>False).
Proof.
  apply p_recognizes_def.
  - intros. inversion H.
  - intros. inversion H.
Qed.

(**

Average. Show that Coq functions are decidable

 *)
Theorem ex3:
  forall f, Decidable (fun i => f i = true).
Proof.
  intros.
  unfold Decidable.
  apply p_decidable_def with (p:=fun i => halt_with(f i)).
  apply p_decides_def.
  apply p_recognizes_def; intros.
  - apply run_halt_with_inv_accept in H.
    apply H.
  - rewrite H.
    apply run_halt_with_true.
  - unfold PDecider.
    intros.
    apply p_halts_halt_with.
Qed.


(**

Easy. Show that any program followed by LOOP also loops.

 *)
Theorem ex4:
  forall p, Run (Seq LOOP p) Loop.
Proof.
  intros.
  apply run_seq_loop.
  apply run_ret.
Qed.
(**

Average. Show that sequencing a program with a loop, also loops. To start your proof you must do a case analysis on what is the outcome of running p.


 *)
Theorem ex5:
  forall p, Run (Seq p (fun b => LOOP)) Loop.
Proof.
  intros.
  destruct (run_exists p).
  induction x.
  - apply run_seq_accept. 
    + apply H.
    + apply run_ret.
  - apply run_seq_reject.
    + apply H.
    + apply run_ret.
  - apply run_seq_loop.
    + apply H.
Qed.


(**

Hard. If a given program decides a language, then negating its result
recognizes the complement of that language.
Make sure you use p_decides_run_reject and p_decides_reject.
In the second branch of proving recognizability, make sure you do a
case analysis on the result of running p with i, that is to say, use:

    destruct (run_exists (p i)) as (r, Hr).


 *)
Theorem ex6_1:
  forall p L, PDecides p L -> PRecognizes (fun i =>
    mlet b <- p i in halt_with (negb b)) (compl L).
Proof.
  intros.
  apply p_recognizes_def; intros.
  - inversion H0.
    subst.
    apply p_decides_run_reject with (i:=i) (p:=p) in H.
    + apply H.
    + run_simpl_all.
      subst.
      run_simpl_all.
      apply H3.
  - destruct (run_exists (p i)) as (r, Hr).
    apply run_seq_reject.
    + apply p_decides_reject with (i:=i) (r:=r) in H.
      * subst.
        apply Hr.
      * apply Hr.
      * apply H0. 
    + apply run_halt_with_true.
Qed.


(**

Easy. This can be solved using 3 lemmas. Make sure you use Search. The difficult part of the proof is on showing the program halts.


 *)
Theorem ex6_2:
  forall p, PDecider p -> PDecider (fun i : input => mlet b <- p i in halt_with (negb b)).
Proof.
  intros.
  apply p_decider_def.
  intros.
  apply p_halts_seq_p_decider.
  - apply H.
  - intros.
    apply p_halts_halt_with.
Qed.


(**

Easy. Use exercises defined before.

 *)
Theorem ex6_3:
  forall p L, PDecides p L -> PDecides (fun i =>
    mlet b <- p i in halt_with (negb b)) (compl L).
Proof.
  intros. 
  apply p_decides_def.
  - apply ex6_1.
    apply H.
  - apply ex6_2.
    apply H.
Qed.
(**

Easy. Prove that if L is decidable, then its complement is also decidable.


 *)
Theorem ex6:
  forall L, Decidable L -> Decidable (compl L).
Proof.
  intros.
  unfold Decidable in H.
  apply decidable_to_p_decides in H.
  destruct H.
  apply ex6_3 with (p:=x) in H.
  apply p_decidable_def with (p := fun i : input => mlet b <- x i in halt_with (negb b)).
  apply H.
Qed.

