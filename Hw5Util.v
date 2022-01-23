(*
        #####################################################
        ###  PLEASE DO NOT DISTRIBUTE SOLUTIONS PUBLICLY  ###
        #####################################################
*)

Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope char_scope.

Definition rule := (ascii * list ascii) % type.

Structure grammar := {
    grammar_vars : list ascii;
    grammar_terminals : list ascii;
    grammar_rules : list rule;
    grammar_start : ascii;
}.

Definition g1 := {|
    grammar_vars := ["C"];
    grammar_terminals := ["{"; "}"];
    grammar_start := "C";
    grammar_rules := [
        ("C", ["{"; "C"; "}"]);
        ("C", ["C"; "C"]);
        ("C", [])
    ];
|}.

Inductive Yield (G:grammar) : list ascii -> list ascii -> Prop :=
| yield_def:
    forall u v w A w1 w2,
    In (A, w) (grammar_rules G) ->
    w1 = u ++ [A] ++ v ->
    w2 = u ++ w ++ v ->
    Yield G w1 w2.

Inductive Derivation (G:grammar): list (list ascii) -> Prop :=
| derivation_nil:
    Derivation G [[grammar_start G]]
| derivation_cons:
    forall u v ws,
    Derivation G (u :: ws) ->
    Yield G u v ->
    Derivation G (v :: u :: ws).

Inductive Accept (G:grammar) : list ascii -> Prop :=
| accept_def:
    forall w ws,
    Derivation G (w::ws) ->
    Forall (fun c => List.In c (grammar_terminals G)) w ->
    Accept G w.