(** %\chapter{p-automata -- Parametric Timed Automata}\label{chap::p-automata}%

    Here, we follow the definition of Parametetric Timed Automata (or p-automata) as defined in %\cite{beerardAutomatedVerificationParametric1999}%. In %\cite{paulin-mohringModelisationTimedAutomata2001}% the authors propose a formalization of p-automata in Coq. In the following, we adapt this formalization to newer versions of Coq and in the context of AADL mechanization. In particular, we XXX

*)

(* begin hide *)
Require Import time.
Import NaturalTime.

Require Import lts.
(* end hide *)

(** * Definition of p-Automata

%In the following, we introduce a general definition of p-automata. Let us note $Var$ the type of variables, $Loc$ the type of locations, and $Act$ the type for transition labels (or actions).

\begin{definition}[invariant]
An invariant is a proposition over a triple $(l,s,v)$ with $l \in Loc$ a location, $s$ the clock value and $v\in Var$ a variable.
\end{definition}% *)

Definition P_Invariant (Var : Type) (Loc : Set) :=
    Loc -> Time -> Var -> Prop.

(**
%\begin{definition}[p-automata transition] A transition takes place at some instant s, it is labeled by an action a, it goes from a location l to a location l' and transforms a variable v into a variable v'.
\end{definition}%
*)

Definition P_Transition (Act : Set) (Var : Type) (Loc : Set) :=
    Act -> Time -> Loc -> Var -> Loc -> Var -> Prop.

(**
%\begin{definition}[p-automata] A p-automata on the $Var$ domain for variables is built from a set $Loc$ of locations, an invariant $Inv$ on these locations, a set of actions, and a set of transitions. \end{definition}%
*)

Module Type Pautomata.

    Parameter Var : Type.
    Parameter Loc : Set.
    Parameter Inv : P_Invariant Var Loc.
    Parameter Act : Set.
    Parameter Trans : P_Transition Act Var Loc.

End Pautomata.
