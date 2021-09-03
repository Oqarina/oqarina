From ExtLib Require Import
  Data.Monads.EitherMonad
  Data.Monads.StateMonad Structures.Monads.

Require Import List.
Import ListNotations. (* from List *)

Require Import Oqarina.AADL.property_sets.all.
Require Import Oqarina.aadl_dynamic_thread.
Require Import Oqarina.core.all.

Require Import Coq.ZArith.ZArith_base.

Section ThreadStateMonad.

    Import MonadNotation.
    Local Open Scope monad_scope.

    Variable m : Type -> Type.
    Context {Monad_m: Monad m}.
    Context {State_m: MonadState thread_state_variable m}.
    Context {MonadExc_m : MonadExc string m}.

    Inductive thread_action :=
    (* Definition of the "private" RTS of a thread, i.e. the functions that the AADL runtime may manipulate *)

    | th_advance_time : AADL_Time -> thread_action
    | th_store_in : identifier -> bool -> thread_action

    (* Definition of the "public" RTS of a thred, as defined by the AADL standard. *)

    | th_await_dispatch
    | th_get_count : identifier -> thread_action

    (* To crash the thread *)
    | th_crash.

    Fixpoint run_actions' (act : list thread_action): m thread_state_variable :=
        match act with
        | nil =>  v <- MonadState.get ;; ret v
        | h :: t =>
            v <- MonadState.get ;;
            match h with
            | th_store_in id value => MonadState.put (store_in v id value)
            | th_advance_time time => MonadState.put (advance_time v time)
            | _ => raise "kaboom"%string
            end ;;
            run_actions' t
        end.

End ThreadStateMonad.

Existing Instance Monad_stateT.

Definition run_actions (act : list thread_action) (th_state : thread_state_variable) :=
    evalStateT
    (run_actions' (stateT thread_state_variable (sum string)) act) th_state.

Definition main := run_actions [] A_Periodic_Thread_State.
Compute main.

Compute run_actions [ th_store_in  (Id "a_feature") true ;
                   (*   th_crash ; *)
                      th_advance_time 1%Z ]
                        A_Periodic_Thread_State.


