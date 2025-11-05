.. coq::


.. coq:: none

   Require Import Coq.Init.Datatypes.
   Require Import Coq.ZArith.ZArith.
   Require Import Coq.Lists.List.
   Import ListNotations. (* from List *)
   Import IfNotations.
   Require Import Coq.Lists.ListSet.

   Require Import Oqarina.core.all.
   Require Import Oqarina.AADL.property_sets.all.
   Require Import Oqarina.coq_utils.all.
   Require Import Oqarina.formalisms.lts.
   Require Import Oqarina.formalisms.DEVS.classic.devs.
   #[local] Open Scope bool_scope.
   Set Implicit Arguments.

   Section DEVS_Coupled.

==============
Coupled models
==============

Coupled models represent a hierarchy of DEVS model.

A coupled DEVS model is an 8-tuple :math:`M=<X,Y,D,\{M_{i}\},Z_{{i, self}},Select>` where

    * X is the set of input events;
    * Y is the set of output events;
    * D is the name set of sub-components;
    * :math:`\{M_{i}\}` is the set of sub-components where for each i ∈ D,  :math:`i\in D,M_{i}` is an atomic DEVS model.
    * :math:`Select:2^{D}\rightarrow D` is the tie-breaking function which defines how to select the event from the set of simultaneous events;
    * I = model influencees

.. coq:: none

   Variable Time : Type.
   Context `{Time_i : TimeClass Time }.
   Context `{Time_ops : TimeOperations Time }.
   Import Time_Notations.

   Variable S : Type.                  (* State Set (S) *)
   Variable X : Type.                  (* Input Set (X) *)
   Variable Y : Type.                  (* Output Set (Y) *)

The state of the resulting DEVS is the combination of the states of all DEVS. From these considerations, one could derive the various functions of the DEVS.

.. coq::

   Definition Q_S : Type := Q Time S.

   Definition S_Combined : Type := list (Q_S).

   Definition Q_Combined : Type := Q Time S_Combined.

   Definition Select_Function :=
       list ((DEVS_Simulator Time S X Y) * (Q_S)) ->
           option ((DEVS_Simulator Time S X Y) * (Q_S)).

   Definition Default_Select_Function : Select_Function :=
       fun l => hd_error l.

   Definition Z_Function := identifier -> Y_output Y -> X. (* XXX simplified here *)

   Definition I_Function := identifier -> list identifier.

   Definition Default_I_Function : I_Function :=
       fun x => [ (*empty_identifier*) ].

   Record DEVS_Coupled_Model := {
       devs_coupled_model_id : identifier ;
       D : list (DEVS_Simulator Time S X Y);
       Select : Select_Function ;
       Z_f : Z_Function ;
       I : I_Function;
   }.

======================
Closure under coupling
======================

From a coupled model, one can build the corresponding atomic model using the "closure under coupling" approach. See chapter 7.2 of Theory of Modeling and Simulation

.. coq::

   Definition e_init (l : list (DEVS_Simulator Time S X Y)) :=
       let e_init_l := map (fun x =>  x.(d).(Q_init).(e)) l in
           time_list_min _ e_init_l.

   Definition Build_Q_init_Combined
       (l : list (DEVS_Simulator Time S X Y)) : Q_Combined :=
       let e_init_v := e_init l in
       let sc := map (fun x =>
           Build_Q x.(d).(Q_init).(st) (x.(d).(Q_init).(e) - e_init_v)%time) l in
           Build_Q sc e_init_v.

   Definition ta_combined
       (l : list (DEVS_Simulator Time S X Y)) (sc : S_Combined) : Time :=
       let ta_combined_v :=
           map2 (fun a b => (a.(d).(ta) b.(st) - b.(e))%time) l sc in
           time_list_min _ ta_combined_v.

   Definition sigma_combined (* debugging *)
       (l : list (DEVS_Simulator Time S X Y))
       (sc : S_Combined)
   :=
       map2 (fun a b => (sigma a.(d) b)) l sc.

   Definition IMM (l : list (DEVS_Simulator Time S X Y)) (sc : S_Combined) :=
       let ta_v := ta_combined l sc in
           filter2 (fun a b => (sigma a.(d) b) ==b ta_v) l sc.

   Definition λ_combined
       (l : list (DEVS_Simulator Time S X Y))
       (select : Select_Function)
       (sc : S_Combined)
   :=
       let imm := IMM l sc in
       let i_star := select imm in
       match i_star with
           | None => no_output Y
           | Some i_star' => (fst i_star').(d).(λ) (snd i_star').(st)
       end.

   Definition δint_combined
       (l : list (DEVS_Simulator Time S X Y))
       (select : Select_Function)
       (I : I_Function)
       (Z_f : Z_Function)
       (sc : S_Combined) : S_Combined
   :=
       let imm := IMM l sc in
       let i_star := select imm in

       match i_star with
       | None => sc (* should not happen *)
       | Some i_star' =>
           let i_star_id := (fst i_star').(devs_simulator_id) (* XXX use get_id*)
           in
           let I_star := I i_star_id in

           let dispatch :=
               (fun (s : Q_S) (ds : DEVS_Simulator Time S X Y)  =>
                   if (identifier_beq ds.(devs_simulator_id) i_star_id)
                       then Build_Q (ds.(d).(δint) s.(st)) Zero

                   else if id_in ds.(devs_simulator_id) I_star
                       then Build_Q
                            (ds.(d).(δext)
                               (Build_Q s.(st) (s.(e) + ta_combined l sc)%time)
                               (Z_f i_star_id ((fst i_star').(d).(λ)
                               (* XXX only iff λ produce a valid message *)
                                               (snd i_star').(st))))
                            Zero

                   else Build_Q s.(st) (s.(e) + ta_combined l sc)%time)
           in

       (* Main processing of δint_combined *)
       map2 dispatch sc l
       end.

   Definition δext_combined
       (l : list (DEVS_Simulator Time S X Y))
       (select : Select_Function)
       (I : I_Function)
       (Z_f : Z_Function)
       (qc : Q_Combined) (x : X)
       : S_Combined
   :=
       let imm := IMM l qc.(st) in
       let i_star := select imm in

       match i_star with
       | None => qc.(st) (* should not happen *)
       | Some i_star' =>
           let i_star_id := (fst i_star').(devs_simulator_id) (* XXX use get_id*) in
           let I_star := I i_star_id in

           let dispatch :=
               (fun (s : Q_S) (ds : DEVS_Simulator Time S X Y)  =>
                   if id_in ds.(devs_simulator_id) (I (Id "_self"))
                       then Build_Q
                           (ds.(d).(δext) (Build_Q s.(st) (s.(e) + qc.(e))%time)
                            x (* should be Zself,i*))
                       Zero

                   else Build_Q s.(st) (s.(e) + qc.(e))%time

               ) in

           (* Main processing of δext_combined *)
           map2 dispatch qc.(st) l

       end.

Hence, one can now build an atomic DEVS from a coupled DEVS using
:coq:`Maps_DEVS_Coupled_Model`.

.. coq::

   Definition Map_DEVS_Coupled_Model
       (dc : DEVS_Coupled_Model) : DEVS_Atomic_Model Time S_Combined X Y := {|
           devs_atomic_id := dc.(devs_coupled_model_id);
           Q_init := Build_Q_init_Combined dc.(D);
           ta := ta_combined dc.(D);
           δint := δint_combined dc.(D) dc.(Select) dc.(I) dc.(Z_f) ;
           λ := λ_combined dc.(D) dc.(Select) ;
           δext := δext_combined dc.(D) dc.(Select) dc.(I) dc.(Z_f) ;
       |}.

   Inductive DEVS_Coupled_Debug : Type :=
       dbg_coupled  : identifier -> Q_S -> DEVS_Coupled_Debug.

   Definition Print_DEVS_Coupled_Debug
       (dc : DEVS_Coupled_Model)
       (dc_sim : DEVS_Simulator Time S_Combined X Y)
   :=
       let devs_names := map (fun x => x.(devs_simulator_id)) dc.(D) in
       let devs_dbg : list (Q_S) := dc_sim.(cs).(st) in
       map2 (fun x y =>  dbg_coupled x y) devs_names devs_dbg.

.. coq:: none

   End DEVS_Coupled.
