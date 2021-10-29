(* begin hide *)
Require Import Coq.Lists.List.
Import ListNotations. (* from List *)
(* end hide *)

Section BoolList.

    (** [andbl] returns the logical and of a list of bools *)

    Fixpoint andbl (lb : list bool) :=
        match lb with
            | nil => true
            | h :: t => andb h (andbl t)
        end.

End BoolList.
