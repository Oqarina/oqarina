(***
 * Oqarina
 * Copyright 2021 Carnegie Mellon University.
 *
 * NO WARRANTY. THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING
 * INSTITUTE MATERIAL IS FURNISHED ON AN "AS-IS" BASIS. CARNEGIE MELLON
 * UNIVERSITY MAKES NO WARRANTIES OF ANY KIND, EITHER EXPRESSED OR
 * IMPLIED, AS TO ANY MATTER INCLUDING, BUT NOT LIMITED TO, WARRANTY OF
 * FITNESS FOR PURPOSE OR MERCHANTABILITY, EXCLUSIVITY, OR RESULTS
 * OBTAINED FROM USE OF THE MATERIAL. CARNEGIE MELLON UNIVERSITY DOES NOT
 * MAKE ANY WARRANTY OF ANY KIND WITH RESPECT TO FREEDOM FROM PATENT,
 * TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 *
 * Released under a BSD (SEI)-style license, please see license.txt or
 * contact permission@sei.cmu.edu for full terms.
 *
 * [DISTRIBUTION STATEMENT A] This material has been approved for public
 * release and unlimited distribution.  Please see Copyright notice for
 * non-US Government use and distribution.
 *
 * This Software includes and/or makes use of the following Third-Party
 * Software subject to its own license:
 *
 * 1. Coq theorem prover (https://github.com/coq/coq/blob/master/LICENSE)
 * Copyright 2021 INRIA.
 *
 * 2. Coq JSON (https://github.com/liyishuai/coq-json/blob/comrade/LICENSE)
 * Copyright 2021 Yishuai Li.
 *
 * DM21-0762
***)

(*| .. coq:: none |*)
(** Coq Library *)
Require Import Coq.Strings.String.
Require Import List.
Import ListNotations. (* from List *)

(* Coq Ext-lib *)
Require Import ExtLib.Structures.Monads.
(*
Require Import ExtLib.Data.Monads.OptionMonad.
*)
(*| .. coq:: |*)

(*| This module adds a monad-compatible map function to the monad library from Coq.ExtLib.  |*)

Section monadic_map.

    Variable m : Type -> Type.
    Context {Monad_m : Monad m}.
    (*
    Context {MonadExc_m : MonadExc string m}.
*)
    Import MonadNotation.
    Local Open Scope monad_scope.

    Section mmap.

        Variables (A : Type) (B: Type).
        Variable f: A -> m B.

        Fixpoint mmap (l: list A) {struct l}
            : m (list B)
        :=
            match l with
                | nil => ret nil
                | hd :: tl =>  hd' <- f hd ;; tl' <- (mmap tl) ;; ret (hd' :: tl')
            end.

    End mmap.

End monadic_map.
