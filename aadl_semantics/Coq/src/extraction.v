(* extraction.v *)

From Coq Require Extraction.
Require Coq.extraction.ExtrOcamlBasic.
Require Coq.extraction.ExtrOcamlString.

Require Import aadl.
Require Import aadl_declarative.
Require Import aadl_wf.

Extraction Library aadl.
Extraction Library aadl_declarative.
Extraction Library aadl_wf.

Extraction Library identifiers.