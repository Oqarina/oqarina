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

Require Import Oqarina.core.all.

Section Examples.

  Example test_split_fq_colons_1 :
    split_fq_colons nil EmptyString "Hello" None = FQN nil (Id "Hello") None.
  Proof.
    trivial.
  Qed.

  Example test_split_fq_colons_2:
    split_fq_colons nil EmptyString "Hello::World" None = FQN (Id "Hello" :: nil) (Id "World") None.
  Proof.
    trivial.
  Qed.

  Example test_split_fq_colons_3:
    split_fq_colons nil EmptyString "A::B::C::D" None = FQN (Id "A" :: Id "B" :: Id "C" :: nil) (Id "D") None.
  Proof.
    trivial.
  Qed.

  Example test_split_fq_colons_4:
    split_fq_colons nil EmptyString "" None = FQN nil (Id "") None.
  Proof.
    trivial.
  Qed.

  Example test_parse_fq_name_1 : parse_fq_name "Foo.impl" = FQN nil (Id "Foo") (Some (Id "impl")).
  Proof.
    trivial.
  Qed.

  Example test_parse_fq_name_2 : parse_fq_name "Foo::Bar.impl" = FQN (Id "Foo" :: nil) (Id "Bar") (Some (Id "impl")).
  Proof.
    trivial.
  Qed.

End Examples.
