Require Import Oqarina.core.all.

(* begin hide *)
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
(* end hide *)