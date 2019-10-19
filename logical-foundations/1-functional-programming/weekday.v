(*
  type: day
*)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(*
  function: next_weekday
*)

Definition next_weekday (d:day) : day := 
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.

(*
  tests
*)

Compute (next_weekday thursday).
Compute (next_weekday tuesday).

Example test_next_weekday:
  (next_weekday (next_weekday thursday)) = saturday.


(*
  proof
*)

Proof. simpl. reflexivity. Qed.
