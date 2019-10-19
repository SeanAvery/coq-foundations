
(*
  type: boolean
*)

Inductive bool : Type := 
  | true
  | false.


(*
  definitions
*)

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with 
  | true => b2
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) : bool := 
  match b1 with
  | true => true
  | false => b2
  end.

(*
  tests
*)

Example test_negb: (negb true) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb: (andb true false) = false.
Proof. simpl. reflexivity. Qed.


(*
  Notation
*)

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb2: false || false || true = true.
Proof. simpl. reflexivity. Qed.
