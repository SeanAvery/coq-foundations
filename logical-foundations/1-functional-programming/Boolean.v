
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

(*
  Exercise 1
  on should return true if either or both of its inputs are false.
*)


Definition nandb (b1:bool) (b2:bool) : bool :=
  negb(b1 && b2).


Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
