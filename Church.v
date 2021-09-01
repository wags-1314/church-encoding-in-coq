Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(* \f\x.x *)
Definition zero : cnat :=
  fun (X : Type)(f : X -> X)(x : X) => x.

(* \f\x.f x *)
Definition one : cnat :=
  fun (X : Type)(f : X -> X)(x : X) => f x.

(* \f\x.f (f x) *)
Definition two : cnat :=
  fun (X : Type)(f : X -> X)(x : X) => f (f x).

(* \f\x.f (f (f x)) *)
Definition three : cnat :=
  fun (X : Type)(f : X -> X)(x : X) => f (f (f x)).

Definition succ(n: cnat) : cnat :=
  fun (X: Type) (f: X -> X) (x : X) => f (n X f x).

Compute succ one.

Definition plus(m n: cnat) : cnat :=
  fun (X: Type) (f: X -> X) (x : X) => m X f (n X f x).

Example zero_plus_one : plus zero one = one.
Proof. reflexivity. Qed.

Example two_p_three_eq_three_p_two : plus two three = plus three two.
Proof. reflexivity. Qed.

Example assoc_test : plus one (plus two three) = plus (plus one two) three.
Proof. reflexivity. Qed.

Definition multiply(m n: cnat) : cnat :=
  fun (X: Type) (f: X -> X) (x : X) => m X (n X f) x.

Definition cbool := forall X : Type, X -> X -> X.

Definition true : cbool :=
  fun (X : Type) (t f: X) => t.

Definition false : cbool :=
  fun (X : Type) (t f: X) => f.

Definition not (b : cbool) :=
  fun (X : Type) (t f: X) => b X f t.

Example not_involutive : not (not true) = true.
Proof. reflexivity. Qed.

Definition and (b c : cbool) :=
  fun (X: Type) (t f: X) => b X (c X t f) f.

Definition or (b c : cbool) := 
  fun (X: Type) (t f: X) => b X t (c X t f).

Example and_comm : and true false = and false true.
Proof. reflexivity. Qed.

Definition xor (b c : cbool) := 
  fun (X: Type) (t f: X) => b X ((not c) X t f) (c X t f).

Example xor_test : xor true true = false.
Proof. reflexivity. Qed.

End Church.








