Section predicate_logic.
Variable D: Set.
Variable c d e :D.
Variable P Q T: D-> Prop.


Theorem example_12 : (exists x, ~ P x) -> ~forall x, P x.
Proof.
intros.
intro H1.
destruct H as [y H].
 (* this replaces the assumption 
       "exists x : D, ~ P x" 
    by a fresh variable y :D and a hypothesis H : ~ P y
    also try 
       "elim H" and then "intros" and compare
  *)
apply H.
apply H1.
  (* This unifies the "P x" of "H : forall x : D, P x" with the goal "P y" 
     and finds the instantiation of y for x in the hypothesis 
   *)
Qed.

Theorem pred_023 : ((exists x, P x) -> forall x, Q x) -> 
  forall y, P y  -> Q y.
Proof.
intros.
apply H.
exists y.
  (* This says that we take "y" for the existentially quantified variable 
     in the goal
         "exists x : D, P x"
   *)
assumption.
Qed.

Theorem pred_008 : ~(forall x, P x)  -> ~ forall x, P x /\ Q x.
Proof.
Admitted.

Theorem coq_pred_015 : 
  ~(forall x : D, P x \/ (Q x -> T x)) -> ~forall x : D, T x.
Proof.
Admitted.


Theorem pred_025 : ~(forall x, P x /\ Q x) /\ (forall x, P x) -> 
  ~forall x, Q x.
Proof.
Admitted.

(* Note how a binary relation on D is declared in Coq *)
Variable R : D -> D -> Prop.

Theorem pred_031 : (forall x, P x /\ Q x) -> forall x, P x \/ exists y, R x y.
Proof.
Admitted.


Theorem pred_036 : (exists x, forall y, ~R x y) -> ~forall x, R x x.
Proof.
Admitted.


Theorem pred_013 : (exists x, P x \/ Q x) -> (forall x, ~Q x) -> exists x, P x.
Proof.
Admitted.

Theorem pred_035 : (forall y, Q y -> ~exists x, P x) /\ (forall x, P x) -> forall y, ~Q y.
Proof.
Admitted.

(* more difficult *)
Theorem pred_016 : (forall x, P x \/ R x x) -> (forall x, P x -> exists y, R x y /\ R y x) -> forall x, exists y, R x y.
Proof.
Admitted.

Theorem pred_067 : (forall x, ~P x) -> ~exists x, P x.
Proof.
Admitted.

(* Predicate logic with equality *)

Theorem example_14 : forall x y, R y y /\ x = y -> R y x.
Proof.
intros.
destruct H as [H1 H2].
rewrite <- H2 in H1.
rewrite <- H2.
 (* This replaces x by y in the goal
    Also try
      "rewrite <- H2"
    and see what happens
    Also try
      "rewrite <- H2 in H1"
    and see what happens
  *)
assumption.
Qed.


Variable W : D -> D -> D -> Prop.

Theorem example_17 : forall x y, W x x y /\ x = y -> W x y y.
Proof.
Admitted.


Theorem pred_059 : (forall x:D, forall y, x = y) -> (exists x, P x) -> forall x, P x.
Proof.
Admitted.

Theorem pred_058 : (forall x:D, forall y, x = y) /\ P d -> P e.
Proof.
Admitted.

Section pred_080.

Hypothesis Domain : forall x, (x = c \/ x = d \/ x = e).

Theorem pred_080 : (forall x, P x) -> P e /\ P d /\ P c.
Proof.
Admitted.


End pred_080.

(*CHALLENGE PROBLEM
    This theorem shows that if we have a transitive
   relation on a 3-element set, and if each element has
   a successor, then some element must be reflexive for
   this relation *)

Section pred_078.

Hypothesis Domain : exists x1, exists x2, exists x3, forall x:D, (x = x1 \/ x = x2 \/ x = x3).
Hypothesis Successor : forall x, exists y, R x y.
Hypothesis Transitive : forall x, forall y, forall z, R x y /\ R y z -> R x z.

Theorem pred_078 : exists x, R x x.
Proof.
Admitted.

End pred_078.


End predicate_logic.