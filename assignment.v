Require Import Arith.

Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

Fixpoint bst_lt (t: tree) (n: nat) : Prop :=
  match t with
  | leaf => True
  | node l v r =>
      v < n /\
      bst_lt l n /\
      bst_lt r n
  end.

Fixpoint bst_gt (t: tree) (n: nat) : Prop :=
  match t with
  | leaf => True
  | node l v r =>
      v > n /\
      bst_gt l n /\
      bst_gt r n
  end.

(* bst recursively checks if t is a BST *)
Fixpoint bst (t : tree) : Prop :=
  match t with
  | leaf => True
  | node l v r =>
      bst_lt l v /\
      bst_gt r v /\
      bst l /\
      bst r
  end.

(* insert insert a natural number n in the tree t *)
Fixpoint insert (n: nat) (t: tree) : tree :=
  match t with 
  | leaf => node leaf n leaf
  | node l v r => 
      match n ?= v with
        | Eq => node l v r
        | Lt => node (insert n l) v r
        | Gt => node l v (insert n r)
      end
 end.

Lemma bst_left : forall (l r: tree) (v: nat), bst (node l v r) -> bst l.
Proof.
intros.
inversion H.
intuition.
Qed.

Lemma bst_right : forall (l r: tree) (v: nat), bst (node l v r) -> bst r.
Proof.
intros.
inversion H.
intuition.
Qed.

Lemma insert_correct: forall (t:tree) (n:nat), bst t -> bst (insert n t).
Proof.
intros.
induction t.
- simpl.
  auto.
- rewrite <- (bst_right ) in IHt1. simpl.
  destruct (n ?= n0).
  + assumption.
  + rewrite <- IHt1.
(* TODO *)
Admitted.

(*Define a function sort that takes an arbitrary tree and sorts it, i.e. it transforms
it into a binary search tree. Hint: you can define two auxiliary functions,
one that stores the elements of a tree in a list and one that builds a binary
search tree from the elements of a list.*)
Definition sort (t: tree) : tree := (* TODO *) t.

(*Prove that the result of the sort function is always a binary search tree.*)
Lemma sort_correct: forall (t: tree), bst (sort t).
Proof.
(* TODO *)
Admitted. 

(*Given the predicate occurs expressing that an element belongs to a tree *)
Fixpoint occurs (n: nat) (t: tree) : Prop :=
  match t with
  | leaf => False
  | node l v r =>
      match n ?= v with
      | Eq => True
      | Lt => occurs n l
      | Gt => occurs n r
      end
  end.

(* Proves that the sorted version of a tree contains the same elements as the original one. *)
Lemma sorted_occurs : forall (t: tree) (n: nat), occurs n t <-> occurs n (sort t).
Proof.
(* TODO *)
Admitted.

(* PART 2 *)