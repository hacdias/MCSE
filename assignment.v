Require Import Arith.

Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

(* Define a predicate bst on tree to express that a tree is sorted, i.e. it is a binary
search tree (see http://en.wikipedia.org/wiki/Binary_search_tree for
introduction to binary search trees). Experience of the past has shown that
it works very well if you define bst as a recursive function:
Fixpoint bst (T : tree) : Prop := ... *)

(* Given a condition C, checks if the tree t complies with C. *)
(* Maybe we can avoid checking recursively by changing to Function
and only testing C v. After all, bst already does the checks on the left and right. *)
Fixpoint bst_check (C: nat -> Prop) (t: tree) : Prop :=
  match t with
  | leaf => True
  | node l v r => C v /\ bst_check C l /\ bst_check C r
  end.

Fixpoint bst (T : tree) : Prop :=
  match T with
  | leaf => True
  | node l m r =>
      bst_check (fun y => y < m) l /\
      bst_check (fun y => y > m) r /\
      bst l /\
      bst r
  end.

(* Define a function insert that takes a binary search tree and a natural number
and inserts the number in the right place in the tree. *)

(*
Prove correctness of the insert function that is prove that:
bst t -> bst (insert n t) (for all t:tree, n:nat).
*)

(*Define a function sort that takes an arbitrary tree and sorts it, i.e. it transforms
it into a binary search tree. Hint: you can define two auxiliary functions,
one that stores the elements of a tree in a list and one that builds a binary
search tree from the elements of a list.*)
Definition sort (t: tree) : tree := (* TODO *) t.

(*Prove that the result of the sort function is always a binary search tree. *)

(*Given the predicate occurs expressing that an element belongs to a tree *)
Fixpoint occurs (n: nat) (t: tree) : Prop :=
  match t with
  | leaf => False
  | node l v r =>
      if v =? n then True
      else (occurs n l) \/ (occurs n r)
  end.

(* prove that the sorted version of a tree contains the same elements as the
original one, i.e. prove: “occurs n t <-> occurs n (sort t)” (for all n:nat, t:tree) *)

(* PART 2 *)