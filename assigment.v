Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

(* Fixpoint bst (T : tree) : Prop := ... *)