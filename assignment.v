Require Import Arith.

Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

Fixpoint tree_forall (c: nat -> Prop) (t: tree) : Prop :=
  match t with
  | leaf => True
  | node l v r =>
      c v /\
      tree_forall c l /\
      tree_forall c r
  end.

(* bst recursively checks if t is a BST *)
Fixpoint bst (t : tree) : Prop :=
  match t with
  | leaf => True
  | node l v r =>
      tree_forall (fun y => y < v) l /\
      tree_forall (fun y => y > v) r /\
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

Lemma insert_tree_forall: forall (c: nat -> Prop) (t: tree) (v: nat),
  tree_forall c t -> c v -> tree_forall c (insert v t).
Proof.
  intros.
  induction t.
  - simpl.
    auto.
  - inversion H.
    simpl.
    destruct (v ?= n); simpl; split; auto; split; intuition.
Qed.

Lemma insert_correct: forall (t:tree) (n:nat), bst t -> bst (insert n t).
Proof.
  intros.
  induction t; simpl.
  - auto.
  - inversion H.
    destruct H1.
    destruct H2.
    destruct (n ?= n0) eqn:eq.
    + assumption.
    + apply nat_compare_lt in eq; simpl; split; auto.
      apply (insert_tree_forall (fun y => y < n0) t1 n) in H0; auto.
    + apply nat_compare_gt in eq; simpl; split; auto.
      apply (insert_tree_forall (fun y => y > n0) t2 n) in H1; auto.
Qed.

Fixpoint tree_to_list (t: tree) : list nat :=
  match t with
  | leaf => nil
  | node l v r => tree_to_list(l) ++ (v :: nil) ++ tree_to_list(r)
  end.

Fixpoint list_to_bst (l: list nat) : tree :=
  match l with
  | nil => leaf
  | cons x xs => insert x (list_to_bst xs)
  end.

(* sort takes an arbitrary tree and transforms it into a bst *)
Function sort (t: tree) : tree := list_to_bst (tree_to_list t).

(* proving that list_to_bst always yields a bst *)
Lemma list_to_bst_correct: forall (l: list nat), bst (list_to_bst l).
Proof.
  intros.
  induction l; simpl; auto.
  apply (insert_correct (list_to_bst l) a); auto.
Qed.

(* proving that sort always yields a bst *)
Lemma sort_correct: forall (t: tree), bst (sort t).
Proof.
  intros.
  induction t; simpl; auto.
  unfold sort.
  apply (list_to_bst_correct (tree_to_list (node t1 n t2))).
Qed. 

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

(*Define a function treeMin that will return the value of the minimal node in a
tree. You may want to use Coq.Arith.Min for the minimum function. Note
that every function in Coq needs to be total and you will need to decide what
this function should return applied on an empty tree. To do this, use the
option type. Check the definition of option by doing Print option. *)
Fixpoint treeMin (t: tree): option nat := (* TODO *) None.

(*
• 
• Given the predicate occurs expressing that an element belongs to a tree,
prove correctness of the treeMin function, i.e. prove that:
– the minimal element belongs to the tree and
– that the values in all nodes are greater or equal than the minimal value. 

Lemma treeMin_correct: forall (t: tree), 
  treeMin t <> None -> occurs (treeMin t) t /\ tree_forall (fun y => y <= (treeMin t)) t. *)

(* Define a function leftmost that given a tree will return a value of its leftmost
node. *)
Fixpoint leftmost (t: tree): option nat := (* TODO *) None.

(* the minimal element of a BST is its leftmost node *)
Lemma leftmost_is_min_bst: forall (t: tree), bst t -> treeMin t = leftmost t.
Proof.
  (* TODO *)
Admitted.

(* search searches a BST t and checks if the number occurs in the tree, leveraging
the fact that t is a bst *)
Fixpoint search (n: nat) (t: tree): Prop := (* TODO *) False.

(* proving that search is correct for bsts *)
Lemma search_eq_occurs: forall (t: tree) (n: nat), bst t -> (occurs n t <-> search n t).
Proof.
  (* TODO *)
Admitted.