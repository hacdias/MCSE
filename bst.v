Require Import Arith.
Require Import List.
Require Import Lia.

(*
  match authors with
    | Henrique Dias
    | Venislav Varbanov
  end.
*)

Inductive tree : Set :=
  | leaf : tree
  | node : tree -> nat -> tree -> tree.

(* Apply condition c on all elements of tree t. *)
Fixpoint tree_forall (c: nat -> Prop) (t: tree) : Prop :=
  match t with
  | leaf => True
  | node l v r =>
      c v /\
      tree_forall c l /\
      tree_forall c r
  end.

(* Recursively check if tree t is a binary search tree. *)
Fixpoint bst (t : tree) : Prop :=
  match t with
  | leaf => True
  | node l v r =>
      tree_forall (fun y => y < v) l /\
      tree_forall (fun y => y > v) r /\
      bst l /\
      bst r
  end.

(* Insert inserts a natural number n in the tree t. *)
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

(* Prove that tree_forall conditions are persisted when inserting. *)
Lemma insert_forall: forall (c: nat -> Prop) (t: tree) (v: nat),
  tree_forall c t -> c v -> tree_forall c (insert v t).
Proof.
  intros.
  induction t.
  - simpl.
    auto.
  - inversion H.
    simpl.
    destruct (v ?= n); simpl; intuition.
Qed.

(* Prove that inserting in a bst produces a bst. *)
Lemma insert_bst: forall (t:tree) (n:nat), bst t -> bst (insert n t).
Proof.
  intros.
  induction t; simpl.
  - auto.
  - inversion H.
    destruct H1, H2.
    destruct (n ?= n0) eqn:eq.
    + assumption.
    + apply nat_compare_lt in eq; simpl; intuition.
      apply (insert_forall (fun y => y < n0) t1 n) in H0; auto.
    + apply nat_compare_gt in eq; simpl; intuition.
      apply (insert_forall (fun y => y > n0) t2 n) in H1; auto.
Qed.

(* Converts tree to list. *)
Fixpoint tree_to_list (t: tree) : list nat :=
  match t with
  | leaf => nil
  | node l v r => tree_to_list(l) ++ (v :: nil) ++ tree_to_list(r)
  end.

(* Convert list to bst. *)
Fixpoint list_to_bst (l: list nat) : tree :=
  match l with
  | nil => leaf
  | cons x xs => insert x (list_to_bst xs)
  end.

(* Sort takes an arbitrary tree and transforms it into a bst. *)
Definition sort (t: tree) : tree := list_to_bst (tree_to_list t).
 
(* Proving that list_to_bst always yields a bst. *)
Lemma list_to_bst_correct: forall (l: list nat), bst (list_to_bst l).
Proof.
  intros.
  induction l; simpl; auto.
  apply (insert_bst (list_to_bst l) a); auto.
Qed.

(* Proving that sort always yields a bst. *)
Lemma sort_correct: forall (t: tree), bst (sort t).

(* HGComment: this Lemma should be a direct consequence of 
   list_to_bst_correct.

   Henrique: I simplified it so it looks like a direct consequence. Not sure if it's
  hwat you meant.
*)

Proof.
  intros; unfold sort.
  apply (list_to_bst_correct (tree_to_list t)).
Qed. 

(* Check if n occurrs in tree t. *)
Fixpoint occurs (n: nat) (t: tree) : Prop :=
  match t with
  | leaf => False
  | node l v r => (v = n) \/ (occurs n l) \/ (occurs n r)
  end.

Lemma insert_occurs : forall (t: tree) (n: nat) (m: nat), occurs n (insert m t) <-> n=m \/ occurs n t.
Proof.
intros.
unfold iff.
split.

intros.
induction t.
simpl.
simpl in H. 
intuition.
simpl.
simpl in H.
case (m?=n0) eqn:C1.
apply nat_compare_eq in C1.
intuition.
simpl in H.
intuition.
simpl in H.
intuition.

intros.
destruct H.
induction t.
simpl.
intuition.
simpl.
case (m?=n0) eqn:C1.
apply nat_compare_eq in C1.
simpl.
subst.
intuition.
simpl.
intuition.
simpl.
intuition.


induction t.
simpl.
intuition.
simpl in H.
intuition.
simpl.
case (m?=n0) eqn:C1.
apply nat_compare_eq in C1.
simpl.
auto.
simpl.
left.
auto.
simpl.
left.
auto.

simpl.
case (m?=n0) eqn:C1.
apply nat_compare_eq in C1.
simpl.
auto.
simpl.
right.
left.
auto.
simpl.
intuition.

simpl.
case (m?=n0) eqn:C1.
apply nat_compare_eq in C1.
simpl.
auto.
simpl.
intuition.
simpl.
intuition.
Qed.

Lemma list_occurs : forall (t: tree) (n: nat), occurs n t <-> In n (tree_to_list t).
Proof.
intros.
unfold iff.
split.

intros.
induction t.
auto.
simpl.
simpl in H.
intuition.
apply in_or_app.
right.
left.
auto.

intros.
induction t.
auto.
simpl.
simpl in H.
apply in_app_or in H.
destruct H. 
right.
left.
intuition.
destruct H.
auto.
right.
right.
intuition.
Qed.

Lemma bst_occurs : forall (l: list nat) (n: nat), In n l <-> occurs n (list_to_bst l).
Proof.
intros.
unfold iff.
split.

intros.
induction l.
auto.
simpl.
simpl in H.
intuition.
apply insert_occurs.
intuition.
apply insert_occurs.
intuition.

intros.
induction l.
auto.
simpl.
simpl in H.
apply insert_occurs in H.
intuition.
Qed.

(* Proves that the sorted version of a tree contains the same elements as the original one. *)
Lemma sorted_occurs : forall (t: tree) (n: nat), occurs n t <-> occurs n (sort t).
Proof.
intros.
unfold iff.
split.

intros.
induction t.
auto.
unfold sort.
apply bst_occurs.
apply list_occurs.
simpl.
auto.

intros.
induction t.
auto.
unfold sort in H.
apply bst_occurs in H.
apply list_occurs in H.
simpl.
auto.
Qed.

(* PART 2 *)

(* Returns the minimal node value in a tree t. *)
Fixpoint treeMin (t: tree): option nat :=
  match t with
  | leaf => None
  | node l v r => match (treeMin l), (treeMin r) with
    | None, None => Some v
    | Some n, None => Some (min v n)
    | None, Some n => Some (min v n)
    | Some n, Some m => Some (min v (min n m))
    end
  end.

(* Given the predicate occurs expressing that an element belongs to a tree,
prove correctness of the treeMin function, i.e. prove that:
– the minimal element belongs to the tree and
– that the values in all nodes are greater or equal than the minimal value.  *)
Lemma treeMin_correct1: forall (t: tree) (n: nat), 
  treeMin t = Some n -> occurs n t.
Proof.
intros.

induction t.
simpl in H.
congruence.

simpl.
simpl in H.
case (treeMin t1) eqn:C1.
case (treeMin t2) eqn:C2.
case (n1?=n2) eqn:C3.

apply nat_compare_eq in C3.
case (n0?=n1) eqn:C4.

apply nat_compare_eq in C4.
subst.
right.
right.
apply IHt2.
inversion H.
f_equal.
symmetry.
apply Nat.min_l.
Nat.solve_min.

apply nat_compare_lt in C4.
subst.
left.
inversion H.
symmetry.
apply Nat.min_l.
Nat.solve_min.

apply nat_compare_gt in C4.
subst.
right.
right.
apply IHt2.
inversion H.
f_equal.
replace (Init.Nat.min n2 n2) with n2.
symmetry.
Nat.solve_min.
Nat.solve_min.

apply nat_compare_lt in C3.
case (n0?=n1) eqn:C4.

apply nat_compare_eq in C4.
subst.
right.
left.
apply IHt1.
inversion H.
f_equal.
symmetry.
apply Nat.min_l.
Nat.solve_min.

apply nat_compare_lt in C4.
left.
inversion H.
symmetry.
apply Nat.min_l.
Nat.solve_min.

apply nat_compare_gt in C4.
right.
left.
apply IHt1.
inversion H.
f_equal.
replace (Init.Nat.min n1 n2) with n1.
symmetry.
Nat.solve_min.
Nat.solve_min.

apply nat_compare_gt in C3.
case (n0?=n2) eqn:C4.

apply nat_compare_eq in C4.
subst.
right.
right.
apply IHt2.
inversion H.
f_equal.
symmetry.
apply Nat.min_l.
replace (Init.Nat.min n1 n2) with n2.
auto.
symmetry.
Nat.solve_min.

apply nat_compare_lt in C4.
left.
inversion H.
symmetry.
apply Nat.min_l.
replace (Init.Nat.min n1 n2) with n2.
auto with arith.
symmetry.
Nat.solve_min.

apply nat_compare_gt in C4.
right.
right.
apply IHt2.
inversion H.
f_equal.
replace (Init.Nat.min n1 n2) with n2.
symmetry.
Nat.solve_min.
symmetry.
Nat.solve_min.

case (n0?=n1) eqn:C3.

apply nat_compare_eq in C3.
subst.
right.
left.
apply IHt1.
inversion H.
f_equal.
symmetry.
Nat.solve_min.

apply nat_compare_lt in C3.
left.
inversion H.
symmetry.
Nat.solve_min.

apply nat_compare_gt in C3.
right.
left.
apply IHt1.
inversion H.
f_equal.
symmetry.
Nat.solve_min.

case (treeMin t2) eqn:C2.
case (n0?=n1) eqn:C3.

apply nat_compare_eq in C3.
subst.
right.
right.
apply IHt2.
inversion H.
f_equal.
Nat.solve_min.

apply nat_compare_lt in C3.
left.
inversion H.
symmetry.
Nat.solve_min.

apply nat_compare_gt in C3.
right.
right.
apply IHt2.
inversion H.
f_equal.
symmetry.
Nat.solve_min.

left.
inversion H.
auto.
Qed.

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