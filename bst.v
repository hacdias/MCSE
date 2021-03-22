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

Lemma occurs_insert : forall (t: tree) (n m: nat), m = n \/ occurs n t <-> occurs n (insert m t).
Proof.
  intuition.
  - induction t; simpl; auto.
    case (m?=n0) eqn:eq; simpl; auto.
    apply nat_compare_eq in eq.
    subst.
    auto.
  - induction t; simpl; auto.
    case (m?=n0) eqn:eq; simpl; auto; simpl in H0; intuition.
  - induction t; simpl; auto.
    simpl in H.
    intuition.
    simpl in H.
    case (m?=n0) eqn:eq in H; simpl in H; intuition.
Qed.


Lemma occurs_tree_list : forall (t: tree) (n: nat), occurs n t <-> In n (tree_to_list t).
Proof.
  intuition.
  - induction t; simpl; auto.
    simpl in H.
    intuition.
    apply in_or_app.
    right.
    left.
    auto.
  - induction t; simpl; auto.
    simpl in H.
    apply in_app_or in H.
    destruct H. 
    + right; left; intuition.
    + destruct H; auto.
Qed.

Lemma occurs_list_tree : forall (l: list nat) (n: nat), In n l <-> occurs n (list_to_bst l).
Proof.
  intuition.
  - induction l; simpl; auto.
    simpl in H.
    apply occurs_insert.
    intuition.
  - induction l; simpl; auto.
    apply occurs_insert in H.
    intuition.
Qed.

(* Proves that the sorted version of a tree contains the same elements as the original one. *)
Lemma sorted_occurs : forall (t: tree) (n: nat), occurs n t <-> occurs n (sort t).
Proof.
  intuition.
  - induction t; auto.
    unfold sort.
    apply occurs_list_tree.
    apply occurs_tree_list.
    auto.
  - induction t; auto.
    unfold sort in H.
    rewrite <- occurs_list_tree in H.
    rewrite <- occurs_tree_list in H.
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

Lemma treeMin_occurs: forall (t: tree) (n: nat), treeMin t = Some n -> occurs n t.
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

Lemma treeMin_is_min: forall (t: tree) (n: nat), treeMin t = Some n -> tree_forall (fun y => y <= n) t.
Proof.
  (* TODO *)
Admitted.

Lemma treeMin_correct: forall (t: tree) (n: nat), 
  treeMin t = Some n -> occurs n t /\ tree_forall (fun y => y <= n) t.
Proof.
  intros.
  split.
  - apply treeMin_occurs; auto.
  - apply treeMin_is_min; auto.
Qed.

(* Returns a value of the leftmost node of a tree t. *)
Fixpoint leftmost (t: tree): option nat :=
  match t with
  | leaf => None
  | node l v r => match l with
    | leaf => Some v
    | node _ _ _ => leftmost l
    end
  end.

(* the minimal element of a BST is its leftmost node *)
Lemma leftmost_is_min_bst: forall (t: tree), bst t -> treeMin t = leftmost t.
Proof.
  (* TODO *)
Admitted.

(* Searches a bst t and checks if number n occurs in the tree, leveraging the fact that t is a bst. *)
Fixpoint search (n: nat) (t: tree) : Prop :=
  match t with
  | leaf => False
  | node l v r =>
      match n ?= v with
      | Eq => True
      | Lt => search n l
      | Gt => search n r
      end
  end.

(* proving that search is correct for bsts *)
Lemma search_eq_occurs: forall (t: tree) (n: nat), bst t -> (occurs n t <-> search n t).
Proof.
intuition.
- induction t; simpl; auto.
  simpl in H0.
  case (n ?= n0) eqn:eq; simpl; auto.
  + intuition.
  (* TODO *)
Admitted.