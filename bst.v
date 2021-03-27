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
    case (m ?= n0) eqn:eq; simpl; auto.
    apply nat_compare_eq in eq.
    subst.
    auto.
  - induction t; simpl; auto.
    case (m ?= n0) eqn:eq; simpl; auto; simpl in H0; intuition.
  - induction t; simpl; auto.
    simpl in H.
    intuition.
    simpl in H.
    case (m ?= n0) eqn:eq in H; simpl in H; intuition.
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
  induction t; simpl; auto.
  - simpl in H.
    congruence.
  - simpl in H.
    case (treeMin t1) eqn:C1.
    + case (treeMin t2) eqn:C2.
      case (n1 ?= n2) eqn:C3.
      * apply nat_compare_eq in C3.
        case (n0 ?= n1) eqn:C4.
        { apply nat_compare_eq in C4.
          subst.
          right.
          right.
          apply IHt2.
          inversion H.
          f_equal.
          symmetry.
          lia. }
        { apply nat_compare_lt in C4.
          subst.
          left.
          inversion H.
          lia. }
        { apply nat_compare_gt in C4.
          subst.
          right.
          right.
          apply IHt2.
          inversion H.
          f_equal.
          lia. }
      * apply nat_compare_lt in C3.
        case (n0 ?= n1) eqn:C4.
        { apply nat_compare_eq in C4.
          subst.
          right.
          left.
          apply IHt1.
          inversion H.
          f_equal.
          lia. }
        { apply nat_compare_lt in C4.
          left.
          inversion H.
          lia. }
        { apply nat_compare_gt in C4.
          right.
          left.
          apply IHt1.
          inversion H.
          f_equal.
          lia. }
      * apply nat_compare_gt in C3.
        case (n0 ?= n2) eqn:C4.
        { apply nat_compare_eq in C4.
          subst.
          right.
          right.
          apply IHt2.
          inversion H.
          f_equal.
          lia. }
        { apply nat_compare_lt in C4.
          left.
          inversion H.
          lia. }
        { apply nat_compare_gt in C4.
          right.
          right.
          apply IHt2.
          inversion H.
          f_equal.
          lia. }
      * case (n0 ?= n1) eqn:C3.
        { apply nat_compare_eq in C3.
          subst.
          right.
          left.
          apply IHt1.
          inversion H.
          f_equal.
          lia. }
        { apply nat_compare_lt in C3.
          left.
          inversion H.
          lia. }
        { apply nat_compare_gt in C3.
          right.
          left.
          apply IHt1.
          inversion H.
          f_equal.
          lia. }
    + case (treeMin t2) eqn:C2.
      case (n0 ?= n1) eqn:C3.
      * apply nat_compare_eq in C3.
        subst.
        right.
        right.
        apply IHt2.
        inversion H.
        f_equal.
        lia.
      * apply nat_compare_lt in C3.
        left.
        inversion H.
        lia.
      * apply nat_compare_gt in C3.
        right.
        right.
        apply IHt2.
        inversion H.
        f_equal.
        lia.
      * left.
        inversion H.
        auto.
Qed.

(* TODO: explain perhaps better name *)
Function helperGE (n : option nat) (m : option nat) : Prop :=
  match n, m with
    | None, None => False
    | Some a, None => False
    | None, Some b => True
    | Some a, Some b => match (a ?= b) with 
      | Eq => True
      | Lt => False
      | Gt => True
  end
end.

Lemma treeMin_correct2: forall (t: tree) (n: nat), 
  helperGE (treeMin t) (Some n) -> tree_forall (fun y => n <= y) t.
Proof.
  intros.
  induction t; simpl; intuition.
  - simpl in H.
    case (treeMin t1) eqn:C1.
    + case (treeMin t2) eqn:C2.
      simpl in H.
      case (Init.Nat.min n0 (Init.Nat.min n1 n2) ?= n) eqn:C3; intuition.
      * apply nat_compare_eq in C3; lia.
      * apply nat_compare_gt in C3; lia.
      * simpl in H.
        case (Init.Nat.min n0 n1 ?= n) eqn:C3; try lia.
        apply nat_compare_eq in C3; lia.
        apply nat_compare_gt in C3; lia.
    + case (treeMin t2) eqn:C2.
      simpl in H.
      case (Init.Nat.min n0 n1 ?= n) eqn:C3; intuition.
      * apply nat_compare_eq in C3; lia.
      * apply nat_compare_gt in C3; lia.
      * simpl in H.
        case (n0 ?= n) eqn:C3; try lia.
        apply nat_compare_eq in C3; lia.
        apply nat_compare_gt in C3; lia.
  - simpl in H.
    case (treeMin t1) eqn:C1.
    + case (treeMin t2) eqn:C2.
      simpl in H.
      case (Init.Nat.min n0 (Init.Nat.min n1 n2) ?= n) eqn:C3; intuition.
      * apply nat_compare_eq in C3.
        apply IHt1.
        inversion C3.
        simpl.
        case (n1 ?= Init.Nat.min n0 (Init.Nat.min n1 n2)) eqn:C4; try lia.
        apply nat_compare_lt in C4; lia.
      * apply IHt1.
        simpl.
        case (n1 ?= n) eqn:C4; try lia.
        apply nat_compare_lt in C4.
        apply nat_compare_gt in C3.
        lia.
      * simpl in H.
        case (Init.Nat.min n0 n1 ?= n) eqn:C3; try lia.
        apply IHt1.
        simpl.
        case (n1 ?= n) eqn:C4; try lia.
        apply nat_compare_lt in C4.
        apply nat_compare_eq in C3.
        lia.
        apply IHt1.
        simpl.
        case (n1 ?= n) eqn:C4; try lia.
        apply nat_compare_lt in C4.
        apply nat_compare_gt in C3.
        lia.
    + case (treeMin t2) eqn:C2l.
      simpl in H.
      case (Init.Nat.min n0 n1 ?= n) eqn:C3; try lia.
      apply nat_compare_eq in C3.
      apply IHt1.
      simpl.
      simpl in IHt2.
      case (n1 ?= n) eqn:C4; try lia; simpl.
      auto.
      apply IHt1.
      simpl.
      auto.
  - simpl in H.
    case (treeMin t1) eqn:C1.
      + case (treeMin t2) eqn:C2.
        * simpl in H.
          case (Init.Nat.min n0 (Init.Nat.min n1 n2) ?= n) eqn:C3; try lia.
          apply nat_compare_eq in C3.
          apply IHt2.
          simpl.
          case (n2 ?= n) eqn:C4; auto.
          apply nat_compare_lt in C4.
          lia.
          apply IHt2.
          simpl.
          case (n2 ?= n) eqn:C4; auto.
          apply nat_compare_lt in C4.
          apply nat_compare_gt in C3.
          lia.
        * apply IHt2.
          simpl.
          auto.
      + case (treeMin t2) eqn:C2.
        * simpl in H.
          case (Init.Nat.min n0 n1 ?= n) eqn:C3; try lia.
          apply nat_compare_eq in C3.
          apply IHt2.
          simpl.
          case (n1 ?= n) eqn:C4; auto.
          apply nat_compare_lt in C4.
          lia.
          apply IHt2.
          simpl.
          case (n1 ?= n) eqn:C4; auto.
          apply nat_compare_lt in C4.
          apply nat_compare_gt in C3.
          lia.
        * apply IHt2.
          simpl.
          auto.
Qed.

(* TOO: explain and give better name *)
Lemma treeMin_correct3: forall (t: tree) (n: nat), 
  treeMin t = Some n -> helperGE (treeMin t) (Some n).
Proof.
  intros.
  induction t.
  - simpl.
    auto.
  - simpl in H.
    case (treeMin t1) eqn:C1.
    + case (treeMin t2) eqn:C2; simpl.
      * case (treeMin t1) eqn:C3.
        case (treeMin t2) eqn:C4.
        simpl.
        case (Init.Nat.min n0 (Init.Nat.min n3 n4) ?= n) eqn:C5; auto.
        apply nat_compare_lt in C5; intuition.
        inversion C1.
        inversion C2.
        inversion H.
        subst.
        lia.
        simpl.
        case (Init.Nat.min n0 n3 ?= n) eqn:C5; auto.
        apply nat_compare_lt in C5.
        inversion C1.
        inversion C2.
        case (treeMin t2) eqn:C4.
        inversion C1.
        inversion C2.
      * case (treeMin t1) eqn:C3.
        case (treeMin t2) eqn:C4.
        inversion C1.
        inversion C2.
        inversion C1.
        subst.
        simpl.
        case (Init.Nat.min n0 n1 ?= n) eqn:C5; auto.
        apply nat_compare_lt in C5.
        inversion H.
        lia.
        inversion C1.
    + case (treeMin t2) eqn:C2; simpl.
      * case (treeMin t1) eqn:C3.
        inversion C1.
        case (treeMin t2) eqn:C4.
        inversion C2.
        subst.
        inversion C1.
        simpl.
        case (Init.Nat.min n0 n1 ?= n) eqn:C5; auto.
        apply nat_compare_lt in C5.
        inversion H.
        lia.
        inversion C2.
      * case (treeMin t1) eqn:C3.
        inversion C1.
        case (treeMin t2) eqn:C4.
        inversion C2.
        inversion H.
        subst.
        simpl.
        case (n ?= n) eqn:C5; auto.
        apply nat_compare_lt in C5.
        lia.
Qed.

Lemma treeMin_is_min: forall (t: tree) (n: nat), treeMin t = Some n -> tree_forall (fun y => n <= y) t.
Proof.
  intros.
  apply treeMin_correct2.
  apply treeMin_correct3 in H.
  auto.
Qed.

Lemma treeMin_correct: forall (t: tree) (n: nat), 
  treeMin t = Some n -> occurs n t /\ tree_forall (fun y => n <= y) t.
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

(* Prove that for all trees and two natural numbers n, m, if n occurs in the tree and all elements in the
tree are smaller than m, then n is smaller than m. *)
Lemma occurs_is_lt: forall (t: tree) (n m: nat), occurs n t /\ tree_forall (fun y : nat => y < m) t -> n < m.
Proof.
  intuition.
  induction t.
  - simpl in H0.
    intuition.
  - simpl in H0,H1.
    intuition.
    lia.
Qed.

(* Prove that for all trees and two natural numbers n, m, if n occurs in the tree and all elements in the
tree are larger than m, then n is larger than m. *)
Lemma occurs_is_gt: forall (t: tree) (n m: nat), occurs n t /\ tree_forall (fun y : nat => y > m) t -> n > m.
Proof.
  intuition.
  induction t.
  - simpl in H0.
    intuition.
  - simpl in H0,H1.
    intuition.
    lia.
Qed.

(* the minimal element of a BST is its leftmost node *)
Lemma leftmost_is_min_bst: forall (t: tree), bst t -> treeMin t = leftmost t.
Proof.
  intros.
  induction t; simpl; auto.
  simpl in H.
  intuition.
  case (treeMin t1) eqn:C1.
  - case (treeMin t2) eqn:C2.
    + case (t1) eqn:C3.
        * simpl in C1.
          discriminate.
        * apply treeMin_occurs in C1.
          apply treeMin_occurs in C2.
          assert (CC1 := conj C1 H0).
          apply occurs_is_lt in CC1.
          assert (CC2 := conj C2 H).
          apply occurs_is_gt in CC2.
          replace (Some (Init.Nat.min n (Init.Nat.min n0 n1))) with (Some n0).
          auto.
          f_equal.
          lia.
    + case (t1) eqn:C3.
        * simpl in C1.
          discriminate.
        * apply treeMin_occurs in C1.
          assert (CC1 := conj C1 H0).
          apply occurs_is_lt in CC1.
          replace (Some (Init.Nat.min n n0)) with (Some n0).
          auto.
          f_equal.
          lia.
  - case (treeMin t2) eqn:C2.
    + case (t1) eqn:C3.
        * apply treeMin_occurs in C2.
          assert (CC2 := conj C2 H).
          apply occurs_is_gt in CC2.
          f_equal.
          lia.
        * simpl in C1.
          case (treeMin t3) eqn:C4.
          case (treeMin t4) eqn:C5.
          congruence.
          congruence.
          case (treeMin t4) eqn:C5.
          congruence.
          congruence.
    + case (t1) eqn:C3; auto.
      simpl in C1.
      case (treeMin t3) eqn:C4.
      case (treeMin t4) eqn:C5.
      congruence.
      congruence.
      case (treeMin t4) eqn:C5.
      congruence.
      congruence.
Qed.

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

(* Prove that search is correct for BSTs. *)
Lemma search_eq_occurs: forall (t: tree) (n: nat), bst t -> (occurs n t <-> search n t).
Proof.
  intuition.
  induction t. 
  - simpl. 
    auto. 
  - simpl in H,H0.
    intuition; simpl.
    + case (n ?= n0) eqn:C1; auto.
      apply nat_compare_lt in C1; lia.
      apply nat_compare_gt in C1; lia.
    + case (n ?= n0) eqn:C1; auto.
      apply nat_compare_gt in C1.
      assert (C := conj H0 H1).
      apply occurs_is_lt in C; lia.
    + case (n ?= n0) eqn:C1; auto.
      apply nat_compare_lt in C1.
      assert (C := conj H0 H).
      apply occurs_is_gt in C; lia.
  - induction t; simpl; auto. 
    simpl in H,H0.
    intuition.
    case (n ?= n0) eqn:C1; auto.
    apply nat_compare_eq in C1.
    left.
    auto.
Qed.