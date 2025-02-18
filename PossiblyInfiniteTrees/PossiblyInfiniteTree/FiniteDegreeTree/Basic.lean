import BasicLeanDatastructures.Fin
import BasicLeanDatastructures.Set.Finite

import PossiblyInfiniteTrees.PossiblyInfiniteTree.PossiblyInfiniteTree

structure FiniteDegreeTree (α : Type u) where
  tree : PossiblyInfiniteTree α
  finitely_many_children : ∀ node : List Nat, ∃ k, (tree.children node).infinite_list k = none ∧ ∀ k' : Fin k, (tree.children node).infinite_list k' ≠ none

namespace FiniteDegreeTree
  def get (tree : FiniteDegreeTree α) (node : List Nat) : Option α := tree.tree.get node

  def children (tree : FiniteDegreeTree α) (node : List Nat) : List α :=
    let rec loop (n : Nat) : List α := match eq : (tree.tree.children node).infinite_list n with
      | .none => []
      | .some a =>
        have : Classical.choose (tree.finitely_many_children node) - (n+1) < Classical.choose (tree.finitely_many_children node) - n := by
          apply Nat.sub_add_lt_sub
          . apply Classical.byContradiction
            intro contra
            simp at contra
            have hk_none := (Classical.choose_spec (tree.finitely_many_children node)).left
            have hk_not_none : (tree.tree.children node).infinite_list (Classical.choose (tree.finitely_many_children node)) ≠ none := by
              simp only [PossiblyInfiniteTree.children]
              simp only [PossiblyInfiniteTree.children] at eq
              have goal :=
                tree.tree.no_holes_in_children
                node
                n
                (by rw [eq]; simp)
                ⟨Classical.choose (tree.finitely_many_children node), by
                  cases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ contra) with
                  | inl hl =>
                    simp only [PossiblyInfiniteTree.children] at hk_none
                    rw [hl] at hk_none
                    rw [eq] at hk_none
                    simp at hk_none
                  | inr hr => exact hr
                ⟩
              exact goal
            contradiction
          . simp
        a :: loop (n+1)
    termination_by Classical.choose (tree.finitely_many_children node) - n
    loop 0

    theorem in_children_loop_iff_step (tree : FiniteDegreeTree α) (node : List Nat) : ∀ (el : α) (n : Nat), (el ∈ children.loop tree node n) ↔ ((some el = (tree.tree.children node).infinite_list n) ∨ el ∈ children.loop tree node (n+1)) := by
    intro el n
    cases eq : (tree.tree.children node).infinite_list n with
    | none =>
      simp
      unfold children.loop
      constructor
      . intro contra
        apply False.elim
        simp [eq] at contra
        split at contra
        . contradiction
        case h_2 _ heq =>
          rw [eq] at heq
          contradiction
      . intro h
        let fin : Fin (n+1) := ⟨n, by simp⟩
        have : ¬ (tree.tree.children node).infinite_list fin = none := by
          apply tree.tree.no_holes_in_children
          cases eq2 : (tree.tree.children node).infinite_list (n+1) with
          | none =>
            split at h
            . contradiction
            case a.none.h_2 _ heq =>
              rw [eq2] at heq
              contradiction
          | some a =>
            simp only [PossiblyInfiniteTree.children] at eq2
            rw [eq2]
            simp
        contradiction
    | some a =>
      constructor
      . intro h
        unfold children.loop at h
        split at h
        . contradiction
        case h_2 a' heq =>
          simp at h
          cases h with
          | inl h => apply Or.inl; rw [h, ←eq, heq]
          | inr h => apply Or.inr; apply h
      . intro h
        unfold children.loop
        split
        case h_1 heq => rw [heq] at eq; contradiction
        case h_2 a heq =>
          simp
          cases h with
          | inl h => apply Or.inl; rw [heq] at eq; injection eq with eq; injection h with h; rw [h, eq]
          | inr h => apply Or.inr; apply h

  theorem in_children_loop_iff (tree : FiniteDegreeTree α) (node : List Nat) : ∀ (el : α) (n m : Nat), (el ∈ children.loop tree node n) ↔ ((∃ i : Fin m, some el = (tree.tree.children node).infinite_list (n+i)) ∨ el ∈ children.loop tree node (n+m)) := by
    intro el n m

    induction m with
    | zero => simp; intro i; have contra := i.isLt; contradiction
    | succ m ih =>
      rw [ih]
      constructor
      . intro h
        cases h with
        | inl h =>
          apply Or.inl
          cases h with | intro i hi =>
            exists ⟨i.val, by apply Nat.lt_trans; apply i.isLt; simp⟩
        | inr h =>
          have h_iff_step := (tree.in_children_loop_iff_step node el (n + m)).mp h
          cases h_iff_step with
          | inl h =>
            apply Or.inl
            let fin : Fin (m+1) := ⟨m, by simp⟩
            exists fin
          | inr h => apply Or.inr; apply h
      . intro h
        cases h with
        | inl h =>
          rw [tree.in_children_loop_iff_step]
          rw [← or_assoc]
          apply Or.inl
          cases h with | intro i hi =>
            have fin_cases := i.eq_last_or_prev
            cases fin_cases with
            | inl h => rw [h] at hi; apply Or.inr; apply hi
            | inr h =>
              cases h with | intro j hj =>
                rw [hj] at hi
                apply Or.inl
                exists j
        | inr h =>
          apply Or.inr
          rw [tree.in_children_loop_iff_step]
          apply Or.inr
          apply h

  theorem in_children_iff_loop_index_exists (tree : FiniteDegreeTree α) (node : List Nat) : ∀ (el : α), (el ∈ tree.children node) ↔ (∃ n l, (children.loop tree node n) = el :: l) := by
    intro el
    unfold children
    constructor
    . cases tree.finitely_many_children node with | intro k hk =>
        rw [tree.in_children_loop_iff node el 0 k]
        intro h
        cases h with
        | inr h =>
          simp at h
          unfold children.loop at h
          split at h
          . contradiction
          case h_2 a heq =>
            have contra := hk.left
            rw [heq] at contra
            contradiction
        | inl h =>
          cases h with | intro i hi =>
            simp at hi
            exists i
            exists children.loop tree node (i+1)
            conv => left; unfold children.loop
            split
            case h_1 heq => rw [heq] at hi; contradiction
            case h_2 a heq =>
              simp
              rw [heq] at hi
              injection hi with hi
              rw [hi]
    . intro h
      cases h with | intro n h => cases h with | intro l h =>
        rw [tree.in_children_loop_iff node el 0 n]
        apply Or.inr
        simp
        rw [h]
        simp

  theorem in_children_iff_index_exists (tree : FiniteDegreeTree α) (node : List Nat) : ∀ (el : α), (el ∈ tree.children node) ↔ (∃ n, (tree.tree.children node).infinite_list n = some el) := by
    intro el
    rw [in_children_iff_loop_index_exists]
    constructor
    . intro h
      cases h with | intro n h => cases h with | intro l h =>
        exists n
        unfold children.loop at h
        split at h
        . contradiction
        case h_2 a heq =>
          simp at h
          rw [heq]
          rw [h.left]
    . intro h
      cases h with | intro n h =>
        exists n
        exists children.loop tree node (n+1)
        conv => left; unfold children.loop
        split
        case h_1 heq => rw [heq] at h; contradiction
        case h_2 a heq =>
          simp
          rw [heq] at h
          injection h

  theorem children_empty_when_not_existing (tree : FiniteDegreeTree α) (node : List Nat) : tree.get node = none -> tree.children node = [] := by
    intro h
    unfold children
    unfold children.loop
    unfold get at h
    have : tree.tree.children node = PossiblyInfiniteList.empty := by apply PossiblyInfiniteTree.children_empty_when_not_existing; exact h
    have : (tree.tree.children node).infinite_list 0 = none := by rw [this]; unfold PossiblyInfiniteList.empty; simp
    simp
    rw [this]

  theorem children_empty_means_all_following_none (tree : FiniteDegreeTree α) (node : List Nat) : tree.children node = [] -> ∀ i, tree.get (i :: node) = none := by
    intro h
    unfold children at h
    unfold children.loop at h
    unfold get
    apply PossiblyInfiniteTree.children_empty_means_all_following_none

    have zero_th_child_none : (tree.tree.children node).infinite_list 0 = none := by
      have dec : Decidable ((tree.tree.children node).infinite_list 0 = none) := Option.decidable_eq_none
      apply dec.byContradiction
      intro contra
      split at h
      . contradiction
      . simp at h

    have : ∀ i, (tree.tree.children node).infinite_list i = none := by
      intro i
      cases i with
      | zero => apply zero_th_child_none
      | succ i =>
        have dec : Decidable ((tree.tree.children node).infinite_list (i+1) = none) := Option.decidable_eq_none
        apply dec.byContradiction
        intro contra
        let zero_fin : Fin (i+1) := ⟨0, by simp⟩
        have : ¬ (tree.tree.children node).infinite_list zero_fin = none := by
          apply (tree.tree.children node).no_holes
          apply contra
        contradiction
    unfold PossiblyInfiniteTree.children
    unfold PossiblyInfiniteList.empty
    simp
    apply funext
    unfold PossiblyInfiniteTree.children at this
    simp at this
    apply this

  theorem first_child_none_means_children_empty (tree : FiniteDegreeTree α) (node : List Nat) : tree.get (0::node) = none -> tree.children node = [] := by
    intro h
    have lifted_children_none := tree.tree.first_child_none_means_children_empty node h
    unfold children
    unfold children.loop
    split
    case h_1 _ => rfl
    case h_2 heq => rw [lifted_children_none] at heq; simp [PossiblyInfiniteList.empty] at heq

  theorem getElem_children_eq_loop_at_index (tree : FiniteDegreeTree α) (node : List Nat) (index : Nat) : ∀ c, (children.loop tree node c)[index]? = (children.loop tree node (index + c))[0]? := by
    induction index with
    | zero => simp
    | succ index ih =>
      intro c
      conv => left; unfold children.loop
      split
      case h_1 heq =>
        unfold children.loop
        have : (tree.tree.children node).infinite_list (index + 1 + c) = none := by
          apply Option.decidable_eq_none.byContradiction
          intro contra
          let m : Fin (index + 1 + c) := ⟨c, by simp⟩
          apply (tree.tree.children node).no_holes (index + 1 + c) contra m
          simp [m]
          exact heq
        simp
        rw [this]
      case h_2 heq =>
        simp
        rw [ih]
        rw [Nat.add_assoc, Nat.add_comm c 1]

  theorem getElem_children_eq_getElem_tree_children (tree : FiniteDegreeTree α) (node : List Nat) (index : Nat) : (tree.children node)[index]? = (tree.tree.children node).infinite_list index := by
    unfold children
    rw [getElem_children_eq_loop_at_index]
    simp
    unfold children.loop
    split
    case h_1 heq => rw [heq]; simp
    case h_2 heq => simp; rw [heq]

  theorem getElem_children_eq_get_tree (tree : FiniteDegreeTree α) (node : List Nat) (index : Fin (tree.children node).length) : (tree.children node)[index.val] = tree.get (index.val :: node) := by
    unfold get
    rw [← List.getElem?_eq_getElem]
    rw [getElem_children_eq_getElem_tree_children]
    apply PossiblyInfiniteTree.getElem_children_eq_get_tree

  theorem children_eq_lifted_children (tree : FiniteDegreeTree α) (node : List Nat) : PossiblyInfiniteList.fromList (tree.children node) = tree.tree.children node := by
    rw [PossiblyInfiniteList.eq_iff_same_on_all_indices]
    intro n
    rw [PossiblyInfiniteList.get_fromList_eq_list_getElem]
    apply getElem_children_eq_getElem_tree_children

  def branches_through (tree : FiniteDegreeTree α) (node : List Nat) : Set (PossiblyInfiniteList α) := tree.tree.branches_through node

  def branches (tree : FiniteDegreeTree α) : Set (PossiblyInfiniteList α) := tree.tree.branches

  theorem branches_through_eq_union_children (tree : FiniteDegreeTree α) (node : List Nat) : tree.branches_through node = fun b => ∃ (i : Nat), b ∈ tree.branches_through (i :: node) := by
    unfold branches_through
    rw [tree.tree.branches_through_eq_union_children]

  def leaves (tree : FiniteDegreeTree α) : Set α := tree.tree.leaves

end FiniteDegreeTree

