import PossiblyInfiniteTrees.PossiblyInfiniteTree.InfiniteTree

structure PossiblyInfiniteTree (α : Type u) where
  infinite_tree : InfiniteTreeSkeleton (Option α)
  no_orphans : ∀ node : List Nat, infinite_tree node ≠ none -> ∀ parent : { l : List Nat // ∃ diff, diff ++ l = node }, infinite_tree parent ≠ none
  no_holes_in_children : ∀ node : List Nat, ∀ n : Nat, (infinite_tree.children node) n ≠ none -> ∀ m : Fin n, (infinite_tree.children node) m ≠ none

namespace PossiblyInfiniteTree
  def get (tree : PossiblyInfiniteTree α) (node : List Nat) : Option α := tree.infinite_tree node

  def children (tree : PossiblyInfiniteTree α) (node : List Nat) : PossiblyInfiniteList α := {
    infinite_list := tree.infinite_tree.children node,
    no_holes := by apply tree.no_holes_in_children
  }

  theorem children_empty_when_not_existing (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.get node = none -> tree.children node = PossiblyInfiniteList.empty := by
    intro h
    unfold children
    unfold PossiblyInfiniteList.empty
    simp
    apply funext
    intro index
    have dec : Decidable (tree.infinite_tree.children node index = none) := Option.decidable_eq_none
    apply dec.byContradiction
    intro contra
    let parent : { l : List Nat // ∃ diff, diff ++ l = index :: node } := ⟨node, by exists [index]⟩
    have : tree.infinite_tree parent ≠ none := by
      apply no_orphans
      unfold InfiniteTreeSkeleton.children at contra
      exact contra
    contradiction

  theorem children_empty_means_all_following_none (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.children node = PossiblyInfiniteList.empty -> ∀ i, tree.get (i :: node) = none := by
    intro h i
    unfold get
    unfold children at h
    unfold PossiblyInfiniteList.empty at h
    simp at h
    unfold InfiniteTreeSkeleton.children at h
    apply congr h
    rfl

  theorem first_child_none_means_children_empty (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.get (0::node) = none -> tree.children node = PossiblyInfiniteList.empty := by
    intro h
    unfold PossiblyInfiniteList.empty
    unfold children
    unfold InfiniteTreeSkeleton.children
    simp
    apply funext
    intro n
    cases n with
    | zero => exact h
    | succ n =>
      apply Option.decidable_eq_none.byContradiction
      intro contra
      have no_holes := tree.no_holes_in_children node (n+1)
      unfold children at no_holes
      unfold InfiniteTreeSkeleton.children at no_holes
      specialize no_holes contra ⟨0, by simp⟩
      contradiction

  theorem getElem_children_eq_get_tree (tree : PossiblyInfiniteTree α) (node : List Nat) (index : Nat) : (tree.children node).infinite_list index = tree.get (index :: node) := by
    unfold children
    unfold get
    unfold InfiniteTreeSkeleton.children
    simp

  def branches_through (tree : PossiblyInfiniteTree α) (node : List Nat) : Set (PossiblyInfiniteList α) := fun pil =>
    pil.infinite_list ∈ tree.infinite_tree.branches_through node

  def branches (tree : PossiblyInfiniteTree α) : Set (PossiblyInfiniteList α) := fun pil =>
    pil.infinite_list ∈ tree.infinite_tree.branches

  theorem branches_through_eq_union_children (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.branches_through node = fun b => ∃ (i : Nat), b ∈ tree.branches_through (i :: node) := by
    unfold branches_through
    apply funext
    simp
    intro pil
    rw [tree.infinite_tree.branches_through_eq_union_children]
    constructor
    . intro h
      rcases h with ⟨i, h⟩
      exists i
    . intro h
      rcases h with ⟨i, h⟩
      exists i

  def leaves (tree : PossiblyInfiniteTree α) : Set α := fun a => ∃ node : List Nat, tree.get node = some a ∧ tree.children node = PossiblyInfiniteList.empty
end PossiblyInfiniteTree

