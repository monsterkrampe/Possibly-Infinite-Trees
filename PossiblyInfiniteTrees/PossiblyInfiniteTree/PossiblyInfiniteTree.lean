import PossiblyInfiniteTrees.PossiblyInfiniteTree.InfiniteTree

structure PossiblyInfiniteTree (α : Type u) where
  infinite_tree : InfiniteTreeSkeleton (Option α)
  no_orphans :
    ∀ node : List Nat, infinite_tree node ≠ none ->
    ∀ parent : { l : List Nat // ∃ diff, diff ++ l = node }, infinite_tree parent ≠ none
  no_holes_in_children :
    ∀ node : List Nat, ∀ n : Nat, (infinite_tree.children node) n ≠ none ->
    ∀ m : Fin n, (infinite_tree.children node) m ≠ none

namespace PossiblyInfiniteTree

  def get (tree : PossiblyInfiniteTree α) (node : List Nat) : Option α := tree.infinite_tree node

  def children (tree : PossiblyInfiniteTree α) (node : List Nat) : PossiblyInfiniteList α := {
    infinite_list := tree.infinite_tree.children node,
    no_holes := by apply tree.no_holes_in_children
  }

  theorem children_empty_of_get_eq_none (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.get node = none -> tree.children node = PossiblyInfiniteList.empty := by
    intro h
    unfold children
    unfold PossiblyInfiniteList.empty
    simp
    apply funext
    intro index
    have dec : Decidable (tree.infinite_tree.children node index = none) := Option.decidableEqNone
    apply dec.byContradiction
    intro contra
    let parent : { l : List Nat // ∃ diff, diff ++ l = index :: node } := ⟨node, by exists [index]⟩
    have : tree.infinite_tree parent ≠ none := by
      apply no_orphans
      unfold InfiniteTreeSkeleton.children at contra
      exact contra
    contradiction

  theorem each_successor_none_of_children_empty (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.children node = PossiblyInfiniteList.empty -> ∀ i, tree.get (i :: node) = none := by
    intro h i
    unfold get
    unfold children at h
    unfold PossiblyInfiniteList.empty at h
    simp at h
    unfold InfiniteTreeSkeleton.children at h
    apply congr h
    rfl

  theorem children_empty_of_first_successor_none (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.get (0::node) = none -> tree.children node = PossiblyInfiniteList.empty := by
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
      apply Option.decidableEqNone.byContradiction
      intro contra
      have no_holes := tree.no_holes_in_children node (n+1)
      unfold children at no_holes
      unfold InfiniteTreeSkeleton.children at no_holes
      specialize no_holes contra ⟨0, by simp⟩
      contradiction

  theorem getElem_children_eq_get (tree : PossiblyInfiniteTree α) (node : List Nat) (index : Nat) : (tree.children node).infinite_list index = tree.get (index :: node) := by
    unfold children
    unfold get
    unfold InfiniteTreeSkeleton.children
    simp

  def branch_address_is_maximal (tree : PossiblyInfiniteTree α) (nodes : InfiniteList Nat) : Prop :=
    ∀ n, tree.get (nodes.take (n+1)).reverse = none -> tree.get (0 :: (nodes.take n).reverse) = none

  def branch_addresses_through (tree : PossiblyInfiniteTree α) (node : List Nat) : Set (InfiniteList Nat) := fun nodes =>
    nodes ∈ InfiniteTreeSkeleton.branch_addresses_through node ∧ tree.branch_address_is_maximal nodes

  def branch_for_address (tree : PossiblyInfiniteTree α) (nodes : InfiniteList Nat) : PossiblyInfiniteList α := {
    infinite_list := tree.infinite_tree.branch_for_address nodes
    no_holes := by
      intro n h m
      exact tree.no_orphans
        (nodes.take n).reverse
        h
        ⟨(nodes.take m.val).reverse, by exists ((nodes.skip m.val).take (n - m.val)).reverse; rw [← List.reverse_append, InfiniteList.combine_skip_take]⟩
  }

  def branches_through (tree : PossiblyInfiniteTree α) (node : List Nat) : Set (PossiblyInfiniteList α) :=
    (tree.branch_addresses_through node).map tree.branch_for_address

  def branches (tree : PossiblyInfiniteTree α) : Set (PossiblyInfiniteList α) := tree.branches_through []

  theorem branch_addresses_through_eq_union_branch_addresses_through_successors (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.branch_addresses_through node = fun nodes => ∃ (i : Nat), nodes ∈ tree.branch_addresses_through (i :: node) := by
    unfold branch_addresses_through
    apply Set.ext
    intro pil
    rw [InfiniteTreeSkeleton.branch_addresses_through_eq_union_branch_addresses_through_successors]
    constructor
    . intro ⟨hl, hr⟩
      rcases hl with ⟨i, hl⟩
      exists i
    . intro h
      rcases h with ⟨i, hl, hr⟩
      constructor
      . exists i
      . exact hr

  theorem branches_through_eq_union_branches_through_successors (tree : PossiblyInfiniteTree α) (node : List Nat) : tree.branches_through node = fun b => ∃ (i : Nat), b ∈ tree.branches_through (i :: node) := by
    unfold branches_through
    rw [branch_addresses_through_eq_union_branch_addresses_through_successors]
    apply Set.ext
    intro pil
    constructor
    . intro ⟨nodes, h, b_eq⟩
      rcases h with ⟨i, h⟩
      exists i
      exists nodes
    . intro h
      rcases h with ⟨i, nodes, h⟩
      exists nodes
      constructor
      . exists i
        exact h.left
      . exact h.right

  def leaves (tree : PossiblyInfiniteTree α) : Set α := fun a => ∃ node : List Nat, tree.get node = some a ∧ tree.children node = PossiblyInfiniteList.empty

end PossiblyInfiniteTree

