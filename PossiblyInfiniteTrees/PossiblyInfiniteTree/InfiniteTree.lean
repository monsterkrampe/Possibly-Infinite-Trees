import BasicLeanDatastructures.Set.Basic

import PossiblyInfiniteTrees.PossiblyInfiniteList.PossiblyInfiniteList

-- NOTE: all finite lists indicating positions are right to left; infinite lists left to right (don't ask)

def InfiniteTreeSkeleton (α : Type u) := (List Nat) -> α

namespace InfiniteTreeSkeleton

  def children (tree : InfiniteTreeSkeleton α) (node : List Nat) : InfiniteList α := fun n => tree (n :: node)

  def branch_addresses_through (node : List Nat) : Set (InfiniteList Nat) := fun nodes =>
    (nodes.take node.length).reverse = node

  def branch_for_address (tree : InfiniteTreeSkeleton α) (nodes : InfiniteList Nat) : InfiniteList α := fun n => tree (nodes.take n).reverse

  def branches_through (tree : InfiniteTreeSkeleton α) (node : List Nat) : Set (InfiniteList α) :=
    (branch_addresses_through node).map tree.branch_for_address

  def branches (tree : InfiniteTreeSkeleton α) : Set (InfiniteList α) := tree.branches_through []

  theorem branch_addresses_through_eq_union_branch_addresses_through_successors (node : List Nat) : branch_addresses_through node = fun nodes => ∃ (i : Nat), nodes ∈ branch_addresses_through (i :: node) := by
    unfold branch_addresses_through
    apply Set.ext
    simp only [List.length_cons, List.reverse_eq_cons_iff, Membership.mem]
    intro nodes
    constructor
    . intro h
      exists nodes node.length
      unfold InfiniteList.take
      rw [List.append_cancel_right_eq]
      rw [← List.reverse_eq_iff]
      exact h
    . intro h
      rcases h with ⟨i, h⟩
      unfold InfiniteList.take at h
      rw [← List.reverse_inj] at h
      rw [List.reverse_append] at h
      rw [List.reverse_append] at h
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.reverse_reverse] at h
      rw [List.cons.injEq] at h
      exact h.right

  theorem branches_through_eq_union_branches_through_successors (tree : InfiniteTreeSkeleton α) (node : List Nat) : tree.branches_through node = fun b => ∃ (i : Nat), b ∈ tree.branches_through (i :: node) := by
    unfold branches_through
    rw [branch_addresses_through_eq_union_branch_addresses_through_successors]
    unfold Set.map
    apply Set.ext
    intro b
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

end InfiniteTreeSkeleton

