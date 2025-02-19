import BasicLeanDatastructures.Set.Basic

import PossiblyInfiniteTrees.PossiblyInfiniteList.PossiblyInfiniteList

-- NOTE: all finite lists indicating positions are right to left; infinite lists left to right (don't ask)

def InfiniteTreeSkeleton (α : Type u) := (List Nat) -> α

namespace InfiniteTreeSkeleton

  def children (tree : InfiniteTreeSkeleton α) (node : List Nat) : InfiniteList α := fun n => tree (n :: node)

  def branches_through (tree : InfiniteTreeSkeleton α) (node : List Nat) : Set (InfiniteList α) := fun branch =>
    ∃ nodes : InfiniteList Nat, (∀ n : Nat, branch n = tree (nodes.take n).reverse) ∧ (nodes.take node.length).reverse = node

  def branches (tree : InfiniteTreeSkeleton α) : Set (InfiniteList α) := tree.branches_through []

  theorem branches_through_eq_union_branches_through_successors (tree : InfiniteTreeSkeleton α) (node : List Nat) : tree.branches_through node = fun b => ∃ (i : Nat), b ∈ tree.branches_through (i :: node) := by
    unfold branches_through
    apply funext
    simp only [List.length_cons, List.reverse_eq_cons_iff, eq_iff_iff]
    intro b
    constructor
    . intro ⟨nodes, h⟩
      exists nodes node.length
      simp [Set.element]
      exists nodes
      constructor
      . exact h.left
      . unfold InfiniteList.take
        simp
        rw [← List.reverse_eq_iff]
        exact h.right
    . intro h
      rcases h with ⟨i, nodes, h⟩
      exists nodes
      constructor
      . exact h.left
      . have hr := h.right
        unfold InfiniteList.take at hr
        rw [← List.reverse_inj] at hr
        rw [List.reverse_append] at hr
        rw [List.reverse_append] at hr
        simp at hr
        exact hr.right

end InfiniteTreeSkeleton

