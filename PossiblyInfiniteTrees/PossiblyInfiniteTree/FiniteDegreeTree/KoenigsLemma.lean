import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.EraseDupsKeepRight

import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

namespace FiniteDegreeTree

  theorem branches_through_finite_of_get_eq_none (tree : FiniteDegreeTree α) (node : List Nat) : tree.get node = none -> (tree.branches_through node).finite := by
    intro is_none
    let nodes : InfiniteList Nat := fun n => if _isLt : n < node.length then node[node.length - (n+1)] else 0
    let branch_for_node := tree.tree.branch_for_address nodes
    have nodes_eq : ∀ n, n ≤ node.length -> (nodes.take n).reverse = node.drop (node.length - n) := by
      intro n
      induction n with
      | zero => simp [InfiniteList.take]
      | succ n ih =>
        intro le
        unfold InfiniteList.take
        simp
        rw [ih (by apply Nat.le_of_succ_le le)]
        unfold nodes
        have lt : n < node.length := by apply Nat.lt_of_succ_le le
        simp [lt]
        conv => right; rw [List.drop_eq_getElem_cons (by apply Nat.sub_lt_self; simp; exact le)]
        have : node.length - (n + 1) + 1 = node.length - n := by omega
        rw [this]
    -- TODO: I think this could be decidable
    cases Classical.em (tree.tree.branch_address_is_maximal nodes) with
    | inl is_maximal =>
      exists [branch_for_node]
      constructor
      . simp
      . intro e
        constructor
        . intro h
          simp at h
          rw [h]
          exists nodes
          constructor
          . constructor
            . unfold InfiniteTreeSkeleton.branch_addresses_through
              simp only [Membership.mem]
              rw [nodes_eq node.length]
              . simp
              . simp
            . exact is_maximal
          . rfl
        . intro h
          rcases h with ⟨nodes2, h⟩
          rw [List.mem_singleton]
          rw [PossiblyInfiniteList.eq_iff_same_on_all_indices]
          intro n
          rw [h.right]
          unfold branch_for_node
          simp only [PossiblyInfiniteTree.branch_for_address, InfiniteTreeSkeleton.branch_for_address]
          cases Decidable.em (n ≤ node.length) with
          | inl le =>
            have : (nodes2.take n).reverse = node.drop (node.length - n) := by
              conv => right; right; rw [← h.left.left]
              rw [List.drop_reverse]
              rw [InfiniteList.length_take]
              rw [InfiniteList.take_after_take]
              rw [Nat.sub_sub_self le]
              simp [Nat.min_eq_right le]
            rw [this, nodes_eq]
            exact le
          | inr lt =>
            have nodes2_eq_none : tree.tree.infinite_tree (nodes2.take n).reverse = none := by
              apply Option.decidableEqNone.byContradiction
              intro contra
              have no_orphans := tree.tree.no_orphans (nodes2.take n).reverse contra ⟨node, by
                exists ((nodes2.skip (node.length)).take (n - node.length)).reverse
                conv => left; right; rw [← h.left.left]
                rw [← List.reverse_append]
                rw [InfiniteList.combine_skip_take nodes2 n ⟨node.length, by apply Nat.lt_of_not_le; exact lt⟩]⟩
              apply no_orphans
              exact is_none
            have nodes_eq_none : tree.tree.infinite_tree (nodes.take n).reverse = none := by
              apply Option.decidableEqNone.byContradiction
              intro contra
              have no_orphans := tree.tree.no_orphans (nodes.take n).reverse contra ⟨node, by
                exists ((nodes.skip (node.length)).take (n - node.length)).reverse
                have : node = (nodes.take node.length).reverse := by
                  rw [nodes_eq]
                  . simp
                  . simp
                conv => left; right; rw [this]
                rw [← List.reverse_append]
                rw [InfiniteList.combine_skip_take nodes n ⟨node.length, by apply Nat.lt_of_not_le; exact lt⟩]⟩
              apply no_orphans
              exact is_none
            rw [nodes2_eq_none, nodes_eq_none]
    | inr not_maximal =>
      exists []
      constructor
      . simp
      . simp only [List.not_mem_nil, false_iff]
        intro pil contra
        rcases contra with ⟨nodes2, contra⟩
        apply not_maximal

        have nodes_eq_nodes2 : ∀ n, n ≤ node.length -> (nodes.take n).reverse = (nodes2.take n).reverse := by
          intro n le
          have : (nodes2.take n).reverse = node.drop (node.length - n) := by
            conv => right; right; rw [← contra.left.left]
            rw [List.drop_reverse]
            rw [InfiniteList.length_take]
            rw [InfiniteList.take_after_take]
            rw [Nat.sub_sub_self le]
            simp [Nat.min_eq_right le]
          rw [this]
          rw [nodes_eq]
          exact le

        intro n h
        cases Decidable.em (n < node.length) with
        | inl lt =>
          rw [nodes_eq_nodes2]
          apply contra.left.right
          rw [← nodes_eq_nodes2]
          . exact h
          . apply Nat.succ_le_of_lt
            exact lt
          . apply Nat.le_of_lt
            exact lt
        | inr le =>
          simp only [Nat.not_lt] at le
          have : (nodes.take (n+1)).reverse = 0 :: (nodes.take n).reverse := by
            conv => left; unfold nodes; simp only [InfiniteList.take]
            rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, List.cons_eq_cons]
            constructor
            . have : ¬ n < node.length := by apply Nat.not_lt_of_le; exact le
              simp [this]
            . rfl
          rw [← this]
          exact h

  theorem branches_through_finite_of_children_empty (tree : FiniteDegreeTree α) (node : List Nat) : tree.children node = [] -> (tree.branches_through node).finite := by
    intro h
    cases Option.decidableEqNone.em (tree.get node = none) with
    | inl eq_none => apply branches_through_finite_of_get_eq_none; exact eq_none
    | inr neq_none =>
      let nodes : InfiniteList Nat := fun n => if _isLt : n < node.length then node[node.length - (n+1)] else 0
      let branch_for_node := tree.tree.branch_for_address nodes
      have nodes_eq : ∀ n, n ≤ node.length -> (nodes.take n).reverse = node.drop (node.length - n) := by
        intro n
        induction n with
        | zero => simp [InfiniteList.take]
        | succ n ih =>
          intro le
          unfold InfiniteList.take
          simp
          rw [ih (by apply Nat.le_of_succ_le le)]
          unfold nodes
          have lt : n < node.length := by apply Nat.lt_of_succ_le le
          simp [lt]
          conv => right; rw [List.drop_eq_getElem_cons (by apply Nat.sub_lt_self; simp; exact le)]
          have : node.length - (n + 1) + 1 = node.length - n := by omega
          rw [this]
      exists [branch_for_node]
      constructor
      . simp
      . intro branch
        simp only [List.mem_singleton]
        constructor
        . intro pre
          rw [pre]
          exists nodes
          constructor
          . constructor
            . unfold InfiniteTreeSkeleton.branch_addresses_through; simp only [Membership.mem]; rw [nodes_eq node.length]; simp; simp
            . intro n
              cases Decidable.em (n < node.length) with
              | inl lt =>
                intro contra
                apply False.elim
                apply tree.tree.no_orphans node neq_none ⟨(nodes.take (n+1)).reverse, by
                  exists ((nodes.skip (n+1)).take (node.length - (n+1))).reverse
                  rw [← List.reverse_append]
                  cases Decidable.em (n + 1 < node.length) with
                  | inl lt2 =>
                    rw [InfiniteList.combine_skip_take nodes node.length ⟨n+1, lt2⟩]
                    rw [nodes_eq]
                    . simp
                    . simp
                  | inr le2 =>
                    have : n+1 = node.length := by
                      apply Nat.eq_of_lt_succ_of_not_lt
                      . apply Nat.succ_lt_succ; exact lt
                      . exact le2
                    rw [this]
                    simp only [Nat.sub_self, InfiniteList.take, List.append_nil]
                    rw [nodes_eq]
                    . simp
                    . simp⟩
                exact contra
              | inr le =>
                intro eq_none
                unfold InfiniteList.take at eq_none
                rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] at eq_none
                unfold nodes at eq_none
                simp only [le, ↓reduceDIte] at eq_none
                exact eq_none
          . rfl
        . intro pre
          rcases pre with ⟨nodes2, pre⟩
          rw [pre.right]
          rw [PossiblyInfiniteList.eq_iff_same_on_all_indices]
          intro n
          unfold branch_for_node
          simp only [PossiblyInfiniteTree.branch_for_address, InfiniteTreeSkeleton.branch_for_address]
          cases Decidable.em (n ≤ node.length) with
          | inl le =>
            have : (nodes2.take n).reverse = node.drop (node.length - n) := by
              conv => right; right; rw [← pre.left.left]
              rw [List.drop_reverse]
              rw [InfiniteList.length_take]
              rw [InfiniteList.take_after_take]
              rw [Nat.sub_sub_self le]
              simp [Nat.min_eq_right le]
            rw [this, nodes_eq]
            exact le
          | inr lt =>
            have nodes2_eq_none : tree.tree.infinite_tree (nodes2.take n).reverse = none := by
              apply Option.decidableEqNone.byContradiction
              intro contra
              have no_orphans := tree.tree.no_orphans (nodes2.take n).reverse contra ⟨(nodes2.take (node.length + 1)).reverse, by
                exists ((nodes2.skip (node.length + 1)).take (n - (node.length + 1))).reverse
                rw [← List.reverse_append]
                cases Decidable.em (node.length + 1 < n) with
                | inl lt2 => rw [InfiniteList.combine_skip_take nodes2 n ⟨node.length+1, lt2⟩]
                | inr le2 =>
                  have : node.length + 1 = n := by
                    apply Nat.eq_of_lt_succ_of_not_lt
                    . apply Nat.succ_lt_succ; apply Nat.lt_of_not_le; exact lt
                    . exact le2
                  rw [this]
                  simp only [Nat.sub_self, InfiniteList.take, List.append_nil]⟩
              apply no_orphans
              have := tree.each_successor_none_of_children_empty node h (nodes2 node.length)
              simp only [InfiniteList.take, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
              rw [pre.left.left]
              exact this
            have nodes_eq_none : tree.tree.infinite_tree (nodes.take n).reverse = none := by
              apply Option.decidableEqNone.byContradiction
              intro contra
              have no_orphans := tree.tree.no_orphans (nodes.take n).reverse contra ⟨(nodes.take (node.length + 1)).reverse, by
                exists ((nodes.skip (node.length + 1)).take (n - (node.length + 1))).reverse
                rw [← List.reverse_append]
                cases Decidable.em (node.length + 1 < n) with
                | inl lt2 => rw [InfiniteList.combine_skip_take nodes n ⟨node.length+1, lt2⟩]
                | inr le2 =>
                  have : node.length + 1 = n := by
                    apply Nat.eq_of_lt_succ_of_not_lt
                    . apply Nat.succ_lt_succ; apply Nat.lt_of_not_le; exact lt
                    . exact le2
                  rw [this]
                  simp only [Nat.sub_self, InfiniteList.take, List.append_nil]⟩
              apply no_orphans
              have := tree.each_successor_none_of_children_empty node h (nodes node.length)
              simp only [InfiniteList.take, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
              rw [nodes_eq]
              . simp only [Nat.sub_self, List.drop_zero]
                exact this
              . simp
            rw [nodes2_eq_none, nodes_eq_none]

  theorem branches_through_finite_of_each_successor_branches_through_finite (tree : FiniteDegreeTree α) (node : List Nat) : (∀ i, (tree.branches_through (i :: node)).finite) -> (tree.branches_through node).finite := by

    intro h
    have dec := Classical.typeDecidableEq (PossiblyInfiniteList α)

    cases Option.decidableEqNone.em ((tree.get (0::node)) = none) with
    | inl childs_empty => apply branches_through_finite_of_children_empty; apply tree.children_empty_of_first_successor_none; exact childs_empty
    | inr childs_not_empty =>
      let branches_for_i (i : Nat) := Classical.choose (h i)
      let target_list : List (PossiblyInfiniteList α) := ((tree.children node).zipIdx_with_lt.map (fun (_, i) => branches_for_i i.val)).flatten.eraseDupsKeepRight
      exists target_list
      constructor
      . apply List.nodup_eraseDupsKeepRight
      . intro branch
        unfold target_list
        rw [List.mem_eraseDupsKeepRight]
        simp only [List.mem_flatten, List.mem_map, Prod.exists]
        constructor
        . intro pre
          rcases pre with ⟨branches, ex_i, branch_mem⟩
          rcases ex_i with ⟨_, i, _, eq⟩
          rw [branches_through_eq_union_branches_through_successors]
          exists i.val
          have spec := Classical.choose_spec (h i.val)
          rw [← spec.right]
          unfold branches_for_i at eq
          rw [eq]
          exact branch_mem
        . intro pre
          rw [branches_through_eq_union_branches_through_successors] at pre
          rcases pre with ⟨i, pre⟩
          cases Decidable.em (i < (tree.children node).length) with
          | inl lt =>
            exists branches_for_i i
            constructor
            . let i_fin : Fin (tree.children node).length := ⟨i, lt⟩
              exists (tree.children node)[i]
              exists i_fin
              constructor
              . rw [List.mem_zipIdx_with_lt_iff_mem_zipIdx]
                rw [List.mem_zipIdx_iff_getElem?]
                simp [i_fin]
              . rfl
            . have spec := Classical.choose_spec (h i)
              unfold branches_for_i
              rw [spec.right]
              exact pre
          | inr not_lt =>
            rcases pre with ⟨nodes, pre⟩
            apply False.elim
            apply childs_not_empty
            have node_eq := pre.left.left
            unfold InfiniteTreeSkeleton.branch_addresses_through at node_eq
            simp only [List.length_cons, InfiniteList.take, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append, Membership.mem] at node_eq
            rw [List.cons_eq_cons] at node_eq
            rw [← node_eq.right]
            apply pre.left.right
            have : (tree.children node)[nodes node.length]? = none := by
              apply List.getElem?_eq_none
              rw [node_eq.left]
              apply Nat.le_of_not_gt
              exact not_lt
            rw [getElem_children_eq_getElem_lifted_children, PossiblyInfiniteTree.getElem_children_eq_get] at this
            unfold PossiblyInfiniteTree.get at this
            unfold InfiniteList.take
            rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
            rw [node_eq.right]
            exact this

  noncomputable def infinite_branching_node_for_depth_of_branches_infinite (tree : FiniteDegreeTree α) (not_finite : ¬ tree.branches.finite) : (depth : Nat) -> { node : List Nat // node.length = depth ∧ ¬ (tree.branches_through node).finite }
  | .zero => ⟨[], by constructor; rfl; exact not_finite⟩
  | .succ depth =>
    let prev_res := infinite_branching_node_for_depth_of_branches_infinite tree not_finite depth
    let prev_node := prev_res.val
    let length_eq := prev_res.property.left
    let not_finite := prev_res.property.right
    have : ¬ ∀ i, (tree.branches_through (i :: prev_node)).finite := by
      intro contra
      apply not_finite
      apply branches_through_finite_of_each_successor_branches_through_finite
      exact contra
    have : ∃ i, ¬ (tree.branches_through (i :: prev_node)).finite := by simp at this; exact this
    let i := Classical.choose this
    let i_spec := Classical.choose_spec this

    ⟨i :: prev_node, by
      constructor
      . simp; exact length_eq
      . exact i_spec
    ⟩

  theorem infinite_branching_node_extends_previous (tree : FiniteDegreeTree α) (not_finite : ¬ tree.branches.finite) (depth : Nat) : (infinite_branching_node_for_depth_of_branches_infinite tree not_finite depth.succ).val = (infinite_branching_node_for_depth_of_branches_infinite tree not_finite depth.succ).val.head (by simp [infinite_branching_node_for_depth_of_branches_infinite]) :: (infinite_branching_node_for_depth_of_branches_infinite tree not_finite depth).val := by
    simp [infinite_branching_node_for_depth_of_branches_infinite]

  theorem branches_finite_of_each_branch_finite (tree : FiniteDegreeTree α) : (∀ branch, branch ∈ tree.branches -> ∃ i, branch.infinite_list i = none) -> tree.branches.finite := by
    intro h

    apply Classical.byContradiction
    intro contra
    simp at contra

    have : ∃ (nodes : InfiniteList Nat), ∀ (i : Nat), ¬ (tree.branches_through (nodes.take i).reverse).finite := by
      let nodes : InfiniteList Nat := fun n => (infinite_branching_node_for_depth_of_branches_infinite tree contra n.succ).val.head (by
        simp [infinite_branching_node_for_depth_of_branches_infinite]
      )
      have : ∀ i, (nodes.take i).reverse = (infinite_branching_node_for_depth_of_branches_infinite tree contra i).val := by
        intro i
        induction i with
        | zero => simp [InfiniteList.take, infinite_branching_node_for_depth_of_branches_infinite]
        | succ i ih =>
          unfold InfiniteList.take
          unfold nodes
          simp
          rw [ih]
          conv => right; rw [infinite_branching_node_extends_previous]
      exists nodes
      intro i
      rw [this]
      have prop := (infinite_branching_node_for_depth_of_branches_infinite tree contra i).property
      exact prop.right

    rcases this with ⟨nodes, all_infinite⟩

    let branch : PossiblyInfiniteList α := ⟨fun n => tree.get (nodes.take n).reverse, by
      intro n not_none m contra
      apply all_infinite m.val
      apply branches_through_finite_of_get_eq_none
      exact contra
    ⟩

    specialize h branch (by
      exists nodes
      constructor
      . constructor
        . rfl
        . intro n contra
          apply False.elim
          apply all_infinite (n+1)
          apply branches_through_finite_of_get_eq_none
          exact contra
      . rfl
    )

    rcases h with ⟨i, hi⟩
    apply all_infinite i
    apply branches_through_finite_of_get_eq_none
    exact hi

end FiniteDegreeTree

