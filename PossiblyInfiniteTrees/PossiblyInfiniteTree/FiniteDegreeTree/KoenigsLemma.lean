import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.EraseDupsKeepRight

import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

namespace FiniteDegreeTree

  theorem branches_through_finite_of_none (tree : FiniteDegreeTree α) (node : List Nat) : tree.get node = none -> (tree.branches_through node).finite := by

    intro is_none
    let branch_for_node : PossiblyInfiniteList α := ⟨fun n => if n ≤ node.length then tree.get (node.drop (node.length - n)) else none, by
      intro n not_none
      cases Decidable.em (n ≤ node.length) with
      | inr lt => simp [lt] at not_none
      | inl le =>
        simp [le] at not_none
        intro m
        have m_le : m ≤ node.length := by apply Nat.le_trans; apply Nat.le_of_lt m.isLt; exact le
        simp [m_le]
        have no_orphans := tree.tree.no_orphans (node.drop (node.length - n)) not_none ⟨(node.drop (node.length - m)), by
          exists (node.drop (node.length - n)).take (n - m)
          rw [List.take_drop]
          have : node.length - n + (n - m.val) = node.length - m.val := by
            rw [← Nat.add_sub_assoc (by apply Nat.le_of_lt; exact m.isLt)]
            rw [← Nat.sub_add_comm le]
            simp
          rw [this]
          rw [← List.drop_append_of_le_length (by rw [List.length_take_of_le (by simp), Nat.sub_le_sub_iff_left m_le]; apply Nat.le_of_lt; exact m.isLt)]
          simp
        ⟩
        exact no_orphans
    ⟩
    exists [branch_for_node]
    constructor
    . simp
    . intro e
      constructor
      . intro h
        simp at h
        rw [h]
        let nodes : InfiniteList Nat := fun n => if lt : n < node.length then node[node.length - (n+1)] else (tree.children node).length
        have : ∀ n, n ≤ node.length -> (nodes.take n).reverse = node.drop (node.length - n) := by
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
        exists nodes
        constructor
        . intro n
          cases Decidable.em (n ≤ node.length) with
          | inl le =>
            rw [this n le]
            simp only [branch_for_node, le]
            rfl
          | inr lt =>
            simp only [branch_for_node, lt]
            have no_orphans := tree.tree.no_orphans (nodes.take n).reverse
            apply Eq.symm
            apply Option.decidable_eq_none.byContradiction
            intro contra
            specialize no_orphans contra ⟨node, by
              exists ((nodes.skip (node.length)).take (n - node.length)).reverse
              have : node = (nodes.take (node.length)).reverse := by
                rw [this node.length]
                . simp
                . simp
              conv => left; right; rw [this]
              rw [← List.reverse_append]
              rw [InfiniteList.combine_skip_take nodes n ⟨node.length, by apply Nat.lt_of_not_le; exact lt⟩]
            ⟩
            apply no_orphans
            exact is_none
        . rw [this]
          . simp
          . simp
      . intro h
        rcases h with ⟨nodes, h⟩
        simp
        rw [PossiblyInfiniteList.eq_iff_same_on_all_indices]
        intro n
        rw [h.left]
        unfold branch_for_node
        simp
        cases Decidable.em (n ≤ node.length) with
        | inl le =>
          simp [le]
          have : (nodes.take n).reverse = node.drop (node.length - n) := by
            conv => right; right; rw [← h.right]
            rw [List.drop_reverse]
            rw [InfiniteList.length_take]
            rw [InfiniteList.take_after_take]
            rw [Nat.sub_sub_self le]
            simp [Nat.min_eq_right le]
          rw [this]
          rfl
        | inr lt =>
          simp [lt]

          have no_orphans := tree.tree.no_orphans (nodes.take n).reverse
          apply Option.decidable_eq_none.byContradiction
          intro contra
          specialize no_orphans contra ⟨node, by
            exists ((nodes.skip (node.length)).take (n - node.length)).reverse
            conv => left; right; rw [← h.right]
            rw [← List.reverse_append]
            rw [InfiniteList.combine_skip_take nodes n ⟨node.length, by apply Nat.lt_of_not_le; exact lt⟩]
          ⟩
          apply no_orphans
          exact is_none

  theorem branches_through_finite_of_branches_through_children_finite (tree : FiniteDegreeTree α) (node : List Nat) : (∀ i, (tree.branches_through (i :: node)).finite) -> (tree.branches_through node).finite := by

    intro h
    have dec := Classical.typeDecidableEq (PossiblyInfiniteList α)
    let branch_for_node : PossiblyInfiniteList α := ⟨fun n => if n ≤ node.length then tree.get (node.drop (node.length - n)) else none, by
      intro n not_none
      cases Decidable.em (n ≤ node.length) with
      | inr lt => simp [lt] at not_none
      | inl le =>
        simp [le] at not_none
        intro m
        have m_le : m ≤ node.length := by apply Nat.le_trans; apply Nat.le_of_lt m.isLt; exact le
        simp [m_le]
        have no_orphans := tree.tree.no_orphans (node.drop (node.length - n)) not_none ⟨(node.drop (node.length - m)), by
          exists (node.drop (node.length - n)).take (n - m)
          rw [List.take_drop]
          have : node.length - n + (n - m.val) = node.length - m.val := by
            rw [← Nat.add_sub_assoc (by apply Nat.le_of_lt; exact m.isLt)]
            rw [← Nat.sub_add_comm le]
            simp
          rw [this]
          rw [← List.drop_append_of_le_length (by rw [List.length_take_of_le (by simp), Nat.sub_le_sub_iff_left m_le]; apply Nat.le_of_lt; exact m.isLt)]
          simp
        ⟩
        exact no_orphans
    ⟩
    let branches_for_i (i : Nat) := Classical.choose (h i)
    let target_list : List (PossiblyInfiniteList α) := (branch_for_node :: ((tree.children node).enum_with_lt.map (fun (i, _) => branches_for_i i.val)).flatten).eraseDupsKeepRight
    exists target_list
    constructor
    . apply List.nodup_eraseDupsKeepRight
    . intro branch
      unfold target_list
      rw [List.mem_eraseDupsKeepRight]
      simp
      constructor
      . intro pre
        cases pre with
        | inl eq =>
          let nodes : InfiniteList Nat := fun n => if lt : n < node.length then node[node.length - (n+1)] else (tree.children node).length
          have : ∀ n, n ≤ node.length -> (nodes.take n).reverse = node.drop (node.length - n) := by
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
          exists nodes
          constructor
          . rw [eq]
            intro n
            cases Decidable.em (n ≤ node.length) with
            | inl le =>
              rw [this n le]
              simp only [branch_for_node, le]
              rfl
            | inr lt =>
              simp only [branch_for_node, lt]
              have : tree.tree.infinite_tree (nodes.take (node.length + 1)).reverse = none := by
                have child_none : (tree.children node)[nodes node.length]? = none := by
                  apply List.getElem?_eq_none
                  unfold nodes
                  simp
                rw [getElem_children_eq_getElem_tree_children, PossiblyInfiniteTree.getElem_children_eq_get_tree] at child_none
                unfold PossiblyInfiniteTree.get at child_none
                unfold InfiniteList.take
                simp
                rw [this]
                . simp
                  exact child_none
                . simp
              have le : node.length + 1 ≤ n := by apply Nat.succ_le_of_lt; apply Nat.lt_of_not_ge; exact lt
              cases Nat.eq_or_lt_of_le le with
              | inl eq => simp [← eq, this]
              | inr lt =>
                have no_orphans := tree.tree.no_orphans (nodes.take n).reverse
                apply Eq.symm
                apply Option.decidable_eq_none.byContradiction
                intro contra
                specialize no_orphans contra ⟨(nodes.take (node.length + 1)).reverse, by
                  exists ((nodes.skip (node.length + 1)).take (n - (node.length + 1))).reverse
                  rw [← List.reverse_append]
                  rw [InfiniteList.combine_skip_take nodes n ⟨node.length + 1, lt⟩]
                ⟩
                apply no_orphans
                exact this
          . rw [this]
            . simp
            . simp
        | inr pre =>
          rcases pre with ⟨branches, ex_i, branch_mem⟩
          rcases ex_i with ⟨i, _, eq⟩
          rw [branches_through_eq_union_children]
          exists i.val
          have spec := Classical.choose_spec (h i.val)
          rw [← spec.right]
          unfold branches_for_i at eq
          rw [eq]
          exact branch_mem
      . intro pre
        rw [branches_through_eq_union_children] at pre
        rcases pre with ⟨i, pre⟩
        cases Decidable.em (i < (tree.children node).length) with
        | inl lt =>
          apply Or.inr
          exists branches_for_i i
          constructor
          . let i_fin : Fin (tree.children node).length := ⟨i, lt⟩
            exists i_fin
            constructor
            . exists (tree.children node)[i_fin]
              rw [List.mem_enum_with_lt_iff_mem_enum]
              rw [List.mem_enum_iff_getElem?]
              simp
            . rfl
          . have spec := Classical.choose_spec (h i)
            unfold branches_for_i
            rw [spec.right]
            exact pre
        | inr not_lt =>
          apply Or.inl
          rcases pre with ⟨nodes, pre⟩
          unfold branch_for_node
          rw [PossiblyInfiniteList.eq_iff_same_on_all_indices]
          intro n
          rw [pre.left n]
          have pre_r := pre.right
          simp [InfiniteList.take] at pre_r
          simp
          cases Decidable.em (n ≤ node.length) with
          | inl le =>
            simp [le]
            have : (nodes.take n).reverse = node.drop (node.length - n) := by
              conv => right; right; rw [← pre_r.right]
              rw [List.drop_reverse]
              rw [InfiniteList.length_take]
              rw [InfiniteList.take_after_take]
              rw [Nat.sub_sub_self le]
              simp [Nat.min_eq_right le]
            rw [this]
            rfl
          | inr lt =>
            simp [lt]
            have : tree.tree.infinite_tree (nodes.take (node.length + 1)).reverse = none := by
              have : (tree.children node)[nodes node.length]? = none := by
                apply List.getElem?_eq_none
                rw [pre_r.left]
                apply Nat.le_of_not_gt
                exact not_lt
              rw [getElem_children_eq_getElem_tree_children, PossiblyInfiniteTree.getElem_children_eq_get_tree] at this
              unfold PossiblyInfiniteTree.get at this
              unfold InfiniteList.take
              simp
              rw [pre_r.right]
              exact this
            have le : node.length + 1 ≤ n := by apply Nat.succ_le_of_lt; apply Nat.lt_of_not_ge; exact lt
            cases Nat.eq_or_lt_of_le le with
            | inl eq => rw [← eq]; exact this
            | inr lt =>
              have no_orphans := tree.tree.no_orphans (nodes.take n).reverse
              apply Option.decidable_eq_none.byContradiction
              intro contra
              specialize no_orphans contra ⟨(nodes.take (node.length + 1)).reverse, by
                exists ((nodes.skip (node.length + 1)).take (n - (node.length + 1))).reverse
                rw [← List.reverse_append]
                rw [InfiniteList.combine_skip_take nodes n ⟨node.length + 1, lt⟩]
              ⟩
              apply no_orphans
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
      apply branches_through_finite_of_branches_through_children_finite
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

  theorem branches_finite_of_each_finite (tree : FiniteDegreeTree α) : (∀ branch, branch ∈ tree.branches -> ∃ i, branch.infinite_list i = none) -> tree.branches.finite := by
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
      apply branches_through_finite_of_none
      exact contra
    ⟩

    specialize h branch (by
      exists nodes
      constructor
      . intro n
        rfl
      . rfl
    )

    rcases h with ⟨i, hi⟩
    apply all_infinite i
    apply branches_through_finite_of_none
    exact hi

end FiniteDegreeTree

