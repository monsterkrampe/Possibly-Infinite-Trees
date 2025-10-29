import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.EraseDupsKeepRight

import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

namespace FiniteDegreeTree

  theorem branches_empty_of_root_none {t : FiniteDegreeTree α} : t.root = none -> t.branches = fun b => b = PossiblyInfiniteList.empty := by
    intro root_none
    unfold root at root_none
    rw [← PossiblyInfiniteTree.empty_iff_root_none] at root_none
    unfold branches
    unfold PossiblyInfiniteTree.branches
    apply Set.ext
    intro b
    constructor
    . rintro ⟨ns, b_eq, max⟩
      rw [b_eq]
      rw [root_none]
      unfold PossiblyInfiniteTree.branchForAddress
      unfold InfiniteTreeSkeleton.branchForAddress
      apply PossiblyInfiniteList.ext
      intro n
      rw [PossiblyInfiniteList.get?_empty]
      simp only [PossiblyInfiniteList.get?, InfiniteList.get]
      rw [← PossiblyInfiniteTree.get?.eq_def, PossiblyInfiniteTree.get?_empty]
    . intro b_eq
      exists fun _ => 0
      constructor
      . rw [root_none, b_eq]
        unfold PossiblyInfiniteTree.branchForAddress
        unfold InfiniteTreeSkeleton.branchForAddress
        apply PossiblyInfiniteList.ext
        intro n
        rw [PossiblyInfiniteList.get?_empty]
        simp only [PossiblyInfiniteList.get?, InfiniteList.get]
        rw [← PossiblyInfiniteTree.get?.eq_def, PossiblyInfiniteTree.get?_empty]
      . rw [root_none]
        intro n _
        unfold PossiblyInfiniteList.head InfiniteList.head
        rw [← PossiblyInfiniteList.get?.eq_def]
        rw [PossiblyInfiniteTree.get?_childNodes, PossiblyInfiniteTree.get?_childTrees]
        rw [PossiblyInfiniteTree.drop_drop, PossiblyInfiniteTree.drop_empty, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]
        rw [PossiblyInfiniteTree.root_empty]

  theorem branches_finite_of_root_none {t : FiniteDegreeTree α} : t.root = none -> t.branches.finite := by
    intro root_none
    rw [branches_empty_of_root_none root_none]
    exists [PossiblyInfiniteList.empty]
    constructor
    . simp
    . intro b; rw [List.mem_singleton]; rfl


  theorem branches_finite_of_each_child_branches_finite (t : FiniteDegreeTree α) : (∀ c ∈ t.childTrees, c.val.branches.finite) -> t.branches.finite := by
    cases root_eq : t.root with
    | none => intro _; apply branches_finite_of_root_none; exact root_eq
    | some r =>
      intro children_finite

      cases eq : t.childTrees with
      | nil =>
        exists [PossiblyInfiniteList.cons r (PossiblyInfiniteList.empty)]
        constructor
        . simp
        intro b
        rw [List.mem_singleton, branches_eq]
        constructor
        . intro h
          rw [h]
          constructor
          . rw [PossiblyInfiniteList.head_cons, root_eq]
          . apply Or.inl
            constructor
            . exact eq
            . rw [PossiblyInfiniteList.tail_cons]
        . rintro ⟨head_eq, tail_eq⟩
          cases tail_eq with
          | inr tail_eq => rcases tail_eq with ⟨_, c_mem, _⟩; rw [eq] at c_mem; simp at c_mem
          | inl tail_eq =>
            rw [PossiblyInfiniteList.cons_head_tail b r (by rw [head_eq, root_eq])]
            rw [tail_eq.right]
      | cons _ _ =>
        let branch_list := t.childTrees.attach.flatMap (fun c => Classical.choose (children_finite c.val c.property))

        -- TODO: can we get rid of the Classical here?
        have dec := Classical.typeDecidableEq (PossiblyInfiniteList α)

        apply Set.finite_of_list_with_same_elements (branch_list.map (fun b => PossiblyInfiniteList.cons r b))
        intro b
        rw [List.mem_map, branches_eq]
        constructor
        . rintro ⟨tail, tail_mem, b_eq⟩
          rw [← b_eq]
          constructor
          . rw [PossiblyInfiniteList.head_cons]; rw [root_eq]
          . apply Or.inr
            rw [List.mem_flatMap] at tail_mem
            rcases tail_mem with ⟨c, c_mem, tail_mem⟩
            have spec := Classical.choose_spec (children_finite c.val c.property)
            exists c.val
            constructor
            . exact c.property
            . rw [PossiblyInfiniteList.tail_cons]; rw [← spec.right]; exact tail_mem
        . rintro ⟨head_eq, tail_eq⟩
          cases tail_eq with
          | inl tail_eq => rw [tail_eq.left] at eq; simp at eq
          | inr tail_eq =>
            rcases tail_eq with ⟨c, c_mem, tail_mem⟩
            have spec := Classical.choose_spec (children_finite c c_mem)
            exists b.tail
            constructor
            . rw [List.mem_flatMap]; exists ⟨c, c_mem⟩; rw [spec.right]; simp [tail_mem]
            . rw [PossiblyInfiniteList.cons_head_tail b r (by rw [head_eq, root_eq]), PossiblyInfiniteList.tail_cons]

  noncomputable def infinite_branching_child_index_of_branches_infinite (t : FiniteDegreeTree α) (not_finite : ¬ t.branches.finite) : { n : Nat // ∃ (lt : n < t.childTrees.length), ¬ t.childTrees[n].val.branches.finite } :=
    have : ¬ (∀ c ∈ t.childTrees, c.val.branches.finite) := by
      intro contra
      apply not_finite
      apply branches_finite_of_each_child_branches_finite
      exact contra
    have : ∃ (i : Nat) (lt : i < t.childTrees.length), ¬ t.childTrees[i].val.branches.finite := by
      simp at this
      rcases this with ⟨c, ⟨_, c_mem⟩, fin⟩
      rw [List.mem_iff_getElem] at c_mem
      rcases c_mem with ⟨i, lt, c_mem⟩
      exists i, lt
      rw [c_mem]
      exact fin
    let i := Classical.choose this
    let i_spec := Classical.choose_spec this
    ⟨i, i_spec⟩

  noncomputable def infinite_branching_node_at_depth_of_branches_infinite (t : FiniteDegreeTree α) (not_finite : ¬ t.branches.finite) : (depth : Nat) -> { ns : List Nat // ns.length = depth ∧ ¬ (t.drop ns).branches.finite }
  | .zero => ⟨[], by constructor; simp; exact not_finite⟩
  | .succ depth =>
    let prev_result := t.infinite_branching_node_at_depth_of_branches_infinite not_finite depth
    let step_result := (t.drop prev_result.val).infinite_branching_child_index_of_branches_infinite prev_result.property.right
    ⟨prev_result.val ++ [step_result.val], by
      constructor
      . rw [List.length_append, prev_result.property.left]; simp
      . rcases step_result.property with ⟨lt, step_prop⟩
        rw [get_childTrees, drop_drop] at step_prop
        exact step_prop⟩

  theorem infinite_branching_node_at_depth_extends_previous {t : FiniteDegreeTree α} {not_finite : ¬ t.branches.finite} {depth : Nat} : (t.infinite_branching_node_at_depth_of_branches_infinite not_finite depth.succ).val = (t.infinite_branching_node_at_depth_of_branches_infinite not_finite depth).val ++ [(t.infinite_branching_node_at_depth_of_branches_infinite not_finite depth.succ).val.getLast (by simp [infinite_branching_node_at_depth_of_branches_infinite])] := by
    simp [infinite_branching_node_at_depth_of_branches_infinite]

  -- König's Lemma
  theorem branches_finite_of_each_branch_finite (t : FiniteDegreeTree α) : (∀ b ∈ t.branches, b.finite) -> t.branches.finite := by
    intro all_finite
    apply Classical.byContradiction
    intro contra

    have : ∃ (ns : InfiniteList Nat), ∀ (n : Nat), ¬ (t.drop (ns.take n)).branches.finite := by
      let ns : InfiniteList Nat := fun n =>
        (t.infinite_branching_node_at_depth_of_branches_infinite contra n.succ).val.getLast
          (by simp [infinite_branching_node_at_depth_of_branches_infinite])
      have : ∀ n, ns.take n = (t.infinite_branching_node_at_depth_of_branches_infinite contra n).val := by
        intro n
        induction n with
        | zero => simp [InfiniteList.take, infinite_branching_node_at_depth_of_branches_infinite]
        | succ i ih =>
          rw [InfiniteList.take_succ']
          rw [ih]
          rw [infinite_branching_node_at_depth_extends_previous]
          rfl
      exists ns
      intro n
      rw [this]
      exact (t.infinite_branching_node_at_depth_of_branches_infinite contra n).property.right

    rcases this with ⟨ns, all_infinite⟩

    let branch := t.tree.branchForAddress ns

    specialize all_finite branch (by
      exists ns
      constructor
      . rfl
      . intro n contra
        rw [PossiblyInfiniteTree.get?_branchForAddress] at contra
        apply False.elim
        apply all_infinite n.succ
        apply branches_finite_of_root_none
        rw [root_drop]
        exact contra
    )

    rcases all_finite with ⟨n, eq_none⟩
    apply all_infinite n
    apply branches_finite_of_root_none
    rw [root_drop]
    exact eq_none

end FiniteDegreeTree

