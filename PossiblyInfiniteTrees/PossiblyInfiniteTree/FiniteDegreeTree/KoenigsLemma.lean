import BasicLeanDatastructures.List.Basic
import BasicLeanDatastructures.List.EraseDupsKeepRight

import PossiblyInfiniteTrees.PossiblyInfiniteTree.FiniteDegreeTree.Basic

/-!
# König's Lemma

This entire file is dedicated to proving König's Lemma on the `FiniteDegreeTree`.
That is, we show that if every branch in a `FiniteDegreeTree` is finite, then there the set of `branches` is finite.
We show this result in `branches_finite_of_each_branch_finite`.
-/

namespace FiniteDegreeTree

/-- If the `root` of the tree is none, then the `branches` only consist of the (unique) empty branch. -/
theorem branches_empty_of_root_none {t : FiniteDegreeTree α} :
    t.root = none -> t.branches = fun b => b = PossiblyInfiniteList.empty := by
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

/-- By the above theorem, the set of `branches` is finite if the `root` is none. -/
theorem branches_finite_of_root_none {t : FiniteDegreeTree α} : t.root = none -> t.branches.finite := by
  intro root_none
  rw [branches_empty_of_root_none root_none]
  exists [PossiblyInfiniteList.empty]
  constructor
  . simp
  . intro b; rw [List.mem_singleton]; rfl

/-- The set of `branches` is finite, if the set of branches in each `childTrees` is finite. This is simply because there are only finitely many `childTrees` in a `FiniteDegreeTree`. -/
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

/-- For König's Lemma below, we need to be able to generate an infinite branch. For this, we aim to leverage `FiniteDegreeTree.generate_branch` but we need to define an appropriate generator function. This is exactly what happens here. By this, we generate an infinite list of `FiniteDegreeTreeWithRoot` where each tree has infinitely many branches, based on knowing that the previous tree has infinitely many branches. This works since if a tree has infinitely many branches but only finitely many children, then there needs to exists a child tree that has infinitely many branches. The function is `noncomputable` since we need `Classical.choose` to pick a suitable child tree. -/
noncomputable def infinite_branch_generator (inf_branch_tree : { t : FiniteDegreeTreeWithRoot α // ¬ t.val.branches.finite }) : { t : FiniteDegreeTreeWithRoot α // t ∈ inf_branch_tree.val.val.childTrees ∧ ¬ t.val.branches.finite } :=
  have : ¬ (∀ c ∈ inf_branch_tree.val.val.childTrees, c.val.branches.finite) := by
    intro contra
    apply inf_branch_tree.property
    apply branches_finite_of_each_child_branches_finite
    exact contra
  have : ∃ c ∈ inf_branch_tree.val.val.childTrees, ¬ c.val.branches.finite := by
    simp at this
    rcases this with ⟨c, ⟨_, c_mem⟩, fin⟩
    exact ⟨_, ⟨c_mem, fin⟩⟩
  let c := Classical.choose this
  let c_spec := Classical.choose_spec this
  ⟨c, c_spec⟩

/-- This is König's Lemma. If each branch is finite, then there are only finitely many branches. We show this essentially via contraposition, i.e. we assume that there are infinitely many branches and then we construct an infinite branch using `generate_branch` and the previously defined `infinite_branch_generator`. -/
theorem branches_finite_of_each_branch_finite (t : FiniteDegreeTree α) : (∀ b ∈ t.branches, b.finite) -> t.branches.finite := by
  intro all_finite
  apply Classical.byContradiction
  intro contra

  let start : { t : FiniteDegreeTreeWithRoot α // ¬ t.val.branches.finite } := ⟨⟨t, by intro root_none; apply contra; apply branches_finite_of_root_none; exact root_none⟩, contra⟩
  let branch : PossiblyInfiniteList α := FiniteDegreeTree.generate_branch (some start) (fun t =>
    let next := infinite_branch_generator t
    some ⟨next.val, next.property.right⟩
  ) (fun t => t.val)
  have branch_mem : branch ∈ t.branches := by
    apply generate_branch_mem_branches
    . intro t c mem
      simp only [Option.mem_def, Option.some_inj] at mem
      rw [← mem]
      exact (infinite_branch_generator t).property.left
    . simp
    . simp

  rcases all_finite branch branch_mem with ⟨n, eq_none⟩

  induction n with
  | zero =>
    simp only [← PossiblyInfiniteList.head_eq, branch, head_generate_branch, Option.map_some, Option.some_get] at eq_none
    apply contra; apply branches_finite_of_root_none; exact eq_none
  | succ n ih =>
    simp only [branch, get?_generate_branch, Option.map_eq_none_iff, PossiblyInfiniteList.get?_succ_generate, Option.bind_eq_none_iff] at eq_none
    simp only [branch, get?_generate_branch, Option.map_eq_none_iff, PossiblyInfiniteList.get?_generate] at ih
    rw [imp_false, ← ne_eq, Option.ne_none_iff_exists] at ih
    rcases ih with ⟨x, x_eq⟩
    specialize eq_none x (Eq.symm x_eq)
    simp at eq_none

end FiniteDegreeTree

