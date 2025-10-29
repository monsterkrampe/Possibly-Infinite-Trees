import BasicLeanDatastructures.Fin
import BasicLeanDatastructures.Set.Finite

import PossiblyInfiniteTrees.PossiblyInfiniteTree.PossiblyInfiniteTree

def PossiblyInfiniteTree.finitely_many_children (t : PossiblyInfiniteTree α) : Prop := ∀ ns : List Nat, (t.drop ns).childTrees.finite

theorem PossiblyInfiniteTree.finitely_many_children_empty {α} : (@PossiblyInfiniteTree.empty α).finitely_many_children := by
  intro ns; exists 0

structure FiniteDegreeTree (α : Type u) where
  tree : PossiblyInfiniteTree α
  finitely_many_children : tree.finitely_many_children

namespace FiniteDegreeTree

  def get? (t : FiniteDegreeTree α) (ns : List Nat) : Option α := t.tree.get? ns

  def drop (t : FiniteDegreeTree α) (ns : List Nat) : FiniteDegreeTree α where
    tree := t.tree.drop ns
    finitely_many_children := by intro ns'; rw [PossiblyInfiniteTree.drop_drop]; exact t.finitely_many_children (ns ++ ns')

  theorem drop_nil {t : FiniteDegreeTree α} : t.drop [] = t := by rfl

  theorem get?_drop {t : FiniteDegreeTree α} {ns ns' : List Nat} : (t.drop ns).get? ns' = t.get? (ns ++ ns') := by rfl

  theorem drop_drop {t : FiniteDegreeTree α} {ns ns' : List Nat} : (t.drop ns).drop ns' = t.drop (ns ++ ns') := by simp [drop, PossiblyInfiniteTree.drop_drop]

  theorem ext {t1 t2 : FiniteDegreeTree α} : (∀ ns, t1.get? ns = t2.get? ns) -> t1 = t2 := by
    intro h; rw [FiniteDegreeTree.mk.injEq]; apply PossiblyInfiniteTree.ext; exact h

  theorem ext_iff {t1 t2 : FiniteDegreeTree α} : t1 = t2 ↔ (∀ ns, t1.get? ns = t2.get? ns) := by
    constructor
    . intro h _; rw [h]
    . exact ext

  def root (t : FiniteDegreeTree α) : Option α := t.tree.root

  theorem root_eq {t : FiniteDegreeTree α} : t.root = t.get? [] := by rfl

  theorem root_drop {t : FiniteDegreeTree α} {ns : List Nat} : (t.drop ns).root = t.get? ns := by
    unfold root drop; simp [PossiblyInfiniteTree.root_drop]; rfl

  abbrev FiniteDegreeTreeWithRoot (α : Type u) := {t : FiniteDegreeTree α // t.root ≠ none}

  namespace FiniteDegreeTreeWithRoot

    def from_possibly_infinite (t : PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot α) (fin : t.val.finitely_many_children) : FiniteDegreeTreeWithRoot α := ⟨{tree := t.val, finitely_many_children := fin}, t.property⟩

    def to_possibly_infinite (t : FiniteDegreeTreeWithRoot α) : PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot α :=
      ⟨t.val.tree, t.property⟩

    theorem from_possibly_infinite_after_to_possibly_infinite {t : FiniteDegreeTreeWithRoot α} :
      from_possibly_infinite (t.to_possibly_infinite) t.val.finitely_many_children = t := by rfl

    theorem to_possibly_infinite_after_from_possibly_infinite (t : PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot α) (fin : t.val.finitely_many_children) :
      (from_possibly_infinite t fin).to_possibly_infinite = t := by rfl

    def opt_to_tree (opt : Option (FiniteDegreeTreeWithRoot α)) : FiniteDegreeTree α where
      tree := PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree (opt.map to_possibly_infinite)
      finitely_many_children := by
        cases opt with
        | none => exact PossiblyInfiniteTree.finitely_many_children_empty
        | some t => exact t.val.finitely_many_children

    theorem opt_to_tree_none_iff {opt : Option (FiniteDegreeTreeWithRoot α)} : opt = none ↔ (opt_to_tree opt).root = none := by
      unfold opt_to_tree root
      rw [← PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]
      simp

    def tree_to_opt (t : FiniteDegreeTree α) : Option (FiniteDegreeTreeWithRoot α) :=
      (PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt t.tree).attach.map (fun t' =>
        from_possibly_infinite t'.val (by have prop := t'.property; rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff] at prop; rw [← prop.left]; exact t.finitely_many_children))

    theorem tree_to_opt_none_iff {t : FiniteDegreeTree α} : tree_to_opt t = none ↔ t.root = none := by
      unfold tree_to_opt root
      rw [← PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff]
      simp

    theorem tree_to_opt_some_iff {t : FiniteDegreeTree α} : ∀ {t'}, tree_to_opt t = some t' ↔ t = t' ∧ t.root.isSome := by
      intro t'
      unfold tree_to_opt
      rw [Option.map_attach_eq_pmap, Option.pmap_eq_some_iff]
      constructor
      . rintro ⟨a, _, a_eq, t'_eq⟩
        rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff] at a_eq
        constructor
        . rw [t'_eq]; rw [FiniteDegreeTree.mk.injEq]; exact a_eq.left
        . exact a_eq.right
      . rintro ⟨t_eq, root_some⟩
        exists to_possibly_infinite t', (by
          rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff]
          constructor
          . rw [t_eq]; rfl
          . exact root_some)
        constructor
        . rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff]
          constructor
          . rw [t_eq]; rfl
          . exact root_some
        . simp [from_possibly_infinite_after_to_possibly_infinite]

    theorem tree_to_opt_after_opt_to_tree {opt : Option (FiniteDegreeTreeWithRoot α)} :
        tree_to_opt (opt_to_tree opt) = opt := by
      unfold opt_to_tree tree_to_opt
      rw [Option.map_attach_eq_pmap]
      simp only [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_after_opt_to_tree]
      rw [Option.pmap_map]
      simp only [from_possibly_infinite_after_to_possibly_infinite]
      simp

    theorem opt_to_tree_after_tree_to_opt {t : FiniteDegreeTree α} :
        opt_to_tree (tree_to_opt t) = t := by
      unfold opt_to_tree tree_to_opt
      rw [Option.map_attach_eq_pmap]
      simp only [Option.map_pmap, to_possibly_infinite_after_from_possibly_infinite]
      simp only [Option.pmap_eq_map, Option.map_id']
      simp only [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]

  end FiniteDegreeTreeWithRoot

  def childTrees (t : FiniteDegreeTree α) : List (FiniteDegreeTreeWithRoot α) :=
    (t.tree.childTrees.toList_of_finite (t.finitely_many_children [])).attach.map (fun t' => FiniteDegreeTreeWithRoot.from_possibly_infinite t'.val (by
      intro ns
      have t'_mem := t'.property
      rw [PossiblyInfiniteList.mem_toList_of_finite, PossiblyInfiniteList.mem_iff] at t'_mem;
      rcases t'_mem with ⟨n, t'_mem⟩
      rw [PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff] at t'_mem
      rw [← t'_mem.left]
      exact t.finitely_many_children (n::ns)))

  def node (root : α) (childTrees : List (FiniteDegreeTreeWithRoot α)) : FiniteDegreeTree α where
    tree := PossiblyInfiniteTree.node root (PossiblyInfiniteList.from_list (childTrees.map FiniteDegreeTreeWithRoot.to_possibly_infinite))
    finitely_many_children := by
      intro ns
      cases ns with
      | nil => exists childTrees.length; rw [PossiblyInfiniteTree.drop_nil, PossiblyInfiniteTree.childTrees_node, PossiblyInfiniteList.get?_from_list, List.getElem?_map, (List.getElem?_eq_none (by simp)), Option.map_none]
      | cons n ns =>
        rw [PossiblyInfiniteTree.drop_node_cons, PossiblyInfiniteList.get?_from_list, List.getElem?_map]
        cases Decidable.em (n < childTrees.length) with
        | inl n_le => rw [List.getElem?_eq_getElem n_le]; exact childTrees[n].val.finitely_many_children ns
        | inr n_le => rw [List.getElem?_eq_none (Nat.le_of_not_lt n_le), Option.map_none]; simp only [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree]; rw [PossiblyInfiniteTree.drop_empty, PossiblyInfiniteTree.childTrees_empty]; exact PossiblyInfiniteList.finite_empty

  theorem get?_node_nil {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} : (node root childTrees).get? [] = .some root := by rfl
  theorem get?_node_cons {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} : ∀ n ns, (node root childTrees).get? (n :: ns) = (FiniteDegreeTreeWithRoot.opt_to_tree childTrees[n]?).get? ns := by
    intro n ns
    simp only [node, get?]
    rw [PossiblyInfiniteTree.get?_node_cons, PossiblyInfiniteList.get?_from_list, List.getElem?_map]
    rfl

  theorem root_node {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} : (node root childTrees).root = root := by rfl
  theorem childTrees_node {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} : (node root childTrees).childTrees = childTrees := by
    simp only [node, FiniteDegreeTree.childTrees]
    apply List.ext_getElem?
    intro n
    rw [List.getElem?_map, List.getElem?_attach]
    simp only [PossiblyInfiniteTree.childTrees_node]
    simp only [PossiblyInfiniteList.toList_of_finite_after_from_list]
    cases eq : childTrees[n]? with
    | none => simp only [List.getElem?_map, eq]; simp
    | some t => simp only [List.getElem?_map, eq]; simp [FiniteDegreeTreeWithRoot.from_possibly_infinite_after_to_possibly_infinite]

  theorem node_root_childTrees {t : FiniteDegreeTree α} {root : α} (h : t.root = .some root) : t = node root t.childTrees := by
    rw [FiniteDegreeTree.mk.injEq]
    simp only [node]
    rw [PossiblyInfiniteTree.node_root_childTrees h]
    apply congrArg
    unfold childTrees
    apply PossiblyInfiniteList.ext
    intro n
    rw [PossiblyInfiniteList.get?_from_list, List.getElem?_map]
    rw [List.getElem?_map, List.getElem?_attach]
    cases eq : t.tree.childTrees.get? n with
    | none => simp only [PossiblyInfiniteList.getElem?_toList_of_finite, eq]; simp
    | some => simp only [PossiblyInfiniteList.getElem?_toList_of_finite, eq, Option.pmap_some, Option.map_some]; rw [FiniteDegreeTreeWithRoot.to_possibly_infinite_after_from_possibly_infinite]

  theorem get?_childTrees {t : FiniteDegreeTree α} : ∀ n, t.childTrees[n]? = FiniteDegreeTreeWithRoot.tree_to_opt (t.drop [n]) := by
    intro n
    unfold childTrees
    rw [List.getElem?_map, List.getElem?_attach]
    simp only [PossiblyInfiniteList.getElem?_toList_of_finite]
    unfold FiniteDegreeTreeWithRoot.tree_to_opt
    rw [Option.map_attach_eq_pmap, Option.map_pmap]
    cases eq : PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt (t.tree.drop [n]) <;> simp [PossiblyInfiniteTree.get?_childTrees, drop, eq]

  theorem get_childTrees {t : FiniteDegreeTree α} : ∀ n, (lt : n < t.childTrees.length) -> t.childTrees[n].val = t.drop [n] := by
    intro n lt
    have get_some : t.childTrees[n]?.isSome := by rw [List.getElem?_eq_getElem lt]; simp
    have root_some : (t.drop [n]).root.isSome := by
      rw [get?_childTrees] at get_some
      rw [Option.isSome_iff_exists] at get_some
      rcases get_some with ⟨t', get_some⟩
      rw [FiniteDegreeTreeWithRoot.tree_to_opt_some_iff] at get_some
      exact get_some.right
    have : t.childTrees[n] = ⟨t.drop [n], by intro contra; rw [contra] at root_some; simp at root_some⟩ := by
      rw [List.getElem_eq_iff]
      rw [get?_childTrees]
      rw [FiniteDegreeTreeWithRoot.tree_to_opt_some_iff]
      constructor
      . rfl
      . exact root_some
    rw [this]

  theorem get?_get?_childTrees {t : FiniteDegreeTree α} : ∀ n ns, (FiniteDegreeTreeWithRoot.opt_to_tree t.childTrees[n]?).get? ns = t.get? (n::ns) := by intros; rw [get?_childTrees, FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt]; rfl

  theorem drop_node_cons {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} {n : Nat} {ns : List Nat} : (node root childTrees).drop (n::ns) = (FiniteDegreeTreeWithRoot.opt_to_tree childTrees[n]?).drop ns := by
    simp only [node, drop, PossiblyInfiniteTree.drop_node_cons]
    unfold FiniteDegreeTreeWithRoot.opt_to_tree
    simp only [PossiblyInfiniteList.get?_from_list, List.getElem?_map]

  def childNodes (t : FiniteDegreeTree α) : List α := t.tree.childNodes.toList_of_finite (by rcases t.finitely_many_children [] with ⟨k, fin⟩; exists k; rw [PossiblyInfiniteTree.get?_childNodes, ← PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]; exact fin)

  theorem get?_childNodes {t : FiniteDegreeTree α} : ∀ {n : Nat}, t.childNodes[n]? = (FiniteDegreeTreeWithRoot.opt_to_tree t.childTrees[n]?).root := by
    intro n
    rw [get?_childTrees, FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt]
    unfold childNodes
    rw [PossiblyInfiniteList.getElem?_toList_of_finite]
    rw [PossiblyInfiniteTree.get?_childNodes, PossiblyInfiniteTree.get?_childTrees]
    rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]
    rfl

  theorem childNodes_eq {t : FiniteDegreeTree α} : t.childNodes = t.childTrees.map (fun t => t.val.root.get (by rw [Option.isSome_iff_ne_none]; exact t.property)) := by
    unfold childNodes
    simp only [PossiblyInfiniteTree.childNodes_eq]
    rw [← PossiblyInfiniteList.map_toList_of_finite (l := t.tree.childTrees) (fin := (t.finitely_many_children []))]
    apply List.ext_getElem
    . simp only [List.length_map, childTrees, List.length_attach]
    . intro i _ _
      simp only [List.getElem_map]
      rw [Option.get_inj]
      unfold childTrees
      simp only [List.getElem_map, List.getElem_attach]
      rfl

  theorem length_childNodes {t : FiniteDegreeTree α} : t.childNodes.length = t.childTrees.length := by
    rw [childNodes_eq, List.length_map]

  theorem get_childNodes {t : FiniteDegreeTree α} : ∀ n, (lt : n < t.childNodes.length) -> t.childNodes[n] = (t.childTrees[n]'(by rw [← length_childNodes]; exact lt)).val.root := by
    intro n lt; rw [List.getElem_eq_getElem?_get, Option.some_get, get?_childNodes, get?_childTrees, FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt, get_childTrees]

  theorem no_orphans {t : FiniteDegreeTree α} : ∀ ns : List Nat, t.get? ns = none -> ∀ n : Nat, (t.drop ns).childNodes[n]? = none := by intro ns eq_none n; unfold childNodes; rw [PossiblyInfiniteList.getElem?_toList_of_finite]; apply t.tree.no_orphans'; exact eq_none

  theorem no_orphans_closure {t : FiniteDegreeTree α} :
      ∀ ns : List Nat, t.get? ns = none -> ∀ ns', (t.drop ns).get? ns' = none := by
    exact t.tree.no_orphans'_closure

  def branches (t : FiniteDegreeTree α) : Set (PossiblyInfiniteList α) := t.tree.branches

  theorem branches_eq {t : FiniteDegreeTree α} : t.branches = fun b =>
      b.head = t.root ∧ ((t.childTrees = [] ∧ b.tail = PossiblyInfiniteList.empty) ∨ (∃ c ∈ t.childTrees, b.tail ∈ c.val.branches)) := by
    unfold branches
    rw [PossiblyInfiniteTree.branches_eq]
    apply Set.ext
    intro b
    constructor
    . rintro ⟨head_eq, tail_eq⟩
      constructor
      . exact head_eq
      cases tail_eq with
      | inl tail_eq =>
        apply Or.inl
        constructor
        . unfold childTrees
          rw [List.map_eq_nil_iff, List.attach_eq_nil_iff]
          rw [PossiblyInfiniteList.toList_of_finite_empty_iff]
          exact tail_eq.left
        . exact tail_eq.right
      | inr tail_eq =>
        apply Or.inr
        rcases tail_eq with ⟨c, c_mem, tail_mem⟩
        rcases c_mem with ⟨i, c_mem⟩
        rw [← PossiblyInfiniteList.get?.eq_def] at c_mem
        rw [PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff] at c_mem
        exists FiniteDegreeTreeWithRoot.from_possibly_infinite c (by
          intro ns
          rw [← c_mem.left, PossiblyInfiniteTree.drop_drop]
          apply t.finitely_many_children)
        constructor
        . rw [List.mem_iff_getElem?]
          exists i
          rw [get?_childTrees, FiniteDegreeTreeWithRoot.tree_to_opt_some_iff]
          unfold FiniteDegreeTreeWithRoot.from_possibly_infinite
          constructor
          . rw [FiniteDegreeTree.mk.injEq]
            exact c_mem.left
          . exact c_mem.right
        . exact tail_mem
    . rintro ⟨head_eq, tail_eq⟩
      constructor
      . exact head_eq
      cases tail_eq with
      | inl tail_eq =>
        apply Or.inl
        constructor
        . unfold childTrees at tail_eq
          rw [List.map_eq_nil_iff, List.attach_eq_nil_iff] at tail_eq
          rw [PossiblyInfiniteList.toList_of_finite_empty_iff] at tail_eq
          exact tail_eq.left
        . exact tail_eq.right
      | inr tail_eq =>
        apply Or.inr
        rcases tail_eq with ⟨c, c_mem, tail_mem⟩
        rw [List.mem_iff_getElem?] at c_mem
        rcases c_mem with ⟨i, c_mem⟩
        rw [get?_childTrees, FiniteDegreeTreeWithRoot.tree_to_opt_some_iff] at c_mem
        exists FiniteDegreeTreeWithRoot.to_possibly_infinite c
        constructor
        . exists i
          rw [← PossiblyInfiniteList.get?.eq_def]
          rw [PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff]
          unfold FiniteDegreeTreeWithRoot.to_possibly_infinite
          constructor
          . rw [FiniteDegreeTree.mk.injEq] at c_mem
            exact c_mem.left
          . exact c_mem.right
        . exact tail_mem

  def leaves (t : FiniteDegreeTree α) : Set α := t.tree.leaves

  def from_branch (b : PossiblyInfiniteList α) : FiniteDegreeTree α where
    tree := PossiblyInfiniteTree.from_branch b
    finitely_many_children := by
      intro ns
      exists 1
      rw [PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.drop_drop]
      rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff]
      simp only [PossiblyInfiniteTree.from_branch, PossiblyInfiniteTree.root_eq, PossiblyInfiniteTree.get?_drop]
      simp only [PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
      simp

end FiniteDegreeTree

