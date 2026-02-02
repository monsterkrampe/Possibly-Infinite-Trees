import BasicLeanDatastructures.Set.Finite

import PossiblyInfiniteTrees.PossiblyInfiniteTree.PossiblyInfiniteTree

/-!
# FiniteDegreeTree

This file defines a `FiniteDegreeTree` which is a `PossiblyInfiniteTree` where each node has only finitely many children.
The offered functions are similar to the ones of `PossiblyInfiniteTree`.
The tree can now only infinite in one dimensions, i.e. it can have infinite depth but
each node has only finitely many children by definition.
However, note that there is no (global) bound for the number of children.
The number of children might grow arbitrarily along the tree as long as it is finite everywhere.
-/

/-- A `PossiblyInfiniteTree` has `finitely_many_children` if for each subtree, the list of `PossiblyInfiniteTree.childTrees` is `PossiblyInfiniteList.finite`. -/
def PossiblyInfiniteTree.finitely_many_children (t : PossiblyInfiniteTree α) : Prop :=
  ∀ subtree, subtree <:+ t -> subtree.childTrees.finite

/-- The `PossiblyInfiniteTree.empty` tree has `finitely_many_children`. -/
theorem PossiblyInfiniteTree.finitely_many_children_empty {α} :
    (@PossiblyInfiniteTree.empty α).finitely_many_children := by
  intro _ suf; rw [empty_suffix_of_empty suf, childTrees_empty]; exact PossiblyInfiniteList.finite_empty

/-- A `FiniteDegreeTree` is a `PossiblyInfiniteTree` with the `finitely_many_children` property. -/
structure FiniteDegreeTree (α : Type u) where
  tree : PossiblyInfiniteTree α
  finitely_many_children : tree.finitely_many_children

namespace FiniteDegreeTree

section Basic

/-!
## Basics

The essential functions on infinite trees, mainly get, drop, and root.
The `childTrees` function is defined separately here as for the `PossiblyInfiniteTree`.
-/

/-- Obtains the element of the tree at the given address. -/
def get? (t : FiniteDegreeTree α) (ns : List Nat) : Option α := t.tree.get? ns

/-- Obtains the subtree at the given address (by dropping everything else). -/
def drop (t : FiniteDegreeTree α) (ns : List Nat) : FiniteDegreeTree α where
  tree := t.tree.drop ns
  finitely_many_children := by intro _ suf; exact t.finitely_many_children _ (PossiblyInfiniteTree.IsSuffix_trans suf (PossiblyInfiniteTree.IsSuffix_drop ns))

/-- Get the element at the root of the tree (i.e. at the empty address). -/
def root (t : FiniteDegreeTree α) : Option α := t.tree.root

instance : Membership α (FiniteDegreeTree α) where
  mem t a := a ∈ t.tree

/-- An element is a member of the tree iff it occurs at some address. -/
theorem mem_iff {t : FiniteDegreeTree α} : ∀ {e}, e ∈ t ↔ ∃ ns, t.get? ns = some e := by rfl

/-- Two `FiniteDegreeTree`s are the same if they agree on all addresses. -/
theorem ext {t1 t2 : FiniteDegreeTree α} : (∀ ns, t1.get? ns = t2.get? ns) -> t1 = t2 := by
  intro h; rw [FiniteDegreeTree.mk.injEq]; apply PossiblyInfiniteTree.ext; exact h

theorem ext_iff {t1 t2 : FiniteDegreeTree α} : t1 = t2 ↔ (∀ ns, t1.get? ns = t2.get? ns) := by
  constructor
  . intro h _; rw [h]
  . exact ext

/-- Get after drop can be rewritten into get. -/
theorem get?_drop {t : FiniteDegreeTree α} {ns ns' : List Nat} : (t.drop ns).get? ns' = t.get? (ns ++ ns') := by rfl

/-- Dropping the empty address changes nothing. -/
theorem drop_nil {t : FiniteDegreeTree α} : t.drop [] = t := by rfl

/-- Two calls to drop can be combined. -/
theorem drop_drop {t : FiniteDegreeTree α} {ns ns' : List Nat} : (t.drop ns).drop ns' = t.drop (ns ++ ns') := by simp [drop, PossiblyInfiniteTree.drop_drop]

/-- The `root` is equal to getting the empty address. -/
theorem root_eq {t : FiniteDegreeTree α} : t.root = t.get? [] := by rfl

/-- The root is in the tree. -/
theorem root_mem {t : FiniteDegreeTree α} : ∀ r ∈ t.root, r ∈ t := t.tree.root_mem

/-- The root of the dropped tree at address ns is exactly the element at address ns. -/
theorem root_drop {t : FiniteDegreeTree α} {ns : List Nat} : (t.drop ns).root = t.get? ns := by
  unfold root drop; simp [PossiblyInfiniteTree.root_drop]; rfl

end Basic

section Empty

/-!
## Empty Infinite Trees

The `empty` `FiniteDegreeTree` is simply the `FiniteDegreeTree` that is `none` on all addresses. That is, its underlying `PossiblyInfiniteTree` is `PossiblyInfiniteTree.empty`.
-/

/-- The empty `FiniteDegreeTree` is essentially `PossiblyInfiniteTree.empty`. -/
def empty : FiniteDegreeTree α where
  tree := PossiblyInfiniteTree.empty
  finitely_many_children := PossiblyInfiniteTree.finitely_many_children_empty

/-- Getting from the `empty` tree always returns none. -/
theorem get?_empty {α} : ∀ {n}, (@FiniteDegreeTree.empty α).get? n = none := by intro _; rfl

/-- Dropping from the `empty` tree again yields the empty tree. -/
theorem drop_empty {α} : ∀ {ns}, (@FiniteDegreeTree.empty α).drop ns = FiniteDegreeTree.empty := by
  intro _; apply ext; intro _; rw [get?_drop, get?_empty, get?_empty]

/-- The `root` of the `empty` tree is none. -/
theorem root_empty {α} : (@FiniteDegreeTree.empty α).root = none := by rfl

/-- A tree is `empty` if and only if the `root` is none. -/
theorem empty_iff_root_none {t : FiniteDegreeTree α} : t = FiniteDegreeTree.empty ↔ t.root = none := by
  rw [FiniteDegreeTree.mk.injEq]; simp only [empty]; rw [PossiblyInfiniteTree.empty_iff_root_none]; rfl

end Empty

section ChildTrees

/-!
## Child Trees

Defining the `childTrees` function requires a bit of machinery.
We only want to return the child trees that are not already empty.
Then all returned trees have a non-none root, which we aim to capture directly in the return type.
-/

/-- The `FiniteDegreeTreeWithRoot` is a `FiniteDegreeTree` where the `root` is not none. -/
abbrev FiniteDegreeTreeWithRoot (α : Type u) := {t : FiniteDegreeTree α // t.root ≠ none}

namespace FiniteDegreeTreeWithRoot

/-!
### FiniteDegreeTreeWithRoot

For the `FiniteDegreeTreeWithRoot` we mainly provide some functions to convert `FiniteDegreeTree` to and from `Option FiniteDegreeTreeWithRoot`. Clearly, if a `FiniteDegreeTree` has a non-none root, we can convert it directly into a `FiniteDegreeTreeWithRoot`, otherwise, we simply convert it to `none`. Also in the other direction, none can just be converted to `PossiblyInfiniteTree.empty` and any `FiniteDegreeTreeWithRoot` is already a `FiniteDegreeTree`.

So far this is similar to `PossiblyInfiniteTreeWithRoot` and mainly implemented using its existing methods.
For this purpose, we also provide methods `from_possibly_infinite` and `to_possibly_infinite` that allow to convert
between `FiniteDegreeTreeWithRoot` and `PossiblyInfiniteTreeWithRoot`.
-/

def from_possibly_infinite (t : PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot α) (fin : t.val.finitely_many_children) : FiniteDegreeTreeWithRoot α := ⟨{tree := t.val, finitely_many_children := fin}, t.property⟩

def to_possibly_infinite (t : FiniteDegreeTreeWithRoot α) : PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot α :=
  ⟨t.val.tree, t.property⟩

def opt_to_tree (opt : Option (FiniteDegreeTreeWithRoot α)) : FiniteDegreeTree α where
  tree := PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree (opt.map to_possibly_infinite)
  finitely_many_children := by
    cases opt with
    | none => exact PossiblyInfiniteTree.finitely_many_children_empty
    | some t => exact t.val.finitely_many_children

def tree_to_opt (t : FiniteDegreeTree α) : Option (FiniteDegreeTreeWithRoot α) :=
  (PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt t.tree).attach.map (fun t' =>
    from_possibly_infinite t'.val (by have prop := t'.property; rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff] at prop; rw [← prop.left]; exact t.finitely_many_children))

theorem from_possibly_infinite_after_to_possibly_infinite {t : FiniteDegreeTreeWithRoot α} :
  from_possibly_infinite (t.to_possibly_infinite) t.val.finitely_many_children = t := by rfl

theorem to_possibly_infinite_after_from_possibly_infinite (t : PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot α) (fin : t.val.finitely_many_children) :
  (from_possibly_infinite t fin).to_possibly_infinite = t := by rfl

theorem opt_to_tree_none_iff {opt : Option (FiniteDegreeTreeWithRoot α)} : opt = none ↔ (opt_to_tree opt).root = none := by
  unfold opt_to_tree root
  rw [← PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]
  simp

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

/-!
### The actual childTrees definition

With `FiniteDegreeTreeWithRoot` in place, we can now define the actual `childTrees` function.
-/

/-- The `childTrees` of a `FiniteDegreeTree` are the `List` of all child trees that are not empty, i.e. it only consists of `FiniteDegreeTreeWithRoot`. Note that we can indeed build a finite `List` since we have `finitely_many_children` in place. -/
def childTrees (t : FiniteDegreeTree α) : List (FiniteDegreeTreeWithRoot α) :=
  (t.tree.childTrees.toList_of_finite (t.finitely_many_children _ PossiblyInfiniteTree.IsSuffix_refl)).attach.map (fun t' => FiniteDegreeTreeWithRoot.from_possibly_infinite t'.val (by
    intro _ ; rw [PossiblyInfiniteTree.IsSuffix_iff]; rintro ⟨ns, suf⟩
    have t'_mem := t'.property
    rw [PossiblyInfiniteList.mem_toList_of_finite, PossiblyInfiniteList.mem_iff] at t'_mem;
    rcases t'_mem with ⟨n, t'_mem⟩
    rw [PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff] at t'_mem
    rw [← suf, ← t'_mem.left]
    exact t.finitely_many_children _ (PossiblyInfiniteTree.IsSuffix_drop (n::ns))))

/-- `FiniteDegreeTree.childTrees` can be expressed through `PossiblyInfiniteTree.childTrees`. -/
theorem mem_childTrees_iff {t : FiniteDegreeTree α} : ∀ c, c ∈ t.childTrees ↔ c.to_possibly_infinite ∈ t.tree.childTrees := by
  intro c
  simp only [childTrees, List.mem_map, List.mem_attach, true_and]
  constructor
  . rintro ⟨⟨d, d_mem⟩, c_eq⟩
    rw [← c_eq]
    rw [FiniteDegreeTreeWithRoot.to_possibly_infinite_after_from_possibly_infinite]
    rw [PossiblyInfiniteList.mem_toList_of_finite] at d_mem
    exact d_mem
  . intro c_mem
    exists ⟨c.to_possibly_infinite, by rw [PossiblyInfiniteList.mem_toList_of_finite]; exact c_mem⟩

/-- Getting a child tree is the same as dropping the corresponding singleton address. -/
theorem get?_childTrees {t : FiniteDegreeTree α} : ∀ n, t.childTrees[n]? = FiniteDegreeTreeWithRoot.tree_to_opt (t.drop [n]) := by
  intro n
  unfold childTrees
  rw [List.getElem?_map, List.getElem?_attach]
  simp only [PossiblyInfiniteList.getElem?_toList_of_finite]
  unfold FiniteDegreeTreeWithRoot.tree_to_opt
  rw [Option.map_attach_eq_pmap, Option.map_pmap]
  cases eq : PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt (t.tree.drop [n]) <;> simp [PossiblyInfiniteTree.get?_childTrees, drop, eq]

/-- Getting a child tree is the same as dropping the corresponding singleton address. -/
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

/-- Getting at an address in a child tree can be combined into a single get call. -/
theorem get?_get?_childTrees {t : FiniteDegreeTree α} : ∀ n ns, (FiniteDegreeTreeWithRoot.opt_to_tree t.childTrees[n]?).get? ns = t.get? (n::ns) := by intros; rw [get?_childTrees, FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt]; rfl

/-- The `childTrees` of the `empty` tree are exactly `[]`. -/
theorem childTrees_empty {α} : (@FiniteDegreeTree.empty α).childTrees = [] := by
  simp only [childTrees, List.map_eq_nil_iff, List.attach_eq_nil_iff, PossiblyInfiniteList.toList_of_finite_empty_iff, empty]
  exact PossiblyInfiniteTree.childTrees_empty

end ChildTrees

section Node

/-!
## Node Constructor

Similar to the `PossiblyInfiniteTree`, we can also define a `node` constructor on the `FiniteDegreeTree`.
-/

/-- Construct a `FiniteDegreeTree` from a `List` of `FiniteDegreeTreeWithRoot` and a new root element. -/
def node (root : α) (childTrees : List (FiniteDegreeTreeWithRoot α)) : FiniteDegreeTree α where
  tree := PossiblyInfiniteTree.node root (PossiblyInfiniteList.from_list (childTrees.map FiniteDegreeTreeWithRoot.to_possibly_infinite))
  finitely_many_children := by
    intro _; rw [PossiblyInfiniteTree.IsSuffix_iff]; intro ⟨ns, suf⟩; rw [← suf]
    cases ns with
    | nil => exists childTrees.length; rw [PossiblyInfiniteTree.drop_nil, PossiblyInfiniteTree.childTrees_node, PossiblyInfiniteList.get?_from_list, List.getElem?_map, (List.getElem?_eq_none (by simp)), Option.map_none]
    | cons n ns =>
      rw [PossiblyInfiniteTree.drop_node_cons, PossiblyInfiniteList.get?_from_list, List.getElem?_map]
      cases Decidable.em (n < childTrees.length) with
      | inl n_le => rw [List.getElem?_eq_getElem n_le]; exact childTrees[n].val.finitely_many_children _ (by exists ns)
      | inr n_le => rw [List.getElem?_eq_none (Nat.le_of_not_lt n_le), Option.map_none]; simp only [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree]; rw [PossiblyInfiniteTree.drop_empty, PossiblyInfiniteTree.childTrees_empty]; exact PossiblyInfiniteList.finite_empty

/-- Getting the element at address [] on `node` is the new root. -/
theorem get?_node_nil {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} : (node root childTrees).get? [] = .some root := by rfl

/-- Getting any address != [] on `node` yields the respective element from the previous `FiniteDegreeTreeWithRoot`. -/
theorem get?_node_cons {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} : ∀ n ns, (node root childTrees).get? (n :: ns) = (FiniteDegreeTreeWithRoot.opt_to_tree childTrees[n]?).get? ns := by
  intro n ns
  simp only [node, get?]
  rw [PossiblyInfiniteTree.get?_node_cons, PossiblyInfiniteList.get?_from_list, List.getElem?_map]
  rfl

/-- Dropping from `node` with an address of the form `n::ns` is the same as getting the `n` child from the child trees used in the construction and then dropping `ns` there.  -/
theorem drop_node_cons {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} {n : Nat} {ns : List Nat} : (node root childTrees).drop (n::ns) = (FiniteDegreeTreeWithRoot.opt_to_tree childTrees[n]?).drop ns := by
  simp only [node, drop, PossiblyInfiniteTree.drop_node_cons]
  unfold FiniteDegreeTreeWithRoot.opt_to_tree
  simp only [PossiblyInfiniteList.get?_from_list, List.getElem?_map]

/-- The `root` of `node` is the root used in the construction. -/
theorem root_node {root : α} {childTrees : List (FiniteDegreeTreeWithRoot α)} : (node root childTrees).root = root := by rfl

/-- The `childTrees` of `node` are the childTrees used in the construction. -/
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

/-- Any `FiniteDegreeTree` where the `root` is not none can be written using the `node` constructor. -/
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

end Node

section ChildNodes

/-!
# ChildNodes

It can be convenient to obtain a list of the immediate child nodes of a given tree.
This is equivalent to mapping each child tree to its root.
-/

/-- The `childNodes` are `PossiblyInfiniteTree.childNodes`. -/
def childNodes (t : FiniteDegreeTree α) : List α := t.tree.childNodes.toList_of_finite (by rcases t.finitely_many_children _ PossiblyInfiniteTree.IsSuffix_refl with ⟨k, fin⟩; exists k; rw [PossiblyInfiniteTree.get?_childNodes, ← PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]; exact fin)

/-- Getting the nth `childNodes` is the root of the nth `childTrees`. -/
theorem get?_childNodes {t : FiniteDegreeTree α} : ∀ {n : Nat}, t.childNodes[n]? = (FiniteDegreeTreeWithRoot.opt_to_tree t.childTrees[n]?).root := by
  intro n
  rw [get?_childTrees, FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt]
  unfold childNodes
  rw [PossiblyInfiniteList.getElem?_toList_of_finite]
  rw [PossiblyInfiniteTree.get?_childNodes, PossiblyInfiniteTree.get?_childTrees]
  rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]
  rfl

/-- The `childNodes` are the `root`s of the `childTrees`. -/
theorem childNodes_eq {t : FiniteDegreeTree α} : t.childNodes = t.childTrees.map (fun t => t.val.root.get (by rw [Option.isSome_iff_ne_none]; exact t.property)) := by
  unfold childNodes
  simp only [PossiblyInfiniteTree.childNodes_eq]
  rw [← PossiblyInfiniteList.map_toList_of_finite (l := t.tree.childTrees) (fin := (t.finitely_many_children _ PossiblyInfiniteTree.IsSuffix_refl))]
  apply List.ext_getElem
  . simp only [List.length_map, childTrees, List.length_attach]
  . intro i _ _
    simp only [List.getElem_map]
    rw [Option.get_inj]
    unfold childTrees
    simp only [List.getElem_map, List.getElem_attach]
    rfl

/-- The `childNodes` have the same length as the `childTrees`. -/
theorem length_childNodes {t : FiniteDegreeTree α} : t.childNodes.length = t.childTrees.length := by
  rw [childNodes_eq, List.length_map]

/-- Getting the nth `childNodes` is the root of the nth `childTrees`. -/
theorem get_childNodes {t : FiniteDegreeTree α} : ∀ n, (lt : n < t.childNodes.length) -> t.childNodes[n] = (t.childTrees[n]'(by rw [← length_childNodes]; exact lt)).val.root := by
  intro n lt; rw [List.getElem_eq_getElem?_get, Option.some_get, get?_childNodes, get?_childTrees, FiniteDegreeTreeWithRoot.opt_to_tree_after_tree_to_opt, get_childTrees]

/-- Each child node is a tree member. -/
theorem mem_of_mem_childNodes {t : FiniteDegreeTree α} : ∀ c ∈ t.childNodes, c ∈ t := by
  intro c c_mem; apply t.tree.mem_of_mem_childNodes; unfold childNodes at c_mem; rw [PossiblyInfiniteList.mem_toList_of_finite] at c_mem; exact c_mem

/-- The `childNodes` of the `empty` tree are `[]`. -/
theorem childNodes_empty {α} : (@FiniteDegreeTree.empty α).childNodes = [] := by
  simp only [childNodes, PossiblyInfiniteList.toList_of_finite_empty_iff, empty]
  exact PossiblyInfiniteTree.childNodes_empty

end ChildNodes

section Suffixes

/-!
## Suffixes

Here, we define a suffix relation on `FiniteDegreeTree` inspired by `List.IsSuffix`.
For `t1` and `t2`, `t1 <:+ t2` denotes that `t1` is a subtree of `t2`.

The suffix relation is reflexive and transitive but not necesarrily antisymmetric!
Note also that `InfiniteList.suffix_or_suffix_of_suffix` has no equivalent statement here, i.e.
just because two trees are subtrees of the same parent tree, we cannot say anything about their relation to one another.
They might be totally "disconnected".
-/

/-- A suffix relation on infinite trees. This is inspired by `List.IsSuffix`. Read `t1 <:+ t2` as: t1 is a subtree of t2. -/
def IsSuffix (t1 t2 : FiniteDegreeTree α) : Prop := t1.tree <:+ t2.tree
infixl:50 " <:+ " => IsSuffix

/-- t1 is a subtree of t2 if t1 can be obtained from t2 by dropping. -/
theorem IsSuffix_iff {t1 t2 : FiniteDegreeTree α} : t1 <:+ t2 ↔ ∃ ns, t2.drop ns = t1 := by
  constructor
  . rintro ⟨ns, h⟩; exists ns; simp [drop, PossiblyInfiniteTree.drop, h]
  . rintro ⟨ns, h⟩; exists ns; simp only [drop, PossiblyInfiniteTree.drop] at h; rw [← h]

/-- The suffix relation is reflexive. -/
theorem IsSuffix_refl {t : FiniteDegreeTree α} : t <:+ t := t.tree.IsSuffix_refl

/-- The suffix relation is transitive. -/
theorem IsSuffix_trans {t1 t2 t3 : FiniteDegreeTree α} : t1 <:+ t2 -> t2 <:+ t3 -> t1 <:+ t3 := PossiblyInfiniteTree.IsSuffix_trans

/-- A member of a subtree is also a member of the current tree. -/
theorem mem_of_mem_suffix {t1 t2 : FiniteDegreeTree α} (suffix : t1 <:+ t2) : ∀ e ∈ t1, e ∈ t2 := PossiblyInfiniteTree.mem_of_mem_suffix suffix

/-- Dropping elements yields a subtree. -/
theorem IsSuffix_drop {t : FiniteDegreeTree α} : ∀ ns, t.drop ns <:+ t := t.tree.IsSuffix_drop

/-- Each child tree is a subtree. -/
theorem IsSuffix_of_mem_childTrees {t : FiniteDegreeTree α} : ∀ c ∈ t.childTrees, c.val <:+ t := by
  intro c c_mem; rw [mem_childTrees_iff] at c_mem
  exact t.tree.IsSuffix_of_mem_childTrees _ c_mem

/-- Every suffix of the empty tree is empty. -/
theorem empty_suffix_of_empty {t : FiniteDegreeTree α} : t <:+ empty -> t = empty := by
  intro suf; rw [IsSuffix_iff] at suf; rcases suf with ⟨_, suf⟩; rw [← suf]; exact drop_empty

/-- We can express the `PossiblyInfiniteTree.no_orphans'` condition directly on `FiniteDegreeTree`. -/
theorem no_orphans {t : FiniteDegreeTree α} :
    ∀ subtree, subtree <:+ t -> subtree.root = none -> subtree.childNodes = [] := by
  intro _; unfold childNodes; rw [PossiblyInfiniteList.toList_of_finite_empty_iff]; apply t.tree.no_orphans'

end Suffixes

section ElementRecursor

/-!
## Recursor for Members

We define a recursion (induction) principle for members (`Element`s) of an `FiniteDegreeTree` called `mem_rec`.
This can be used with the `induction` tactic to prove a property for each `Element` of an `FiniteDegreeTree`.
Note that for using this coveniently, the goal needs to expressed (rewritten) using an `Element`.
-/

/-- A tree `Element` is a Subtype featuring a proof of being a tree member. -/
def Element (t : FiniteDegreeTree α) := { e : α // e ∈ t }

/-- A recursor for proving properties about tree members (`Element`s) via induction. -/
theorem mem_rec
    {t : FiniteDegreeTree α}
    {motive : Element t -> Prop}
    (root : ∀ r, (mem : r ∈ t.root) -> motive ⟨r, root_mem _ mem⟩)
    (step : ∀ t2, (suffix : t2 <:+ t) -> (∃ (r : α) (mem : r ∈ t2.root), motive ⟨r, t2.mem_of_mem_suffix suffix _ (t2.root_mem _ mem)⟩) -> ∀ {c}, (mem : c ∈ t2.childNodes) -> motive ⟨c, mem_of_mem_suffix suffix _ (mem_of_mem_childNodes _ mem)⟩)
    (a : Element t) :
    motive a := by
  induction a using PossiblyInfiniteTree.mem_rec with
  | root r r_mem => exact root r r_mem
  | step t2 suffix ih c_mem =>
    rw [PossiblyInfiniteTree.IsSuffix_iff] at suffix
    rcases suffix with ⟨ns, suffix⟩
    apply step (t.drop ns) (t.IsSuffix_drop ns)
    . rcases ih with ⟨r, r_mem, ih⟩; rw [← suffix] at r_mem; exists r, r_mem
    . rw [← suffix] at c_mem; unfold childNodes; rw [PossiblyInfiniteList.mem_toList_of_finite]; exact c_mem

end ElementRecursor

section Branches

/-!
# Branches

Branches are essentially `PossiblyInfiniteList`s in a `FiniteDegreeTree`
and can be characterizes by an infinite "address", i.e. `InfiniteList Nat`.
Here, we merely define them as the branches of the underlying `PossiblyInfiniteTree`.
-/

/-- The `branches` in the `FiniteDegreeTree` are exactly the branches in the underlying `PossiblyInfiniteTree`. -/
def branches (t : FiniteDegreeTree α) : Set (PossiblyInfiniteList α) := t.tree.branches

/-- The set of `branches` can equivalently be expressed as the set of all `PossiblyInfiniteList`s where the head equals the root of the tree and the tail occurs in the branches of some childTree. If there are no childTrees, then the tail needs to be empty. -/
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
        rw [← c_mem.left]; intro _ suf
        apply t.finitely_many_children _ (PossiblyInfiniteTree.IsSuffix_trans suf (PossiblyInfiniteTree.IsSuffix_drop _)))
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

end Branches

section Generate

/-!
# Branch Generation

We can use `PossiblyInfiniteList.generate` to construct `branches` in a `FiniteDegreeTree`.
Here, we just proxy the existing function `PossiblyInfiniteTree.generate_branch`.
First of all, this requires that the mapper function produces a `FiniteDegreeTreeWithRoot`.
Intuitively, using all the roots of these trees gives us a branch.
But this is only true if the generate trees are always child trees of each other and the generation indeed creates a maximal branch, meaning that once the generation stops, there would indeed by no `childTrees` to continue.
This condition is used in the `generate_branch_mem_branches` theorem to proof that a `PossiblyInfiniteList`
from the `generate_branch` function is indeed in `branches`.
-/

/-- Given a generator and a mapper that maps generated elements to `FiniteDegreeTreeWithRoot`, construct an `PossiblyInfiniteList` with the goal of constructing a branch in a tree. -/
def generate_branch (start : Option β) (generator : β -> Option β) (mapper : β -> FiniteDegreeTreeWithRoot α) : PossiblyInfiniteList α :=
  PossiblyInfiniteTree.generate_branch start generator (fun b => (mapper b).to_possibly_infinite)

/-- If the generated trees are `childTrees` of each other and the generated branch is maximal, i.e. the generation only stops if there are no `childTrees` available anymore, then the generated `PossiblyInfiniteList` is indeed a branch. -/
theorem generate_branch_mem_branches {start : Option β} {generator : β -> Option β} {mapper : β -> FiniteDegreeTreeWithRoot α}
    (next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).val.childTrees)
    (maximal : ∀ b, generator b = none -> (mapper b).val.childTrees = [])
    (isSome_start : start.isSome) :
    generate_branch start generator mapper ∈ (mapper (start.get isSome_start)).val.branches := by
  apply PossiblyInfiniteTree.generate_branch_mem_branches
  . intro b b' b'_mem
    specialize next_is_child b b' b'_mem
    simp only [childTrees, List.mem_map, List.mem_attach, true_and] at next_is_child
    rcases next_is_child with ⟨t, next_is_child⟩
    rw [← next_is_child, FiniteDegreeTreeWithRoot.to_possibly_infinite_after_from_possibly_infinite]
    simp only [FiniteDegreeTreeWithRoot.to_possibly_infinite]
    rw [← PossiblyInfiniteList.mem_toList_of_finite]
    exact t.property
  . intro b eq_none
    specialize maximal b eq_none
    simp only [childTrees, List.map_eq_nil_iff, List.attach_eq_nil_iff, PossiblyInfiniteList.toList_of_finite_empty_iff] at maximal
    simp only [FiniteDegreeTreeWithRoot.to_possibly_infinite]
    exact maximal

/-- The `PossiblyInfiniteList.head` of `generate_branch` is the `root` of the first tree. -/
theorem head_generate_branch {start : Option β} {generator : β -> Option β} {mapper : β -> FiniteDegreeTreeWithRoot α} : (generate_branch start generator mapper).head = start.map (fun s => (mapper s).val.root.get (by rw [Option.isSome_iff_ne_none]; exact (mapper s).property)) := PossiblyInfiniteTree.head_generate_branch

/-- Getting the nth element from a `generate_branch` result is the root of the nth generated tree. -/
theorem get?_generate_branch {start : Option β} {generator : β -> Option β} {mapper : β -> FiniteDegreeTreeWithRoot α} :
  ∀ n, (generate_branch start generator mapper).get? n = ((PossiblyInfiniteList.generate start generator mapper).get? n).map (fun t => t.val.root.get (by rw [Option.isSome_iff_ne_none]; exact t.property)) := by intro n; simp only [generate_branch, PossiblyInfiniteTree.get?_generate_branch, PossiblyInfiniteList.get?_generate, Option.map_map, FiniteDegreeTreeWithRoot.to_possibly_infinite]; rfl

/-- The `PossiblyInfiniteList.tail` of `generate_branch` is the branch generated when applying the generator function once on the starting element before the actual generation. -/
theorem tail_generate_branch {start : Option β} {generator : β -> Option β} {mapper : β -> FiniteDegreeTreeWithRoot α} : (generate_branch start generator mapper).tail = generate_branch (start.bind generator) generator mapper := PossiblyInfiniteTree.tail_generate_branch

end Generate

section Leaves

/-!
## Leaves

The `leaves` of a `FiniteDegreeTree` is the set of elements that occur in a node that has no `childNodes`.
The function is simply defined via `PossiblyInfiniteTree.leaves` for the underlying tree.
-/

def leaves (t : FiniteDegreeTree α) : Set α := t.tree.leaves

end Leaves

section FromBranch

/-!
## Constructing a Tree from a Branch

A `PossiblyInfiniteList` directly corresponds to the `FiniteDegreeTree`
where the list is the "first" branch (with the address that only consists of zeros) and all other nodes are none.
-/

def from_branch (b : PossiblyInfiniteList α) : FiniteDegreeTree α where
  tree := PossiblyInfiniteTree.from_branch b
  finitely_many_children := by
    intro _; rw [PossiblyInfiniteTree.IsSuffix_iff]; intro ⟨_, suf⟩; rw [← suf]
    exists 1
    rw [PossiblyInfiniteTree.get?_childTrees, PossiblyInfiniteTree.drop_drop]
    rw [PossiblyInfiniteTree.PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff]
    simp only [PossiblyInfiniteTree.from_branch, PossiblyInfiniteTree.root_eq, PossiblyInfiniteTree.get?_drop]
    simp only [PossiblyInfiniteTree.get?, InfiniteTreeSkeleton.get]
    simp

end FromBranch

end FiniteDegreeTree

