import PossiblyInfiniteTrees.PossiblyInfiniteTree.InfiniteTree

/-!
# PossiblyInfiniteTree

This file defines a `PossiblyInfiniteTree` which is an `InfiniteTreeSkeleton` over an `Option` of the desired type.
The offered functions are similar to the ones of `InfiniteTreeSkeleton`.
The tree can still be infinite in both dimensions, i.e.
it may have infinite depth and each node may have infinitely many (direct) children.
-/


/-- An `InfiniteTreeSkeleton` over `Option` has `no_orphans` if an element being `none` implies its `InfiniteTreeSkeleton.childNodes` also being `none`. That is, intuitively, every non-none node needs to have a non-none parent. This is a property that we want for possibly infinite trees but we need to be able to express it on the underlying infinite tree first. -/
def InfiniteTreeSkeleton.no_orphans (t : InfiniteTreeSkeleton (Option α)) : Prop :=
  ∀ subtree, subtree <:+ t -> subtree.root = none -> ∀ n ∈ subtree.childNodes, n = none

/-- A closed version of the `no_orphans` property. That is, if an element is none, then not only its immediate childNodes but all nodes in all subtrees are none. -/
theorem InfiniteTreeSkeleton.no_orphans_closure {t : InfiniteTreeSkeleton (Option α)} (no_orph : t.no_orphans) :
    ∀ subtree, subtree <:+ t -> subtree.root = none -> ∀ n ∈ subtree, n = none := by
  intro subtree suf root_none node node_mem
  let node : subtree.Element := ⟨node, node_mem⟩
  show node.val = none
  induction node using InfiniteTreeSkeleton.mem_rec with
  | root => exact root_none
  | step t2 suf2 ih next_mem =>
    exact no_orph _ (InfiniteTreeSkeleton.IsSuffix_trans suf2 suf) ih _ next_mem

/-- A `PossiblyInfiniteTree` is an `InfiniteTreeSkeleton` over `Option` that has `no_orphans` and also for each subtree, its `InfiniteTreeSkeleton.childNodes` have `InfiniteList.no_holes`. The last condition is necessary because we want the trees to be somewhat "compact", meaning that we want to forbid that e.g. the second child for a node is defined but the first child is none. Note that this would not be captured by the `InfiniteTreeSkeleto.no_orphans` property yet. -/
structure PossiblyInfiniteTree (α : Type u) where
  infinite_tree : InfiniteTreeSkeleton (Option α)
  no_orphans : infinite_tree.no_orphans
  no_holes_in_children : ∀ subtree, subtree <:+ infinite_tree -> subtree.childNodes.no_holes

namespace PossiblyInfiniteTree

section Basic

/-!
## Basics

The essential functions on infinite trees, mainly get, drop, and root.
The `childTrees` function is defined separately here since it is more involved than for the `InfiniteTreeSkeleton` case.
-/

/-- Obtains the element of the tree at the given address. -/
def get? (t : PossiblyInfiniteTree α) (ns : List Nat) : Option α := t.infinite_tree.get ns

/-- Obtains the subtree at the given address (by dropping everything else). -/
def drop (t : PossiblyInfiniteTree α) (ns : List Nat) : PossiblyInfiniteTree α where
  infinite_tree := t.infinite_tree.drop ns
  no_orphans := by intro _ suf; apply t.no_orphans; exact InfiniteTreeSkeleton.IsSuffix_trans suf (t.infinite_tree.IsSuffix_drop ns)
  no_holes_in_children := by intro _ suf; apply t.no_holes_in_children; exact InfiniteTreeSkeleton.IsSuffix_trans suf (t.infinite_tree.IsSuffix_drop ns)

/-- Get the element at the root of the tree (i.e. at the empty address). -/
def root (t : PossiblyInfiniteTree α) : Option α := t.infinite_tree.root

instance : Membership α (PossiblyInfiniteTree α) where
  mem t a := some a ∈ t.infinite_tree

/-- An element is a member of the tree iff it occurs at some address. -/
theorem mem_iff {t : PossiblyInfiniteTree α} : ∀ {e}, e ∈ t ↔ ∃ ns, t.get? ns = some e := by rfl

/-- Two `PossiblyInfiniteTree`s are the same if they agree on all addresses. -/
theorem ext {t1 t2 : PossiblyInfiniteTree α} : (∀ ns, t1.get? ns = t2.get? ns) -> t1 = t2 := by
  intro h; rw [PossiblyInfiniteTree.mk.injEq]; apply InfiniteTreeSkeleton.ext; exact h

theorem ext_iff {t1 t2 : PossiblyInfiniteTree α} : t1 = t2 ↔ (∀ ns, t1.get? ns = t2.get? ns) := by
  constructor
  . intro h _; rw [h]
  . exact ext

/-- Get after drop can be rewritten into get. -/
theorem get?_drop {t : PossiblyInfiniteTree α} {ns ns' : List Nat} : (t.drop ns).get? ns' = t.get? (ns ++ ns') := by rfl

/-- Dropping the empty address changes nothing. -/
theorem drop_nil {t : PossiblyInfiniteTree α} : t.drop [] = t := by rfl

/-- Two calls to drop can be combined. -/
theorem drop_drop {t : PossiblyInfiniteTree α} {ns ns' : List Nat} : (t.drop ns).drop ns' = t.drop (ns ++ ns') := by simp [drop, InfiniteTreeSkeleton.drop_drop]

/-- The `root` is equal to getting the empty address. -/
theorem root_eq {t : PossiblyInfiniteTree α} : t.root = t.get? [] := by rfl

/-- The root is in the tree. -/
theorem root_mem {t : PossiblyInfiniteTree α} : ∀ r ∈ t.root, r ∈ t := by intro h h_mem; rw [Option.mem_def] at h_mem; simp only [Membership.mem, ← h_mem]; exact t.infinite_tree.root_mem

/-- The root of the dropped tree at address ns is exactly the element at address ns. -/
theorem root_drop {t : PossiblyInfiniteTree α} {ns : List Nat} : (t.drop ns).root = t.get? ns := by
  unfold root drop; simp [InfiniteTreeSkeleton.root_drop]; rfl

end Basic

section Empty

/-!
## Empty Infinite Trees

The `empty` `PossiblyInfiniteTree` is simply the `PossiblyInfiniteTree` that is `none` on all addresses.
-/

/-- The empty `PossiblyInfiniteTree` is none everywhere. -/
def empty : PossiblyInfiniteTree α where
  infinite_tree := fun _ => none
  no_orphans := by rintro _ ⟨_, eq⟩ _ _ ⟨_, eq2⟩; rw [← eq2, ← eq, InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop]; simp [InfiniteTreeSkeleton.get]
  no_holes_in_children := by rintro _ ⟨_, eq⟩ _ _; rw [← eq, InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop]; simp [InfiniteTreeSkeleton.get]

/-- Getting from the `empty` tree always returns none. -/
theorem get?_empty {α} : ∀ {n}, (@PossiblyInfiniteTree.empty α).get? n = none := by intro _; rfl

/-- Dropping from the `empty` tree again yields the empty tree. -/
theorem drop_empty {α} : ∀ {ns}, (@PossiblyInfiniteTree.empty α).drop ns = PossiblyInfiniteTree.empty := by
  intro _; apply ext; intro _; rw [get?_drop, get?_empty, get?_empty]

/-- The `root` of the `empty` tree is none. -/
theorem root_empty {α} : (@PossiblyInfiniteTree.empty α).root = none := by rfl

/-- A tree is `empty` if and only if the `root` is none. -/
theorem empty_iff_root_none {t : PossiblyInfiniteTree α} : t = PossiblyInfiniteTree.empty ↔ t.root = none := by
  constructor
  . intro h; rw [h]; exact root_empty
  intro h
  rw [root_eq] at h
  apply PossiblyInfiniteTree.ext
  intro ns
  rw [get?_empty]
  apply InfiniteTreeSkeleton.no_orphans_closure t.no_orphans _ InfiniteTreeSkeleton.IsSuffix_refl h
  apply InfiniteTreeSkeleton.get_mem

end Empty

section ChildTrees

/-!
## Child Trees

Defining the `childTrees` function requires a bit of machinery.
We only want to return the child trees that are not already empty.
Then all returned trees have a non-none root, which we aim to capture directly in the return type.
-/

/-- The `PossiblyInfiniteTreeWithRoot` is a `PossiblyInfiniteTree` where the `root` is not none. -/
abbrev PossiblyInfiniteTreeWithRoot (α : Type u) := {t : PossiblyInfiniteTree α // t.root ≠ none}

namespace PossiblyInfiniteTreeWithRoot

/-!
### PossiblyInfiniteTreeWithRoot

For the `PossiblyInfiniteTreeWithRoot` we mainly provide some functions to convert `PossiblyInfiniteTree` to and from `Option PossiblyInfiniteTreeWithRoot`. Clearly, if a `PossiblyInfiniteTree` has a non-none root, we can convert it directly into a `PossiblyInfiniteTreeWithRoot`, otherwise, we simply convert it to `none`. Also in the other direction, none can just be converted to `PossiblyInfiniteTree.empty` and any `PossiblyInfiniteTreeWithRoot` is already a `PossiblyInfiniteTree`.
-/

def opt_to_tree (opt : Option (PossiblyInfiniteTreeWithRoot α)) : PossiblyInfiniteTree α :=
  match opt with
  | .none => PossiblyInfiniteTree.empty
  | .some t => t.val

def tree_to_opt (t : PossiblyInfiniteTree α) : Option (PossiblyInfiniteTreeWithRoot α) :=
  match eq : t.root with
  | .none => none
  | .some r => some ⟨t, by simp [eq]⟩

theorem opt_to_tree_none_iff {opt : Option (PossiblyInfiniteTreeWithRoot α)} : opt = none ↔ (opt_to_tree opt).root = none := by
  unfold opt_to_tree
  cases opt with
  | none => simp [root_empty]
  | some t => simp [t.property]

theorem tree_to_opt_none_iff {t : PossiblyInfiniteTree α} : tree_to_opt t = none ↔ t.root = none := by
  unfold tree_to_opt
  split; simpa; simp [*]

theorem tree_to_opt_some_iff {t : PossiblyInfiniteTree α} : ∀ {t'}, tree_to_opt t = some t' ↔ t = t' ∧ t.root.isSome := by
  unfold tree_to_opt
  split
  case h_1 eq => simp [eq]
  case h_2 eq => simp [eq]

theorem tree_to_opt_after_opt_to_tree {opt : Option (PossiblyInfiniteTreeWithRoot α)} :
    tree_to_opt (opt_to_tree opt) = opt := by
  cases eq : opt with
  | none => rw [tree_to_opt_none_iff, ← opt_to_tree_none_iff]
  | some t =>
    simp only [opt_to_tree, tree_to_opt]
    split
    . have := t.property; contradiction
    . rfl

theorem opt_to_tree_after_tree_to_opt {t : PossiblyInfiniteTree α} :
    opt_to_tree (tree_to_opt t) = t := by
  unfold tree_to_opt
  split
  . simp only [opt_to_tree]; apply Eq.symm; rw [empty_iff_root_none]; assumption
  . simp only [opt_to_tree]

end PossiblyInfiniteTreeWithRoot

/-!
### The actual childTrees definition

With `PossiblyInfiniteTreeWithRoot` in place, we can now define the actual `childTrees` function.
-/

/-- The `childTrees` of a `PossiblyInfiniteTree` are the `PossiblyInfiniteList` of all child trees that are not empty, i.e. it only consists of `PossiblyInfiniteTreeWithRoot`. -/
def childTrees (t : PossiblyInfiniteTree α) : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α) where
  infinite_list := fun n => PossiblyInfiniteTreeWithRoot.tree_to_opt {
    infinite_tree := t.infinite_tree.childTrees.get n
    no_orphans := by intro _ suf; apply t.no_orphans; apply InfiniteTreeSkeleton.IsSuffix_trans suf; apply InfiniteTreeSkeleton.IsSuffix_of_mem_childTrees; apply InfiniteList.get_mem
    no_holes_in_children := by intro _ suf; apply t.no_holes_in_children; exact InfiniteTreeSkeleton.IsSuffix_trans suf (t.infinite_tree.IsSuffix_of_mem_childTrees _ InfiniteList.get_mem)
  }
  no_holes := by intro n'; simp only [InfiniteList.get]; rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff, PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff]; exact t.no_holes_in_children _ InfiniteTreeSkeleton.IsSuffix_refl n'

/-- `PossiblyInfiniteTree.childTrees` can be expressed through `InfiniteTreeSkeleton.childTrees`. -/
theorem mem_childTrees_iff {t : PossiblyInfiniteTree α} : ∀ c, c ∈ t.childTrees ↔ c.val.infinite_tree ∈ t.infinite_tree.childTrees := by
  intro c; unfold childTrees
  simp only [PossiblyInfiniteList.mem_iff, PossiblyInfiniteList.get?, InfiniteList.get, PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff]
  constructor
  . rintro ⟨n, mem⟩
    exists n
    rw [← mem.left]
    rfl
  . rintro ⟨n, mem⟩
    simp only [InfiniteList.get] at mem
    exists n
    constructor
    . rw [PossiblyInfiniteTree.mk.injEq]; exact mem
    . simp only [root]
      rw [mem, Option.isSome_iff_ne_none]
      exact c.property

/-- Getting a child tree is the same as dropping the corresponding singleton address. -/
theorem get?_childTrees {t : PossiblyInfiniteTree α} : ∀ n, (t.childTrees.get? n) = PossiblyInfiniteTreeWithRoot.tree_to_opt (t.drop [n]) := by intros; rfl

/-- Getting at an address in a child tree can be combined into a single get call. -/
theorem get?_get?_childTrees {t : PossiblyInfiniteTree α} : ∀ n ns, (PossiblyInfiniteTreeWithRoot.opt_to_tree (t.childTrees.get? n)).get? ns = t.get? (n::ns) := by intros; rw [get?_childTrees, PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]; rfl

/-- The `childTrees` of the `empty` tree are exactly `PossiblyInfiniteList.empty`. -/
theorem childTrees_empty {α} : (@PossiblyInfiniteTree.empty α).childTrees = PossiblyInfiniteList.empty := by rfl

end ChildTrees

section Node

/-!
## Node Constructor

Similar to the `InfiniteTreeSkeleton`, we can also define a `node` constructor on the `PossiblyInfiniteTree`.
-/

/-- Construct a `PossiblyInfiniteTree` from a `PossiblyInfiniteList` of `PossiblyInfiniteTreeWithRoot` and a new root element. -/
def node (root : α) (childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)) : PossiblyInfiniteTree α where
  infinite_tree := InfiniteTreeSkeleton.node (.some root) (childTrees.infinite_list.map (PossiblyInfiniteTree.infinite_tree ∘ PossiblyInfiniteTreeWithRoot.opt_to_tree))
  no_orphans := by
    intro _ ⟨ns, eq⟩
    cases ns with
    | nil => rintro contra _ ⟨_, eq2⟩; rw [← eq, InfiniteTreeSkeleton.drop_nil, InfiniteTreeSkeleton.root_node] at contra; simp at contra
    | cons n ns =>
      rw [InfiniteTreeSkeleton.drop_node_cons] at eq
      rw [← eq]
      apply (PossiblyInfiniteTreeWithRoot.opt_to_tree (childTrees.infinite_list.get n)).no_orphans
      exists ns
  no_holes_in_children := by
    rintro _ ⟨ns, eq⟩
    cases ns with
    | nil => rw [← eq, InfiniteTreeSkeleton.drop_nil]; unfold InfiniteTreeSkeleton.childNodes; rw [InfiniteTreeSkeleton.childTrees_node]; intro n; simp only [InfiniteList.get_map, Function.comp_apply]; rw [← PossiblyInfiniteTree.root.eq_def, ← PossiblyInfiniteTree.root.eq_def, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]; exact childTrees.no_holes n
    | cons n ns =>
      rw [← eq, InfiniteTreeSkeleton.drop_node_cons, InfiniteList.get_map]
      exact (PossiblyInfiniteTreeWithRoot.opt_to_tree (childTrees.infinite_list.get n)).no_holes_in_children _ (by exists ns)

/-- Getting the element at address [] on `node` is the new root. -/
theorem get?_node_nil {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} : (node root childTrees).get? [] = .some root := by rfl

/-- Getting any address != [] on `node` yields the respective element from the previous `PossiblyInfiniteTreeWithRoot`. -/
theorem get?_node_cons {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} : ∀ n ns, (node root childTrees).get? (n :: ns) = (PossiblyInfiniteTreeWithRoot.opt_to_tree (childTrees.get? n)).get? ns := by intro n ns; rfl

/-- Dropping from `node` with an address of the form `n::ns` is the same as getting the `n` child from the child trees used in the construction and then dropping `ns` there.  -/
theorem drop_node_cons {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} {n : Nat} {ns : List Nat} : (node root childTrees).drop (n::ns) = (PossiblyInfiniteTreeWithRoot.opt_to_tree (childTrees.get? n)).drop ns := by rfl

/-- The `root` of `node` is the root used in the construction. -/
theorem root_node {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} : (node root childTrees).root = root := by rfl

/-- The `childTrees` of `node` are the childTrees used in the construction. -/
theorem childTrees_node {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} : (node root childTrees).childTrees = childTrees := by
  unfold node PossiblyInfiniteTree.childTrees
  simp only [InfiniteTreeSkeleton.childTrees_node, InfiniteList.get_map, Function.comp_apply]
  apply PossiblyInfiniteList.ext
  intro n
  simp only [PossiblyInfiniteList.get?, InfiniteList.get]
  rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_after_opt_to_tree]

/-- Any `PossiblyInfiniteTree` where the `root` is not none can be written using the `node` constructor. -/
theorem node_root_childTrees {t : PossiblyInfiniteTree α} {root : α} (h : t.root = .some root) : t = node root t.childTrees := by
  rw [PossiblyInfiniteTree.mk.injEq]; simp only [node]; rw [← h]; rw [InfiniteTreeSkeleton.node_root_childTrees t.infinite_tree]
  apply congrArg
  unfold PossiblyInfiniteTree.childTrees
  apply InfiniteList.ext
  intro n
  simp only [InfiniteList.get_map, Function.comp_apply]
  simp only [InfiniteList.get]
  rw [PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]

end Node

section ChildNodes

/-!
# ChildNodes

It can be convenient to obtain a list of the immediate child nodes of a given tree.
This is equivalent to mapping each child tree to its root.
-/

/-- The `childNodes` are `InfiniteTreeSkeleton.childNodes`. -/
def childNodes (t : PossiblyInfiniteTree α) : PossiblyInfiniteList α where
  infinite_list := t.infinite_tree.childNodes
  no_holes := t.no_holes_in_children _ InfiniteTreeSkeleton.IsSuffix_refl

/-- Getting the nth `childNodes` is the root of the nth `childTrees`. -/
theorem get?_childNodes {t : PossiblyInfiniteTree α} : ∀ {n}, t.childNodes.get? n = (PossiblyInfiniteTreeWithRoot.opt_to_tree (t.childTrees.get? n)).root := by
  intro n; rw [get?_childTrees, PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]; rfl

/-- The `childNodes` are the `root`s of the `childTrees`. -/
theorem childNodes_eq {t : PossiblyInfiniteTree α} : t.childNodes = t.childTrees.map (fun t => t.val.root.get (by rw [Option.isSome_iff_ne_none]; exact t.property)) := by
  apply PossiblyInfiniteList.ext
  intro n
  rw [PossiblyInfiniteList.get?_map]
  rw [get?_childNodes, get?_childTrees, PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]
  apply Eq.symm
  cases eq : (t.drop [n]).root with
  | none => rw [Option.map_eq_none_iff, PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff]; exact eq
  | some r => rw [Option.map_eq_some_iff]; exists ⟨t.drop [n], by simp [eq]⟩; rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff]; simp [eq]

/-- Each child node is a tree member. -/
theorem mem_of_mem_childNodes {t : PossiblyInfiniteTree α} : ∀ c ∈ t.childNodes, c ∈ t := by
  intro c; exact t.infinite_tree.mem_of_mem_childNodes (some c)

/-- The `childNodes` of the `empty` tree are `PossiblyInfiniteList.empty`. -/
theorem childNodes_empty {α} : (@PossiblyInfiniteTree.empty α).childNodes = PossiblyInfiniteList.empty := by
  apply PossiblyInfiniteList.ext; intro _; rw [get?_childNodes, childTrees_empty, PossiblyInfiniteList.get?_empty, PossiblyInfiniteList.get?_empty, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]

end ChildNodes

section Suffixes

/-!
## Suffixes

Here, we define a suffix relation on `PossiblyInfiniteTree` inspired by `List.IsSuffix`.
For `t1` and `t2`, `t1 <:+ t2` denotes that `t1` is a subtree of `t2`.

The suffix relation is reflexive and transitive but not necesarrily antisymmetric!
Note also that `InfiniteList.suffix_or_suffix_of_suffix` has no equivalent statement here, i.e.
just because two trees are subtrees of the same parent tree, we cannot say anything about their relation to one another.
They might be totally "disconnected".
-/

/-- A suffix relation on infinite trees. This is inspired by `List.IsSuffix`. Read `t1 <:+ t2` as: t1 is a subtree of t2. -/
def IsSuffix (t1 t2 : PossiblyInfiniteTree α) : Prop := t1.infinite_tree <:+ t2.infinite_tree
infixl:50 " <:+ " => IsSuffix

/-- t1 is a subtree of t2 if t1 can be obtained from t2 by dropping. -/
theorem IsSuffix_iff {t1 t2 : PossiblyInfiniteTree α} : t1 <:+ t2 ↔ ∃ ns, t2.drop ns = t1 := by
  constructor
  . rintro ⟨ns, h⟩; exists ns; simp [drop, h]
  . rintro ⟨ns, h⟩; exists ns; simp only [drop] at h; rw [← h]

/-- The suffix relation is reflexive. -/
theorem IsSuffix_refl {t : PossiblyInfiniteTree α} : t <:+ t := t.infinite_tree.IsSuffix_refl

/-- The suffix relation is transitive. -/
theorem IsSuffix_trans {t1 t2 t3 : PossiblyInfiniteTree α} : t1 <:+ t2 -> t2 <:+ t3 -> t1 <:+ t3 := InfiniteTreeSkeleton.IsSuffix_trans

/-- A member of a subtree is also a member of the current tree. -/
theorem mem_of_mem_suffix {t1 t2 : PossiblyInfiniteTree α} (suffix : t1 <:+ t2) : ∀ e ∈ t1, e ∈ t2 := by
  intro e mem; apply InfiniteTreeSkeleton.mem_of_mem_suffix suffix; exact mem

/-- Dropping elements yields a subtree. -/
theorem IsSuffix_drop {t : PossiblyInfiniteTree α} : ∀ ns, t.drop ns <:+ t := t.infinite_tree.IsSuffix_drop

/-- Each child tree is a subtree. -/
theorem IsSuffix_of_mem_childTrees {t : PossiblyInfiniteTree α} : ∀ c ∈ t.childTrees, c <:+ t := by
  intro c c_mem; apply t.infinite_tree.IsSuffix_of_mem_childTrees; rw [mem_childTrees_iff] at c_mem; exact c_mem

/-- Every suffix of the empty tree is empty. -/
theorem empty_suffix_of_empty {t : PossiblyInfiniteTree α} : t <:+ empty -> t = empty := by
  intro suf; rw [IsSuffix_iff] at suf; rcases suf with ⟨_, suf⟩; rw [← suf]; exact drop_empty

/-- We can express the `InfiniteTreeSkeleton.no_orphans` condition directly on `PossiblyInfiniteTree`. -/
theorem no_orphans' {t : PossiblyInfiniteTree α} :
    ∀ subtree, subtree <:+ t -> subtree.root = none -> subtree.childNodes = PossiblyInfiniteList.empty := by
  intro subtree suf root_none
  rw [PossiblyInfiniteList.empty_iff_head_none]
  apply t.no_orphans _ suf root_none
  exact subtree.infinite_tree.childNodes.head_mem

end Suffixes

section ElementRecursor

/-!
## Recursor for Members

We define a recursion (induction) principle for members (`Element`s) of an `PossiblyInfiniteTree` called `mem_rec`.
This can be used with the `induction` tactic to prove a property for each `Element` of an `PossiblyInfiniteTree`.
Note that for using this coveniently, the goal needs to expressed (rewritten) using an `Element`.
-/

/-- A tree `Element` is a Subtype featuring a proof of being a tree member. -/
def Element (t : PossiblyInfiniteTree α) := { e : α // e ∈ t }

/-- A recursor for proving properties about tree members (`Element`s) via induction. -/
theorem mem_rec
    {t : PossiblyInfiniteTree α}
    {motive : Element t -> Prop}
    (root : ∀ r, (mem : r ∈ t.root) -> motive ⟨r, root_mem _ mem⟩)
    (step : ∀ t2, (suffix : t2 <:+ t) -> (∃ (r : α) (mem : r ∈ t2.root), motive ⟨r, t2.mem_of_mem_suffix suffix _ (t2.root_mem _ mem)⟩) -> ∀ {c}, (mem : c ∈ t2.childNodes) -> motive ⟨c, mem_of_mem_suffix suffix _ (mem_of_mem_childNodes _ mem)⟩)
    (a : Element t) :
    motive a := by
  let motive' (o : t.infinite_tree.Element) : Prop := ∀ v, (mem : v ∈ o.val) -> motive ⟨v, by have := o.property; rw [Option.mem_def] at mem; rw [mem] at this; exact this⟩
  let a' : t.infinite_tree.Element := ⟨some a.val, a.property⟩
  have : motive' a' := by
    induction a' using InfiniteTreeSkeleton.mem_rec with
    | root => exact root
    | step t2 suffix ih c_mem =>
      cases eq : t2.root with
      | none => intro _ mem; simp [t.no_orphans t2 suffix eq _ c_mem] at mem
      | some r =>
        rcases suffix with ⟨ns, suffix⟩
        rcases c_mem with ⟨m, c_mem⟩
        rw [← suffix] at eq
        rw [← suffix] at c_mem
        specialize step (t.drop ns) (t.IsSuffix_drop ns)
        intro v v_mem
        apply step
        . exists r, eq; apply ih; simp [← suffix, eq]
        . exists m; rw [← v_mem]; exact c_mem
  apply this
  rfl

end ElementRecursor

section Branches

/-!
# Branches

Branches are essentially `PossiblyInfiniteList`s in a `PossiblyInfiniteTree`
and can be characterizes by an infinite "address", i.e. `InfiniteList Nat`.
-/

/-- This function defines the `PossiblyInfiniteList` of tree elements that corresponds to a given infinite address. -/
def branchForAddress (t : PossiblyInfiniteTree α) (ns : InfiniteList Nat) : PossiblyInfiniteList α where
  infinite_list := t.infinite_tree.branchForAddress ns
  no_holes := by
    intro n
    rw [InfiniteTreeSkeleton.get_branchForAddress]
    intro eq_none
    rw [InfiniteTreeSkeleton.get_branchForAddress]
    rw [InfiniteList.take_succ']
    apply t.no_orphans (t.infinite_tree.drop (ns.take n)) (t.infinite_tree.IsSuffix_drop (ns.take n))
    . rw [InfiniteTreeSkeleton.root_drop]; exact eq_none
    . exists (ns.get n)

/-- An infinite address is maximal in a `PossiblyInfiniteTree` if whenever the the tree element is `none` at the nth step of the address, then all of its siblings are also none (and it is enough to demand that the first sibling is none). -/
def branchAddressIsMaximal (t : PossiblyInfiniteTree α) (ns : InfiniteList Nat) : Prop :=
  ∀ n, (t.branchForAddress ns).get? n.succ = none -> (t.drop (ns.take n)).childNodes.head = none

/-- The `branches` in the `PossiblyInfiniteTree` are exactly the `PossiblyInfiniteList`s for which an infinite address exists that is also maximal. -/
def branches (t : PossiblyInfiniteTree α) : Set (PossiblyInfiniteList α) :=
  fun b => ∃ ns, b = t.branchForAddress ns ∧ t.branchAddressIsMaximal ns

/-- Getting from the branch corresponding to an infinite address corresponds to getting from the tree at the corresponding finite part of the address. -/
theorem get?_branchForAddress {t : PossiblyInfiniteTree α} {ns : InfiniteList Nat} {n : Nat} : (t.branchForAddress ns).get? n = t.get? (ns.take n) := by rfl

/-- The set of `branches` can equivalently be expressed as the set of all `PossiblyInfiniteList`s where the head equals the root of the tree and the tail occurs in the branches of some childTree. If there are no childTrees, then the tail needs to be empty. -/
theorem branches_eq {t : PossiblyInfiniteTree α} : t.branches = fun b =>
    b.head = t.root ∧ ((t.childTrees = PossiblyInfiniteList.empty ∧ b.tail = PossiblyInfiniteList.empty) ∨ (∃ c ∈ t.childTrees, b.tail ∈ c.val.branches)) := by
  unfold branches
  apply Set.ext
  intro b
  constructor
  . rintro ⟨ns, b_eq, ns_max⟩
    constructor
    . rw [b_eq]; rfl
    . cases eq : t.childTrees.get? (ns.get 0) with
      | none =>
        apply Or.inl
        rw [get?_childTrees] at eq
        rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff] at eq
        rw [root_drop] at eq
        rw [PossiblyInfiniteList.empty_iff_head_none]
        rw [PossiblyInfiniteList.empty_iff_head_none]
        constructor
        . specialize ns_max 0
          rw [get?_branchForAddress] at ns_max
          rw [InfiniteList.take_succ, InfiniteList.take_zero, InfiniteList.take_zero, drop_nil] at ns_max
          unfold InfiniteList.head at ns_max
          specialize ns_max eq
          rw [PossiblyInfiniteList.head_eq] at ns_max
          rw [PossiblyInfiniteList.head_eq]
          rw [get?_childNodes, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff] at ns_max
          exact ns_max
        . rw [b_eq]
          rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_tail]
          rw [get?_branchForAddress]
          rw [InfiniteList.take_succ, InfiniteList.take_zero]
          unfold InfiniteList.head
          exact eq
      | some c =>
        apply Or.inr
        exists c
        constructor
        . exists ns.get 0
        exists ns.tail
        rw [get?_childTrees] at eq
        rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff] at eq
        constructor
        . rw [b_eq]
          apply PossiblyInfiniteList.ext
          intro n
          rw [PossiblyInfiniteList.get?_tail]
          rw [get?_branchForAddress]
          rw [get?_branchForAddress]
          rw [InfiniteList.take_succ]
          rw [← List.singleton_append]
          rw [← get?_drop]
          unfold InfiniteList.head
          rw [eq.left]
        . intro n
          specialize ns_max (n+1)
          rw [get?_branchForAddress] at ns_max
          rw [InfiniteList.take_succ] at ns_max
          rw [← List.singleton_append] at ns_max
          rw [← get?_drop] at ns_max
          unfold InfiniteList.head at ns_max
          rw [eq.left] at ns_max
          rw [get?_branchForAddress]
          intro h
          specialize ns_max h
          rw [InfiniteList.take_succ] at ns_max
          rw [← List.singleton_append] at ns_max
          rw [← drop_drop] at ns_max
          unfold InfiniteList.head at ns_max
          rw [eq.left] at ns_max
          exact ns_max
  . rintro ⟨head_eq, tail_eq⟩
    cases tail_eq with
    | inl tail_eq =>
      exists fun _ => 0
      constructor
      . apply PossiblyInfiniteList.ext
        intro n
        cases n with
        | zero =>
          rw [get?_branchForAddress, InfiniteList.take_zero]
          exact head_eq
        | succ n =>
          rw [← PossiblyInfiniteList.get?_tail]
          rw [tail_eq.right, PossiblyInfiniteList.get?_empty]
          rw [get?_branchForAddress, InfiniteList.take_succ, ← List.singleton_append, ← get?_drop]
          simp only [InfiniteList.head, InfiniteList.get]
          have : t.childTrees.get? 0 = none := by rw [tail_eq.left, PossiblyInfiniteList.get?_empty]
          rw [get?_childTrees, PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff] at this
          rw [← empty_iff_root_none] at this
          rw [this, get?_empty]
      . intro n
        rw [get?_branchForAddress, InfiniteList.take_succ', ← List.singleton_append, ← get?_drop]
        simp only [InfiniteList.get, List.append_nil]
        rw [PossiblyInfiniteList.head_eq]
        rw [get?_childNodes]
        rw [← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]
        rw [get?_childTrees]
        rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff]
        rw [root_drop]
        intro h; exact h
    | inr tail_eq =>
      rcases tail_eq with ⟨c, c_mem, ns, tail_eq, ns_max⟩
      rw [PossiblyInfiniteList.mem_iff] at c_mem
      rcases c_mem with ⟨i, c_mem⟩
      exists InfiniteList.cons i ns
      rw [get?_childTrees] at c_mem
      rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff] at c_mem
      constructor
      . apply PossiblyInfiniteList.ext
        intro n
        rw [get?_branchForAddress]
        cases n with
        | zero => rw [InfiniteList.take_zero]; exact head_eq
        | succ n =>
          rw [← PossiblyInfiniteList.get?_tail, tail_eq]
          rw [InfiniteList.take_succ, InfiniteList.head_cons, InfiniteList.tail_cons]
          rw [← List.singleton_append]
          rw [← get?_drop]
          rw [c_mem.left]
          rw [get?_branchForAddress]
      . intro n
        rw [get?_branchForAddress]
        cases n with
        | zero =>
          intro contra
          rw [InfiniteList.take_succ, InfiniteList.take_zero, InfiniteList.head_cons] at contra
          rw [root_drop] at c_mem
          rw [contra] at c_mem
          simp at c_mem
        | succ n =>
          specialize ns_max n
          rw [InfiniteList.take_succ, InfiniteList.head_cons, InfiniteList.tail_cons]
          rw [← List.singleton_append]
          rw [← get?_drop]
          rw [c_mem.left]
          rw [get?_branchForAddress] at ns_max
          intro h; specialize ns_max h
          rw [InfiniteList.take_succ, InfiniteList.head_cons, InfiniteList.tail_cons]
          rw [← List.singleton_append]
          rw [← drop_drop]
          rw [c_mem.left]
          exact ns_max

end Branches

section Generate

/-!
# Branch Generation

We can use `PossiblyInfiniteList.generate` to construct `branches` in a `PossiblyInfiniteTree`.
First of all, this requires that the mapper function produces a `PossiblyInfiniteTreeWithRoot`.
By that `PossiblyInfiniteList.generate` gives us an `PossiblyInfiniteList` of `PossiblyInfiniteTreeWithRoot`.
Intuitively, using all the roots of these trees gives us a branch.
But this is only true if the generate trees are always child trees of each other and the generation indeed creates a maximal branch according to `branchAddressIsMaximal`.
This condition is used in the `generate_branch_mem_branches` theorem to proof that a `PossiblyInfiniteList`
from the `generate_branch` function is indeed in `branches`.
-/

/-- Given a generator and a mapper that maps generated elements to `PossiblyInfiniteTreeWithRoot`, construct an `PossiblyInfiniteList` with the goal of constructing a branch in a tree. -/
def generate_branch (start : Option β) (generator : β -> Option β) (mapper : β -> PossiblyInfiniteTreeWithRoot α) : PossiblyInfiniteList α :=
  (PossiblyInfiniteList.generate start generator mapper).map (fun t => t.val.root.get (by rw [Option.isSome_iff_ne_none]; exact t.property))

/-- If the generated trees are `childTrees` of each other and the generated branch is maximal according to `branchAddressIsMaximal`, then the generated `PossiblyInfiniteList` is indeed a branch. -/
theorem generate_branch_mem_branches {start : Option β} {generator : β -> Option β} {mapper : β -> PossiblyInfiniteTreeWithRoot α}
    (next_is_child : ∀ b, ∀ b' ∈ generator b, mapper b' ∈ (mapper b).val.childTrees)
    (maximal : ∀ b, generator b = none -> (mapper b).val.childTrees = PossiblyInfiniteList.empty)
    (isSome_start : start.isSome) :
    generate_branch start generator mapper ∈ (mapper (start.get isSome_start)).val.branches := by
  let addresses : InfiniteList Nat := InfiniteList.generate start (fun o => o.bind generator)
    (fun o => (o.bind (fun b => (generator b).attach.map (fun b' => Classical.choose (next_is_child b b'.val b'.property)))).getD 0)
  let trees := PossiblyInfiniteList.generate start generator mapper
  have : ∀ n, PossiblyInfiniteTreeWithRoot.opt_to_tree (trees.get? n) = (trees.head.get (by simp only [trees, PossiblyInfiniteList.head_generate, Option.isSome_map]; exact isSome_start)).val.drop (addresses.take n) := by
    intro n
    induction n with
    | zero =>
      simp only [InfiniteList.take_zero, drop_nil, PossiblyInfiniteList.head_eq, PossiblyInfiniteTreeWithRoot.opt_to_tree]
      split
      case h_1 _ eq => simp only [trees, ← PossiblyInfiniteList.head_eq, PossiblyInfiniteList.head_generate, Option.map_eq_none_iff] at eq; rw [eq] at isSome_start; simp at isSome_start
      case h_2 _ _ eq => simp [eq]
    | succ n ih =>
      rw [InfiniteList.take_succ', ← drop_drop, ← ih]
      cases eq : trees.get? n with
      | none =>
        conv => right; simp only [PossiblyInfiniteTreeWithRoot.opt_to_tree]
        rw [drop_empty, empty_iff_root_none, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]
        apply trees.no_holes'; exact eq
      | some t =>
        cases eq2 : trees.get? (n + 1) with
        | none =>
          simp only [PossiblyInfiniteTreeWithRoot.opt_to_tree]
          simp only [trees, PossiblyInfiniteList.get?_generate, Option.map_eq_some_iff] at eq
          simp only [trees, PossiblyInfiniteList.get?_succ_generate, Option.map_eq_none_iff, Option.bind_eq_none_iff] at eq2
          rcases eq with ⟨b, b_mem, eq⟩
          specialize maximal b (eq2 b b_mem)
          rw [eq] at maximal
          have : PossiblyInfiniteTreeWithRoot.opt_to_tree (t.val.childTrees.get? (addresses.get n)) = empty := by
            rw [maximal, PossiblyInfiniteList.get?_empty]; rfl
          rw [get?_childTrees, PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt] at this
          rw [this]
        | some t2 =>
          simp only [trees, PossiblyInfiniteList.get?_generate, Option.map_eq_some_iff] at eq
          simp only [trees, PossiblyInfiniteList.get?_succ_generate] at eq2
          rcases eq with ⟨b, b_mem, eq⟩
          rw [b_mem, Option.bind_some, Option.map_eq_some_iff] at eq2
          rcases eq2 with ⟨b', b'_mem, t2_eq⟩
          have eq_child := Classical.choose_spec (next_is_child b b' b'_mem)
          rw [← t2_eq, ← eq_child]
          conv => left; right; left; rw [eq]
          rw [← PossiblyInfiniteList.get?.eq_def, get?_childTrees, PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]
          simp only [PossiblyInfiniteTreeWithRoot.opt_to_tree]
          have : addresses.get n = Classical.choose (next_is_child b b' b'_mem) := by
            simp only [addresses, InfiniteList.get_generate]
            rw [b_mem, Option.bind_some]
            have : (generator b).attach = some ⟨b', b'_mem⟩ := by simp [b'_mem]
            conv => left; left; right; rw [this]
            rw [Option.map_some, Option.getD_some]
          rw [this]
  exists addresses; constructor
  . apply PossiblyInfiniteList.ext
    intro n
    simp only [generate_branch]
    rw [PossiblyInfiniteList.get?_map, get?_branchForAddress]
    simp only [trees, PossiblyInfiniteList.head_generate, Option.get_map] at this
    rw [← root_drop, ← this]
    cases (PossiblyInfiniteList.generate start generator mapper).get? n <;> simp [PossiblyInfiniteTreeWithRoot.opt_to_tree, root_empty]
  . intro n
    rw [get?_branchForAddress]
    simp only [trees, PossiblyInfiniteList.head_generate, Option.get_map] at this
    rw [← root_drop, ← this, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]
    rw [← this]
    rw [PossiblyInfiniteList.get?_succ_generate, PossiblyInfiniteList.get?_generate, Option.map_eq_none_iff]
    rw [PossiblyInfiniteList.head_eq, get?_childNodes, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff, ← PossiblyInfiniteList.head_eq, ← PossiblyInfiniteList.empty_iff_head_none]
    rw [Option.bind_eq_none_iff]
    intro eq_none
    cases b_eq : (InfiniteList.iterate start fun x => x.bind generator).get n with
    | none => simp [PossiblyInfiniteTreeWithRoot.opt_to_tree, childTrees_empty]
    | some b => simp only [Option.map_some, PossiblyInfiniteTreeWithRoot.opt_to_tree]; apply maximal; apply eq_none; exact b_eq

/-- The `PossiblyInfiniteList.head` of `generate_branch` is the `root` of the first tree. -/
theorem head_generate_branch {start : Option β} {generator : β -> Option β} {mapper : β -> PossiblyInfiniteTreeWithRoot α} : (generate_branch start generator mapper).head = start.map (fun s => (mapper s).val.root.get (by rw [Option.isSome_iff_ne_none]; exact (mapper s).property)) := by simp only [generate_branch]; rw [PossiblyInfiniteList.head_eq, PossiblyInfiniteList.get?_map, ← PossiblyInfiniteList.head_eq, PossiblyInfiniteList.head_generate, Option.map_map]; rfl

/-- Getting the nth element from a `generate_branch` result is the root of the nth generated tree. -/
theorem get?_generate_branch {start : Option β} {generator : β -> Option β} {mapper : β -> PossiblyInfiniteTreeWithRoot α} :
  ∀ n, (generate_branch start generator mapper).get? n = ((PossiblyInfiniteList.generate start generator mapper).get? n).map (fun t => t.val.root.get (by rw [Option.isSome_iff_ne_none]; exact t.property)) := by intros; rfl

/-- The `PossiblyInfiniteList.tail` of `generate_branch` is the branch generated when applying the generator function once on the starting element before the actual generation. -/
theorem tail_generate_branch {start : Option β} {generator : β -> Option β} {mapper : β -> PossiblyInfiniteTreeWithRoot α} : (generate_branch start generator mapper).tail = generate_branch (start.bind generator) generator mapper := by unfold generate_branch; rw [PossiblyInfiniteList.tail_map, PossiblyInfiniteList.tail_generate]

end Generate

section Leaves

/-!
## Leaves

The `leaves` of a `PossiblyInfiniteTree` is the set of elements that occur in a node that has no `childNodes`.
-/

def leaves (t : PossiblyInfiniteTree α) : Set α := fun a => ∃ node : List Nat, t.get? node = some a ∧ (t.drop node).childNodes.head = none

end Leaves

section FromBranch

/-!
## Constructing a Tree from a Branch

A `PossiblyInfiniteList` directly corresponds to the `PossiblyInfiniteTree`
where the list is the "first" branch (with the address that only consists of zeros) and all other nodes are none.
-/

def from_branch (b : PossiblyInfiniteList α) : PossiblyInfiniteTree α where
  infinite_tree := fun ns => if ns.all (fun e => e = 0) then b.infinite_list ns.length else none
  no_orphans := by
    intro _ ⟨ns, eq⟩ root_none _ ⟨n, mem⟩
    rw [← mem, ← eq, InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop]
    rw [← eq, InfiniteTreeSkeleton.root_drop] at root_none
    simp only [InfiniteTreeSkeleton.get]
    simp only [InfiniteTreeSkeleton.get] at root_none
    cases eq : (ns ++ [n]).all (fun e => e = 0) with
    | false => rfl
    | true =>
      have : ns.all (fun e => e = 0) := by rw [List.all_append, Bool.and_eq_true] at eq; exact eq.left
      simp only [this] at root_none
      simp only [List.length_append, List.length_singleton]
      apply b.no_holes
      exact root_none
  no_holes_in_children := by
    rintro _ ⟨ns, eq⟩ n _
    rw [← eq, InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop]
    simp only [InfiniteTreeSkeleton.get]
    have : (ns ++ [n.succ]).all (fun e => e = 0) = false := by
      rw [List.all_eq_false]
      exists n.succ
      simp
    simp [this]

end FromBranch

end PossiblyInfiniteTree

