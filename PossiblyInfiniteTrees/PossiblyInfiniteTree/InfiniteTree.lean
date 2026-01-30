import BasicLeanDatastructures.Set.Basic

import PossiblyInfiniteTrees.PossiblyInfiniteList.PossiblyInfiniteList

/-!
# InfiniteTreeSkeleton

This file defines an `InfiniteTreeSkeleton` as a function from the a list of naturals into the desired type.
Note that this is very similar to an `InfiniteList` only replacing `Nat` for `List Nat`.
In this way, the `InfiniteTreeSkeleton` is infinite in both dimensions, i.e.
it has infinite depth and each node has infinitely many (direct) children.

Similar to `InfiniteList`, we offer many convenience functions, some of which have different names.
For example, the equivalent to `InfiniteList.head` would be `root`
and the equivalent to `InfiniteList.tail` would be `childTrees`.
The functions `get` and `drop` behave analogously to their `InfiniteList` counterparts.

As for the `InfiniteList`, we also implement a `mem_rec` recursor that allows showing properties of tree members via induction.
We also allow generating branches of a tree using the `generate_branch` function, which yields an `InfiniteList`.
The convenience of this function lies in the theorem `generate_branch_mem_branches` that immediately allows us to verify
that the generated `InfiniteList` is indeed a branch in the `InfiniteTreeSkeleton`.
-/

/-- An `InfiniteTreeSkeleton` is a function from a list of naturals (representing an address in the tree) into the desired type. -/
def InfiniteTreeSkeleton (α : Type u) := (List Nat) -> α

namespace InfiniteTreeSkeleton

section Basic

/-!
## Basics

The essential functions on infinite trees, mainly get, drop, root, and childTrees.
-/

/-- Obtains the element of the tree at the given address. -/
def get (t : InfiniteTreeSkeleton α) (ns : List Nat) : α := t ns

/-- Obtains the subtree at the given address (by dropping everything else). -/
def drop (t : InfiniteTreeSkeleton α) (ns : List Nat) : InfiniteTreeSkeleton α := fun ns' => t.get (ns ++ ns')

/-- Get the element at the root of the tree (i.e. at the empty address). -/
def root (t : InfiniteTreeSkeleton α) : α := t.get []

/-- Get the `InfiniteList` of immediate child trees of the current tree. -/
def childTrees (t : InfiniteTreeSkeleton α) : InfiniteList (InfiniteTreeSkeleton α) := fun n ns => t.get (n::ns)

/-- Construct an `InfiniteTreeSkeleton` from an `InfiniteList` of `InfiniteTreeSkeleton`s and a new root element. -/
def node (root : α) (childTrees : InfiniteList (InfiniteTreeSkeleton α)) : InfiniteTreeSkeleton α
| .nil => root
| .cons hd tl => childTrees hd tl

instance : Membership α (InfiniteTreeSkeleton α) where
  mem t a := ∃ ns, t.get ns = a

/-- Two `InfiniteTreeSkeleton`s are the same if they agree on all addresses. -/
theorem ext {t1 t2 : InfiniteTreeSkeleton α} : (∀ ns, t1.get ns = t2.get ns) -> t1 = t2 := by
  apply funext

theorem ext_iff {t1 t2 : InfiniteTreeSkeleton α} : t1 = t2 ↔ (∀ ns, t1.get ns = t2.get ns) := by
  constructor
  . intro h _; rw [h]
  . exact ext

/-- Each element we can get is in the tree. -/
theorem get_mem {t : InfiniteTreeSkeleton α} {ns : List Nat} : t.get ns ∈ t := by exists ns

/-- Get after drop can be rewritten into get. -/
theorem get_drop {t : InfiniteTreeSkeleton α} {ns ns' : List Nat} : (t.drop ns).get ns' = t.get (ns ++ ns') := by rfl

/-- Helper theorem stating the definition of drop. -/
theorem drop_eq {t : InfiniteTreeSkeleton α} {ns : List Nat} : t.drop ns = fun ns' => t.get (ns ++ ns') := rfl

/-- Dropping the empty list changes nothing. -/
theorem drop_nil {t : InfiniteTreeSkeleton α} : t.drop [] = t := by rfl

/-- Two calls to drop can be combined. -/
theorem drop_drop {t : InfiniteTreeSkeleton α} {ns ns' : List Nat} : (t.drop ns).drop ns' = t.drop (ns ++ ns') := by
  rw [drop_eq]; simp only [get_drop]; rw [drop_eq]; simp

/-- The root is in the tree. -/
theorem root_mem {t : InfiniteTreeSkeleton α} : t.root ∈ t := by exists []

/-- The root of the dropped tree at address ns is exactly the element at address ns. -/
theorem root_drop {t : InfiniteTreeSkeleton α} {ns : List Nat} : (t.drop ns).root = t.get ns := by
  unfold root; rw [get_drop]; simp

/-- Getting a child tree is the same as dropping the corresponding singleton address. -/
theorem get_childTrees {t : InfiniteTreeSkeleton α} : ∀ n, (t.childTrees.get n) = t.drop [n] := by intros; rfl

/-- Getting at an address in a child tree can be combined into a single get call. -/
theorem get_get_childTrees {t : InfiniteTreeSkeleton α} : ∀ n ns, (t.childTrees.get n).get ns = t.get (n::ns) := by intros; rfl

/-- Getting the element at address [] on `node` is the new root. -/
theorem get_node_nil {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : (node root childTrees).get [] = root := by rfl

/-- Getting any address != [] on `node` yields the respective element from the previous `InfiniteTreeSkeleton`. -/
theorem get_node_cons {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : ∀ n ns, (node root childTrees).get (n :: ns) = (childTrees.get n).get ns := by intro n ns; rfl

/-- Dropping from `node` with an address of the form `n::ns` is the same as getting the `n` child from the child trees used in the construction and then dropping `ns` there,  -/
theorem drop_node_cons {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} {n : Nat} {ns : List Nat} :
  (node root childTrees).drop (n::ns) = (childTrees.get n).drop ns := by rfl

/-- The `root` of `node` is the root used in the construction. -/
theorem root_node {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : (node root childTrees).root = root := by rfl

/-- The `childTrees` of `node` are the childTrees used in the construction. -/
theorem childTrees_node {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : (node root childTrees).childTrees = childTrees := by rfl

/-- Any `InfiniteTreeSkeleton` can be written using the `node` constructor. -/
theorem node_root_childTrees (t : InfiniteTreeSkeleton α) : t = node t.root t.childTrees := by apply ext; intro ns; cases ns; rw [get_node_nil]; rfl; rw [get_node_cons]; rfl

end Basic

section ChildNodes

/-!
# ChildNodes

It can be convenient to obtain a list of the immediate child nodes of a given tree.
This is equivalent to and actually just defined via mapping each child tree to its root.
-/

/-- The `childNodes` are the roots of the `childTrees`. -/
def childNodes (t : InfiniteTreeSkeleton α) : InfiniteList α := t.childTrees.map root

/-- When getting the nth child node, we can instead get the tree element at the singleton address `[n]`. -/
theorem get_childNodes {t : InfiniteTreeSkeleton α} {n : Nat} : t.childNodes.get n = t.get [n] := by rfl

/-- Each child node is a tree member. -/
theorem mem_of_mem_childNodes {t : InfiniteTreeSkeleton α} : ∀ c ∈ t.childNodes, c ∈ t := by
  rintro c ⟨n, c_mem⟩
  rw [get_childNodes] at c_mem
  exact ⟨_, c_mem⟩

end ChildNodes

section Suffixes

/-!
## Suffixes

Here, we define a suffix relation on `InfiniteTreeSkeleton` inspired by `List.IsSuffix`.
For `t1` and `t2`, `t1 <:+ t2` denotes that `t1` is a subtree of `t2`.

The suffix relation is reflexive and transitive but not necesarrily antisymmetric!
Note also that `InfiniteList.suffix_or_suffix_of_suffix` has no equivalent statement here, i.e.
just because two trees are subtrees of the same parent tree, we cannot say anything about their relation to one another.
They might be totally "disconnected".
-/

/-- A suffix relation on infinite trees. This is inspired by `List.IsSuffix`. Read `t1 <:+ t2` as: t1 is a subtree of t2. -/
def IsSuffix (t1 t2 : InfiniteTreeSkeleton α) : Prop := ∃ ns, t2.drop ns = t1
infixl:50 " <:+ " => IsSuffix

/-- The suffix relation is reflexive. -/
theorem IsSuffix_refl {t : InfiniteTreeSkeleton α} : t <:+ t := by exists []

/-- The suffix relation is transitive. -/
theorem IsSuffix_trans {t1 t2 t3 : InfiniteTreeSkeleton α} : t1 <:+ t2 -> t2 <:+ t3 -> t1 <:+ t3 := by
  rintro ⟨ns1, h1⟩ ⟨ns2, h2⟩
  exists (ns2 ++ ns1)
  rw [← h1, ← h2]
  apply ext
  intro n
  simp only [get_drop, ← List.append_assoc]

/-- A member of a subtree is also a member of the current tree. -/
theorem mem_of_mem_suffix {t1 t2 : InfiniteTreeSkeleton α} (suffix : t1 <:+ t2) : ∀ e ∈ t1, e ∈ t2 := by
  rintro e ⟨ns, e_eq⟩
  rcases suffix with ⟨ms, suffix⟩
  exists ms ++ ns
  rw [← suffix, get_drop] at e_eq
  exact e_eq

/-- Dropping elements yields a subtree. -/
theorem IsSuffix_drop {t : InfiniteTreeSkeleton α} : ∀ ns, t.drop ns <:+ t := by intro ns; exists ns

/-- Each child tree is a subtree. -/
theorem IsSuffix_of_mem_childTrees {t : InfiniteTreeSkeleton α} : ∀ c ∈ t.childTrees, c <:+ t := by rintro c ⟨n, c_mem⟩; exists [n]

end Suffixes

section ElementRecursor

/-!
## Recursor for Members

We define a recursion (induction) principle for members (`Element`s) of an `InfiniteTreeSkeleton` called `mem_rec`.
This can be used with the `induction` tactic to prove a property for each `Element` of an `InfiniteTreeSkeleton`.
Note that for using this coveniently, the goal needs to expressed (rewritten) using an `Element`.
-/

/-- A list `Element` is a Subtype featuring a proof of being a tree member. -/
def Element (t : InfiniteTreeSkeleton α) := { e : α // e ∈ t }

/-- A recursor for proving properties about tree members (`Element`s) via induction. -/
theorem mem_rec
    {t : InfiniteTreeSkeleton α}
    {motive : Element t -> Prop}
    (root : motive ⟨t.root, t.root_mem⟩)
    (step : ∀ t2, (suffix : t2 <:+ t) -> motive ⟨t2.root, t2.mem_of_mem_suffix suffix _ t2.root_mem⟩ -> ∀ {c}, (mem : c ∈ t2.childNodes) -> motive ⟨c, mem_of_mem_suffix suffix _ (mem_of_mem_childNodes _ mem)⟩)
    (a : Element t) :
    motive a := by
  rcases a.property with ⟨ns, a_mem⟩
  let rev_ns := ns.reverse
  have a_mem : a = ⟨t.get rev_ns.reverse, t.get_mem⟩ := by simp only [rev_ns, List.reverse_reverse, a_mem]; rfl
  induction eq : rev_ns generalizing a ns with
  | nil => rw [a_mem, eq, List.reverse_nil]; exact root
  | cons hd tl ih =>
    specialize step (t.drop tl.reverse) (t.IsSuffix_drop _)
    rw [a_mem, eq, List.reverse_cons]
    apply step
    . simp only [root_drop]
      apply ih _ tl.reverse rfl <;> simp
    . exists hd

end ElementRecursor

section Branches

/-!
# Branches

Branches are essentially `InfiniteList` in an `InfiniteTreeSkeleton`
and can be characterizes by an infinite "address", i.e. `InfiniteList Nat`.
-/

/-- This function defines the `InfiniteList` of tree elemenets that corresponds to a given infinite address. -/
def branchForAddress (t : InfiniteTreeSkeleton α) (ns : InfiniteList Nat) : InfiniteList α := fun n => t.get (ns.take n)

/-- The `branches` in the `InfiniteTreeSkeleton` are exactly the `InfiniteList`s for which an infinite address exists. -/
def branches (t : InfiniteTreeSkeleton α) : Set (InfiniteList α) := fun b => ∃ ns, b = t.branchForAddress ns

/-- Getting from the branch corresponding to an infinite address corresponds to getting from the tree at the corresponding finite part of the address. This essentially unfold the definition of `branchForAddress`. -/
theorem get_branchForAddress {t : InfiniteTreeSkeleton α} {ns : InfiniteList Nat} {n : Nat} : (t.branchForAddress ns).get n = t.get (ns.take n) := by rfl

/-- The `InfiniteList.head` of `branchForAddress` is the tree's `root`. -/
theorem head_branchForAddress {t : InfiniteTreeSkeleton α} {ns : InfiniteList Nat} : (t.branchForAddress ns).head = t.root := by rfl

/-- The `InfiniteList.tail` of `branchForAddress` corresponds to a branch in a child tree. -/
theorem tail_branchForAddress {t : InfiniteTreeSkeleton α} {ns : InfiniteList Nat} : (t.branchForAddress ns).tail = (t.childTrees.get ns.head).branchForAddress ns.tail := by rfl

/-- The `branchForAddress` for an `InfiniteList.cons` address can be decomposed accordingly. -/
theorem branchForAddress_cons {t : InfiniteTreeSkeleton α} {n : Nat} {ns : InfiniteList Nat} :
    t.branchForAddress (InfiniteList.cons n ns) = InfiniteList.cons t.root ((t.childTrees.get n).branchForAddress ns) := by
  conv => left; rw [InfiniteList.cons_head_tail (t.branchForAddress (InfiniteList.cons n ns))]
  rw [head_branchForAddress, tail_branchForAddress, InfiniteList.head_cons, InfiniteList.tail_cons]

/-- The `branches` of a tree constructed through `node` are exactly the ones who's head is the root from the construction and who's tail occurs in the `branches` of one of the child trees. -/
theorem branches_node {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} :
    (node root childTrees).branches = fun b => b.head = root ∧ ∃ n, b.tail ∈ (childTrees.get n).branches := by
  apply Set.ext
  intro b
  constructor
  . rintro ⟨ns, h⟩
    constructor
    . rw [h, head_branchForAddress, root_node]
    . exists ns.head, ns.tail
      rw [h, tail_branchForAddress, childTrees_node]
  . rintro ⟨head_eq, n, ns, tail_eq⟩
    exists InfiniteList.cons n ns
    rw [branchForAddress_cons, root_node, childTrees_node]
    rw [InfiniteList.cons_head_tail b]
    rw [head_eq, tail_eq]

end Branches

section Generate

/-!
# Branch Generation

We can use `InfiniteList.generate` to construct `branches` in a `InfiniteTreeSkeleton`.
First of all, this requires that the mapper function produces an `InfiniteTreeSkeleton`.
By that `InfiniteList.generate` gives us an `InfiniteList` of `InfiniteTreeSkeleton`s.
Intuitively, using all the roots of these trees gives us a branch.
But this is only true if the generate trees are always child trees of each other.
This condition is used in the `generate_branch_mem_branches` theorem to proof that an `InfiniteList`
from the `generate_branch` function is indeed in `branches`.
-/

/-- Given a generator and a mapper that maps generated elements to `InfiniteTreeSkeleton`s, construct an `InfiniteList` with the goal of constructing a branch in a tree. -/
def generate_branch (start : β) (generator : β -> β) (mapper : β -> InfiniteTreeSkeleton α) : InfiniteList α :=
  (InfiniteList.generate start generator mapper).map root

/-- If the generated trees are `childTrees` of each other, then the generated `InfiniteList` is indeed a branch. -/
theorem generate_branch_mem_branches {start : β} {generator : β -> β} {mapper : β -> InfiniteTreeSkeleton α}
    (next_is_child : ∀ b, mapper (generator b) ∈ (mapper b).childTrees) :
    generate_branch start generator mapper ∈ (mapper start).branches := by
  let addresses : InfiniteList Nat := InfiniteList.generate start generator (fun b => Classical.choose (next_is_child b))
  let trees := InfiniteList.generate start generator mapper
  have : ∀ n, trees.get n = trees.head.drop (addresses.take n) := by
    intro n
    induction n with
    | zero => simp [InfiniteList.take_zero, drop_nil, InfiniteList.head]
    | succ n ih =>
      rw [InfiniteList.take_succ', ← drop_drop, ← ih]
      simp only [trees, InfiniteList.get_succ_generate]
      have eq_child := Classical.choose_spec (next_is_child ((InfiniteList.iterate start generator).get n))
      rw [← eq_child]
      rw [get_childTrees]
      rfl
  exists addresses
  apply InfiniteList.ext
  intro n
  simp only [generate_branch]
  rw [InfiniteList.get_map, get_branchForAddress]
  rw [this, root_drop]
  simp only [trees]
  rw [InfiniteList.head_generate]

/-- The `InfiniteList.head` of `generate_branch` is the `root` of the first tree. -/
theorem head_generate_branch {start : β} {generator : β -> β} {mapper : β -> InfiniteTreeSkeleton α} : (generate_branch start generator mapper).head = (mapper start).root := rfl

/-- Getting the nth element from a `generate_branch` result is the root of the nth generated tree. -/
theorem get_generate_branch {start : β} {generator : β -> β} {mapper : β -> InfiniteTreeSkeleton α} :
  ∀ n, (generate_branch start generator mapper).get n = ((InfiniteList.generate start generator mapper).get n).root := by intros; rfl

/-- The `InfiniteList.tail` of `generate_branch` is the branch generated when applying the generator function once on the starting element before the actual generation. -/
theorem tail_generate_branch {start : β} {generator : β -> β} {mapper : β -> InfiniteTreeSkeleton α} : (generate_branch start generator mapper).tail = generate_branch (generator start) generator mapper := by unfold generate_branch; rw [InfiniteList.tail_map, InfiniteList.tail_generate]

end Generate

end InfiniteTreeSkeleton

