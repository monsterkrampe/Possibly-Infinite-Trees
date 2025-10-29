import BasicLeanDatastructures.Set.Basic

import PossiblyInfiniteTrees.PossiblyInfiniteList.PossiblyInfiniteList

def InfiniteTreeSkeleton (α : Type u) := (List Nat) -> α

namespace InfiniteTreeSkeleton

  def get (t : InfiniteTreeSkeleton α) (ns : List Nat) : α := t ns

  def drop (t : InfiniteTreeSkeleton α) (ns : List Nat) : InfiniteTreeSkeleton α := fun ns' => t.get (ns ++ ns')

  theorem drop_eq {t : InfiniteTreeSkeleton α} {ns : List Nat} : t.drop ns = fun ns' => t.get (ns ++ ns') := rfl

  theorem drop_nil {t : InfiniteTreeSkeleton α} : t.drop [] = t := by rfl

  theorem get_drop {t : InfiniteTreeSkeleton α} {ns ns' : List Nat} : (t.drop ns).get ns' = t.get (ns ++ ns') := by rfl

  theorem drop_drop {t : InfiniteTreeSkeleton α} {ns ns' : List Nat} : (t.drop ns).drop ns' = t.drop (ns ++ ns') := by
    rw [drop_eq]; simp only [get_drop]; rw [drop_eq]; simp

  theorem ext {t1 t2 : InfiniteTreeSkeleton α} : (∀ ns, t1.get ns = t2.get ns) -> t1 = t2 := by
    apply funext

  theorem ext_iff {t1 t2 : InfiniteTreeSkeleton α} : t1 = t2 ↔ (∀ ns, t1.get ns = t2.get ns) := by
    constructor
    . intro h _; rw [h]
    . exact ext

  def node (root : α) (childTrees : InfiniteList (InfiniteTreeSkeleton α)) : InfiniteTreeSkeleton α
  | .nil => root
  | .cons hd tl => childTrees hd tl

  theorem get_node_nil {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : (node root childTrees).get [] = root := by rfl
  theorem get_node_cons {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : ∀ n ns, (node root childTrees).get (n :: ns) = (childTrees.get n).get ns := by intro n ns; rfl

  def root (t : InfiniteTreeSkeleton α) : α := t.get []
  def childTrees (t : InfiniteTreeSkeleton α) : InfiniteList (InfiniteTreeSkeleton α) := fun n ns => t.get (n::ns)

  theorem root_drop {t : InfiniteTreeSkeleton α} {ns : List Nat} : (t.drop ns).root = t.get ns := by
    unfold root; rw [get_drop]; simp

  theorem root_node {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : (node root childTrees).root = root := by rfl
  theorem childTrees_node {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : (node root childTrees).childTrees = childTrees := by rfl

  theorem node_root_childTrees (t : InfiniteTreeSkeleton α) : t = node t.root t.childTrees := by apply ext; intro ns; cases ns; rw [get_node_nil]; rfl; rw [get_node_cons]; rfl

  theorem get_childTrees {t : InfiniteTreeSkeleton α} : ∀ n, (t.childTrees.get n) = t.drop [n] := by intros; rfl
  theorem get_get_childTrees {t : InfiniteTreeSkeleton α} : ∀ n ns, (t.childTrees.get n).get ns = t.get (n::ns) := by intros; rfl

  theorem drop_node_cons {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} {n : Nat} {ns : List Nat} :
      (node root childTrees).drop (n::ns) = (childTrees.get n).drop ns := by
    rfl

  def childNodes (t : InfiniteTreeSkeleton α) : InfiniteList α := t.childTrees.map root

  theorem get_childNodes {t : InfiniteTreeSkeleton α} {n : Nat} : t.childNodes.get n = t.get [n] := by rfl

  def branchForAddress (t : InfiniteTreeSkeleton α) (ns : InfiniteList Nat) : InfiniteList α := fun n => t.get (ns.take n)
  def branches (t : InfiniteTreeSkeleton α) : Set (InfiniteList α) := fun b => ∃ ns, b = t.branchForAddress ns

  theorem get_branchForAddress {t : InfiniteTreeSkeleton α} {ns : InfiniteList Nat} {n : Nat} : (t.branchForAddress ns).get n = t.get (ns.take n) := by rfl
  theorem head_branchForAddress {t : InfiniteTreeSkeleton α} {ns : InfiniteList Nat} : (t.branchForAddress ns).head = t.root := by rfl
  theorem tail_branchForAddress {t : InfiniteTreeSkeleton α} {ns : InfiniteList Nat} : (t.branchForAddress ns).tail = (t.childTrees.get ns.head).branchForAddress ns.tail := by rfl
  theorem branchForAddress_cons {t : InfiniteTreeSkeleton α} {n : Nat} {ns : InfiniteList Nat} : t.branchForAddress (InfiniteList.cons n ns) = InfiniteList.cons t.root ((t.childTrees.get n).branchForAddress ns) := by
    conv => left; rw [InfiniteList.cons_head_tail (t.branchForAddress (InfiniteList.cons n ns))]
    rw [head_branchForAddress, tail_branchForAddress, InfiniteList.head_cons, InfiniteList.tail_cons]

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

end InfiniteTreeSkeleton

