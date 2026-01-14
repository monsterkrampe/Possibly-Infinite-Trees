import BasicLeanDatastructures.Set.Basic

import PossiblyInfiniteTrees.PossiblyInfiniteList.PossiblyInfiniteList

def InfiniteTreeSkeleton (α : Type u) := (List Nat) -> α

namespace InfiniteTreeSkeleton

  def get (t : InfiniteTreeSkeleton α) (ns : List Nat) : α := t ns

  instance : Membership α (InfiniteTreeSkeleton α) where
    mem t a := ∃ ns, t.get ns = a

  theorem get_mem {t : InfiniteTreeSkeleton α} {ns : List Nat} : t.get ns ∈ t := by exists ns

  def Element (t : InfiniteTreeSkeleton α) := { e : α // e ∈ t }

  def drop (t : InfiniteTreeSkeleton α) (ns : List Nat) : InfiniteTreeSkeleton α := fun ns' => t.get (ns ++ ns')

  -- inspired by List.IsSuffix; see https://github.com/leanprover/lean4/blob/9d4ad1273f6cea397c3066c2c83062a4410d16bf/src/Init/Data/List/Basic.lean#L1205
  -- here it would read as: IsSubtree
  def IsSuffix (t1 t2 : InfiniteTreeSkeleton α) : Prop := ∃ ns, t2.drop ns = t1
  infixl:50 " <:+ " => IsSuffix

  theorem drop_eq {t : InfiniteTreeSkeleton α} {ns : List Nat} : t.drop ns = fun ns' => t.get (ns ++ ns') := rfl

  theorem drop_nil {t : InfiniteTreeSkeleton α} : t.drop [] = t := by rfl

  theorem get_drop {t : InfiniteTreeSkeleton α} {ns ns' : List Nat} : (t.drop ns).get ns' = t.get (ns ++ ns') := by rfl

  theorem drop_drop {t : InfiniteTreeSkeleton α} {ns ns' : List Nat} : (t.drop ns).drop ns' = t.drop (ns ++ ns') := by
    rw [drop_eq]; simp only [get_drop]; rw [drop_eq]; simp

  theorem mem_of_mem_suffix {t1 t2 : InfiniteTreeSkeleton α} (suffix : t1 <:+ t2) : ∀ e ∈ t1, e ∈ t2 := by
    rintro e ⟨ns, e_eq⟩
    rcases suffix with ⟨ms, suffix⟩
    exists ms ++ ns
    rw [← suffix, get_drop] at e_eq
    exact e_eq

  theorem ext {t1 t2 : InfiniteTreeSkeleton α} : (∀ ns, t1.get ns = t2.get ns) -> t1 = t2 := by
    apply funext

  theorem ext_iff {t1 t2 : InfiniteTreeSkeleton α} : t1 = t2 ↔ (∀ ns, t1.get ns = t2.get ns) := by
    constructor
    . intro h _; rw [h]
    . exact ext

  theorem IsSuffix_refl {t : InfiniteTreeSkeleton α} : t <:+ t := by exists []

  theorem IsSuffix_drop {t : InfiniteTreeSkeleton α} : ∀ ns, t.drop ns <:+ t := by intro ns; exists ns

  theorem IsSuffix_trans {t1 t2 t3 : InfiniteTreeSkeleton α} : t1 <:+ t2 -> t2 <:+ t3 -> t1 <:+ t3 := by
    rintro ⟨ns1, h1⟩ ⟨ns2, h2⟩
    exists (ns2 ++ ns1)
    rw [← h1, ← h2]
    apply ext
    intro n
    simp only [get_drop, ← List.append_assoc]

  def node (root : α) (childTrees : InfiniteList (InfiniteTreeSkeleton α)) : InfiniteTreeSkeleton α
  | .nil => root
  | .cons hd tl => childTrees hd tl

  theorem get_node_nil {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : (node root childTrees).get [] = root := by rfl
  theorem get_node_cons {root : α} {childTrees : InfiniteList (InfiniteTreeSkeleton α)} : ∀ n ns, (node root childTrees).get (n :: ns) = (childTrees.get n).get ns := by intro n ns; rfl

  def root (t : InfiniteTreeSkeleton α) : α := t.get []
  def childTrees (t : InfiniteTreeSkeleton α) : InfiniteList (InfiniteTreeSkeleton α) := fun n ns => t.get (n::ns)

  theorem root_mem {t : InfiniteTreeSkeleton α} : t.root ∈ t := by exists []

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

  theorem IsSuffix_of_mem_childTrees {t : InfiniteTreeSkeleton α} : ∀ c ∈ t.childTrees, c <:+ t := by rintro c ⟨n, c_mem⟩; exists [n]

  def childNodes (t : InfiniteTreeSkeleton α) : InfiniteList α := t.childTrees.map root

  theorem get_childNodes {t : InfiniteTreeSkeleton α} {n : Nat} : t.childNodes.get n = t.get [n] := by rfl

  theorem mem_of_mem_childNodes {t : InfiniteTreeSkeleton α} : ∀ c ∈ t.childNodes, c ∈ t := by
    rintro c ⟨n, c_mem⟩
    rw [get_childNodes] at c_mem
    exact ⟨_, c_mem⟩

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

  def generate_branch (start : β) (generator : β -> β) (mapper : β -> InfiniteTreeSkeleton α) : InfiniteList α :=
    (InfiniteList.generate start generator mapper).map root

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

  theorem head_generate_branch {start : β} {generator : β -> β} {mapper : β -> InfiniteTreeSkeleton α} : (generate_branch start generator mapper).head = (mapper start).root := rfl

  theorem get_generate_branch {start : β} {generator : β -> β} {mapper : β -> InfiniteTreeSkeleton α} :
    ∀ n, (generate_branch start generator mapper).get n = ((InfiniteList.generate start generator mapper).get n).root := by intros; rfl

end InfiniteTreeSkeleton

