import PossiblyInfiniteTrees.PossiblyInfiniteTree.InfiniteTree

def InfiniteTreeSkeleton.no_orphans (t : InfiniteTreeSkeleton (Option α)) : Prop :=
  ∀ ns : List Nat, t.get ns = none -> ∀ n, (t.drop ns).childNodes.get n = none

theorem InfiniteTreeSkeleton.no_orphans_closure {t : InfiniteTreeSkeleton (Option α)} (no_orph : t.no_orphans) :
    ∀ ns : List Nat, t.get ns = none -> ∀ ns', (t.drop ns).get ns' = none := by
  intro ns eq_none ns'
  induction ns' generalizing ns with
  | nil => rw [get_drop, List.append_nil]; exact eq_none
  | cons hd tl ih =>
    specialize ih (ns ++ [hd]) (by
      have := no_orph ns eq_none hd
      rw [get_childNodes, get_drop] at this
      exact this)
    rw [get_drop, List.append_assoc, List.singleton_append] at ih
    rw [get_drop]
    exact ih

structure PossiblyInfiniteTree (α : Type u) where
  infinite_tree : InfiniteTreeSkeleton (Option α)
  no_orphans :
    ∀ ns : List Nat, infinite_tree.get ns = none -> ∀ n, (infinite_tree.drop ns).childNodes.get n = none
  no_holes_in_children :
    ∀ ns : List Nat, (infinite_tree.drop ns).childNodes.no_holes

namespace PossiblyInfiniteTree

  def empty : PossiblyInfiniteTree α where
    infinite_tree := fun _ => none
    no_orphans := by intro _ _ _; rw [InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop]; simp [InfiniteTreeSkeleton.get]
    no_holes_in_children := by intro _ _ _; rw [InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop]; simp [InfiniteTreeSkeleton.get]

  def get? (t : PossiblyInfiniteTree α) (ns : List Nat) : Option α := t.infinite_tree.get ns

  theorem get?_empty {α} : ∀ {n}, (@PossiblyInfiniteTree.empty α).get? n = none := by intro _; rfl

  def drop (t : PossiblyInfiniteTree α) (ns : List Nat) : PossiblyInfiniteTree α where
    infinite_tree := t.infinite_tree.drop ns
    no_orphans := by intro ns'; rw [InfiniteTreeSkeleton.get_drop]; intro eq_none n; rw [InfiniteTreeSkeleton.drop_drop]; apply t.no_orphans; exact eq_none
    no_holes_in_children := by intro ns; rw [InfiniteTreeSkeleton.drop_drop]; apply t.no_holes_in_children

  theorem drop_nil {t : PossiblyInfiniteTree α} : t.drop [] = t := by rfl

  theorem get?_drop {t : PossiblyInfiniteTree α} {ns ns' : List Nat} : (t.drop ns).get? ns' = t.get? (ns ++ ns') := by rfl

  theorem drop_drop {t : PossiblyInfiniteTree α} {ns ns' : List Nat} : (t.drop ns).drop ns' = t.drop (ns ++ ns') := by simp [drop, InfiniteTreeSkeleton.drop_drop]

  theorem ext {t1 t2 : PossiblyInfiniteTree α} : (∀ ns, t1.get? ns = t2.get? ns) -> t1 = t2 := by
    intro h; rw [PossiblyInfiniteTree.mk.injEq]; apply InfiniteTreeSkeleton.ext; exact h

  theorem ext_iff {t1 t2 : PossiblyInfiniteTree α} : t1 = t2 ↔ (∀ ns, t1.get? ns = t2.get? ns) := by
    constructor
    . intro h _; rw [h]
    . exact ext

  theorem drop_empty {α} : ∀ {ns}, (@PossiblyInfiniteTree.empty α).drop ns = PossiblyInfiniteTree.empty := by
    intro _; apply ext; intro _; rw [get?_drop, get?_empty, get?_empty]

  def root (t : PossiblyInfiniteTree α) : Option α := t.infinite_tree.root

  theorem root_eq {t : PossiblyInfiniteTree α} : t.root = t.get? [] := by rfl

  theorem root_drop {t : PossiblyInfiniteTree α} {ns : List Nat} : (t.drop ns).root = t.get? ns := by
    unfold root drop; simp [InfiniteTreeSkeleton.root_drop]; rfl

  theorem root_empty {α} : (@PossiblyInfiniteTree.empty α).root = none := by rfl

  theorem empty_iff_root_none {t : PossiblyInfiniteTree α} : t = PossiblyInfiniteTree.empty ↔ t.root = none := by
    constructor
    . intro h; rw [h]; exact root_empty
    intro h
    rw [root_eq] at h
    apply PossiblyInfiniteTree.ext
    intro ns
    induction ns generalizing t with
    | nil => rw [h]; rfl
    | cons n ns ih =>
      rw [← List.singleton_append, ← get?_drop];
      rw [ih]
      . rfl
      . rw [get?_drop]
        have := t.no_orphans [] h n
        rw [InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop] at this
        exact this

  abbrev PossiblyInfiniteTreeWithRoot (α : Type u) := {t : PossiblyInfiniteTree α // t.root ≠ none}

  namespace PossiblyInfiniteTreeWithRoot

    def opt_to_tree (opt : Option (PossiblyInfiniteTreeWithRoot α)) : PossiblyInfiniteTree α :=
      match opt with
      | .none => PossiblyInfiniteTree.empty
      | .some t => t.val

    theorem opt_to_tree_none_iff {opt : Option (PossiblyInfiniteTreeWithRoot α)} : opt = none ↔ (opt_to_tree opt).root = none := by
      unfold opt_to_tree
      cases opt with
      | none => simp [root_empty]
      | some t => simp [t.property]

    def tree_to_opt (t : PossiblyInfiniteTree α) : Option (PossiblyInfiniteTreeWithRoot α) :=
      match eq : t.root with
      | .none => none
      | .some r => some ⟨t, by simp [eq]⟩

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

  def childTrees (t : PossiblyInfiniteTree α) : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α) where
    infinite_list := fun n => PossiblyInfiniteTreeWithRoot.tree_to_opt {
      infinite_tree := t.infinite_tree.childTrees.get n
      no_orphans := by intro ns; rw [InfiniteTreeSkeleton.get_get_childTrees]; intro eq_none n'; rw [InfiniteTreeSkeleton.get_childTrees, InfiniteTreeSkeleton.drop_drop]; apply t.no_orphans; exact eq_none
      no_holes_in_children := by intro ns; rw [InfiniteTreeSkeleton.get_childTrees, InfiniteTreeSkeleton.drop_drop]; apply t.no_holes_in_children
    }
    no_holes := by intro n'; simp only [InfiniteList.get]; rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff, PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff]; exact t.no_holes_in_children [] n'

  theorem childTrees_empty {α} : (@PossiblyInfiniteTree.empty α).childTrees = PossiblyInfiniteList.empty := by rfl

  def node (root : α) (childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)) : PossiblyInfiniteTree α where
    infinite_tree := InfiniteTreeSkeleton.node (.some root) (childTrees.infinite_list.map (PossiblyInfiniteTree.infinite_tree ∘ PossiblyInfiniteTreeWithRoot.opt_to_tree))
    no_orphans := by
      intro ns
      cases ns with
      | nil => intro contra; rw [← InfiniteTreeSkeleton.root.eq_def, InfiniteTreeSkeleton.root_node] at contra; simp at contra
      | cons n ns =>
        rw [← InfiniteTreeSkeleton.childTrees.eq_def, InfiniteTreeSkeleton.childTrees_node]
        intro eq_none n'
        unfold InfiniteList.map at eq_none
        rw [InfiniteTreeSkeleton.drop_node_cons, InfiniteList.get_map]
        apply (PossiblyInfiniteTreeWithRoot.opt_to_tree (childTrees.infinite_list.get n)).no_orphans
        exact eq_none
    no_holes_in_children := by
      intro ns
      cases ns with
      | nil => rw [InfiniteTreeSkeleton.drop_nil]; unfold InfiniteTreeSkeleton.childNodes; rw [InfiniteTreeSkeleton.childTrees_node]; intro n; simp only [InfiniteList.get_map, Function.comp_apply]; rw [← PossiblyInfiniteTree.root.eq_def, ← PossiblyInfiniteTree.root.eq_def, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]; exact childTrees.no_holes n
      | cons n ns =>
        rw [InfiniteTreeSkeleton.drop_node_cons, InfiniteList.get_map]
        exact (PossiblyInfiniteTreeWithRoot.opt_to_tree (childTrees.infinite_list.get n)).no_holes_in_children ns

  theorem get?_node_nil {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} : (node root childTrees).get? [] = .some root := by rfl
  theorem get?_node_cons {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} : ∀ n ns, (node root childTrees).get? (n :: ns) = (PossiblyInfiniteTreeWithRoot.opt_to_tree (childTrees.get? n)).get? ns := by intro n ns; rfl

  theorem root_node {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} : (node root childTrees).root = root := by rfl
  theorem childTrees_node {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} : (node root childTrees).childTrees = childTrees := by
    unfold node PossiblyInfiniteTree.childTrees
    simp only [InfiniteTreeSkeleton.childTrees_node, InfiniteList.get_map, Function.comp_apply]
    apply PossiblyInfiniteList.ext
    intro n
    simp only [PossiblyInfiniteList.get?, InfiniteList.get]
    rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_after_opt_to_tree]

  theorem node_root_childTrees {t : PossiblyInfiniteTree α} {root : α} (h : t.root = .some root) : t = node root t.childTrees := by
    rw [PossiblyInfiniteTree.mk.injEq]; simp only [node]; rw [← h]; rw [InfiniteTreeSkeleton.node_root_childTrees t.infinite_tree]
    apply congrArg
    unfold PossiblyInfiniteTree.childTrees
    apply InfiniteList.ext
    intro n
    simp only [InfiniteList.get_map, Function.comp_apply]
    simp only [InfiniteList.get]
    rw [PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]

  theorem get?_childTrees {t : PossiblyInfiniteTree α} : ∀ n, (t.childTrees.get? n) = PossiblyInfiniteTreeWithRoot.tree_to_opt (t.drop [n]) := by intros; rfl
  theorem get?_get?_childTrees {t : PossiblyInfiniteTree α} : ∀ n ns, (PossiblyInfiniteTreeWithRoot.opt_to_tree (t.childTrees.get? n)).get? ns = t.get? (n::ns) := by intros; rw [get?_childTrees, PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]; rfl

  theorem drop_node_cons {root : α} {childTrees : PossiblyInfiniteList (PossiblyInfiniteTreeWithRoot α)} {n : Nat} {ns : List Nat} : (node root childTrees).drop (n::ns) = (PossiblyInfiniteTreeWithRoot.opt_to_tree (childTrees.get? n)).drop ns := by rfl

  def childNodes (t : PossiblyInfiniteTree α) : PossiblyInfiniteList α where
    infinite_list := t.infinite_tree.childNodes
    no_holes := t.no_holes_in_children []

  theorem get?_childNodes {t : PossiblyInfiniteTree α} : ∀ {n}, t.childNodes.get? n = (PossiblyInfiniteTreeWithRoot.opt_to_tree (t.childTrees.get? n)).root := by
    intro n; rw [get?_childTrees, PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]; rfl

  theorem childNodes_eq {t : PossiblyInfiniteTree α} : t.childNodes = t.childTrees.map (fun t => t.val.root.get (by rw [Option.isSome_iff_ne_none]; exact t.property)) := by
    apply PossiblyInfiniteList.ext
    intro n
    rw [PossiblyInfiniteList.get?_map]
    rw [get?_childNodes, get?_childTrees, PossiblyInfiniteTreeWithRoot.opt_to_tree_after_tree_to_opt]
    apply Eq.symm
    cases eq : (t.drop [n]).root with
    | none => rw [Option.map_eq_none_iff, PossiblyInfiniteTreeWithRoot.tree_to_opt_none_iff]; exact eq
    | some r => rw [Option.map_eq_some_iff]; exists ⟨t.drop [n], by simp [eq]⟩; rw [PossiblyInfiniteTreeWithRoot.tree_to_opt_some_iff]; simp [eq]

  theorem childNodes_empty {α} : (@PossiblyInfiniteTree.empty α).childNodes = PossiblyInfiniteList.empty := by
    apply PossiblyInfiniteList.ext; intro _; rw [get?_childNodes, childTrees_empty, PossiblyInfiniteList.get?_empty, PossiblyInfiniteList.get?_empty, ← PossiblyInfiniteTreeWithRoot.opt_to_tree_none_iff]

  theorem no_orphans' {t : PossiblyInfiniteTree α} : ∀ ns : List Nat, t.get? ns = none -> ∀ n, (t.drop ns).childNodes.get? n = none := by exact t.no_orphans

  theorem no_orphans'_closure {t : PossiblyInfiniteTree α} :
      ∀ ns : List Nat, t.get? ns = none -> ∀ ns', (t.drop ns).get? ns' = none := by
    exact t.infinite_tree.no_orphans_closure t.no_orphans

  def branchForAddress (t : PossiblyInfiniteTree α) (ns : InfiniteList Nat) : PossiblyInfiniteList α where
    infinite_list := t.infinite_tree.branchForAddress ns
    no_holes := by
      intro n
      rw [InfiniteTreeSkeleton.get_branchForAddress]
      intro eq_none
      rw [InfiniteTreeSkeleton.get_branchForAddress]
      rw [InfiniteList.take_succ']
      apply t.no_orphans
      exact eq_none

  theorem get?_branchForAddress {t : PossiblyInfiniteTree α} {ns : InfiniteList Nat} {n : Nat} : (t.branchForAddress ns).get? n = t.get? (ns.take n) := by rfl

  def branchAddressIsMaximal (t : PossiblyInfiniteTree α) (ns : InfiniteList Nat) : Prop :=
    ∀ n, (t.branchForAddress ns).get? n.succ = none -> (t.drop (ns.take n)).childNodes.head = none

  def branches (t : PossiblyInfiniteTree α) : Set (PossiblyInfiniteList α) :=
    fun b => ∃ ns, b = t.branchForAddress ns ∧ t.branchAddressIsMaximal ns

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

  def leaves (t : PossiblyInfiniteTree α) : Set α := fun a => ∃ node : List Nat, t.get? node = some a ∧ (t.drop node).childNodes.head = none

  def from_branch (b : PossiblyInfiniteList α) : PossiblyInfiniteTree α where
    infinite_tree := fun ns => if ns.all (fun e => e = 0) then b.infinite_list ns.length else none
    no_orphans := by
      intro ns eq_none n
      simp only [InfiniteTreeSkeleton.get] at eq_none
      rw [InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop]
      simp only [InfiniteTreeSkeleton.get]
      cases eq : (ns ++ [n]).all (fun e => e = 0) with
      | false => rfl
      | true =>
        have : ns.all (fun e => e = 0) := by rw [List.all_append, Bool.and_eq_true] at eq; exact eq.left
        simp only [this] at eq_none
        simp only [List.length_append, List.length_singleton]
        apply b.no_holes
        exact eq_none
    no_holes_in_children := by
      intro ns n _
      rw [InfiniteTreeSkeleton.get_childNodes, InfiniteTreeSkeleton.get_drop]
      simp only [InfiniteTreeSkeleton.get]
      have : (ns ++ [n.succ]).all (fun e => e = 0) = false := by
        rw [List.all_eq_false]
        exists n.succ
        simp
      simp [this]

end PossiblyInfiniteTree

