-- We mimic Mathlib's Stream'.Seq a lot here.
-- Still I keep this separate to see better what is actually needed
-- and since what we need should be simple enough.

import PossiblyInfiniteTrees.PossiblyInfiniteList.InfiniteList

def InfiniteList.no_holes (l : InfiniteList (Option α)) : Prop := ∀ n : Nat, l.get n = none -> l.get n.succ = none

structure PossiblyInfiniteList (α : Type u) where
  infinite_list : InfiniteList (Option α)
  no_holes : infinite_list.no_holes

namespace PossiblyInfiniteList

  def empty : PossiblyInfiniteList α where
    infinite_list := fun _ => none
    no_holes := by intro _ _; rfl

  def get? (l : PossiblyInfiniteList α) (n : Nat) : Option α := l.infinite_list.get n

  theorem get?_empty {α} : ∀ {n}, (@PossiblyInfiniteList.empty α).get? n = none := by intro _; rfl

  theorem no_holes' {l : PossiblyInfiniteList α} : ∀ n, l.get? n = none -> l.get? n.succ = none := by exact l.no_holes

  instance : Membership α (PossiblyInfiniteList α) where
    mem l a := some a ∈ l.infinite_list

  theorem mem_iff {l : PossiblyInfiniteList α} : ∀ {e}, e ∈ l ↔ ∃ n, l.get? n = some e := by rfl

  theorem get?_eq_none_of_le_of_eq_none {l : PossiblyInfiniteList α} {n : Nat} :
      l.get? n = none -> ∀ m, n ≤ m -> l.get? m = none := by
    intro h
    have : ∀ k, l.get? (n + k) = none := by
      intro k
      induction k with
      | zero => exact h
      | succ k ih => apply l.no_holes; exact ih
    intro m le
    rcases Nat.exists_eq_add_of_le le with ⟨k, k_eq⟩
    rw [k_eq]
    exact this k

  def drop (l : PossiblyInfiniteList α) (n : Nat) : PossiblyInfiniteList α where
    infinite_list := l.infinite_list.drop n
    no_holes := by intro n'; rw [InfiniteList.get_drop, InfiniteList.get_drop, Nat.add_succ]; exact l.no_holes (n + n')

  theorem get?_drop {l : PossiblyInfiniteList α} {n i : Nat} : (l.drop n).get? i = l.get? (n + i) := by rfl

  theorem ext {l1 l2 : PossiblyInfiniteList α} : (∀ n, l1.get? n = l2.get? n) -> l1 = l2 := by
    intro h; rw [PossiblyInfiniteList.mk.injEq]; apply InfiniteList.ext; exact h

  theorem ext_iff {l1 l2 : PossiblyInfiniteList α} : l1 = l2 ↔ (∀ n, l1.get? n = l2.get? n) := by
    constructor
    . intro h _; rw [h]
    . exact ext

  theorem drop_zero {l : PossiblyInfiniteList α} : l.drop 0 = l := by
    rw [PossiblyInfiniteList.mk.injEq]; exact InfiniteList.drop_zero

  def cons (hd : α) (tl : PossiblyInfiniteList α) : PossiblyInfiniteList α where
    infinite_list := InfiniteList.cons (.some hd) tl.infinite_list
    no_holes := by
      intro n
      cases n with
      | zero => intro contra; rw [← InfiniteList.head.eq_def, InfiniteList.head_cons] at contra; simp at contra
      | succ n =>
        rw [← InfiniteList.tail.eq_def, InfiniteList.tail_cons]
        rw [← InfiniteList.tail.eq_def, InfiniteList.tail_cons]
        exact tl.no_holes n

  theorem get?_cons_zero {hd : α} {tl : PossiblyInfiniteList α} : (cons hd tl).get? 0 = .some hd := by unfold get?; unfold cons; rw [InfiniteList.get_cons_zero]
  theorem get?_cons_succ {hd : α} {tl : PossiblyInfiniteList α} : ∀ n, (cons hd tl).get? n.succ = tl.get? n := by intro n; unfold get?; unfold cons; rw [InfiniteList.get_cons_succ]

  def head (l : PossiblyInfiniteList α) : Option α := l.infinite_list.head
  def tail (l : PossiblyInfiniteList α) : PossiblyInfiniteList α where
    infinite_list := l.infinite_list.tail
    no_holes := by intro n; rw [InfiniteList.get_tail, InfiniteList.get_tail]; exact l.no_holes n.succ

  theorem head_eq {l : PossiblyInfiniteList α} : l.head = l.get? 0 := by rfl

  theorem head_cons (hd : α) (tl : PossiblyInfiniteList α) : (cons hd tl).head = hd := InfiniteList.head_cons
  theorem tail_cons (hd : α) (tl : PossiblyInfiniteList α) : (cons hd tl).tail = tl := by simp [cons, tail, InfiniteList.tail_cons]

  theorem cons_head_tail (l : PossiblyInfiniteList α) (hd : α) (h : l.head = .some hd) : l = cons hd l.tail := by rw [PossiblyInfiniteList.mk.injEq]; simp only [cons]; rw [← h]; apply InfiniteList.cons_head_tail

  theorem get?_tail {l : PossiblyInfiniteList α} : ∀ n, l.tail.get? n = l.get? n.succ := by intros; rfl

  theorem head_drop {l : PossiblyInfiniteList α} : ∀ {n}, (l.drop n).head = l.get? n := by intros; rfl
  theorem tail_drop {l : PossiblyInfiniteList α} : ∀ {n}, (l.drop n).tail = l.drop n.succ := by
    intros; unfold tail drop; apply ext; intro n; simp only [get?, InfiniteList.tail_drop]

  theorem empty_iff_head_none {l : PossiblyInfiniteList α} : l = PossiblyInfiniteList.empty ↔ l.head = none := by
    constructor
    . intro h; rw [h]; simp [head, empty, InfiniteList.head, InfiniteList.get]
    intro h
    apply ext
    intro n
    induction n with
    | zero => rw [get?_empty]; exact h
    | succ n ih =>
      rw [get?_empty] at ih
      rw [get?_empty]
      apply l.no_holes
      exact ih

  def map (l : PossiblyInfiniteList α) (f : α -> β) : PossiblyInfiniteList β where
    infinite_list := l.infinite_list.map (fun o => o.map f)
    no_holes := by intro n; simp only [InfiniteList.get_map, Option.map_eq_none_iff]; apply l.no_holes

  theorem get?_map {l : PossiblyInfiniteList α} {f : α -> β} {n : Nat} : (l.map f).get? n = (l.get? n).map f := by rfl

  def finite (l : PossiblyInfiniteList α) : Prop := ∃ k, l.get? k = none

  theorem finite_empty {α} : (@PossiblyInfiniteList.empty α).finite := by exists 0

  theorem map_finite_of_finite {l : PossiblyInfiniteList α} {f : α -> β} : l.finite -> (l.map f).finite := by
    rintro ⟨i, h⟩; exists i; rw [get?_map, Option.map_eq_none_iff]; exact h

  def toList_of_finite (l : PossiblyInfiniteList α) (fin : l.finite) : List α :=
    let rec loop (n : Nat) : List α :=
      match eq : l.get? n with
      | .none => []
      | .some a =>
        have termination_hint : Classical.choose fin - (n + 1) < Classical.choose fin - n := by
          apply Nat.sub_add_lt_sub _ (by simp)
          have spec := Classical.choose_spec fin
          apply Classical.byContradiction
          intro contra
          simp only [Nat.not_le] at contra
          have contra := Nat.le_of_lt_succ contra
          have := l.get?_eq_none_of_le_of_eq_none spec _ contra
          rw [eq] at this
          simp at this
        a :: loop (n+1)
    termination_by (Classical.choose fin) - n
    loop 0

  theorem getElem?_toList_of_finite {l : PossiblyInfiniteList α} {fin : l.finite} : ∀ {n}, (l.toList_of_finite fin)[n]? = l.get? n := by
    have : ∀ n m, (toList_of_finite.loop l fin m)[n]? = l.get? (m + n) := by
      intro n
      induction n with
      | zero =>
        intro m; unfold toList_of_finite.loop
        split
        case h_1 eq => simp [eq]
        case h_2 eq => simp [eq]
      | succ n ih =>
        intro m; unfold toList_of_finite.loop; specialize ih (m+1); rw [Nat.add_comm n 1, ← Nat.add_assoc, ← ih]
        split
        case h_2 eq => rw [Nat.add_comm 1 n, List.getElem?_cons_succ]
        case h_1 eq =>
          unfold toList_of_finite.loop
          split
          . simp
          case h_2 eq2 =>
            have := l.no_holes m eq
            unfold PossiblyInfiniteList.get? at eq2
            rw [this] at eq2
            simp at eq2
    intro n
    unfold toList_of_finite
    rw [this n 0, Nat.zero_add]

  theorem mem_toList_of_finite {l : PossiblyInfiniteList α} {fin : l.finite} : ∀ {e}, e ∈ l.toList_of_finite fin ↔ e ∈ l := by
    intro e
    rw [List.mem_iff_getElem?]
    constructor
    . intro h; rcases h with ⟨i, h⟩; exists i; rw [getElem?_toList_of_finite] at h; exact h
    . intro h; rcases h with ⟨i, h⟩; exists i; rw [getElem?_toList_of_finite]; exact h

  theorem map_toList_of_finite {l : PossiblyInfiniteList α} {fin : l.finite} {f : α -> β} : (l.toList_of_finite fin).map f = (l.map f).toList_of_finite (map_finite_of_finite fin) := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_map, getElem?_toList_of_finite, getElem?_toList_of_finite]
    rfl

  theorem toList_of_finite_empty_iff {l : PossiblyInfiniteList α} {fin : l.finite} : l.toList_of_finite fin = [] ↔ l = PossiblyInfiniteList.empty := by
    constructor
    . intro eq
      apply PossiblyInfiniteList.ext
      rw [List.ext_getElem?_iff] at eq
      intro n
      specialize eq n
      rw [getElem?_toList_of_finite] at eq
      rw [eq]
      rfl
    . intro eq
      apply List.ext_getElem?
      intro n
      rw [getElem?_toList_of_finite]
      rw [eq]
      rw [get?_empty, List.getElem?_nil]

  def from_list (l : List α) : PossiblyInfiniteList α where
    infinite_list := fun n => l[n]?
    no_holes := by intro n; simp only [InfiniteList.get]; simp only [List.getElem?_eq_none_iff]; exact Nat.le_succ_of_le

  theorem get?_from_list {l : List α} : ∀ {n}, (from_list l).get? n = l[n]? := by intros; rfl

  theorem finite_from_list {l : List α} : (from_list l).finite := by exists l.length; rw [get?_from_list]; apply List.getElem?_eq_none; simp

  theorem toList_of_finite_after_from_list {l : List α} : (from_list l).toList_of_finite finite_from_list = l := by
    apply List.ext_getElem?; intro i; rw [getElem?_toList_of_finite, get?_from_list]

end PossiblyInfiniteList

