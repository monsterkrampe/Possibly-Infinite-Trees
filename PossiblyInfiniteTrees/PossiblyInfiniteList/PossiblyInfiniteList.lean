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

  def Element (l : PossiblyInfiniteList α) := { e : α // e ∈ l }

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

  -- inspired by List.IsSuffix; see https://github.com/leanprover/lean4/blob/9d4ad1273f6cea397c3066c2c83062a4410d16bf/src/Init/Data/List/Basic.lean#L1205
  def IsSuffix (l1 l2 : PossiblyInfiniteList α) : Prop := l1.infinite_list <:+ l2.infinite_list
  infixl:50 " <:+ " => IsSuffix

  theorem IsSuffix_iff {l1 l2 : PossiblyInfiniteList α} : l1 <:+ l2 ↔ ∃ n, l2.drop n = l1 := by
    constructor
    . rintro ⟨n, h⟩; exists n; simp [drop, h]
    . rintro ⟨n, h⟩; exists n; simp only [drop] at h; rw [← h]

  theorem get?_drop {l : PossiblyInfiniteList α} {n i : Nat} : (l.drop n).get? i = l.get? (n + i) := by rfl

  theorem mem_of_mem_suffix {l1 l2 : PossiblyInfiniteList α} (suffix : l1 <:+ l2) : ∀ e ∈ l1, e ∈ l2 := by
    intro e mem; apply InfiniteList.mem_of_mem_suffix suffix; exact mem

  theorem ext {l1 l2 : PossiblyInfiniteList α} : (∀ n, l1.get? n = l2.get? n) -> l1 = l2 := by
    intro h; rw [PossiblyInfiniteList.mk.injEq]; apply InfiniteList.ext; exact h

  theorem ext_iff {l1 l2 : PossiblyInfiniteList α} : l1 = l2 ↔ (∀ n, l1.get? n = l2.get? n) := by
    constructor
    . intro h _; rw [h]
    . exact ext

  theorem drop_zero {l : PossiblyInfiniteList α} : l.drop 0 = l := by
    rw [PossiblyInfiniteList.mk.injEq]; exact InfiniteList.drop_zero

  theorem IsSuffix_refl {l : PossiblyInfiniteList α} : l <:+ l := l.infinite_list.IsSuffix_refl

  theorem IsSuffix_drop {l : PossiblyInfiniteList α} : ∀ n, l.drop n <:+ l := l.infinite_list.IsSuffix_drop

  theorem IsSuffix_trans {l1 l2 l3 : PossiblyInfiniteList α} : l1 <:+ l2 -> l2 <:+ l3 -> l1 <:+ l3 := InfiniteList.IsSuffix_trans

  -- same statement as List.suffix_or_suffix_of_suffix
  theorem suffix_or_suffix_of_suffix {l1 l2 l3 : PossiblyInfiniteList α} : l1 <:+ l3 -> l2 <:+ l3 -> (l1 <:+ l2) ∨ (l2 <:+ l1) := InfiniteList.suffix_or_suffix_of_suffix

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
  theorem head_mem {l : PossiblyInfiniteList α} : ∀ h ∈ l.head, h ∈ l := by intro h h_mem; rw [Option.mem_def] at h_mem; simp only [Membership.mem, ← h_mem]; exact l.infinite_list.head_mem

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

  theorem IsSuffix_tail {l : PossiblyInfiniteList α} : l.tail <:+ l := l.infinite_list.IsSuffix_tail

  -- a recursor for proving properties about list members via induction
  theorem mem_rec
      {l : PossiblyInfiniteList α}
      {motive : Element l -> Prop}
      (head : ∀ head, (mem : head ∈ l.head) -> motive ⟨head, head_mem _ mem⟩)
      (step : ∀ l2, (suffix : l2 <:+ l) -> (∃ (head : α) (mem : head ∈ l2.head), motive ⟨head, l2.mem_of_mem_suffix suffix _ (l2.head_mem _ mem)⟩) -> ∀ tail_head, (mem_th : tail_head ∈ l2.tail.head) -> motive ⟨tail_head, l2.tail.mem_of_mem_suffix (IsSuffix_trans l2.IsSuffix_tail suffix) _ (l2.tail.head_mem _ mem_th)⟩)
      (a : Element l) :
      motive a := by
    let motive' (o : l.infinite_list.Element) : Prop := ∀ v, (mem : v ∈ o.val) -> motive ⟨v, by have := o.property; rw [Option.mem_def] at mem; rw [mem] at this; exact this⟩
    let a' : l.infinite_list.Element := ⟨some a.val, a.property⟩
    have : motive' a' := by
      induction a' using InfiniteList.mem_rec with
      | head => exact head
      | step l2 suffix ih =>
        rcases suffix with ⟨n, suffix⟩
        simp only [← suffix]
        cases eq : (l.infinite_list.drop n).head with
        | none => simp only [InfiniteList.head_drop, InfiniteList.tail_drop, motive']; intro _ mem; rw [Option.mem_def, l.no_holes] at mem; simp at mem; exact eq
        | some b =>
          specialize step (l.drop n) (l.IsSuffix_drop n)
          apply step
          exists b, eq
          unfold motive' at ih
          apply ih
          simp only [← suffix]
          exact eq
    apply this
    rfl

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

  def generate (start : Option α) (generator : α -> Option α) (mapper : α -> β) : PossiblyInfiniteList β := {
    infinite_list := InfiniteList.generate start (·.bind generator) (·.map mapper)
    no_holes := by
      intro n
      rw [InfiniteList.get_generate, InfiniteList.get_succ_generate, Option.map_eq_none_iff, Option.map_eq_none_iff]
      intro eq
      rw [eq, Option.bind_none]
  }

  theorem head_generate {start : Option α} {generator : α -> Option α} {mapper : α -> β} : (generate start generator mapper).head = start.map mapper := rfl

  theorem get?_generate {start : Option α} {generator : α -> Option α} {mapper : α -> β} :
    ∀ n, (generate start generator mapper).get? n = ((InfiniteList.iterate start (·.bind generator)).get n).map mapper := by intros; rfl

  theorem get?_succ_generate {start : Option α} {generator : α -> Option α} {mapper : α -> β} :
    ∀ n, (generate start generator mapper).get? n.succ = (((InfiniteList.iterate start (·.bind generator)).get n).bind generator).map mapper := by intros; rfl

end PossiblyInfiniteList

