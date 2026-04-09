/-
Copyright 2026 Lukas Gerlach
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import PossiblyInfiniteTrees.PossiblyInfiniteList.InfiniteList

/-!
# PossiblyInfiniteList

A note in the beginning:
We mimic Mathlib's Stream'.Seq a lot here.
Still I keep this separate to have full control about all the details.
In the end, what we need should be simple enough.

This file defines a `PossiblyInfiniteList` which is an `InfiniteList` over an `Option` of the desired type.
The offered functions are very similar to the ones of `InfiniteList`.
-/

public section

/-- An `InfiniteList` over `Option` has `no_holes` if an element being `none` implies its successors also being `none`. This is a property that we want for possibly infinite lists but we need to be able to express it on the underlying infinite list first. -/
@[expose]
def InfiniteList.no_holes (l : InfiniteList (Option α)) : Prop :=
  ∀ n : Nat, l.get n = none -> l.get n.succ = none

/-- A `PossiblyInfiniteList` is an `InfiniteList` over `Option` that has `no_holes`. -/
structure PossiblyInfiniteList (α : Type u) where
  infinite_list : InfiniteList (Option α)
  no_holes : infinite_list.no_holes

namespace PossiblyInfiniteList

section Basic

/-!
## Basics

The essential functions on infinite lists, mainly get, drop, head, and tail.
-/

/-- Obtains the nth element from the list. -/
@[expose]
def get? (l : PossiblyInfiniteList α) (n : Nat) : Option α := l.infinite_list.get n

/-- Obtain another possibly infinite list by dropping the first n elements from the current one. -/
def drop (l : PossiblyInfiniteList α) (n : Nat) : PossiblyInfiniteList α where
  infinite_list := l.infinite_list.drop n
  no_holes := by intro n'; rw [InfiniteList.get_drop, InfiniteList.get_drop, Nat.add_succ]; exact l.no_holes (n + n')

/-- Returns the first element. -/
@[expose]
def head (l : PossiblyInfiniteList α) : Option α := l.infinite_list.head

/-- Drops the first element. -/
def tail (l : PossiblyInfiniteList α) : PossiblyInfiniteList α where
  infinite_list := l.infinite_list.tail
  no_holes := by intro n; rw [InfiniteList.get_tail, InfiniteList.get_tail]; exact l.no_holes n.succ

/-- Constructs a possibly infinite list from a possibly infinite list and a new head element. -/
def cons (hd : α) (tl : PossiblyInfiniteList α) : PossiblyInfiniteList α where
  infinite_list := InfiniteList.cons (.some hd) tl.infinite_list
  no_holes := by
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simp only [InfiniteList.get_cons_succ]
      exact tl.no_holes n

instance : Membership α (PossiblyInfiniteList α) where
  mem l a := some a ∈ l.infinite_list

/-- An element is a member of the list iff it occurs at some index. -/
theorem mem_iff {l : PossiblyInfiniteList α} : ∀ {e}, e ∈ l ↔ ∃ n, l.get? n = some e := by rfl

/-- Two possibly infinite lists are the same of they are the same on all indices. -/
@[ext, grind ext]
theorem ext {l1 l2 : PossiblyInfiniteList α} : (∀ n, l1.get? n = l2.get? n) -> l1 = l2 := by
  intro h; rw [PossiblyInfiniteList.mk.injEq]; apply InfiniteList.ext; exact h

/-- `InfiniteList.no_holes` restated for the `PossiblyInfiniteList`. -/
@[grind ->]
theorem no_holes' {l : PossiblyInfiniteList α} : ∀ n, l.get? n = none -> l.get? n.succ = none := by exact l.no_holes

/-- A closed version of the `no_holes` property. That is, if an element is none, then not only its immediate successor but all successors are none. -/
@[grind ->]
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

/-- Get after drop can be rewritten into get. -/
@[simp, grind =]
theorem get?_drop {l : PossiblyInfiniteList α} {n i : Nat} : (l.drop n).get? i = l.get? (n + i) := InfiniteList.get_drop

/-- Dropping zero elements changes nothing. -/
@[simp, grind =]
theorem drop_zero {l : PossiblyInfiniteList α} : l.drop 0 = l := by
  rw [PossiblyInfiniteList.mk.injEq]; exact InfiniteList.drop_zero

/-- The head is the same as getting the element at index zero. -/
theorem head_eq {l : PossiblyInfiniteList α} : l.head = l.get? 0 := by unfold head; rw [InfiniteList.head_eq]; rfl

/-- The `head` is in the list. -/
@[grind ->]
theorem head_mem {l : PossiblyInfiniteList α} : ∀ h ∈ l.head, h ∈ l := by
  intro h h_mem; rw [Option.mem_def] at h_mem; simp only [Membership.mem, ← h_mem]; exact l.infinite_list.head_mem

/-- Getting the head after dropping n equals getting n. -/
@[simp, grind =]
theorem head_drop {l : PossiblyInfiniteList α} : ∀ {n}, (l.drop n).head = l.get? n := InfiniteList.head_drop

/-- Getting the nth element from the tail equals getting the successor of n from the original list. -/
@[simp, grind =]
theorem get?_tail {l : PossiblyInfiniteList α} : ∀ n, l.tail.get? n = l.get? n.succ := InfiniteList.get_tail

/-- Getting the tail after dropping n is the same as dropping n.succ. -/
@[simp, grind =]
theorem tail_drop {l : PossiblyInfiniteList α} : ∀ {n}, (l.drop n).tail = l.drop n.succ := by
  intros; unfold tail drop; ext; simp

/-- Getting the first element on cons is the new head. -/
@[simp, grind =]
theorem get?_cons_zero {hd : α} {tl : PossiblyInfiniteList α} : (cons hd tl).get? 0 = .some hd := by simp [get?, cons]

/-- Getting any index > 0 on cons yields the respective element from the previous possibly infinite list. -/
@[simp, grind =]
theorem get?_cons_succ {hd : α} {tl : PossiblyInfiniteList α} : ∀ n, (cons hd tl).get? n.succ = tl.get? n := by simp [get?, cons]

/-- The `head` of `cons` is the head used in the construction. -/
@[simp, grind =]
theorem head_cons (hd : α) (tl : PossiblyInfiniteList α) : (cons hd tl).head = hd := InfiniteList.head_cons

/-- The `tail` of `cons` is the list used in the construction. -/
@[simp, grind =]
theorem tail_cons (hd : α) (tl : PossiblyInfiniteList α) : (cons hd tl).tail = tl := by simp [cons, tail]

/-- Any `PossiblyInfiniteList` can be written using the `cons` constructor. -/
theorem cons_head_tail (l : PossiblyInfiniteList α) (hd : α) (h : l.head = .some hd) : l = cons hd l.tail := by
  rw [PossiblyInfiniteList.mk.injEq]; simp only [cons]; rw [← h]; apply InfiniteList.cons_head_tail

end Basic

section Suffixes

/-!
## Suffixes

Here, we define a suffix relation on `PossiblyInfiniteList` inspired by `List.IsSuffix`.
For `l1` and `l2`, `l1 <:+ l2` denotes that `l1` is a suffix of `l2`.

The suffix relation is reflexive and transitive but not necesarrily antisymmetric!
-/

/-- A suffix relation on possibly infinite lists. This is inspired by `List.IsSuffix`. Read `l1 <:+ l2` as: l1 is a suffix of l2. -/
def IsSuffix (l1 l2 : PossiblyInfiniteList α) : Prop := l1.infinite_list <:+ l2.infinite_list
infixl:50 " <:+ " => IsSuffix

/-- l1 is a suffix of l2 if l1 can be obtained from l2 by dropping some elements. -/
theorem IsSuffix_iff {l1 l2 : PossiblyInfiniteList α} : l1 <:+ l2 ↔ ∃ n, l2.drop n = l1 := by
  unfold IsSuffix; rw [InfiniteList.IsSuffix_iff]
  constructor
  . rintro ⟨n, h⟩; exists n; simp [drop, h]
  . rintro ⟨n, h⟩; exists n; rw [← h]; simp [drop]

/-- The suffix relation is reflexive. -/
@[grind <-]
theorem IsSuffix_refl {l : PossiblyInfiniteList α} : l <:+ l := l.infinite_list.IsSuffix_refl

/-- The suffix relation is transitive. -/
@[grind ->]
theorem IsSuffix_trans {l1 l2 l3 : PossiblyInfiniteList α} : l1 <:+ l2 -> l2 <:+ l3 -> l1 <:+ l3 := InfiniteList.IsSuffix_trans

/-- Two suffixes of the same list must be suffixes of each other in some way. This is similar to List.suffix_or_suffix_of_suffix. -/
theorem suffix_or_suffix_of_suffix {l1 l2 l3 : PossiblyInfiniteList α} : l1 <:+ l3 -> l2 <:+ l3 -> (l1 <:+ l2) ∨ (l2 <:+ l1) := InfiniteList.suffix_or_suffix_of_suffix

/-- A member of a suffix is also a member of the current list. -/
@[grind ->]
theorem mem_of_mem_suffix {l1 l2 : PossiblyInfiniteList α} (suffix : l1 <:+ l2) : ∀ e ∈ l1, e ∈ l2 := by
  intro e mem; apply InfiniteList.mem_of_mem_suffix suffix; exact mem

/-- Dropping elements yields a suffix. -/
@[grind <-]
theorem IsSuffix_drop {l : PossiblyInfiniteList α} : ∀ n, l.drop n <:+ l := l.infinite_list.IsSuffix_drop

/-- The `tail` is a suffix. -/
@[grind <-]
theorem IsSuffix_tail {l : PossiblyInfiniteList α} : l.tail <:+ l := l.infinite_list.IsSuffix_tail

end Suffixes

section ElementRecursor

/-!
## Recursor for Members

We define a recursion (induction) principle for members (`Element`s) of a `PossiblyInfiniteList` called `mem_rec`.
This can be used with the `induction` tactic to prove a property for each `Element` of a `PossiblyInfiniteList`.
Note that for using this coveniently, the goal needs to expressed (rewritten) using an `Element`.
-/

/-- A list `Element` is a Subtype featuring a proof of being a list member. -/
@[expose]
def Element (l : PossiblyInfiniteList α) := { e : α // e ∈ l }

/-- A recursor for proving properties about list members via induction. -/
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
      rw [InfiniteList.IsSuffix_iff] at suffix
      rcases suffix with ⟨n, suffix⟩
      simp only [← suffix]
      cases eq : (l.infinite_list.drop n).head with
      | none => simp only [InfiniteList.head_drop, InfiniteList.tail_drop, motive']; intro _ mem; rw [Option.mem_def, l.no_holes] at mem; simp at mem; grind
      | some b =>
        specialize step (l.drop n) (l.IsSuffix_drop n)
        apply step
        exists b, eq
        apply ih
        simp only [← suffix]
        exact eq
  apply this
  rfl

end ElementRecursor

section Map

/-!
## Map

We allow to `map` over `PossiblyInfiniteList` just like `List.map`.
-/

/-- Applies a function to each list element; just like `List.map`. -/
def map (l : PossiblyInfiniteList α) (f : α -> β) : PossiblyInfiniteList β where
  infinite_list := l.infinite_list.map (fun o => o.map f)
  no_holes := by intro n; simp only [InfiniteList.get_map, Option.map_eq_none_iff]; apply l.no_holes

/-- When getting after map, we can instead get and then apply the mapping function. -/
@[simp, grind =]
theorem get?_map {l : PossiblyInfiniteList α} {f : α -> β} {n : Nat} : (l.map f).get? n = (l.get? n).map f := InfiniteList.get_map

/-- An element `e` is in the mapped list if there was an element that maps to `e`. -/
@[simp]
theorem mem_map {l : PossiblyInfiniteList α} {f : α -> β} : ∀ e, e ∈ (l.map f) ↔ ∃ e' ∈ l, f e' = e := by
  intro e
  rw [mem_iff]
  constructor
  . rintro ⟨i, e_mem⟩; rw [get?_map, Option.map_eq_some_iff] at e_mem; rcases e_mem with ⟨e', e'_mem, e_eq⟩; exists e'; constructor; exists i; exact e_eq
  . rintro ⟨e', ⟨i, e'_mem⟩, e_eq⟩; rw [← e_eq]; exists i; rw [get?_map, Option.map_eq_some_iff]; exists e'

/-- The head of a mapped list is the same as applying the function to the head. -/
@[simp, grind =]
theorem head_map {l : PossiblyInfiniteList α} {f : α -> β} : (l.map f).head = l.head.map f := InfiniteList.head_map

/-- The tail of a mapped list is the same as applyign map to the tail. -/
@[simp, grind =]
theorem tail_map {l : PossiblyInfiniteList α} {f : α -> β} : (l.map f).tail = l.tail.map f := by ext; simp

end Map


section Attach

/-!
## Attach

We allow to `attach` membership proofs to list elements just like `List.attach`.
-/

/-- Attaches a membership proof to each list element. -/
def attach (l : PossiblyInfiniteList α) : PossiblyInfiniteList l.Element where
  infinite_list := l.infinite_list.attach.map (fun e => e.val.attach.map (fun v => ⟨v.val, by rw [mem_iff]; rcases e.property with ⟨n, eq⟩; exists n; simp only [get?]; rw [eq]; exact v.property⟩))
  no_holes := by intro n; simpa using l.no_holes n

/-- Calling `get` after `attach` returns the correct element with its membership proof. -/
theorem val_get_attach {l : PossiblyInfiniteList α} :
  ∀ {n}, (l.attach.get? n).map (fun e => e.val) = l.get? n := by intros; simp [get?, attach]

end Attach

section Generate

/-!
## Generating a PossiblyInfiniteList

We provide functions for "step-by-step" generation of a `PossiblyInfiniteList` from a function building a next element from an existing one. This is very similar to what is done for Mathlib's `Stream'.Seq`.
-/

/-- Making use of `InfiniteList.generate`, we can also generate a `PossiblyInfiniteList` only that the start value and the result of the generator function are now options. -/
def generate (start : Option α) (generator : α -> Option α) (mapper : α -> β) : PossiblyInfiniteList β := {
  infinite_list := InfiniteList.generate start (·.bind generator) (·.map mapper)
  no_holes := by
    intro n
    rw [InfiniteList.get_generate, InfiniteList.get_succ_generate, Option.map_eq_none_iff, Option.map_eq_none_iff]
    intro eq
    rw [eq, Option.bind_none]
}

/-- The head of a generated list is the mapped version of the starting value. -/
@[simp, grind =]
theorem head_generate {start : Option α} {generator : α -> Option α} {mapper : α -> β} :
  (generate start generator mapper).head = start.map mapper := InfiniteList.head_generate

/-- The nth element of a generated list is the mapped version of the nth element of the iterated "carrier" list. -/
theorem get?_generate {start : Option α} {generator : α -> Option α} {mapper : α -> β} :
  ∀ n, (generate start generator mapper).get? n = ((InfiniteList.iterate start (·.bind generator)).get n).map mapper := InfiniteList.get_generate

/-- The successor of the nth element of a generated list can be seen as applying the mapper function after the generator function after taking the nth element from the iterated "carrier" list. -/
theorem get?_succ_generate {start : Option α} {generator : α -> Option α} {mapper : α -> β} :
    ∀ n, (generate start generator mapper).get? n.succ = (((InfiniteList.iterate start (·.bind generator)).get n).bind generator).map mapper :=
  InfiniteList.get_succ_generate

/-- The tail of a generated list is the list generated when applying the generator function once on the starting element before the actual generation. -/
theorem tail_generate {start : Option α} {generator : α -> Option α} {mapper : α -> β} :
    (generate start generator mapper).tail = generate (start.bind generator) generator mapper := by
  simp only [generate, tail, mk.injEq]
  exact InfiniteList.tail_generate

end Generate

section Empty

/-!
## Empty Infinite Lists

The `empty` `PossiblyInfiniteList` is simply the `PossiblyInfiniteList` that is `none` on all indices.
-/

/-- The empty `PossiblyInfiniteList` is none everywhere. -/
def empty : PossiblyInfiniteList α where
  infinite_list := fun _ => none
  no_holes := by intro _ _; rw [InfiniteList.compute_get]

/-- Getting from the empty list always returns none. -/
@[simp, grind =]
theorem get?_empty {α} : ∀ {n}, (@PossiblyInfiniteList.empty α).get? n = none := by
  intro _; unfold get?; rw [InfiniteList.compute_get]; rfl

/-- The head of the empty list is none. -/
@[simp, grind =]
theorem head_empty {α} : (@PossiblyInfiniteList.empty α).head = none := by simp [head_eq]

/-- The empty list stays empty when mapped. -/
@[simp, grind =]
theorem map_empty {α} {f : α -> β} : (@PossiblyInfiniteList.empty α).map f = empty := by ext; simp

/-- A `PossiblyInfiniteList` is empty if and only if its head is none. -/
theorem empty_iff_head_none {l : PossiblyInfiniteList α} : l = PossiblyInfiniteList.empty ↔ l.head = none := by
  constructor
  . intro h; simp [h]
  intro h
  apply ext
  intro n
  induction n with
  | zero => rw [get?_empty, ← head_eq]; exact h
  | succ n ih =>
    rw [get?_empty] at ih
    rw [get?_empty]
    apply l.no_holes
    exact ih

end Empty

section Finite

/-!
## Finite PossiblyInfiniteList

We define when we consider a `PossiblyInfiniteList` to be `finite`, namely when it is `none` on some index.
We also define a function converting a `finite` `PossiblyInfiniteList` into a plain `List`.
-/

/-- The `PossiblyInfiniteList` is finite if some element is none. -/
@[expose]
def finite (l : PossiblyInfiniteList α) : Prop := ∃ k, l.get? k = none

/-- Transforms a finite list into an inductive `List`. -/
def toList_of_finite (l : PossiblyInfiniteList α) (fin : l.finite) : List α :=
  let rec loop (n : Nat) : List α :=
    match eq : l.get? n with
    | .none => []
    | .some a =>
      have termination_hint : Classical.choose fin - (n + 1) < Classical.choose fin - n := by
        apply Nat.sub_add_lt_sub _ (by simp)
        grind
      a :: loop (n+1)
  termination_by (Classical.choose fin) - n
  loop 0

/-- A mapped list is finite if the original list is finite. -/
@[grind <-]
theorem map_finite_of_finite {l : PossiblyInfiniteList α} {f : α -> β} : l.finite -> (l.map f).finite := by
  rintro ⟨i, _⟩; exists i; grind

/-- The empty list is finite. -/
@[grind <-]
theorem finite_empty {α} : (@PossiblyInfiniteList.empty α).finite := by exists 0; simp

/-- The nth element in the transformed list is the nth element from the original list. -/
@[simp, grind =]
theorem getElem?_toList_of_finite {l : PossiblyInfiniteList α} {fin : l.finite} : ∀ {n}, (l.toList_of_finite fin)[n]? = l.get? n := by
  have : ∀ n m, (toList_of_finite.loop l fin m)[n]? = l.get? (m + n) := by
    intro n
    induction n with
    | zero =>
      unfold toList_of_finite.loop
      grind
    | succ n ih =>
      intro m; unfold toList_of_finite.loop; specialize ih (m+1); rw [Nat.add_comm n 1, ← Nat.add_assoc, ← ih]
      split
      case h_2 eq => grind
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

/-- An element is in the transformed finite list if and only if it is in the original list. -/
@[simp, grind =]
theorem mem_toList_of_finite {l : PossiblyInfiniteList α} {fin : l.finite} : ∀ {e}, e ∈ l.toList_of_finite fin ↔ e ∈ l := by
  intro e
  rw [List.mem_iff_getElem?, mem_iff]
  constructor <;> (intro h; rcases h with ⟨i, h⟩; exists i; grind)

/-- Mapping over the transformed finite list is the same as mapping first and then transforming. -/
@[simp, grind =]
theorem map_toList_of_finite {l : PossiblyInfiniteList α} {fin : l.finite} {f : α -> β} :
  (l.toList_of_finite fin).map f = (l.map f).toList_of_finite (map_finite_of_finite fin) := by apply List.ext_getElem?; simp

/-- The transformed list is empty if and only if the original list is empty. -/
theorem toList_of_finite_empty_iff {l : PossiblyInfiniteList α} {fin : l.finite} : l.toList_of_finite fin = [] ↔ l = PossiblyInfiniteList.empty := by
  constructor
  . intro eq
    rw [List.ext_getElem?_iff] at eq
    apply PossiblyInfiniteList.ext
    intro n
    specialize eq n
    grind
  . intro eq
    apply List.ext_getElem?
    simp [eq]

end Finite

section FromList

/-!
## Converting a List into a PossiblyInfiniteList

We can always convert a plain `List` into a `PossiblyInfiniteList` by setting all indices beyond the length of the list to none.
-/

/-- Builds a PossiblyInfiniteList from an inductive `List`. -/
def from_list (l : List α) : PossiblyInfiniteList α where
  infinite_list := fun n => l[n]?
  no_holes := by intro n; simp only [InfiniteList.compute_get]; simp only [List.getElem?_eq_none_iff]; exact Nat.le_succ_of_le

/-- After building from a `List`, the nth elements are the same. -/
@[simp, grind =]
theorem get?_from_list {l : List α} : ∀ {n}, (from_list l).get? n = l[n]? := by intros; unfold from_list get?; rw [InfiniteList.compute_get]

/-- When building from a `List`, the `PossiblyInfiniteList` is `finite`. -/
@[grind <-]
theorem finite_from_list {l : List α} : (from_list l).finite := by exists l.length; simp

/-- Transforming a `List` to a `PossiblyInfiniteList` and back, gives the original list. -/
@[simp, grind =]
theorem toList_of_finite_after_from_list {l : List α} : (from_list l).toList_of_finite finite_from_list = l := by ext; simp

end FromList

end PossiblyInfiniteList

