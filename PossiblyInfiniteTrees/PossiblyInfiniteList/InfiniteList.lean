/-!
# InfiniteList

A note in the beginning:
We mimic Mathlib's Stream' a lot here.
Still I keep this separate to have full control about all the details.
In the end, what we need should be simple enough.

This file defines an `InfiniteList` as a function from the naturals into the desired type.
We abstract away from this using many convenience functions.
For example, we offer `head` and `tail` to give the list a more coinductive flavor.
Also, there is `mem_rec` as a recursor over list elements to allow showing properties of list members via induction.
Furthermore, we offer a `generate` function that can build an infinite list from a function that builds a new element from a previous one.
-/

/-- An `InfiniteList` is defined as a function from the naturals into the desired type. -/
def InfiniteList (α : Type u) := Nat -> α

namespace InfiniteList

section Basic

/-!
## Basics

The essential functions on infinite lists, mainly get, drop, head, and tail.
-/

/-- Obtains the nth element from the list. -/
def get (l : InfiniteList α) (n : Nat) : α := l n

/-- Obtain another infinite list by dropping the first n elements from the current one. -/
def drop (l : InfiniteList α) (n : Nat) : InfiniteList α := fun i => l.get (n + i)

/-- Returns the first element. -/
def head (l : InfiniteList α) : α := l.get 0

/-- Drops the first element. -/
def tail (l : InfiniteList α) : InfiniteList α := fun n => l.get n.succ

/-- Constructs an infinite list from an infinite list and a new head element. -/
def cons (hd : α) (tl : InfiniteList α) : InfiniteList α
| .zero => hd
| .succ n => tl n

instance : Membership α (InfiniteList α) where
  mem l a := ∃ n, l.get n = a

/-- Two infinite lists are the same of they are the same on all indices. -/
theorem ext {l1 l2 : InfiniteList α} : (∀ n, l1.get n = l2.get n) -> l1 = l2 := by
  apply funext

theorem ext_iff {l1 l2 : InfiniteList α} : l1 = l2 ↔ (∀ n, l1.get n = l2.get n) := by
  constructor
  . intro h _; rw [h]
  . exact ext

/-- Each element we can get is in the list. -/
theorem get_mem {l : InfiniteList α} {n : Nat} : l.get n ∈ l := by exists n

/-- Get after drop can be rewritten into get. -/
theorem get_drop {l : InfiniteList α} {n i : Nat} : (l.drop n).get i = l.get (n + i) := by rfl

/-- Dropping zero elements changes nothing. -/
theorem drop_zero {l : InfiniteList α} : l.drop 0 = l := by apply ext; intro n; rw [get_drop, Nat.zero_add]

/-- The `head` is in the list. -/
theorem head_mem {l : InfiniteList α} : l.head ∈ l := l.get_mem (n := 0)

/-- Getting the head after dropping n equals getting n. -/
theorem head_drop {l : InfiniteList α} : ∀ {n}, (l.drop n).head = l.get n := by intros; rfl

/-- Helper theorem stating the definition of tail. -/
theorem tail_eq {l : InfiniteList α} : l.tail = fun n => l.get n.succ := rfl

/-- Getting the nth element from the tail equals getting the successor of n from the original list. -/
theorem get_tail {l : InfiniteList α} : ∀ n, l.tail.get n = l.get n.succ := by intros; rfl

/-- Getting the tail after dropping n is the same as dropping n.succ. -/
theorem tail_drop {l : InfiniteList α} : ∀ {n}, (l.drop n).tail = l.drop n.succ := by
  intros; unfold tail; apply ext; intro n; simp only [get_drop]; simp only [get]; rw [Nat.add_succ, Nat.succ_add]

/-- Getting the first element on cons is the new head. -/
theorem get_cons_zero {hd : α} {tl : InfiniteList α} : (cons hd tl).get 0 = hd := by rfl

/-- Getting any index > 0 on cons yields the respective element from the previous infinite list. -/
theorem get_cons_succ {hd : α} {tl : InfiniteList α} : ∀ n, (cons hd tl).get n.succ = tl.get n := by intro n; rfl

/-- The `head` of `cons` is the head used in the construction. -/
theorem head_cons {hd : α} {tl : InfiniteList α} : (cons hd tl).head = hd := by rfl

/-- The `tail` of `cons` is the list used in the construction. -/
theorem tail_cons {hd : α} {tl : InfiniteList α} : (cons hd tl).tail = tl := by rfl

/-- Any `InfiniteList` can be written using the `cons` constructor. -/
theorem cons_head_tail (l : InfiniteList α) : l = cons l.head l.tail := by apply ext; intro n; cases n; rw [get_cons_zero]; rfl; rw [get_cons_succ]; rfl

end Basic

section Suffixes

/-!
## Suffixes

Here, we define a suffix relation on `InfiniteList` inspired by `List.IsSuffix`.
For `l1` and `l2`, `l1 <:+ l2` denotes that `l1` is a suffix of `l2`.

The suffix relation is reflexive and transitive but not necesarrily antisymmetric!
-/

/-- A suffix relation on infinite lists. This is inspired by `List.IsSuffix`. Read `l1 <:+ l2` as: l1 is a suffix of l2. -/
def IsSuffix (l1 l2 : InfiniteList α) : Prop := ∃ n, l2.drop n = l1
infixl:50 " <:+ " => IsSuffix

/-- The suffix relation is reflexive. -/
theorem IsSuffix_refl {l : InfiniteList α} : l <:+ l := by exists 0; exact l.drop_zero

/-- The suffix relation is transitive. -/
theorem IsSuffix_trans {l1 l2 l3 : InfiniteList α} : l1 <:+ l2 -> l2 <:+ l3 -> l1 <:+ l3 := by
  rintro ⟨n1, h1⟩ ⟨n2, h2⟩
  exists (n2 + n1)
  rw [← h1, ← h2]
  apply ext
  intro n
  simp only [get_drop, ← Nat.add_assoc]

/-- Two suffixes of the same list must be suffixes of each other in some way. This is similar to List.suffix_or_suffix_of_suffix. -/
theorem suffix_or_suffix_of_suffix {l1 l2 l3 : InfiniteList α} : l1 <:+ l3 -> l2 <:+ l3 -> (l1 <:+ l2) ∨ (l2 <:+ l1) := by
  rintro ⟨n, eq⟩ ⟨n2, eq2⟩
  cases Decidable.em (n2 ≤ n) with
  | inl le =>
    apply Or.inl
    exists (n - n2)
    apply ext
    intro n3
    rw [← eq2, ← eq, get_drop, get_drop, get_drop, ← Nat.add_assoc, Nat.add_sub_of_le le]
  | inr le =>
    have le := Nat.le_of_not_le le
    apply Or.inr
    exists (n2 - n)
    apply ext
    intro n3
    rw [← eq2, ← eq, get_drop, get_drop, get_drop, ← Nat.add_assoc, Nat.add_sub_of_le le]

/-- A member of a suffix is also a member of the current list. -/
theorem mem_of_mem_suffix {l1 l2 : InfiniteList α} (suffix : l1 <:+ l2) : ∀ e ∈ l1, e ∈ l2 := by
  rintro e ⟨n, e_eq⟩
  rcases suffix with ⟨m, suffix⟩
  exists m + n
  rw [← suffix, get_drop] at e_eq
  exact e_eq

/-- Dropping elements yields a suffix. -/
theorem IsSuffix_drop {l : InfiniteList α} : ∀ n, l.drop n <:+ l := by intro n; exists n

/-- The `tail` is a suffix. -/
theorem IsSuffix_tail {l : InfiniteList α} : l.tail <:+ l := by exists 1; apply ext; intro n; rw [get_drop, get_tail, Nat.add_comm]

end Suffixes

section ElementRecursor

/-!
## Recursor for Members

We define a recursion (induction) principle for members (`Element`s) of an `InfiniteList` called `mem_rec`.
This can be used with the `induction` tactic to prove a property for each `Element` of an `InfiniteList`.
Note that for using this coveniently, the goal needs to expressed (rewritten) using an `Element`.
-/

/-- A list `Element` is a Subtype featuring a proof of being a list member. -/
def Element (l : InfiniteList α) := { e : α // e ∈ l }

/-- A recursor for proving properties about list members (`Element`s) via induction. -/
theorem mem_rec
    {l : InfiniteList α}
    {motive : Element l -> Prop}
    (head : motive ⟨l.head, l.head_mem⟩)
    (step : ∀ l2, (suffix : l2 <:+ l) -> motive ⟨l2.head, l2.mem_of_mem_suffix suffix _ l2.head_mem⟩ -> motive ⟨l2.tail.head, l2.tail.mem_of_mem_suffix (IsSuffix_trans l2.IsSuffix_tail suffix) _ l2.tail.head_mem⟩)
    (a : Element l) :
    motive a := by
  rcases a.property with ⟨n, a_mem⟩
  have a_mem : a = ⟨l.get n, l.get_mem⟩ := by simp only [a_mem]; rfl
  induction n generalizing a with
  | zero => rw [a_mem]; exact head
  | succ n ih =>
    specialize step (l.drop n) (l.IsSuffix_drop n)
    simp only [head_drop, tail_drop] at step
    rw [a_mem]
    apply step
    apply ih
    . rfl
    . rfl

end ElementRecursor

section Map

/-!
## Map

We allow to `map` over `InfiniteList` just like `List.map`.
-/

/-- Applies a function to each list element. -/
def map (l : InfiniteList α) (f : α -> β) : InfiniteList β := fun n => f (l.get n)

/-- When getting after map, we can instead get and then apply the mapping function. -/
theorem get_map {l : InfiniteList α} {f : α -> β} {n : Nat} : (l.map f).get n = f (l.get n) := by rfl

/-- An element `e` is in the mapped list if there was an element that maps to `e`. -/
theorem mem_map {l : InfiniteList α} {f : α -> β} : ∀ e, e ∈ (l.map f) ↔ ∃ e' ∈ l, f e' = e := by
  intro e
  constructor
  . rintro ⟨i, e_mem⟩; rw [get_map] at e_mem; exists l.get i; exact ⟨get_mem, e_mem⟩
  . rintro ⟨e', ⟨i, e'_mem⟩, e_eq⟩; rw [← e_eq]; exists i; rw [get_map]; rw [e'_mem]

/-- The tail of a mapped list is the same as applying map to the tail. -/
theorem tail_map {l : InfiniteList α} {f : α -> β} : (l.map f).tail = l.tail.map f := by rfl

end Map

section Generate

/-!
## Generating an InfiniteList

We provide functions for "step-by-step" generation of an `InfiniteList` from a function building a next element from an existing one. This is very similar to what is done for Mathlib's `Stream'`.
-/

/-- Construct an infinite list by repeating a generator function. This is essentially Stream'.iterate from Mathlib. -/
def iterate (start : α) (generator : α -> α) : InfiniteList α
| .zero => start
| .succ n => generator (iterate start generator n)

/-- When getting the successor of a number `n` from an interated list, we can instead get the nth element and apply the generator once mode. -/
theorem get_succ_iterate {start : α} {generator : α -> α} :
  ∀ n, (iterate start generator).get n.succ = generator ((iterate start generator).get n) := by intros; rfl

/-- When getting the successor of a number `n` from an interated list, we can instead apply the generator once initially, then iterate and then get the nth element. -/
theorem get_succ_iterate' {start : α} {generator : α -> α} : ∀ n, (iterate start generator).get n.succ = (iterate (generator start) generator).get n := by
  intro n; induction n with
  | zero => simp [get, iterate]
  | succ n ih => simp only [get, iterate] at *; rw [ih]

/-- Instead of only iterating, we may want to create a kind of "carrier" list and then map this to the actually desired list. This is useful when the generator function requires more information that what actually ends up being in the desired list. Note that this is essentially the same as Stream'.corec from Mathlib. -/
def generate (start : α) (generator : α -> α) (mapper : α -> β) : InfiniteList β := (iterate start generator).map mapper

/-- The head of a generated list is the mapped version of the starting value. -/
theorem head_generate {start : α} {generator : α -> α} {mapper : α -> β} : (generate start generator mapper).head = mapper start := rfl

/-- The nth element of a generated list is the mapped version of the nth element of the iterated "carrier" list. -/
theorem get_generate {start : α} {generator : α -> α} {mapper : α -> β} :
  ∀ n, (generate start generator mapper).get n = mapper ((iterate start generator).get n) := by intros; rfl

/-- The successor of the nth element of a generated list can be seen as applying the mapper function after the generator function after taking the nth element from the iterated "carrier" list. -/
theorem get_succ_generate {start : α} {generator : α -> α} {mapper : α -> β} :
  ∀ n, (generate start generator mapper).get n.succ = mapper (generator ((iterate start generator).get n)) := by intros; rfl

/-- The successor of the nth element of a generated list can be seen as taking the nth element after initializing the generation process with the generator function already applied once in the beginning. -/
theorem get_succ_generate' {start : α} {generator : α -> α} {mapper : α -> β} :
    ∀ n, (generate start generator mapper).get n.succ = (generate (generator start) generator mapper).get n := by
  intro n; simp only [generate, get_map, get_succ_iterate']

/-- The tail of a generated list is the list generated when applying the generator function once on the starting element before the actual generation. -/
theorem tail_generate {start : α} {generator : α -> α} {mapper : α -> β} : (generate start generator mapper).tail = generate (generator start) generator mapper := by
  apply ext
  intro n
  rw [get_tail]
  rw [get_succ_generate']

end Generate

section Take
/-!
## Take

The `take` function puts the first `n` elements of an `InfiniteList` into a regular `List`.
-/

/-- Obtain a finite list from an infinite list by taking the first n elements. -/
def take (l : InfiniteList α) : Nat -> List α
| .zero => []
| .succ n => l.head :: (l.tail.take n)

/-- The length of a taken list has exactly the desired number of elements. -/
theorem length_take {l : InfiniteList α} : ∀ {n}, (l.take n).length = n := by
  intro n
  induction n generalizing l with
  | zero => simp [take]
  | succ n ih => simp [take, ih]

/-- When taking zero, you get nil. -/
theorem take_zero {l : InfiniteList α} : l.take 0 = [] := by rfl

/-- When taking the successor of a number n, you get the head following by taking n from the tail. -/
theorem take_succ {l : InfiniteList α} : ∀ n, l.take n.succ = l.head :: (l.tail.take n) := by intros; rfl

/-- When taking the successor of a number n, you can take n and then also take the nth element. -/
theorem take_succ' {l : InfiniteList α} : ∀ n, l.take n.succ = l.take n ++ [l.get n] := by
  intro n
  induction n generalizing l with
  | zero => simp [take_succ, take_zero, head]
  | succ n ih => rw [take_succ, ih, take_succ]; rfl

/-- When taking the sum of two numbers, you take the first and then take the second after dropping the first. -/
theorem take_add {l : InfiniteList α} : ∀ n m, l.take (n + m) = l.take n ++ (l.drop n).take m := by
  intro n m
  induction m with
  | zero => simp [take_zero]
  | succ m ih => rw [← Nat.add_assoc, take_succ', take_succ', get_drop, ih, List.append_assoc]

end Take

end InfiniteList

