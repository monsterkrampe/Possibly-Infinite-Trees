-- We mimic Mathlib's Stream' a lot here.
-- Still I keep this separate to see better what is actually needed
-- and since what we need should be simple enough.

def InfiniteList (α : Type u) := Nat -> α

namespace InfiniteList

  def get (l : InfiniteList α) (n : Nat) : α := l n

  instance : Membership α (InfiniteList α) where
    mem l a := ∃ n, l.get n = a

  def drop (l : InfiniteList α) (n : Nat) : InfiniteList α := fun i => l.get (n + i)

  theorem get_drop {l : InfiniteList α} {n i : Nat} : (l.drop n).get i = l.get (n + i) := by rfl

  theorem ext {l1 l2 : InfiniteList α} : (∀ n, l1.get n = l2.get n) -> l1 = l2 := by
    apply funext

  theorem ext_iff {l1 l2 : InfiniteList α} : l1 = l2 ↔ (∀ n, l1.get n = l2.get n) := by
    constructor
    . intro h _; rw [h]
    . exact ext

  theorem drop_zero {l : InfiniteList α} : l.drop 0 = l := by apply ext; intro n; rw [get_drop, Nat.zero_add]

  def cons (hd : α) (tl : InfiniteList α) : InfiniteList α
  | .zero => hd
  | .succ n => tl n

  theorem get_cons_zero {hd : α} {tl : InfiniteList α} : (cons hd tl).get 0 = hd := by rfl
  theorem get_cons_succ {hd : α} {tl : InfiniteList α} : ∀ n, (cons hd tl).get n.succ = tl.get n := by intro n; rfl

  def head (l : InfiniteList α) : α := l.get 0
  def tail (l : InfiniteList α) : InfiniteList α := fun n => l.get n.succ

  theorem tail_eq {l : InfiniteList α} : l.tail = fun n => l.get n.succ := rfl

  theorem head_cons {hd : α} {tl : InfiniteList α} : (cons hd tl).head = hd := by rfl
  theorem tail_cons {hd : α} {tl : InfiniteList α} : (cons hd tl).tail = tl := by rfl

  theorem cons_head_tail (l : InfiniteList α) : l = cons l.head l.tail := by apply ext; intro n; cases n; rw [get_cons_zero]; rfl; rw [get_cons_succ]; rfl

  theorem get_tail {l : InfiniteList α} : ∀ n, l.tail.get n = l.get n.succ := by intros; rfl

  theorem head_drop {l : InfiniteList α} : ∀ {n}, (l.drop n).head = l.get n := by intros; rfl
  theorem tail_drop {l : InfiniteList α} : ∀ {n}, (l.drop n).tail = l.drop n.succ := by
    intros; unfold tail; apply ext; intro n; simp only [get_drop]; simp only [get]; rw [Nat.add_succ, Nat.succ_add]

  -- a recursor for proving properties about list members via induction
  theorem mem_rec
      {motive : α -> Prop}
      {l : InfiniteList α}
      {a : α}
      (a_mem : a ∈ l)
      (head : motive l.head)
      (step : ∀ n, motive (l.drop n).head -> motive (l.drop n).tail.head) :
      motive a := by
    rcases a_mem with ⟨n, a_mem⟩
    induction n generalizing a with
    | zero => rw [← a_mem]; exact head
    | succ n ih =>
      specialize step n
      simp only [head_drop, tail_drop] at step
      rw [← a_mem]
      apply step
      apply ih
      rfl

  def map (l : InfiniteList α) (f : α -> β) : InfiniteList β := fun n => f (l.get n)

  theorem get_map {l : InfiniteList α} {f : α -> β} {n : Nat} : (l.map f).get n = f (l.get n) := by rfl

  def take (l : InfiniteList α) : Nat -> List α
  | .zero => []
  | .succ n => l.head :: (l.tail.take n)

  theorem length_take {l : InfiniteList α} : ∀ {n}, (l.take n).length = n := by
    intro n
    induction n generalizing l with
    | zero => simp [take]
    | succ n ih => simp [take, ih]

  theorem take_zero {l : InfiniteList α} : l.take 0 = [] := by rfl
  theorem take_succ {l : InfiniteList α} : ∀ n, l.take n.succ = l.head :: (l.tail.take n) := by intros; rfl
  theorem take_succ' {l : InfiniteList α} : ∀ n, l.take n.succ = l.take n ++ [l.get n] := by
    intro n
    induction n generalizing l with
    | zero => simp [take_succ, take_zero, head]
    | succ n ih => rw [take_succ, ih, take_succ]; rfl

  theorem take_add {l : InfiniteList α} : ∀ n m, l.take (n + m) = l.take n ++ (l.drop n).take m := by
    intro n m
    induction m with
    | zero => simp [take_zero]
    | succ m ih => rw [← Nat.add_assoc, take_succ', take_succ', get_drop, ih, List.append_assoc]

end InfiniteList

