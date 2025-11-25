import PossiblyInfiniteTrees.PossiblyInfiniteList.InfiniteList

structure PossiblyInfiniteList (α : Type u) where
  infinite_list : InfiniteList (Option α)
  no_holes : ∀ n : Nat, infinite_list n ≠ none -> ∀ m : Fin n, infinite_list m ≠ none

namespace PossiblyInfiniteList
  def empty : PossiblyInfiniteList α := {
    infinite_list := fun _ => none
    no_holes := by intros; contradiction
  }

  def fromList : List α -> PossiblyInfiniteList α
  | .nil => {
    infinite_list := fun _ => none
    no_holes := by simp
  }
  | .cons a as => {
    infinite_list := fun n => match n with
    | .zero => a
    | .succ n => (fromList as).infinite_list n
    no_holes := by
      have no_holes_rec := (fromList as).no_holes
      intro n
      cases n with
      | zero => simp
      | succ n =>
        simp
        intro h m
        cases eq : m.val with
        | zero => simp
        | succ m' =>
          simp
          specialize no_holes_rec n h ⟨m-1, by
            have isLt := m.isLt
            rw [eq] at isLt
            simp at isLt
            have : m - 1 = m' := by rw [eq]; simp
            rw [this]
            exact isLt
          ⟩
          simp only [eq] at no_holes_rec
          simp at no_holes_rec
          exact no_holes_rec
  }

  theorem eq_iff_same_on_all_indices (as bs : PossiblyInfiniteList α) : as = bs ↔ ∀ n, as.infinite_list n = bs.infinite_list n := by
    constructor
    . intro h _
      rw [h]
    . intro h
      rw [PossiblyInfiniteList.mk.injEq]
      apply funext
      exact h

  theorem get_fromList_eq_list_getElem (l : List α) : ∀ n, (fromList l).infinite_list n = l[n]? := by
    induction l with
    | nil => simp [fromList]
    | cons a as ih =>
      intro n
      unfold fromList
      cases n with
      | zero => simp
      | succ n =>
        simp
        apply ih

end PossiblyInfiniteList

