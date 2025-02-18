def InfiniteList (α : Type u) := Nat -> α

namespace InfiniteList

  def take (l : InfiniteList α) : Nat -> List α
  | 0 => []
  | n+1 => (l.take n) ++ [l n]

  theorem length_take (l : InfiniteList α) (n : Nat) : (l.take n).length = n := by
    induction n ; simp [take] ; simpa [take]

  def skip (l : InfiniteList α) (m : Nat) : InfiniteList α := fun n => l (n + m)

  theorem skip_zero_eq (l : InfiniteList α) : l.skip 0 = l := by unfold skip; simp only [Nat.add_zero]

  theorem skip_m_get_sub_eq_get (l : InfiniteList α) (n m : Nat) (h : m ≤ n) : (l.skip m) (n - m) = l n := by
    unfold skip
    rw [← Nat.sub_add_comm h]
    simp

  theorem combine_skip_take (l : InfiniteList α) (n : Nat) (m : Fin n) : l.take m ++ (l.skip m).take (n-m) = l.take n := by
    induction n with
    | zero =>
      apply False.elim
      apply Nat.not_lt_zero
      apply m.isLt
    | succ k ih =>
      have : k.succ - m = (k-m).succ := by
        simp only [Nat.succ_eq_add_one]
        rw [Nat.sub_add_comm]
        apply Nat.le_of_lt_succ
        exact m.isLt
      rw [this]
      simp only [take]
      rw [skip_m_get_sub_eq_get (h := by apply Nat.le_of_lt_succ; exact m.isLt)]
      rw [← List.append_assoc]
      cases Decidable.em (m < k) with
      | inl hl =>
        rw [ih ⟨m.val, hl⟩]
      | inr hr =>
        have : m = k := by cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ m.isLt); contradiction; assumption
        rw [this]
        simp [take]

  theorem take_after_take (l : InfiniteList α) (n m : Nat) : (l.take n).take m = l.take (n.min m) := by
    induction n with
    | zero => simp [take]
    | succ n ih =>
      simp [take]
      rw [List.take_append_eq_append_take]
      rw [ih]
      rw [length_take]
      cases Decidable.em (n ≤ m) with
      | inl le =>
        simp [Nat.min_eq_left le]
        cases Nat.eq_or_lt_of_le le with
        | inl eq =>
          rw [eq]
          simp
        | inr lt =>
          simp [Nat.min_eq_left (Nat.succ_le_of_lt lt)]
          conv => right; unfold InfiniteList.take
          rw [List.take_of_length_le (by apply Nat.le_sub_of_add_le; rw [Nat.add_comm, List.length_singleton]; apply Nat.succ_le_of_lt; exact lt)]
      | inr lt =>
        simp at lt
        simp [Nat.min_eq_right (Nat.le_of_lt lt), Nat.min_eq_right (Nat.le_succ_of_le (Nat.le_of_lt lt))]
        apply Nat.sub_eq_zero_of_le (Nat.le_of_lt lt)
end InfiniteList

