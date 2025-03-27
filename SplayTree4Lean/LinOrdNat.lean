import Mathlib.Order.Basic
instance : LinearOrder Nat where
  le := Nat.le
  lt := Nat.lt
  le_refl := Nat.le_refl
  le_trans := fun a b c hab hbc => Nat.le_trans hab hbc
  lt_iff_le_not_le := fun a b => ⟨
  fun h => ⟨Nat.le_of_lt h, Nat.not_le_of_gt h⟩,
  fun ⟨h1, h2⟩ => Nat.lt_of_le_of_ne h1 (fun h3 => h2 (h3 ▸ Nat.le_refl b))
  ⟩
  le_antisymm := fun a b hab hba => Nat.le_antisymm hab hba
  le_total := Nat.le_total
  decidableLE := fun a b => inferInstanceAs (Decidable (a ≤ b))
  compare := fun a b => if a < b then Ordering.lt else if a = b then Ordering.eq else Ordering.gt
  compare_eq_compareOfLessAndEq := fun a b => rfl
