-- import SplayTree4Lean.SplayMap
-- import SplayTree4Lean.SplayTree
import Mathlib.Order.Basic -- for LinearOrder

-- open SplayMap
universe u v
variable {α : Type u} [LinearOrder α]

-- theorem right_rotate_preserves_inorder {α : Type u} {β : Type v} :
--   ∀ (T : SplayMap α β), toList (rotateRightChild T) = toList T := by
--   intro T
--   match T with
--   | nil => rfl
--   | node yk yv yL yR =>
--     match yR with
--     | nil => rfl
--     | node xk xv xL xR => simp [rotateRightChild, toList]

-- theorem left_rotate_preserves_inorder {α : Type u} {β : Type v} :
--   ∀ (T : SplayMap α β), toList (rotateLeftChild T) = toList T := by
--   intro T
--   match T with
--   | nil => rfl
--   | node yk yv yL yR =>
--     match yL with
--     | nil => rfl
--     | node xk xv xL xR => simp [rotateLeftChild, toList]

@[simp]
lemma lt_gt_false (x y : α) (hlt : x < y) (hgt : y < x) : False := by
  have : x < x := lt_trans' hgt hlt
  simp_all

@[simp]
lemma gt_of_ne_not_lt (x y : α) (hneq : ¬x = y) (hlt : ¬x < y) : y < x := by
  have h := lt_or_lt_iff_ne.mpr hneq
  have h' := Or.resolve_left h
  exact h' hlt
