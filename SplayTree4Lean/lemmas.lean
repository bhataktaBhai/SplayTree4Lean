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

lemma lt_gt_false (x y : α) (hlt : x < y) (hgt : y < x) : False := by
  have : x < x := lt_trans' hgt hlt
  simp_all
