import SplayTree4Lean.SplayMap
import SplayTree4Lean.SplayTree

open SplayMap
universe u v

theorem right_rotate_preserves_inorder {α : Type u} {β : Type v} :
  ∀ (T : SplayMap α β), toList (rotateRightChild T) = toList T := by
  intro T
  match T with
  | nil => rfl
  | node yk yv yL yR =>
    match yR with
    | nil => rfl
    | node xk xv xL xR => simp [rotateRightChild, toList]

theorem left_rotate_preserves_inorder {α : Type u} {β : Type v} :
  ∀ (T : SplayMap α β), toList (rotateLeftChild T) = toList T := by
  intro T
  match T with
  | nil => rfl
  | node yk yv yL yR =>
    match yL with
    | nil => rfl
    | node xk xv xL xR => simp [rotateLeftChild, toList]
