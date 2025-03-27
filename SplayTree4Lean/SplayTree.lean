import Mathlib.Order.Basic
import SplayTree4Lean.LinOrdNat

inductive SplayTree (α : Type)
  | empty : SplayTree α
  | node (val : α) (left right : SplayTree α) : SplayTree α
deriving Repr

def rotateRight {α : Type} : SplayTree α → SplayTree α
  | SplayTree.node x (SplayTree.node y A B) C => SplayTree.node y A (SplayTree.node x B C)
  | t => t

def rotateLeft {α : Type} : SplayTree α → SplayTree α
  | SplayTree.node x A (SplayTree.node y B C) => SplayTree.node y (SplayTree.node x A B) C
  | t => t

def splay {α : Type} [LinearOrder α] (x : α) : SplayTree α → SplayTree α
  | SplayTree.empty => SplayTree.empty
  | SplayTree.node y A B =>
      if x < y then
        match A with
        | SplayTree.node z _ _ =>
            if x < z then rotateRight (SplayTree.node y (rotateRight A) B)
            else rotateRight (SplayTree.node y (rotateLeft A) B)
        | _ => SplayTree.node y A B
      else if x > y then
        match B with
        | SplayTree.node z _ _ =>
            if x > z then rotateLeft (SplayTree.node y A (rotateLeft B)) -- Zig-Zig
            else rotateLeft (SplayTree.node y A (rotateRight B)) -- Zig-Zag
        | _ => SplayTree.node y A B
      else SplayTree.node y A B

def insert {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  let t' := splay x t
  match t' with
  | SplayTree.empty => SplayTree.node x SplayTree.empty SplayTree.empty
  | SplayTree.node y A B =>
      if x < y then SplayTree.node x A (SplayTree.node y SplayTree.empty B)
      else if x > y then SplayTree.node x (SplayTree.node y A SplayTree.empty) B
      else t'

def find {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  splay x t

def exampleTree : SplayTree Nat :=
  insert 10 (insert 20 (insert 30 (insert 25 (insert 5 (insert (15 : ℕ) SplayTree.empty)))))

#eval exampleTree  -- Check the tree structure

#eval find 15 exampleTree  -- Splay 15 to root

#eval find 5 exampleTree   -- Splay 5 to root
