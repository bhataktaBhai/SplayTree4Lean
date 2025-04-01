import Mathlib.Order.Basic -- for LinearOrder
import Mathlib.Data.Nat.Basic -- for LinearOrder Nat

inductive SplayTree (α : Type)
  | empty : SplayTree α
  | node (val : α) (left right : SplayTree α) : SplayTree α

namespace SplayTree

def rotateRight {α : Type} : SplayTree α → SplayTree α
  | node x (node y A B) C => node y A (node x B C)
  | t => t

def rotateLeft {α : Type} : SplayTree α → SplayTree α
  | node x A (node y B C) => node y (node x A B) C
  | t => t

def splay {α : Type} [LinearOrder α] (x : α) : SplayTree α → SplayTree α
  | empty => empty
  | node y A B =>
      if x < y then
        match A with
        | node z _ _ =>
            if x < z then rotateRight (node y (rotateRight A) B)
            else rotateRight (node y (rotateLeft A) B)
        | _ => node y A B
      else if x > y then
        match B with
        | node z _ _ =>
            if x > z then rotateLeft (node y A (rotateLeft B))
            else rotateLeft (node y A (rotateRight B))
        | _ => node y A B
      else node y A B

def find {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  splay x t

def split {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α × SplayTree α :=
  let t' := splay x t
  match t' with
  | empty => (empty, empty)
  | node y A B =>
      if x < y then (A, node y empty B)
      else if x > y then (node y A empty, B)
      else (A, B)

def join {α : Type} [LinearOrder α] (A B : SplayTree α) : SplayTree α :=
  match A, B with
  | empty, _ => B
  | _, empty => A
  | node y A1 A2, _ => node y A1 (join A2 B)

def insert {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  let (L, R) := split x t
  node x L R

def delete {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  let t' := splay x t
  match t' with
  | empty => empty
  | node y A B => if y = x then join A B else t'

def fromList {α : Type} [LinearOrder α] (L : List α) : SplayTree α :=
  L.foldl (fun t x => insert x t) empty

def toList {α : Type} : SplayTree α → List α
  | empty => []
  | node x l r => toList l ++ [x] ++ toList r

end SplayTree

section demo
open SplayTree

def exampleTree1 : SplayTree Nat :=
  insert 10 (insert 20 (insert 30 (insert 25 (insert 5 (insert (15 : ℕ) SplayTree.empty)))))

def L : List Nat := [5, 3, 8, 1, 4, 7, 9]

def exampleTree2 : SplayTree Nat :=
  fromList L

#eval exampleTree1
#eval exampleTree2
#eval find 15 exampleTree1
#eval find 5 exampleTree1
#eval delete 5 exampleTree1

end demo
