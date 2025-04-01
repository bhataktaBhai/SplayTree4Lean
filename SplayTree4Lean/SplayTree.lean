import Mathlib.Order.Basic -- for LinearOrder
import Mathlib.Data.Nat.Basic -- for LinearOrder Nat

inductive SplayTree (α : Type)
  | nil : SplayTree α
  | node (val : α) (left right : SplayTree α) : SplayTree α

namespace SplayTree

def rotateLeftChild {α : Type} : SplayTree α → SplayTree α
  | node x (node y A B) C => node y A (node x B C)
  | t => t

def rotateRightChild {α : Type} : SplayTree α → SplayTree α
  | node x A (node y B C) => node y (node x A B) C
  | t => t

/--
Inductive type to keep track of where a particular value is present in a tree,
in the first two levels: at the `root`, the `left` child of the root,
the `right` child of the root, or `idk` because I do not know what to name this
case.
-/
inductive Location
  | root | left | right | idk

/-- Returns the `Location` of the supplied value in the supplied tree. -/
def locationOf {α : Type} [LinearOrder α] (x : α) : SplayTree α → Location
  | nil => .idk
  | node y yL yR =>
    if x = y then .root
    else if x < y then
      match yL with
      | nil => .idk
      | node yl _ _ =>
          if x = yl then .left
          else .idk
    else
      match yR with
      | nil => .idk
      | node yr _ _ =>
          if x = yr then .right
          else .idk

/--
Looks for a value `x` in a `SplayTree`.
If found, splays the tree at that node, executing zig-zig and zig-zag steps
but *not* a zig step.
That is, if `x` ends up as a child of the root, a final rotation to bring it to
the root is *not* performed.
This is necessary for recursion to work in the `splay` function.
-/
def splayButOne {α : Type} [LinearOrder α] (x : α) : SplayTree α → SplayTree α
  | nil => nil
  | node y yL yR =>
      if x = y then
        node y yL yR
      else if x < y then
        let yL' := splayButOne x yL
        match locationOf x yL' with
        | .root => node y yL' yR
        | .left => node y yL' yR |> rotateLeftChild |> rotateLeftChild -- zig-zig
        | .right => node y (rotateRightChild yL') yR |> rotateLeftChild -- zig-zag
        | .idk => node y yL' yR
      else
        let yR' := splayButOne x yR
        match locationOf x yR' with
        | .root => node y yL yR'
        | .right => node y yL yR' |> rotateRightChild |> rotateRightChild -- zig-zig
        | .left => node y yL (rotateLeftChild yR') |> rotateRightChild -- zig-zag
        | .idk => node y yL yR'

/--
Looks for a value `x` in a `SplayTree`.
If found, splays the tree at that node.
-/
def splay {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  let t' := splayButOne x t
  match locationOf x t' with
  | .root => t'
  | .left => rotateLeftChild t'
  | .right => rotateRightChild t'
  | .idk => t'

def find {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  splay x t

def split {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α × SplayTree α :=
  let t' := splay x t
  match t' with
  | nil => (nil, nil)
  | node y A B =>
      if x < y then (A, node y nil B)
      else if x > y then (node y A nil, B)
      else (A, B)

def join {α : Type} [LinearOrder α] (A B : SplayTree α) : SplayTree α :=
  match A, B with
  | nil, _ => B
  | _, nil => A
  | node y A1 A2, _ => node y A1 (join A2 B)

def insert {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  let (L, R) := split x t
  node x L R

def delete {α : Type} [LinearOrder α] (x : α) (t : SplayTree α) : SplayTree α :=
  let t' := splay x t
  match t' with
  | nil => nil
  | node y A B => if y = x then join A B else t'

def fromList {α : Type} [LinearOrder α] (L : List α) : SplayTree α :=
  L.foldl (fun t x => insert x t) nil

def toList {α : Type} : SplayTree α → List α
  | nil => []
  | node x l r => toList l ++ [x] ++ toList r

end SplayTree

section demo
open SplayTree

def exampleTree1 : SplayTree Nat :=
  insert 10 (insert 20 (insert 30 (insert 25 (insert 5 (insert (15 : ℕ) SplayTree.nil)))))

def L : List Nat := [5, 3, 8, 1, 4, 7, 9]

def exampleTree2 : SplayTree Nat :=
  fromList L

#eval exampleTree1
#eval exampleTree2
#eval find 15 exampleTree1
#eval find 5 exampleTree1
#eval delete 5 exampleTree1

end demo
