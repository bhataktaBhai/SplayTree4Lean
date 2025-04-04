import Mathlib.Order.Basic -- for LinearOrder
import Mathlib.Data.Nat.Basic -- for LinearOrder Nat
import Mathlib.Data.Nat.MaxPowDiv -- for maxPowDiv

universe u v
variable {α : Type u} [LinearOrder α]
variable {β : Type v}

inductive SplayMap (α : Type u) (β : Type v)
  | nil : SplayMap α β
  | node (key : α) (val : β) (left right : SplayMap α β) : SplayMap α β
  deriving DecidableEq, BEq

namespace SplayMap

def toStr [ToString α] [ToString β] (header : String) : SplayMap α β → String
  | nil => header ++ "nil\n"
  | node yk yv yL yR => header ++ toString (yk, yv) ++ "\n" ++ toStr header' yL ++ toStr header' yR
      where header' := header ++ "    "

instance [ToString α] [ToString β] : ToString (SplayMap α β) where
  toString := toStr ""

/-- Rotates the edge joining the supplied node and its left child, if it exists. -/
def rotateLeftChild : SplayMap α β → SplayMap α β
  | node yk yv (node xk xv xL xR) yR => node xk xv xL (node yk yv xR yR)
  | t => t

/-- Rotates the edge joining the supplied node and its right child, if it exists. -/
def rotateRightChild : SplayMap α β → SplayMap α β
  | node yk yv yL (node xk xv xL xR) => node xk xv (node yk yv yL xL) xR
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
def locationOf (t : SplayMap α β) (x : α) : Location :=
  match t with
  | nil => .idk
  | node yk _ yL yR =>
    if x = yk then .root
    else if x < yk then
      match yL with
      | nil => .idk
      | node ylk _ _ _ =>
          if x = ylk then .left
          else .idk
    else
      match yR with
      | nil => .idk
      | node yrk _ _ _ =>
          if x = yrk then .right
          else .idk

/--
Looks for a value `x` in a `SplayMap`.
If found, splays the tree at that node, executing zig-zig and zig-zag steps
but *not* a zig step.
That is, if `x` ends up as a child of the root, a final rotation to bring it to
the root is *not* performed.
This is necessary for recursion to work in the `splay` function.
-/
def splayButOne (t : SplayMap α β) (x : α) : SplayMap α β :=
  match t with
  | nil => nil
  | node yk yv yL yR =>
      if x = yk then
        t
      else if x < yk then
        let yL := yL.splayButOne x
        match yL.locationOf x with
        | .root => node yk yv yL yR
        | .left => node yk yv yL yR |> rotateLeftChild |> rotateLeftChild -- zig-zig
        | .right => node yk yv (rotateRightChild yL) yR |> rotateLeftChild -- zig-zag
        | .idk => node yk yv yL yR
      else
        let yR := yR.splayButOne x
        match yR.locationOf x with
        | .root => node yk yv yL yR
        | .right => node yk yv yL yR |> rotateRightChild |> rotateRightChild -- zig-zig
        | .left => node yk yv yL (rotateLeftChild yR) |> rotateRightChild -- zig-zag
        | .idk => node yk yv yL yR

/--
Looks for a value `x` in a `SplayMap`.
If found, splays the tree at that node.
-/
def splay (t : SplayMap α β) (x : α) : SplayMap α β :=
  let t := t.splayButOne x
  match t.locationOf x with
  | .root => t
  | .left => rotateLeftChild t
  | .right => rotateRightChild t
  | .idk => t

/-- Alias for `splay`. -/
def find (t : SplayMap α β) (x : α) : SplayMap α β :=
  t.splay x

/-- Doesn't work, needs rewriting `splay`. -/
def split (t : SplayMap α β) (x : α) : SplayMap α β × SplayMap α β :=
  let t := t.splay x
  match t with
  | nil => (nil, nil)
  | node yk yv yL yR =>
      if x < yk then (yL, node yk yv nil yR)
      else if x > yk then (node yk yv yL nil, yR)
      else (yL, yR)

def join (A B : SplayMap α β) : SplayMap α β :=
  match A, B with
  | nil, _ => B
  | _, nil => A
  | node yk yv yL yR, _ => node yk yv yL (join yR B)

/-- Doesn't work, needs rewriting `splay`. -/
def insert (t : SplayMap α β) (xk : α) (xv : β) : SplayMap α β :=
  let (L, R) := t.split xk
  node xk xv L R

def delete (t : SplayMap α β) (x : α) : SplayMap α β :=
  let t := t.splay x
  match t with
  | nil => nil
  | node yk _ yL yR => if yk = x then join yL yR else t

/-- Builds a `SplayMap` from a `List` by inserting its elements one-by-one. -/
def fromList (L : List (α × β)) : SplayMap α β :=
  L.foldl (fun t (xk, xv) => t.insert xk xv) nil

/-- Returns the elements of the tree in order. -/
def toList : SplayMap α β → List (α × β)
  | nil => []
  | node xk xv xL xR => toList xL ++ [(xk, xv)] ++ toList xR

end SplayMap
