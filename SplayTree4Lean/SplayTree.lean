import SplayTree4Lean.SplayMap

universe u
variable {α : Type u} [LinearOrder α]

def SplayTree (α : Type u) := SplayMap α Unit -- is this the best way?

namespace SplayTree

def nil : SplayTree α :=
  SplayMap.nil
def node (xk : α) : SplayTree α → SplayTree α → SplayTree α :=
  SplayMap.node xk Unit.unit

def toStr [ToString α] (header : String) : SplayTree α → String
  | SplayMap.nil => header ++ "nil\n"
  | SplayMap.node yk _ yL yR => header ++ toString yk ++ "\n" ++ toStr header' yL ++ toStr header' yR
      where header' := header ++ "    "

instance [ToString α] : ToString (SplayTree α) where
  toString := toStr ""

#synth DecidableEq (SplayMap Nat Unit)
#synth DecidableEq (SplayTree Nat) -- why does this not work?

def find : SplayTree α → α → SplayTree α :=
  SplayMap.find

def insert (t : SplayTree α) (xk : α) : SplayTree α :=
  SplayMap.insert t xk Unit.unit

def delete : SplayTree α → α → SplayTree α :=
  SplayMap.delete

def fromList : List α → SplayTree α :=
  SplayMap.fromList ∘ List.map (fun x => (x, Unit.unit))

def toList : SplayTree α → List α :=
  List.map (fun (x, _) => x) ∘ SplayMap.toList

end SplayTree

section demo
open SplayTree

/-- Doesn't work, needs rewriting `splay`. -/
def exampleTree1 : SplayTree Nat :=
  -- insert 10 (insert 20 (insert 30 (insert 25 (insert 5 (insert (15 : ℕ) nil)))))
  (((((nil.insert 15).insert 5).insert 25).insert 30).insert 20).insert 10

def L : List Nat := [5, 3, 8, 1, 4, 7, 9]

/-- Doesn't work, needs rewriting `splay`. -/
def exampleTree2 : SplayTree Nat :=
  fromList L

#eval exampleTree1
#eval exampleTree2
#eval find exampleTree1 15
#eval find exampleTree1 5
#eval delete exampleTree1 5

/-! Time for some unit testing. -/

-- The subtree of the infinite complete binary tree with r at the root
def ctf (r : Nat) : SplayTree Nat :=
  let h := Nat.maxPowDiv 2 r
  if h = 0 then
    node r nil nil
  else
    node r (ctf (r - 2 ^ (h - 1))) (ctf (r + 2 ^ (h - 1)))
termination_by Nat.maxPowDiv 2 r
decreasing_by sorry; sorry -- why do I need two of them?

def tree4 : SplayTree Nat := ctf 4
#eval! tree4
#eval! find tree4 4 -- root
#eval! find tree4 2 -- zig
#eval! find tree4 1 -- ziz-zig
#eval! find tree4 3 -- zig-zag

def tree16 : SplayTree Nat := ctf (16 : Nat)
#eval! tree16
#eval! tree16.find 8
#eval! tree16.find 4
#eval! tree16.find 12 -- zig-zag
#eval! tree16.find 2 -- ziz-zig then zig
#eval! tree16.find 6 -- ziz-zag then zig
#eval! tree16.find 1 -- ziz-zig then zig-zig
#eval! tree16.find 3 -- ziz-zag then zig-zig
#eval! tree16.find 15 -- ziz-zig then zig-zag
#eval! tree16.find 19 -- ziz-zag then zig-zag

#eval! node 8 (ctf 4) (node 16 (ctf 12) (ctf 24))
#eval! tree16.find 8 = node 8 (ctf 4) (node 16 (ctf 12) (ctf 24))
#guard tree16.find 8 = node 8 (ctf 4) (node 16 (ctf 12) (ctf 24))
#guard tree16.find 4 = node 4 (ctf 2) (node 8 (ctf 6) (node 16 (ctf 12) (ctf 24)))
#guard tree16.find 12 = node 12 (node 8 (ctf 4) (ctf 10)) (node 16 (ctf 14) (ctf 24))
#guard tree16.find 2 = node 2 (ctf 1) (node 16 (node 4 (ctf 3) (node 8 (ctf 6) (ctf 12))) (ctf 24))
#guard tree16.find 2 = node 2 (ctf 1) (node 16 (node 4 (ctf 3) (node 8 (ctf 6) (ctf 12))) (ctf 24))
#guard tree16.find 6 = node 6 (node 4 (ctf 2) (ctf 5)) (node 16 (node 8 (ctf 7) (ctf 12)) (ctf 24))
#guard tree16.find 1 = node 1 nil (node 8 (node 2 nil (node 4 (ctf 3) (ctf 6))) (node 16 (ctf 12) (ctf 24)))
#guard tree16.find 3 = node 3 (node 2 (ctf 1) nil) (node 8 (node 4 nil (ctf 6)) (node 16 (ctf 12) (ctf 24)))
#guard tree16.find 15 = node 15 (node 8 (ctf 4) (node 14 (node 12 (ctf 10) (ctf 13)) nil)) (node 16 nil (ctf 24))
#guard tree16.find 19 = node 19 (node 16 (ctf 8) (node 18 (ctf 17) nil)) (node 24 (node 20 nil (ctf 22)) (ctf 28))

end demo
