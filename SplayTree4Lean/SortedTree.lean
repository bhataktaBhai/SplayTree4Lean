import SortedTree4Lean.SplayMap

universe u
variable {α : Type u} [LinearOrder α]

/-! A formal implementation of Splay trees. These are implemented using dynamic self-balancing search trees, modified mainly by a `splay` operation, attributed to Sleator and Tardos (https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf).

API offered by this module:
- `SortedTree α β` is a splay tree with `key`s of type `α` with a `LinearOrder` instance, and `value`s of type `β`.
- `SortedMap.nil` is the empty tree.
- `search` is a function that takes a `SortedMap α β` and a key `x : α`, and returns the tree with `x` splayed to the root. Even if `x` is not in the tree, the output tree may still be modified.
- `insert` is a function that takes a `SortedMap α β`, a key `xk : α`, a value `xv : β`, and returns the tree with `(xk, xv)` inserted. If `xk` is already in the tree, the value is updated.
- `delete` is a function that takes a `SortedMap α β` and a key `x : α`, and returns the tree with `x` deleted. If `x` is not in the input tree, the output tree may still be modified.
 -/

def SortedTree (α : Type u) := SplayMap α Unit

instance [DecidableEq α] : DecidableEq (SortedTree α) :=
  inferInstanceAs (DecidableEq (SplayMap α Unit))

namespace SortedTree

def nil : SortedTree α :=
  SplayMap.nil
def node (xk : α) : SortedTree α → SortedTree α → SortedTree α :=
  SplayMap.node xk .unit

def toStr [ToString α] (header : String) : SortedTree α → String
  | SplayMap.nil => header ++ "nil\n"
  | SplayMap.node yk _ yL yR => header ++ toString yk ++ "\n" ++ toStr header' yL ++ toStr header' yR
      where header' := header ++ "    "

instance [ToString α] : ToString (SortedTree α) :=
  ⟨toStr ""⟩

instance instSortedTreeMem : Membership α (SortedTree α) :=
  inferInstanceAs (Membership α (SplayMap α Unit))

#synth DecidableEq (SplayMap Nat Unit)
#synth DecidableEq (SortedTree Nat)

def insert (t : SortedTree α) (xk : α) : SortedTree α :=
  SplayMap.insert t xk Unit.unit

def delete : SortedTree α → α → SortedTree α :=
  SplayMap.delete

def fromList : List α → SortedTree α :=
  SplayMap.fromList ∘ List.map (fun x => (x, Unit.unit))

def toList : SortedTree α → List α :=
  List.map (fun (x, _) => x) ∘ SplayMap.toList

end SortedTree

section demo
open SortedTree

def exampleTree1 : SortedTree Nat :=
  -- insert 10 (insert 20 (insert 30 (insert 25 (insert 5 (insert (15 : ℕ) nil)))))
  (((((nil.insert 15).insert 5).insert 25).insert 30).insert 20).insert 10

def L : List Nat := [5, 3, 8, 1, 4, 7, 9]

def exampleTree2 : SortedTree Nat :=
  fromList L

#eval exampleTree1
#eval exampleTree2
#eval find exampleTree1 15
#eval find exampleTree1 5
#eval delete exampleTree1 5

/-! Time for some unit testing. -/

-- The subtree of the infinite complete binary tree with r at the root
def ctf (r : Nat) : SortedTree Nat :=
  let h := Nat.maxPowDiv 2 r
  if h = 0 then
    node r nil nil
  else
    node r (ctf (r - 2 ^ (h - 1))) (ctf (r + 2 ^ (h - 1)))
termination_by Nat.maxPowDiv 2 r
decreasing_by sorry; sorry -- why do I need two of them?

def tree4 : SortedTree Nat := ctf 4
#eval! tree4
#eval! find tree4 4 -- root
#eval! find tree4 2 -- zig
#eval! find tree4 1 -- ziz-zig
#eval! find tree4 3 -- zig-zag

def tree16 : SortedTree Nat := ctf (16 : Nat)
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
