import SplayTree4Lean.SortedMap

universe u
variable {α : Type u} [LinearOrder α]

def SortedSet (α : Type u) [LinearOrder α] := SortedMap α Unit

/-! A formal implementation of Splay trees. These are implemented using dynamic self-balancing search trees, modified mainly by a `splay` operation, attributed to Sleator and Tardos (https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf).

API offered by this module:
- - `SortedSet α` is a splay tree with `key`s of type `α` with a `LinearOrder` instance.
- - `SortedSet.nil` is the empty tree.
- - `toList` is a function that takes a `SortedSet α` and returns the `key`s pairs of the set in order.
- - `insert` is a function that takes a `SortedSet α` and a key `xk : α`, and returns the map with `xk` inserted. If `xk` is already in the map, does nothing.
- - `fromList` is a function that takes a list of `key`s and makes a SplaySet out of them.
- - `delete` is a function that takes a `SortedSet α` and a key `x : α`, and returns the map with `x` deleted. If `x` is not in the input set, the output set may still be modified.
 -/

instance [DecidableEq α] : DecidableEq (SortedSet α) :=
  inferInstanceAs (DecidableEq (SortedMap α Unit))

namespace SortedSet

def nil : SortedSet α :=
  SortedMap.nil
-- def node (xk : α) : SortedSet α → SortedSet α → SortedSet α :=
--   SortedMap.node xk .unit

def toStr' [ToString α] (header : String) : SplayMap α Unit → String
  | .nil => header ++ "nil\n"
  | .node yk _ yL yR => header ++ toString yk ++ "\n" ++ toStr' header' yL ++ toStr' header' yR
      where header' := header ++ "    "

def toStr [ToString α] (header : String) : SortedSet α → String
  | ⟨t, _⟩ => toStr' header t

instance [ToString α] : ToString (SortedSet α) :=
  ⟨toStr ""⟩

instance instSortedSetMem : Membership α (SortedSet α) :=
  inferInstanceAs (Membership α (SortedMap α Unit))

#synth DecidableEq (SortedMap Nat Unit)
#synth DecidableEq (SortedSet Nat)

def insert (t : SortedSet α) (xk : α) : SortedSet α :=
  SortedMap.insert t xk Unit.unit

def delete : SortedSet α → α → SortedSet α :=
  SortedMap.delete

def fromList : List α → SortedSet α :=
  SortedMap.fromList ∘ List.map (fun x => (x, Unit.unit))

def toList : SortedSet α → List α :=
  List.map (fun (x, _) => x) ∘ SortedMap.toList

end SortedSet
