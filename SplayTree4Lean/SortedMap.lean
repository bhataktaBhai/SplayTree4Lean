import SplayTree4Lean.SplayMap

universe u v
variable {α : Type u} [LinearOrder α] [DecidableEq α]
variable {β : Type v} [DecidableEq β]

/-! A formal implementation of Splay maps. These are implemented using dynamic self-balancing search trees, modified mainly by a `splay` operation, attributed to Sleator and Tardos (https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf).

API offered by this module:
- - `SortedMap α β` is a splay map with `key`s of type `α` with a `LinearOrder` instance, and `value`s of type `β`.
- - `SortedMap.nil` is the empty tree.
- - `get` is a function that takes a `SortedMap α β` and a key `x : α`, and returns the map with `x` splayed to the root along with the value corresponding to `x`. Even if `x` is not in the map, the output map may still be modified.
- - `insert` is a function that takes a `SortedMap α β`, a key `xk : α`, a value `xv : β`, and returns the map with `(xk, xv)` inserted. If `xk` is already in the map, the value is updated.
- - `fromList` is a function that takes a list of `(key, val)` pairs and makes a SplayMap out of them.
- - `delete` is a function that takes a `SortedMap α β` and a key `x : α`, and returns the map with `x` deleted. If `x` is not in the input map, the output map may still be modified.
 -/

def SortedMap (α : Type u) (β : Type v) [LinearOrder α] :=
  { t : SplayMap α β // SplayMap.Sorted t }

instance [DecidableEq (SplayMap α β)]: DecidableEq (SortedMap α β) :=
  fun s t => if h : s.val = t.val then isTrue (Subtype.eq h) else isFalse (fun p => by cases p; contradiction)

namespace SortedMap
open SplayMap

def nil : SortedMap α β :=
  ⟨.nil, .nil⟩

instance instSortedMapInhabited : Inhabited (SortedMap α β) :=
  ⟨nil⟩

instance instSortedMapMem : Membership α (SortedMap α β) :=
  ⟨fun t x => x ∈ t.val⟩

omit [DecidableEq α] [DecidableEq β] in
@[simp]
lemma sorted_nil_iff (t : SortedMap α β) : t = nil ↔ t.val = .nil := by
  apply Iff.intro <;> intro h
  · subst h
    rfl
  · apply Subtype.eq
    assumption

omit [DecidableEq α] [DecidableEq β] in
@[simp]
lemma sorted_not_nil_implies (t : SortedMap α β) : t ≠ nil → t.val ≠ .nil := by
  simp [sorted_nil_iff]

def key (t : SortedMap α β) (nt : t ≠ .nil) : α :=
  t.val.key (t.sorted_not_nil_implies nt)

def value (t : SortedMap α β) (nt : t ≠ nil) : β :=
  t.val.value (t.sorted_not_nil_implies nt)

def left (t : SortedMap α β) (nt : t ≠ nil) : SortedMap α β :=
  ⟨t.val.left ntv, Sorted_implies_left_Sorted t.val ntv t.prop⟩
    where ntv : t.val ≠ .nil := t.sorted_not_nil_implies nt

def right (t : SortedMap α β) (nt : t ≠ nil) : SortedMap α β :=
  ⟨t.val.right ntv, Sorted_implies_right_Sorted t.val ntv t.prop⟩
    where ntv : t.val ≠ .nil := t.sorted_not_nil_implies nt

omit [DecidableEq α] [DecidableEq β] in
@[simp]
lemma sorted_left_not_nil_implies (t : SortedMap α β) (nt : t ≠ nil)
    : t.left nt ≠ nil → t.val.left (t.sorted_not_nil_implies nt) ≠ .nil := by
  intro nL
  simp_all [sorted_not_nil_implies, left]

omit [DecidableEq α] [DecidableEq β] in
@[simp]
lemma sorted_right_not_nil_implies (t : SortedMap α β) (nt : t ≠ nil)
    : t.right nt ≠ nil → t.val.right (t.sorted_not_nil_implies nt) ≠ .nil := by
  intro nR
  simp_all [sorted_not_nil_implies, right]

def max (t : SortedMap α β) (nt : t ≠ nil) : α :=
  have ntv : t.val ≠ SplayMap.nil := t.sorted_not_nil_implies nt
  if h' : t.right nt = nil then
    t.val.key ntv
  else
    (t.right nt).max h'
termination_by t.val.size
decreasing_by (exact size_mono_right t.val ntv)

def min (t : SortedMap α β) (nt : t ≠ nil) : α :=
  have ntv : t.val ≠ SplayMap.nil := t.sorted_not_nil_implies nt
  if h' : t.left nt = nil then
    t.val.key ntv
  else
    (t.left nt).min h'
termination_by t.val.size
decreasing_by (exact size_mono_left t.val ntv)

def rotateLeftChild (t : SortedMap α β) (nt : t ≠ nil) (nL : t.left nt ≠ nil) : SortedMap α β :=
  have nt' : t.val ≠ SplayMap.nil := t.sorted_not_nil_implies nt
  have nL' : (t.val).left nt' ≠ SplayMap.nil := t.sorted_left_not_nil_implies nt nL
  let t' := (t.val).rotateLeftChild nt' nL'
  have h' := t.val.Sorted_implies_rotateLeft_Sorted nt' nL' t.prop
  ⟨t', h'⟩

def rotateRightChild (t : SortedMap α β) (nt : t ≠ nil) (nL : t.right nt ≠ nil) : SortedMap α β :=
  have nt' : t.val ≠ SplayMap.nil := t.sorted_not_nil_implies nt
  have nL' : (t.val).right nt' ≠ SplayMap.nil := t.sorted_right_not_nil_implies nt nL
  let t' := (t.val).rotateRightChild nt' nL'
  have h' := t.val.Sorted_implies_rotateRight_Sorted nt' nL' t.prop
  ⟨t', h'⟩

-- def search (t : SortedMap α β) (x : α) : SortedMap α β :=
--   match ht : t with
--   | nil => nil
--   | _ => t.splay x (x ∈ t)

def insert (t : SortedMap α β) (xk : α) (xv : β) : SortedMap α β :=
  ⟨t.val.insert t.prop xk xv, t.val.insert_preserves_sorted t.prop xk xv⟩

def fromList : List (α × β) → SortedMap α β :=
  List.foldr (fun (xk, xv) t => t.insert xk xv) nil

def delete (t : SortedMap α β) (xk : α) : SortedMap α β :=
  ⟨t.val.delete t.prop xk, t.val.delete_preserves_sorted t.prop xk⟩

def delete! (t : SortedMap α β) (xk : α) : SortedMap α β :=
  ⟨t.val.delete! t.prop xk, t.val.delete!_preserves_sorted t.prop xk⟩

def get (t : SortedMap α β) (x : α) (mx : x ∈ t) : SortedMap α β × β :=
  (⟨(t.val.get t.prop x mx).1, t.val.get_preserves_sorted t.prop x mx⟩, (t.val.get t.prop x mx).2)

end SortedMap

def five? : Option Nat := Option.some 5
#check five?

#eval five?.get!
-- #eval (none : Option (SortedMap Nat Nat)).get!
#eval (2, 3).1
