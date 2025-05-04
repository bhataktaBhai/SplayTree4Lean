import SplayTree4Lean.SplayMap

universe u v
variable {α : Type u} [LinearOrder α] [DecidableEq α]
variable {β : Type v} [DecidableEq β]

def SortedMap (α : Type u) (β : Type v) [LinearOrder α] :=
  { t : SplayMap α β // SplayMap.Sorted t }

instance [DecidableEq (SplayMap α β)]: DecidableEq (SortedMap α β) :=
  fun s t => if h : s.val = t.val then isTrue (Subtype.eq h) else isFalse (fun p => by cases p; contradiction)

namespace SortedMap
open SplayMap

def nil : SortedMap α β :=
  ⟨.nil, .nil⟩

instance instSortedMapMem : Membership α (SortedMap α β) :=
  ⟨fun t x => x ∈ t.val⟩

omit [DecidableEq α] [DecidableEq β] in
@[simp]
theorem sorted_nil_iff (t : SortedMap α β) : t = nil ↔ t.val = .nil := by
  apply Iff.intro <;> intro h
  · subst h
    rfl
  · apply Subtype.eq
    assumption

omit [DecidableEq α] [DecidableEq β] in
@[simp]
theorem sorted_not_nil_implies (t : SortedMap α β) : t ≠ nil → t.val ≠ .nil := by
  simp [sorted_nil_iff]

def key (t : SortedMap α β) (h : t ≠ .nil) : α :=
  t.val.key (by simp [h])

def value (t : SortedMap α β) (h : t ≠ nil) : β :=
  t.val.value (by simp [h])

def left (t : SortedMap α β) (h : t ≠ nil) : SortedMap α β :=
  ⟨t.val.left h', Sorted_implies_left_Sorted t.val h' t.prop⟩
    where h' : t.val ≠ .nil := by simp [h]

def right (t : SortedMap α β) (h : t ≠ nil) : SortedMap α β :=
  ⟨t.val.right h', Sorted_implies_right_Sorted t.val h' t.prop⟩
    where h' : t.val ≠ .nil := by simp [h]

def max (t : SortedMap α β) (h : t ≠ nil) : α :=
  have h0 : t.val ≠ SplayMap.nil := by simp [h]
  if h' : t.right h = nil then
    t.val.key h0
  else
    (t.right h).max h'
termination_by t.val.size
decreasing_by (exact size_mono_right t.val h0)

def min (t : SortedMap α β) (h : t ≠ nil) : α :=
  have h0 : t.val ≠ SplayMap.nil := by simp [h]
  if h' : (t.left h) = nil then
    t.val.key h0
  else
    (t.left h).min h'
termination_by t.val.size
decreasing_by (exact size_mono_left t.val h0)

example (n : ℕ) : n + 1 > n := by
  induction n with
  | zero => trivial
  | succ n => simp

def rotateLeftChild (t : SortedMap α β) (nt : t ≠ nil) (nL : t.left nt ≠ nil) : SortedMap α β :=
  have nt' : t.val ≠ SplayMap.nil := by simp [nt]
  have nL' : (t.val).left nt' ≠ SplayMap.nil := by
    have nL'a : (t.left nt) ≠ nil := by simp [nL]
    have nL'b : (t.val).left nt' = (t.left nt).val := by
      simp_all only [ne_eq, not_false_eq_true]
      rfl
    simp only [nL'a, nL'b, ne_eq, not_false_eq_true, sorted_not_nil_implies]
  let t' := (t.val).rotateLeftChild nt' nL'
  have h' : t'.Sorted := t.val.Sorted_implies_rotateLeft_Sorted nt' nL' t.prop
  ⟨t', h'⟩

def rotateRightChild (t : SortedMap α β) (nt : t ≠ nil) (nR : t.right nt ≠ nil) : SortedMap α β :=
  have nt' : t.val ≠ SplayMap.nil := by simp [nt]
  have nR' : (t.val).right nt' ≠ SplayMap.nil := by
    have nR'a : (t.right nt) ≠ nil := by simp [nR]
    have nR'b : (t.val).right nt' = (t.right nt).val := by
      simp_all only [ne_eq, not_false_eq_true]
      rfl
    simp only [nR'a, nR'b, ne_eq, not_false_eq_true, sorted_not_nil_implies]
  let t' := (t.val).rotateRightChild nt' nR'
  have h' : t'.Sorted := sorry --t.val.Sorted_implies_rotateRight_Sorted nt' nR' t.prop
  ⟨t', h'⟩

-- theorem splayButOneMemberLocation (t : SplayMap α β) (x : α) (h : x ∈ t) :
--     (t.splayButOne x).locationOf x ≠ .idk := by
--   cases t with
--   | nil =>
--       absurd h
--       exact noMemNil x
--   | node yk yv yL yR =>
--       if h₁ : x = yk then
--         subst h₁
--         have h' : (node x yv yL yR).locationOf x = .root := by
--           simp_all!
--         intro h''
--         have p : Location.root ≠ Location.idk := by
--           intro q
--           trivial
--         simp_all!
--       else if x < yk then
--         sorry
--       else
--         sorry

/-
Looks for a value `x` in a `SplayMap`.
If found, splays the tree at that node.
-/
def splay (t : SplayMap α β) (x : α) (h : x ∈ t) : SplayMap α β :=
  let t' := t.splayButOne x
  let loc := t'.locationOf x
  have h' : loc ≠ .idk := splayButOneMemberLocation t x h
  match loc with
  | .root => t
  | .left => rotateLeftChild t
  | .right => rotateRightChild t
  | .idk => by trivial

def last_to? (t : SortedMap α β) (x : α) : Option α :=
  match ht : t with
  | ⟨.nil, _⟩ => none
  | ⟨node yk yv yL yR, p⟩ =>
    some (last_to ⟨node yk yv yL yR, p⟩ (by simp_all) x)

def search (t : SortedMap α β) (x : α) : SortedMap α β :=
  match ht : t with
  | nil => nil
  | _ => t.splay x (x ∈ t)

end SortedMap

def five? : Option Nat := Option.some 5
#check five?

#eval five?.get!
#eval (2, 3).1
