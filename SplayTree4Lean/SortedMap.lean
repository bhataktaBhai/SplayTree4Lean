import SplayTree4Lean.SplayMap

universe u v
variable {α : Type u} [LinearOrder α] [DecidableEq α]
variable {β : Type v} [DecidableEq β]

def SortedMap (α : Type u) (β : Type v) [LinearOrder α] :=
  { t : SplayMap α β // SplayMap.is_sorted t }

instance [DecidableEq (SplayMap α β)]: DecidableEq (SortedMap α β) :=
  fun s t => if h : s.val = t.val then isTrue (Subtype.eq h) else isFalse (fun p => by cases p; contradiction)

namespace SortedMap
open SplayMap

def nil : SortedMap α β :=
  ⟨SplayMap.nil, trivial⟩

omit [DecidableEq α] [DecidableEq β] in
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
  ⟨t.val.left h', sorted_implies_left_sorted t.val h' t.prop⟩
    where h' : t.val ≠ .nil := by simp [h]

def right (t : SortedMap α β) (h : t ≠ nil) : SortedMap α β :=
  ⟨t.val.right h', sorted_implies_right_sorted t.val h' t.prop⟩
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

theorem plus_one (n : ℕ) : n + 1 > n := by
  induction n with
  | zero => trivial
  | succ n => simp

def rotateLeftChild (t : SortedMap α β) (h1 : t ≠ nil) (h2 : t.left h1 ≠ nil) : SortedMap α β :=
  -- let t' := match t.val with
  -- | node yk yv (node ylk ylv yLL yLR) yR =>
  --   node ylk ylv yLL (node yk yv yLR yR) -- how is Lean so smart?!
  -- | node yk yv .nil yR => sorry
  -- | .nil => sorry
  have ht : t.val ≠ .nil := by simp [h1]
  have htl : t.val.left ht ≠ .nil := by sorry
  let t' := SplayMap.rotateLeftChild t.val ht htl
  have h' : (SplayMap.rotateLeftChild t.val ht htl).is_sorted := by
    induction t.val with
    | nil => 
      have hh : t.val = .nil := by simp_all!
      sorry
    | node yk yv yL yR ihL ihR => sorry
    match h : t.val with
    | .nil =>
      contradiction
    | node yk yv .nil yR =>
      have htl' : t.val.left ht = .nil := by simp_all! only
      contradiction
    | node yk yv (node ylk ylv yLL yLR) yR =>
      simp_all [SplayMap.rotateLeftChild, t', ht]
      match t.val, ht, htl with
      | node yk yv (node ylk ylv yLL yLR) yR, h1, h2 =>
        simp only
      -- unfold SplayMap.is_sorted
      match t' with
      | .nil => trivial
      | node _ _ l r => simp only
      have hl : (t.1.left h).is_sorted := sorted_implies_left_sorted t.1 h t.2
      have htl : t.1.left h = l := by
        simp [ht]
        rw [SplayMap.left]
      have hl' : l.is_sorted := by simp_all
      have hr : (t.1.right h).is_sorted := sorted_implies_right_sorted t.1 h t.2
      have htr : t.1.right h = r := by
        simp [ht]
        rw [SplayMap.right]
      have hr' : r.is_sorted := by simp_all

      -- unfold SplayMap.is_sorted
      -- match t' with
      -- | .nil => trivial
      -- | .node _ _ _ _ =>
      -- exact h''
  ⟨t', h'⟩

def rotateRightChild (t : SortedMap α β) (h1 : t.val ≠ SplayMap.nil) (h2 : (t.val).right h1 ≠ SplayMap.nil) : SortedMap α β :=
  let t' := (t.val).rotateRightChild h1 h2
  have h' : t'.is_sorted := by sorry
  ⟨t', h'⟩

/--
Looks for a value `x` in a `SplayMap`.
If found, splays the tree at that node, executing zig-zig and zig-zag steps
but *not* a zig step.
That is, if `x` ends up as a child of the root, a final rotation to bring it to
the root is *not* performed.
This is necessary for recursion to work in the `splay` function.
-/
def splayButOne (t : SortedMap α β) (x : α) : SortedMap α β :=
  match t.val with
  | .nil => nil
  | .node yk yv yL yR =>
      if x = yk then
        t
      else if x < yk then
        let yL' := yL.splayButOne x
        match yL'.locationOf x with
        | Location.root => ⟨.node yk yv yL' yR, sorry⟩
        | Location.left =>
          match (node yk yv yL' yR).rotateLeftChild (sorry) with
          | t1 =>
            match rotateLeftChild t1 with
            | some t2 => t2
            | none => t1
          | none => node yk yv yL' yR
        | Location.right =>
          match rotateRightChild yL' with
          | some newYl =>
            match rotateLeftChild (node yk yv newYl yR) with
            | some t' => t'
            | none => node yk yv newYl yR
          | none => node yk yv yL' yR
        | none => sorry
      else
        let yR' := yR.splayButOne x
        match yR'.locationOf x with
        | Location.root => node yk yv yL yR'
        | Location.right =>
          match rotateRightChild (node yk yv yL yR') with
          | some t1 =>
            match rotateRightChild t1 with
            | some t2 => t2
            | none => t1
          | none => node yk yv yL yR'
        | Location.left =>
          match rotateLeftChild yR' with
          | some newYr =>
            match rotateRightChild (node yk yv yL newYr) with
            | some t' => t'
            | none => node yk yv yL newYr
          | none => node yk yv yL yR'

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

end SortedMap

def five? : Option Nat := Option.some 5
#check five?

#eval five?.get!
#eval (2, 3).1

