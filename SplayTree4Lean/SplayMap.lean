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

@[simp]
def splayMem (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | nil => False
  | node key _ left right => x = key ∨ left.splayMem x ∨ right.splayMem x

@[simp]
instance instSplayMapMem : Membership α (SplayMap α β) :=
  ⟨splayMem⟩

omit [LinearOrder α] in
lemma noMemNil : ∀ x, x ∉ (nil : SplayMap α β) := by
  intro x h ; exact h

/-- Returns the (key, val) pairs of the tree in order. -/
def toList : SplayMap α β → List (α × β)
  | nil => []
  | node xk xv xL xR => toList xL ++ [(xk, xv)] ++ toList xR

/-- Returns the keys of the tree in order. -/
def keyList : SplayMap α β → List α
  | nil => []
  | node xk _ xL xR => keyList xL ++ [xk] ++ keyList xR

omit [LinearOrder α] in
theorem mem_iff_mem_list (x : α) (t : SplayMap α β): x ∈ t ↔ ∃ y : β, (x, y) ∈ t.toList := by
  induction t with
  | nil =>
    apply Iff.intro
    · intro a
      simp_all only [instSplayMapMem, splayMem]
    · simp_all!
  | node yk yv yL yR ihL ihR =>
    apply Iff.intro <;> intro h
    · simp only at h
      cases h with
      | inl h' =>
        subst h'
        exact ⟨yv, by simp [toList]⟩
      | inr h' =>
        cases h' with
        | inl h'' =>
          have ⟨y, hy⟩ := ihL.mp h''
          exact ⟨y, by simp [toList]; exact Or.inl hy⟩
        | inr h'' =>
          have ⟨y, hy⟩ := ihR.mp h''
          exact ⟨y, by simp [toList]; exact Or.inr (Or.inr hy)⟩
    · simp [toList] at h
      have ⟨y, hy⟩ := h
      match hy with
      | Or.inl hL =>
        exact Or.inr (Or.inl (ihL.mpr ⟨y, hL⟩))
      | Or.inr (Or.inl hMid) =>
        left; let ⟨hMid1, hMid2⟩ := hMid; exact hMid1
      | Or.inr (Or.inr hR) =>
        exact Or.inr (Or.inr (ihR.mpr ⟨y, hR⟩))

omit [LinearOrder α] in
theorem mem_iff_mem_key_list (x : α) (t : SplayMap α β): x ∈ t ↔ x ∈ t.keyList := by
  induction t with
  | nil =>
    apply Iff.intro <;> simp_all!
  | node yk yv yL yR ihL ihR =>
    apply Iff.intro <;> intro h
    · simp only at h
      cases h with
      | inl h' => simp_all!
      | inr h' => cases h' <;> simp_all!
    · simp [keyList] at h
      cases h with
      | inl h' => simp_all!
      | inr h' =>
        cases h' with
        | inl h'' => simp_all!
        | inr h'' => simp_all!

def max? (t : SplayMap α β) : Option α :=
  t.keyList.max?

def max (t : SplayMap α β) (h : t ≠ nil) : α :=
  match max? t with
  | some k => k
  | none   => by
      cases t
      · trivial
      · rename_i key _ _ _
        exact key

def min? (t : SplayMap α β) : Option α :=
  t.keyList.min?

def min (t : SplayMap α β) (h : t ≠ nil) : α :=
  match min? t with
  | some k => k
  | none   => by
      cases t
      · trivial
      · rename_i key _ _ _
        exact key

def is_sorted : SplayMap α β → Prop
 | nil => True
 | node k _ left right =>
   (match max? left with | some m => m ≤ k | none => True) ∧
   (match min? right with | some m => k < m | none => True) ∧
   is_sorted left ∧ is_sorted right

def key (t : SplayMap α β) (h : t ≠ nil) : α :=
  match t with
  | nil => by trivial
  | node key _ _ _ => key

def val (t : SplayMap α β) (h : t ≠ nil) : β :=
  match t with
  | nil => by trivial
  | node _ value _ _ => value

def leftChild (t : SplayMap α β) (h : t ≠ nil) : SplayMap α β :=
  match t with
  | nil => by trivial
  | node _ _ left _ => left

def rightChild (t : SplayMap α β) (h : t ≠ nil) : SplayMap α β :=
  match t with
  | nil => by trivial
  | node _ _ _ right => right

/-- Rotates the edge joining the supplied node and its left child, if it exists. -/
def rotateLeftChild (t : SplayMap α β) (h1 : t ≠ nil) (h2 : t.leftChild h1 ≠ nil) : SplayMap α β :=
 (node ((t.leftChild h1).key h2) ((t.leftChild h1).val h2) ((t.leftChild h1).leftChild h2) (node (t.key h1) (t.val h1) ((t.leftChild h1).rightChild h2) (t.rightChild h1)))

/-- Rotates the edge joining the supplied node and its right child, if it exists. -/
def rotateRightChild (t : SplayMap α β) (h1 : t ≠ nil) (h2 : t.rightChild h1 ≠ nil) : SplayMap α β :=
 (node ((t.rightChild h1).key h2) ((t.rightChild h1).val h2) (node (t.key h1) (t.val h1) (t.leftChild h1) ((t.rightChild h1).leftChild h2)) ((t.rightChild h1).rightChild h2))

-- theorem le_max_of_mem (t : SplayMap α β) (h : t ≠ nil) (x : α) (hx : x ∈ t) :
--   x ≤ max t h := by
--   have h' : t.keyList ≠ [] := by
--     simp_all only [ne_eq, bne_iff_ne, mem_iff_mem_key_list, splayMem]
--     intro a
--     simp_all only [List.not_mem_nil]
--   unfold max
--   generalize hmax : max? t = o
--   cases o with
--   | none =>
--     dsimp [max?] at h'
--     have h_empty : t.keyList = [] := List.max?_eq_none_iff.mp hmax
--     contradiction
--   | some k' =>

/- I was trying...
  intro t x h
  intro h
  induction t with
  | nil => trivial
  | node yk yv yL yR =>
      if h' : x = yk then
        subst h'
        cases yL with
        | nil => trivial
        | node ylk ylv yll ylr =>
            aesop?
      else if x < yk then
        rotateLeftPreservesMem yL x h
      else
        rotateLeftPreservesMem yR x h
-/

/--
Inductive type to keep track of where a particular value is present in a tree,
in the first two levels: at the `root`, the `left` child of the root,
the `right` child of the root, or `idk` because I do not know what to name this
case.
-/
inductive Location
  | root | left | right

/-- Returns the `Location` of the supplied value in the supplied tree. -/
def locationOf (t : SplayMap α β) (x : α) : Option (Location) :=
  match t with
  | nil => none
  | node yk _ yL yR =>
    if x = yk then
      Location.root
    else if x < yk then
      match yL with
      | nil => none
      | node ylk _ _ _ =>
          if x = ylk then Location.left
          else none
    else
      match yR with
      | nil => none
      | node yrk _ _ _ =>
          if x = yrk then Location.right
          else none

def atRoot (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | node yk _ _ _ => x = yk
  | _ => False

def atLeft (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | node _ _ (node ylk _ _ _) _ => x = ylk
  | _ => False

def atRight (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | node _ _ _ (node yrk _ _ _) => x = yrk
  | _ => False

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
        let yL' := yL.splayButOne x
        match yL'.locationOf x with
        | Location.root => node yk yv yL' yR
        | Location.left =>
          match rotateLeftChild (node yk yv yL' yR) with
          | some t1 =>
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

theorem splay_preserves_membership
    (t : SplayMap α β) (x : α) (h : x ∈ t) : x ∈ splay t x h := by
  let t' := t.splayButOne x
  let loc := t'.locationOf x
  have h' : loc ≠ .idk := splayButOneMemberLocation t x h
  have mem_sbo : x ∈ t' := by sorry

  match loc with
  | .root => sorry
  | .left => sorry
  | .right => sorry
  | .idk => simp at h'


-- theorem splayMember (t : SplayMap α β) (x : α) (h : x ∈ t) :
--     (t.splay? x h).isSome := by
--   sorry

/-- Return the last non-nil (key, value) pair on the search path to `x`. -/
def search? (t : SplayMap α β) (x : α) : Option (α × β) :=
  match t with
  | nil => none
  | node yk yv yL yR =>
      if x = yk then
        (yk, yv)
      else if x < yk then
        match search? yL x with
        | none => (yk, yv)
        | some (zk, zv) => some (zk, zv)
      else
        match search? yR x with
        | none => (yk, yv)
        | some (zk, zv) => some (zk, zv)
      /- Alternative if easier to prove:
      let k :=
        if x = yk then
          some x
        else if x < yk then
          search? yL x
        else
          search? yR x
      if k matches none then yk else k
      -/

-- theorem searchMember (t : SplayMap α β) (x : α) (h : t ≠ nil) :
--   (t.search? x).isSome ∧ ((t.search? x).get!.1 ∈ t) := sorry

/-- Alias for `splay?`. -/
def get (t : SplayMap α β) (x : α) : SplayMap α β × Option β :=
  let ykv? := t.search? x
  match ykv? with
  | none => (t, none) -- TODO: prove `t` is `nil`
  | some (yk, yv) => sorry
      -- let t := t.splay? yk
      -- have t_isSome : t.isSome := sorry
      -- let t := -- TODO: prove this is safe
      -- have yk_mem : yk ∈ t := sorry
      -- match t with
      -- | nil => (nil, none) -- TODO: prove this does not happen
      -- | node yk' yv' _ _ =>
      --     if yk' = yk then (t, some yv')
      --     else (t, none)
  -- match yk with
  -- | none => (t, none) -- means t is nil
  -- | some yk => sorry

/-- Doesn't work, needs rewriting `splay?`. -/
def split (t : SplayMap α β) (x : α) (h : x ∈ t) : SplayMap α β × SplayMap α β :=
  let t' := t.splay x h
  have h' : x ∈ t' := splay_preserves_membership t x h
  match t' with
  | nil => absurd h (by trivial)
  | node yk yv yL yR =>
      if x ≤ yk then (yL, node yk yv nil yR)
      else (node yk yv yL nil, yR)

/-- Joins two splay trees where all keys in A are less than all keys in B -/
def join (A B : SplayMap α β) : SplayMap α β :=
  match A, B with
  | nil, _ => B
  | _, nil => A
  | A, B =>
      -- Find and splay the max element in A
      let (maxK, maxV) := A.max (by sorry)
      let A' := A.splay maxK (by sorry)
      -- Now max element is at root of A'
      match A' with
      | node _ _ l _ => node maxK maxV l B
      | nil => nil

/-- Doesn't work, needs rewriting `splay?`. -/
def insert (t : SplayMap α β) (xk : α) (xv : β) : SplayMap α β :=
  match t.search? xk with
  | none =>
    let (L, R) := t.split xk (by sorry)
    node xk xv L R
  | some _ =>
    let t' := t.splay xk (by sorry)
    match t' with
    | node _ _ l r => node xk xv l r
    | nil => nil

theorem max_mem (t : SplayMap α β) (h : t ≠ nil) :
    (t.max h).1 ∈ t := by sorry

def delete (t : SplayMap α β) (x : α) (h : x ∈ t) : SplayMap α β :=
  let t' := t.splay x h  -- First splay the node to delete to the root
  have h' : x ∈ t' := splay_preserves_membership t x h
  match t' with
  | nil => absurd h' (noMemNil x)
  | node k v l r =>
    if x = k then
      let (maxK, maxV) := l.max (by sorry)
      let l' := l.splay maxK (by
        simp [Membership.mem, splayMem]
        apply l.max_mem (by sorry))
      match l' with
        | node _ _ ll lr => node maxK maxV ll r
        | nil => nil
      -- match l.max? with
      -- | none => r
      -- | some (maxK, maxV) =>
      --     -- Splay the max of left subtree to root
      --     let l' := l.splay maxK (by
      --       simp [Membership.mem, splayMem]
      --       exact l.max_mem (by sorry))
      --     match l' with
      --     | node _ _ ll lr => node maxK maxV ll r
      --     | nil => nil
    else
      -- Prove contradiction
      sorry

/-- Builds a `SplayMap` from a `List` by inserting its elements one-by-one. -/
def fromList (L : List (α × β)) : SplayMap α β :=
  L.foldl (fun t (xk, xv) => t.insert xk xv) nil

end SplayMap

def SortedMap (α : Type u) (β : Type v) [LinearOrder α] :=
  {t : SplayMap α β // SplayMap.is_sorted t}

namespace SortedMap
open SplayMap

def nil : SortedMap α β :=
  ⟨SplayMap.nil, True.intro⟩

def leftChild (t : SortedMap α β) (h : t.val ≠ SplayMap.nil) : SortedMap α β :=
  let t' := (t.val).leftChild h
  have h' : is_sorted t' := by
    let ⟨t, h⟩ := t

  ⟨t', h'⟩

def rotateLeftChild (t : SortedMap α β) (h1 : t.val ≠ SplayMap.nil) (h2 : (t.val).leftChild h1 ≠ SplayMap.nil) : SortedMap α β :=
  let t' := (t.val).rotateLeftChild h1 h2
  have h' : SplayMap.is_sorted t' := by
  ⟨t', h'⟩

def rotateRightChild (t : SortedMap α β) (h1 : t.val ≠ SplayMap.nil) (h2 : (t.val).rightChild h1 ≠ SplayMap.nil) : SortedMap α β :=
  let t' := (t.val).rotateRightChild h1 h2
  have h' : SplayMap.is_sorted t' := by sorry
⟨t', h'⟩

end SortedMap

def five? : Option Nat := Option.some 5
#check five?

#eval five?.get!
#eval (2, 3).1
