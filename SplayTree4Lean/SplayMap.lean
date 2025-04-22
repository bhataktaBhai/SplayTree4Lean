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

instance : Inhabited (SplayMap α β) :=
  ⟨nil⟩

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
  intro x
  intro h; exact h

/-- Rotates the edge joining the supplied node and its left child, if it exists. -/
def rotateLeftChild : SplayMap α β → SplayMap α β
  | node yk yv (node xk xv xL xR) yR => node xk xv xL (node yk yv xR yR)
  | t => t

/-- Rotates the edge joining the supplied node and its right child, if it exists. -/
def rotateRightChild : SplayMap α β → SplayMap α β
  | node yk yv yL (node xk xv xL xR) => node xk xv (node yk yv yL xL) xR
  | t => t

omit [LinearOrder α] in
lemma rotateLeftPreservesMem : ∀ t : SplayMap α β, ∀ x, x ∈ t → x ∈ t.rotateLeftChild := by
  intro t x h
  unfold rotateLeftChild
  split
  · simp only [splayMem, instSplayMapMem] at h
    cases h with
    | inl h1 =>
        subst h1
        simp
    | inr h1 =>
        aesop
  · exact h

omit [LinearOrder α] in
lemma rotateRightPreservesMem : ∀ t : SplayMap α β, ∀ x, x ∈ t → x ∈ t.rotateRightChild := by
  intro t x h
  unfold rotateRightChild
  aesop

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
  | root | left | right | idk

/-- Returns the `Location` of the supplied value in the supplied tree. -/
def locationOf (t : SplayMap α β) (x : α) : Location :=
  match t with
  | nil => .idk
  | node yk _ yL yR =>
    if x = yk then
      .root
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

theorem splayButOneMemberLocation (t : SplayMap α β) (x : α) (h : x ∈ t) :
    (t.splayButOne x).locationOf x ≠ .idk := by
  cases t with
  | nil =>
      absurd h
      exact noMemNil x
  | node yk yv yL yR =>
      if h₁ : x = yk then
        subst h₁
        have h' : (node x yv yL yR).locationOf x = .root := by
          simp_all! -- wtf?
        intro h''
        have p : Location.root ≠ Location.idk := by
          intro q
          trivial
        -- aesop?
        simp_all! -- ???
      else if x < yk then
        sorry
      else
        sorry

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

theorem searchMember (t : SplayMap α β) (x : α) (h : t ≠ nil) :
  (t.search? x).isSome ∧ ((t.search? x).get!.1 ∈ t) := sorry

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

/-- Doesn't work, needs rewriting `splay?`. -/
def insert (t : SplayMap α β) (xk : α) (xv : β) : SplayMap α β :=
  let (L, R) := t.split xk
  node xk xv L R

def delete (t : SplayMap α β) (x : α) (h : x ∈ t) : SplayMap α β :=
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

def five? : Option Nat := Option.some 5
#check five?

#eval five?.get!
#eval (2, 3).1
