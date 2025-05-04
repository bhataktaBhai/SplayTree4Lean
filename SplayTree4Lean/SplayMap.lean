import Mathlib.Order.Basic -- for LinearOrder
import Mathlib.Data.Nat.Basic -- for LinearOrder Nat
import Mathlib.Data.Nat.MaxPowDiv -- for maxPowDiv
import Mathlib.Tactic -- for Linarith
import SplayTree4Lean.lemmas -- for lemmas

universe u v
variable {α : Type u} [LinearOrder α] [DecidableEq α]
variable {β : Type v} [DecidableEq β]

inductive SplayMap (α : Type u) (β : Type v)
  | nil : SplayMap α β
  | node (key : α) (val : β) (left right : SplayMap α β) : SplayMap α β
  deriving DecidableEq

namespace SplayMap

def toStr [ToString α] [ToString β] (header : String) : SplayMap α β → String
  | nil => header ++ "nil\n"
  | node yk yv yL yR => header ++ toString (yk, yv) ++ "\n" ++ toStr header' yL ++ toStr header' yR
    where header' := header ++ "    "

instance [ToString α] [ToString β] : ToString (SplayMap α β) :=
  ⟨toStr ""⟩

@[simp]
def splayMem (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | nil => False
  | node key _ left right => x = key ∨ left.splayMem x ∨ right.splayMem x

@[simp]
instance instSplayMapMem : Membership α (SplayMap α β) :=
  ⟨splayMem⟩

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
@[simp]
lemma noMemNil : ∀ x, x ∉ (nil : SplayMap α β) := by
  intro x h; exact h

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma memNoNil : ∀ (t : SplayMap α β) x, x ∈ t → t ≠ nil := by
  intro t x a
  simp_all only [instSplayMapMem, ne_eq]
  intro a1
  simp_all

/-- Returns the (key, val) pairs of the tree in order. -/
def toList : SplayMap α β → List (α × β)
  | nil => []
  | node xk xv xL xR => toList xL ++ [(xk, xv)] ++ toList xR

/-- Returns the keys of the tree in order. -/
def keyList : SplayMap α β → List α :=
  List.map Prod.fst ∘ toList

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
theorem mem_iff_mem_list (x : α) (t : SplayMap α β): x ∈ t ↔ ∃ y : β, (x, y) ∈ t.toList := by
  induction t with
  | nil =>
    apply Iff.intro
    · intro a
      simp_all only [instSplayMapMem, splayMem]
    · simp [toList]
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

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma mem_iff_mem_key_list (x : α) (t : SplayMap α β): x ∈ t ↔ x ∈ t.keyList := by
  simp [keyList, mem_iff_mem_list]

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
theorem list_empty_iff : ∀ t : SplayMap α β, t.toList = [] ↔ t = nil
  | nil => by
    simp [toList]
  | node key _ left right => by
    simp [toList]

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma key_list_empty_iff : ∀ t : SplayMap α β, t.keyList = [] ↔ t = nil := by
  simp [keyList, list_empty_iff]

-- def max? (t : SplayMap α β) : Option α :=
--   t.keyList.max?

-- def min? (t : SplayMap α β) : Option α :=
--   t.keyList.min?

-- omit [DecidableEq α] [DecidableEq β] in
-- lemma max?_eq_none_iff : ∀ t : SplayMap α β, t.max? = none ↔ t = nil := by
--   intro t
--   apply Iff.intro <;> intro h
--   · have h_empty : t.keyList = [] := List.max?_eq_none_iff.mp h
--     exact (key_list_empty_iff t).mp h_empty
--   · simp [max?, h, key_list_empty_iff]

-- omit [DecidableEq α] [DecidableEq β] in
-- lemma min?_eq_none_iff : ∀ t : SplayMap α β, t.min? = none ↔ t = nil := by
--   intro t
--   apply Iff.intro <;> intro h
--   · have h_empty : t.keyList = [] := List.min?_eq_none_iff.mp h
--     exact (key_list_empty_iff t).mp h_empty
--   · simp [min?, h, key_list_empty_iff]

-- def max_ (t : SplayMap α β) (h : t ≠ nil) : α :=
--   match h' : t.max? with
--   | some k => k
--   | none   => by simp_all only [max?_eq_none_iff]

-- theorem max_mem (t : SplayMap α β) (h : t ≠ nil) :
--     (t.max h) ∈ t := by
--   match h' : t.max? with
--   | some k =>
--     simp_all!
--     split
--     · rename_i k' heq
--       rw [(List.max?_eq_some_iff' (h1 : )).mp] at heq
--       sorry
--       sorry
--     · trivial
--   | none   => simp_all only [max?_eq_none_iff]
-- #check List.max?_eq_some_iff'

-- def min_ (t : SplayMap α β) (h : t ≠ nil) : α :=
--   match h' : min? t with
--   | some k => k
--   | none   => by simp_all only [min?_eq_none_iff]

-- TODO: is the below useful?
-- inductive Forall (p : α → β → Prop) : SplayMap α β → Prop
--   | nil : Forall p .nil
--   | node yk yv yL yR :
--       p yk yv →
--       Forall p yL →
--       Forall p yR →
--     Forall p (node yk yv yL yR)

@[simp]
def Forall (p : α → Prop) (t : SplayMap α β) : Prop :=
  ∀ x ∈ t, p x

inductive Sorted : SplayMap α β → Prop
  | nil : Sorted nil
  | node yk yv yL yR :
      Forall (fun k => k < yk) yL →
      Forall (fun k => yk < k) yR →
      Sorted yL →
      Sorted yR →
    Sorted (node yk yv yL yR)

@[simp]
def key (t : SplayMap α β) (h : t ≠ nil) : α := match t with
  | node key _ _ _ => key -- how is Lean so smart?!

@[simp]
def value (t : SplayMap α β) (h : t ≠ nil) : β := match t with
  | node _ value _ _ => value

@[simp]
def left (t : SplayMap α β) (h : t ≠ nil) : SplayMap α β := match t with
  | node _ _ left _ => left

@[simp]
def right (t : SplayMap α β) (h : t ≠ nil) : SplayMap α β := match t with
  | node _ _ _ right => right

def size : SplayMap α β → Nat
  | SplayMap.nil => 0
  | SplayMap.node _ _ l r => 1 + l.size + r.size

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma size_mono_left (t : SplayMap α β) (h : t ≠ nil) : t.size > (t.left h).size :=
  match ht : t with
  | node k v l r => by
    rw [size, left]
    omega

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma size_mono_right (t : SplayMap α β) (h : t ≠ nil) : t.size > (t.right h).size :=
  match t with
  | node k v l r => by
    rw [size, right]
    omega

/-- Rotates the edge joining the supplied node and its left child, if it exists. -/
def rotateLeftChild (t : SplayMap α β) (h1 : t ≠ nil) (h2 : t.left h1 ≠ nil) : SplayMap α β :=
  match t with
  | node yk yv (node ylk ylv yLL yLR) yR =>
    node ylk ylv yLL (node yk yv yLR yR) -- how is Lean so smart?!

/-- Rotates the edge joining the supplied node and its right child, if it exists. -/
def rotateRightChild (t : SplayMap α β) (h1 : t ≠ nil) (h2 : t.right h1 ≠ nil) : SplayMap α β :=
  match t with
  | node yk yv yL (node yrk yrV yRL yRR) =>
    node yrk yrV (node yk yv yL yRL) yRR

omit [DecidableEq α] [DecidableEq β] in
@[simp]
theorem Sorted_implies_left_Sorted (t : SplayMap α β) (h : t ≠ nil) :
    Sorted t → Sorted (t.left h) := by
  intro st
  match t, st with
  | node yk yv yL yR, .node _ _ _ _ biggerL smallerR sL sR =>
    simp [left]
    exact sL

omit [DecidableEq α] [DecidableEq β] in
@[simp]
theorem Sorted_implies_right_Sorted (t : SplayMap α β) (h : t ≠ nil) :
    Sorted t → Sorted (t.right h) := by
  intro st
  match t, st with
  | node yk yv yL yR, .node _ _ _ _ biggerL smallerR sL sR =>
    simp [right]
    exact sR

def max (t : SplayMap α β) (st : Sorted t) (nt : t ≠ nil) : α :=
  if nR : t.right nt = nil then
    t.key nt
  else
    (t.right nt).max (t.Sorted_implies_right_Sorted nt st) nR
termination_by t.size
decreasing_by (exact size_mono_right t nt)

def min (t : SplayMap α β) (st : Sorted t) (nt : t ≠ nil) : α :=
  if nL : t.left nt = nil then
    t.key nt
  else
    (t.left nt).min (t.Sorted_implies_left_Sorted nt st) nL
termination_by t.size
decreasing_by (exact size_mono_left t nt)

omit [DecidableEq α] [DecidableEq β] in
theorem Sorted_implies_rotateLeft_Sorted (t : SplayMap α β) (nt : t ≠ nil) (nL : t.left nt ≠ nil) :
    Sorted t → Sorted (rotateLeftChild t nt nL) := by
  intro st
  match t, st with
  | node yk yv (node ylk ylv yLL yLR) yR, .node _ _ _ _ biggerL smallerR sL sR =>
    simp only [rotateLeftChild, nt, nL]
    have sLL : Sorted yLL := match sL with
      | .node _ _ _ _ biggerLL smallerLR sLL sLR => sLL
    have sLR : Sorted yLR := match sL with
      | .node _ _ _ _ biggerLL smallerLR sLL sLR => sLR
    simp_all!
    have snewR : Sorted (node yk yv yLR yR) :=
      .node yk yv yLR yR (by simp_all only [ne_eq, Forall, instSplayMapMem, or_true, implies_true]) smallerR sLR sR
    have ylk_bigger_yLL : Forall (fun k => k < ylk) yLL := match sL with
      | .node _ _ _ _ bigger_ylk smaller_ylk _ _ => bigger_ylk
    have ylk_smaller_yLR : Forall (fun k => ylk < k) yLR := match sL with
      | .node _ _ _ _ bigger_ylk smaller_ylk _ _ => smaller_ylk
    have ylk_smaller_yk : ylk < yk := biggerL.1
    rw [Forall] at ylk_bigger_yLL
    have ylk_smaller_right : Forall (fun k => ylk < k) (node yk yv yLR yR) := by
      intro x hx
      cases hx with
      | inl h_eq =>
        rw [h_eq]
        exact ylk_smaller_yk
      | inr hx' =>
        cases hx' with
        | inl h_in =>
          simp_all only [ne_eq, true_and, instSplayMapMem, Forall]
        | inr h_in =>
          have h_temp : ylk < yk := ylk_smaller_yk
          have h_yk_x : yk < x := smallerR x h_in
          exact lt_trans h_temp h_yk_x
    exact .node ylk ylv yLL (node yk yv yLR yR) ylk_bigger_yLL ylk_smaller_right sLL snewR

omit [DecidableEq α] [DecidableEq β] in
theorem Sorted_implies_rotateRight_Sorted (t : SplayMap α β) (nt : t ≠ nil) (nR : t.right nt ≠ nil) :
    Sorted t → Sorted (rotateRightChild t nt nR) := by
  intro st
  match t, st with
  | node yk yv yL (node yrk yrv yRL yRR), .node _ _ _ _ biggerL smallerR sL sR =>
    simp only [rotateRightChild, nt, nR]
    have sRL : Sorted yRL := match sR with
      | .node _ _ _ _ biggerRL smallerRR sRL sRR => sRL
    have sRR : Sorted yRR := match sR with
      | .node _ _ _ _ biggerRL smallerRR sRL sRR => sRR
    simp_all!
    have snewL : Sorted (node yk yv yL yRL) :=
      .node yk yv yL yRL (by simp_all) (by simp_all) sL sRL
    have yrk_smaller_yRR : Forall (fun k => yrk < k) yRR := match sR with
      | .node _ _ _ _ bigger_yrk smaller_yrk _ _ => smaller_yrk
    have yrk_bigger_yRL : Forall (fun k => k < yrk) yRL := match sR with
      | .node _ _ _ _ bigger_yrk smaller_yrk _ _ => bigger_yrk
    have yrk_bigger_yk : yk < yrk := smallerR.1
    rw [Forall] at yrk_smaller_yRR
    have yrk_bigger_left : Forall (fun k => k < yrk) (node yk yv yL yRL) := by
      intro x hx
      cases hx with
      | inl h_eq =>
        rw [h_eq]
        exact yrk_bigger_yk
      | inr hx' =>
        cases hx' with
        | inl h_in =>
          have h_temp : yk < yrk := yrk_bigger_yk
          have h_x_yk : x < yk := biggerL x h_in
          exact lt_trans h_x_yk h_temp
        | inr h_in =>
          simp_all only [ne_eq, true_and, instSplayMapMem, Forall]
    exact .node yrk yrv (node yk yv yL yRL) yRR yrk_bigger_left yrk_smaller_yRR snewL sRR

-- theorem le_max_of_mem (t : SplayMap α β) (h : t ≠ nil) (x : α) (mx : x ∈ t) :
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
in the first two levels: at the `root`, at the `left` child of the root,
or at the `right` child of the root.
The `locationOf` function defined below returns `none` if it is at none of these.
-/
inductive Location
  | root | left | right

structure Prop_Proof where
  prop : Prop
  proof : prop

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

/-- Returns the `Location` of the supplied value in the supplied tree.
Returns `none` if it is not in the first two levels of the tree. -/
def locationOf (t : SplayMap α β) (x : α) : Option Location × Prop_Proof := by
  match ht : t with
  | nil => exact (none, ⟨True, trivial⟩)
  | node yk yv yL yR =>
    if h : x = yk then
      have xr : atRoot t x := by aesop
      exact (Location.root, ⟨atRoot t x, xr⟩)
    else if x < yk then
      match yL with
      | nil => exact (none, ⟨True, trivial⟩)
      | node ylk _ _ _ =>
        if x = ylk then
          have xl : atLeft t x := by aesop
          exact (Location.left, ⟨atLeft t x, xl⟩)
        else
          exact (none, ⟨True, trivial⟩)
    else
      match yR with
      | nil => exact (none, ⟨True, trivial⟩)
      | node yrk _ _ _ =>
        if x = yrk then
          have xr : atRight t x := by aesop
          exact (Location.right, ⟨atRight t x, xr⟩)
        else exact (none, ⟨True, trivial⟩)

omit [DecidableEq β] in
lemma loc_left_implies_not_nil (t : SplayMap α β) (x : α) (loc : (t.locationOf x).1 = Location.left) : t ≠ nil := by
  match t with
  | nil => trivial
  | node yk _ yL yR =>
    simp

omit [DecidableEq β] in
lemma loc_right_implies_not_nil (t : SplayMap α β) (x : α) (loc : t.locationOf x = Location.right) : t ≠ nil := by
  match t with
  | nil => trivial
  | node yk _ yL yR =>
    simp

lemma loc_left_implies_left_not_nil (t : SplayMap α β) (x : α) (hloc : t.locationOf x = Location.left) :
    (t.left (loc_left_implies_not_nil t x hloc)) ≠ nil := by
  match t with
  | nil => trivial
  | node yk yv yL yR =>
    have id : t = node yk yv yL yR := by sorry
    match w : t.locationOf x with
    | Location.root => aesop
    | Location.left =>
      unfold locationOf at hloc
      simp_all only

    | Location.right =>
      aesop
    | none =>
      aesop



-- lemma loc_left_implies_left_not_nil (t : SplayMap α β) (x : α) (hloc : t.locationOf x = Location.left) :
--     t.left (loc_left_implies_not_nil t x hloc) ≠ nil := by
--   match t with
--   | nil => trivial
--   | node yk _ yL yR =>
--     dsimp



-- lemma root_means_root (t : SplayMap α β) (x : α) (lx : t.locationOf x = Location.root) :
--     t ≠ nil ∧

-- TODO: do we use the three above functions anywhere? should we use them in `locationOf`?

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

/- Doesn't work, needs rewriting `splay?`. -/

-- def delete (t : SplayMap α β) (x : α) (h : x ∈ t) : SplayMap α β :=
--   let t' := t.splay x h  -- First splay the node to delete to the root
--   have h' : x ∈ t' := splay_preserves_membership t x h
--   match t' with
--   | nil => absurd h' (noMemNil x)
--   | node k v l r =>
--     if x = k then
--       let (maxK, maxV) := l.max (by sorry)
--       let l' := l.splay maxK (by
--         simp [Membership.mem, splayMem]
--         apply l.max_mem (by sorry))
--       match l' with
--         | node _ _ ll lr => node maxK maxV ll r
--         | nil => nil
--       -- match l.max? with
--       -- | none => r
--       -- | some (maxK, maxV) =>
--       --     -- Splay the max of left subtree to root
--       --     let l' := l.splay maxK (by
--       --       simp [Membership.mem, splayMem]
--       --       exact l.max_mem (by sorry))
--       --     match l' with
--       --     | node _ _ ll lr => node maxK maxV ll r
--       --     | nil => nil
--     else
--       -- Prove contradiction
--       sorry

/- Builds a `SplayMap` from a `List` by inserting its elements one-by-one. -/
-- def fromList (L : List (α × β)) : SplayMap α β :=
--   L.foldl (fun t (xk, xv) => t.insert xk xv) nil

omit [DecidableEq α] [DecidableEq β] in
lemma mem_lt_key_implies_mem_left (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) :
    x < t.key (t.memNoNil x mx) → x ∈ t.left (t.memNoNil x mx) := by
  match t with
  | nil => trivial
  | node yk yv yL yR  =>
      intro xlt
      simp_all only [instSplayMapMem, splayMem]
      cases mx with
      | inl h_eq => simp_all!
      | inr mx' =>
        cases mx' with
        | inl mx'' =>
          simp_all only [left]
        | inr mx'' =>
          dsimp at *
          have h_new : Forall (fun k => yk < k) yR := match st with
            | .node _ _ _ _ biggerL smallerR sL sR => smallerR
          rw [Forall] at h_new
          have nmx'' : ¬ x ∈ yR := by
            intro mxR
            have xgt : yk < x := h_new x mxR
            exact lt_gt_false x yk xlt xgt
          simp_all

omit [DecidableEq α] [DecidableEq β] in
lemma mem_gt_key_implies_mem_right (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) :
    t.key (t.memNoNil x mx) < x → x ∈ t.right (t.memNoNil x mx) := by
  match t with
  | node yk yv yL yR  =>
      intro xgt
      simp_all only [instSplayMapMem, splayMem]
      cases mx with
      | inl h_eq => simp_all!
      | inr mx' =>
        cases mx' with
        | inr mx'' =>
          simp_all only [right]
        | inl mx'' =>
          dsimp at *
          have h_new : Forall (fun k => k < yk) yL := match st with
            | .node _ _ _ _ biggerL smallerR sL sR => biggerL
          rw [Forall] at h_new
          have nmx'' : ¬ x ∈ yL := by
            intro mxL
            have xlt : x < yk := h_new x mxL
            exact lt_gt_false x yk xlt xgt
          simp_all

/--
Looks for a value `x` in a `SplayMap`.
If found, splays the tree at that node, executing zig-zig and zig-zag steps
but *not* a zig step.
That is, if `x` ends up as a child of the root, a final rotation to bring it to
the root is *not* performed.
This is necessary for recursion to work in the `splay` function.
-/
def splayButOne (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) : SplayMap α β :=
  match t with
  | node yk yv yL yR =>
      if x = yk then
        t
      else if h : x < yk then
        let yL' := yL.splayButOne ((node yk yv yL yR).Sorted_implies_left_Sorted (by simp) st) x (mem_lt_key_implies_mem_left (node yk yv yL yR) st x mx h)
        match yL'.locationOf x with
        | Location.root => node yk yv yL' yR
        | Location.left =>
          have : yL' ≠ nil := by sorry
          let t' := (node yk yv yL' yR).rotateLeftChild (by simp) (sorry)
          t'.rotateLeftChild (sorry) (sorry)
        | Location.right =>
          let yL'' := yL'.rotateRightChild (sorry) (sorry)
          (node yk yv yL'' yR).rotateLeftChild (sorry) (sorry)
        | none => sorry
      else
        let yR' := yR.splayButOne ((node yk yv yL yR).Sorted_implies_right_Sorted (by simp) st) x (sorry)
        match yR'.locationOf x with
        | Location.root => node yk yv yL yR'
        | Location.right =>
          have : yR' ≠ nil := by sorry
          let t' := (node yk yv yL yR').rotateRightChild (by simp) (sorry)
          t'.rotateRightChild (sorry) (sorry)
        | Location.left =>
          let yR'' := yR'.rotateLeftChild (sorry) (sorry)
          (node yk yv yL yR'').rotateRightChild (sorry) (sorry)
        | none => sorry

theorem splayButOne_location (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) :
    (t.splayButOne st x mx).locationOf x ≠ none := by sorry

theorem splayButOne_sorted (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) :
    Sorted (t.splayButOne st x mx) := by
  induction t with
  | nil => contradiction
  | node yk yv yL yR iL iR =>
    if x = yk then
      simp_all [splayButOne]
    else if x < yk then
      -- rw [splayButOne]
      simp_all [splayButOne]
      split
      · have mxL : x ∈ yL := sorry
        simp_all! [splayButOne]
      · sorry
      · sorry
      · sorry
    else
      sorry

def splay (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) : SplayMap α β :=
  let t' := t.splayButOne st x mx
  match lx : t'.locationOf x with
  | Location.root => t'
  | Location.left => t'.rotateLeftChild (sorry) (sorry)
  | Location.right => t'.rotateRightChild (sorry) (sorry)
  | none => by
    have : t'.locationOf x ≠ none := splayButOne_location t st x mx
    contradiction

theorem splay_preserves_membership (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) : x ∈ t.splay x mx := by
  sorry

def split (t : SplayMap α β) (st : Sorted t) (x : α) (h : x ∈ t) : SplayMap α β × SplayMap α β :=
  let t' := t.splay st x h
  have h' : x ∈ t' := splay_preserves_membership t st x h
  match t' with
  | nil => by contradiction
  | node yk yv yL yR =>
      if x ≤ yk then (yL, node yk yv nil yR)
      else (node yk yv yL nil, yR)

/- Joins two splay trees where all keys in A are less than all keys in B -/
def join (A B : SplayMap α β) (sA : Sorted A) (sB : Sorted B) : SplayMap α β :=
  match hA : A, hB : B with
  | nil, _ => B
  | _, nil => A
  | A, B =>
      -- Find and splay the max element in A
      let maxK := A.max (by sorry)
      let A' := A.splay sA maxK (A.max_mem (sorry))
      -- Now max element is at root of A'
      match A' with
      | node k v L _ => node k v L B
      | nil => sorry

def last_to (t : SplayMap α β) (nt : t ≠ nil) (x : α) : α :=
  match ht : t with
  | nil => by contradiction
  | node yk yv yL yR =>
    if x = yk then
      yk
    else if x < yk then
      if nyL : yL = .nil then
        yk
      else
        have : yL.size < t.size := by
          simp_all [SplayMap.size]; omega
        last_to yL nyL x
    else
      if nyR : yR = .nil then
        yk
      else
        have : yR.size < t.size := by
          simp_all [SplayMap.size]
        last_to yR nyR x

theorem last_to_mem (t : SplayMap α β) (nt : t ≠ nil) (x : α) : t.last_to nt x ∈ t := by
  induction t with
  | nil => contradiction
  | node yk yv yL yR iL iR =>
    if x = yk then
      simp_all [last_to]
    else if x < yk then
      if nyL : yL = .nil then
        simp_all [last_to]
      else
        simp_all [last_to]
    else
      if nyR : yR = .nil then
        simp_all [last_to]
      else
        simp_all [last_to]
        aesop

theorem last_to_eq_if_mem (t : SplayMap α β) (st : Sorted t) (nt : t ≠ nil) (x : α) (mx : x ∈ t) :
    t.last_to nt x = x := by
  sorry

def search (t : SplayMap α β) (x : α) : SplayMap α β :=
  sorry

def insert (t : SplayMap α β) (xk : α) (xv : β) : SplayMap α β :=
  let t' := t.search xk
  match t' with
  | nil => nil
  | node k v L R =>
    if xk = k then
      node k xv L R
    else
      sorry

end SplayMap
