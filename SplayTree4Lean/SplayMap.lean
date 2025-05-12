import Mathlib.Order.Basic -- for LinearOrder
import Mathlib.Data.Nat.Basic -- for LinearOrder Nat
import Mathlib.Data.Nat.MaxPowDiv -- for maxPowDiv
import Mathlib.Tactic.Linarith -- for linarith
import Mathlib.Tactic.Order -- for order
import SplayTree4Lean.lemmas

universe u v
variable {α : Type u} [LinearOrder α] [DecidableEq α]
variable {β : Type v} [DecidableEq β]

/-! This module develops most of the groundwork required to implement Splay maps. Not meant for external use. -/

/-- A binary search tree (BST) map, allowing for just a right or left child to exist without the other. Not meant for the user; will be provided in a `SortedMap` wrapper. Such a map may not have its `key`s sorted.

Since the map is designed to be used as a search tree, a `LinearOrder` is imposed on the keys.
 -/
inductive SplayMap (α : Type u) (β : Type v)
  | nil : SplayMap α β
  | node (key : α) (val : β) (left right : SplayMap α β) : SplayMap α β
  deriving DecidableEq, Inhabited

namespace SplayMap

/-- Custom representation of a BST map for Lean Infoview. Best used with small maps. -/
def toString [ToString α] [ToString β] (header : String) : SplayMap α β → String
  | nil => header ++ "nil\n"
  | node yk yv yL yR => header ++ ToString.toString (yk, yv) ++ "\n" ++ toString header' yL ++ toString header' yR
    where header' := header ++ "    "

instance [ToString α] [ToString β] : ToString (SplayMap α β) :=
  ⟨toString ""⟩

/-- Membership (`∈`), implemented as a function for recursive reasons. Only the keys are said to be members for utility reasons. -/
@[simp]
def splayMem (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | nil => False
  | node key _ left right => x = key ∨ left.splayMem x ∨ right.splayMem x

@[simp]
instance instSplayMapMem : Membership α (SplayMap α β) :=
  ⟨splayMem⟩

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma no_mem_nil (x : α) : x ∉ (nil : SplayMap α β) := by
  intro h
  exact h

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma mem_no_nil {t : SplayMap α β} {x : α} (mx : x ∈ t) : t ≠ nil := by
  intro nt
  simp_all

/-- Returns the `(key, val)` pairs of the map in order. -/
def toList : SplayMap α β → List (α × β)
  | nil => []
  | node xk xv xL xR => toList xL ++ [(xk, xv)] ++ toList xR

@[simp]
def key (t : SplayMap α β) (nt : t ≠ nil) : α := match t with
  | node key _ _ _ => key -- how is Lean so smart?!

@[simp]
def value (t : SplayMap α β) (nt : t ≠ nil) : β := match t with
  | node _ value _ _ => value

@[simp]
def left (t : SplayMap α β) (nt : t ≠ nil) : SplayMap α β := match t with
  | node _ _ left _ => left

@[simp]
def right (t : SplayMap α β) (nt : t ≠ nil) : SplayMap α β := match t with
  | node _ _ _ right => right

/-- Returns the number of keys in a SplayMap. Useful for proving termination sometimes. -/
def size : SplayMap α β → Nat
  | SplayMap.nil => 0
  | SplayMap.node _ _ l r => 1 + l.size + r.size

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- The size of the left submap must be strictly less than that of the original map.-/
lemma size_mono_left {t : SplayMap α β} (nt : t ≠ nil) : t.size > (t.left nt).size :=
  match t with
  | node k v l r => by
    rw [size, left]
    omega

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- The size of the right submap must be strictly less than that of the original map.-/
lemma size_mono_right {t : SplayMap α β} (nt : t ≠ nil) : t.size > (t.right nt).size :=
  match t with
  | node k v l r => by
    rw [size, right]
    omega

/-- Returns the keys of the map in order. -/
def keyList : SplayMap α β → List α :=
  List.map Prod.fst ∘ toList

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- Proved unintentionally; only serves to prove `mem_iff_mem_key_list` now. -/
theorem mem_iff_mem_list {x : α} {t : SplayMap α β} : x ∈ t ↔ ∃ y : β, (x, y) ∈ t.toList := by
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
/-- The recursive membership and membership via the in-order list are equivalent. Mostly meant to be a sanity check. -/
lemma mem_iff_mem_key_list {x : α} {t : SplayMap α β} : x ∈ t ↔ x ∈ t.keyList := by
  simp [keyList, mem_iff_mem_list]

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma list_empty_iff : ∀ t : SplayMap α β, t.toList = [] ↔ t = nil
  | nil => by
    simp [toList]
  | node key _ left right => by
    simp [toList]

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma key_list_empty_iff : ∀ t : SplayMap α β, t.keyList = [] ↔ t = nil := by
  simp [keyList, list_empty_iff]

/-- Implements `∀` for `SplayMap`s in a rather convenient way. Motivated by other tree maps implemented in Lean. -/
@[simp]
def Forall (p : α → Prop) (t : SplayMap α β) : Prop :=
  ∀ x ∈ t, p x

/-- An inductive definition of sortedness for `SplayMap`. It enforces uniqueness of keys by virtue of demanding a strict inequalty.  -/
inductive Sorted : SplayMap α β → Prop
  | nil : Sorted nil
  | node yk yv yL yR :
      Forall (fun k => k < yk) yL →
      Forall (fun k => yk < k) yR →
      Sorted yL →
      Sorted yR →
    Sorted (node yk yv yL yR)

/-- Rotates the edge joining the supplied node and its left child, if it exists. -/
def rotateLeftChild (t : SplayMap α β) (nt : t ≠ nil) (nL : t.left nt ≠ nil) : SplayMap α β :=
  match t with
  | node yk yv (node ylk ylv yLL yLR) yR =>
    node ylk ylv yLL (node yk yv yLR yR) -- how is Lean so smart?!

/-- Rotates the edge joining the supplied node and its right child, if it exists. -/
def rotateRightChild (t : SplayMap α β) (nt : t ≠ nil) (nR : t.right nt ≠ nil) : SplayMap α β :=
  match t with
  | node yk yv yL (node yrk yrV yRL yRR) =>
    node yrk yrV (node yk yv yL yRL) yRR

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- The left rotation operator preserves the non-emptiness of a `SplayMap`. -/
lemma rotate_left_preserves_no_nil {t : SplayMap α β} (nt : t ≠ nil) (nL : t.left nt ≠ nil) :
    rotateLeftChild t nt nL ≠ nil := by
  match t with
  | node yk yv (node ylk ylv yLL yLR) yR =>
    simp_all!

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- The right rotation operator preserves the non-emptiness of a `SplayMap`. -/
lemma rotate_right_preserves_no_nil {t : SplayMap α β} (nt : t ≠ nil) (nR : t.right nt ≠ nil) :
    rotateRightChild t nt nR ≠ nil := by
  match t with
  | node yk yv yL (node yrk yrV yRL yRR) =>
    simp_all!

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `rotateLeftChild` preserves the set of members of a `SplayMap`. -/
lemma mem_rotate_left_of_mem {t : SplayMap α β} (nt : t ≠ nil) (nL : t.left nt ≠ nil) :
    ∀ x ∈ t, x ∈ rotateLeftChild t nt nL := by
  intro x mx
  match t with
  | node yk yv (node ylk ylv yLL yLR) yR =>
    rw [rotateLeftChild]
    aesop

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `rotateRigftChild` preserves the set of members of a `SplayMap`. -/
lemma mem_rotate_right_of_mem {t : SplayMap α β} (nt : t ≠ nil) (nR : t.right nt ≠ nil) :
    ∀ x ∈ t, x ∈ rotateRightChild t nt nR := by
  intro x mx
  match t with
  | node yk yv yL (node yrk yrV yRL yRR) =>
    rw [rotateRightChild]
    aesop

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma mem_of_mem_rotate_left {t : SplayMap α β} (nt : t ≠ nil) (nL : t.left nt ≠ nil) :
    ∀ x ∈ rotateLeftChild t nt nL, x ∈ t := by
  intro x mx
  match t with
  | node yk yv (node ylk ylv yLL yLR) yR =>
    rw [rotateLeftChild] at mx
    aesop

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
lemma mem_of_mem_rotate_right {t : SplayMap α β} (nt : t ≠ nil) (nR : t.right nt ≠ nil) :
    ∀ x ∈ rotateRightChild t nt nR, x ∈ t := by
  intro x mx
  match t with
  | node yk yv yL (node yrk yrV yRL yRR) =>
    rw [rotateRightChild] at mx
    aesop

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `rotateLeftChild` sends the leftmost grandchild to the left submap. -/
lemma left_rotate_left_eq_left_left {t : SplayMap α β} (nt : t ≠ nil) (nL : t.left nt ≠ nil) :
    (rotateLeftChild t nt nL).left (rotate_left_preserves_no_nil nt nL) = (t.left nt).left nL := by
  match t with
    | node yk yv (node ylk ylv yLL yLR) yR => aesop

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `rotateRightChild` sends the rightmost grandchild to the right submap. -/
lemma right_rotate_right_eq_right_right {t : SplayMap α β} (nt : t ≠ nil) (nR : t.right nt ≠ nil) :
    (rotateRightChild t nt nR).right (rotate_right_preserves_no_nil nt nR) = (t.right nt).right nR := by
  match t with
    | node yk yv yL (node yrk yrv yRL yRR) => aesop

omit [DecidableEq α] [DecidableEq β] in
/-- If a `SplayMap` is sorted, so must be its left submap. -/
@[simp]
theorem left_sorted_of_sorted {t : SplayMap α β} (nt : t ≠ nil) (st : Sorted t) :
    Sorted (t.left nt) := by
  match t, st with
  | node yk yv yL yR, .node _ _ _ _ biggerL smallerR sL sR =>
    simp [left]
    exact sL

omit [DecidableEq α] [DecidableEq β] in
/-- If a `SplayMap` is sorted, so must be its right submap. -/
@[simp]
theorem right_sorted_of_sorted {t : SplayMap α β} (nt : t ≠ nil) (st : Sorted t) :
    Sorted (t.right nt) := by
  match t, st with
  | node yk yv yL yR, .node _ _ _ _ biggerL smallerR sL sR =>
    simp [right]
    exact sR

omit [DecidableEq α] [DecidableEq β] in
/-- In a sorted map, each member to the left of the root must be strictly smaller than each member to the right of the root. -/
theorem left_lt_right_of_sorted {t : SplayMap α β} (nt : t ≠ nil) :
    Sorted t → ∀ x y, x ∈ t.left nt → y ∈ t.right nt → x < y := by
  intro st
  match t, st with
  | node k v L R, .node _ _ _ _ biggerL smallerR sL sR =>
    intro x y mx my
    have x_lt_k : x < k := biggerL x mx
    have k_lt_y : k < y := smallerR y my
    exact lt_trans x_lt_k k_lt_y

/-- Checks for non-emptiness and sortedness of the map and returns the maximum element. The sortedness is used to achieve a logarithmic time complexity. -/
def max (t : SplayMap α β) (st : Sorted t) (nt : t ≠ nil) : α :=
  if nR : t.right nt = nil then
    t.key nt
  else
    (t.right nt).max (right_sorted_of_sorted nt st) nR
termination_by t.size
decreasing_by (exact size_mono_right nt)

/-- Checks for non-emptiness and sortedness of the map and returns the minimum element. The sortedness is used to achieve a logarithmic time complexity. -/
def min (t : SplayMap α β) (st : Sorted t) (nt : t ≠ nil) : α :=
  if nL : t.left nt = nil then
    t.key nt
  else
    (t.left nt).min (left_sorted_of_sorted nt st) nL
termination_by t.size
decreasing_by (exact size_mono_left nt)

/-- The `max` function returns a member of the map. -/
theorem max_mem (t : SplayMap α β) (st : Sorted t) (nt : t ≠ nil) :
    (t.max st nt) ∈ t := by
  induction t with
  | nil => trivial
  | node yk yv yL yR ihL ihR =>
    let t : SplayMap α β := node yk yv yL yR
    by_cases h : yR = nil
    have h : yk ∈ t := by
      aesop
    · have h : t.max st nt = yk := by
        sorry
      aesop
    · have h' : t.max st nt = yR.max (right_sorted_of_sorted nt st) (by simp [h]) := by
        sorry
      have h' : yR.max (right_sorted_of_sorted (by simp_all) st) (by simp [h]) ∈ yR := by
        simp [ihR]
      aesop
  -- cases hR : t.right nt
  -- · simp_all! [max]
  --   rw [key]
  -- · sorry
#check List.max?_eq_some_iff'

omit [DecidableEq α] [DecidableEq β] in
/-- If a map is sorted, so must be its left submap. -/
theorem rotate_left_sorted_of_sorted {t : SplayMap α β} (nt : t ≠ nil) (nL : t.left nt ≠ nil) :
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
/-- If a map is sorted, so must be its right submap. -/
theorem rotate_right_sorted_of_sorted {t : SplayMap α β} (nt : t ≠ nil) (nR : t.right nt ≠ nil) :
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


def AtRoot (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | node yk _ _ _ => x = yk
  | _ => False

def AtLeft (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | node _ _ (node ylk _ _ _) _ => x = ylk
  | _ => False

def AtRight (t : SplayMap α β) (x : α) : Prop :=
  match t with
  | node _ _ _ (node yrk _ _ _) => x = yrk
  | _ => False

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `AtRoot` proves the non-emptiness of the map. -/
lemma not_nil_of_atRoot {t : SplayMap α β} {x : α} :
    AtRoot t x → t ≠ nil := by
  intro h nt
  simp_all [AtRoot]

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `AtLeft` proves the non-emptiness of the map. -/
lemma not_nil_of_atLeft {t : SplayMap α β} {x : α} :
    AtLeft t x → t ≠ nil := by
  intro h nt
  simp_all [AtLeft]

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `AtRight` proves the non-emptiness of the map. -/
lemma not_nil_of_atRight {t : SplayMap α β} {x : α} :
    AtRight t x → t ≠ nil := by
  intro h nt
  simp_all [AtRight]

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `AtLeft` proves the non-emptiness of the left submap. -/
lemma left_not_nil_of_atLeft {t : SplayMap α β} {x : α} (al : AtLeft t x) : t.left (not_nil_of_atLeft al) ≠ nil := by
  intro ntL
  match t with
  | node yk yv .nil yR =>
    unfold AtLeft at al
    simp_all
  | node yk yv (node ylk ylv yLL yLR) yR =>
    simp_all

omit [LinearOrder α] [DecidableEq α] [DecidableEq β] in
/-- `AtRight` proves the non-emptiness of the right submap. -/
lemma right_not_nil_of_atRight {t : SplayMap α β} {x : α} (ar : AtRight t x) : t.right (not_nil_of_atRight ar) ≠ nil := by
  intro ntR
  match t with
  | node yk yv yL .nil =>
    unfold AtRight at ar
    simp_all
  | node yk yv yL (node yrk yrV yRL yRR) =>
    simp_all

/--
Dependednt inductive type to keep track of where a particular value is present in a map,
in the first two levels: at the `root`, at the `left` child of the root,
at the `right` child of the root, or `none` if at none of these.
-/
inductive Location (t : SplayMap α β) (x : α)
  | root : AtRoot t x → Location t x
  | left : AtLeft t x → Location t x
  | right : AtRight t x → Location t x
  | none : Location t x

def locationOf (t : SplayMap α β) (x : α) : Location t x := by
  match ht : t with
  | nil => exact .none
  | node yk yv yL yR =>
    if h : x = yk then
      have xr : AtRoot (node yk yv yL yR) x := by aesop
      exact (.root xr)
    else if x < yk then
      match yL with
      | nil => exact .none
      | node ylk _ _ _ =>
        if x = ylk then
          rw [←ht]
          have xl : AtLeft t x := by aesop
          exact (.left xl)
        else
          exact .none
    else
      match yR with
      | nil => exact .none
      | node yrk _ _ _ =>
        if x = yrk then
          rw [←ht]
          have xr : AtRight t x := by aesop
          exact (.right xr)
        else
          exact .none

omit [DecidableEq α] [DecidableEq β] in
/-- In a sorted map, if a given `key` is smaller than the root, then it must be in the left submap. -/
lemma mem_left_of_mem_lt_key {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    x < t.key (mem_no_nil mx) → x ∈ t.left (mem_no_nil mx) := by
  match t with
  | nil => trivial
  | node yk yv yL yR  =>
      intro xlt
      simp_all only [instSplayMapMem, splayMem]
      cases mx with
      | inl h_eq => simp_all
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
/-- In a sorted map, if a given `key` is greater than the root, then it must be in the right submap. -/
lemma mem_right_of_mem_gt_key {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    t.key (mem_no_nil mx) < x → x ∈ t.right (mem_no_nil mx) := by
  match t with
  | node yk yv yL yR  =>
      intro xgt
      simp_all only [instSplayMapMem, splayMem]
      cases mx with
      | inl h_eq => simp_all
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
Looks for a value `x` in a sorted `SplayMap`. If found, splays the map at that node, executing zig-zig and zig-zag steps but *not* a zig step, i.e. it performs *pairs* of rotations to bring `x` near the root.
If `x` ends up as a child of the root, a final rotation to bring it to the root is *not* performed. This is necessary for recursion to work in the `splay` function.
-/
def splayButOne (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) : SplayMap α β :=
  match t with
  | node yk yv yL yR =>
    if h0 : x = yk then
      t
    else if h : x < yk then
      have sL : Sorted yL := left_sorted_of_sorted (by simp) st
      have mxL : x ∈ yL := mem_left_of_mem_lt_key st mx (by simp_all)
      let yL' := yL.splayButOne sL x mxL
      match hyL' : yL'.locationOf x with
      | .root _ => node yk yv yL' yR
      | .left p =>
        have nyL' : yL' ≠ nil := not_nil_of_atLeft p
        have nyL'L : yL'.left nyL' ≠ nil := left_not_nil_of_atLeft p
        let t' := (node yk yv yL' yR).rotateLeftChild (by simp) nyL'
        have nt' : t' ≠ nil := rotate_left_preserves_no_nil (by simp) (by simp [nyL'])
        have heq_t'L_yL'L : t'.left nt' = yL'.left nyL' :=
          left_rotate_left_eq_left_left (by simp) (by simp [nyL'])
        have nt'L : t'.left nt' ≠ nil := by simp_all
        t'.rotateLeftChild nt' nt'L
      | .right p =>
        have nyL' : yL' ≠ nil := not_nil_of_atRight p
        have nyL'R : yL'.right nyL' ≠ nil := right_not_nil_of_atRight p
        let yL'' := yL'.rotateRightChild nyL' nyL'R
        have : yL'' ≠ nil := rotate_right_preserves_no_nil nyL' nyL'R
        (node yk yv yL'' yR).rotateLeftChild (by simp) (by simp_all)
      | .none => sorry
    else
      have sR : Sorted yR := right_sorted_of_sorted (by simp) st
      have mxL : x ∈ yR := mem_right_of_mem_gt_key st mx (by simp_all)
      let yR' := yR.splayButOne sR x mxL
      match hyR' : yR'.locationOf x with
      | .root _ => node yk yv yL yR'
      | .left p =>
        have nyR' : yR' ≠ nil := not_nil_of_atLeft p
        have nyR'L : yR'.left nyR' ≠ nil := left_not_nil_of_atLeft p
        let yR'' := yR'.rotateLeftChild nyR' nyR'L
        have nR'' : yR'' ≠ nil := rotate_left_preserves_no_nil nyR' nyR'L
        (node yk yv yL yR'').rotateRightChild (by simp) (by simp_all)
      | .right p =>
        have nyR' : yR' ≠ nil := not_nil_of_atRight p
        have nyR'R : yR'.right nyR' ≠ nil := right_not_nil_of_atRight p
        let t' := (node yk yv yL yR').rotateRightChild (by simp) nyR'
        have nt' : t' ≠ nil := rotate_right_preserves_no_nil (by simp) (by simp [nyR'])
        have heq_t'R_yR'R : t'.right nt' = yR'.right nyR' :=
          right_rotate_right_eq_right_right (by simp) (by simp [nyR'])
        have nt'R : t'.right nt' ≠ nil := by simp_all
        t'.rotateRightChild nt' nt'R
      | .none => sorry

/-- `splayButOne` when called at the root leaves the tree unchanged. -/
lemma splayButOne_root_id {t : SplayMap α β} (st : Sorted t) (nt : t ≠ nil) :
    t.splayButOne st (t.key nt) (by aesop) = t := by
  match t with
  | nil => trivial
  | node yk yv yL yR =>
    have h1 : (node yk yv yL yR).key (sorry) = yk := by -- TODO: this sorry is fine?
      simp_all only [key]
    rw [splayButOne]
    simp_all

/-- `splayButOne` never encounters the `none` case of `locationOf`. -/
theorem splayButOne_location {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    (t.splayButOne st x mx).locationOf x ≠ .none := by
  induction t with
  | nil => trivial
  | node yk yv yL yR iL iR =>
    if h0 : x = yk then
      induction h0
      simp only [ne_eq, splayButOne, dite_true, dite_eq_ite, ite_false, ite_true]
      intro p
      sorry
    else
      sorry

/-- For any `SplayMap`, its set of members is preserved upon applying `splayButOne`. -/
theorem mem_iff_mem_splayButOne {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    ∀ y, y ∈ t ↔ y ∈ t.splayButOne st x mx := by
  induction t with
  | nil =>
      intro y
      apply Iff.intro
      · trivial
      · trivial
  | node yk yv yL yR ihL ihR =>
    intro y
    have sL : Sorted yL := left_sorted_of_sorted (by simp) st
    have sR : Sorted yR := right_sorted_of_sorted (by simp) st
    if h0 : x = yk then
      apply Iff.intro <;> (intro my; simp_all [splayButOne])
    else if h : x < yk then
      have mxL : x ∈ yL := mem_left_of_mem_lt_key st mx (by simp_all)
      apply Iff.intro <;> intro my
      · simp only [instSplayMapMem, splayMem] at my
        simp only [h0, h, instSplayMapMem, splayButOne, dite_true, dite_eq_ite, ite_false]
        split
        · simp_all
        · repeat apply mem_rotate_left_of_mem
          simp_all
        · apply mem_rotate_left_of_mem
          simp
          apply Or.elim3 my <;> intro h
          · simp [h]
          · apply Or.inr
            apply Or.inl
            apply mem_rotate_right_of_mem
            simp_all
          · simp_all
        · sorry
      · simp only [instSplayMapMem, splayMem, splayButOne] at my
        simp only [h0, h, instSplayMapMem, splayButOne, dite_true, dite_eq_ite, ite_false] at my
        split at my
        · simp_all
        · have my' : y ∈ node yk yv (yL.splayButOne sL x mxL) yR := by
            have nL' : yL.splayButOne sL x mxL ≠ nil := by
              have mxL' : x ∈ yL.splayButOne sL x mxL := (ihL sL mxL x).mp mxL
              exact mem_no_nil mxL'
            apply mem_of_mem_rotate_left (by simp) (by simp [nL'])
            have nL'L : (yL.splayButOne sL x mxL).left nL' ≠ nil := by
              rename_i p _
              exact left_not_nil_of_atLeft p
            have nL'' : ((node yk yv (yL.splayButOne sL x mxL) yR).rotateLeftChild (by simp) (by simp [nL'])).left (by simp [rotate_left_preserves_no_nil, nL']) ≠ nil := by
              have := (node yk yv (yL.splayButOne sL x mxL) yR).left_rotate_left_eq_left_left
                      (by simp) (by simp [nL'])
              simp_all [left_rotate_left_eq_left_left]
            apply mem_of_mem_rotate_left
                  (by simp [rotate_left_preserves_no_nil])
                  nL''
            exact my
          simp_all
        · sorry
        · sorry
    else
      have mxR : x ∈ yR := mem_right_of_mem_gt_key st mx (by simp_all)
      apply Iff.intro <;> intro my
      · simp only [instSplayMapMem, splayMem] at my
        simp only [h0, h, instSplayMapMem, splayButOne, dite_eq_ite, ite_false, dite_false]
        split
        · simp_all
        · apply mem_rotate_right_of_mem
          simp
          apply Or.elim3 my <;> intro h
          · simp [h]
          · simp_all
          · apply Or.inr
            apply Or.inr
            apply mem_rotate_left_of_mem
            simp_all
        · repeat apply mem_rotate_right_of_mem
          simp_all
        · sorry
      · sorry

omit [DecidableEq α] [DecidableEq β] in
/-- Decomposes the `Sorted`ness condition into its constituents for easier use. -/
theorem sorted_unfold (yk : α) (yv : β) (yL yR : SplayMap α β) :
    Forall (fun k => k < yk) yL → Forall (fun k => yk < k) yR → Sorted yL → Sorted yR →
    Sorted (node yk yv yL yR) := by
  intro h1 h2 sL sR
  exact Sorted.node yk yv yL yR h1 h2 sL sR

/-- The output of `splayButOne` is a sorted `SplayMap`. -/
theorem sorted_splayButOne {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    Sorted (t.splayButOne st x mx) := by
  induction t with
  | nil => contradiction
  | node yk yv yL yR iL iR =>
    have nt : node yk yv yL yR ≠ nil := by simp only [ne_eq, reduceCtorEq, not_false_eq_true]
    if x = yk then
      simp_all [splayButOne]
    else if h : x < yk then
      rw [splayButOne]
      split
      · rename_i h_2
        subst h_2
        trivial
      · have m_x_yL : x ∈ yL := mem_left_of_mem_lt_key st mx h
        let yL' := yL.splayButOne (left_sorted_of_sorted (by simp) st) x m_x_yL
        have hyL_to_yL' : yL.Sorted → yL'.Sorted := by
            intro a
            simp_all only [yL']
        have syL : yL.Sorted := left_sorted_of_sorted (by simp) st
        have nyL' : yL' ≠ nil := by
          sorry
        have syL' : yL'.Sorted := hyL_to_yL' syL
        have hltR : Forall (fun k ↦ yk < k) yR := match st with
          | .node _ _ _ _ biggerL smallerR sL sR => smallerR
        have syR : Sorted yR := match st with
          | .node _ _ _ _ biggerL smallerR sL sR => sR
        have hgtL : Forall (fun k ↦ k < yk) yL := match st with
          | .node _ _ _ _ biggerL smallerLR s sR => biggerL
        have hgtL' : Forall (fun k ↦ k < yk) yL' := by
          intro yl' m_yl'_yL'
          have m_yl'_yL : yl' ∈ yL := (mem_iff_mem_splayButOne syL m_x_yL yl').mpr m_yl'_yL'
          exact hgtL yl' m_yl'_yL
        let tNew := (node yk yv yL' yR)
        have nNew : tNew ≠ nil := by
          simp only [ne_eq, reduceCtorEq, not_false_eq_true]
        have stNew : tNew.Sorted := by
          apply sorted_unfold
          · exact hgtL'
          · exact hltR
          · exact syL'
          · exact syR
        let yL'R : SplayMap α β := yL'.right (nyL')
        match hyL' : yL'.locationOf x with
        | .root _ =>
          have sNew : tNew.Sorted := by
            apply sorted_unfold
            · exact hgtL'
            · exact hltR
            · exact syL'
            · exact syR
          aesop
        | .left p =>
          have nyL' : yL' ≠ nil := not_nil_of_atLeft p
          let tNewRl := tNew.rotateLeftChild (by simp) nyL'
          have nNewRl : tNewRl ≠ nil :=
            rotate_left_preserves_no_nil (by simp : tNew ≠ nil) nyL'
          have h1 : tNewRl.AtLeft x := by
            sorry
          have nNewL : tNew.left nNew ≠ nil := by
            simp_all [yL', tNewRl, tNew]
          have nNewRlL : tNewRl.left nNewRl ≠ nil :=
            left_not_nil_of_atLeft h1
          have stNewRl : tNewRl.Sorted :=
            rotate_left_sorted_of_sorted nNew nNewL stNew
          have : Sorted (tNewRl.rotateLeftChild nNewRl nNewRlL) :=
            rotate_left_sorted_of_sorted nNewRl nNewRlL stNewRl
          aesop
        | .right p =>
          let nyL' : yL' ≠ nil := not_nil_of_atRight p
          let yL'R : SplayMap α β := yL'.right nyL'
          have nyL'R : yL'R ≠ nil := right_not_nil_of_atRight (by simp_all only : AtRight yL' x)
          have syL'R : yL'R.Sorted := right_sorted_of_sorted nyL' syL'
          have nNewL : (tNew).left nNew ≠ nil := by
            simp_all [yL', tNew]
          let yL'Rr := yL'.rotateRightChild nyL' nyL'R
          have hgtL'Rr : Forall (fun k ↦ k < yk) yL'Rr := by
            intro x' m_xRr_yL'R
            sorry
          let tNewRl := node yk yv yL'Rr yR
          have nNewRl : (tNewRl) ≠ nil := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          have h1 : tNewRl.AtLeft x := by
            sorry
          have nNewRlL : (tNewRl).left nNewRl ≠ nil := left_not_nil_of_atLeft h1
          have syL'Rr : yL'Rr.Sorted := rotate_right_sorted_of_sorted nyL' nyL'R syL'
          have stNewRl : tNewRl.Sorted := by
            apply sorted_unfold
            · exact hgtL'Rr
            · exact hltR
            · exact syL'Rr
            · sorry
          have : Sorted ((tNewRl).rotateLeftChild nNewRl nNewRlL) :=
            rotate_left_sorted_of_sorted nNewRl nNewRlL stNewRl
          aesop
        | .none =>
          have : yL'.locationOf x ≠ .none := splayButOne_location syL m_x_yL
          simp [hyL'] at this
    else
      have hr : yk < x := by
        simp_all only [gt_iff_lt, not_false_eq_true, gt_of_ne_not_lt]
      rw [splayButOne]
      split
      · rename_i h_2
        subst h_2
        trivial
      · have m_x_yR : x ∈ yR := mem_right_of_mem_gt_key st mx hr
        let yR' := yR.splayButOne (right_sorted_of_sorted (by simp) st) x m_x_yR
        have hyR_to_yR' : yR.Sorted → yR'.Sorted := by
            intro a
            simp_all only [yR']
        have syR : yR.Sorted := right_sorted_of_sorted (by simp) st
        have syR' : yR'.Sorted := hyR_to_yR' syR
        have hltL : Forall (fun k ↦ k < yk) yL := match st with
          | .node _ _ _ _ biggerL smallerR sL sR => biggerL
        have syL : Sorted yL := match st with
          | .node _ _ _ _ biggerL smallerR sL sR => sL
        have hgtR : Forall (fun k ↦ yk < k) yR := match st with
          | .node _ _ _ _ biggerL smallerR sL sR => smallerR
        have hgtR' : Forall (fun k ↦ yk < k) yR' := by
          intro yr' m_yr'_yR'
          have m_yr'_yR : yr' ∈ yR := (mem_iff_mem_splayButOne syR m_x_yR yr').mpr m_yr'_yR'
          exact hgtR yr' m_yr'_yR
        let tNew := (node yk yv yL yR')
        have nNew : tNew ≠ nil := by
          simp only [ne_eq, reduceCtorEq, not_false_eq_true]
        have stNew : tNew.Sorted := by
          apply sorted_unfold
          · exact hltL
          · exact hgtR'
          · exact syL
          · exact syR'
        match hyR' : yR'.locationOf x with
        | .root _ =>
          have sNew : tNew.Sorted := by
            apply sorted_unfold
            · exact hltL
            · exact hgtR'
            · exact syL
            · exact syR'
          aesop
        | .left p =>
          have nyR' : yR' ≠ nil := not_nil_of_atLeft p
          let yR'L : SplayMap α β := yR'.left nyR'
          have nyR'L : yR'L ≠ nil := left_not_nil_of_atLeft p
          have syR'L : yR'L.Sorted := left_sorted_of_sorted nyR' syR'
          have nNewR : tNew.right nNew ≠ nil := by
            simp_all [yR', tNew]
          let yR'Rl := yR'.rotateLeftChild nyR' nyR'L
          have hgtR'Rl : Forall (fun k ↦ k < yk) yR'Rl := by
            intro x' m_xRl_yR'L
            sorry
          let tNewRr := node yk yv yR'Rl yL
          have nNewRr : tNewRr ≠ nil := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true]
          have h1 : tNewRr.AtRight x := by
            sorry
          have nNewRrR : tNewRr.right nNewRr ≠ nil := right_not_nil_of_atRight h1
          have syR'Rl : yR'Rl.Sorted := rotate_left_sorted_of_sorted nyR' nyR'L syR'
          have stNewRl : tNewRr.Sorted := by
            apply sorted_unfold
            · exact hgtR'Rl
            · sorry
            · exact syR'Rl
            · sorry
          have : Sorted (tNewRr.rotateRightChild nNewRr nNewRrR) :=
            rotate_right_sorted_of_sorted nNewRr nNewRrR stNewRl
          aesop
          sorry
        | .right p =>
          have nyR' : yR' ≠ nil := not_nil_of_atRight p
          let tNewRr := tNew.rotateRightChild (by simp) nyR'
          have nNewRr : tNewRr ≠ nil :=
            rotate_right_preserves_no_nil (by simp : tNew ≠ nil) nyR'
          have h1 : tNewRr.AtRight x := by
            sorry
          have nNewL : tNew.right nNew ≠ nil := by
            simp_all [yR', tNewRr, tNew]
          have nNewRrR : tNewRr.right nNewRr ≠ nil :=
            right_not_nil_of_atRight h1
          have stNewRr : tNewRr.Sorted :=
            rotate_right_sorted_of_sorted nNew nNewL stNew
          have : Sorted (tNewRr.rotateRightChild nNewRr nNewRrR) :=
            rotate_right_sorted_of_sorted nNewRr nNewRrR stNewRr
          aesop
        | .none =>
          have : yR'.locationOf x ≠ .none := splayButOne_location syR m_x_yR
          simp [hyR'] at this

/-- `splay` looks for a member of the `SplayMap`, and bubbles it right up to the top, altering the `SplayMap` in the process. -/
def splay (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) : SplayMap α β :=
  let t' := t.splayButOne st x mx
  match t'lx : t'.locationOf x with
  | .root _ => t'
  | .left p =>
      have nt' : t' ≠ nil := not_nil_of_atLeft p
      have nt'L : t'.left nt' ≠ nil := left_not_nil_of_atLeft p
      t'.rotateLeftChild nt' nt'L
  | .right p =>
      have nt' : t' ≠ nil := not_nil_of_atRight p
      have nt'R : t'.right nt' ≠ nil := right_not_nil_of_atRight p
      t'.rotateRightChild nt' nt'R
  | .none => by
      have : t'.locationOf x ≠ .none := splayButOne_location st mx
      contradiction

/-- The output of `splay` is a sorted `SplayMap`. -/
theorem mem_iff_mem_splay {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    ∀ y ∈ t, y ∈ t.splay st x mx := by
  intro y my
  have mxsbo : y ∈ t.splayButOne st x mx :=
    (mem_iff_mem_splayButOne st mx y).mp my
  match t'ly : (t.splayButOne st x mx).locationOf x with
  | .root _ =>
    rw [splay]
    split <;> simp_all
  | .left _ =>
    rw [splay]
    split <;> simp_all [mem_rotate_left_of_mem]
  | .right _ =>
    rw [splay]
    split <;> simp_all [mem_rotate_right_of_mem]
  | .none =>
    have := splayButOne_location st mx
    simp_all

/-- The output of `splayButOne` is a sorted `SplayMap`. -/
theorem sorted_splay {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    Sorted (t.splay st x mx) := by
  have ssbo : Sorted (t.splayButOne st x mx) := sorted_splayButOne st mx
  match t'lx : (t.splayButOne st x mx).locationOf x with
  | .root _ =>
    rw [splay]
    split <;> simp_all
  | .left _ =>
    rw [splay]
    split <;> simp_all [rotate_left_sorted_of_sorted]
  | .right _ =>
    rw [splay]
    split <;> simp_all [rotate_right_sorted_of_sorted]
  | .none =>
    have := splayButOne_location st mx
    simp_all

theorem splay_not_nil {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    t.splay st x mx ≠ nil := by
  intro nt'
  have : x ∈ t.splay st x mx := mem_iff_mem_splay st mx x mx
  simp_all [no_mem_nil]

theorem splay_top {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    (t.splay st x mx).key (splay_not_nil st mx) = x := by
  sorry

/-- Performs a search for `x` on the `SplayMap t` by using the BST structure, and returns the element found in the process. -/
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

/-- `last_to` always returns a member of the map. -/
theorem last_to_mem {t : SplayMap α β} (nt : t ≠ nil) : ∀ x, t.last_to nt x ∈ t := by
  intro x
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

/-- If the input `x` of `last_to` is in the map, then the output of `last_to` must be `x`. -/
theorem last_to_eq_if_mem {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    t.last_to (mem_no_nil mx) x = x := by
  induction t with
  | nil => contradiction
  | node yk yv yL yR iL iR =>
    if x_eq_yk : x = yk then
      simp_all [last_to]
    else if x_vs_yk : x < yk then
      have := mem_left_of_mem_lt_key st mx
      have mxL : x ∈ yL := by simp_all
      if nyL : yL = .nil then
        simp_all
      else
        have : Sorted yL := left_sorted_of_sorted (by simp) st
        simp_all [last_to]
    else
      have := mem_right_of_mem_gt_key st mx
      have mxR : x ∈ yR := by simp_all
      if nyR : yR = .nil then
        simp_all
      else
        have : Sorted yR := right_sorted_of_sorted (by simp) st
        simp_all [last_to]

/-- `last_to`, when asked to search for `x`, returns the closest element to `x` not greater than `x`. -/
theorem last_to_closest_lt {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    t.last_to (mem_no_nil mx) x < x → ∀ y ∈ t, y < t.last_to (mem_no_nil mx) x ∨ x < y := by
  let k := t.last_to (mem_no_nil mx) x
  -- have hk : k = t.last_to (mem_no_nil mx) x := rfl
  -- rw [←hk] at *
  intro h
  induction t with
  | nil => contradiction
  | node yk yv yL yR iL iR =>
    if x_eq_yk : x = yk then
      have : (node yk yv yL yR).last_to (mem_no_nil mx) x = x := by simp_all [last_to]
      order
    else if x_vs_yk : x < yk then
      have := mem_left_of_mem_lt_key st mx
      have mxL : x ∈ yL := by simp_all
      if nyL : yL = .nil then
        sorry
      else
        have : Sorted yL := left_sorted_of_sorted (by simp) st
        simp_all [last_to]
        sorry
    else
      have := mem_right_of_mem_gt_key st mx
      have mxR : x ∈ yR := by simp_all
      if nyR : yR = .nil then
        sorry
      else
        have : Sorted yR := right_sorted_of_sorted (by simp) st
        simp_all [last_to]
        sorry

/-- Searches for `x` in the `SplayMap t`, and bubbles up the result of `last_to` to the root, modifying `t` in the process.-/
def search (t : SplayMap α β) (st : Sorted t) (x : α) : SplayMap α β :=
  match ht : t with
  | nil => nil
  | node yk yv yL yR => by
    have nt : t ≠ nil := by simp_all
    rw [←ht] at st
    exact t.splay st (t.last_to nt x) (last_to_mem nt x)

lemma search_preserves_not_nil {t : SplayMap α β} (st : Sorted t) (x : α) :
    t ≠ nil → t.search st x ≠ .nil := by
  intro nt
  match ht : t with
  | node yk yv yL yR => simp_all [search, splay_not_nil]

lemma mem_search_of_mem {t : SplayMap α β} (st : Sorted t) (x : α) :
    ∀ y ∈ t, y ∈ t.search st x := by
  intro y my
  match ht : t with
  | node yk yv yL yR => simp_all [search, mem_iff_mem_splay]

/-- `search` does not alter the set of members in a SplayMap. -/
theorem sorted_search {t : SplayMap α β} (st : Sorted t) (x : α) : Sorted (t.search st x) := by
  match ht : t with
  | nil => simp_all [search]
  | node yk yv yL yR => simp_all [search, sorted_splay]

theorem search_top {t : SplayMap α β} (st : Sorted t) (x : α) (nt : t ≠ nil) :
    (t.search st x).key (search_preserves_not_nil st x nt) = t.last_to nt x := by
  match ht : t with
  | node yk yv yL yR =>
    simp_all [search, splay_top]
    sorry

lemma search_top_mem {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    (t.search st x).key (search_preserves_not_nil st x (mem_no_nil mx)) = x := by
  have ltx_eq_x : t.last_to (mem_no_nil mx) x = x := last_to_eq_if_mem st mx
  rw [search_top st x (mem_no_nil mx)]
  assumption

/-- Returns the value associated with `x` in the `SplayMap t`. -/
def get (t : SplayMap α β) (st : Sorted t) (x : α) (mx : x ∈ t) : SplayMap α β × β :=
  let t' := t.search st x
  have nt : t ≠ nil := mem_no_nil mx
  have nt' : t' ≠ nil := search_preserves_not_nil st x nt
  have hx : t'.key nt' = x := search_top_mem st mx
  match ht' : t' with
  | nil => by contradiction
  | node k v _ _ =>
    if hx' : x = k then
      have st' : Sorted t' := sorted_search st x
      (t', v)
    else by
      simp_all

theorem sorted_get {t : SplayMap α β} {x : α} (st : Sorted t) (mx : x ∈ t) :
    Sorted ((t.get st x mx).1) := by
  simp_all [get]
  split
  · contradiction
  · rename_i k _ _ _ _ _ _ _ heq _ _
    simp
    have hx' : x = k := by simp_all
    rw [hx']
    rw [←heq]
    exact sorted_search st x


/-- Inserts `(xk, xv)` into the search map. If `xk` is already present as a key, then the stored value is altered. In either case, the search map is altered. -/
def insert (t : SplayMap α β) (st : Sorted t) (xk : α) (xv : β) : SplayMap α β :=
  let t' := t.search st xk
  match t' with
  | nil => nil
  | node k v L R =>
    if xk = k then
      node k xv L R
    else if xk < k then
      node xk xv (node k v L nil) R
    else
      node xk xv L (node k v nil R)

/-- Inserting elements into a sorted `SplayMap` returns a sorted `SplayMap`. -/
theorem sorted_insert {t : SplayMap α β} {xk : α} {xv : β} (st : Sorted t) :
    Sorted (t.insert st xk xv) := by
  have st' : Sorted (t.search st xk) := sorted_search st xk
  match ht' : t.search st xk with
  | nil => simp_all [insert]
  | node k v L R =>
    simp_all [insert, Sorted]
    match st' with
    | .node _ _ _ _ gt_L lt_R sL sR =>
      aesop
      · exact .node xk xv L R gt_L lt_R sL sR
      · have xk_lt_R : ∀ y ∈ R, xk < y := by
          intro y myR
          exact lt_trans h_1 (lt_R y myR)
        have xk_gt_kvL : ∀ y ∈ node k v L nil, y < xk := by
          intro y myL
          simp_all
          sorry
        exact .node xk xv (node k v L nil) R (by simp_all) xk_lt_R (.node k v L nil gt_L (by simp) sL Sorted.nil) sR
      · sorry

/- Joins two `splayMap`s `L`, `R` where all keys in `L` are less than all keys in `R`. -/
def join (L R : SplayMap α β) (sL : Sorted L) (sR : Sorted R) (ord : ∀ x y, x ∈ L → y ∈ R → x < y) :
    SplayMap α β :=
  match hL : L, hR : R with
  | nil, _ => R
  | _, nil => L
  | node Ll Lv LL LR, node Rl Rv RL RR =>
      let L := node Ll Lv LL LR
      let R := node Rl Rv RL RR
      -- Find and splay the max element in L
      let maxK := L.max sL (by simp)
      let L' := L.splay sL maxK (L.max_mem sL (_))
      -- Now max element is at root of L'
      match L' with
      | node k v L _ => node k v L R
      | nil => sorry

theorem sorted_join {L R : SplayMap α β} (sL : Sorted L) (sR : Sorted R)
    (ord : ∀ x y, x ∈ L → y ∈ R → x < y) : Sorted (join L R sL sR ord) := by
  match hL : L, hR : R with
  | nil, _ => simp_all [join, right_sorted_of_sorted]
  | node Ll Lv LL LR, nil => simp_all [join, left_sorted_of_sorted]
  | node Ll Lv LL LR, node Rl Rv RL RR =>
    simp_all [join, left_sorted_of_sorted, right_sorted_of_sorted]
    split
    · simp_all [sorted_splay]
      sorry
    · sorry

/-- Tries to find the key `x` in map, and deletes it and the corresponding value it if found. Returns an error if `x` is not a key already. -/
def delete (t : SplayMap α β) (st : Sorted t) (x : α) : SplayMap α β :=
  let t' := t.search st x
  match ht' : t' with
  | nil => nil
  | node k v L R => by
    have st' : Sorted t' := sorted_search st x
    rw [ht'] at st'
    if x = k then
      have sL : Sorted L := left_sorted_of_sorted (by simp) st'
      have sR : Sorted R := right_sorted_of_sorted (by simp) st'
      exact join L R sL sR (left_lt_right_of_sorted (by simp) st')
    else
      exact panic! "key not found"

/-- Tries to find `x` in the map, and deletes it if found. Does not delete anything if `x` is not found, but alters the tree in the search process nonetheless. -/
def delete! (t : SplayMap α β) (st : Sorted t) (x : α) : SplayMap α β :=
  let t' := t.search st x
  match ht' : t' with
  | nil => nil
  | node k v L R => by
    have st' : Sorted t' := sorted_search st x
    rw [ht'] at st'
    if x = k then
      have sL : Sorted L := left_sorted_of_sorted (by simp) st'
      have sR : Sorted R := right_sorted_of_sorted (by simp) st'
      exact join L R sL sR (left_lt_right_of_sorted (by simp) st')
    else
      exact t'

theorem sorted_delete {t : SplayMap α β} {x : α} (st : Sorted t) : Sorted (t.delete st x) := by
  simp_all [delete]
  split
  · exact Sorted.nil
  · split
    · simp_all [sorted_search, sorted_join]
    · exact Sorted.nil

theorem sorted_delete! {t : SplayMap α β} {x : α} (st : Sorted t) : Sorted (t.delete! st x) := by
  simp_all [delete!]
  split
  · exact Sorted.nil
  · split
    · simp_all [sorted_search, sorted_join]
    · rename_i heq h
      rw [←heq]
      exact sorted_search st x

end SplayMap
