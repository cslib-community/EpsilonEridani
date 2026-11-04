/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Basic

/-!
# Search in classic B-trees

Search in the B-trees of `EpsilonEridani.BTree`, following Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms*, Chapter 18: scan a node's keys in order, stop at the query, or
descend into the child before the first key above it.

Each operation is defined once, over an arbitrary monad `m`, taking a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`, with no order instance in scope,
so that every comparison goes through `le`. `slotM` is the within-node linear search, `lookupM`
the search itself and `containsM` the membership test. The pure operations `slot`, `lookup` and
`contains` are the `Id` instantiations with the decidable comparator `leI` of a linear order and
`visit := pure ()`, in the pattern of CSLib's `List.mergeSortM` and `List.idRun_mergeSortM`.

`lookup_eq_of_isSortedAssoc` is the model equation: on any tree whose entries are sorted,
`lookup` is `List.lookup` on `toList`. `lookup_eq`, `contains_eq` and `contains_iff` specialize
it to well-formed trees. Costs are not stated here.

`lookupM` recurses on `.node c rest`, which is not a structural subterm, so it is defined by
well-founded recursion on `sizeOf` and does not reduce in the elaborator; the examples evaluate it
with `decide +kernel`.
-/

public section

universe w

namespace EpsilonEridani

namespace BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Within-node linear search: the position of the first key not below `k`. At most one
comparison per key. -/
@[expose] def slotM (le : α → α → m Bool) (k : α) : List (α × β × BTree α β) → m ℕ
  | [] => pure 0
  | (k', _, _) :: rest => do
    if ← le k k' then pure 0 else return (← slotM le k rest) + 1

/-- Lookup. Walking along a node's triples is free; `visit` fires when the search commits to a
child or stops at a key, so each node is visited once. Equality is two `le` queries. -/
@[expose] def lookupM (le : α → α → m Bool) (visit : m Unit) (k : α) :
    BTree α β → m (Option β)
  | .leaf => pure none
  | .node first [] => do
    visit
    lookupM le visit k first
  | .node first ((k', v, c) :: rest) => do
    if ← le k k' then
      visit
      if ← le k' k then
        pure (some v)
      else
        lookupM le visit k first
    else
      lookupM le visit k (.node c rest)
termination_by tr => sizeOf tr

/-- Membership test. -/
@[expose] def containsM (le : α → α → m Bool) (visit : m Unit) (k : α) (tr : BTree α β) :
    m Bool := do
  return (← lookupM le visit k tr).isSome

end Polymorphic

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- The decidable comparator of a linear order, in the identity monad. -/
abbrev leI (a b : α) : Id Bool := pure (decide (a ≤ b))

/-- Pure within-node search: the `Id` instantiation of `slotM`. -/
@[expose] def slot (k : α) (rest : List (α × β × BTree α β)) : ℕ := Id.run (slotM leI k rest)

/-- Pure lookup: the `Id` instantiation of `lookupM` with `visit := pure ()`. -/
@[expose] def lookup (k : α) (tr : BTree α β) : Option β := Id.run (lookupM leI (pure ()) k tr)

/-- Pure membership test: the `Id` instantiation of `containsM` with `visit := pure ()`. -/
@[expose] def contains (k : α) (tr : BTree α β) : Bool := Id.run (containsM leI (pure ()) k tr)

/-- The pure within-node search counts the keys below `k` before the first key not below it. -/
theorem slot_eq_length_takeWhile (k : α) (rest : List (α × β × BTree α β)) :
    slot k rest = (rest.takeWhile fun e => decide (e.1 < k)).length := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    unfold slot at ih ⊢
    by_cases hk : k ≤ k'
    · simp [slotM, hk, not_lt.2 hk]
    · simp [slotM, hk, lt_of_not_ge hk, ih]

/-- The position found by the within-node search is at most the number of keys. -/
theorem slot_le_length (k : α) (rest : List (α × β × BTree α β)) : slot k rest ≤ rest.length := by
  rw [slot_eq_length_takeWhile]
  exact (List.takeWhile_sublist _).length_le

/-- Lookup in the empty tree fails. -/
@[simp] theorem lookup_leaf (k : α) : lookup k (.leaf : BTree α β) = none := by
  simp [lookup, lookupM]

/-- Model equation: on a tree with sorted entries, lookup is lookup in `toList`. -/
theorem lookup_eq_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    lookup k tr = List.lookup k tr.toList := by
  unfold lookup
  fun_induction lookupM (m := Id) leI (pure ()) k tr with
  | case1 => simp
  | case2 first ih => simpa using ih (by simpa using h)
  | case3 first k' v c rest ih₁ ih₂ =>
    rw [toList_node, toListRest_cons, List.cons_append] at h ⊢
    rw [toList_node] at ih₂
    obtain ⟨h₁, h₂, hlt, hgt⟩ := List.isSortedAssoc_append_cons_iff.1 h
    rcases lt_trichotomy k k' with hk | rfl | hk
    · simp only [leI, hk.le, not_le.2 hk, decide_true, decide_false, pure_bind, ite_true,
        Bool.false_eq_true, ite_false]
      rw [List.lookup_append_of_forall_gt fun p hp => ?_, ih₁ h₁]
      rcases List.mem_cons.1 hp with rfl | hp
      exacts [hk, hk.trans (hgt p hp)]
    · simp [leI, List.lookup_append_of_forall_lt hlt]
    · simp only [leI, not_le.2 hk, decide_false, pure_bind, Bool.false_eq_true, ite_false]
      rw [ih₂ h₂, List.lookup_append_of_forall_lt fun p hp => (hlt p hp).trans hk,
        List.lookup_cons_of_ne hk.ne']

/-- Model equation on well-formed trees. -/
theorem lookup_eq (h : IsWF t tr) (k : α) : lookup k tr = List.lookup k tr.toList :=
  lookup_eq_of_isSortedAssoc h.sorted k

/-- Membership on well-formed trees is success of lookup in `toList`. -/
theorem contains_eq (h : IsWF t tr) (k : α) : contains k tr = (List.lookup k tr.toList).isSome := by
  rw [← lookup_eq h k]
  rfl

/-- A key is in a well-formed tree exactly when it is among the tree's keys. -/
theorem contains_iff (h : IsWF t tr) (k : α) : contains k tr = true ↔ k ∈ tr.keys := by
  simp only [contains_eq h, Option.isSome_iff_exists, h.sorted.lookup_eq_some_iff, mem_keys,
    mem_def]

/-- Sorted but not well-formed: a two-level tree whose child has no keys. Lookup still agrees
with the model, which is what `lookup_eq_of_isSortedAssoc` promises. -/
example : lookup 1 (BTree.node (α := ℕ) (β := String) (.node .leaf []) [(1, "a", .leaf)]) =
    some "a" := by decide +kernel

example : lookup 2 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf), (3, "c", .leaf)]) =
    none := by decide +kernel

example : slot 2 ([(1, "a", .leaf), (3, "c", .leaf)] : List (ℕ × String × BTree ℕ String)) = 1 := by
  decide

example : contains 3 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf), (3, "c", .leaf)]) =
    true := by decide +kernel

end Pure

end BTree

end EpsilonEridani
