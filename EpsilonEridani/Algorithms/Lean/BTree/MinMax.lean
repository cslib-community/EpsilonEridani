/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Basic

/-!
# Minimum and maximum in classic B-trees

The extremal-entry queries follow the leftmost or rightmost child, as in Cormen, Leiserson,
Rivest and Stein, *Introduction to Algorithms*, Chapter 18. Each is defined once over an
arbitrary monad, with a node-visit action, then instantiated at `Id` for the pure query.
No comparator or order instance is needed: the queries use the tree's structural order.
A visit is charged once for each nonempty node on the descent; scanning a node's triples
for its last child does not charge additional visits.

`min?_eq` and `max?_eq` identify these queries with `head?` and `getLast?` of `toList`, even
without sortedness or occupancy. Under `List.IsSortedAssoc`, the returned entry is respectively
the least or greatest entry by key. The corresponding `IsWF` characterizations apply at any
minimum degree. The queries return `none` exactly when the tree has no entries, including
malformed trees consisting of nodes with no keys.
-/

public section

universe w

namespace EpsilonEridani.BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- First entry in structural order: descend through first children, falling back to the
node's first entry when its first child has no entries. No comparisons are needed. -/
def minM (visit : m Unit) : BTree α β → m (Option (α × β))
  | .leaf => pure none
  | .node first rest => do
    visit
    match ← minM visit first with
    | some p => pure (some p)
    | none => pure (rest.head?.map fun e => (e.1, e.2.1))

/-- Last entry in structural order: scan the node's triples and descend into its last child,
falling back to the last entry when that child has no entries. `visit` fires once per node,
after the scan, and no comparisons are needed. -/
def maxM (visit : m Unit) : BTree α β → m (Option (α × β))
  | .leaf => pure none
  | .node first [] => do
    visit
    maxM visit first
  | .node _ [(k, v, c)] => do
    visit
    match ← maxM visit c with
    | some p => pure (some p)
    | none => pure (some (k, v))
  | .node _ ((_, _, c) :: e :: rest) => maxM visit (.node c (e :: rest))
termination_by tr => sizeOf tr

end Polymorphic

section Pure

variable {α β : Type} {tr : BTree α β}

/-- Pure minimum query: the `Id` instantiation of `minM` with a trivial visit action. -/
def min? (tr : BTree α β) : Option (α × β) := Id.run (minM (pure ()) tr)

/-- Pure maximum query: the `Id` instantiation of `maxM` with a trivial visit action. -/
def max? (tr : BTree α β) : Option (α × β) := Id.run (maxM (pure ()) tr)

/-- `min?` is the `Id` instantiation of `minM`. -/
theorem min?_def : min? tr = Id.run (minM (pure ()) tr) := (rfl)

/-- `max?` is the `Id` instantiation of `maxM`. -/
theorem max?_def : max? tr = Id.run (maxM (pure ()) tr) := (rfl)

/-- The empty tree has no minimum entry. -/
@[simp] theorem min?_leaf : min? (.leaf : BTree α β) = none := by
  simp [min?, minM]

/-- The empty tree has no maximum entry. -/
@[simp] theorem max?_leaf : max? (.leaf : BTree α β) = none := by
  simp [max?, maxM]

/-- The first child's minimum takes priority over the node's first entry. -/
@[simp] theorem min?_node (first : BTree α β) (rest : List (α × β × BTree α β)) :
    min? (.node first rest) =
      (min? first).or (rest.head?.map fun e => (e.1, e.2.1)) := by
  simp only [min?, minM, Id.run_bind]
  cases Id.run (minM (pure ()) first) <;> rfl

/-- A node without keys has the maximum of its only child. -/
@[simp] theorem max?_node_nil (first : BTree α β) :
    max? (.node first []) = max? first := by
  simp [max?, maxM]

/-- At the last triple, the last child's maximum takes priority over the last entry. -/
@[simp] theorem max?_node_singleton (first c : BTree α β) (k : α) (v : β) :
    max? (.node first [(k, v, c)]) = (max? c).or (some (k, v)) := by
  simp only [max?, maxM, Id.run_bind]
  cases Id.run (maxM (pure ()) c) <;> rfl

/-- Scanning past a triple leaves the maximum query on the remaining suffix of the node. -/
@[simp] theorem max?_node_cons_cons (first c : BTree α β) (k : α) (v : β)
    (e : α × β × BTree α β) (rest : List (α × β × BTree α β)) :
    max? (.node first ((k, v, c) :: e :: rest)) = max? (.node c (e :: rest)) := by
  simp [max?, maxM]

/-- Model equation: the minimum query returns the first entry of `toList`, on any tree. -/
theorem min?_eq : min? tr = tr.toList.head? := by
  induction tr with
  | leaf => simp
  | node first rest ih _ =>
    rw [min?_node, toList_node, List.head?_append, ih]
    cases rest <;> simp

/-- Model equation: the maximum query returns the last entry of `toList`, on any tree. -/
theorem max?_eq : max? tr = tr.toList.getLast? := by
  fun_induction maxM (m := Id) (pure ()) tr with
  | case1 => simp
  | case2 first ih => simpa using ih
  | case3 first k v c ih =>
    simp only [max?_node_singleton, ih, toList_node, toListRest_cons, toListRest_nil,
      List.append_nil, List.getLast?_append_cons]
    simp [List.getLast?_cons]
  | case4 first k v c e rest ih =>
    rw [max?_node_cons_cons, ih]
    simp only [toList_node, toListRest_cons, List.cons_append, List.getLast?_append_cons]
    exact (List.getLast?_cons_of_ne_nil (by simp)).symm

/-- The minimum query fails exactly when there are no entries. -/
@[simp] theorem min?_eq_none_iff : min? tr = none ↔ tr.size = 0 := by
  simp [min?_eq, ← length_toList]

/-- The maximum query fails exactly when there are no entries. -/
@[simp] theorem max?_eq_none_iff : max? tr = none ↔ tr.size = 0 := by
  simp [max?_eq, ← length_toList]

variable [LinearOrder α] {t : ℕ} {p : α × β}

/-- On a tree with sorted entries, `min?` returns exactly the entry of least key. -/
theorem min?_eq_some_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) :
    min? tr = some p ↔ p ∈ tr ∧ ∀ q ∈ tr, p.1 ≤ q.1 := by
  simpa only [min?_eq, mem_def] using h.head?_eq_some_iff

/-- On a tree with sorted entries, `max?` returns exactly the entry of greatest key. -/
theorem max?_eq_some_iff_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) :
    max? tr = some p ↔ p ∈ tr ∧ ∀ q ∈ tr, q.1 ≤ p.1 := by
  simpa only [max?_eq, mem_def] using h.getLast?_eq_some_iff

/-- In a well-formed tree, `min?` returns exactly the entry of least key. -/
theorem min?_eq_some_iff (h : IsWF t tr) :
    min? tr = some p ↔ p ∈ tr ∧ ∀ q ∈ tr, p.1 ≤ q.1 :=
  min?_eq_some_iff_of_isSortedAssoc h.sorted

/-- In a well-formed tree, `max?` returns exactly the entry of greatest key. -/
theorem max?_eq_some_iff (h : IsWF t tr) :
    max? tr = some p ↔ p ∈ tr ∧ ∀ q ∈ tr, q.1 ≤ p.1 :=
  max?_eq_some_iff_of_isSortedAssoc h.sorted

end Pure

/-! Examples exercise both descent and fallback, including nodes with no keys. -/

example : min? (BTree.leaf : BTree ℕ String) = none := by simp

example : max? (BTree.leaf : BTree ℕ String) = none := by simp

example : min? (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf)]) = some (1, "a") := by simp

example : max? (BTree.node (α := ℕ) (β := String) .leaf
    [(1, "a", .leaf), (3, "c", .leaf)]) = some (3, "c") := by simp

example : min? (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (1, "a") := by simp

example : max? (BTree.node (α := ℕ) (β := String)
    (.node .leaf [(1, "a", .leaf)]) [(3, "c", .node .leaf [(5, "e", .leaf)])]) =
    some (5, "e") := by simp

example : min? (BTree.node (α := ℕ) (β := String) (.node .leaf []) []) = none := by simp

example : max? (BTree.node (α := ℕ) (β := String) (.node .leaf []) []) = none := by simp

example : min? (BTree.node (α := ℕ) (β := String) (.node .leaf [])
    [(3, "c", .node .leaf [])]) = some (3, "c") := by simp

example : max? (BTree.node (α := ℕ) (β := String) (.node .leaf [])
    [(3, "c", .node .leaf [])]) = some (3, "c") := by simp

end EpsilonEridani.BTree
