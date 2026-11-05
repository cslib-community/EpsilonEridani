/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Lookup

/-!
# Rank queries in classic B-trees

`rankM` scans a node's separators and descends into one child, following the search in
`lookupM`. Each separator passed contributes one plus the pure size of its preceding child.
At the first separator at least the query, the search descends into the preceding child;
a key equal to the query is not counted. The pure `Id` instantiation is `rank`.

`rank_eq_of_isSortedAssoc` identifies this count with `SortedAssoc.rank` on `toList` when
the entries are sorted. `rank_eq` specializes it to well-formed trees of any minimum degree.
The constructor equations support evaluation and monadic instantiations without unfolding
the well-founded recursion.
-/

public section

universe w

namespace EpsilonEridani.BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Rank by a single descent. Scan past separators `k'` for which `le k k'` fails, adding
the pure `BTree.size` of the child before each separator plus one. At the first separator
with `le k k'`, descend into the child before it; otherwise descend into the last child.
When `le` decides the key order and `toList` is sorted, the result counts keys strictly below
`k`, excluding equality. Scanning triples and computing pure subtree sizes are uncharged
client computation in the node-visit and comparison cost models. `visit` fires once when
the scan chooses a child, including at zero-key nodes, and never at an empty leaf. -/
def rankM (le : α → α → m Bool) (visit : m Unit) (k : α) : BTree α β → m ℕ
  | .leaf => pure 0
  | .node first [] => do
    visit
    rankM le visit k first
  | .node first ((k', _, c) :: rest) => do
    if ← le k k' then
      visit
      rankM le visit k first
    else
      return first.size + 1 + (← rankM le visit k (.node c rest))
termination_by tr => sizeOf tr

/-- The empty tree has rank zero and is not visited. -/
theorem rankM_leaf (le : α → α → m Bool) (visit : m Unit) (k : α) :
    rankM le visit k (.leaf : BTree α β) = pure 0 := by
  rw [rankM]

/-- A node without keys is visited before searching its only child. -/
theorem rankM_node_nil (le : α → α → m Bool) (visit : m Unit) (k : α)
    (first : BTree α β) :
    rankM le visit k (.node first []) = (do
      visit
      rankM le visit k first) := by
  rw [rankM]

/-- Descend before the first separator at least the query; otherwise count the preceding
child and separator and continue scanning, without an additional visit. -/
theorem rankM_node_cons (le : α → α → m Bool) (visit : m Unit) (k k' : α) (v : β)
    (first c : BTree α β) (rest : List (α × β × BTree α β)) :
    rankM le visit k (.node first ((k', v, c) :: rest)) = (do
      if ← le k k' then
        visit
        rankM le visit k first
      else
        return first.size + 1 + (← rankM le visit k (.node c rest))) := by
  rw [rankM]

end Polymorphic

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Pure rank: the `Id` instantiation of `rankM` with a trivial visit action. -/
def rank (k : α) (tr : BTree α β) : ℕ := Id.run (rankM leI (pure ()) k tr)

/-- `rank` is the `Id` instantiation of `rankM`. -/
theorem rank_def (k : α) : rank k tr = Id.run (rankM leI (pure ()) k tr) := (rfl)

/-- No keys are below the query in the empty tree. -/
@[simp] theorem rank_leaf (k : α) : rank k (.leaf : BTree α β) = 0 := by
  simp [rank, rankM_leaf]

/-- A node without keys delegates rank to its only child. -/
@[simp] theorem rank_node_nil (k : α) (first : BTree α β) :
    rank k (.node first []) = rank k first := by
  simp [rank, rankM_node_nil]

/-- A separator at least the query selects the preceding child; a smaller separator
contributes its preceding child's size plus one before the scan continues. -/
@[simp] theorem rank_node_cons (k k' : α) (v : β) (first c : BTree α β)
    (rest : List (α × β × BTree α β)) :
    rank k (.node first ((k', v, c) :: rest)) =
      if k ≤ k' then rank k first else first.size + 1 + rank k (.node c rest) := by
  by_cases hk : k ≤ k' <;> simp [rank, rankM_node_cons, leI, hk]

/-- Model equation: on a tree with sorted entries, rank counts exactly the entries of
`toList` whose keys are strictly below the query. -/
theorem rank_eq_of_isSortedAssoc (h : tr.toList.IsSortedAssoc) (k : α) :
    rank k tr = SortedAssoc.rank k tr.toList := by
  fun_induction rankM (m := Id) leI (pure ()) k tr with
  | case1 => simp
  | case2 first ih => simpa using ih (by simpa using h)
  | case3 first k' v c rest ih₁ ih₂ =>
    rw [toList_node, toListRest_cons, List.cons_append] at h ⊢
    rw [toList_node] at ih₂
    obtain ⟨h₁, h₂, hlt, hgt⟩ := List.isSortedAssoc_append_cons_iff.1 h
    rw [rank_node_cons, SortedAssoc.rank_append, SortedAssoc.rank_cons]
    by_cases hk : k ≤ k'
    · have hn : SortedAssoc.rank k (c.toList ++ toListRest rest) = 0 :=
        SortedAssoc.rank_eq_zero_iff.2 fun p hp => hk.trans (hgt p hp).le
      simp only [hk, not_lt.2 hk, ↓reduceIte, hn, Nat.add_zero, ih₁ h₁]
    · have hall : SortedAssoc.rank k first.toList = first.toList.length :=
        SortedAssoc.rank_eq_length_iff.2 fun p hp => (hlt p hp).trans (lt_of_not_ge hk)
      simp only [hk, lt_of_not_ge hk, ↓reduceIte, hall, ih₂ h₂, length_toList]
      omega

/-- Model equation for rank on well-formed trees. -/
theorem rank_eq (h : IsWF t tr) (k : α) : rank k tr = SortedAssoc.rank k tr.toList :=
  rank_eq_of_isSortedAssoc h.sorted k

private def rankExample : BTree ℕ String :=
  .node (.node .leaf [(1, "a", .leaf), (3, "c", .leaf)])
    [(5, "e", .node .leaf [(7, "g", .leaf), (9, "i", .leaf)]),
     (11, "k", .node .leaf [(13, "m", .leaf), (15, "o", .leaf)])]

example : IsWF 2 rankExample := by decide

example : IsWF 3 rankExample := by decide

-- Equal root separators are excluded, while all entries of earlier children are counted.
example : rank 5 rankExample = 2 := by simp [rankExample, size]

example : rank 11 rankExample = 5 := by simp [rankExample, size]

-- Search in each child, including equality at a child key and a gap between keys.
example : rank 3 rankExample = 1 := by simp [rankExample, size]

example : rank 8 rankExample = 4 := by simp [rankExample, size]

example : rank 15 rankExample = 7 := by simp [rankExample, size]

example : rank 0 rankExample = 0 := by simp [rankExample]

example : rank 16 rankExample = 8 := by simp [rankExample, size]

example : rank 2 (.leaf : BTree ℕ String) = 0 := by simp

-- Sortedness suffices even for zero-key nodes, which need not satisfy occupancy.
example : rank 2 (.node (.node .leaf [(1, "a", .leaf)]) []) = 1 := by simp

end Pure

end EpsilonEridani.BTree
