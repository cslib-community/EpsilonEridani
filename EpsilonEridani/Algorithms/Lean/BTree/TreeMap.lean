/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.OfSortedList
public import Std.Data.TreeMap.Lemmas

/-!
# Bulk loading and `Std.TreeMap`

The output of bulk loading agrees with Lean core's `Std.TreeMap`, ordered by the `compare` of
the linear order: on a sorted list `l`, the entries of `Std.TreeMap.ofList l compare` are `l`
itself (`Std.TreeMap.toList_ofList_of_isSortedAssoc`), and so are those of
`EpsilonEridani.BTree.ofSortedList t l` (`toList_ofSortedList`). The comparison uses only the
public lemmas of `Std.TreeMap`, nothing of its internals.
-/

public section

variable {α β : Type} [LinearOrder α]

namespace Std.TreeMap

/-- The entries of the tree map built from a sorted association list are the list itself. -/
theorem toList_ofList_of_isSortedAssoc {l : List (α × β)} (h : l.IsSortedAssoc) :
    (ofList l compare).toList = l := by
  have hd : l.Pairwise fun a b => ¬compare a.1 b.1 = .eq :=
    h.pairwise.imp fun hab => by rw [compare_eq_iff_eq]; exact hab.ne
  have hof : ∀ {k : α} {v : β}, (k, v) ∈ l → (ofList l compare)[k]? = some v :=
    fun hm => getElem?_ofList_of_mem (compare_eq_iff_eq.2 rfl) hd hm
  refine List.IsSortedAssoc.eq_of_forall_mem_iff ?_ h fun ⟨k, v⟩ => ?_
  · rw [List.isSortedAssoc_iff_pairwise, List.pairwise_map]
    exact ordered_keys_toList.imp fun hab => compare_lt_iff_lt.1 hab
  · rw [mem_toList_iff_getElem?_eq_some]
    refine ⟨fun hk => ?_, hof⟩
    by_cases hc : (l.map Prod.fst).contains k
    · obtain ⟨⟨k', v'⟩, hm, rfl⟩ := List.mem_map.1 (List.contains_iff_mem.1 hc)
      rw [hof hm, Option.some_inj] at hk
      exact hk ▸ hm
    · rw [getElem?_ofList_of_contains_eq_false (Bool.eq_false_iff.2 hc)] at hk
      exact absurd hk (by simp)

end Std.TreeMap

namespace EpsilonEridani.BTree

/-- Bulk loading a sorted list gives the entries of Lean core's tree map built from it: an output
equality, for every minimum degree. -/
theorem toList_ofSortedList_eq_treeMap (t : ℕ) {l : List (α × β)} (h : l.IsSortedAssoc) :
    (ofSortedList t l).toList = (Std.TreeMap.ofList l compare).toList :=
  (toList_ofSortedList t l).trans (Std.TreeMap.toList_ofList_of_isSortedAssoc h).symm

/-- Four entries at `t = 2`: the same entries as the tree map. -/
example : (ofSortedList 2 [(1, 'a'), (2, 'b'), (3, 'c'), (4, 'd')]).toList =
    (Std.TreeMap.ofList [(1, 'a'), (2, 'b'), (3, 'c'), (4, 'd')] compare).toList :=
  toList_ofSortedList_eq_treeMap 2 (by decide)

end EpsilonEridani.BTree
