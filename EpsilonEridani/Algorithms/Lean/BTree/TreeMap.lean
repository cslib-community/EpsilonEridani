/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.OfSortedList
public import EpsilonEridani.Foundations.Data.TreeMap.SortedAssoc

/-!
# Bulk loading and `Std.TreeMap`

The output of bulk loading agrees with Lean core's `Std.TreeMap`, ordered by the `compare` of
the linear order: on a sorted list `l`, the entries of `Std.TreeMap.ofList l compare` are `l`
itself (`Std.TreeMap.toList_ofList_of_isSortedAssoc`, in
`EpsilonEridani.Foundations.Data.TreeMap.SortedAssoc`), and so are those of
`EpsilonEridani.BTree.ofSortedList t l` (`toList_ofSortedList`).
-/

public section

variable {α β : Type} [LinearOrder α]

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
