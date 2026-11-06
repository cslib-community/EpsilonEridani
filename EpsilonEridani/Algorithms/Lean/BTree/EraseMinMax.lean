/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Erase
public import EpsilonEridani.Algorithms.Lean.BTree.MinMax

/-!
# Removing the least and greatest entries of classic B-trees

`eraseMinM` and `eraseMaxM` remove and return the least and greatest entries of a B-tree: they
find the extreme entry with `minM` or `maxM` from `EpsilonEridani.BTree.MinMax` and erase its key
with `eraseM` from `EpsilonEridani.BTree.Erase`, over an arbitrary monad with a comparator and a
node-visit action. The pure operations `eraseMin?` and `eraseMax?` are the `Id` instantiations
with `leI` and `visit := pure ()`.

`eraseMin?_eq` and `eraseMax?_eq` are the model equations, on any tree: the first or last entry
of `toList` together with the erasure of its key. On well-formed trees,
`toList_of_eraseMin?_eq_some` and `toList_of_eraseMax?_eq_some` split the entries into the
removed entry and the rest, and the rest is well-formed. Costs are not stated here.
-/

public section

universe w

namespace EpsilonEridani.BTree

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Remove and return the least entry: find it with `minM`, then erase its key. -/
@[expose] def eraseMinM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    m (Option ((α × β) × BTree α β)) := do
  match ← minM visit tr with
  | none => pure none
  | some p => return some (p, ← eraseM t le visit p.1 tr)

/-- Removing the least entry finds it with `minM`, then erases its key. -/
theorem eraseMinM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    eraseMinM t le visit tr = (do
      match ← minM visit tr with
      | none => pure none
      | some p => return some (p, ← eraseM t le visit p.1 tr)) := rfl

/-- Remove and return the greatest entry: find it with `maxM`, then erase its key. -/
@[expose] def eraseMaxM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    m (Option ((α × β) × BTree α β)) := do
  match ← maxM visit tr with
  | none => pure none
  | some p => return some (p, ← eraseM t le visit p.1 tr)

/-- Removing the greatest entry finds it with `maxM`, then erases its key. -/
theorem eraseMaxM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (tr : BTree α β) :
    eraseMaxM t le visit tr = (do
      match ← maxM visit tr with
      | none => pure none
      | some p => return some (p, ← eraseM t le visit p.1 tr)) := rfl

end Polymorphic

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Remove and return the least entry, pure. -/
@[expose] def eraseMin? (t : ℕ) (tr : BTree α β) : Option ((α × β) × BTree α β) :=
  Id.run (eraseMinM t leI (pure ()) tr)

/-- Remove and return the greatest entry, pure. -/
@[expose] def eraseMax? (t : ℕ) (tr : BTree α β) : Option ((α × β) × BTree α β) :=
  Id.run (eraseMaxM t leI (pure ()) tr)

/-- `eraseMin?` is the minimum together with the erasure of its key. -/
theorem eraseMin?_eq_map_min? : eraseMin? t tr = (min? tr).map fun p => (p, erase t p.1 tr) := by
  unfold eraseMin? eraseMinM min?
  cases minM (m := Id) (pure ()) tr <;> rfl

/-- `eraseMax?` is the maximum together with the erasure of its key. -/
theorem eraseMax?_eq_map_max? : eraseMax? t tr = (max? tr).map fun p => (p, erase t p.1 tr) := by
  rw [max?_def]
  unfold eraseMax? eraseMaxM
  cases maxM (m := Id) (pure ()) tr <;> rfl

/-- Model equation of `eraseMin?`: the first entry and the tree with its key erased. -/
theorem eraseMin?_eq : eraseMin? t tr = tr.toList.head?.map fun p => (p, erase t p.1 tr) := by
  rw [eraseMin?_eq_map_min?, min?_eq]

/-- Model equation of `eraseMax?`: the last entry and the tree with its key erased. -/
theorem eraseMax?_eq : eraseMax? t tr = tr.toList.getLast?.map fun p => (p, erase t p.1 tr) := by
  rw [eraseMax?_eq_map_max?, max?_eq]

/-- On a well-formed tree, `eraseMin?` splits the entries into the first and the rest, and the
rest is well-formed. -/
theorem toList_of_eraseMin?_eq_some (h : IsWF t tr) {p : α × β} {tr' : BTree α β}
    (he : eraseMin? t tr = some (p, tr')) : tr.toList = p :: tr'.toList ∧ IsWF t tr' := by
  rw [eraseMin?_eq, Option.map_eq_some_iff] at he
  obtain ⟨q, hq, hpq⟩ := he
  simp only [Prod.mk.injEq] at hpq
  obtain ⟨rfl, rfl⟩ := hpq
  refine ⟨?_, h.erase _⟩
  obtain ⟨l, hl⟩ : ∃ l, tr.toList = q :: l := by
    cases hc : tr.toList with
    | nil => simp [hc] at hq
    | cons a l => simp only [hc, List.head?_cons, Option.some.injEq] at hq; exact ⟨l, hq ▸ rfl⟩
  have hs := h.sorted
  rw [hl, List.isSortedAssoc_cons_iff] at hs
  rw [toList_erase h, hl, SortedAssoc.erase_cons]
  simp only [↓reduceIte]
  rw [SortedAssoc.erase_of_forall_ne fun r hr => (hs.1 r hr).ne']

/-- On a well-formed tree, `eraseMax?` splits the entries into the rest and the last, and the
rest is well-formed. -/
theorem toList_of_eraseMax?_eq_some (h : IsWF t tr) {p : α × β} {tr' : BTree α β}
    (he : eraseMax? t tr = some (p, tr')) : tr.toList = tr'.toList ++ [p] ∧ IsWF t tr' := by
  rw [eraseMax?_eq, Option.map_eq_some_iff] at he
  obtain ⟨q, hq, hpq⟩ := he
  simp only [Prod.mk.injEq] at hpq
  obtain ⟨rfl, rfl⟩ := hpq
  refine ⟨?_, h.erase _⟩
  obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 hq
  have hs := h.sorted
  rw [hl, List.isSortedAssoc_append_iff] at hs
  rw [toList_erase h, hl, SortedAssoc.erase_append,
    SortedAssoc.erase_of_forall_ne fun r hr => (hs.2.2 r hr q (by simp)).ne]
  simp [SortedAssoc.erase_cons]

/-! ### Examples -/

/-- `eraseMin?` returns the least entry and the rest. -/
example :
    ((eraseMin? 2 (BTree.node (α := ℕ) (β := String) .leaf
      [(1, "a", .leaf), (3, "c", .leaf)])).map fun p => (p.1, p.2.toList)) =
      some ((1, "a"), [(3, "c")]) := by decide

end Pure

end EpsilonEridani.BTree
