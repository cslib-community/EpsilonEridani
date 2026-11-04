/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama, Claude
-/
module

public import Mathlib.Data.List.Sort

/-!
# Sorted association lists

The specification model for ordered maps: a list of `(key, value)` pairs whose keys are strictly
increasing, so that keys are distinct. `List.IsSortedAssoc` is the predicate, stated as
`List.Pairwise (· < ·)` on the key list, which is the form that the splitting and concatenation
lemmas consume; Mathlib's `List.SortedLT` is the same predicate by `List.sortedLT_iff_pairwise`.

The model operations live in `EpsilonEridani.SortedAssoc` and are plain list functions. Lookup is
`List.lookup`; insertion replaces an existing key; erasure, strict predecessor and successor,
closed-interval restriction, and rank are defined here. The minimum and maximum of a sorted list
are its `head?` and `getLast?`, characterised by `List.IsSortedAssoc.head?_eq_some_iff` and
`List.IsSortedAssoc.getLast?_eq_some_iff`. Together these are the reference semantics against
which tree-shaped maps are verified through their `toList`.

The operations are `@[expose]`d: consumers check examples by `decide` and `rfl`, which must
evaluate them from other modules.

The lemmas come in two kinds. Those about the operations themselves (`insert`, `erase`, `pred?`,
`succ?`, `rank`) say what each does to a sorted list. Those about `++`
(`List.isSortedAssoc_append_iff`, `lookup_append_of_forall_lt`, `rank_append`, ...) are the
shapes used when a tree node's entry list is split as `first ++ (k, v) :: rest`. Specifying a
search tree by its sorted in-order list and verifying the operations through such splitting
lemmas is the method of Nipkow, *Automatic Functional Correctness Proofs for Functional Search
Trees* (ITP 2016), applied to B-trees by Mündler and Nipkow. The trees this model serves are
those of Bayer and McCreight, *Organization and maintenance of large ordered indexes* (1972), in
the form of Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 18.
-/

public section

universe u v

namespace List

variable {α : Type u} {β : Type v}

section Lookup

variable [DecidableEq α] {l : List (α × β)} {k a : α} {b : β}

/-- Lookup skips an entry with a different key. -/
theorem lookup_cons_of_ne (h : k ≠ a) : List.lookup k ((a, b) :: l) = List.lookup k l := by
  simp [List.lookup_cons, beq_eq_false_iff_ne.2 h]

/-- Lookup fails when no entry carries the key. -/
theorem lookup_eq_none_of_forall_ne (h : ∀ p ∈ l, p.1 ≠ k) : List.lookup k l = none :=
  List.lookup_eq_none_iff.2 fun p hp => by simpa using (h p hp).symm

end Lookup

variable [LinearOrder α]

/-- An association list whose keys are strictly increasing, hence distinct. -/
def IsSortedAssoc (l : List (α × β)) : Prop :=
  (l.map Prod.fst).Pairwise (· < ·)

instance (l : List (α × β)) : Decidable l.IsSortedAssoc :=
  inferInstanceAs (Decidable ((l.map Prod.fst).Pairwise (· < ·)))

variable {l l₁ l₂ : List (α × β)} {k : α} {v : β} {p q : α × β}

/-- `IsSortedAssoc` restated: the key list is strictly increasing. -/
theorem isSortedAssoc_iff_pairwise : l.IsSortedAssoc ↔ (l.map Prod.fst).Pairwise (· < ·) :=
  Iff.rfl

/-- `IsSortedAssoc` restated through Mathlib's `SortedLT`. -/
theorem isSortedAssoc_iff_sortedLT : l.IsSortedAssoc ↔ (l.map Prod.fst).SortedLT :=
  List.sortedLT_iff_pairwise.symm

@[simp] theorem isSortedAssoc_nil : ([] : List (α × β)).IsSortedAssoc := List.Pairwise.nil

/-- A sorted association list is an entry whose key is below every later key, then a sorted
list. -/
@[simp] theorem isSortedAssoc_cons_iff :
    (p :: l).IsSortedAssoc ↔ (∀ q ∈ l, p.1 < q.1) ∧ l.IsSortedAssoc := by
  simp [IsSortedAssoc, List.pairwise_cons]

/-- A concatenation is sorted iff both parts are and every key of the first part is below
every key of the second. -/
@[simp] theorem isSortedAssoc_append_iff :
    (l₁ ++ l₂).IsSortedAssoc ↔
      l₁.IsSortedAssoc ∧ l₂.IsSortedAssoc ∧ ∀ p ∈ l₁, ∀ q ∈ l₂, p.1 < q.1 := by
  simp [IsSortedAssoc, List.pairwise_append]

/-- Splitting a sorted list at a key: the shape of the lemma used at every tree node. -/
theorem isSortedAssoc_append_cons_iff :
    (l₁ ++ (k, v) :: l₂).IsSortedAssoc ↔
      l₁.IsSortedAssoc ∧ l₂.IsSortedAssoc ∧ (∀ p ∈ l₁, p.1 < k) ∧ ∀ p ∈ l₂, k < p.1 := by
  rw [isSortedAssoc_append_iff, isSortedAssoc_cons_iff]
  constructor
  · rintro ⟨h₁, ⟨h₂, hl₂⟩, h₃⟩
    exact ⟨h₁, hl₂, fun p hp => h₃ p hp (k, v) (List.mem_cons_self ..), h₂⟩
  · rintro ⟨h₁, hl₂, h₃, h₂⟩
    refine ⟨h₁, ⟨h₂, hl₂⟩, fun p hp q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h₃ p hp
    · exact (h₃ p hp).trans (h₂ q hq)

/-- A sublist of a sorted association list is sorted. -/
theorem IsSortedAssoc.sublist (h : l₂.IsSortedAssoc) (hs : l₁.Sublist l₂) : l₁.IsSortedAssoc :=
  List.Pairwise.sublist (hs.map Prod.fst) h

/-- Filtering a sorted association list keeps it sorted. -/
theorem IsSortedAssoc.filter (f : α × β → Bool) (h : l.IsSortedAssoc) :
    (l.filter f).IsSortedAssoc :=
  h.sublist List.filter_sublist

/-- Keys are distinct: two entries of a sorted list with the same key are the same entry. -/
theorem IsSortedAssoc.eq_of_mem_of_mem (h : l.IsSortedAssoc) (hp : p ∈ l) (hq : q ∈ l)
    (hk : p.1 = q.1) : p = q := by
  induction l with
  | nil => simp at hp
  | cons a l ih =>
    rw [isSortedAssoc_cons_iff] at h
    rcases List.mem_cons.1 hp with rfl | hp' <;> rcases List.mem_cons.1 hq with rfl | hq'
    · rfl
    · exact absurd hk (h.1 q hq').ne
    · exact absurd hk.symm (h.1 p hp').ne
    · exact ih h.2 hp' hq'

/-- The head of a sorted association list is its entry of least key. -/
theorem IsSortedAssoc.head?_eq_some_iff (h : l.IsSortedAssoc) :
    l.head? = some p ↔ p ∈ l ∧ ∀ q ∈ l, p.1 ≤ q.1 := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [isSortedAssoc_cons_iff] at h
    simp only [List.head?_cons, Option.some.injEq, List.mem_cons]
    constructor
    · rintro rfl
      refine ⟨Or.inl rfl, fun q hq => ?_⟩
      rcases hq with rfl | hq
      · exact le_rfl
      · exact (h.1 q hq).le
    · rintro ⟨hp, hle⟩
      rcases hp with rfl | hp
      · rfl
      · exact absurd (hle a (Or.inl rfl)) (not_le.2 (h.1 p hp))

/-- The last entry of a sorted association list is its entry of greatest key. -/
theorem IsSortedAssoc.getLast?_eq_some_iff (h : l.IsSortedAssoc) :
    l.getLast? = some p ↔ p ∈ l ∧ ∀ q ∈ l, q.1 ≤ p.1 := by
  have aux : ∀ {b : α × β}, l.getLast? = some b → b ∈ l ∧ ∀ q ∈ l, q.1 ≤ b.1 := by
    intro b hb
    obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.1 hb
    rw [isSortedAssoc_append_iff] at h
    refine ⟨List.mem_append_right _ (List.mem_singleton_self _), fun q hq => ?_⟩
    rcases List.mem_append.1 hq with hq | hq
    · exact (h.2.2 q hq b (List.mem_singleton_self _)).le
    · rw [List.mem_singleton.1 hq]
  refine ⟨aux, fun ⟨hp, hle⟩ => ?_⟩
  obtain ⟨b, hb⟩ : ∃ b, l.getLast? = some b :=
    Option.isSome_iff_exists.1 (by simpa using List.ne_nil_of_mem hp)
  obtain ⟨hbl, hble⟩ := aux hb
  rw [hb, h.eq_of_mem_of_mem hbl hp (le_antisymm (hle b hbl) (hble p hp))]

end List

namespace EpsilonEridani.SortedAssoc

variable {α : Type u} {β : Type v}

/-! ### Erasure

Erasure and its unconditional laws need only decidable equality of keys. -/

section Erase

variable [DecidableEq α] {l l₁ l₂ : List (α × β)} {k k' : α} {p : α × β}

/-- Remove every entry with key `k`; on a sorted list there is at most one. -/
@[expose] def erase (k : α) (l : List (α × β)) : List (α × β) :=
  l.filter fun p => p.1 ≠ k

theorem erase_def : erase k l = l.filter fun p => p.1 ≠ k := rfl

@[simp] theorem erase_nil : erase k ([] : List (α × β)) = [] := rfl

theorem erase_cons : erase k (p :: l) = if p.1 = k then erase k l else p :: erase k l := by
  unfold erase
  rw [List.filter_cons]
  by_cases hp : p.1 = k <;> simp [hp]

@[simp] theorem erase_append : erase k (l₁ ++ l₂) = erase k l₁ ++ erase k l₂ := by
  unfold erase
  exact List.filter_append l₁ l₂

@[simp] theorem mem_erase_iff : p ∈ erase k l ↔ p ∈ l ∧ p.1 ≠ k := by
  simp [erase, List.mem_filter]

/-- Erasing a key that no entry carries is the identity. -/
theorem erase_of_forall_ne (h : ∀ p ∈ l, p.1 ≠ k) : erase k l = l :=
  List.filter_eq_self.2 fun p hp => by simpa using h p hp

/-- Lookup of the erased key fails, on any list. -/
@[simp] theorem lookup_erase_self : List.lookup k (erase k l) = none :=
  List.lookup_eq_none_of_forall_ne fun _ hp => (mem_erase_iff.1 hp).2

/-- Erasure does not change lookup at other keys, on any list. -/
@[simp] theorem lookup_erase_of_ne (hne : k' ≠ k) :
    List.lookup k' (erase k l) = List.lookup k' l := by
  rcases hl : List.lookup k' l with _ | w
  · exact List.Sublist.lookup_eq_none List.filter_sublist hl
  · obtain ⟨l₁, l₂, rfl, hl₁⟩ := List.lookup_eq_some_iff.1 hl
    refine List.lookup_eq_some_iff.2
      ⟨erase k l₁, erase k l₂, ?_, fun p hp => hl₁ p (mem_erase_iff.1 hp).1⟩
    simp [erase_cons, hne]

/-- Erasing an absent key is the identity. -/
@[simp] theorem erase_of_lookup_eq_none (h : List.lookup k l = none) : erase k l = l :=
  erase_of_forall_ne fun p hp => (bne_iff_ne.1 (List.lookup_eq_none_iff.1 h p hp)).symm

end Erase

variable [LinearOrder α]

/-- Insert `(k, v)` before the first entry whose key is at least `k`, replacing that entry if
its key is `k`. On a sorted list this is insert-or-replace at the sorted position. -/
@[expose] def insert (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k < k' then (k, v) :: (k', v') :: rest
    else if k = k' then (k, v) :: rest
    else (k', v') :: insert k v rest

/-- The last entry with key strictly below `k`. On a sorted list this is the greatest such
entry, the strict predecessor of `k`. -/
@[expose] def pred? (k : α) (l : List (α × β)) : Option (α × β) :=
  (l.filter fun p => p.1 < k).getLast?

/-- The first entry with key strictly above `k`. On a sorted list this is the least such entry,
the strict successor of `k`. -/
@[expose] def succ? (k : α) (l : List (α × β)) : Option (α × β) :=
  (l.filter fun p => k < p.1).head?

/-- Restriction to the entries with keys in the closed interval `[lo, hi]`. -/
@[expose] def range (lo hi : α) (l : List (α × β)) : List (α × β) :=
  l.filter fun p => lo ≤ p.1 ∧ p.1 ≤ hi

/-- The rank of `k`: the number of entries with key strictly below it. -/
@[expose] def rank (k : α) (l : List (α × β)) : ℕ :=
  (l.filter fun p => p.1 < k).length

variable {l l₁ l₂ : List (α × β)} {k k' : α} {v : β} {p q : α × β}

/-! ### Lookup -/

/-- On a sorted list, lookup finds exactly the entries present. -/
theorem lookup_eq_some_iff (h : l.IsSortedAssoc) : List.lookup k l = some v ↔ (k, v) ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    rw [List.isSortedAssoc_cons_iff] at h
    by_cases hk : k = a₁
    · subst hk
      simp only [List.lookup_cons, beq_self_eq_true, Option.some.injEq, List.mem_cons,
        Prod.mk.injEq, true_and]
      constructor
      · rintro rfl
        exact Or.inl rfl
      · rintro (rfl | hm)
        · rfl
        · exact absurd (h.1 _ hm) (lt_irrefl _)
    · rw [List.lookup_cons_of_ne hk]
      simp [hk, ih h.2]

/-- Lookup skips a prefix whose keys are all below the query. -/
theorem lookup_append_of_forall_lt (h : ∀ p ∈ l₁, p.1 < k) :
    List.lookup k (l₁ ++ l₂) = List.lookup k l₂ := by
  rw [List.lookup_append, List.lookup_eq_none_of_forall_ne fun p hp => (h p hp).ne,
    Option.none_or]

/-- Lookup ignores a suffix whose keys are all above the query. -/
theorem lookup_append_of_forall_gt (h : ∀ p ∈ l₂, k < p.1) :
    List.lookup k (l₁ ++ l₂) = List.lookup k l₁ := by
  rw [List.lookup_append, List.lookup_eq_none_of_forall_ne fun p hp => (h p hp).ne',
    Option.or_none]

/-! ### Insertion -/

@[simp] theorem insert_nil : insert k v ([] : List (α × β)) = [(k, v)] := rfl

theorem insert_cons :
    insert k v (p :: l) =
      if k < p.1 then (k, v) :: p :: l else if k = p.1 then (k, v) :: l else p :: insert k v l := by
  obtain ⟨a₁, a₂⟩ := p
  rfl

/-- An entry of `insert k v l` is the new entry or an entry of `l`. -/
theorem eq_or_mem_of_mem_insert (hq : q ∈ insert k v l) : q = (k, v) ∨ q ∈ l := by
  induction l with
  | nil => simpa using hq
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [insert] at hq
    split_ifs at hq with h₁ h₂
    · simpa using hq
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inr (List.mem_cons_self ..)
      · rcases ih hq with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Insertion preserves sortedness. -/
theorem isSortedAssoc_insert (h : l.IsSortedAssoc) : (insert k v l).IsSortedAssoc := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    rw [List.isSortedAssoc_cons_iff] at h
    simp only [insert]
    split_ifs with h₁ h₂
    · rw [List.isSortedAssoc_cons_iff, List.isSortedAssoc_cons_iff]
      refine ⟨fun q hq => ?_, h⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h₁
      · exact h₁.trans (h.1 q hq)
    · subst h₂
      exact List.isSortedAssoc_cons_iff.2 h
    · rw [List.isSortedAssoc_cons_iff]
      refine ⟨fun q hq => ?_, ih h.2⟩
      have hak : a₁ < k := lt_of_le_of_ne (not_lt.1 h₁) (Ne.symm h₂)
      rcases eq_or_mem_of_mem_insert hq with rfl | hq
      · exact hak
      · exact h.1 q hq

/-- The inserted entry is present, on any list. -/
theorem mem_insert_self : (k, v) ∈ insert k v l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [insert]
    split_ifs
    · exact List.mem_cons_self ..
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ ih

/-- An entry with a different key survives insertion, on any list. -/
theorem mem_insert_of_mem (hq : q ∈ l) (hne : q.1 ≠ k) : q ∈ insert k v l := by
  induction l with
  | nil => simp at hq
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [insert]
    split_ifs with h₁ h₂
    · exact List.mem_cons_of_mem _ hq
    · rcases List.mem_cons.1 hq with rfl | hq'
      · exact absurd h₂.symm hne
      · exact List.mem_cons_of_mem _ hq'
    · rcases List.mem_cons.1 hq with rfl | hq'
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hq')

/-- On a sorted list, the entries after insertion are the new entry and the old entries with
other keys. -/
theorem mem_insert_iff (h : l.IsSortedAssoc) :
    q ∈ insert k v l ↔ q = (k, v) ∨ q ∈ l ∧ q.1 ≠ k := by
  constructor
  · intro hq
    rcases eq_or_mem_of_mem_insert hq with rfl | hql
    · exact Or.inl rfl
    · by_cases hk : q.1 = k
      · exact Or.inl ((isSortedAssoc_insert h).eq_of_mem_of_mem hq mem_insert_self hk)
      · exact Or.inr ⟨hql, hk⟩
  · rintro (rfl | ⟨hql, hk⟩)
    · exact mem_insert_self
    · exact mem_insert_of_mem hql hk

/-- Lookup of the inserted key finds the new value, on any list. -/
@[simp] theorem lookup_insert_self : List.lookup k (insert k v l) = some v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [insert]
    split_ifs with h₁ h₂
    · simp
    · simp
    · rw [List.lookup_cons_of_ne h₂, ih]

/-- Insertion does not change lookup at other keys, on any list. -/
@[simp] theorem lookup_insert_of_ne (hne : k' ≠ k) :
    List.lookup k' (insert k v l) = List.lookup k' l := by
  induction l with
  | nil => simp [List.lookup_cons_of_ne hne]
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    simp only [insert]
    split_ifs with h₁ h₂
    · rw [List.lookup_cons_of_ne hne]
    · subst h₂
      rw [List.lookup_cons_of_ne hne, List.lookup_cons_of_ne hne]
    · by_cases hka : k' = a₁
      · subst hka
        simp
      · rw [List.lookup_cons_of_ne hka, List.lookup_cons_of_ne hka, ih]

/-- On a sorted list, insertion keeps the length if the key was present and adds one
otherwise. -/
theorem length_insert (h : l.IsSortedAssoc) :
    (insert k v l).length = if (List.lookup k l).isSome then l.length else l.length + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    rw [List.isSortedAssoc_cons_iff] at h
    by_cases h₁ : k < a₁
    · have hnone : List.lookup k ((a₁, a₂) :: l) = none := by
        refine List.lookup_eq_none_of_forall_ne fun p hp => ?_
        rcases List.mem_cons.1 hp with rfl | hp
        · exact h₁.ne'
        · exact (h₁.trans (h.1 p hp)).ne'
      simp [insert, h₁, hnone]
    · by_cases h₂ : k = a₁
      · subst h₂
        simp [insert]
      · simp only [insert, h₁, h₂, ↓reduceIte, List.length_cons, ih h.2,
          List.lookup_cons_of_ne h₂]
        split_ifs <;> rfl

/-! ### Erasure on sorted lists -/

/-- Erasure preserves sortedness. -/
theorem isSortedAssoc_erase (h : l.IsSortedAssoc) : (erase k l).IsSortedAssoc :=
  h.filter _

/-- On a sorted list, erasure removes one entry if the key was present and none otherwise. -/
theorem length_erase (h : l.IsSortedAssoc) :
    (erase k l).length = if (List.lookup k l).isSome then l.length - 1 else l.length := by
  split_ifs with hk
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hk
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 hw
    rw [List.isSortedAssoc_append_cons_iff] at h
    rw [erase_append, erase_cons, erase_of_forall_ne fun p hp => (h.2.2.1 p hp).ne,
      erase_of_forall_ne fun p hp => (h.2.2.2 p hp).ne']
    simp
  · rw [erase_of_lookup_eq_none (Option.not_isSome_iff_eq_none.1 hk)]

/-! ### Predecessor and successor -/

theorem pred?_def : pred? k l = (l.filter fun p => p.1 < k).getLast? := rfl

@[simp] theorem pred?_nil : pred? k ([] : List (α × β)) = none := rfl

theorem succ?_def : succ? k l = (l.filter fun p => k < p.1).head? := rfl

@[simp] theorem succ?_nil : succ? k ([] : List (α × β)) = none := rfl

/-- There is no predecessor iff every key is at least `k`, on any list. -/
@[simp] theorem pred?_eq_none_iff : pred? k l = none ↔ ∀ q ∈ l, k ≤ q.1 := by
  simp [pred?]

/-- There is no successor iff every key is at most `k`, on any list. -/
@[simp] theorem succ?_eq_none_iff : succ? k l = none ↔ ∀ q ∈ l, q.1 ≤ k := by
  simp [succ?]

/-- On a sorted list, `pred? k` is the greatest entry with key below `k`. -/
theorem pred?_eq_some_iff (h : l.IsSortedAssoc) :
    pred? k l = some p ↔ p ∈ l ∧ p.1 < k ∧ ∀ q ∈ l, q.1 < k → q.1 ≤ p.1 := by
  rw [pred?, (h.filter _).getLast?_eq_some_iff]
  simp [List.mem_filter, and_assoc]

/-- On a sorted list, `succ? k` is the least entry with key above `k`. -/
theorem succ?_eq_some_iff (h : l.IsSortedAssoc) :
    succ? k l = some p ↔ p ∈ l ∧ k < p.1 ∧ ∀ q ∈ l, k < q.1 → p.1 ≤ q.1 := by
  rw [succ?, (h.filter _).head?_eq_some_iff]
  simp [List.mem_filter, and_assoc]

/-! ### Range and rank -/

theorem range_def {lo hi : α} : range lo hi l = l.filter fun p => lo ≤ p.1 ∧ p.1 ≤ hi := rfl

@[simp] theorem range_nil {lo hi : α} : range lo hi ([] : List (α × β)) = [] := rfl

theorem rank_def : rank k l = (l.filter fun p => p.1 < k).length := rfl

@[simp] theorem rank_nil : rank k ([] : List (α × β)) = 0 := rfl

/-- An entry is in the range restriction iff it is in the list with key in `[lo, hi]`. -/
@[simp] theorem mem_range_iff {lo hi : α} :
    p ∈ range lo hi l ↔ p ∈ l ∧ lo ≤ p.1 ∧ p.1 ≤ hi := by
  simp [range, List.mem_filter]

/-- Range restriction preserves sortedness. -/
theorem isSortedAssoc_range {lo hi : α} (h : l.IsSortedAssoc) :
    (range lo hi l).IsSortedAssoc :=
  h.filter _

/-- Range restriction distributes over concatenation. -/
@[simp] theorem range_append {lo hi : α} :
    range lo hi (l₁ ++ l₂) = range lo hi l₁ ++ range lo hi l₂ := by
  unfold range
  exact List.filter_append l₁ l₂

/-- Rank is additive over concatenation. -/
@[simp] theorem rank_append : rank k (l₁ ++ l₂) = rank k l₁ + rank k l₂ := by
  simp [rank, List.filter_append]

/-- On a sorted list, the rank is the length of the prefix of keys below `k`. -/
theorem rank_eq_length_takeWhile (h : l.IsSortedAssoc) :
    rank k l = (l.takeWhile fun p => decide (p.1 < k)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.isSortedAssoc_cons_iff] at h
    rw [rank, List.filter_cons, List.takeWhile_cons]
    by_cases ha : a.1 < k
    · simp only [ha, decide_true, ↓reduceIte, List.length_cons]
      rw [← rank, ih h.2]
    · have hnil : l.filter (fun p => decide (p.1 < k)) = [] :=
        List.filter_eq_nil_iff.2 fun q hq => by
          simpa using not_lt.2 ((not_lt.1 ha).trans (h.1 q hq).le)
      simp [ha, hnil]

/-! ### Examples -/

example : insert 2 20 [(1, 10), (3, 30)] = [(1, 10), (2, 20), (3, 30)] := by decide
example : insert 3 31 [(1, 10), (3, 30)] = [(1, 10), (3, 31)] := by decide
example : erase 3 [(1, 10), (3, 30)] = [(1, 10)] := by decide
example : List.lookup 3 [(1, 10), (3, 30)] = some 30 := by decide
example : List.lookup 2 [(1, 10), (3, 30)] = none := by decide
example : range 2 2 [(1, 10), (2, 20), (3, 30)] = [(2, 20)] := by decide
example : range 3 2 [(1, 10), (2, 20), (3, 30)] = [] := by decide
example : pred? 3 [(1, 10), (2, 20), (3, 30)] = some (2, 20) := by decide
example : succ? 3 [(1, 10), (2, 20), (3, 30)] = none := by decide
example : rank 3 [(1, 10), (2, 20), (3, 30)] = 2 := by decide
example : [(1, 10), (2, 20)].IsSortedAssoc := by decide
example : ¬ [(2, 20), (2, 21)].IsSortedAssoc := by decide
example : insert 2 "b" [(1, "a"), (3, "c")] = [(1, "a"), (2, "b"), (3, "c")] := by decide

end EpsilonEridani.SortedAssoc
