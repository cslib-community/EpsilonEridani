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
increasing, so that keys are distinct. The model operations are plain list functions. Lookup is
`List.lookup`; insertion replaces an existing key; erasure, minimum, maximum, strict predecessor
and successor, closed-interval restriction, and rank are defined here and are the reference
semantics against which tree-shaped maps are verified through their `toList`.

Sortedness is stated as `List.Pairwise (· < ·)` on the key list, which is the form that the
splitting and concatenation lemmas consume. Mathlib's `List.SortedLT` is the same predicate by
`List.sortedLT_iff_pairwise`.

The lemmas come in two kinds. Those about the model operations themselves (`insert`, `erase`,
`pred?`, `succ?`, `rank`) say what each operation does to a sorted list. Those about `++`
(`isSortedAssoc_append_iff`, `lookup_append_of_forall_lt`, `rank_append`, ...) are the shapes
used when a tree node's entry list is split as `first ++ (k, v) :: rest`, following the
treatment of search trees as sorted sequences in Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms*, Chapter 18, and Bayer and McCreight, *Organization and maintenance
of large ordered indexes* (1972).
-/

public section

namespace EpsilonEridani.SortedAssoc

universe u v

variable {α : Type u} {β : Type v} [LinearOrder α]

/-- Keys strictly increasing, hence distinct. -/
def IsSortedAssoc (l : List (α × β)) : Prop :=
  (l.map Prod.fst).Pairwise (· < ·)

instance (l : List (α × β)) : Decidable (IsSortedAssoc l) :=
  inferInstanceAs (Decidable ((l.map Prod.fst).Pairwise (· < ·)))

/-- Lookup is `List.lookup`; the model does not introduce a second lookup. -/
abbrev lookup (k : α) (l : List (α × β)) : Option β :=
  List.lookup k l

/-- Insert-or-replace at the sorted position. -/
@[expose] def insert (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k < k' then (k, v) :: (k', v') :: rest
    else if k = k' then (k, v) :: rest
    else (k', v') :: insert k v rest

/-- Remove the entry with key `k`, if any. -/
@[expose] def erase (k : α) (l : List (α × β)) : List (α × β) :=
  l.filter fun p => p.1 ≠ k

/-- The entry with least key. -/
abbrev min? (l : List (α × β)) : Option (α × β) := l.head?

/-- The entry with greatest key. -/
abbrev max? (l : List (α × β)) : Option (α × β) := l.getLast?

/-- The greatest entry with key strictly below `k`. -/
@[expose] def pred? (k : α) (l : List (α × β)) : Option (α × β) :=
  (l.filter fun p => p.1 < k).getLast?

/-- The least entry with key strictly above `k`. -/
@[expose] def succ? (k : α) (l : List (α × β)) : Option (α × β) :=
  (l.filter fun p => k < p.1).head?

/-- Restriction to the closed key interval `[lo, hi]`. -/
@[expose] def range (lo hi : α) (l : List (α × β)) : List (α × β) :=
  l.filter fun p => lo ≤ p.1 ∧ p.1 ≤ hi

/-- The rank of `k`: the number of keys strictly below it. -/
@[expose] def rank (k : α) (l : List (α × β)) : ℕ :=
  (l.filter fun p => p.1 < k).length

variable {l l₁ l₂ : List (α × β)} {k k' : α} {v : β} {p q : α × β}

/-! ### Sortedness: structural lemmas -/

@[simp] theorem isSortedAssoc_nil : IsSortedAssoc ([] : List (α × β)) := List.Pairwise.nil

theorem isSortedAssoc_cons_iff :
    IsSortedAssoc (p :: l) ↔ (∀ q ∈ l, p.1 < q.1) ∧ IsSortedAssoc l := by
  simp [IsSortedAssoc, List.pairwise_cons]

theorem isSortedAssoc_append_iff :
    IsSortedAssoc (l₁ ++ l₂) ↔
      IsSortedAssoc l₁ ∧ IsSortedAssoc l₂ ∧ ∀ p ∈ l₁, ∀ q ∈ l₂, p.1 < q.1 := by
  simp [IsSortedAssoc, List.pairwise_append]

/-- Splitting a sorted list at a key: the shape of the lemma used at every tree node. -/
theorem isSortedAssoc_append_cons_iff :
    IsSortedAssoc (l₁ ++ (k, v) :: l₂) ↔
      IsSortedAssoc l₁ ∧ IsSortedAssoc l₂ ∧ (∀ p ∈ l₁, p.1 < k) ∧ ∀ p ∈ l₂, k < p.1 := by
  rw [isSortedAssoc_append_iff, isSortedAssoc_cons_iff]
  constructor
  · rintro ⟨h₁, ⟨h₂, hl₂⟩, h₃⟩
    exact ⟨h₁, hl₂, fun p hp => h₃ p hp (k, v) (List.mem_cons_self ..), h₂⟩
  · rintro ⟨h₁, hl₂, h₃, h₂⟩
    refine ⟨h₁, ⟨h₂, hl₂⟩, fun p hp q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact h₃ p hp
    · exact (h₃ p hp).trans (h₂ q hq)

theorem IsSortedAssoc.sublist (h : IsSortedAssoc l₂) (hs : l₁.Sublist l₂) : IsSortedAssoc l₁ :=
  List.Pairwise.sublist (hs.map Prod.fst) h

/-- Keys are distinct: two entries of a sorted list with the same key are the same entry. -/
theorem IsSortedAssoc.eq_of_mem_of_mem (h : IsSortedAssoc l) (hp : p ∈ l) (hq : q ∈ l)
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

/-! ### Lookup -/

theorem lookup_eq_some_iff (h : IsSortedAssoc l) : lookup k l = some v ↔ (k, v) ∈ l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    rw [isSortedAssoc_cons_iff] at h
    by_cases hk : k = a₁
    · subst hk
      simp only [lookup, List.lookup_cons, beq_self_eq_true, Option.some.injEq, List.mem_cons,
        Prod.mk.injEq, true_and]
      constructor
      · rintro rfl
        exact Or.inl rfl
      · rintro (rfl | hm)
        · rfl
        · exact absurd (h.1 _ hm) (lt_irrefl _)
    · have hb : (k == a₁) = false := beq_eq_false_iff_ne.2 hk
      simp [lookup, List.lookup_cons, hb, hk, ih h.2]

theorem lookup_append_of_forall_lt (h : ∀ p ∈ l₁, p.1 < k) :
    lookup k (l₁ ++ l₂) = lookup k l₂ := by
  have h₁ : List.lookup k l₁ = none :=
    List.lookup_eq_none_iff.2 fun p hp => by simpa using (h p hp).ne'
  rw [lookup, List.lookup_append, h₁, Option.none_or]

theorem lookup_append_of_forall_gt (h : ∀ p ∈ l₂, k < p.1) :
    lookup k (l₁ ++ l₂) = lookup k l₁ := by
  have h₂ : List.lookup k l₂ = none :=
    List.lookup_eq_none_iff.2 fun p hp => by simpa using (h p hp).ne
  rw [lookup, List.lookup_append, h₂, Option.or_none]

/-! ### Insertion -/

/-- An entry of `insert k v l` is the new entry or an entry of `l`. No sortedness is needed. -/
theorem mem_of_mem_insert (hq : q ∈ insert k v l) : q = (k, v) ∨ q ∈ l := by
  induction l with
  | nil => simpa [insert] using hq
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

theorem isSortedAssoc_insert (h : IsSortedAssoc l) : IsSortedAssoc (insert k v l) := by
  induction l with
  | nil => simp [insert, IsSortedAssoc]
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    rw [isSortedAssoc_cons_iff] at h
    simp only [insert]
    split_ifs with h₁ h₂
    · rw [isSortedAssoc_cons_iff, isSortedAssoc_cons_iff]
      refine ⟨fun q hq => ?_, h⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h₁
      · exact h₁.trans (h.1 q hq)
    · subst h₂
      exact isSortedAssoc_cons_iff.2 h
    · rw [isSortedAssoc_cons_iff]
      refine ⟨fun q hq => ?_, ih h.2⟩
      have hak : a₁ < k := lt_of_le_of_ne (not_lt.1 h₁) (Ne.symm h₂)
      rcases mem_of_mem_insert hq with rfl | hq
      · exact hak
      · exact h.1 q hq

theorem lookup_insert_self (h : IsSortedAssoc l) : lookup k (insert k v l) = some v := by
  induction l with
  | nil => simp [insert]
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    rw [isSortedAssoc_cons_iff] at h
    simp only [insert]
    split_ifs with h₁ h₂
    · simp
    · simp
    · have hb : (k == a₁) = false := beq_eq_false_iff_ne.2 h₂
      simp [lookup, List.lookup_cons, hb, ih h.2]

theorem lookup_insert_of_ne (h : IsSortedAssoc l) (hne : k' ≠ k) :
    lookup k' (insert k v l) = lookup k' l := by
  have hb : (k' == k) = false := beq_eq_false_iff_ne.2 hne
  induction l with
  | nil => simp [insert, hne]
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    rw [isSortedAssoc_cons_iff] at h
    simp only [insert]
    split_ifs with h₁ h₂
    · simp [lookup, List.lookup_cons, hb]
    · subst h₂
      simp [lookup, List.lookup_cons, hb]
    · by_cases hka : k' = a₁
      · subst hka
        simp [lookup]
      · have hb' : (k' == a₁) = false := beq_eq_false_iff_ne.2 hka
        simp [lookup, List.lookup_cons, hb', ih h.2]

theorem length_insert (h : IsSortedAssoc l) :
    (insert k v l).length = if (lookup k l).isSome then l.length else l.length + 1 := by
  induction l with
  | nil => simp [insert]
  | cons a l ih =>
    obtain ⟨a₁, a₂⟩ := a
    rw [isSortedAssoc_cons_iff] at h
    by_cases h₁ : k < a₁
    · have hnone : lookup k ((a₁, a₂) :: l) = none := by
        refine List.lookup_eq_none_iff.2 fun p hp => ?_
        rcases List.mem_cons.1 hp with rfl | hp
        · simpa using h₁.ne
        · simpa using (h₁.trans (h.1 p hp)).ne
      simp [insert, h₁, hnone]
    · by_cases h₂ : k = a₁
      · subst h₂
        simp [insert]
      · have hb : (k == a₁) = false := beq_eq_false_iff_ne.2 h₂
        simp only [insert, h₁, h₂, ↓reduceIte, List.length_cons, ih h.2, lookup, List.lookup_cons,
          hb]
        split_ifs <;> rfl

/-! ### Erasure -/

theorem isSortedAssoc_erase (h : IsSortedAssoc l) : IsSortedAssoc (erase k l) :=
  h.sublist List.filter_sublist

@[simp] theorem lookup_erase_self : lookup k (erase k l) = none :=
  List.lookup_eq_none_iff.2 fun p hp => by
    have := (List.mem_filter.1 hp).2
    simp only [decide_eq_true_eq] at this
    simpa [bne_iff_ne] using this.symm

theorem lookup_erase_of_ne (hne : k' ≠ k) : lookup k' (erase k l) = lookup k' l := by
  rcases hl : lookup k' l with _ | w
  · exact List.Sublist.lookup_eq_none List.filter_sublist hl
  · obtain ⟨l₁, l₂, rfl, hl₁⟩ := List.lookup_eq_some_iff.1 hl
    refine List.lookup_eq_some_iff.2
      ⟨erase k l₁, erase k l₂, ?_, fun p hp => hl₁ p (List.mem_filter.1 hp).1⟩
    simp [erase, hne]

theorem erase_of_lookup_eq_none (h : lookup k l = none) : erase k l = l :=
  List.filter_eq_self.2 fun p hp => by
    have hne : k ≠ p.1 := bne_iff_ne.1 (List.lookup_eq_none_iff.1 h p hp)
    simpa using hne.symm

theorem length_erase (h : IsSortedAssoc l) :
    (erase k l).length = if (lookup k l).isSome then l.length - 1 else l.length := by
  split_ifs with hk
  · obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 hk
    obtain ⟨l₁, l₂, rfl, -⟩ := List.lookup_eq_some_iff.1 hw
    rw [isSortedAssoc_append_cons_iff] at h
    have e₁ : erase k l₁ = l₁ :=
      List.filter_eq_self.2 fun p hp => by simpa using (h.2.2.1 p hp).ne
    have e₂ : erase k l₂ = l₂ :=
      List.filter_eq_self.2 fun p hp => by simpa using (h.2.2.2 p hp).ne'
    unfold erase at e₁ e₂ ⊢
    have hc : decide ((k, w).1 ≠ k) = false := by simp
    rw [List.filter_append, List.filter_cons, e₁, e₂, hc]
    simp only [Bool.false_eq_true, ↓reduceIte, List.length_append, List.length_cons]
    omega
  · rw [erase_of_lookup_eq_none (Option.not_isSome_iff_eq_none.1 hk)]

/-! ### Minimum and maximum -/

theorem min?_eq_some_iff (h : IsSortedAssoc l) :
    min? l = some p ↔ p ∈ l ∧ ∀ q ∈ l, p.1 ≤ q.1 := by
  cases l with
  | nil => simp
  | cons a l =>
    rw [isSortedAssoc_cons_iff] at h
    simp only [min?, List.head?_cons, Option.some.injEq, List.mem_cons]
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

theorem max?_eq_some_iff (h : IsSortedAssoc l) :
    max? l = some p ↔ p ∈ l ∧ ∀ q ∈ l, q.1 ≤ p.1 := by
  have aux : ∀ {b : α × β}, max? l = some b → b ∈ l ∧ ∀ q ∈ l, q.1 ≤ b.1 := by
    intro b hb
    obtain ⟨l', rfl⟩ := List.getLast?_eq_some_iff.1 hb
    rw [isSortedAssoc_append_iff] at h
    refine ⟨List.mem_append_right _ (List.mem_singleton_self _), fun q hq => ?_⟩
    rcases List.mem_append.1 hq with hq | hq
    · exact (h.2.2 q hq b (List.mem_singleton_self _)).le
    · rw [List.mem_singleton.1 hq]
  refine ⟨aux, fun ⟨hp, hle⟩ => ?_⟩
  obtain ⟨b, hb⟩ : ∃ b, max? l = some b :=
    Option.isSome_iff_exists.1 (by simpa [max?] using List.ne_nil_of_mem hp)
  obtain ⟨hbl, hble⟩ := aux hb
  rw [hb, h.eq_of_mem_of_mem hbl hp (le_antisymm (hle b hbl) (hble p hp))]

/-! ### Predecessor and successor -/

theorem pred?_eq_some_iff (h : IsSortedAssoc l) :
    pred? k l = some p ↔ p ∈ l ∧ p.1 < k ∧ ∀ q ∈ l, q.1 < k → q.1 ≤ p.1 := by
  have hf : IsSortedAssoc (l.filter fun p => p.1 < k) := h.sublist List.filter_sublist
  rw [pred?, ← max?, max?_eq_some_iff hf]
  simp [List.mem_filter, and_assoc]

theorem succ?_eq_some_iff (h : IsSortedAssoc l) :
    succ? k l = some p ↔ p ∈ l ∧ k < p.1 ∧ ∀ q ∈ l, k < q.1 → p.1 ≤ q.1 := by
  have hf : IsSortedAssoc (l.filter fun p => k < p.1) := h.sublist List.filter_sublist
  rw [succ?, ← min?, min?_eq_some_iff hf]
  simp [List.mem_filter, and_assoc]

/-! ### Range and rank -/

@[simp] theorem mem_range_iff {lo hi : α} :
    p ∈ range lo hi l ↔ p ∈ l ∧ lo ≤ p.1 ∧ p.1 ≤ hi := by
  simp [range, List.mem_filter]

@[simp] theorem range_append {lo hi : α} :
    range lo hi (l₁ ++ l₂) = range lo hi l₁ ++ range lo hi l₂ := by
  unfold range
  exact List.filter_append l₁ l₂

@[simp] theorem rank_append : rank k (l₁ ++ l₂) = rank k l₁ + rank k l₂ := by
  simp [rank, List.filter_append]

/-- On a sorted list, the rank is the length of the prefix of keys below `k`. -/
theorem rank_eq_length_takeWhile (h : IsSortedAssoc l) :
    rank k l = (l.takeWhile fun p => decide (p.1 < k)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [isSortedAssoc_cons_iff] at h
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
example : lookup 3 [(1, 10), (3, 30)] = some 30 := by decide
example : lookup 2 [(1, 10), (3, 30)] = none := by decide
example : range 2 2 [(1, 10), (2, 20), (3, 30)] = [(2, 20)] := by decide
example : range 3 2 [(1, 10), (2, 20), (3, 30)] = [] := by decide
example : pred? 3 [(1, 10), (2, 20), (3, 30)] = some (2, 20) := by decide
example : succ? 3 [(1, 10), (2, 20), (3, 30)] = none := by decide
example : rank 3 [(1, 10), (2, 20), (3, 30)] = 2 := by decide
example : IsSortedAssoc [(1, 10), (2, 20)] := by decide
example : ¬ IsSortedAssoc [(2, 20), (2, 21)] := by decide
example : insert 2 "b" [(1, "a"), (3, "c")] = [(1, "a"), (2, "b"), (3, "c")] := by decide

end EpsilonEridani.SortedAssoc
