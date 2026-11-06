/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Height
public import EpsilonEridani.Algorithms.Lean.BTree.Insert

/-!
# Bulk loading of classic B-trees

Building a B-tree of `EpsilonEridani.BTree` from a list of entries in one pass, level by level
from the bottom, in the manner of the bulk loading of Bayer and McCreight, *Organization and
maintenance of large ordered indexes* (1972); the shape invariants are those of Cormen,
Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 18.

A level is a first tree followed by `(key, value, tree)` triples, all of its trees of one
height; the bottom level is the empty leaf and one triple per entry, each with an empty child.
A round cuts the triples of a level into groups of `t - 1` to `2 * t - 1` triples with one
triple between consecutive groups: each group becomes a node one level taller, and each triple
between groups moves up, its child becoming the first child of the next node. `groupSizes`
chooses the sizes of all groups but the last, with one look ahead: a group of `2 * t - 1`
unless that would leave fewer than `t - 1` triples for the rest, then one of `t - 1`. `packM`
cuts a level by a list of sizes, and `buildM` runs rounds until at most `2 * t - 1` triples are
left, which become the root. Below `2` the loader uses minimum degree `2`, so that every node
built holds a key.

Each operation is defined once over an arbitrary monad `m`, with a node-visit action
`visit : m Unit` that fires once per node built; no comparator is needed, since the input order
is kept. The pure operations `pack`, `build` and `ofSortedList` are the `Id` instantiations with
`visit := pure ()`. All recursion is structural, on a fuel argument or on the list of sizes, so
the definitions are `@[expose]`d and `decide` evaluates bulk loading on concrete inputs; when the
fuel runs out, the remaining level becomes a single node, which keeps the entries.

`toList_ofSortedList` states that bulk loading keeps the entries in order, for every list.
Costs are not stated here.
-/

public section

universe w

namespace EpsilonEridani.BTree

/-- The sizes of all groups but the last when the `r` triples of a level are cut into groups of
`t - 1` to `2 * t - 1` triples with one triple between groups, with recursion bounded by `fuel`.
A group has `2 * t - 1` triples unless that would leave fewer than `t - 1`, then `t - 1`. -/
@[expose] def groupSizes (t : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, r =>
    if r ≤ 2 * t - 1 then []
    else
      let s := if r < 3 * t - 1 then t - 1 else 2 * t - 1
      s :: groupSizes t fuel (r - s - 1)

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

/-- Cut a level by a list of group sizes: the node over the first group, and the next level's
triples, each a key moved up with the node over the following group. The last group takes the
remaining triples. `visit` fires once per node built. -/
@[expose] def packM (visit : m Unit) (first : BTree α β) (rest : List (α × β × BTree α β)) :
    List ℕ → m (BTree α β × List (α × β × BTree α β))
  | [] => do visit; pure (.node first rest, [])
  | s :: ss =>
    match rest.drop s with
    | [] => do visit; pure (.node first rest, [])
    | (k, v, c) :: rest' => do
      visit
      let p ← packM visit c rest' ss
      pure (.node first (rest.take s), (k, v, p.1) :: p.2)

/-- With no sizes left, the whole level is one node. -/
@[simp] theorem packM_nil (visit : m Unit) (first : BTree α β)
    (rest : List (α × β × BTree α β)) :
    packM visit first rest [] = (do visit; pure (.node first rest, [])) := rfl

/-- A group of `s` triples becomes a node, and the triple after it moves up over the rest. -/
theorem packM_cons (visit : m Unit) (first : BTree α β) (rest : List (α × β × BTree α β))
    (s : ℕ) (ss : List ℕ) :
    packM visit first rest (s :: ss) =
      (match rest.drop s with
      | [] => do visit; pure (.node first rest, [])
      | (k, v, c) :: rest' => do
        visit
        let p ← packM visit c rest' ss
        pure (.node first (rest.take s), (k, v, p.1) :: p.2)) := rfl

/-- Rounds of bulk loading at minimum degree `t`, at most `fuel` of them: a level with no
triples is its first tree, a level with at most `2 * t - 1` triples becomes the root, and a
longer one is cut by `groupSizes` into the next level. Out of fuel, the level becomes one
node. -/
@[expose] def buildM (t : ℕ) (visit : m Unit) :
    ℕ → BTree α β → List (α × β × BTree α β) → m (BTree α β)
  | _, first, [] => pure first
  | fuel, first, e :: es =>
    if (e :: es).length ≤ 2 * t - 1 then do visit; pure (.node first (e :: es))
    else
      match fuel with
      | 0 => do visit; pure (.node first (e :: es))
      | fuel + 1 => do
        let p ← packM visit first (e :: es) (groupSizes t (e :: es).length (e :: es).length)
        buildM t visit fuel p.1 p.2

/-- A level with no triples is its first tree. -/
@[simp] theorem buildM_nil (t : ℕ) (visit : m Unit) (fuel : ℕ) (first : BTree α β) :
    buildM t visit fuel first [] = pure first := by
  cases fuel <;> rfl

/-- A round of bulk loading on a level with triples. -/
theorem buildM_cons (t : ℕ) (visit : m Unit) (fuel : ℕ) (first : BTree α β)
    (e : α × β × BTree α β) (es : List (α × β × BTree α β)) :
    buildM t visit fuel first (e :: es) =
      (if (e :: es).length ≤ 2 * t - 1 then do visit; pure (.node first (e :: es))
      else
        match fuel with
        | 0 => do visit; pure (.node first (e :: es))
        | fuel + 1 => do
          let p ← packM visit first (e :: es) (groupSizes t (e :: es).length (e :: es).length)
          buildM t visit fuel p.1 p.2) := by
  cases fuel <;> rfl

/-- Bulk loading at minimum degree `t`, or `2` when `t` is below `2`: the rounds of `buildM`
from the bottom level of empty children, with fuel the number of entries. -/
@[expose] def ofSortedListM (t : ℕ) (visit : m Unit) (l : List (α × β)) : m (BTree α β) :=
  buildM (max t 2) visit l.length .leaf (l.map fun p => (p.1, p.2, .leaf))

/-- Bulk loading runs the rounds of `buildM` at minimum degree `max t 2`. -/
theorem ofSortedListM_def (t : ℕ) (visit : m Unit) (l : List (α × β)) :
    ofSortedListM t visit l =
      buildM (max t 2) visit l.length .leaf (l.map fun p => (p.1, p.2, .leaf)) := rfl

/-- Bulk loading the empty list builds the empty tree, without a visit. -/
@[simp] theorem ofSortedListM_nil (t : ℕ) (visit : m Unit) :
    ofSortedListM t visit ([] : List (α × β)) = pure .leaf := rfl

end Polymorphic

section Pure

variable {α β : Type} {t : ℕ}

/-- Pure cutting of a level by a list of group sizes. -/
@[expose] def pack (first : BTree α β) (rest : List (α × β × BTree α β)) (ss : List ℕ) :
    BTree α β × List (α × β × BTree α β) :=
  Id.run (packM (pure ()) first rest ss)

/-- Pure rounds of bulk loading. -/
@[expose] def build (t fuel : ℕ) (first : BTree α β) (rest : List (α × β × BTree α β)) :
    BTree α β :=
  Id.run (buildM t (pure ()) fuel first rest)

/-- Pure bulk loading. -/
@[expose] def ofSortedList (t : ℕ) (l : List (α × β)) : BTree α β :=
  Id.run (ofSortedListM t (pure ()) l)

/-- `pack` is the `Id` instantiation of `packM`. -/
theorem pack_def (first : BTree α β) (rest : List (α × β × BTree α β)) (ss : List ℕ) :
    pack first rest ss = Id.run (packM (pure ()) first rest ss) := (rfl)

/-- `build` is the `Id` instantiation of `buildM`. -/
theorem build_def (fuel : ℕ) (first : BTree α β) (rest : List (α × β × BTree α β)) :
    build t fuel first rest = Id.run (buildM t (pure ()) fuel first rest) := (rfl)

/-- `ofSortedList` is the `Id` instantiation of `ofSortedListM`. -/
theorem ofSortedList_def (l : List (α × β)) :
    ofSortedList t l = Id.run (ofSortedListM t (pure ()) l) := (rfl)

/-- With no sizes left, the whole level is one node. -/
@[simp] theorem pack_nil (first : BTree α β) (rest : List (α × β × BTree α β)) :
    pack first rest [] = (.node first rest, []) := rfl

/-- Cutting at a size beyond the level leaves the whole level as one node. -/
theorem pack_cons_of_drop_eq_nil {first : BTree α β} {rest : List (α × β × BTree α β)} {s : ℕ}
    (ss : List ℕ) (h : rest.drop s = []) : pack first rest (s :: ss) = (.node first rest, []) := by
  -- `pack` unfolds through `Id` to the `match` of `packM_cons`
  simp only [pack, packM_cons, h]
  rfl

/-- A group of `s` triples becomes a node, and the triple after it moves up over the rest. -/
theorem pack_cons_of_drop_eq_cons {first : BTree α β} {rest : List (α × β × BTree α β)} {s : ℕ}
    {k : α} {v : β} {c : BTree α β} {rest' : List (α × β × BTree α β)} (ss : List ℕ)
    (h : rest.drop s = (k, v, c) :: rest') :
    pack first rest (s :: ss) =
      (.node first (rest.take s), (k, v, (pack c rest' ss).1) :: (pack c rest' ss).2) := by
  -- `pack` unfolds through `Id` to the `match` of `packM_cons`
  simp only [pack, packM_cons, h]
  rfl

/-- A level with no triples is its first tree. -/
@[simp] theorem build_nil (fuel : ℕ) (first : BTree α β) : build t fuel first [] = first := by
  simp [build]

/-- A level of at most `2 * t - 1` triples becomes the root. -/
theorem build_of_length_le {fuel : ℕ} {first : BTree α β} {rest : List (α × β × BTree α β)}
    (hne : rest ≠ []) (h : rest.length ≤ 2 * t - 1) :
    build t fuel first rest = .node first rest := by
  obtain ⟨e, es, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [build, buildM_cons, h, ↓reduceIte]
  rfl

/-- Out of fuel, a level of more than `2 * t - 1` triples becomes one node. -/
theorem build_zero_of_lt {first : BTree α β} {rest : List (α × β × BTree α β)}
    (h : 2 * t - 1 < rest.length) : build t 0 first rest = .node first rest := by
  obtain ⟨e, es, rfl⟩ :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (Nat.zero_lt_of_lt h))
  simp only [build, buildM_cons, Nat.not_le.2 h, ↓reduceIte]
  rfl

/-- A level of more than `2 * t - 1` triples is cut by `groupSizes` into the next level. -/
theorem build_succ_of_lt {fuel : ℕ} {first : BTree α β} {rest : List (α × β × BTree α β)}
    (h : 2 * t - 1 < rest.length) :
    build t (fuel + 1) first rest =
      build t fuel (pack first rest (groupSizes t rest.length rest.length)).1
        (pack first rest (groupSizes t rest.length rest.length)).2 := by
  obtain ⟨e, es, rfl⟩ :=
    List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (Nat.zero_lt_of_lt h))
  simp only [build, buildM_cons, Nat.not_le.2 h, ↓reduceIte]
  rfl

/-- Bulk loading runs the rounds of `build` at minimum degree `max t 2`. -/
theorem ofSortedList_eq_build (l : List (α × β)) :
    ofSortedList t l = build (max t 2) l.length .leaf (l.map fun p => (p.1, p.2, .leaf)) := rfl

/-- Bulk loading the empty list builds the empty tree. -/
@[simp] theorem ofSortedList_nil : ofSortedList t ([] : List (α × β)) = .leaf := rfl

/-! ### Entries -/

/-- Cutting a level keeps its entries in order. -/
theorem toList_pack (first : BTree α β) (rest : List (α × β × BTree α β)) (ss : List ℕ) :
    (pack first rest ss).1.toList ++ toListRest (pack first rest ss).2 =
      first.toList ++ toListRest rest := by
  induction ss generalizing first rest with
  | nil => simp
  | cons s ss ih =>
    rcases h : rest.drop s with _ | ⟨⟨k, v, c⟩, rest'⟩
    · rw [pack_cons_of_drop_eq_nil ss h]
      simp
    · rw [pack_cons_of_drop_eq_cons ss h]
      have hr : rest = rest.take s ++ (k, v, c) :: rest' := by
        rw [← h, List.take_append_drop]
      have := ih c rest'
      simp only [toListRest_eq_flatMap] at this
      conv_rhs => rw [hr]
      simp only [toList_node, toListRest_eq_flatMap, List.flatMap_cons, List.flatMap_append,
        List.cons_append, List.append_assoc, ← this]

/-- The rounds of bulk loading keep the entries of a level in order. -/
theorem toList_build (fuel : ℕ) (first : BTree α β) (rest : List (α × β × BTree α β)) :
    (build t fuel first rest).toList = first.toList ++ toListRest rest := by
  induction fuel generalizing first rest with
  | zero =>
    rcases Nat.lt_or_ge (2 * t - 1) rest.length with h | h
    · rw [build_zero_of_lt h, toList_node]
    · rcases rest with _ | ⟨e, es⟩
      · simp
      · rw [build_of_length_le (List.cons_ne_nil e es) h, toList_node]
  | succ fuel ih =>
    rcases Nat.lt_or_ge (2 * t - 1) rest.length with h | h
    · rw [build_succ_of_lt h, ih, toList_pack]
    · rcases rest with _ | ⟨e, es⟩
      · simp
      · rw [build_of_length_le (List.cons_ne_nil e es) h, toList_node]

/-- The bottom level of bulk loading has the entries of the list. -/
@[simp] theorem toListRest_map_leaf (l : List (α × β)) :
    toListRest (l.map fun p => (p.1, p.2, (.leaf : BTree α β))) = l := by
  induction l with
  | nil => rfl
  | cons p l ih => simpa using ih

/-- Bulk loading keeps the entries in order, for every list and every `t`. -/
@[simp] theorem toList_ofSortedList (t : ℕ) (l : List (α × β)) : (ofSortedList t l).toList = l := by
  rw [ofSortedList_eq_build, toList_build, toListRest_map_leaf, toList_leaf, List.nil_append]

/-- Bulk loading keeps the number of entries. -/
@[simp] theorem size_ofSortedList (l : List (α × β)) : (ofSortedList t l).size = l.length := by
  rw [size, toList_ofSortedList]

/-- An entry belongs to a bulk-loaded tree exactly when it belongs to the list. -/
@[simp] theorem mem_ofSortedList {l : List (α × β)} {p : α × β} :
    p ∈ ofSortedList t l ↔ p ∈ l := by
  rw [mem_def, toList_ofSortedList]


/-! ### Group sizes -/

/-- `IsGrouping t r ss`: the `r` triples of a level are cut into groups of `t - 1` to
`2 * t - 1` triples with one triple between consecutive groups, the groups but the last having
the sizes `ss`. -/
inductive IsGrouping (t : ℕ) : ℕ → List ℕ → Prop
  /-- The last group, of `t - 1` to `2 * t - 1` triples. -/
  | last {r : ℕ} : t - 1 ≤ r → r ≤ 2 * t - 1 → IsGrouping t r []
  /-- A group of `s` triples, the triple after it, and a grouping of the remaining `r`. -/
  | cut {s r : ℕ} {ss : List ℕ} : t - 1 ≤ s → s ≤ 2 * t - 1 → IsGrouping t r ss →
      IsGrouping t (s + 1 + r) (s :: ss)

/-- `groupSizes` cuts `r` triples, at least `t - 1` of them, into a grouping, given fuel at
least `r`. -/
theorem isGrouping_groupSizes {t fuel r : ℕ} (hr : t - 1 ≤ r) (hf : r ≤ fuel) :
    IsGrouping t r (groupSizes t fuel r) := by
  induction fuel generalizing r with
  | zero => exact .last hr (by omega)
  | succ fuel ih =>
    by_cases h : r ≤ 2 * t - 1
    · simp only [groupSizes, h, ↓reduceIte]
      exact .last hr h
    · simp only [groupSizes, h, ↓reduceIte]
      by_cases h' : r < 3 * t - 1
      · simp only [h', ↓reduceIte]
        have := IsGrouping.cut (t := t) le_rfl (by omega) (ih (r := r - (t - 1) - 1)
          (by omega) (by omega))
        rwa [show t - 1 + 1 + (r - (t - 1) - 1) = r by omega] at this
      · simp only [h', ↓reduceIte]
        have := IsGrouping.cut (t := t) (by omega) le_rfl (ih (r := r - (2 * t - 1) - 1)
          (by omega) (by omega))
        rwa [show 2 * t - 1 + 1 + (r - (2 * t - 1) - 1) = r by omega] at this

/-- At minimum degree at least `2`, a grouping has fewer sizes than triples: every group but the
last takes at least two triples with the one after it, and the last at least one. -/
theorem IsGrouping.length_lt {t r : ℕ} {ss : List ℕ} (ht : 2 ≤ t) (hg : IsGrouping t r ss) :
    ss.length < r := by
  induction hg with
  | last hr _ => simp only [List.length_nil]; omega
  | cut _ _ _ ih => simp only [List.length_cons]; omega

/-! ### Shape -/

/-- A node with `t - 1` to `2 * t - 1` keys over good children of height `h` is good, of height
`h + 1`. -/
theorem good_node {t h : ℕ} {first : BTree α β} {rest : List (α × β × BTree α β)}
    (hf : Good t h first) (hr : ∀ e ∈ rest, Good t h e.2.2) (h₁ : t - 1 ≤ rest.length)
    (h₂ : rest.length ≤ 2 * t - 1) : Good t (h + 1) (.node first rest) :=
  have hn := node_of_good hf hr
  ⟨hn.1, hn.2.1, .node h₁ h₂ hf.occupied fun e he => (hr e he).occupied⟩

/-- A level of height `h`: its first tree and the children of its triples are good, of height
`h`. -/
structure GoodLevel (t h : ℕ) (first : BTree α β) (rest : List (α × β × BTree α β)) : Prop where
  /-- The first tree is good. -/
  good_first : Good t h first
  /-- The child of every triple is good. -/
  good_rest : ∀ e ∈ rest, Good t h e.2.2

/-- Cutting a good level of height `h` by a grouping gives a good level of height `h + 1`, with
one triple per size. -/
theorem GoodLevel.pack {t h r : ℕ} {ss : List ℕ} (hg : IsGrouping t r ss) :
    ∀ {first : BTree α β} {rest : List (α × β × BTree α β)}, GoodLevel t h first rest →
      rest.length = r →
      GoodLevel t (h + 1) (pack first rest ss).1 (pack first rest ss).2 ∧
        (pack first rest ss).2.length = ss.length := by
  induction hg with
  | last h₁ h₂ =>
    intro first rest hl hr
    rw [pack_nil]
    exact ⟨⟨good_node hl.good_first hl.good_rest (by omega) (by omega), by simp⟩, rfl⟩
  | @cut s r ss h₁ h₂ _ ih =>
    intro first rest hl hr
    rcases hd : rest.drop s with _ | ⟨⟨k, v, c⟩, rest'⟩
    · have := congrArg List.length hd
      simp only [List.length_drop, List.length_nil] at this
      omega
    · rw [pack_cons_of_drop_eq_cons ss hd]
      have hmem : ∀ e ∈ rest.drop s, e ∈ rest := fun e he => List.mem_of_mem_drop he
      rw [hd] at hmem
      have hlen := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at hlen
      obtain ⟨hl', hlen'⟩ := ih (first := c) (rest := rest')
        ⟨hl.good_rest _ (hmem _ List.mem_cons_self),
          fun e he => hl.good_rest e (hmem e (List.mem_cons_of_mem _ he))⟩ (by omega)
      refine ⟨⟨good_node hl.good_first (fun e he => hl.good_rest e (List.mem_of_mem_take he))
        (by simp; omega) (by simp; omega), ?_⟩, by simp [hlen']⟩
      rintro e (_ | ⟨_, he⟩)
      exacts [hl'.good_first, hl'.good_rest e he]

variable [LinearOrder α]

/-- A good tree with sorted entries is well-formed at a minimum degree of at least `2`: the
occupancy of a non-root node implies that of a root. -/
theorem Good.isWF {t h : ℕ} {tr : BTree α β} (ht : 2 ≤ t) (hg : Good t h tr)
    (hs : tr.toList.IsSortedAssoc) : IsWF t tr where
  two_le := ht
  rootKeys_le := hg.occupied.rootKeys_le
  rootKeys_pos hne := by have := hg.occupied.le_rootKeys hne; omega
  occupied_of_mem_children _ hc := hg.occupied.of_mem_children hc
  balanced := hg.balanced
  sorted := hs

/-- The rounds of bulk loading build a well-formed tree from a good level with sorted entries,
given fuel at least its number of triples. -/
theorem isWF_build {t h fuel : ℕ} {first : BTree α β} {rest : List (α × β × BTree α β)}
    (ht : 2 ≤ t) (hl : GoodLevel t h first rest) (hfuel : rest.length ≤ fuel)
    (hs : (first.toList ++ toListRest rest).IsSortedAssoc) :
    IsWF t (build t fuel first rest) := by
  induction fuel generalizing h first rest with
  | zero =>
    rcases rest with _ | ⟨e, es⟩
    · simpa using hl.good_first.isWF ht (by simpa using hs)
    · simp at hfuel
  | succ fuel ih =>
    rcases Nat.lt_or_ge (2 * t - 1) rest.length with hlt | hle
    · rw [build_succ_of_lt hlt]
      obtain ⟨hl', hlen⟩ :=
        hl.pack (isGrouping_groupSizes (t := t) (fuel := rest.length) (by omega) le_rfl) rfl
      have hg := isGrouping_groupSizes (t := t) (fuel := rest.length) (r := rest.length)
        (by omega) le_rfl
      exact ih hl' (by have := hg.length_lt ht; omega) (by rwa [toList_pack])
    · rcases rest with _ | ⟨e, es⟩
      · simpa using hl.good_first.isWF ht (by simpa using hs)
      · rw [build_of_length_le (List.cons_ne_nil e es) hle]
        have hn := node_of_good hl.good_first hl.good_rest
        exact ⟨ht, hle, fun _ => by simp, hn.2.2, hn.1, hs⟩

/-- Bulk loading a sorted list builds a well-formed tree at a minimum degree of at least `2`. -/
theorem isWF_ofSortedList {t : ℕ} {l : List (α × β)} (ht : 2 ≤ t) (h : l.IsSortedAssoc) :
    IsWF t (ofSortedList t l) := by
  rw [ofSortedList_eq_build, Nat.max_eq_left ht]
  refine isWF_build ht ⟨⟨.leaf, rfl, .leaf⟩, fun e he => ?_⟩ (by simp)
    (by rwa [toList_leaf, List.nil_append, toListRest_map_leaf])
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
  exact ⟨.leaf, rfl, .leaf⟩

/-- A bulk-loaded tree meets the height bound of well-formed trees. -/
theorem height_ofSortedList_le {t : ℕ} {l : List (α × β)} (ht : 2 ≤ t) (h : l.IsSortedAssoc) :
    (ofSortedList t l).height ≤ Nat.log t ((l.length + 1) / 2) + 1 := by
  simpa using (isWF_ofSortedList ht h).height_le_log

/-- Lookup in a bulk-loaded sorted list is lookup in the list. -/
@[simp] theorem lookup_ofSortedList {t : ℕ} {l : List (α × β)} (h : l.IsSortedAssoc) (k : α) :
    lookup k (ofSortedList t l) = l.lookup k := by
  rw [lookup_eq_of_isSortedAssoc (by simpa using h), toList_ofSortedList]

end Pure

/-! ### Examples -/

example : ofSortedList 2 ([] : List (ℕ × Unit)) = .leaf := rfl

/-- `2 * t - 1 = 3` entries: a single root. -/
example : ofSortedList 2 [(1, ()), (2, ()), (3, ())] =
    .node .leaf [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)] := rfl

/-- Four entries: the look ahead cuts a first group of `t - 1 = 1`. -/
example : ofSortedList 2 [(1, ()), (2, ()), (3, ()), (4, ())] =
    .node (.node .leaf [(1, (), .leaf)])
      [(2, (), .node .leaf [(3, (), .leaf), (4, (), .leaf)])] := rfl

/-- Seven entries: two groups of three, and the key `4` moves up. -/
example : ofSortedList 2 ((List.range' 1 7).map (·, ())) =
    .node (.node .leaf [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])
      [(4, (), .node .leaf [(5, (), .leaf), (6, (), .leaf), (7, (), .leaf)])] := rfl

/-- At `t = 3`, six entries: a first group of `t - 1 = 2`. -/
example : ofSortedList 3 ((List.range' 1 6).map (·, ())) =
    .node (.node .leaf [(1, (), .leaf), (2, (), .leaf)])
      [(3, (), .node .leaf [(4, (), .leaf), (5, (), .leaf), (6, (), .leaf)])] := rfl

/-- Below `2` the loader uses minimum degree `2`. -/
example : ofSortedList 0 ((List.range' 1 7).map (·, ())) =
    ofSortedList 2 ((List.range' 1 7).map (·, ())) := rfl

/-- An unsorted list keeps its order. -/
example : (ofSortedList 2 [(3, ()), (1, ()), (2, ()), (5, ()), (4, ())]).toList =
    [(3, ()), (1, ()), (2, ()), (5, ()), (4, ())] := by decide

/-- The empty tree is well-formed. -/
example : isWF 2 (ofSortedList 2 ([] : List (ℕ × Unit))) = true := by decide

/-- Four entries at `t = 2`: a well-formed tree of two levels. -/
example : isWF 2 (ofSortedList 2 [(1, ()), (2, ()), (3, ()), (4, ())]) = true := by decide

/-- Twenty entries at `t = 2`: three levels, well-formed. -/
example : isWF 2 (ofSortedList 2 ((List.range' 1 20).map (·, ()))) = true := by decide

example : (ofSortedList 2 ((List.range' 1 20).map (·, ()))).height = 3 := by decide

/-- Twenty entries at `t = 3`: well-formed. -/
example : isWF 3 (ofSortedList 3 ((List.range' 1 20).map (·, ()))) = true := by decide

end EpsilonEridani.BTree
