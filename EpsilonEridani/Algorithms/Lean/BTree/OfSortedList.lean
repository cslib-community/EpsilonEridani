/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

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

/-- Bulk loading keeps the entries in order, for every list and every `t`. -/
@[simp] theorem toList_ofSortedList (t : ℕ) (l : List (α × β)) : (ofSortedList t l).toList = l := by
  rw [ofSortedList_eq_build, toList_build]
  induction l with
  | nil => rfl
  | cons p l ih => simpa using ih

/-- Bulk loading keeps the number of entries. -/
@[simp] theorem size_ofSortedList (l : List (α × β)) : (ofSortedList t l).size = l.length := by
  rw [size, toList_ofSortedList]

/-- An entry belongs to a bulk-loaded tree exactly when it belongs to the list. -/
@[simp] theorem mem_ofSortedList {l : List (α × β)} {p : α × β} :
    p ∈ ofSortedList t l ↔ p ∈ l := by
  rw [mem_def, toList_ofSortedList]

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

end EpsilonEridani.BTree
