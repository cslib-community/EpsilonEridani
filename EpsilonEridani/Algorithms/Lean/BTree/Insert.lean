/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Lookup

/-!
# Insertion into classic B-trees

Insert-or-replace in the B-trees of `EpsilonEridani.BTree`, by the bottom-up algorithm of the
functional literature: a recursive call returns either a tree of the same height or an overflow
split around a median entry (`InsertResult`), and the parent absorbs the overflow, splitting in
turn when it then has `2 * t` keys (`InsertResult.ofNode`). An overflow at the root grows a new
root (`InsertResult.toTree`), so the height grows only there. The insertion into the empty tree
overflows at once, which makes the bottom level uniform with the rest. This is the shape of the
classic algorithm of Bayer and McCreight; Cormen, Leiserson, Rivest and Stein, *Introduction to
Algorithms*, Chapter 18, split full nodes pre-emptively on the way down instead.

Each operation is defined once over an arbitrary monad `m`, with a comparator
`le : α → α → m Bool` and a node-visit action `visit : m Unit`, as in `EpsilonEridani.BTree.Lookup`.
`insertOrSplitM` inserts into a subtree and `insertRestM` searches among the triples of a node,
with the scan and the equality test of `lookupM`; `insertM` is the operation. `visit` fires once
on entering each node of the search path, and never at the empty leaf. The pure operations
`insertOrSplit`, `insertRest` and `insert` are the `Id` instantiations with `leI` and
`visit := pure ()`.

The definitions are structurally recursive and `@[expose]`d, so `decide` evaluates insertion on
concrete trees from other modules; the monadic constructor equations `insertOrSplitM_leaf`,
`insertOrSplitM_node`, `insertRestM_nil` and `insertRestM_cons` hold by `rfl`.

`toList_insert_of_isSortedAssoc` is the model equation: on a tree with sorted entries, `toList`
of the insertion is `SortedAssoc.insert` on `toList`. `InsertResult.Fits` is the shape invariant
of a result relative to the subtree it replaces, and `fits_insertOrSplit` establishes it on
balanced trees with occupied children. On well-formed trees, `IsWF.insert` preserves
well-formedness, `height_insert` states that the height stays or grows by one, `size_insert`
gives the size, and `lookup_insert` gives lookup after insertion. Costs are not stated here.
-/

public section

universe w

namespace EpsilonEridani.BTree

/-- The result of inserting into a subtree: a tree of the same height, or an overflow split
into two trees of the same height around a median entry. -/
inductive InsertResult (α : Type) (β : Type) : Type where
  /-- The subtree absorbed the entry. -/
  | tree (tr : BTree α β)
  /-- The subtree overflowed and split around the entry `(k, v)`. -/
  | split (left : BTree α β) (k : α) (v : β) (right : BTree α β)

namespace InsertResult

variable {α β : Type}

/-- The entries of a result in order. -/
@[expose] def toList : InsertResult α β → List (α × β)
  | tree tr => tr.toList
  | split l k v r => l.toList ++ (k, v) :: r.toList

/-- Put a result in the place of a child followed by the triples `rest`. -/
@[expose] def withRest : InsertResult α β → List (α × β × BTree α β) →
    BTree α β × List (α × β × BTree α β)
  | tree c, rest => (c, rest)
  | split l k v r, rest => (l, (k, v, r) :: rest)

/-- A node with contents `first` and `rest`, split when it has more than `2 * t - 1` keys:
the first `t` keys stay on the left, the next one is the median, and the rest go right. The
`[]` branch is unreachable for `t ≥ 1`. -/
@[expose] def ofNode (t : ℕ) (first : BTree α β) (rest : List (α × β × BTree α β)) :
    InsertResult α β :=
  if rest.length ≤ 2 * t - 1 then tree (.node first rest)
  else match rest.drop t with
    | [] => tree (.node first rest)
    | (k, v, c) :: right => split (.node first (rest.take t)) k v (.node c right)

/-- The tree of a result at the root: an overflow grows a new root. -/
@[expose] def toTree : InsertResult α β → BTree α β
  | tree tr => tr
  | split l k v r => .node l [(k, v, r)]

variable {t : ℕ}

/-- The entries of a tree result are the tree's. -/
@[simp] theorem toList_tree (tr : BTree α β) : (tree tr).toList = tr.toList := rfl

/-- The entries of a split are the left entries, the median, then the right entries. -/
@[simp] theorem toList_split (l r : BTree α β) (k : α) (v : β) :
    (split l k v r).toList = l.toList ++ (k, v) :: r.toList := rfl

/-- Growing a new root keeps the entries. -/
@[simp] theorem toList_toTree (x : InsertResult α β) : x.toTree.toList = x.toList := by
  cases x <;> simp [toTree]

/-- Placing a result in the place of a child keeps the entries, followed by those of `rest`. -/
theorem toList_withRest (x : InsertResult α β) (rest : List (α × β × BTree α β)) :
    x.toList ++ toListRest rest =
      (x.withRest rest).1.toList ++ toListRest (x.withRest rest).2 := by
  cases x <;> simp [withRest]

/-- Splitting an overflowing node keeps its entries. -/
@[simp] theorem toList_ofNode (first : BTree α β) (rest : List (α × β × BTree α β)) :
    (ofNode t first rest).toList = (BTree.node first rest).toList := by
  unfold ofNode
  split_ifs
  · rfl
  · split
    · rfl
    · next k v c right heq =>
      have : rest = rest.take t ++ (k, v, c) :: right := by
        rw [← heq, List.take_append_drop]
      conv_rhs => rw [this]
      simp only [toList_split, toList_node, toListRest_append, toListRest_cons, List.append_assoc,
        List.cons_append]

/-- The shape invariant of the result of inserting into `tr`: either a tree of the same
height with at least as many root keys, still within `2 * t - 1`, or two occupied trees of
the same height. -/
def Fits (t : ℕ) (tr : BTree α β) : InsertResult α β → Prop
  | tree c => tr ≠ .leaf ∧ Balanced c ∧ c.height = tr.height ∧
      (∀ c' ∈ c.children, Occupied t c') ∧ tr.rootKeys ≤ c.rootKeys ∧ c.rootKeys ≤ 2 * t - 1
  | split l _ _ r => Balanced l ∧ Balanced r ∧ l.height = tr.height ∧ r.height = tr.height ∧
      Occupied t l ∧ Occupied t r

/-- A node of at most `2 * t` keys over children that are balanced, of height `h`, and
occupied, after the overflow split, fits any non-empty tree of height `h + 1` that had no more
keys. -/
theorem fits_ofNode (ht : 2 ≤ t) {tr first : BTree α β} {rest : List (α × β × BTree α β)}
    {h : ℕ} (hf : Balanced first ∧ first.height = h ∧ Occupied t first)
    (hr : ∀ e ∈ rest, Balanced e.2.2 ∧ e.2.2.height = h ∧ Occupied t e.2.2)
    (hlen : rest.length ≤ 2 * t) (htr : tr ≠ .leaf) (hh : tr.height = h + 1)
    (hk : tr.rootKeys ≤ rest.length) : (ofNode t first rest).Fits t tr := by
  have hnode : ∀ (f : BTree α β) (rs : List (α × β × BTree α β)),
      Balanced f → f.height = h → (∀ e ∈ rs, Balanced e.2.2 ∧ e.2.2.height = h) →
      Balanced (.node f rs) ∧ (BTree.node f rs).height = h + 1 := by
    intro f rs hbf hhf hrs
    have hb : Balanced (.node f rs) :=
      .node hbf (fun e he => (hrs e he).1) fun e he => (hrs e he).2.trans hhf.symm
    exact ⟨hb, by rw [hb.height_node, hhf]⟩
  unfold ofNode
  split_ifs with hle
  · obtain ⟨hb, hhn⟩ := hnode first rest hf.1 hf.2.1 fun e he => ⟨(hr e he).1, (hr e he).2.1⟩
    refine ⟨htr, hb, hhn.trans hh.symm, fun c hc => ?_, hk, hle⟩
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    exacts [hf.2.2, (hr e he).2.2]
  · have hlen' : rest.length = 2 * t := by omega
    split
    · next heq =>
      rw [List.drop_eq_nil_iff] at heq
      omega
    · next k v c right heq =>
      have hmem : (k, v, c) ∈ rest := List.mem_of_mem_drop (heq ▸ List.mem_cons_self ..)
      have hright : ∀ e ∈ right, e ∈ rest := fun e he =>
        List.mem_of_mem_drop (heq ▸ List.mem_cons_of_mem _ he)
      have hrl : right.length = t - 1 := by
        have := congrArg List.length heq
        simp only [List.length_drop, List.length_cons] at this
        omega
      have htl : (rest.take t).length = t := by simp; omega
      obtain ⟨hbl, hhl⟩ := hnode first (rest.take t) hf.1 hf.2.1 fun e he =>
        ⟨(hr e (List.mem_of_mem_take he)).1, (hr e (List.mem_of_mem_take he)).2.1⟩
      obtain ⟨hbr, hhr⟩ := hnode c right (hr _ hmem).1 (hr _ hmem).2.1 fun e he =>
        ⟨(hr e (hright e he)).1, (hr e (hright e he)).2.1⟩
      refine ⟨hbl, hbr, hhl.trans hh.symm, hhr.trans hh.symm, ?_, ?_⟩
      · exact .node (by omega) (by omega) hf.2.2 fun e he => (hr e (List.mem_of_mem_take he)).2.2
      · exact .node (by omega) (by omega) (hr _ hmem).2.2 fun e he => (hr e (hright e he)).2.2

/-- Placing a fitting result in the place of an occupied child of height `h` keeps every
child balanced, of height `h`, and occupied, and adds at most one key. -/
theorem fits_withRest {c : BTree α β} {x : InsertResult α β} (hx : x.Fits t c)
    (hc : Occupied t c) {h : ℕ} (hch : c.height = h) {rest : List (α × β × BTree α β)}
    (hr : ∀ e ∈ rest, Balanced e.2.2 ∧ e.2.2.height = h ∧ Occupied t e.2.2) :
    (Balanced (x.withRest rest).1 ∧ (x.withRest rest).1.height = h ∧
      Occupied t (x.withRest rest).1) ∧
    (∀ e ∈ (x.withRest rest).2, Balanced e.2.2 ∧ e.2.2.height = h ∧ Occupied t e.2.2) ∧
    rest.length ≤ (x.withRest rest).2.length ∧ (x.withRest rest).2.length ≤ rest.length + 1 := by
  cases x with
  | tree c' =>
    obtain ⟨hne, hb, hh, hco, hk₁, hk₂⟩ := hx
    refine ⟨⟨hb, hh.trans hch, ?_⟩, hr, le_rfl, Nat.le_succ _⟩
    cases c with
    | leaf => exact absurd rfl hne
    | node first' rest' =>
      have := hc.le_length
      cases c' with
      | leaf => exact .leaf
      | node f r =>
        simp only [rootKeys_node] at hk₁ hk₂
        exact .node (by omega) hk₂ (hco f List.mem_cons_self)
          fun e he => hco _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
  | split l k v r =>
    obtain ⟨hbl, hbr, hhl, hhr, hol, hor⟩ := hx
    refine ⟨⟨hbl, hhl.trans hch, hol⟩, fun e he => ?_, Nat.le_succ _, le_rfl⟩
    simp only [withRest, List.mem_cons] at he
    rcases he with rfl | he
    exacts [⟨hbr, hhr.trans hch, hor⟩, hr e he]

end InsertResult

section Polymorphic

variable {α β : Type} {m : Type → Type w} [Monad m]

mutual
/-- Bottom-up insertion into a subtree: the tree with the entry inserted, or its split when it
overflows. A node is visited once, on entry; the empty leaf is not visited and overflows at once
into the entry between two empty leaves. -/
@[expose] def insertOrSplitM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    BTree α β → m (InsertResult α β)
  | .leaf => pure (.split .leaf k v .leaf)
  | .node first rest => do
    visit
    match ← insertRestM t le visit k v rest with
    | some rest' => pure (.ofNode t first rest')
    | none =>
      let p := (← insertOrSplitM t le visit k v first).withRest rest
      pure (.ofNode t p.1 p.2)

/-- Insertion among the triples of a node, scanning them in order with the comparisons of
`lookupM`: `none` defers to the child before the triples, because the key is below the first
of them; `some rest'` is the new list of triples, with the value replaced at an equal key or
the result of the descent placed in the child after the last key below the query. -/
@[expose] def insertRestM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    List (α × β × BTree α β) → m (Option (List (α × β × BTree α β)))
  | [] => pure none
  | (k', v', c) :: rest => do
    if ← le k k' then
      if ← le k' k then pure (some ((k, v, c) :: rest)) else pure none
    else
      match ← insertRestM t le visit k v rest with
      | some rest' => pure (some ((k', v', c) :: rest'))
      | none =>
        let p := (← insertOrSplitM t le visit k v c).withRest rest
        pure (some ((k', v', p.1) :: p.2))
end

/-- Inserting into the empty tree overflows at once, without a visit: the parent absorbs the
new entry. -/
theorem insertOrSplitM_leaf (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    insertOrSplitM t le visit k v (.leaf : BTree α β) = pure (.split .leaf k v .leaf) := rfl

/-- A node is visited once, before its triples are searched; the result is split when it
overflows. -/
theorem insertOrSplitM_node (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (first : BTree α β) (rest : List (α × β × BTree α β)) :
    insertOrSplitM t le visit k v (.node first rest) = (do
      visit
      match ← insertRestM t le visit k v rest with
      | some rest' => pure (.ofNode t first rest')
      | none =>
        let p := (← insertOrSplitM t le visit k v first).withRest rest
        pure (.ofNode t p.1 p.2)) := rfl

/-- The search past the last triple defers to the child before it. -/
theorem insertRestM_nil (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β) :
    insertRestM t le visit k v ([] : List (α × β × BTree α β)) = pure none := rfl

/-- At a triple: replace on equality, defer to the preceding child when the key is below, and
otherwise move on, descending into this triple's child when every later key is above. -/
theorem insertRestM_cons (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (k' : α) (v' : β) (c : BTree α β) (rest : List (α × β × BTree α β)) :
    insertRestM t le visit k v ((k', v', c) :: rest) = (do
      if ← le k k' then
        if ← le k' k then pure (some ((k, v, c) :: rest)) else pure none
      else
        match ← insertRestM t le visit k v rest with
        | some rest' => pure (some ((k', v', c) :: rest'))
        | none =>
          let p := (← insertOrSplitM t le visit k v c).withRest rest
          pure (some ((k', v', p.1) :: p.2))) := rfl

/-- Insert-or-replace: the bottom-up insertion, growing a new root on overflow. -/
@[expose] def insertM (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (tr : BTree α β) : m (BTree α β) := do
  return (← insertOrSplitM t le visit k v tr).toTree

/-- Insertion is the bottom-up insertion with an overflow at the root grown into a new root. -/
theorem insertM_def (t : ℕ) (le : α → α → m Bool) (visit : m Unit) (k : α) (v : β)
    (tr : BTree α β) :
    insertM t le visit k v tr = (do return (← insertOrSplitM t le visit k v tr).toTree) := rfl

end Polymorphic

section Pure

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α} {v : β}

/-- Pure bottom-up insertion into a subtree. -/
@[expose] def insertOrSplit (t : ℕ) (k : α) (v : β) (tr : BTree α β) : InsertResult α β :=
  Id.run (insertOrSplitM t leI (pure ()) k v tr)

/-- Pure insertion among the triples of a node. -/
@[expose] def insertRest (t : ℕ) (k : α) (v : β) (rest : List (α × β × BTree α β)) :
    Option (List (α × β × BTree α β)) :=
  Id.run (insertRestM t leI (pure ()) k v rest)

/-- Pure insertion. -/
@[expose] def insert (t : ℕ) (k : α) (v : β) (tr : BTree α β) : BTree α β :=
  Id.run (insertM t leI (pure ()) k v tr)

theorem insert_eq_toTree (tr : BTree α β) : insert t k v tr = (insertOrSplit t k v tr).toTree :=
  rfl

@[simp] theorem insertOrSplit_leaf :
    insertOrSplit t k v (.leaf : BTree α β) = .split .leaf k v .leaf := rfl

theorem insertOrSplit_node (first : BTree α β) (rest : List (α × β × BTree α β)) :
    insertOrSplit t k v (.node first rest) =
      match insertRest t k v rest with
      | some rest' => .ofNode t first rest'
      | none =>
        let p := (insertOrSplit t k v first).withRest rest
        .ofNode t p.1 p.2 := by
  simp only [insertOrSplit, insertRest, insertOrSplitM]
  cases insertRestM t leI (pure ()) k v rest <;> rfl

@[simp] theorem insertRest_nil : insertRest t k v ([] : List (α × β × BTree α β)) = none := rfl

theorem insertRest_cons (k' : α) (v' : β) (c : BTree α β) (rest : List (α × β × BTree α β)) :
    insertRest t k v ((k', v', c) :: rest) =
      if k ≤ k' then (if k' ≤ k then some ((k, v, c) :: rest) else none)
      else match insertRest t k v rest with
        | some rest' => some ((k', v', c) :: rest')
        | none =>
          let p := (insertOrSplit t k v c).withRest rest
          some ((k', v', p.1) :: p.2) := by
  by_cases h₁ : k ≤ k' <;> by_cases h₂ : k' ≤ k <;>
    simp only [insertRest, insertOrSplit, insertRestM, leI, h₁, h₂, decide_true, decide_false,
      ↓reduceIte, Id.run_pure, pure_bind, bind_pure_comp] <;>
    cases insertRestM t leI (pure ()) k v rest <;> rfl


/-- The search among the triples of a node, against the model: when it defers to the child
before the triples, the key is below all their entries; otherwise it performs the model
insertion after any sorted prefix of smaller keys. -/
theorem insertRest_spec {rest : List (α × β × BTree α β)}
    (hc : ∀ e ∈ rest, e.2.2.toList.IsSortedAssoc →
      (insertOrSplit t k v e.2.2).toList = SortedAssoc.insert k v e.2.2.toList)
    (pre : List (α × β)) (hs : (pre ++ toListRest rest).IsSortedAssoc) :
    (insertRest t k v rest = none → ∀ p ∈ toListRest rest, k < p.1) ∧
      ∀ r, insertRest t k v rest = some r →
        pre ++ toListRest r = SortedAssoc.insert k v (pre ++ toListRest rest) := by
  induction rest generalizing pre with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k', v', c⟩ := e
    have hs' := hs
    rw [toListRest_cons, List.cons_append, List.isSortedAssoc_append_cons_iff,
      List.isSortedAssoc_append_iff] at hs'
    obtain ⟨hpre, ⟨hcs, hrs, hcr⟩, hlt, hgt⟩ := hs'
    have hcc := hc _ (List.mem_cons_self ..) hcs
    have ih := ih (fun e he => hc e (List.mem_cons_of_mem _ he))
    simp only [toListRest_cons, List.cons_append] at hs ⊢
    rw [insertRest_cons]
    by_cases h₁ : k ≤ k'
    · by_cases h₂ : k' ≤ k
      · obtain rfl : k = k' := le_antisymm h₁ h₂
        refine ⟨by simp, fun r hr => ?_⟩
        simp only [h₁, ↓reduceIte, Option.some.injEq] at hr
        subst hr
        rw [SortedAssoc.insert_append_of_forall_lt hlt, SortedAssoc.insert_cons]
        simp
      · have hk : k < k' := lt_of_le_of_ne h₁ fun h => h₂ (h ▸ le_rfl)
        refine ⟨fun _ p hp => ?_, fun r hr => by simp [h₁, h₂] at hr⟩
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hk
        · exact hk.trans (hgt p hp)
    · have hk : k' < k := lt_of_not_ge h₁
      have hpre' : ∀ p ∈ pre ++ [(k', v')], p.1 < k := by
        intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact (hlt p hp).trans hk
        · simp only [List.mem_singleton] at hp
          exact hp ▸ hk
      have ih := ih (pre ++ (k', v') :: c.toList) (by simpa using hs)
      simp only [h₁, ↓reduceIte]
      refine ⟨fun h => by split at h <;> simp at h, fun r hr => ?_⟩
      have hins : SortedAssoc.insert k v (pre ++ (k', v') :: (c.toList ++ toListRest rest)) =
          pre ++ (k', v') :: SortedAssoc.insert k v (c.toList ++ toListRest rest) := by
        have := SortedAssoc.insert_append_of_forall_lt (v := v)
          (l₂ := c.toList ++ toListRest rest) hpre'
        simpa using this
      cases hr' : insertRest t k v rest with
      | some r' =>
        simp only [hr', Option.some.injEq] at hr
        subst hr
        have := ih.2 r' hr'
        simp only [List.append_assoc, List.cons_append] at this
        simpa only [toListRest_cons, List.cons_append, List.append_assoc] using this
      | none =>
        simp only [hr', Option.some.injEq] at hr
        subst hr
        rw [hins, SortedAssoc.insert_append_of_forall_gt (ih.1 hr'), ← hcc,
          InsertResult.toList_withRest]
        simp

/-- Model equation of the bottom-up insertion on a subtree with sorted entries. -/
theorem toList_insertOrSplit_of_isSortedAssoc {tr : BTree α β} (h : tr.toList.IsSortedAssoc) :
    (insertOrSplit t k v tr).toList = SortedAssoc.insert k v tr.toList := by
  induction tr with
  | leaf => rfl
  | node first rest ihf ihr =>
    have spec := insertRest_spec (t := t) (k := k) (v := v) ihr first.toList h
    rw [toList_node, List.isSortedAssoc_append_iff] at h
    rw [insertOrSplit_node]
    cases hr : insertRest t k v rest with
    | some r =>
      simp only [InsertResult.toList_ofNode, toList_node]
      exact spec.2 r hr
    | none =>
      simp only [InsertResult.toList_ofNode, toList_node]
      rw [← InsertResult.toList_withRest, ihf h.1,
        SortedAssoc.insert_append_of_forall_gt (spec.1 hr)]

/-- Model equation of insertion on a tree with sorted entries. -/
theorem toList_insert_of_isSortedAssoc {tr : BTree α β} (h : tr.toList.IsSortedAssoc) :
    (insert t k v tr).toList = SortedAssoc.insert k v tr.toList := by
  rw [insert_eq_toTree, InsertResult.toList_toTree, toList_insertOrSplit_of_isSortedAssoc h]

/-- The search among the triples of a node keeps every child balanced, of height `h`, and
occupied, and adds at most one key. -/
theorem fits_insertRest {rest : List (α × β × BTree α β)} {h : ℕ}
    (hc : ∀ e ∈ rest, Balanced e.2.2 ∧ e.2.2.height = h ∧ Occupied t e.2.2 ∧
      (insertOrSplit t k v e.2.2).Fits t e.2.2)
    {r : List (α × β × BTree α β)} (hr : insertRest t k v rest = some r) :
    (∀ e ∈ r, Balanced e.2.2 ∧ e.2.2.height = h ∧ Occupied t e.2.2) ∧
      rest.length ≤ r.length ∧ r.length ≤ rest.length + 1 := by
  induction rest generalizing r with
  | nil => simp at hr
  | cons e rest ih =>
    obtain ⟨k', v', c⟩ := e
    have hcc := hc _ List.mem_cons_self
    have hrest : ∀ e ∈ rest, Balanced e.2.2 ∧ e.2.2.height = h ∧ Occupied t e.2.2 :=
      fun e he => (hc e (List.mem_cons_of_mem _ he)).imp_right fun h => h.imp_right And.left
    have ih := fun r (hr : insertRest t k v rest = some r) =>
      ih (fun e he => hc e (List.mem_cons_of_mem _ he)) hr
    rw [insertRest_cons] at hr
    by_cases h₁ : k ≤ k'
    · by_cases h₂ : k' ≤ k
      · simp only [h₁, h₂, ↓reduceIte, Option.some.injEq] at hr
        subst hr
        refine ⟨fun e he => ?_, by simp, by simp⟩
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        exacts [⟨hcc.1, hcc.2.1, hcc.2.2.1⟩, hrest e he]
      · simp [h₁, h₂] at hr
    · simp only [h₁, ↓reduceIte] at hr
      cases hr' : insertRest t k v rest with
      | some r' =>
        simp only [hr', Option.some.injEq] at hr
        subst hr
        obtain ⟨h₁, h₂, h₃⟩ := ih r' hr'
        refine ⟨fun e he => ?_, by simpa using h₂, by simpa using h₃⟩
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        exacts [⟨hcc.1, hcc.2.1, hcc.2.2.1⟩, h₁ e he]
      | none =>
        simp only [hr', Option.some.injEq] at hr
        subst hr
        obtain ⟨hp₁, hp₂, hl₁, hl₂⟩ :=
          InsertResult.fits_withRest hcc.2.2.2 hcc.2.2.1 hcc.2.1 hrest
        refine ⟨fun e he => ?_, by simpa using hl₁, by simpa using hl₂⟩
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        exacts [hp₁, hp₂ e he]

/-- Shape invariant of the bottom-up insertion. -/
theorem fits_insertOrSplit (ht : 2 ≤ t) {tr : BTree α β} (hb : Balanced tr)
    (ho : ∀ c ∈ tr.children, Occupied t c) (hk : tr.rootKeys ≤ 2 * t - 1) :
    (insertOrSplit t k v tr).Fits t tr := by
  induction tr with
  | leaf => exact ⟨.leaf, .leaf, rfl, rfl, .leaf, .leaf⟩
  | node first rest ihf ihr =>
    have hof : Occupied t first := ho first List.mem_cons_self
    have hor : ∀ e ∈ rest, Occupied t e.2.2 := fun e he =>
      ho _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))
    have hchild : ∀ c : BTree α β, Occupied t c → Balanced c →
        (∀ c' ∈ c.children, Occupied t c') ∧ c.rootKeys ≤ 2 * t - 1 := by
      intro c hc _
      refine ⟨fun c' hc' => hc.of_mem_children hc', ?_⟩
      cases c with
      | leaf => simp
      | node _ _ => exact hc.length_le
    have hrest : ∀ e ∈ rest, Balanced e.2.2 ∧ e.2.2.height = first.height ∧ Occupied t e.2.2 ∧
        (insertOrSplit t k v e.2.2).Fits t e.2.2 := fun e he => by
      have hbe := hb.of_mem_rest he
      obtain ⟨h₁, h₂⟩ := hchild _ (hor e he) hbe
      exact ⟨hbe, hb.height_of_mem_rest he, hor e he, ihr e he hbe h₁ h₂⟩
    have hrest' : ∀ e ∈ rest, Balanced e.2.2 ∧ e.2.2.height = first.height ∧ Occupied t e.2.2 :=
      fun e he => ⟨(hrest e he).1, (hrest e he).2.1, (hrest e he).2.2.1⟩
    have hh := hb.height_node
    simp only [rootKeys_node] at hk
    rw [insertOrSplit_node]
    cases hr : insertRest t k v rest with
    | some r =>
      obtain ⟨h₁, h₂, h₃⟩ := fits_insertRest hrest hr
      exact InsertResult.fits_ofNode ht ⟨hb.first, rfl, hof⟩ h₁ (by omega) (by simp) hh
        (by simpa using h₂)
    | none =>
      obtain ⟨h₁, h₂⟩ := hchild first hof hb.first
      obtain ⟨hp₁, hp₂, hl₁, hl₂⟩ :=
        InsertResult.fits_withRest (ihf hb.first h₁ h₂) hof rfl hrest'
      exact InsertResult.fits_ofNode ht hp₁ hp₂ (by omega) (by simp) hh (by simpa using hl₁)

variable {tr : BTree α β}

/-- Model equation of insertion on well-formed trees. -/
theorem toList_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).toList = SortedAssoc.insert k v tr.toList :=
  toList_insert_of_isSortedAssoc h.sorted

/-- Insertion preserves well-formedness. -/
theorem IsWF.insert (h : IsWF t tr) (k : α) (v : β) : IsWF t (insert t k v tr) := by
  have hf := fits_insertOrSplit (k := k) (v := v) h.two_le h.balanced h.occupied_of_mem_children
    h.rootKeys_le
  have hs : (BTree.insert t k v tr).toList.IsSortedAssoc := by
    rw [toList_insert h]
    exact SortedAssoc.isSortedAssoc_insert h.sorted
  rw [insert_eq_toTree] at hs ⊢
  cases hx : insertOrSplit t k v tr with
  | tree c =>
    rw [hx] at hf hs
    obtain ⟨hne, hb, -, hco, hk₁, hk₂⟩ := hf
    exact ⟨h.two_le, hk₂, fun _ => (h.rootKeys_pos hne).trans hk₁, hco, hb, hs⟩
  | split l k' v' r =>
    rw [hx] at hf hs
    obtain ⟨hbl, hbr, hhl, hhr, hol, hor⟩ := hf
    have := h.two_le
    refine ⟨h.two_le, by simp [InsertResult.toTree]; omega, fun _ => by simp [InsertResult.toTree],
      fun c hc => ?_, .node hbl (by simpa using hbr) (by simpa using hhr.trans hhl.symm), hs⟩
    simp only [InsertResult.toTree, children_node, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    exacts [hol, hor]

/-- Insertion raises the height of a well-formed tree by at most one: exactly when the root
splits. -/
theorem height_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).height = tr.height ∨ (insert t k v tr).height = tr.height + 1 := by
  have hf := fits_insertOrSplit (k := k) (v := v) h.two_le h.balanced h.occupied_of_mem_children
    h.rootKeys_le
  rw [insert_eq_toTree]
  cases hx : insertOrSplit t k v tr with
  | tree c =>
    rw [hx] at hf
    exact Or.inl hf.2.2.1
  | split l k' v' r =>
    rw [hx] at hf
    obtain ⟨hbl, hbr, hhl, hhr, -, -⟩ := hf
    have hb : Balanced (BTree.node l [(k', v', r)]) :=
      .node hbl (by simpa using hbr) (by simpa using hhr.trans hhl.symm)
    exact Or.inr (by rw [InsertResult.toTree, hb.height_node, hhl])

/-- Insertion raises the height by at most one. -/
theorem height_insert_le (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).height ≤ tr.height + 1 := by
  rcases height_insert h k v with h | h <;> omega

/-- Insertion never lowers the height. -/
theorem height_le_height_insert (h : IsWF t tr) (k : α) (v : β) :
    tr.height ≤ (insert t k v tr).height := by
  rcases height_insert h k v with h | h <;> omega

/-- Insertion keeps the size when the key is present and adds one otherwise. -/
theorem size_insert (h : IsWF t tr) (k : α) (v : β) :
    (insert t k v tr).size = if (lookup k tr).isSome then tr.size else tr.size + 1 := by
  rw [size, toList_insert h, SortedAssoc.length_insert h.sorted, lookup_eq h]
  rfl

/-- Lookup after insertion finds the new value at its key and is unchanged elsewhere. -/
theorem lookup_insert (h : IsWF t tr) (k k' : α) (v : β) :
    lookup k' (insert t k v tr) = if k' = k then some v else lookup k' tr := by
  rw [lookup_eq (h.insert k v), toList_insert h, lookup_eq h]
  split_ifs with hk
  · subst hk
    exact SortedAssoc.lookup_insert_self
  · exact SortedAssoc.lookup_insert_of_ne hk

/-! ### Examples -/

/-- A root split at `t = 2`: a fourth key into a full root raises the height. -/
example :
    (insert 2 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])).height = 2 := by decide

/-- The split root keeps its first two keys on the left and promotes the third. -/
example :
    (insert 2 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])).children.map (·.toList) =
    [[(1, ()), (2, ())], [(4, ())]] := by decide

/-- The tree after the root split is well-formed. -/
example :
    IsWF 2 (insert 2 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])) := by decide

/-- Below the root, a full child splits and the root absorbs its median without growing. -/
example :
    let tr := insert 2 0 "z" (BTree.node (α := ℕ) (β := String)
      (.node .leaf [(1, "a", .leaf), (2, "b", .leaf), (3, "c", .leaf)]) [(5, "e", .node .leaf
        [(6, "f", .leaf)])])
    tr.height = 2 ∧ tr.rootKeys = 2 ∧
      tr.toList = [(0, "z"), (1, "a"), (2, "b"), (3, "c"), (5, "e"), (6, "f")] ∧ IsWF 2 tr := by
  decide

/-- An existing key is replaced in place: no split, no growth. -/
example :
    let tr := insert 2 2 "B" (BTree.node (α := ℕ) (β := String) .leaf
      [(1, "a", .leaf), (2, "b", .leaf), (3, "c", .leaf)])
    tr.height = 1 ∧ tr.toList = [(1, "a"), (2, "B"), (3, "c")] := by decide

/-- At `t = 3` the same root has room for a fourth key. -/
example :
    (insert 3 4 () (BTree.node (α := ℕ) (β := Unit) .leaf
      [(1, (), .leaf), (2, (), .leaf), (3, (), .leaf)])).height = 1 := by decide

/-- Insertion into the empty tree grows a one-key root. -/
example : (insert 2 1 "a" (.leaf : BTree ℕ String)).toList = [(1, "a")] := by decide

end Pure

end EpsilonEridani.BTree
