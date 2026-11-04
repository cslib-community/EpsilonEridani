/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Foundations.Data.List.SortedAssoc

/-!
# Classic B-trees

The B-trees of Bayer and McCreight, *Organization and maintenance of large ordered indexes*
(1972), in the minimum-degree form of Cormen, Leiserson, Rivest and Stein, *Introduction to
Algorithms*, Chapter 18. A node is a first child followed by a list of `(key, value, child)`
triples, so a node with `m` keys has `m + 1` children by construction; `leaf` is the empty tree.
The tree is a map from keys to values, specified by `toList` against the sorted association list
model `List.IsSortedAssoc`. `toList` traverses any tree in structural in-order (the first child,
then each key-value pair followed by its child); under `IsWF` (its `sorted` field) the keys are
strictly increasing, which gives map semantics.

`height` counts the nodes on a root-to-leaf path: the leaf has height `0` and a node has height
one more than its tallest child. Well-formedness at minimum degree `t` is the hypothesis
`IsWF t tr`, never part of the type: `t ≥ 2`, every non-root node has between `t - 1` and
`2 * t - 1` keys (`Occupied`), a non-leaf root has between `1` and `2 * t - 1` keys, all leaves
are at the same depth (`Balanced`), and `toList` is key-sorted. Taking `t = 2` gives 2-3-4 trees.

`induction` is the induction principle for the nested type; proofs use it rather than the raw
nested recursor. The Boolean checkers `occupied`, `balanced` and `isWF` decide the predicates,
so that well-formedness of concrete trees is checked by `decide`. The operations and checkers are
`@[expose]`d so that `decide` and `rfl` evaluate them from other modules.
-/

public section

universe u v w

namespace EpsilonEridani

/-- A classic B-tree. A node is a first child followed by `(key, value, child)` triples, so a
node with `m` keys has `m + 1` children by construction. `leaf` is the empty tree. -/
inductive BTree (α : Type u) (β : Type v) : Type (max u v) where
  /-- The empty tree. -/
  | leaf : BTree α β
  /-- A node: its first child, then the keys, values and remaining children in order. -/
  | node (first : BTree α β) (rest : List (α × β × BTree α β)) : BTree α β

namespace BTree

variable {α : Type u} {β : Type v} {γ : Type w}

mutual
/-- Entries in structural in-order: the first child's, then each key-value pair followed by its
child's. The keys are strictly increasing under `IsWF` (its `sorted` field). -/
@[expose] def toList : BTree α β → List (α × β)
  | leaf => []
  | node first rest => first.toList ++ toListRest rest
/-- Entries of the triples following a first child, each key before its child's entries. -/
@[expose] def toListRest : List (α × β × BTree α β) → List (α × β)
  | [] => []
  | (k, v, c) :: rest => (k, v) :: c.toList ++ toListRest rest
end

mutual
/-- Nodes on a root-to-leaf path: the leaf has height `0`. -/
@[expose] def height : BTree α β → ℕ
  | leaf => 0
  | node first rest => max (first.height + 1) (heightRest rest)
/-- Height contribution of the children in a list of triples. -/
@[expose] def heightRest : List (α × β × BTree α β) → ℕ
  | [] => 0
  | (_, _, c) :: rest => max (c.height + 1) (heightRest rest)
end

mutual
/-- Map over values, keeping keys and shape. -/
@[expose] def map (f : β → γ) : BTree α β → BTree α γ
  | leaf => leaf
  | node first rest => node (first.map f) (mapRest f rest)
/-- Map over the values of a list of triples. -/
@[expose] def mapRest (f : β → γ) : List (α × β × BTree α β) → List (α × γ × BTree α γ)
  | [] => []
  | (k, v, c) :: rest => (k, f v, c.map f) :: mapRest f rest
end

/-- Number of entries. -/
@[expose] def size (tr : BTree α β) : ℕ := tr.toList.length

/-- Keys in structural in-order, as in `toList`; strictly increasing under `IsWF`. -/
@[expose] def keys (tr : BTree α β) : List α := tr.toList.map Prod.fst

/-- Fold over entries in structural in-order, as in `toList`, which is key order under `IsWF`;
the specification of any direct recursive fold. -/
@[expose] def foldl (f : γ → α × β → γ) (init : γ) (tr : BTree α β) : γ :=
  tr.toList.foldl f init

/-- An entry belongs to a tree when it belongs to its `toList`. -/
instance : Membership (α × β) (BTree α β) := ⟨fun tr p => p ∈ tr.toList⟩

/-- Number of keys at the root node. -/
@[expose] def rootKeys : BTree α β → ℕ
  | leaf => 0
  | node _ rest => rest.length

/-- Children of the root node. -/
@[expose] def children : BTree α β → List (BTree α β)
  | leaf => []
  | node first rest => first :: rest.map (·.2.2)

/-- Every node satisfies the occupancy bounds of a non-root node of minimum degree `t`: between
`t - 1` and `2 * t - 1` keys. -/
inductive Occupied (t : ℕ) : BTree α β → Prop
  /-- The empty tree is occupied. -/
  | leaf : Occupied t .leaf
  /-- A node is occupied when its key count is in bounds and all its children are occupied. -/
  | node {first : BTree α β} {rest : List (α × β × BTree α β)} :
      t - 1 ≤ rest.length → rest.length ≤ 2 * t - 1 →
      Occupied t first → (∀ e ∈ rest, Occupied t e.2.2) → Occupied t (.node first rest)

/-- All leaves at the same depth: every child of a node has the height of the first child. -/
inductive Balanced : BTree α β → Prop
  /-- The empty tree is balanced. -/
  | leaf : Balanced .leaf
  /-- A node is balanced when its children are balanced and of equal height. -/
  | node {first : BTree α β} {rest : List (α × β × BTree α β)} :
      Balanced first → (∀ e ∈ rest, Balanced e.2.2) →
      (∀ e ∈ rest, e.2.2.height = first.height) → Balanced (.node first rest)

/-- Well-formed B-tree of minimum degree `t`: root occupancy, non-root occupancy, equal leaf
depth, and key-sortedness of `toList`. -/
structure IsWF [LinearOrder α] (t : ℕ) (tr : BTree α β) : Prop where
  /-- The minimum degree is at least `2`. -/
  two_le : 2 ≤ t
  /-- The root has at most `2 * t - 1` keys. -/
  rootKeys_le : tr.rootKeys ≤ 2 * t - 1
  /-- A non-empty root has at least one key. -/
  rootKeys_pos : tr ≠ .leaf → 1 ≤ tr.rootKeys
  /-- Every child of the root is occupied. -/
  occupied_of_mem_children : ∀ c ∈ tr.children, Occupied t c
  /-- All leaves are at the same depth. -/
  balanced : Balanced tr
  /-- The entries are sorted by strictly increasing key. -/
  sorted : tr.toList.IsSortedAssoc

mutual
/-- Boolean check of `Occupied t`. -/
@[expose] def occupied (t : ℕ) : BTree α β → Bool
  | leaf => true
  | node first rest =>
    decide (t - 1 ≤ rest.length) && decide (rest.length ≤ 2 * t - 1) && occupied t first &&
      occupiedRest t rest
/-- Boolean check that every child in a list of triples is occupied. -/
@[expose] def occupiedRest (t : ℕ) : List (α × β × BTree α β) → Bool
  | [] => true
  | (_, _, c) :: rest => occupied t c && occupiedRest t rest
end

mutual
/-- Boolean check of `Balanced`. -/
@[expose] def balanced : BTree α β → Bool
  | leaf => true
  | node first rest => balanced first && balancedRest first.height rest
/-- Boolean check that every child in a list of triples is balanced and of height `h`. -/
@[expose] def balancedRest (h : ℕ) : List (α × β × BTree α β) → Bool
  | [] => true
  | (_, _, c) :: rest => balanced c && c.height == h && balancedRest h rest
end

/-- Boolean check of `IsWF t`. -/
@[expose] def isWF [LinearOrder α] (t : ℕ) (tr : BTree α β) : Bool :=
  decide (2 ≤ t) && decide (tr.rootKeys ≤ 2 * t - 1) &&
    (tr matches .leaf || decide (1 ≤ tr.rootKeys)) && tr.children.all (occupied t) &&
    balanced tr && decide ((tr.toList.map Prod.fst).Pairwise (· < ·))

/-! ### Equation lemmas -/

section Equations

variable {first : BTree α β} {rest : List (α × β × BTree α β)} {k : α} {v : β} {c : BTree α β}

/-- The empty tree has no entries. -/
@[simp] theorem toList_leaf : (leaf : BTree α β).toList = [] := rfl

/-- The entries of a node: those of its first child, then those of the triples. -/
@[simp] theorem toList_node : (node first rest).toList = first.toList ++ toListRest rest := rfl

/-- An empty list of triples has no entries. -/
@[simp] theorem toListRest_nil : toListRest ([] : List (α × β × BTree α β)) = [] := rfl

/-- The entries of a list of triples: the key, its child's entries, then the rest. -/
@[simp] theorem toListRest_cons :
    toListRest ((k, v, c) :: rest) = (k, v) :: c.toList ++ toListRest rest := rfl

/-- The empty tree has size `0`. -/
@[simp] theorem size_leaf : (leaf : BTree α β).size = 0 := rfl

/-- The empty tree has height `0`. -/
@[simp] theorem height_leaf : (leaf : BTree α β).height = 0 := rfl

/-- The height of a node is one more than that of its tallest child. -/
@[simp] theorem height_node :
    (node first rest).height = max (first.height + 1) (heightRest rest) := rfl

/-- An empty list of triples contributes height `0`. -/
@[simp] theorem heightRest_nil : heightRest ([] : List (α × β × BTree α β)) = 0 := rfl

/-- The height contribution of a list of triples is that of its tallest child. -/
@[simp] theorem heightRest_cons :
    heightRest ((k, v, c) :: rest) = max (c.height + 1) (heightRest rest) := rfl

/-- Mapping the empty tree gives the empty tree. -/
@[simp] theorem map_leaf (f : β → γ) : (leaf : BTree α β).map f = leaf := rfl

/-- Mapping a node maps its first child and its triples. -/
@[simp] theorem map_node (f : β → γ) :
    (node first rest).map f = node (first.map f) (mapRest f rest) := rfl

/-- Mapping an empty list of triples gives the empty list. -/
@[simp] theorem mapRest_nil (f : β → γ) : mapRest f ([] : List (α × β × BTree α β)) = [] := rfl

/-- Mapping a list of triples maps the value and the child of its head, then the rest. -/
@[simp] theorem mapRest_cons (f : β → γ) :
    mapRest f ((k, v, c) :: rest) = (k, f v, c.map f) :: mapRest f rest := rfl

/-- The empty tree has no children. -/
@[simp] theorem children_leaf : (leaf : BTree α β).children = [] := rfl

/-- The children of a node: its first child, then the children of its triples. -/
@[simp] theorem children_node : (node first rest).children = first :: rest.map (·.2.2) := rfl

/-- The empty tree has no keys at its root. -/
@[simp] theorem rootKeys_leaf : (leaf : BTree α β).rootKeys = 0 := rfl

/-- A node has one root key per triple. -/
@[simp] theorem rootKeys_node : (node first rest).rootKeys = rest.length := rfl

end Equations

variable {tr : BTree α β}

/-! ### Induction -/

/-- Induction on B-trees, with a hypothesis for the first child and for every child among the
triples. This replaces the raw nested recursor in proofs. -/
theorem induction {motive : BTree α β → Prop} (leaf : motive .leaf)
    (node : ∀ first rest, motive first → (∀ e ∈ rest, motive e.2.2) → motive (.node first rest)) :
    ∀ tr, motive tr
  | .leaf => leaf
  | .node first rest =>
    node first rest (induction leaf node first) fun e _ => induction leaf node e.2.2
termination_by tr => sizeOf tr
decreasing_by
  · simp_wf
    omega
  · have := List.sizeOf_lt_of_mem ‹e ∈ rest›
    obtain ⟨a, b, c⟩ := e
    simp only [Prod.mk.sizeOf_spec] at this
    simp_wf
    omega

attribute [induction_eliminator] induction

/-! ### Basic API -/

/-- Membership in a tree is membership in its entries. -/
@[simp] theorem mem_def {p : α × β} : p ∈ tr ↔ p ∈ tr.toList := Iff.rfl

/-- The length of the entries is the size. -/
@[simp] theorem length_toList : tr.toList.length = tr.size := rfl

/-- The entries of a list of triples: one per key, plus those of the children. -/
@[simp] theorem length_toListRest {rest : List (α × β × BTree α β)} :
    (toListRest rest).length = rest.length + (rest.map fun e => e.2.2.size).sum := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp only [toListRest_cons, List.length_cons, List.length_append, ih, List.map_cons,
      List.sum_cons, length_toList]
    omega

/-- The size of a node: its first child's, one per key, and its other children's. -/
theorem size_node {first : BTree α β} {rest : List (α × β × BTree α β)} :
    (node first rest).size = first.size + rest.length + (rest.map fun e => e.2.2.size).sum := by
  rw [← length_toList, toList_node, List.length_append, length_toListRest, length_toList,
    Nat.add_assoc]

/-- `foldl` is the fold over `toList`. -/
theorem foldl_eq (f : γ → α × β → γ) (init : γ) : tr.foldl f init = tr.toList.foldl f init :=
  rfl

/-- `keys` is the list of first components of `toList`. -/
theorem keys_def : tr.keys = tr.toList.map Prod.fst := rfl

/-- A key belongs to a tree's keys when some entry of the tree carries it. -/
@[simp] theorem mem_keys {k : α} : k ∈ tr.keys ↔ ∃ v, (k, v) ∈ tr := by
  simp only [keys_def, List.mem_map, mem_def]
  constructor
  · rintro ⟨⟨k, v⟩, hp, rfl⟩
    exact ⟨v, hp⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, hv, rfl⟩

/-- Only the empty tree has height `0`. -/
@[simp] theorem height_eq_zero_iff : tr.height = 0 ↔ tr = .leaf := by
  cases tr with
  | leaf => simp
  | node first rest => simp

/-- Mapping over values maps the entries, keeping keys. -/
@[simp] theorem toList_map (f : β → γ) :
    (tr.map f).toList = tr.toList.map fun p => (p.1, f p.2) := by
  induction tr with
  | leaf => rfl
  | node first rest ih₁ ih₂ =>
    rw [map_node, toList_node, toList_node, List.map_append, ih₁]
    congr 1
    induction rest with
    | nil => rfl
    | cons e rest ih =>
      obtain ⟨k, v, c⟩ := e
      simp [ih₂ _ List.mem_cons_self, ih fun e he => ih₂ e (List.mem_cons_of_mem _ he)]

/-- Mapping over values keeps the height. -/
@[simp] theorem height_map (f : β → γ) : (tr.map f).height = tr.height := by
  induction tr with
  | leaf => rfl
  | node first rest ih₁ ih₂ =>
    rw [map_node, height_node, height_node, ih₁]
    congr 1
    induction rest with
    | nil => rfl
    | cons e rest ih =>
      obtain ⟨k, v, c⟩ := e
      simp [ih₂ _ List.mem_cons_self, ih fun e he => ih₂ e (List.mem_cons_of_mem _ he)]

/-- Mapping over values keeps the size. -/
@[simp] theorem size_map (f : β → γ) : (tr.map f).size = tr.size := by
  simp [← length_toList]

/-- Mapping over values keeps the keys. -/
@[simp] theorem keys_map (f : β → γ) : (tr.map f).keys = tr.keys := by
  simp [keys, Function.comp_def]

/-- Mapping the identity leaves the tree unchanged. -/
@[simp] theorem map_id : tr.map id = tr := by
  induction tr with
  | leaf => rfl
  | node first rest ih₁ ih₂ =>
    rw [map_node, ih₁]
    congr 1
    induction rest with
    | nil => rfl
    | cons e rest ih =>
      obtain ⟨k, v, c⟩ := e
      simp [ih₂ _ List.mem_cons_self, ih fun e he => ih₂ e (List.mem_cons_of_mem _ he)]

/-- Mapping twice is mapping the composition. -/
@[simp] theorem map_map {δ : Type*} (g : γ → δ) (f : β → γ) :
    (tr.map f).map g = tr.map (g ∘ f) := by
  induction tr with
  | leaf => rfl
  | node first rest ih₁ ih₂ =>
    rw [map_node, map_node, map_node, ih₁]
    congr 1
    induction rest with
    | nil => rfl
    | cons e rest ih =>
      obtain ⟨k, v, c⟩ := e
      simp [ih₂ _ List.mem_cons_self, ih fun e he => ih₂ e (List.mem_cons_of_mem _ he)]

/-- The entries of a concatenation of triple lists are the concatenated entries. -/
@[simp] theorem toListRest_append {l₁ l₂ : List (α × β × BTree α β)} :
    toListRest (l₁ ++ l₂) = toListRest l₁ ++ toListRest l₂ := by
  induction l₁ with
  | nil => rfl
  | cons e l₁ ih =>
    obtain ⟨k, v, c⟩ := e
    simp [ih]

/-- The entries of a child among the triples form a sublist of the triples' entries. -/
theorem toList_sublist_toListRest_of_mem {rest : List (α × β × BTree α β)}
    {e : α × β × BTree α β} (he : e ∈ rest) : e.2.2.toList.Sublist (toListRest rest) := by
  induction rest with
  | nil => simp at he
  | cons e' rest ih =>
    obtain ⟨k, v, c'⟩ := e'
    rw [toListRest_cons, List.cons_append]
    rcases List.mem_cons.1 he with rfl | he
    · exact (List.sublist_append_left _ _).cons _
    · exact ((ih he).trans (List.sublist_append_right _ _)).cons _

/-- The entries of a child of the root form a sublist of the tree's entries. -/
theorem toList_sublist_of_mem_children {c : BTree α β} (hc : c ∈ tr.children) :
    c.toList.Sublist tr.toList := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rw [toList_node]
    rcases hc with rfl | ⟨e, he, rfl⟩
    · exact List.sublist_append_left _ _
    · exact (toList_sublist_toListRest_of_mem he).trans (List.sublist_append_right _ _)

/-- Every child among the triples of a node is shorter than the node. -/
theorem height_succ_le_of_mem_rest {first : BTree α β} {rest : List (α × β × BTree α β)}
    {e : α × β × BTree α β} (he : e ∈ rest) : e.2.2.height + 1 ≤ (node first rest).height := by
  rw [height_node]
  suffices e.2.2.height + 1 ≤ heightRest rest by omega
  induction rest with
  | nil => simp at he
  | cons e' rest ih =>
    obtain ⟨k, v, c'⟩ := e'
    rw [heightRest_cons]
    rcases List.mem_cons.1 he with rfl | he
    · dsimp only
      omega
    · have := ih he
      omega

/-- Every child of a tree is shorter than the tree. -/
theorem height_succ_le_of_mem_children {c : BTree α β} (hc : c ∈ tr.children) :
    c.height + 1 ≤ tr.height := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    · rw [height_node]
      omega
    · exact height_succ_le_of_mem_rest he

/-! ### Inversion lemmas -/

section Inversion

variable {fst : BTree α β} {rest : List (α × β × BTree α β)} {t : ℕ}

/-- Every child among the triples of a balanced node has the height of the first child. -/
theorem Balanced.height_of_mem_rest (h : Balanced (.node fst rest)) {e : α × β × BTree α β}
    (he : e ∈ rest) : e.2.2.height = fst.height := by
  cases h with
  | node _ _ h => exact h e he

/-- A balanced node is one taller than its first child. -/
theorem Balanced.height_node (h : Balanced (.node fst rest)) :
    (BTree.node fst rest).height = fst.height + 1 := by
  have hh : ∀ e ∈ rest, e.2.2.height = fst.height := fun _ => h.height_of_mem_rest
  clear h
  rw [BTree.height_node]
  suffices heightRest rest ≤ fst.height + 1 by omega
  induction rest with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    have hc := hh _ List.mem_cons_self
    have := ih fun e he => hh e (List.mem_cons_of_mem _ he)
    simp only at hc
    rw [heightRest_cons]
    omega

/-- The first child of a balanced node is balanced. -/
theorem Balanced.first (h : Balanced (.node fst rest)) : Balanced fst := by
  cases h
  assumption

/-- Every child among the triples of a balanced node is balanced. -/
theorem Balanced.of_mem_rest (h : Balanced (.node fst rest)) {e : α × β × BTree α β}
    (he : e ∈ rest) : Balanced e.2.2 := by
  cases h with
  | node _ h _ => exact h e he

/-- Children of a balanced tree are one level shorter. -/
theorem Balanced.height_of_mem_children {c : BTree α β} (h : Balanced tr) (hc : c ∈ tr.children) :
    c.height + 1 = tr.height := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    rw [h.height_node]
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    · rfl
    · rw [h.height_of_mem_rest he]

/-- Children of a balanced tree are balanced. -/
theorem Balanced.of_mem_children {c : BTree α β} (h : Balanced tr) (hc : c ∈ tr.children) :
    Balanced c := by
  cases tr with
  | leaf => simp at hc
  | node first rest =>
    simp only [children_node, List.mem_cons, List.mem_map] at hc
    rcases hc with rfl | ⟨e, he, rfl⟩
    · exact h.first
    · exact h.of_mem_rest he

/-- The first child of an occupied node is occupied. -/
theorem Occupied.first (h : Occupied t (.node fst rest)) : Occupied t fst := by
  cases h
  assumption

/-- Every child among the triples of an occupied node is occupied. -/
theorem Occupied.of_mem_rest (h : Occupied t (.node fst rest)) {e : α × β × BTree α β}
    (he : e ∈ rest) : Occupied t e.2.2 := by
  cases h with
  | node _ _ _ h => exact h e he

/-- An occupied node has at most `2 * t - 1` keys. -/
theorem Occupied.length_le (h : Occupied t (.node fst rest)) : rest.length ≤ 2 * t - 1 := by
  cases h
  assumption

/-- An occupied node has at least `t - 1` keys. -/
theorem Occupied.le_length (h : Occupied t (.node fst rest)) : t - 1 ≤ rest.length := by
  cases h
  assumption

end Inversion

section LinearOrder

variable [LinearOrder α] {t : ℕ} {c : BTree α β}

/-- The first child of a well-formed node is occupied. -/
theorem IsWF.occupied_first {first : BTree α β} {rest : List (α × β × BTree α β)}
    (h : IsWF t (node first rest)) : Occupied t first :=
  h.occupied_of_mem_children first List.mem_cons_self

/-- Every child among the triples of a well-formed node is occupied. -/
theorem IsWF.occupied_of_mem_rest {first : BTree α β} {rest : List (α × β × BTree α β)}
    {e : α × β × BTree α β} (h : IsWF t (node first rest)) (he : e ∈ rest) :
    Occupied t e.2.2 :=
  h.occupied_of_mem_children _ (List.mem_cons_of_mem _ (List.mem_map_of_mem he))

/-- Every child of a well-formed tree has sorted entries. -/
theorem IsWF.sorted_of_mem_children (h : IsWF t tr) (hc : c ∈ tr.children) :
    c.toList.IsSortedAssoc :=
  h.sorted.sublist (toList_sublist_of_mem_children hc)

end LinearOrder

/-! ### Decidability -/

section Decidability

variable {rest : List (α × β × BTree α β)} {t n : ℕ}

/-- `occupiedRest` checks every child among the triples with `occupied`. -/
@[simp] theorem occupiedRest_eq_all :
    occupiedRest t rest = rest.all fun e => occupied t e.2.2 := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp [occupiedRest, ih]

/-- `balancedRest n` checks that every child among the triples is balanced and of height `n`. -/
@[simp] theorem balancedRest_eq_all :
    balancedRest n rest = rest.all fun e => balanced e.2.2 && e.2.2.height == n := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp [balancedRest, ih, Bool.and_assoc]

/-- `occupied` decides `Occupied`. -/
@[simp] theorem occupied_iff : occupied t tr = true ↔ Occupied t tr := by
  induction tr with
  | leaf => exact ⟨fun _ => .leaf, fun _ => rfl⟩
  | node first rest ih₁ ih₂ =>
    rw [occupied, occupiedRest_eq_all]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, ih₁]
    constructor
    · rintro ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
      exact .node h₁ h₂ h₃ fun e he => (ih₂ e he).1 (h₄ e he)
    · intro h
      cases h with
      | node h₁ h₂ h₃ h₄ => exact ⟨⟨⟨h₁, h₂⟩, h₃⟩, fun e he => (ih₂ e he).2 (h₄ e he)⟩

/-- `balanced` decides `Balanced`. -/
@[simp] theorem balanced_iff : balanced tr = true ↔ Balanced tr := by
  induction tr with
  | leaf => exact ⟨fun _ => .leaf, fun _ => rfl⟩
  | node first rest ih₁ ih₂ =>
    rw [balanced, balancedRest_eq_all]
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, ih₁]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact .node h₁ (fun e he => (ih₂ e he).1 (h₂ e he).1) fun e he => (h₂ e he).2
    · intro h
      cases h with
      | node h₁ h₂ h₃ => exact ⟨h₁, fun e he => ⟨(ih₂ e he).2 (h₂ e he), h₃ e he⟩⟩

/-- `isWF` decides `IsWF`. -/
@[simp] theorem isWF_iff [LinearOrder α] : isWF t tr = true ↔ IsWF t tr := by
  simp only [isWF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    occupied_iff, balanced_iff]
  constructor
  · rintro ⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩
    refine ⟨h₁, h₂, fun hne => ?_, h₄, h₅, List.isSortedAssoc_iff_pairwise.2 h₆⟩
    cases tr with
    | leaf => exact absurd rfl hne
    | node => simpa using h₃
  · intro h
    refine ⟨⟨⟨⟨⟨h.two_le, h.rootKeys_le⟩, ?_⟩, h.occupied_of_mem_children⟩, h.balanced⟩,
      List.isSortedAssoc_iff_pairwise.1 h.sorted⟩
    cases tr with
    | leaf => simp
    | node => exact Or.inr (h.rootKeys_pos nofun)

end Decidability

instance (t : ℕ) (tr : BTree α β) : Decidable (Occupied t tr) := decidable_of_iff _ occupied_iff

instance (tr : BTree α β) : Decidable (Balanced tr) := decidable_of_iff _ balanced_iff

instance [LinearOrder α] (t : ℕ) (tr : BTree α β) : Decidable (IsWF t tr) :=
  decidable_of_iff _ isWF_iff

/-! ### Examples -/

/-- A root with one key and two leaf children is a well-formed 2-3-4 tree. -/
example : IsWF 2 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf)]) := by decide

/-- A node whose children differ in height is not well-formed for any `t`. -/
example (t : ℕ) :
    ¬ IsWF t (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(0, (), .leaf)]) [(1, (), .leaf)]) :=
  fun h => absurd h.balanced (by decide)

/-- Children of different heights violate equal leaf depth. -/
example :
    ¬ IsWF 2 (BTree.node (α := ℕ) (β := Unit) (.node .leaf [(0, (), .leaf)]) [(1, (), .leaf)]) := by
  decide

/-- A root with two keys and three leaf children is well-formed at `t = 3`. -/
example : IsWF 3 (BTree.node (α := ℕ) (β := String) .leaf [(1, "a", .leaf), (2, "b", .leaf)]) := by
  decide

/-- Occupancy depends on `t`: one-key children are full enough at `t = 2` and too sparse at
`t = 3`, where a non-root node needs at least two keys. -/
example :
    IsWF 2 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(0, (), .leaf)]) [(5, (), .node .leaf [(6, (), .leaf)])]) ∧
    ¬ IsWF 3 (BTree.node (α := ℕ) (β := Unit)
      (.node .leaf [(0, (), .leaf)]) [(5, (), .node .leaf [(6, (), .leaf)])]) := by decide

/-- The minimum degree is at least `2`, so even the empty tree is not well-formed at `t = 1`. -/
example : ¬ IsWF 1 (BTree.leaf : BTree ℕ Unit) := by decide

/-- At `t = 0` a root with one key is not well-formed. -/
example : ¬ IsWF 0 (BTree.node (α := ℕ) (β := Unit) .leaf [(1, (), .leaf)]) := by decide

/-- A non-empty root needs at least one key. -/
example : ¬ IsWF 2 (BTree.node (α := ℕ) (β := Unit) .leaf []) := by decide

/-- A node with no keys and a leaf child has height `1`. -/
example : (BTree.node (α := ℕ) (β := Unit) .leaf []).height = 1 := by decide

/-- Keys out of order are not well-formed. -/
example : ¬ IsWF 2 (BTree.node (α := ℕ) (β := Unit) .leaf [(2, (), .leaf), (1, (), .leaf)]) := by
  decide

end BTree

end EpsilonEridani
