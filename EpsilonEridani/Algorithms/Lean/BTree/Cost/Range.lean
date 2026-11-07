/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Cost.Query
public import EpsilonEridani.Algorithms.Lean.BTree.Range

/-!
# Node-visit cost of B-tree closed-interval queries

`rangeT` instantiates `rangeM` at `TimeM ℕ` with the free comparator `leT` and `visit := tick 1`,
so the time of a run is the number of nodes it visits. `ret_rangeT` identifies its value with
`range`, through the transfer lemma `Cslib.IsMonadHom.map_rangeM`.

`time_rangeT` bounds the visits on a well-formed tree by `2 * height + k`, where `k` is the length
of the output. A visited node either returns one of its own keys or has every key outside the
interval; in the second case the keys that can lie below it straddle `lo` or `hi`, and at each
depth at most one node straddles each bound. The proof makes this precise with three auxiliary
bounds, by recursion on the tree:

* a subtree whose entries all lie in the interval is visited at most once per returned entry,
  because every occupied node has a key when `2 ≤ t`;
* a subtree whose keys are all at least `lo`, or all at most `hi`, is visited at most
  `height + k` times: only the path towards the other bound is unpaid;
* at the node where `lo` and `hi` part ways, the child towards `lo` has all its keys at most
  `hi` and the remaining triples have all their keys at least `lo`.

Occupancy is needed: a chain of keyless nodes inside the interval would be visited without
contributing output. `time_rangeT_le_log` composes the bound with `IsWF.height_le_log`.
-/

public section

open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace EpsilonEridani.BTree

section NodeVisits

variable {α β : Type} [LinearOrder α] {t : ℕ} {tr : BTree α β}

/-- Closed-interval query, charging one tick per node visited. -/
def rangeT (lo hi : α) (tr : BTree α β) : TimeM ℕ (List (α × β)) :=
  rangeM leT (tick 1) lo hi tr

/-- `rangeT` is `rangeM` with the free comparator and one tick per visit. -/
theorem rangeT_def (lo hi : α) : rangeT lo hi tr = rangeM leT (tick 1) lo hi tr := (rfl)

/-- The value of `rangeT` is `range`. -/
@[simp] theorem ret_rangeT (lo hi : α) : (rangeT lo hi tr).ret = range lo hi tr := by
  simpa only [range_def, rangeT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_rangeM leT (tick 1) lo hi tr)

/-- The empty tree is not visited. -/
@[simp] theorem time_rangeT_leaf (lo hi : α) : (rangeT lo hi (.leaf : BTree α β)).time = 0 := by
  simp [rangeT, rangeM_leaf]

/-- A node without keys is visited once before its only child. -/
theorem time_rangeT_node_nil (lo hi : α) (first : BTree α β) :
    (rangeT lo hi (.node first [])).time = (rangeT lo hi first).time + 1 := by
  simp [rangeT, rangeM_node, rangeRestM_nil]
  omega

/-- At the first separator, the child before it is entered when the separator is at least `lo`,
and the remaining triples are scanned, as the node without its first child and separator, when
the separator is at most `hi`. That node accounts for the single visit of the original node. -/
theorem time_rangeT_node_cons (lo hi k : α) (v : β) (first c : BTree α β)
    (rest : List (α × β × BTree α β)) :
    (rangeT lo hi (.node first ((k, v, c) :: rest))).time =
      (if lo ≤ k then (rangeT lo hi first).time else 0) +
        (if k ≤ hi then (rangeT lo hi (.node c rest)).time else 1) := by
  by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi <;>
    simp [rangeT, rangeM_node, rangeRestM_cons, hlo, hhi] <;> omega

/-! ### Auxiliary bounds -/

variable {lo hi : α}

private theorem length_range_node_cons (k : α) (v : β) (first c : BTree α β)
    (rest : List (α × β × BTree α β)) :
    (range lo hi (.node first ((k, v, c) :: rest))).length =
      (if lo ≤ k then (range lo hi first).length else 0) +
        (if k ≤ hi then (range lo hi (.node c rest)).length + (if lo ≤ k then 1 else 0)
         else 0) := by
  by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi <;> simp [hlo, hhi]

/-- Facts about the two parts into which the first separator splits a node. -/
private theorem node_cons_parts {k : α} {v : β} {first c : BTree α β}
    {rest : List (α × β × BTree α β)}
    (hc : ∀ c' ∈ (node first ((k, v, c) :: rest)).children, Occupied t c')
    (hs : (node first ((k, v, c) :: rest)).toList.IsSortedAssoc) :
    Occupied t first ∧ (∀ c' ∈ first.children, Occupied t c') ∧
      (∀ c' ∈ (node c rest).children, Occupied t c') ∧
      first.toList.IsSortedAssoc ∧ (node c rest).toList.IsSortedAssoc ∧
      (∀ p ∈ first.toList, p.1 < k) ∧ (∀ p ∈ (node c rest).toList, k < p.1) := by
  have hfirst : Occupied t first := hc first (by simp)
  rw [toList_node, toListRest_cons, List.cons_append] at hs
  obtain ⟨h₁, h₂, hlt, hgt⟩ := List.isSortedAssoc_append_cons_iff.1 hs
  refine ⟨hfirst, fun c' h' => hfirst.of_mem_children h', fun c' h' => hc c' ?_, h₁,
    by simpa using h₂, hlt, by simpa using hgt⟩
  simp only [children_node, List.map_cons, List.mem_cons] at h' ⊢
  tauto

omit [LinearOrder α] in
/-- Every entry of the node is in its first child, is the first separator, or is in the node
without its first child and separator. -/
private theorem mem_toList_node_cons {k : α} {v : β} {first c : BTree α β}
    {rest : List (α × β × BTree α β)} {p : α × β} :
    p ∈ (node first ((k, v, c) :: rest)).toList ↔
      p ∈ first.toList ∨ p = (k, v) ∨ p ∈ (node c rest).toList := by
  simp only [toList_node, toListRest_cons, List.cons_append, List.mem_append, List.mem_cons]

/-- A query whose interval contains every entry visits each node once and returns at least one
entry per occupied node. The root's keys pay for its own visit and for the visit it causes in
the node without its first child. -/
private theorem time_rangeT_add_rootKeys_le {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hin : ∀ p ∈ tr.toList, lo ≤ p.1 ∧ p.1 ≤ hi) :
    (rangeT lo hi tr).time + tr.rootKeys ≤ (range lo hi tr).length + 1 := by
  have occ {c : BTree α β} (ho : Occupied t c)
      (h : (rangeT lo hi c).time + c.rootKeys ≤ (range lo hi c).length + 1) :
      (rangeT lo hi c).time ≤ (range lo hi c).length := by
    cases c with
    | leaf => simp
    | node _ _ =>
      have := ho.one_le_rootKeys ht (by simp)
      omega
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := time_rangeT_add_rootKeys_le ht (fun c h => hfirst.of_mem_children h)
      (by simpa using hs) (fun p hp => hin p (by simpa using hp))
    have := occ hfirst ih
    simp [time_rangeT_node_nil, rootKeys]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hfirst, hcf, hcn, hsf, hsn, -, -⟩ := node_cons_parts hc hs
    have hk := hin (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have ih₁ := time_rangeT_add_rootKeys_le ht hcf hsf
      (fun p hp => hin p (mem_toList_node_cons.2 (Or.inl hp)))
    have ih₂ := time_rangeT_add_rootKeys_le ht hcn hsn
      (fun p hp => hin p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
    have := occ hfirst ih₁
    simp only [rootKeys, List.length_cons] at ih₂ ⊢
    rw [time_rangeT_node_cons, length_range_node_cons]
    simp only [hk.1, hk.2, ↓reduceIte]
    omega
termination_by sizeOf tr

/-- An occupied tree whose entries all lie in the interval is visited at most once per entry
returned. -/
private theorem time_rangeT_le_of_occupied (ht : 2 ≤ t) (ho : Occupied t tr)
    (hs : tr.toList.IsSortedAssoc) (hin : ∀ p ∈ tr.toList, lo ≤ p.1 ∧ p.1 ≤ hi) :
    (rangeT lo hi tr).time ≤ (range lo hi tr).length := by
  have h := time_rangeT_add_rootKeys_le ht (fun c hc => ho.of_mem_children hc) hs hin
  cases tr with
  | leaf => simp
  | node _ _ =>
    have := ho.one_le_rootKeys ht (by simp)
    omega

/-- A query on a tree whose keys are all at least `lo` pays at most one unproductive visit per
level, on the path towards `hi`. -/
private theorem time_rangeT_le_of_forall_lo_le {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hlo : ∀ p ∈ tr.toList, lo ≤ p.1) :
    (rangeT lo hi tr).time ≤ tr.height + (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := time_rangeT_le_of_forall_lo_le (hi := hi) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
      (fun p hp => hlo p (by simpa using hp))
    have e := height_first_succ_le (first := first) (rest := [])
    rw [time_rangeT_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨hfirst, hcf, hcn, hsf, hsn, hlt, -⟩ := node_cons_parts hc hs
    have hk : lo ≤ k := hlo (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [time_rangeT_node_cons, length_range_node_cons]
    by_cases hhi : k ≤ hi
    · have h₁ := time_rangeT_le_of_occupied ht hfirst hsf
        (fun p hp => ⟨hlo p (mem_toList_node_cons.2 (Or.inl hp)), ((hlt p hp).trans_le hhi).le⟩)
      have h₂ := time_rangeT_le_of_forall_lo_le (hi := hi) ht hcn hsn
        (fun p hp => hlo p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
      simp only [hk, hhi, ↓reduceIte]
      omega
    · have h₁ := time_rangeT_le_of_forall_lo_le (hi := hi) ht hcf hsf
        (fun p hp => hlo p (mem_toList_node_cons.2 (Or.inl hp)))
      simp only [hk, hhi, ↓reduceIte]
      omega
termination_by sizeOf tr

/-- A query on a tree whose keys are all at most `hi` pays at most one unproductive visit per
level, on the path towards `lo`. -/
private theorem time_rangeT_le_of_forall_le_hi {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc)
    (hhi : ∀ p ∈ tr.toList, p.1 ≤ hi) :
    (rangeT lo hi tr).time ≤ tr.height + (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := time_rangeT_le_of_forall_le_hi (lo := lo) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
      (fun p hp => hhi p (by simpa using hp))
    have e := height_first_succ_le (first := first) (rest := [])
    rw [time_rangeT_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨-, hcf, hcn, hsf, hsn, -, hgt⟩ := node_cons_parts hc hs
    have hk : k ≤ hi := hhi (k, v) (mem_toList_node_cons.2 (Or.inr (Or.inl rfl)))
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [time_rangeT_node_cons, length_range_node_cons]
    by_cases hlo : lo ≤ k
    · have h₁ := time_rangeT_le_of_forall_le_hi (lo := lo) ht hcf hsf
        (fun p hp => hhi p (mem_toList_node_cons.2 (Or.inl hp)))
      have h₂ := time_rangeT_add_rootKeys_le ht hcn hsn
        (fun p hp => ⟨hlo.trans (hgt p hp).le, hhi p (mem_toList_node_cons.2 (Or.inr (Or.inr hp)))⟩)
      simp only [rootKeys] at h₂
      simp only [hk, hlo, ↓reduceIte]
      omega
    · have h₂ := time_rangeT_le_of_forall_le_hi (lo := lo) ht hcn hsn
        (fun p hp => hhi p (mem_toList_node_cons.2 (Or.inr (Or.inr hp))))
      simp only [hk, hlo, ↓reduceIte]
      omega
termination_by sizeOf tr

/-- The general bound: below the node where `lo` and `hi` part ways, each of the two boundary
paths pays at most one unproductive visit per level. -/
private theorem time_rangeT_le_of_sorted {lo hi : α} {tr : BTree α β} (ht : 2 ≤ t)
    (hc : ∀ c ∈ tr.children, Occupied t c) (hs : tr.toList.IsSortedAssoc) :
    (rangeT lo hi tr).time ≤ 2 * tr.height + (range lo hi tr).length := by
  match tr with
  | .leaf => simp
  | .node first [] =>
    have hfirst : Occupied t first := hc first (by simp)
    have ih := time_rangeT_le_of_sorted (lo := lo) (hi := hi) ht
      (fun c h => hfirst.of_mem_children h) (by simpa using hs)
    have e := height_first_succ_le (first := first) (rest := [])
    rw [time_rangeT_node_nil, range_node_nil]
    omega
  | .node first ((k, v, c) :: rest) =>
    obtain ⟨-, hcf, hcn, hsf, hsn, hlt, hgt⟩ := node_cons_parts hc hs
    have e₁ := height_first_succ_le (first := first) (rest := (k, v, c) :: rest)
    have e₂ := height_node_le_height_node_cons (first := first) (k := k) (v := v) (c := c)
      (rest := rest)
    rw [time_rangeT_node_cons, length_range_node_cons]
    by_cases hlo : lo ≤ k <;> by_cases hhi : k ≤ hi
    · have h₁ := time_rangeT_le_of_forall_le_hi (lo := lo) ht hcf hsf
        (fun p hp => ((hlt p hp).trans_le hhi).le)
      have h₂ := time_rangeT_le_of_forall_lo_le (hi := hi) ht hcn hsn
        (fun p hp => (hlo.trans_lt (hgt p hp)).le)
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · have h₁ := time_rangeT_le_of_sorted (lo := lo) (hi := hi) ht hcf hsf
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · have h₂ := time_rangeT_le_of_sorted (lo := lo) (hi := hi) ht hcn hsn
      simp only [hlo, hhi, ↓reduceIte]
      omega
    · simp only [hlo, hhi, ↓reduceIte]
      omega
termination_by sizeOf tr

/-! ### Node-visit bounds -/

/-- A closed-interval query on a well-formed tree visits at most `2 * height + k` nodes, where `k`
is the number of entries it returns. -/
theorem time_rangeT (h : IsWF t tr) (lo hi : α) :
    (rangeT lo hi tr).time ≤ 2 * tr.height + (range lo hi tr).length :=
  time_rangeT_le_of_sorted h.two_le h.occupied_of_mem_children h.sorted

/-- A closed-interval query on a well-formed tree visits logarithmically many nodes beyond one per
entry it returns. -/
theorem time_rangeT_le_log (h : IsWF t tr) (lo hi : α) :
    (rangeT lo hi tr).time ≤ 2 * (Nat.log t ((tr.size + 1) / 2) + 1) + (range lo hi tr).length :=
  (time_rangeT h lo hi).trans (by have := h.height_le_log; omega)

/-! ### Examples -/

private def rangeTExample : BTree ℕ String :=
  .node (.node .leaf [(1, "a", .leaf), (2, "b", .leaf)])
    [(3, "c", .node .leaf [(4, "d", .leaf), (5, "e", .leaf)]),
     (6, "f", .node .leaf [(7, "g", .leaf), (8, "h", .leaf)])]

/-- An interval spanning all three children visits every node. -/
example : (rangeT 2 7 rangeTExample).time = 4 := by
  simp [rangeTExample, rangeT, rangeM_node, rangeRestM_cons, rangeRestM_nil, rangeM_leaf]

/-- An interval inside one child visits the root and that child. -/
example : (rangeT 4 5 rangeTExample).time = 2 := by
  simp [rangeTExample, rangeT, rangeM_node, rangeRestM_cons, rangeRestM_nil, rangeM_leaf]

/-- An interval above every key visits only the root and its last child. -/
example : (rangeT 9 10 rangeTExample).time = 2 := by
  simp [rangeTExample, rangeT, rangeM_node, rangeRestM_cons, rangeRestM_nil, rangeM_leaf]

end NodeVisits

end EpsilonEridani.BTree
