/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Defs
public import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Size and height of classic B-trees

The three inequalities relating the size and height of a well-formed classic B-tree of minimum
degree `t`, after Cormen, Leiserson, Rivest and Stein, *Introduction to Algorithms*, Chapter 18:

* `IsWF.le_size`: a non-empty tree of height `h` has at least `2 * t ^ (h - 1) - 1` entries;
* `IsWF.size_le`: a tree of height `h` has at most `(2 * t) ^ h - 1` entries;
* `IsWF.height_le_log`: the height is at most `Nat.log t ((size + 1) / 2) + 1`, the bound of
  Theorem 18.1 with heights counted in nodes rather than edges.

They follow from the corresponding bounds for non-root subtrees, `Occupied.pow_sub_one_le_size`
and `Occupied.size_le`. These are structural facts about the shape of a tree; they carry no cost
content.
-/

public section

namespace EpsilonEridani.BTree

variable {α : Type*} {β : Type*}

/-! ### Nodes -/

section Node

variable {first : BTree α β} {rest : List (α × β × BTree α β)}

/-- The entries of a list of triples: one per key, plus those of the children. -/
theorem length_toListRest :
    (toListRest rest).length = rest.length + (rest.map fun e => e.2.2.size).sum := by
  induction rest with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨k, v, c⟩ := e
    simp only [toListRest_cons, List.length_cons, List.length_append, ih, List.map_cons,
      List.sum_cons, length_toList]
    omega

/-- The size of a node: its first child's, one per key, and its other children's. -/
theorem size_node :
    (node first rest).size = first.size + rest.length + (rest.map fun e => e.2.2.size).sum := by
  rw [← length_toList, toList_node, List.length_append, length_toListRest, length_toList,
    Nat.add_assoc]

/-- A node whose children each hold at least `n - 1` entries holds at least
`(rest.length + 1) * n - 1`. -/
theorem le_size_node {n : ℕ} (h₁ : n - 1 ≤ first.size) (h₂ : ∀ e ∈ rest, n - 1 ≤ e.2.2.size) :
    (rest.length + 1) * n - 1 ≤ (node first rest).size := by
  have hs :=
    (rest.map fun e => e.2.2.size).length_nsmul_le_sum (n - 1) (List.forall_mem_map.2 h₂)
  rw [List.length_map, Nat.nsmul_eq_mul] at hs
  rw [size_node]
  obtain _ | n := n
  · simp
  · rw [Nat.add_sub_cancel] at h₁ hs
    rw [Nat.add_mul, Nat.mul_add]
    omega

/-- A node whose children each hold at most `n - 1` entries, for positive `n`, holds at most
`(rest.length + 1) * n - 1`. -/
theorem size_node_le {n : ℕ} (hn : 0 < n) (h₁ : first.size ≤ n - 1)
    (h₂ : ∀ e ∈ rest, e.2.2.size ≤ n - 1) : (node first rest).size ≤ (rest.length + 1) * n - 1 := by
  have hs :=
    (rest.map fun e => e.2.2.size).sum_le_length_nsmul (n - 1) (List.forall_mem_map.2 h₂)
  rw [List.length_map, Nat.nsmul_eq_mul] at hs
  rw [size_node]
  obtain _ | n := n
  · omega
  · rw [Nat.add_sub_cancel] at h₁ hs
    rw [Nat.add_mul, Nat.mul_add]
    omega

end Node

/-! ### Bounds -/

variable {t : ℕ} {tr : BTree α β}

/-- A balanced occupied subtree of height `h` holds at least `t ^ h - 1` entries. -/
theorem Occupied.pow_sub_one_le_size (ho : Occupied t tr) (hb : Balanced tr) :
    t ^ tr.height - 1 ≤ tr.size := by
  induction tr with
  | leaf => simp
  | node first rest ih₁ ih₂ =>
    have hc : ∀ e ∈ rest, t ^ first.height - 1 ≤ e.2.2.size := fun e he =>
      hb.height_of_mem_rest he ▸ ih₂ e he (ho.of_mem_rest he) (hb.of_mem_rest he)
    refine le_trans ?_ (le_size_node (ih₁ ho.first hb.first) hc)
    rw [hb.height_node, Nat.pow_succ']
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (by have := ho.le_length; omega)) 1

/-- A balanced occupied subtree of height `h` holds at most `(2 * t) ^ h - 1` entries. -/
theorem Occupied.size_le (ho : Occupied t tr) (hb : Balanced tr) :
    tr.size ≤ (2 * t) ^ tr.height - 1 := by
  induction tr with
  | leaf => simp
  | node first rest ih₁ ih₂ =>
    have hf := ih₁ ho.first hb.first
    have hc : ∀ e ∈ rest, e.2.2.size ≤ (2 * t) ^ first.height - 1 := fun e he =>
      hb.height_of_mem_rest he ▸ ih₂ e he (ho.of_mem_rest he) (hb.of_mem_rest he)
    have hm := ho.length_le
    rw [hb.height_node, Nat.pow_succ']
    obtain rfl | ht := Nat.eq_zero_or_pos t
    · obtain rfl : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      have : (2 * 0) ^ first.height - 1 = 0 := by cases first.height <;> simp
      simp only [size_node, List.length_nil, List.map_nil, List.sum_nil]
      omega
    · exact (size_node_le (Nat.pow_pos (by omega)) hf hc).trans
        (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (by omega)) 1)

variable [LinearOrder α]

/-- A non-empty well-formed tree of height `h` holds at least `2 * t ^ (h - 1) - 1` entries. -/
theorem IsWF.le_size (h : IsWF t tr) (hne : tr ≠ .leaf) :
    2 * t ^ (tr.height - 1) - 1 ≤ tr.size := by
  cases tr with
  | leaf => exact absurd rfl hne
  | node first rest =>
    have hb := h.balanced
    have hk := h.rootKeys_pos hne
    rw [rootKeys_node] at hk
    have hc : ∀ e ∈ rest, t ^ first.height - 1 ≤ e.2.2.size := fun e he =>
      hb.height_of_mem_rest he ▸
        (h.occupied_of_mem_rest he).pow_sub_one_le_size (hb.of_mem_rest he)
    refine le_trans ?_ (le_size_node (h.occupied_first.pow_sub_one_le_size hb.first) hc)
    rw [hb.height_node, Nat.add_sub_cancel]
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (by omega)) 1

/-- A well-formed tree of height `h` holds at most `(2 * t) ^ h - 1` entries. -/
theorem IsWF.size_le (h : IsWF t tr) : tr.size ≤ (2 * t) ^ tr.height - 1 := by
  cases tr with
  | leaf => simp
  | node first rest =>
    have hb := h.balanced
    have hk := h.rootKeys_le
    rw [rootKeys_node] at hk
    have ht := h.two_le
    have hc : ∀ e ∈ rest, e.2.2.size ≤ (2 * t) ^ first.height - 1 := fun e he =>
      hb.height_of_mem_rest he ▸ (h.occupied_of_mem_rest he).size_le (hb.of_mem_rest he)
    rw [hb.height_node, Nat.pow_succ']
    exact (size_node_le (Nat.pow_pos (by omega)) (h.occupied_first.size_le hb.first) hc).trans
      (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (by omega)) 1)

/-- The height of a well-formed tree is logarithmic in its size (Cormen et al., Theorem 18.1). -/
theorem IsWF.height_le_log (h : IsWF t tr) : tr.height ≤ Nat.log t ((tr.size + 1) / 2) + 1 := by
  rcases eq_or_ne tr .leaf with rfl | hne
  · simp
  have ht := h.two_le
  have hs := h.le_size hne
  have hle : t ^ (tr.height - 1) ≤ (tr.size + 1) / 2 :=
    (Nat.le_div_iff_mul_le (by decide)).2 (by omega)
  have := Nat.le_log_of_pow_le (by omega) hle
  omega

/-! ### Examples -/

/-- The bound at a root with one key and two leaf children: height `1`, size `1`. -/
example :
    (BTree.node (α := ℕ) (β := Unit) .leaf [(1, (), .leaf)]).height ≤
      Nat.log 2 (((BTree.node (α := ℕ) (β := Unit) .leaf [(1, (), .leaf)]).size + 1) / 2) + 1 := by
  decide

end EpsilonEridani.BTree
