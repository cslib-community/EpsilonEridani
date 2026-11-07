/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Cost.Query
public import EpsilonEridani.Algorithms.Lean.BTree.Erase.MinMax

/-!
# Node-visit costs of B-tree erasure

`eraseT`, `eraseMinT` and `eraseMaxT` instantiate `eraseM`, `eraseMinM` and `eraseMaxM` at
`TimeM ℕ` with the free comparator `leT` and `visit := tick 1`, so the time of a run is the number
of nodes it visits. `ret_eraseT`, `ret_eraseMinT` and `ret_eraseMaxT` identify their values with
`erase`, `eraseMin?` and `eraseMax?`, through the transfer lemmas `Cslib.IsMonadHom.map_eraseM`,
`map_eraseMinM` and `map_eraseMaxM`.

Bottom-up erasure visits, at each level, the node on its search path (below the key's node, the
path of `popMinM` to the successor) and, when the child it returns from underflows, the one
sibling the repair merges it with; the root has no sibling. A repair costs at most one visit
(`time_rebalanceRightM_le`, `time_rebalanceLastM_le`). `time_popMinM_le` bounds the removal of
the least entry of a subtree by `2 * height - 1`, because the deepest node on its path has a leaf
as its first child, so `popMinM` returns from it without a repair. `time_eraseSubtreeM_le` bounds
erasure from a subtree by `2 * height`, and `time_eraseRestM_le` the scan of a node's triples,
given a bound on the erasure of the child before them. On every tree, well-formed or not,
`time_eraseT` states `2 * height`, and `time_eraseMinT` and `time_eraseMaxT` state `3 * height`: a
pass to the extreme entry, then erasure of its key. The `_le_log` corollaries compose these with
`IsWF.height_le_log`.
-/

public section

open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace EpsilonEridani.BTree

section NodeVisits

variable {α β : Type} {t : ℕ} {tr : BTree α β}

/-- A repair against the right sibling visits at most that sibling. -/
theorem time_rebalanceRightM_le (c : BTree α β) (k : α) (v : β) (s : BTree α β)
    (rest : List (α × β × BTree α β)) :
    (rebalanceRightM t (tick 1) c k v s rest).time ≤ 1 := by
  rw [rebalanceRightM_def]
  split <;> simp

/-- A repair against the left sibling visits at most that sibling. -/
theorem time_rebalanceLastM_le (prev : BTree α β) (k : α) (v : β) (c : BTree α β) :
    (rebalanceLastM t (tick 1) prev k v c).time ≤ 1 := by
  rw [rebalanceLastM_def]
  split <;> simp

/-- Removing the least entry of a subtree visits at most `2 * height - 1` nodes: one node and at
most one repaired sibling per level, with no repair at the deepest node, whose first child is a
leaf. -/
theorem time_popMinM_le (tr : BTree α β) : (popMinM t (tick 1) tr).time ≤ 2 * tr.height - 1 := by
  match tr with
  | .leaf => simp
  | .node .leaf [] => simp [popMinM_node]
  | .node .leaf ((k, v, c) :: rest) =>
    simp [popMinM_node]
    omega
  | .node (.node f r) rest =>
    have h := time_popMinM_le (.node f r)
    have e : (node f r).height + 1 ≤ (node (.node f r) rest).height := height_first_succ_le
    have e₁ : f.height + 1 ≤ (node f r).height := height_first_succ_le
    generalize (node (.node f r) rest).height = H at e ⊢
    simp only [popMinM_node (first := .node f r), TimeM.time_bind, TimeM.time_tick]
    generalize (node f r).height = h₁ at h e e₁
    split
    · simp; omega
    · simp; omega
    · simp; omega
    · rename_i first' k v c rest' _
      have := time_rebalanceRightM_le (t := t) first' k v c rest'
      simp
      omega
termination_by sizeOf tr

variable [LinearOrder α]

mutual
/-- Erasure from a subtree visits at most `2 * height` nodes: per level, the node on the search
path and at most one sibling inspected by a repair. -/
theorem time_eraseSubtreeM_le (k : α) (tr : BTree α β) :
    (eraseSubtreeM t leT (tick 1) k tr).time ≤ 2 * tr.height := by
  match tr with
  | .leaf => simp
  | .node first rest =>
    have := time_eraseRestM_le k first (eraseSubtreeM t leT (tick 1) k first) rest
      (H := (node first rest).height) height_first_succ_le (time_eraseSubtreeM_le k first)
      (heightRest_le_iff.2 fun _ he => height_succ_le_of_mem_rest he)
    have e : first.height + 1 ≤ (node first rest).height := height_first_succ_le
    simp only [eraseSubtreeM_node, TimeM.time_bind, TimeM.time_tick, TimeM.time_pure]
    omega
termination_by sizeOf tr

/-- Erasure among the triples after the child `prev` visits at most `2 * H - 1` nodes, for a
bound `H` on the height of the node they belong to, when the erasure `prevErased` of `prev`
visits at most `2 * prev.height` nodes. -/
theorem time_eraseRestM_le (k : α) (prev : BTree α β) (prevErased : TimeM ℕ (BTree α β))
    (rest : List (α × β × BTree α β)) {H : ℕ} (hprev : prev.height + 1 ≤ H)
    (hpe : prevErased.time ≤ 2 * prev.height) (hrest : heightRest rest ≤ H) :
    (eraseRestM t leT (tick 1) k prev prevErased rest).time ≤ 2 * H - 1 := by
  match rest with
  | [] =>
    simp only [eraseRestM_nil, TimeM.time_bind, TimeM.time_pure]
    omega
  | (k', v', c) :: rest =>
    rw [heightRest_cons] at hrest
    have hc := time_eraseSubtreeM_le k c
    have hp := time_popMinM_le (t := t) c
    simp only [eraseRestM_cons, leT, pure_bind]
    by_cases hk : k ≤ k'
    · by_cases hk' : k' ≤ k
      · simp only [hk, hk', decide_true, ↓reduceIte, TimeM.time_bind]
        split
        · simp; omega
        · rename_i k₂ v₂ c' _
          rcases rest with _ | ⟨⟨k₃, v₃, c₃⟩, rest₃⟩
          · have := time_rebalanceLastM_le (t := t) prev k₂ v₂ c'
            simp only
            omega
          · have := time_rebalanceRightM_le (t := t) c' k₃ v₃ c₃ rest₃
            simp only [TimeM.time_bind, TimeM.time_pure]
            omega
      · have := time_rebalanceRightM_le (t := t) prevErased.ret k' v' c rest
        simp only [hk, hk', decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
          TimeM.time_bind]
        omega
    · simp only [hk, decide_false, Bool.false_eq_true, ↓reduceIte]
      match hr : rest with
      | [] =>
        have := time_rebalanceLastM_le (t := t) prev k' v' (eraseSubtreeM t leT (tick 1) k c).ret
        simp only [TimeM.time_bind]
        omega
      | e :: rest =>
        have := time_eraseRestM_le k c (eraseSubtreeM t leT (tick 1) k c) (e :: rest)
          (H := H) (by omega) hc (by omega)
        simp only [TimeM.time_bind, TimeM.time_pure]
        omega
termination_by sizeOf rest
end

/-- Erasure, charging one tick per node visited. -/
def eraseT (t : ℕ) (k : α) (tr : BTree α β) : TimeM ℕ (BTree α β) := eraseM t leT (tick 1) k tr

/-- `eraseT` is `eraseM` with the free comparator and one tick per visit. -/
theorem eraseT_def (k : α) : eraseT t k tr = eraseM t leT (tick 1) k tr := (rfl)

/-- Removal of the least entry, charging one tick per node visited. -/
def eraseMinT (t : ℕ) (tr : BTree α β) : TimeM ℕ (Option ((α × β) × BTree α β)) :=
  eraseMinM t leT (tick 1) tr

/-- `eraseMinT` is `eraseMinM` with the free comparator and one tick per visit. -/
theorem eraseMinT_def : eraseMinT t tr = eraseMinM t leT (tick 1) tr := (rfl)

/-- Removal of the greatest entry, charging one tick per node visited. -/
def eraseMaxT (t : ℕ) (tr : BTree α β) : TimeM ℕ (Option ((α × β) × BTree α β)) :=
  eraseMaxM t leT (tick 1) tr

/-- `eraseMaxT` is `eraseMaxM` with the free comparator and one tick per visit. -/
theorem eraseMaxT_def : eraseMaxT t tr = eraseMaxM t leT (tick 1) tr := (rfl)

/-- The value of `eraseT` is `erase`. -/
@[simp] theorem ret_eraseT (k : α) : (eraseT t k tr).ret = erase t k tr := by
  simpa only [erase_def, eraseT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_eraseM t leT (tick 1) k tr)

/-- The value of `eraseMinT` is `eraseMin?`. -/
@[simp] theorem ret_eraseMinT : (eraseMinT t tr).ret = eraseMin? t tr := by
  simpa only [eraseMin?_def, eraseMinT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_eraseMinM t leT (tick 1) tr)

/-- The value of `eraseMaxT` is `eraseMax?`. -/
@[simp] theorem ret_eraseMaxT : (eraseMaxT t tr).ret = eraseMax? t tr := by
  simpa only [eraseMax?_def, eraseMaxT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_eraseMaxM t leT (tick 1) tr)

/-- Erasure visits exactly the nodes that erasure from the root subtree visits: collapsing an
empty root costs nothing. -/
theorem time_eraseT_eq (k : α) :
    (eraseT t k tr).time = (eraseSubtreeM t leT (tick 1) k tr).time := by
  simp [eraseT, eraseM_def]

/-- Erasure from the empty tree visits nothing. -/
@[simp] theorem time_eraseT_leaf (k : α) : (eraseT t k (.leaf : BTree α β)).time = 0 := by
  simp [time_eraseT_eq]

/-- Removing the least entry of the empty tree visits nothing. -/
@[simp] theorem time_eraseMinT_leaf : (eraseMinT t (.leaf : BTree α β)).time = 0 := by
  simp [eraseMinT]

/-- Removing the greatest entry of the empty tree visits nothing. -/
@[simp] theorem time_eraseMaxT_leaf : (eraseMaxT t (.leaf : BTree α β)).time = 0 := by
  simp [eraseMaxT]

/-- Erasure visits at most `2 * height` nodes: per level, the node on the search path (below the
key's node, on the path to its successor) and at most one sibling inspected by a repair; the root
has no sibling. The top-down algorithm of Cormen et al. inspects at most one child and two
siblings per level and states `3 * height` instead. -/
theorem time_eraseT (k : α) : (eraseT t k tr).time ≤ 2 * tr.height := by
  rw [time_eraseT_eq]
  exact time_eraseSubtreeM_le k tr

/-- Removing the least entry visits at most `3 * height` nodes: a pass to the least entry, then
erasure of its key. -/
theorem time_eraseMinT : (eraseMinT t tr).time ≤ 3 * tr.height := by
  have h₁ := time_minT (tr := tr)
  rw [minT_def] at h₁
  simp only [eraseMinT, eraseMinM_def, TimeM.time_bind]
  split
  · simp; omega
  · rename_i p _
    have h₂ := time_eraseT (t := t) (tr := tr) p.1
    simp only [eraseT] at h₂
    simp
    omega

/-- Removing the greatest entry visits at most `3 * height` nodes: a pass to the greatest entry,
then erasure of its key. -/
theorem time_eraseMaxT : (eraseMaxT t tr).time ≤ 3 * tr.height := by
  have h₁ := time_maxT (tr := tr)
  rw [maxT_def] at h₁
  simp only [eraseMaxT, eraseMaxM_def, TimeM.time_bind]
  split
  · simp; omega
  · rename_i p _
    have h₂ := time_eraseT (t := t) (tr := tr) p.1
    simp only [eraseT] at h₂
    simp
    omega

/-- Erasure from a well-formed tree visits logarithmically many nodes. -/
theorem time_eraseT_le_log (h : IsWF t tr) (k : α) :
    (eraseT t k tr).time ≤ 2 * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  (time_eraseT k).trans (Nat.mul_le_mul_left 2 h.height_le_log)

/-- Removing the least entry of a well-formed tree visits logarithmically many nodes. -/
theorem time_eraseMinT_le_log (h : IsWF t tr) :
    (eraseMinT t tr).time ≤ 3 * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  time_eraseMinT.trans (Nat.mul_le_mul_left 3 h.height_le_log)

/-- Removing the greatest entry of a well-formed tree visits logarithmically many nodes. -/
theorem time_eraseMaxT_le_log (h : IsWF t tr) :
    (eraseMaxT t tr).time ≤ 3 * (Nat.log t ((tr.size + 1) / 2) + 1) :=
  time_eraseMaxT.trans (Nat.mul_le_mul_left 3 h.height_le_log)

/-! ### Examples -/

/-- Erasing the only key of a one-node tree visits that node only: the root has no sibling. -/
example : (eraseT 2 1 (BTree.node .leaf [(1, 1, .leaf)] : BTree ℕ ℕ)).time = 1 := by
  decide

/-- A two-level tree at `t = 2`: erasing `1` visits the root, the left child, which underflows,
and its right sibling for the repair. -/
example :
    (eraseT 2 1 (BTree.node (.node .leaf [(1, 1, .leaf)])
      [(2, 2, .node .leaf [(3, 3, .leaf)])] : BTree ℕ ℕ)).time = 3 := by
  decide

end NodeVisits

end EpsilonEridani.BTree
