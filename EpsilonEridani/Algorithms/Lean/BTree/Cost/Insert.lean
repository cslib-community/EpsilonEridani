/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Cost.Query
public import EpsilonEridani.Algorithms.Lean.BTree.Insert

/-!
# Node-visit cost of B-tree insertion

`insertT` instantiates `insertM` at `TimeM ℕ` with the free comparator `leT` and
`visit := tick 1`, so the time of a run is the number of nodes it visits. `ret_insertT`
identifies its value with `insert`, through the transfer lemma `Cslib.IsMonadHom.map_insertM`.

Insertion visits each node of its search path once, on the way down; the splits on the way back
up and the new root grown on overflow cost no visits, because they only rebuild nodes already in
hand. `time_insertOrSplitM_le` bounds the visits into a subtree by its height, on every tree,
well-formed or not, and `time_insertT` states the bound for `insertT`. The scan of a node's
triples descends into at most one child, and visits nothing when it defers to the child before
them (`time_insertRestM_eq_zero_of_ret_eq_none`), so a node and the single child it descends into
account for every visit. `time_insertT_le_log` composes the bound with `IsWF.height_le_log`.
-/

public section

open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace EpsilonEridani.BTree

section NodeVisits

variable {α β : Type} [LinearOrder α] {t : ℕ} {k : α} {v : β} {tr : BTree α β}

/-- Insertion, charging one tick per node visited. -/
def insertT (t : ℕ) (k : α) (v : β) (tr : BTree α β) : TimeM ℕ (BTree α β) :=
  insertM t leT (tick 1) k v tr

/-- `insertT` is `insertM` with the free comparator and one tick per visit. -/
theorem insertT_def : insertT t k v tr = insertM t leT (tick 1) k v tr := (rfl)

/-- The value of `insertT` is `insert`. -/
@[simp] theorem ret_insertT : (insertT t k v tr).ret = insert t k v tr := by
  simpa only [insert_def, insertT, leI, Id.run_pure, TimeM.ret_pure, TimeM.ret_tick] using
    Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_insertM t leT (tick 1) k v tr)

/-- Insertion visits exactly the nodes that the bottom-up insertion into the tree visits: growing
a new root costs nothing. -/
theorem time_insertT_eq :
    (insertT t k v tr).time = (insertOrSplitM t leT (tick 1) k v tr).time := by
  simp [insertT, insertM]

/-- Insertion into the empty tree visits nothing. -/
@[simp] theorem time_insertT_leaf : (insertT t k v (.leaf : BTree α β)).time = 0 := by
  simp [insertT, insertM]

/-- When the scan of a node's triples defers to the child before them, it has visited nothing:
the scan descends into a child only past a key below the query, and then returns new triples. -/
theorem time_insertRestM_eq_zero_of_ret_eq_none {rest : List (α × β × BTree α β)}
    (h : (insertRestM t leT (tick 1) k v rest).ret = none) :
    (insertRestM t leT (tick 1) k v rest).time = 0 := by
  match rest with
  | [] => simp
  | (k', v', c) :: rest =>
    by_cases hk : k ≤ k'
    · by_cases hk' : k' ≤ k <;> simp [insertRestM_cons, hk, hk']
    · simp only [insertRestM_cons, hk, decide_false, TimeM.ret_bind, TimeM.ret_pure,
        Bool.false_eq_true, ↓reduceIte] at h
      split at h <;> simp at h

mutual
/-- The bottom-up insertion into a subtree visits at most `height` nodes. -/
theorem time_insertOrSplitM_le (tr : BTree α β) :
    (insertOrSplitM t leT (tick 1) k v tr).time ≤ tr.height := by
  match tr with
  | .leaf => simp
  | .node first rest =>
    have h₁ := time_insertOrSplitM_le first
    have h₂ := time_insertRestM_le rest
    have h₃ := time_insertRestM_eq_zero_of_ret_eq_none (t := t) (k := k) (v := v) (rest := rest)
    have e : first.height + 1 ≤ (node first rest).height := height_first_succ_le
    rw [height_node] at e ⊢
    simp only [insertOrSplitM_node, TimeM.time_bind, TimeM.time_tick]
    split <;> simp_all <;> omega
termination_by sizeOf tr

/-- The insertion among the triples of a node visits at most as many nodes as the height of
the tallest of their children, `heightRest rest - 1`. -/
theorem time_insertRestM_le (rest : List (α × β × BTree α β)) :
    (insertRestM t leT (tick 1) k v rest).time ≤ heightRest rest - 1 := by
  match rest with
  | [] => simp
  | (k', v', c) :: rest =>
    have h₁ := time_insertOrSplitM_le c
    have h₂ := time_insertRestM_le rest
    have h₃ := time_insertRestM_eq_zero_of_ret_eq_none (t := t) (k := k) (v := v) (rest := rest)
    rw [heightRest_cons]
    by_cases hk : k ≤ k'
    · by_cases hk' : k' ≤ k <;> simp [insertRestM_cons, hk, hk']
    · simp only [insertRestM_cons, hk, leT, decide_false, pure_bind, Bool.false_eq_true,
        ↓reduceIte, TimeM.time_bind]
      split <;> simp_all <;> omega
termination_by sizeOf rest
end

/-- Insertion visits at most `height` nodes. -/
theorem time_insertT : (insertT t k v tr).time ≤ tr.height := by
  rw [time_insertT_eq]
  exact time_insertOrSplitM_le tr

/-- Insertion into a well-formed tree visits logarithmically many nodes. -/
theorem time_insertT_le_log (h : IsWF t tr) :
    (insertT t k v tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  time_insertT.trans h.height_le_log

/-! ### Examples -/

/-- A two-level tree at `t = 2`: inserting `4` visits the root and its last child, whatever
splitting follows. -/
example :
    (insertT 2 4 4 (BTree.node (.node .leaf [(1, 1, .leaf)])
      [(2, 2, .node .leaf [(3, 3, .leaf)])] : BTree ℕ ℕ)).time = 2 := by
  simp [insertT, insertM, insertOrSplitM_node, insertRestM_cons]

end NodeVisits

end EpsilonEridani.BTree
