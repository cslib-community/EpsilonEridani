/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module

public import EpsilonEridani.Algorithms.Lean.BTree.Height
public import EpsilonEridani.Algorithms.Lean.BTree.MinMax
public import EpsilonEridani.Algorithms.Lean.BTree.PredSucc
public import EpsilonEridani.Algorithms.Lean.BTree.Rank
public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Nat.Defs

/-!
# Node-visit costs of B-tree point queries

The point queries of `EpsilonEridani.BTree` are defined once over a monad, with a comparator and
a node-visit action. This file instantiates them at `TimeM ℕ` with the free comparator `leT` and
`visit := tick 1`, so the time of a run is the number of nodes it visits: `lookupT`,
`containsT`, `minT`, `maxT`, `predT`, `succT` and `rankT`.

The transfer lemmas `Cslib.IsMonadHom.map_lookupM` and its siblings push a monad morphism through
each polymorphic definition, in the pattern of CSLib's `Cslib.IsMonadHom.map_listMergeSortM`.
Applied to `TimeM.isMonadHom_pure_ret`, they give `ret_lookupT` and its siblings: the value of
each instrumented query is the pure query.

Each query visits at most one node per level, so `time_lookupT` and its siblings bound the time
by `height` on every tree, well-formed or not, because `height` is the longest root-to-leaf path.
The `_le_log` corollaries compose these with `IsWF.height_le_log`.
-/

public section

open Cslib (IsMonadHom)
open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace EpsilonEridani.BTree

section Transfer

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

/-- A monad morphism commutes with the within-node search. -/
theorem _root_.Cslib.IsMonadHom.map_slotM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (k : α) (rest : List (α × β × BTree α β)) :
    f (slotM le k rest) = slotM (fun a b => f (le a b)) k rest := by
  induction rest with
  | nil => simp [slotM, hf.map_pure]
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    simp [slotM, hf.map_bind, hf.map_pure, apply_ite f, ih]

/-- A monad morphism commutes with lookup. -/
theorem _root_.Cslib.IsMonadHom.map_lookupM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (lookupM le visit k tr) = lookupM (fun a b => f (le a b)) (f visit) k tr := by
  fun_induction lookupM le visit k tr <;>
    simp [lookupM, hf.map_bind, hf.map_pure, apply_ite f, *]

/-- A monad morphism commutes with the membership test. -/
theorem _root_.Cslib.IsMonadHom.map_containsM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (containsM le visit k tr) = containsM (fun a b => f (le a b)) (f visit) k tr := by
  simp [containsM, hf.map_bind, hf.map_pure, hf.map_lookupM]

/-- A monad morphism commutes with the minimum search. -/
theorem _root_.Cslib.IsMonadHom.map_minM (hf : IsMonadHom m n f) (visit : m Unit)
    (tr : BTree α β) : f (minM visit tr) = minM (f visit) tr := by
  fun_induction minM visit tr with
  | case1 => simp [minM, hf.map_pure]
  | case2 first rest ih =>
    simp only [minM, hf.map_bind, ih]
    congr; funext; congr; funext o
    cases o <;> simp [hf.map_pure]

/-- A monad morphism commutes with the maximum search. -/
theorem _root_.Cslib.IsMonadHom.map_maxM (hf : IsMonadHom m n f) (visit : m Unit)
    (tr : BTree α β) : f (maxM visit tr) = maxM (f visit) tr := by
  match tr with
  | .leaf => simp [maxM_leaf, hf.map_pure]
  | .node first [] => simp [maxM_node_nil, hf.map_bind, hf.map_maxM visit first]
  | .node first [(k, v, c)] =>
    simp only [maxM_node_singleton, hf.map_bind, hf.map_maxM visit c]
    congr; funext; congr; funext o
    cases o <;> simp [hf.map_pure]
  | .node first ((k, v, c) :: e :: rest) =>
    simp [maxM_node_cons_cons, hf.map_maxM visit (.node c (e :: rest))]
termination_by sizeOf tr

/-- A monad morphism commutes with the predecessor search. -/
theorem _root_.Cslib.IsMonadHom.map_predM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (predM le visit k tr) = predM (fun a b => f (le a b)) (f visit) k tr := by
  match tr with
  | .leaf => simp [predM_leaf, hf.map_pure]
  | .node first [] => simp [predM_node_nil, hf.map_bind, hf.map_predM le visit k first]
  | .node first ((k', v, c) :: rest) =>
    simp [predM_node_cons, hf.map_bind, hf.map_pure, apply_ite f, hf.map_predM le visit k first,
      hf.map_predM le visit k (.node c rest)]
termination_by sizeOf tr

/-- A monad morphism commutes with the successor search. -/
theorem _root_.Cslib.IsMonadHom.map_succM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (succM le visit k tr) = succM (fun a b => f (le a b)) (f visit) k tr := by
  match tr with
  | .leaf => simp [succM_leaf, hf.map_pure]
  | .node first [] => simp [succM_node_nil, hf.map_bind, hf.map_succM le visit k first]
  | .node first ((k', v, c) :: rest) =>
    simp [succM_node_cons, hf.map_bind, hf.map_pure, apply_ite f, hf.map_succM le visit k first,
      hf.map_succM le visit k (.node c rest)]
termination_by sizeOf tr

/-- A monad morphism commutes with the rank search. -/
theorem _root_.Cslib.IsMonadHom.map_rankM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (rankM le visit k tr) = rankM (fun a b => f (le a b)) (f visit) k tr := by
  match tr with
  | .leaf => simp [rankM_leaf, hf.map_pure]
  | .node first [] => simp [rankM_node_nil, hf.map_bind, hf.map_rankM le visit k first]
  | .node first ((k', v, c) :: rest) =>
    simp [rankM_node_cons, hf.map_bind, hf.map_pure, apply_ite f, hf.map_rankM le visit k first,
      hf.map_rankM le visit k (.node c rest)]
termination_by sizeOf tr

end Transfer

section NodeVisits

variable {α β : Type} {tr : BTree α β}

/-- Least entry, charging one tick per node visited. -/
def minT (tr : BTree α β) : TimeM ℕ (Option (α × β)) := minM (tick 1) tr

/-- Greatest entry, charging one tick per node visited. -/
def maxT (tr : BTree α β) : TimeM ℕ (Option (α × β)) := maxM (tick 1) tr

/-- The value of `minT` is `min?`. -/
theorem ret_minT : (minT tr).ret = min? tr := by
  rw [min?_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_minM (tick 1) tr)

/-- The value of `maxT` is `max?`. -/
theorem ret_maxT : (maxT tr).ret = max? tr := by
  rw [max?_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_maxM (tick 1) tr)

/-- The minimum search visits at most `height` nodes. -/
theorem time_minT {tr : BTree α β} : (minT tr).time ≤ tr.height := by
  unfold minT
  match tr with
  | .leaf => simp [minM]
  | .node first rest =>
    have := time_minT (tr := first)
    simp only [minT] at this
    simp only [minM, TimeM.time_bind, TimeM.time_tick, height_node]
    split <;> simp <;> omega

/-- The maximum search visits at most `height` nodes. -/
theorem time_maxT {tr : BTree α β} : (maxT tr).time ≤ tr.height := by
  unfold maxT
  match tr with
  | .leaf => simp [maxM_leaf]
  | .node first [] =>
    have := time_maxT (tr := first)
    simp only [maxT] at this
    simp [maxM_node_nil]
    omega
  | .node first [(k, v, c)] =>
    have := time_maxT (tr := c)
    simp only [maxT] at this
    simp only [maxM_node_singleton, TimeM.time_bind, TimeM.time_tick, height_node,
      heightRest_cons, heightRest_nil]
    split <;> simp <;> omega
  | .node first ((k, v, c) :: e :: rest) =>
    have := time_maxT (tr := .node c (e :: rest))
    simp only [maxT, height_node] at this
    simp only [maxM_node_cons_cons, height_node, heightRest_cons] at this ⊢
    omega
termination_by sizeOf tr

variable [LinearOrder α] {t : ℕ}

/-- The decidable comparator of a linear order, in `TimeM ℕ`: comparisons are free. -/
abbrev leT (a b : α) : TimeM ℕ Bool := pure (decide (a ≤ b))

/-- Lookup charging one tick per node visited. -/
def lookupT (k : α) (tr : BTree α β) : TimeM ℕ (Option β) := lookupM leT (tick 1) k tr

/-- Membership test charging one tick per node visited. -/
def containsT (k : α) (tr : BTree α β) : TimeM ℕ Bool := containsM leT (tick 1) k tr

/-- Strict predecessor, charging one tick per node visited. -/
def predT (k : α) (tr : BTree α β) : TimeM ℕ (Option (α × β)) := predM leT (tick 1) k tr

/-- Strict successor, charging one tick per node visited. -/
def succT (k : α) (tr : BTree α β) : TimeM ℕ (Option (α × β)) := succM leT (tick 1) k tr

/-- Rank, charging one tick per node visited. -/
def rankT (k : α) (tr : BTree α β) : TimeM ℕ ℕ := rankM leT (tick 1) k tr

/-- The value of `lookupT` is `lookup`. -/
theorem ret_lookupT (k : α) : (lookupT k tr).ret = lookup k tr := by
  rw [lookup_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_lookupM leT (tick 1) k tr)

/-- The value of `containsT` is `contains`. -/
theorem ret_containsT (k : α) : (containsT k tr).ret = contains k tr := by
  rw [contains_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_containsM leT (tick 1) k tr)

/-- The value of `predT` is `pred?`. -/
theorem ret_predT (k : α) : (predT k tr).ret = pred? k tr := by
  rw [pred?_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_predM leT (tick 1) k tr)

/-- The value of `succT` is `succ?`. -/
theorem ret_succT (k : α) : (succT k tr).ret = succ? k tr := by
  rw [succ?_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_succM leT (tick 1) k tr)

/-- The value of `rankT` is `rank`. -/
theorem ret_rankT (k : α) : (rankT k tr).ret = rank k tr := by
  rw [rank_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_rankM leT (tick 1) k tr)

/-! ### Node-visit bounds -/

/-- Lookup visits at most `height` nodes. -/
theorem time_lookupT {tr : BTree α β} (k : α) : (lookupT k tr).time ≤ tr.height := by
  unfold lookupT
  match tr with
  | .leaf => simp [lookupM]
  | .node first [] =>
    have := time_lookupT (tr := first) k
    simp only [lookupT] at this
    simp [lookupM]
    omega
  | .node first ((k', v, c) :: rest) =>
    have h₁ := time_lookupT (tr := first) k
    have h₂ := time_lookupT (tr := .node c rest) k
    simp only [lookupT, height_node] at h₁ h₂
    simp only [lookupM, height_node, heightRest_cons]
    by_cases hk : k ≤ k' <;> by_cases hk' : k' ≤ k <;>
      simp [hk, hk', -heightRest_eq_foldr] <;> omega
termination_by sizeOf tr

/-- The membership test visits at most `height` nodes. -/
theorem time_containsT (k : α) : (containsT k tr).time ≤ tr.height := by
  simpa [containsT, containsM, lookupT] using time_lookupT (tr := tr) k

/-- The predecessor search visits at most `height` nodes. -/
theorem time_predT {tr : BTree α β} (k : α) : (predT k tr).time ≤ tr.height := by
  unfold predT
  match tr with
  | .leaf => simp [predM_leaf]
  | .node first [] =>
    have := time_predT (tr := first) k
    simp only [predT] at this
    simp [predM_node_nil]
    omega
  | .node first ((k', v, c) :: rest) =>
    have h₁ := time_predT (tr := first) k
    have h₂ := time_predT (tr := .node c rest) k
    simp only [predT, height_node] at h₁ h₂
    simp only [predM_node_cons, height_node, heightRest_cons]
    by_cases hk : k ≤ k' <;> simp [hk, -heightRest_eq_foldr] <;> omega
termination_by sizeOf tr

/-- The successor search visits at most `height` nodes. -/
theorem time_succT {tr : BTree α β} (k : α) : (succT k tr).time ≤ tr.height := by
  unfold succT
  match tr with
  | .leaf => simp [succM_leaf]
  | .node first [] =>
    have := time_succT (tr := first) k
    simp only [succT] at this
    simp [succM_node_nil]
    omega
  | .node first ((k', v, c) :: rest) =>
    have h₁ := time_succT (tr := first) k
    have h₂ := time_succT (tr := .node c rest) k
    simp only [succT, height_node] at h₁ h₂
    simp only [succM_node_cons, height_node, heightRest_cons]
    by_cases hk : k' ≤ k <;> simp [hk, -heightRest_eq_foldr] <;> omega
termination_by sizeOf tr

/-- The rank search visits at most `height` nodes. -/
theorem time_rankT {tr : BTree α β} (k : α) : (rankT k tr).time ≤ tr.height := by
  unfold rankT
  match tr with
  | .leaf => simp [rankM_leaf]
  | .node first [] =>
    have := time_rankT (tr := first) k
    simp only [rankT] at this
    simp [rankM_node_nil]
    omega
  | .node first ((k', v, c) :: rest) =>
    have h₁ := time_rankT (tr := first) k
    have h₂ := time_rankT (tr := .node c rest) k
    simp only [rankT, height_node] at h₁ h₂
    simp only [rankM_node_cons, height_node, heightRest_cons]
    by_cases hk : k ≤ k' <;> simp [hk, -heightRest_eq_foldr] <;> omega
termination_by sizeOf tr

/-- Lookup in a well-formed tree visits logarithmically many nodes. -/
theorem time_lookupT_le_log (h : IsWF t tr) (k : α) :
    (lookupT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_lookupT k).trans h.height_le_log

/-- The membership test in a well-formed tree visits logarithmically many nodes. -/
theorem time_containsT_le_log (h : IsWF t tr) (k : α) :
    (containsT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_containsT k).trans h.height_le_log

/-- The predecessor search in a well-formed tree visits logarithmically many nodes. -/
theorem time_predT_le_log (h : IsWF t tr) (k : α) :
    (predT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_predT k).trans h.height_le_log

/-- The successor search in a well-formed tree visits logarithmically many nodes. -/
theorem time_succT_le_log (h : IsWF t tr) (k : α) :
    (succT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_succT k).trans h.height_le_log

/-- The rank search in a well-formed tree visits logarithmically many nodes. -/
theorem time_rankT_le_log (h : IsWF t tr) (k : α) :
    (rankT k tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  (time_rankT k).trans h.height_le_log

/-- The minimum search in a well-formed tree visits logarithmically many nodes. -/
theorem time_minT_le_log (h : IsWF t tr) :
    (minT tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  time_minT.trans h.height_le_log

/-- The maximum search in a well-formed tree visits logarithmically many nodes. -/
theorem time_maxT_le_log (h : IsWF t tr) :
    (maxT tr).time ≤ Nat.log t ((tr.size + 1) / 2) + 1 :=
  time_maxT.trans h.height_le_log

/-! ### Examples -/

/-- The empty tree is not visited. -/
example (k : ℕ) : (lookupT k (.leaf : BTree ℕ ℕ)).time = 0 := by
  simp [lookupT, lookupM]

/-- A node without keys is visited once before descending into its only child. -/
example (k : ℕ) : (rankT k (.node .leaf [] : BTree ℕ ℕ)).time = 1 := by
  simp [rankT, rankM_node_nil, rankM_leaf]

/-- A two-level tree at `t = 2`: lookup of `3` visits the root and one child. -/
example :
    (lookupT 3 (BTree.node (.node .leaf [(1, 1, .leaf)])
      [(2, 2, .node .leaf [(3, 3, .leaf)])] : BTree ℕ ℕ)).time = 2 := by
  simp [lookupT, lookupM]

end NodeVisits

end EpsilonEridani.BTree
