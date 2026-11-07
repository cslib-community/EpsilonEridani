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
-/

public section

open Cslib (IsMonadHom)
open Cslib.Algorithms.Lean (TimeM)
open Cslib.Algorithms.Lean.TimeM (tick)

namespace EpsilonEridani.BTree

section Transfer

variable {α β : Type} {m n : Type → Type*} [Monad m] [Monad n]
  {f : {γ : Type} → m γ → n γ}

theorem _root_.Cslib.IsMonadHom.map_slotM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (k : α) (rest : List (α × β × BTree α β)) :
    f (slotM le k rest) = slotM (fun a b => f (le a b)) k rest := by
  induction rest with
  | nil => simp [slotM, hf.map_pure]
  | cons e rest ih =>
    obtain ⟨k', v, c⟩ := e
    simp [slotM, hf.map_bind, hf.map_pure, apply_ite f, ih]

theorem _root_.Cslib.IsMonadHom.map_lookupM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (lookupM le visit k tr) = lookupM (fun a b => f (le a b)) (f visit) k tr := by
  fun_induction lookupM le visit k tr <;>
    simp [lookupM, hf.map_bind, hf.map_pure, apply_ite f, *]

theorem _root_.Cslib.IsMonadHom.map_containsM (hf : IsMonadHom m n f) (le : α → α → m Bool)
    (visit : m Unit) (k : α) (tr : BTree α β) :
    f (containsM le visit k tr) = containsM (fun a b => f (le a b)) (f visit) k tr := by
  simp [containsM, hf.map_bind, hf.map_pure, hf.map_lookupM]

theorem _root_.Cslib.IsMonadHom.map_minM (hf : IsMonadHom m n f) (visit : m Unit)
    (tr : BTree α β) : f (minM visit tr) = minM (f visit) tr := by
  fun_induction minM visit tr with
  | case1 => simp [minM, hf.map_pure]
  | case2 first rest ih =>
    simp only [minM, hf.map_bind, ih]
    congr; funext; congr; funext o
    cases o <;> simp [hf.map_pure]

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

theorem ret_minT : (minT tr).ret = min? tr := by
  rw [min?_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_minM (tick 1) tr)

theorem ret_maxT : (maxT tr).ret = max? tr := by
  rw [max?_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_maxM (tick 1) tr)

variable [LinearOrder α]

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

theorem ret_lookupT (k : α) : (lookupT k tr).ret = lookup k tr := by
  rw [lookup_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_lookupM leT (tick 1) k tr)

theorem ret_containsT (k : α) : (containsT k tr).ret = contains k tr := by
  rw [contains_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_containsM leT (tick 1) k tr)

theorem ret_predT (k : α) : (predT k tr).ret = pred? k tr := by
  rw [pred?_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_predM leT (tick 1) k tr)

theorem ret_succT (k : α) : (succT k tr).ret = succ? k tr := by
  rw [succ?_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_succM leT (tick 1) k tr)

theorem ret_rankT (k : α) : (rankT k tr).ret = rank k tr := by
  rw [rank_def]
  exact Id.ext_iff.1 (TimeM.isMonadHom_pure_ret.map_rankM leT (tick 1) k tr)

end NodeVisits

end EpsilonEridani.BTree
