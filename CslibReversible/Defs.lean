/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import Cslib.Foundations.Semantics.LTS.Basic

/-!
# Reversible reading of a labelled transition system

An `LTS` records only forward transitions.  To speak about reversibility we
need to name *transitions themselves* — a step together with the direction in
which it is taken — because causal equivalence permutes and cancels
transitions, not states.

This file introduces that datum (`Transition`), what it means for one to be
`Valid` in a given `LTS`, and its reversal.  The Loop Lemma holds *by
construction* here: a backward transition simply is the converse of a forward
one.  This is the same status the Loop Lemma has in Lanese–Phillips–Ulidowski,
who assume it of the LTS.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Theory for Reversible
  Computation*, ACM TOCL 25(2), 2024][LPU2024]
-/

universe u v

namespace Cslib.LTS

/-- The direction in which a transition of an `LTS` is taken. -/
inductive Dir where
  /-- Along the transition relation. -/
  | fwd : Dir
  /-- Against the transition relation. -/
  | bwd : Dir
  deriving DecidableEq, Repr, Inhabited

/-- Reversing a direction. -/
def Dir.rev : Dir → Dir
  | .fwd => .bwd
  | .bwd => .fwd

@[simp] theorem Dir.rev_rev (d : Dir) : d.rev.rev = d := by cases d <;> rfl

/--
A transition datum: a source, a label, a direction, and a target.

Separating the datum from its validity (`Transition.Valid`) is what lets
transitions be compared for equality, which the axiom BTI needs.
-/
@[ext]
structure Transition (State : Type u) (Label : Type v) where
  /-- Where the transition starts. -/
  src : State
  /-- The label of the underlying step. -/
  lbl : Label
  /-- Whether the step is taken forwards or backwards. -/
  dir : Dir
  /-- Where the transition ends. -/
  tgt : State
  deriving Repr

variable {State : Type u} {Label : Type v}

instance [DecidableEq State] [DecidableEq Label] :
    DecidableEq (Transition State Label) := by
  intro t u
  cases t; cases u
  simp only [Transition.mk.injEq]
  infer_instance

/-- A transition datum is valid when the underlying step really is in the `LTS`. -/
def Transition.Valid (lts : LTS State Label) (t : Transition State Label) : Prop :=
  match t.dir with
  | .fwd => lts.Tr t.src t.lbl t.tgt
  | .bwd => lts.Tr t.tgt t.lbl t.src

/-- The reversal of a transition. -/
def Transition.rev (t : Transition State Label) : Transition State Label :=
  ⟨t.tgt, t.lbl, t.dir.rev, t.src⟩

@[simp] theorem Transition.rev_src (t : Transition State Label) : t.rev.src = t.tgt := rfl
@[simp] theorem Transition.rev_tgt (t : Transition State Label) : t.rev.tgt = t.src := rfl
@[simp] theorem Transition.rev_lbl (t : Transition State Label) : t.rev.lbl = t.lbl := rfl
@[simp] theorem Transition.rev_dir (t : Transition State Label) : t.rev.dir = t.dir.rev := rfl

@[simp] theorem Transition.rev_rev (t : Transition State Label) : t.rev.rev = t := by
  cases t; simp [Transition.rev]

/--
**Loop Lemma.**  Every transition can be undone.

Here this is definitional rather than an axiom, because backward transitions
*are* the converses of forward ones.
-/
theorem Transition.rev_valid {lts : LTS State Label} {t : Transition State Label}
    (h : t.Valid lts) : t.rev.Valid lts := by
  cases ht : t.dir <;> simp only [Transition.Valid, Transition.rev, Dir.rev, ht] at h ⊢ <;> exact h

/-- Two transitions are coinitial when they leave the same state. -/
def Transition.Coinitial (t u : Transition State Label) : Prop := t.src = u.src

/-- A transition taken forwards. -/
def Transition.IsFwd (t : Transition State Label) : Prop := t.dir = .fwd

/-- A transition taken backwards. -/
def Transition.IsBwd (t : Transition State Label) : Prop := t.dir = .bwd

end Cslib.LTS
