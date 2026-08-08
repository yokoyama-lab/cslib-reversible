/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Instances.Restrict

/-!
# Grounded states: where well-foundedness comes from

`WellFoundedBwd` — no infinite backward computation — is not a property of a
language with unbounded iteration.  A loop whose body leaves the store alone
cycles, and undoing goes round the cycle forever.  `Instances.RCore` exhibits
such a cycle for R-CORE.

But the axiom is not needed of the whole state space.  It is needed of the
configurations a program actually reaches, and those are grounded: they were
arrived at from a start in finitely many steps, so undoing them terminates.

This file makes that precise without adding an assumption.  A state is
`Grounded` when it is accessible for the step-back relation — exactly the
statement that undoing it terminates, one state at a time instead of all at
once.  Grounded states are closed under stepping back always, and under
stepping forward as soon as the system is backward deterministic, because then
the state stepped into has only the one predecessor.  Restricting to them
therefore *proves* `WellFoundedBwd` rather than assuming it.

The upshot: a language with iteration inherits causal consistency on the part
of its state space that its programs can reach, which is the part its
semantics is about.

## Main definitions

- `Grounded`: the step-back relation is accessible at this state.

## Main statements

- `grounded_of_origin`: a state with nothing to undo is grounded.
- `Grounded.fwd`: under backward determinism, stepping forward stays grounded.
- `wellFoundedBwd_grounded`: the grounded restriction is well-founded — proved,
  not assumed.
- `causal_consistency_grounded`: causal consistency for a language that has
  only relative backward determinism and no global well-foundedness.
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v}

/-! ## Grounded states -/

/--
Undoing this state terminates.

`WellFoundedBwd` says every state is grounded; a language with unbounded
iteration will not have that, but the states its programs reach are grounded
all the same.
-/
def Grounded (lts : LTS State Label) (p : State) : Prop :=
  Acc (fun q p => BStep lts p q) p

/-- A state with nothing left to undo is grounded. -/
theorem grounded_of_origin {lts : LTS State Label} {p : State} (h : Origin lts p) :
    Grounded lts p :=
  Acc.intro p fun _ hq => absurd hq (h _)

/-- Stepping back stays grounded: this is what accessibility says. -/
theorem Grounded.bwd {lts : LTS State Label} {p q : State}
    (h : Grounded lts p) (hs : BStep lts p q) : Grounded lts q :=
  h.inv hs

/--
Stepping forward stays grounded, when the system is backward deterministic
where it matters.

The state stepped into has exactly one way back — to the state stepped from —
so its accessibility follows from that state's.
-/
theorem Grounded.fwd {lts : LTS State Label} {P : State → Prop}
    (hd : BwdDeterministicOn lts P) {p q : State} {a : Label}
    (hq : P q) (hstep : lts.Tr p a q) (h : Grounded lts p) : Grounded lts q := by
  refine Acc.intro q fun r hr => ?_
  obtain ⟨b, hb⟩ := bstep_iff.mp hr
  obtain ⟨_, rfl⟩ := hd hq hb hstep
  exact h

/-! ## The grounded restriction -/

/-- The states of `P` that are grounded. -/
def GroundedOn (lts : LTS State Label) (P : State → Prop) (p : State) : Prop :=
  P p ∧ Grounded lts p

/-- Grounded well-formed states are closed under stepping, in both directions. -/
theorem stepClosed_groundedOn {lts : LTS State Label} {P : State → Prop}
    (hcl : StepClosed lts P) (hd : BwdDeterministicOn lts P) :
    StepClosed lts (GroundedOn lts P) where
  fwd hstep hp := ⟨hcl.fwd hstep hp.1, hp.2.fwd hd (hcl.fwd hstep hp.1) hstep⟩
  bwd hstep hq := ⟨hcl.bwd hstep hq.1, hq.2.bwd (bstep_iff.mpr ⟨_, hstep⟩)⟩

/-- Backward determinism survives the further restriction. -/
theorem bwdDeterministicOn_groundedOn {lts : LTS State Label} {P : State → Prop}
    (hd : BwdDeterministicOn lts P) : BwdDeterministicOn lts (GroundedOn lts P) :=
  fun hp h₁ h₂ => hd hp.1 h₁ h₂

/--
**Well-foundedness on the grounded part is a theorem, not an assumption.**

Every state of the restriction carries its own accessibility, and that is
transported to the restricted step-back relation.
-/
theorem wellFoundedBwd_grounded {lts : LTS State Label} {P : State → Prop} :
    WellFoundedBwd (lts.restrict (GroundedOn lts P)) where
  wf := by
    have key : ∀ {a : State}, Acc (fun q p => BStep lts p q) a →
        ∀ p : {s // GroundedOn lts P s}, p.1 = a →
          Acc (fun q p : {s // GroundedOn lts P s} => BStep (lts.restrict _) p q) p := by
      intro a ha
      induction ha with
      | intro b _ ih =>
        intro p hp
        refine Acc.intro p fun q hq => ?_
        exact ih q.1 (by rw [← hp]; exact bstep_restrict.mp hq) q rfl
    exact ⟨fun p => key p.2.2 p rfl⟩

/-! ## What a language with iteration gets -/

section Inherited

variable {lts : LTS State Label} {P : State → Prop}
variable [DecidableEq State] [DecidableEq Label] [BStepDec lts]

/--
**Causal consistency for a language whose backward computation need not
terminate everywhere.**

The language supplies its determinism theorem and the closure of its
well-formedness; well-foundedness is not among the obligations, because the
restriction to grounded states discharges it.
-/
theorem causal_consistency_grounded (hd : BwdDeterministicOn lts P) (hcl : StepClosed lts P)
    {p q : {s // GroundedOn lts P s}}
    {l₁ l₂ : List (Transition {s // GroundedOn lts P s} Label)}
    (h₁ : Chained (lts.restrict (GroundedOn lts P)) p l₁ q)
    (h₂ : Chained (lts.restrict (GroundedOn lts P)) p l₂ q) :
    CEq (lts.restrict (GroundedOn lts P)) NoIndep p q l₁ l₂ :=
  have := bwdDeterministic_restrict (bwdDeterministicOn_groundedOn hd)
  have := wellFoundedBwd_grounded (lts := lts) (P := P)
  have := bStepDec_restrict (stepClosed_groundedOn hcl hd)
  causal_consistency_of_bwdDeterministic h₁ h₂

/-- **However a grounded state is rewound, the origin reached is the same.** -/
theorem unique_origin_grounded (hd : BwdDeterministicOn lts P) (hcl : StepClosed lts P)
    {p o₁ o₂ : {s // GroundedOn lts P s}}
    (h₁ : Relation.ReflTransGen (BStep (lts.restrict (GroundedOn lts P))) p o₁)
    (ho₁ : Origin (lts.restrict (GroundedOn lts P)) o₁)
    (h₂ : Relation.ReflTransGen (BStep (lts.restrict (GroundedOn lts P))) p o₂)
    (ho₂ : Origin (lts.restrict (GroundedOn lts P)) o₂) : o₁ = o₂ :=
  have := bwdDeterministic_restrict (bwdDeterministicOn_groundedOn hd)
  have := wellFoundedBwd_grounded (lts := lts) (P := P)
  have := bStepDec_restrict (stepClosed_groundedOn hcl hd)
  unique_origin_of_bwdDeterministic h₁ ho₁ h₂ ho₂

end Inherited

end Cslib.LTS

