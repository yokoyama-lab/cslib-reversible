/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.Instances.Deterministic

/-!
# Restricting an LTS to well-formed states

`Instances.Deterministic` asks a language for backward determinism at *every*
state of its transition system.  Real reversible languages do not have that,
and are not expected to: their determinism theorems carry a well-formedness
side condition, and the semantics is stuck or ill-behaved outside it.

The concrete case this file was written for is R-CORE.  Its Rocq development
(`yokoyama-lab/rcore-semantics`, the artifact of Makino–Yokoyama, RC 2026)
proves

```
Theorem ss_bwd_deterministic_tgt :
  forall cfg1 cfg2 cfg,
    wf_cc (fst cfg) -> exec_ss cfg1 cfg -> exec_ss cfg2 cfg -> cfg1 = cfg2.
```

— backward determinism **given well-formedness of the target**, which is
exactly the state the two backward transitions leave from.  The same
development also proves that well-formedness is closed in both directions,

```
Lemma wf_cc_step_preserved : exec_ss (cc, s) (cc', s') -> wf_cc cc -> wf_cc cc'.
Lemma wf_cc_step_reflected : exec_ss (cc, s) (cc', s') -> wf_cc cc' -> wf_cc cc.
```

so the well-formed states carry a sub-LTS.  That is the construction below.

The point is that a language need not be re-mechanised to become an instance:
it has to exhibit the predicate its determinism theorem is relative to, show
the predicate is closed under steps, and it inherits the theory on that
sub-system.  R-WHILE, Janus and the reversible C compiler all state their
determinism the same way.

## Main definitions

- `restrict`: the sub-LTS carried by a predicate on states.
- `BwdDeterministicOn`: backward determinism relative to a predicate.

## Main statements

- `bwdDeterministic_restrict`: a relatively backward-deterministic system is
  backward-deterministic on its restriction, hence an instance of the whole
  axiom layer.
- `wellFoundedBwd_restrict`, `bStepDec_restrict`: the remaining two classes
  transfer from the unrestricted system.
- `causal_consistency_restrict`, `unique_origin_restrict`: what a language gets
  for exhibiting the predicate.
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v}

/-! ## The sub-LTS -/

/-- Undoing a step is exactly having a step in. -/
theorem bstep_iff {lts : LTS State Label} {p q : State} :
    BStep lts p q ↔ ∃ a, lts.Tr q a p := by
  constructor
  · rintro ⟨t, hv, hb, rfl, rfl⟩
    rw [Transition.Valid, hb] at hv
    exact ⟨t.lbl, hv⟩
  · rintro ⟨a, ha⟩
    exact ⟨Transition.mk p a .bwd q, ha, rfl, rfl, rfl⟩

/--
The sub-LTS carried by `P`.

Only the states are restricted; a transition of the restriction is a
transition of the original between two states that satisfy `P`.  For this to
be the right notion, `P` should be closed under transitions in both
directions — `StepClosed` below — and then the restriction has exactly the
transitions of the original that touch `P` at all.
-/
def restrict (lts : LTS State Label) (P : State → Prop) : LTS {s // P s} Label :=
  ⟨fun p a q => lts.Tr p.1 a q.1⟩

@[simp] theorem restrict_Tr {lts : LTS State Label} {P : State → Prop}
    {p q : {s // P s}} {a : Label} :
    (lts.restrict P).Tr p a q ↔ lts.Tr p.1 a q.1 := Iff.rfl

@[simp] theorem bstep_restrict {lts : LTS State Label} {P : State → Prop}
    {p q : {s // P s}} : BStep (lts.restrict P) p q ↔ BStep lts p.1 q.1 := by
  simp only [bstep_iff, restrict_Tr]

/-- `P` is closed under transitions in both directions. -/
structure StepClosed (lts : LTS State Label) (P : State → Prop) : Prop where
  /-- A step out of a state satisfying `P` stays in `P`. -/
  fwd : ∀ {p q : State} {a : Label}, lts.Tr p a q → P p → P q
  /-- A step into a state satisfying `P` comes from `P`. -/
  bwd : ∀ {p q : State} {a : Label}, lts.Tr p a q → P q → P p

/-! ## Backward determinism, relative to a predicate -/

/--
Backward determinism at the states satisfying `P`.

This is the shape the determinism theorems of real reversible languages take:
the side condition sits on the state the two backward transitions leave from,
not on the whole state space.
-/
def BwdDeterministicOn (lts : LTS State Label) (P : State → Prop) : Prop :=
  ∀ {p q₁ q₂ : State} {a b : Label}, P p → lts.Tr q₁ a p → lts.Tr q₂ b p → a = b ∧ q₁ = q₂

/--
A relatively backward-deterministic system is backward-deterministic on its
restriction.

With this, `Instances.Deterministic` applies: the empty independence relation
discharges the Square Property, `CLG` and symmetry outright, and this supplies
`BTI`.
-/
theorem bwdDeterministic_restrict {lts : LTS State Label} {P : State → Prop}
    (h : BwdDeterministicOn lts P) : BwdDeterministic (lts.restrict P) where
  bwd_unique {t u} htv htb huv hub hco := by
    rw [Transition.Valid, htb] at htv
    rw [Transition.Valid, hub] at huv
    rw [Transition.Coinitial] at hco
    rw [← hco] at huv
    obtain ⟨hlbl, hsrc⟩ := h t.src.2 htv huv
    exact Transition.ext hco hlbl (htb.trans hub.symm) (Subtype.ext hsrc)

/-! ## The remaining classes transfer -/

/-- Undoing terminates on the restriction if it terminates at all. -/
theorem wellFoundedBwd_restrict {lts : LTS State Label} {P : State → Prop}
    [WellFoundedBwd lts] : WellFoundedBwd (lts.restrict P) where
  wf := by
    refine Subrelation.wf (r := InvImage (fun q p => BStep lts p q) Subtype.val) ?_
      (InvImage.wf _ (WellFoundedBwd.wf (lts := lts)))
    intro q p h
    exact bstep_restrict.mp h

/--
A computable step-back on the restriction.

The predecessor produced by the unrestricted stepper lands in `P` because `P`
is closed backwards, so nothing has to be searched for twice.
-/
@[instance_reducible] def bStepDec_restrict {lts : LTS State Label} {P : State → Prop}
    (hcl : StepClosed lts P) [BStepDec lts] : BStepDec (lts.restrict P) where
  step p :=
    match BStepDec.step (lts := lts) p.1 with
    | .inl ⟨q, hq⟩ =>
      have hP : P q := by
        obtain ⟨a, ha⟩ := bstep_iff.mp hq
        exact hcl.bwd ha p.2
      .inl ⟨⟨q, hP⟩, bstep_restrict.mpr hq⟩
    | .inr hno => .inr fun q hq => hno q.1 (bstep_restrict.mp hq)

/-! ## What a language gets for exhibiting the predicate -/

section Inherited

variable {lts : LTS State Label} {P : State → Prop}
variable [DecidableEq State] [DecidableEq Label] [WellFoundedBwd lts] [BStepDec lts]

/--
**Causal consistency on the well-formed part of a language.**

Everything the language has to supply is `BwdDeterministicOn` and
`StepClosed` — that is, the determinism theorem it already proved and the fact
that its well-formedness is preserved and reflected by steps.
-/
theorem causal_consistency_restrict (hd : BwdDeterministicOn lts P) (hcl : StepClosed lts P)
    {p q : {s // P s}} {l₁ l₂ : List (Transition {s // P s} Label)}
    (h₁ : Chained (lts.restrict P) p l₁ q) (h₂ : Chained (lts.restrict P) p l₂ q) :
    CEq (lts.restrict P) NoIndep p q l₁ l₂ :=
  have := bwdDeterministic_restrict hd
  have := wellFoundedBwd_restrict (lts := lts) (P := P)
  have := bStepDec_restrict hcl
  causal_consistency_of_bwdDeterministic h₁ h₂

/-- **However a well-formed state is rewound, the origin reached is the same.** -/
theorem unique_origin_restrict (hd : BwdDeterministicOn lts P) (hcl : StepClosed lts P)
    {p o₁ o₂ : {s // P s}}
    (h₁ : Relation.ReflTransGen (BStep (lts.restrict P)) p o₁)
    (ho₁ : Origin (lts.restrict P) o₁)
    (h₂ : Relation.ReflTransGen (BStep (lts.restrict P)) p o₂)
    (ho₂ : Origin (lts.restrict P) o₂) : o₁ = o₂ :=
  have := bwdDeterministic_restrict hd
  have := wellFoundedBwd_restrict (lts := lts) (P := P)
  have := bStepDec_restrict hcl
  unique_origin_of_bwdDeterministic h₁ ho₁ h₂ ho₂

end Inherited

end Cslib.LTS

