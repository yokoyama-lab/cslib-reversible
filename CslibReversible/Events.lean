/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.CausalConsistency

/-!
# Events

Causal safety and causal liveness — "a transition can be undone if and only if
each of its consequences has been undone" — cannot be stated with transitions
alone.  Permuting a path replaces a transition by a *different* transition
with the same label: the two are different occurrences of the same **event**.
This file builds that notion.

## Main definitions

- `CPI` (Coinitial Propagation of Independence): independence propagates
  around a commuting diamond.  With `SquareProperty`, `BTI` and
  `WellFoundedBwd` it makes an LTSI *pre-reversible*, which is the setting in
  which events behave.
- `Diamond`: the four-transition square that the event relation is generated
  from.
- `SameEvent`: the smallest equivalence relation identifying opposite corners
  of a diamond whose coinitial pair is independent.
- `IRE` (Independence Respects Events): independence only depends on the
  event.  This is the extra axiom that causal safety and liveness need on top
  of pre-reversibility.

## Main statements

- `Diamond.swap`: the square is symmetric in its two edges.
- `SameEvent.dir_eq`, `SameEvent.lbl_eq`: an event has a well-defined
  direction and label.
- `Diamond.ofSquare`: the Square Property produces a diamond.
- `Diamond.cEq`: the two ways round a diamond are causally equivalent — the
  bridge between `Diamond` and the `CEq.swap` rule.
- `SameEvent.of_square`: delaying a transition past an independent one
  replaces it by a *different transition of the same event*.  This is the fact
  that makes events, rather than transitions, the right thing to count.

## Not yet formalised

Independence of Diamonds (Proposition 4.7 of [LPU2020]: `BTI` and `CPI` imply
that every commuting diamond has independent coinitial edges) carries a
non-degeneracy side condition — the four corners must be distinct, in a sense
that depends on the directions of the two edges — which is not yet worked out
here.  It is not needed for the definitions below.

## References

* [I. Lanese, I. Phillips, I. Ulidowski, *An Axiomatic Approach to Reversible
  Computation*, FoSSaCS 2020, Definitions 4.2, 4.5, 4.6, 4.12][LPU2020]
-/

universe u v

namespace Cslib.LTS

variable {State : Type u} {Label : Type v} {lts : LTS State Label}
variable {Indep : Transition State Label → Transition State Label → Prop}

/--
`Diamond lts t u u' t'` is the commuting square

```
      t          u'
  P ─────→ Q ─────→ S
  │                 ↑
  │ u            t' │
  ↓                 │
  R ────────────────┘
```

with `u'` a copy of the action of `u` and `t'` a copy of the action of `t`.
-/
structure Diamond (lts : LTS State Label) (t u u' t' : Transition State Label) : Prop where
  /-- All four transitions are transitions of `lts`. -/
  validT : t.Valid lts
  /-- The coinitial partner is a transition of `lts`. -/
  validU : u.Valid lts
  /-- The residual of `u` after `t` is a transition of `lts`. -/
  validU' : u'.Valid lts
  /-- The residual of `t` after `u` is a transition of `lts`. -/
  validT' : t'.Valid lts
  /-- `t` and `u` leave the same state. -/
  coinitial : u.src = t.src
  /-- `u'` continues where `t` arrives. -/
  srcU' : u'.src = t.tgt
  /-- `t'` continues where `u` arrives. -/
  srcT' : t'.src = u.tgt
  /-- The two ways round meet. -/
  cofinal : u'.tgt = t'.tgt
  /-- `u'` performs the action of `u`. -/
  lblU' : u'.lbl = u.lbl
  /-- ... in the same direction. -/
  dirU' : u'.dir = u.dir
  /-- `t'` performs the action of `t`. -/
  lblT' : t'.lbl = t.lbl
  /-- ... in the same direction. -/
  dirT' : t'.dir = t.dir

/-- Rotating a diamond a quarter turn: the square is symmetric in its two edges. -/
theorem Diamond.swap {t u u' t' : Transition State Label} (d : Diamond lts t u u' t') :
    Diamond lts u t t' u' where
  validT := d.validU
  validU := d.validT
  validU' := d.validT'
  validT' := d.validU'
  coinitial := d.coinitial.symm
  srcU' := d.srcT'
  srcT' := d.srcU'
  cofinal := d.cofinal.symm
  lblU' := d.lblT'
  dirU' := d.dirT'
  lblT' := d.lblU'
  dirT' := d.dirU'

/-- Going round a diamond the short way is a path. -/
theorem Diamond.chainedLeft {t u u' t' : Transition State Label}
    (d : Diamond lts t u u' t') {p : State} (hp : t.src = p) :
    Chained lts p [t, u'] u'.tgt :=
  ⟨hp, d.validT, d.srcU', d.validU', rfl⟩

/-- Going round it the long way is a path with the same endpoints. -/
theorem Diamond.chainedRight {t u u' t' : Transition State Label}
    (d : Diamond lts t u u' t') {p : State} (hp : t.src = p) :
    Chained lts p [u, t'] u'.tgt :=
  ⟨d.coinitial.trans hp, d.validU, d.srcT', d.validT', d.cofinal.symm⟩

/-- **The two ways round a diamond are causally equivalent.** -/
theorem Diamond.cEq {t u u' t' : Transition State Label}
    (d : Diamond lts t u u' t') (h : Indep t u) {p : State} (hp : t.src = p) :
    CEq lts Indep p u'.tgt [t, u'] [u, t'] :=
  CEq.swap h d.lblU' d.dirU' d.lblT' d.dirT' (d.chainedLeft hp) (d.chainedRight hp)

/-- **The Square Property produces a diamond.** -/
theorem Diamond.ofSquare [IsIndep lts Indep] [SquareProperty lts Indep]
    {t u : Transition State Label} (htv : t.Valid lts) (huv : u.Valid lts) (h : Indep t u) :
    ∃ u' t', Diamond lts t u u' t' := by
  obtain ⟨w, hw₁, hw₂⟩ := SquareProperty.square (Indep := Indep) htv huv h
  exact ⟨_, _,
    { validT := htv, validU := huv, validU' := hw₁, validT' := hw₂,
      coinitial := (IsIndep.coinitial (lts := lts) (Indep := Indep) h).symm,
      srcU' := rfl, srcT' := rfl,
      cofinal := rfl, lblU' := rfl, dirU' := rfl, lblT' := rfl, dirT' := rfl }⟩

/--
**Propagation of Coinitial Independence.**  Independence is a property of the
commuting diamond rather than of one particular pair of its edges: it
propagates from one corner of the diamond to the next.

The conclusion pairs `u'` with the *reversal* of `t`.  That is forced: both
leave `Q`, whereas `u'` and `t'` are cofinal and so are never a candidate for
a relation that only ever relates coinitial transitions.
-/
class CPI (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Independence propagates round the diamond, from the corner `P` to `Q`. -/
  cpi : ∀ {t u u' t' : Transition State Label},
    Diamond lts t u u' t' → Indep t u → Indep u' t.rev

/--
**Lemma 4.4.**  Coinitial transitions whose labels are mutually inverse — the
same action taken in opposite directions — are never independent.

The proof is the paper's *degenerate diamond*: `t`, `u`, `t.rev`, `u.rev` close
a square with two copies of the source, and `PCI` walked round it yields
`Indep t.rev t.rev`.
-/
theorem not_indep_of_rev_lbl [CPI lts Indep] [IndepIrrefl Indep]
    {t u : Transition State Label} (htv : t.Valid lts) (huv : u.Valid lts)
    (hco : u.src = t.src) (hlbl : u.lbl = t.lbl) (hdir : u.dir = t.dir.rev) :
    ¬ Indep t u := by
  intro hind
  have d : Diamond lts t u t.rev u.rev :=
    { validT := htv, validU := huv
      validU' := Transition.rev_valid htv, validT' := Transition.rev_valid huv
      coinitial := hco, srcU' := rfl, srcT' := rfl
      cofinal := by simpa using hco.symm
      lblU' := by simpa using hlbl.symm
      dirU' := by simp [hdir]
      lblT' := by simpa using hlbl
      dirT' := by simp [hdir] }
  exact IndepIrrefl.irrefl (CPI.cpi d hind)

/--
**Backward Label Determinism** (Definition 4.5, Proposition 4.6).  Coinitial
backward transitions with the same label coincide.
-/
theorem bld_of_sp_bti_cpi [DecidableEq State] [DecidableEq Label]
    [SquareProperty lts Indep] [BTI lts Indep] [CPI lts Indep]
    [IndepSymm Indep] [IndepIrrefl Indep]
    {t u : Transition State Label} (htv : t.Valid lts) (huv : u.Valid lts)
    (htb : t.IsBwd) (hub : u.IsBwd) (hco : t.Coinitial u) (hlbl : t.lbl = u.lbl) :
    t = u := by
  refine Decidable.byContradiction fun hne => ?_
  have hind : Indep t u := BTI.bti htv huv hco htb hub hne
  obtain ⟨w, hw₁, hw₂⟩ := SquareProperty.square (Indep := Indep) htv huv hind
  set u' : Transition State Label := Transition.mk t.tgt u.lbl u.dir w
  set t' : Transition State Label := Transition.mk u.tgt t.lbl t.dir w
  have d : Diamond lts t u u' t' :=
    { validT := htv, validU := huv, validU' := hw₁, validT' := hw₂,
      coinitial := hco.symm, srcU' := rfl, srcT' := rfl, cofinal := rfl,
      lblU' := rfl, dirU' := rfl, lblT' := rfl, dirT' := rfl }
  -- `PCI` makes the residual of `u` independent of the reversal of `t` …
  have hpci : Indep u' t.rev := CPI.cpi d hind
  -- … but those two are coinitial with mutually inverse labels.
  refine not_indep_of_rev_lbl (Indep := Indep) (Transition.rev_valid htv) hw₁ rfl ?_ ?_
    (IndepSymm.symm hpci)
  · simpa using hlbl.symm
  · have hbt : t.dir = Dir.bwd := htb
    change u.dir = Dir.rev (Dir.rev t.dir)
    rw [hbt]
    exact hub

/--
**Same event.**  The smallest equivalence relation identifying the two
opposite `t`-edges of a diamond whose coinitial pair is independent.

Two transitions are different occurrences of the same event exactly when they
are related by this.
-/
def SameEvent (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) :
    Transition State Label → Transition State Label → Prop :=
  Relation.EqvGen fun t t' => ∃ u u', Diamond lts t u u' t' ∧ Indep t u

theorem SameEvent.refl (t : Transition State Label) : SameEvent lts Indep t t :=
  Relation.EqvGen.refl t

theorem SameEvent.symm {t t' : Transition State Label} (h : SameEvent lts Indep t t') :
    SameEvent lts Indep t' t := Relation.EqvGen.symm _ _ h

theorem SameEvent.trans {t t' t'' : Transition State Label}
    (h₁ : SameEvent lts Indep t t') (h₂ : SameEvent lts Indep t' t'') :
    SameEvent lts Indep t t'' := Relation.EqvGen.trans _ _ _ h₁ h₂

/-- Opposite edges of an independent diamond are the same event. -/
theorem SameEvent.of_diamond {t u u' t' : Transition State Label}
    (d : Diamond lts t u u' t') (h : Indep t u) : SameEvent lts Indep t t' :=
  Relation.EqvGen.rel _ _ ⟨u, u', d, h⟩

/--
**Permuting produces the same event.**  Delaying `t` past an independent `u`
replaces it by a different transition, but one belonging to the same event —
and the two orders are causally equivalent.
-/
theorem SameEvent.of_square [IsIndep lts Indep] [SquareProperty lts Indep]
    {t u : Transition State Label} (htv : t.Valid lts) (huv : u.Valid lts) (h : Indep t u) :
    ∃ u' t', Diamond lts t u u' t' ∧ SameEvent lts Indep t t' := by
  obtain ⟨u', t', d⟩ := Diamond.ofSquare (Indep := Indep) htv huv h
  exact ⟨u', t', d, SameEvent.of_diamond d h⟩

/-- Occurrences of the same event agree on direction. -/
theorem SameEvent.dir_eq {t t' : Transition State Label} (h : SameEvent lts Indep t t') :
    t.dir = t'.dir := by
  induction h with
  | rel x y hxy => obtain ⟨u, u', d, -⟩ := hxy; exact d.dirT'.symm
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Occurrences of the same event agree on the label — the event *has* a label. -/
theorem SameEvent.lbl_eq {t t' : Transition State Label} (h : SameEvent lts Indep t t') :
    t.lbl = t'.lbl := by
  induction h with
  | rel x y hxy => obtain ⟨u, u', d, -⟩ := hxy; exact d.lblT'.symm
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/--
**Reversal maps events to reverse events.**

Rotating the diamond a quarter turn sends the pair `(t, t')` to
`(t.rev, t'.rev)`, and the independence the rotated diamond needs is exactly
what `CPI` produces.  The rotational symmetry that Lanese–Phillips–Ulidowski
build into their *general* definition of events is therefore already available
from the simplified one, once `CPI` is assumed.
-/
theorem sameEvent_rev [CPI lts Indep] [IndepSymm Indep] {t t' : Transition State Label}
    (h : SameEvent lts Indep t t') : SameEvent lts Indep t.rev t'.rev := by
  induction h with
  | rel x y hxy =>
    obtain ⟨u, u', d, hi⟩ := hxy
    refine SameEvent.of_diamond (u := u') (u' := u) ?_ (IndepSymm.symm (CPI.cpi d hi))
    exact
      { validT := Transition.rev_valid d.validT, validU := d.validU'
        validU' := d.validU, validT' := Transition.rev_valid d.validT'
        coinitial := d.srcU', srcU' := d.coinitial
        srcT' := d.cofinal.symm, cofinal := d.srcT'.symm
        lblU' := d.lblU'.symm, dirU' := d.dirU'.symm
        lblT' := by simpa using d.lblT'
        dirT' := by simp [d.dirT'] }
  | refl x => exact SameEvent.refl x.rev
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/--
**Independence Respects Events.**  Whether two transitions are independent
depends only on which events they belong to.

This is the axiom that separates causal safety and liveness from causal
consistency: Lanese–Phillips–Ulidowski exhibit a pre-reversible LTSI which is
causally consistent but, lacking `IRE`, satisfies neither.
-/
class IRE (lts : LTS State Label)
    (Indep : Transition State Label → Transition State Label → Prop) : Prop where
  /-- Independence transports along the event relation. -/
  ire : ∀ {t t' u : Transition State Label},
    SameEvent lts Indep t t' → Indep t' u → Indep t u

end Cslib.LTS
