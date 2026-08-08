/-
Copyright (c) 2026 Tetsuo Yokoyama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuo Yokoyama
-/
import CslibReversible.CausalEquiv
import CslibReversible.Diamond
import CslibReversible.Parabolic
import CslibReversible.RevPath
import CslibReversible.CausalConsistency
import CslibReversible.Events
import CslibReversible.EventCount
import CslibReversible.CausalSafety
import CslibReversible.NRE
import CslibReversible.CausalLiveness
import CslibReversible.Independence
import CslibReversible.Instances.Product
import CslibReversible.Complexity.Garbage
import CslibReversible.Complexity.Machine

/-!
# Axiom audit

The results of this development must rest on nothing but the standard
axioms of Lean's classical logic.  `#print axioms` is wrapped in
`#guard_msgs` so that the build *fails* if a `sorryAx` ever appears, rather
than merely reporting it.

The transition-system layer gets by on `propext` and `Quot.sound`.  The
complexity layer does not, and the pins below record where the line falls:
counting with `Finset` drags in `Classical.choice` through Mathlib's own
cardinality lemmas, so `Cslib.Reversible.fiberWidth_le_card` cannot be
choice-free however it is proved.  Pinning it is what keeps that fact a
measured one rather than an assumed one.
-/

open Cslib.LTS

/-- info: 'Cslib.LTS.Transition.rev_valid' does not depend on any axioms -/
#guard_msgs in
#print axioms Transition.rev_valid

/-- info: 'Cslib.LTS.Chained.append' does not depend on any axioms -/
#guard_msgs in
#print axioms Chained.append

/-- info: 'Cslib.LTS.CEq.chained' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CEq.chained

/-- info: 'Cslib.LTS.CEq.comp' depends on axioms: [propext] -/
#guard_msgs in
#print axioms CEq.comp

/-- info: 'Cslib.LTS.CEq.isEquiv' does not depend on any axioms -/
#guard_msgs in
#print axioms CEq.isEquiv

/-- info: 'Cslib.LTS.exists_origin' does not depend on any axioms -/
#guard_msgs in
#print axioms exists_origin

/-- info: 'Cslib.LTS.bstep_diamond' depends on axioms: [propext] -/
#guard_msgs in
#print axioms bstep_diamond

/-- info: 'Cslib.LTS.unique_origin' depends on axioms: [propext] -/
#guard_msgs in
#print axioms unique_origin

/-- info: 'Cslib.LTS.Origin.reflTransGen_eq' does not depend on any axioms -/
#guard_msgs in
#print axioms Origin.reflTransGen_eq

/-- info: 'Cslib.LTS.reflTransGen_cases_head' does not depend on any axioms -/
#guard_msgs in
#print axioms reflTransGen_cases_head

/-- info: 'Cslib.LTS.histLTS_bwd_unique' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.histLTS_bwd_unique

/-- info: 'Cslib.LTS.histLen_lt_of_bstep' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.histLen_lt_of_bstep

/-- info: 'Cslib.LTS.revProd_unique_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.revProd_unique_origin

/-- info: 'Cslib.LTS.exchange_of_square' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.exchange_of_square

/-- info: 'Cslib.LTS.FRun.of_mequiv' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.FRun.of_mequiv

/-- info: 'Cslib.LTS.FRun.mequiv_iff' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.FRun.mequiv_iff

/-- info: 'Cslib.LTS.reachable_of_mequiv' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.reachable_of_mequiv

/-- info: 'Cslib.LTS.fb_swap_or_cancel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.fb_swap_or_cancel

/-- info: 'Cslib.LTS.push_fwd' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.push_fwd

/-- info: 'Cslib.LTS.parabolic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.parabolic

/-- info: 'Cslib.LTS.CEq.rev' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.CEq.rev

/-- info: 'Cslib.LTS.cancel_path' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.cancel_path

/-- info: 'Cslib.LTS.Chained.revPath' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.Chained.revPath

/-- info: 'Cslib.LTS.bwd_cc' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.bwd_cc

/-- info: 'Cslib.LTS.fwd_cc_from_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.fwd_cc_from_origin

/-- info: 'Cslib.LTS.causal_consistency' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.causal_consistency

/-- info: 'Cslib.LTS.revProd_causal_consistency' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.revProd_causal_consistency

/-- info: 'Cslib.LTS.Diamond.cEq' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.Diamond.cEq

/-- info: 'Cslib.LTS.Diamond.ofSquare' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.Diamond.ofSquare

/-- info: 'Cslib.LTS.SameEvent.of_square' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.SameEvent.of_square

/-- info: 'Cslib.LTS.occ_rev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.occ_rev

/-- info: 'Cslib.LTS.eventCount_of_cEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.eventCount_of_cEq

/-- info: 'Cslib.LTS.CIndep.revRight' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.CIndep.revRight

/-- info: 'Cslib.LTS.ladder' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.ladder

/-- info: 'Cslib.LTS.CIndep.toIndep' does not depend on any axioms -/
#guard_msgs in
#print axioms Cslib.LTS.CIndep.toIndep

/-- info: 'Cslib.LTS.causal_safety' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.causal_safety

/-- info: 'Cslib.LTS.exists_forward_of_origin' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.exists_forward_of_origin

/-- info: 'Cslib.LTS.eventCount_eq_zero_of_sameEvent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.eventCount_eq_zero_of_sameEvent

/-- info: 'Cslib.LTS.nre' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.nre

/-- info: 'Cslib.LTS.swap_fwd' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.swap_fwd

/-- info: 'Cslib.LTS.pushEvent' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.pushEvent

/-- info: 'Cslib.LTS.causal_liveness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.LTS.causal_liveness

/-- info: 'Cslib.LTS.not_indep_of_rev_lbl' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.not_indep_of_rev_lbl

/-- info: 'Cslib.LTS.bld_of_sp_bti_cpi' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.bld_of_sp_bti_cpi

/-- info: 'Cslib.LTS.sameEvent_rev' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.sameEvent_rev

/-- info: 'Cslib.LTS.lbl_ne_of_cIndep' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.LTS.lbl_ne_of_cIndep

/-! ## The complexity layer -/

-- `whitespace := lax` because these names are long enough that the single-line
-- message would break the 100-column style limit.
/--
info: 'Cslib.Reversible.fiberWidth_le_card' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reversible.fiberWidth_le_card

/--
info: 'Cslib.Reversible.realization_fin_fiberWidth' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reversible.realization_fin_fiberWidth

/--
info: 'Cslib.Reversible.isLeast_garbageCard' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reversible.isLeast_garbageCard

/--
info: 'Cslib.Reversible.garbageBits_eq_zero_iff' depends on axioms: [propext, Classical.choice,
  Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reversible.garbageBits_eq_zero_iff

-- The line between the two layers is visible here.  That a reversible machine
-- ends distinct inputs in distinct configurations is `propext` alone; choice
-- appears only once the configurations start being counted.
/-- info: 'Cslib.Reversible.Computes.final_injective' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Cslib.Reversible.Computes.final_injective

/--
info: 'Cslib.Reversible.Computes.fiberWidth_le_card' depends on axioms: [propext,
  Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Cslib.Reversible.Computes.fiberWidth_le_card
