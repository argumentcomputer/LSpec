module
public import LSpecProofs.Filter
public import LSpecProofs.Report
public import LSpecProofs.Concurrency

/-!
# Compile-Time Axiom Audit (`LSpecProofs.Axioms`)

Enforces at build time (under both `lake build LSpecProofs` and `nix flake check`)
that every headline theorem in `LSpecProofs` depends exclusively on Lean's standard
axioms (`propext`, `Quot.sound`, and at most `Classical.choice`) — never `sorryAx`
or any custom axiom.
-/

/--
info: 'LSpec.Proofs.matchesTest_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.matchesTest_empty

/--
info: 'LSpec.Proofs.matchesTest_excludeTag_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.matchesTest_excludeTag_rejects

/--
info: 'LSpec.Proofs.matchesTest_exclude_rejects' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.matchesTest_exclude_rejects

/--
info: 'LSpec.Proofs.filterTree_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.filterTree_empty

/--
info: 'LSpec.Proofs.listTests_filterTree_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.listTests_filterTree_eq

/--
info: 'LSpec.Proofs.filterTree_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.filterTree_eq_none_iff

/--
info: 'LSpec.Proofs.filterTreeGo_noEmptyScopes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.filterTreeGo_noEmptyScopes

/--
info: 'LSpec.Proofs.filterTree_withResource_has_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.filterTree_withResource_has_leaf

/--
info: 'LSpec.Proofs.filterTree_idempotent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.filterTree_idempotent

/--
info: 'LSpec.Proofs.leafCount_eq_leaves_size' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.leafCount_eq_leaves_size

/--
info: 'LSpec.Proofs.failures_eq_filter_leaves' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.failures_eq_filter_leaves

/--
info: 'LSpec.Proofs.summarize_total_eq_leafCount' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.summarize_total_eq_leafCount

/--
info: 'LSpec.Proofs.summarize_failed_eq_failures_size' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.summarize_failed_eq_failures_size

/--
info: 'LSpec.Proofs.summarize_allPassed_iff_failures_empty' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.summarize_allPassed_iff_failures_empty

/--
info: 'LSpec.Proofs.summarize_allPassed_iff_forall' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.summarize_allPassed_iff_forall

/--
info: 'LSpec.Proofs.summarizeChildren_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.summarizeChildren_perm

/--
info: 'LSpec.Proofs.toListed_compilePlan' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.toListed_compilePlan

/--
info: 'LSpec.Proofs.compilePlan_seeds_deterministic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.compilePlan_seeds_deterministic

/--
info: 'LSpec.Proofs.skipAll_summary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.skipAll_summary

/--
info: 'LSpec.Proofs.computeWorkerCount_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.computeWorkerCount_bounds

/--
info: 'LSpec.Proofs.Concurrency.bounded_concurrency' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.bounded_concurrency

/--
info: 'LSpec.Proofs.Concurrency.seq_strict_left_to_right' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.seq_strict_left_to_right

/--
info: 'LSpec.Proofs.Concurrency.seq_exclusion' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.seq_exclusion

/--
info: 'LSpec.Proofs.Concurrency.seq_exclusion_at_root' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.seq_exclusion_at_root

/--
info: 'LSpec.Proofs.Concurrency.resPending_only_acquire' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.resPending_only_acquire

/--
info: 'LSpec.Proofs.Concurrency.resActive_release_requires_done' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.resActive_release_requires_done

/--
info: 'LSpec.Proofs.Concurrency.resource_bracket_invariant' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.resource_bracket_invariant

/--
info: 'LSpec.Proofs.Concurrency.resource_released_exactly_once_on_done' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.resource_released_exactly_once_on_done

/--
info: 'LSpec.Proofs.Concurrency.progress_deadlock_free' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.progress_deadlock_free

/--
info: 'LSpec.Proofs.Concurrency.termination_step_bound' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.termination_step_bound

/--
info: 'LSpec.Proofs.Concurrency.parallel_eq_sequential' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms LSpec.Proofs.Concurrency.parallel_eq_sequential
