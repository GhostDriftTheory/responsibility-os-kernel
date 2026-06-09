# Responsibility OS Kernel

A Lean 4 formalization of a kernel-level Responsibility OS claim, built from the ADIC assurance core.

This repository contains one primary Lean file:

- `ResponsibilityOS.lean`

The file formalizes an ADIC assurance core and exposes it as a Responsibility OS Kernel: a category-theoretic structure in which operations, audit traces, responsibility records, and judgment grounds travel together under composition.

The clean line is:

```text
ADIC assurance core -> responsibility-preserving kernel -> policy-relevant inspectability
```

## Core claim

If inspectable governance is formalized as preservation of all responsibility/evidence distinctions, then faithfulness is necessary; for a specified observation policy, the required condition is preservation of the policy-relevant distinctions.

The connection to any concrete governance deployment requires additional interpretation beyond this formalization.

In particular, this repository does not prove that real-world AI governance in general must adopt a specific policy. It proves the mathematical kernel: once a policy says that certain responsibility/evidence distinctions must remain inspectable, a visible operational view must preserve those distinctions.

## ADIC and Responsibility OS

ADIC is the implementation architecture for recording and replaying computation, evidence, audit traces, judgment grounds, and responsibility records.

The Responsibility OS Kernel is the mathematical layer showing how such records can be made to travel with operations under composition.

In this sense:

- ADIC is the implementation architecture.
- The Responsibility OS Kernel is the Lean-verified mathematical kernel.
- A complete real-world Responsibility OS deployment remains outside this Lean proof.

## What this repository verifies

1. **ADIC assurance core**

   `ResponsibilityOS.ADICAssuranceCore` is the public-facing alias for the indexed assurance structure. It carries an operational category, an evidence fiber family, forward handoff by `push`, backward audit by `pull`, an adjunction `push ⊣ pull`, a standard trace section, and a Beck-Chevalley structural assumption.

2. **Total responsibility category**

   `ResponsibilityOS.responsibilityCategory` is the Grothendieck construction over the operational category. Operations and responsibility evidence travel together in this total category.

3. **Faithful responsibility trace**

   `ResponsibilityOS.standard_trace_is_faithful` proves that the standard responsibility trace is faithful, so distinct operational transitions remain distinguishable when carried with responsibility evidence.

4. **Forward responsibility handoff**

   `ResponsibilityOS.forward_handoff_factors_uniquely` proves unique factorization through the responsibility-carrying forward lift.

5. **Backward audit factorization**

   `ResponsibilityOS.backward_audit_factors_uniquely` proves unique factorization through the backward audit lift.

6. **Policy-relevant inspectability**

   `ResponsibilityOS.ObservationPolicy` specifies which responsibility/evidence distinctions must remain inspectable. `ResponsibilityOS.PreservesPolicy` says that a visible view preserves every distinction required by such a policy.

7. **Complete policy sanity check**

   `ResponsibilityOS.preserves_complete_policy_iff_faithful` proves that, under `ResponsibilityOS.CompletePolicy`, policy preservation is equivalent to functor faithfulness. This is a useful sanity check, not the main strength of the repository.

8. **Trace-policy counterexample**

   The main counterexample is the explicit trace policy in `ResponsibilityOS.CollapseCounterexample.tracePolicy`. Lean proves that `traceA` and `traceB` are policy-relevant via `ResponsibilityOS.trace_policy_distinction_is_relevant`, and that the visible operational view does not preserve this policy via `ResponsibilityOS.operational_view_does_not_preserve_trace_policy`.

9. **Collapse counterexample**

   `ResponsibilityOS.forgetting_responsibility_layer_can_collapse_distinctions` shows that a forgetful operational view can identify distinct responsibility traces.

## What is not proven

* This does not prove that any real-world AI system is safe.
* This does not prove legal or regulatory compliance.
* This does not prove EU AI Act compliance.
* This does not prove completeness of all possible evidence.
* This does not derive Beck-Chevalley; it remains an external structural assumption.
* This does not prove that real-world AI governance in general must adopt the policies formalized here.
* This does not replace operational governance, audits, or organizational controls.
* For the definitions in this file, this is a kernel-level formalization of policy preservation and faithfulness, not a complete Responsibility OS implementation.

## Key Lean names

- `ResponsibilityOS.ADICAssuranceCore`
- `ResponsibilityOS.Kernel`
- `ResponsibilityOS.responsibility_section_forgets_to_identity`
- `ResponsibilityOS.standard_trace_is_faithful`
- `ResponsibilityOS.forward_handoff_factors_uniquely`
- `ResponsibilityOS.backward_audit_factors_uniquely`
- `ResponsibilityOS.ObservationPolicy`
- `ResponsibilityOS.PreservesPolicy`
- `ResponsibilityOS.CompletePolicy`
- `ResponsibilityOS.preserves_complete_policy_iff_faithful`
- `ResponsibilityOS.complete_inspectability_requires_faithful`
- `ResponsibilityOS.nonfaithful_view_not_completely_inspectable`
- `ResponsibilityOS.CollapseCounterexample.tracePolicy`
- `ResponsibilityOS.CollapseCounterexample.trace_policy_relevant`
- `ResponsibilityOS.CollapseCounterexample.U_does_not_preserve_trace_policy`
- `ResponsibilityOS.trace_policy_distinction_is_relevant`
- `ResponsibilityOS.operational_view_does_not_preserve_trace_policy`
- `ResponsibilityOS.forgetting_responsibility_layer_can_collapse_distinctions`
- `ResponsibilityOS.inspectable_governance_requires_faithful_responsibility_layer_counterexample`

## Verification

```bash
lake update
lake exe cache get
lake env lean ResponsibilityOS.lean
```

For CI-oriented verification, this repository also includes:

- `check.ps1`
- `.github/workflows/lean.yml`

`check.ps1` verifies the Lean file and checks that the policy-level declarations and counterexample names remain present.

Successful verification returns to the prompt with no errors.
