# Categorical Extraction Schema

Target schemas for the Tier 1 extractors (`L1-extractor`, `L2-extractor`, `delta-extractor`)
that materialize a feature's compilation contract Δ : L₁ → L₂ as a finite, machine-checkable
category, against which the predicates from `lean-formalization/FractalOP.lean`
(`SchemaFractal`, `InstanceFractal`, `Fractal`) can be evaluated.

All three extractors emit JSON files under
`docs/features/{feature}/_categorical/` in the **domainspec** repo:

- `L1.json` — the domain category
- `L2.json` — the code/schema/test/infra category
- `delta.json` — the explicit functor mapping
- `extraction.log.md` — provenance: which files were read, which heuristics matched

These three files are the fixed input contract for Tier 2/3 verifiers.

---

## L1.json — the domain category

```jsonc
{
  "feature": "payment-processing",
  "source_commit": "<git sha>",
  "objects": [
    {
      "id": "payment.PaymentTransaction",         // namespaced ID from SPEC.md concept table
      "meta_type": "Entity",                       // one of the 24 DomainSpec meta-types
      "anchor": "docs/features/payment-processing/domain.md#paymenttransaction",
      "fields": [                                  // structural data, not categorical
        { "name": "amount", "type_ref": "shared.Money", "required": true }
      ],
      "invariants": [                              // for state machines / entities
        "amount.value > 0"
      ]
    }
    // ... one entry per concept in the SPEC.md concept table
  ],
  "morphisms": [
    {
      "id": "payment.ProcessPayment::performs",   // unique morphism id
      "source": "payment.ProcessPayment",
      "target": "payment.PaymentTransaction",
      "rel_type": "performs",                      // one of the 26 typed relationships
      "anchor": "docs/features/payment-processing/operations.md#processpayment",
      "evidence": "ProcessPayment input/postcondition references PaymentTransaction"
    }
    // ... transitions, produces (events), enforces (rules), uses (deps), etc.
  ],
  "composition": [
    // optional: explicit composites, when authored relationships imply a chain.
    // Required for faithfulness checking: if h = g ∘ f exists in L₁, Δ must reflect it.
    { "id": "...", "of": ["morphism_id_f", "morphism_id_g"] }
  ],
  "identities_implicit": true                      // identities at every object are implicit
}
```

### Object meta_type vocabulary (24)

`Entity, ValueObject, Enum, Operation, Query, Calculation, Rule, Policy, Workflow, Saga,
Interface, Event, Mapping, StateMachine, Page, Layout, Component, ViewModel, Hook, Form,
Action, Guard, Binding, Adapter`

(plus `StateIndicator` per UI taxonomy if present.)

### Morphism rel_type vocabulary (26)

From `RELATIONSHIPS.md`. Examples: `performs, produces, consumes, enforces, transitions,
guards, requires, computes, exposes, maps, depends_on, derives, instruments, observes,
emits, reads, writes, ...`

Each rel_type carries its own composition and identity discipline (see `RELATIONSHIPS.md`).
The extractor should **not invent** rel_types not in the vocabulary — unknown relationships
go to `extraction.log.md` as gaps.

---

## L2.json — the code / test / infra category

```jsonc
{
  "feature": "payment-processing",
  "source_commit": "<git sha>",
  "objects": [
    {
      "id": "src.modules.payment.domain.PaymentTransaction",
      "kind": "TSType",                           // TSType | TSFunction | TSModule | TestSuite | TestCase | OTelMetric | PromAlert | IaCNode | E2EScenario
      "path": "src/modules/payment/domain/payment-transaction.ts",
      "loc_range": [12, 47],
      "biz_anchor": "payment.PaymentTransaction"  // value of @biz tag if present, else null
    }
  ],
  "morphisms": [
    {
      "id": "import:payment-transaction->money",
      "source": "src.modules.payment.domain.PaymentTransaction",
      "target": "shared.Money",                   // resolved via tsconfig paths
      "rel_type": "imports",                      // imports | calls | derives_test | emits_metric | alerts_on | ...
      "evidence": "import { Money } from '@shared/money'"
    }
  ]
}
```

L₂ is **not** the TypeScript AST verbatim — it's a coarse-grained category whose structure
is what Δ can plausibly map into. We only record morphisms that have a typed counterpart
in L₁'s rel_type vocabulary (e.g., `imports` → reflects `uses`/`depends_on`;
`derives_test` → reflects `enforces`/`postcondition`; `emits_metric` → reflects
`observes`).

---

## delta.json — the functor Δ : L₁ → L₂

```jsonc
{
  "feature": "payment-processing",
  "source_commit": "<git sha>",
  "object_map": [
    {
      "l1": "payment.PaymentTransaction",
      "l2": ["src.modules.payment.domain.PaymentTransaction"],
      "evidence": "@biz payment.PaymentTransaction tag found at src/modules/payment/domain/payment-transaction.ts:12",
      "confidence": "direct"                      // direct | derivation-rule | heuristic | none
    },
    {
      "l1": "payment.MaxAmountRule",
      "l2": ["tests.features.payment-processing.rules.max-amount.spec.ts"],
      "evidence": "TEST-PIPELINE rule: every Rule produces a guard test",
      "confidence": "derivation-rule"
    },
    {
      "l1": "payment.RetryPolicy",
      "l2": [],                                    // empty image → potential schema-residue
      "evidence": null,
      "confidence": "none"
    }
  ],
  "morphism_map": [
    {
      "l1": "payment.ProcessPayment::performs",
      "l2": ["import:process-payment->payment-transaction"],
      "confidence": "direct"
    }
  ],
  "diagnostics": {
    "objects_unmapped":  ["payment.RetryPolicy", ...],          // L₁ objects with empty Δ image
    "objects_orphan_l2": ["src.modules.payment.utils.legacy"],  // L₂ objects with no L₁ preimage
    "objects_multi_mapped": [                                   // injectivity violations
      { "l1": ["a", "b"], "l2": "shared_artifact" }
    ],
    "morphisms_unwitnessed": [...],                             // L₁ morphisms with no L₂ structural witness
    "rel_type_coverage": {                                       // by rel_type, % of morphisms with a witness
      "performs": 0.83,
      "transitions": 1.00,
      "enforces": 0.40
    }
  }
}
```

The `diagnostics` block is exactly the shape Tier 2 expects:

- `objects_unmapped` ≠ ∅ → counterexample to **injectivity-on-objects** in the surjective sense
  (every L₁ object should have ≥ 1 image; failure implies missing implementation).
- `objects_orphan_l2` ≠ ∅ → counterexample to **representability** (M2): L₂ artifact with no L₁
  preimage means Δ* cannot be a left/right inverse on it.
- `objects_multi_mapped` ≠ ∅ → counterexample to **injectivity** (Δ collapses two concepts).
- `morphisms_unwitnessed` ≠ ∅ → counterexample to **faithfulness**: an L₁ morphism with no
  structural reflection in L₂ means Δ does not reflect the equation it lives in.

---

## Maps to the theorem repo

| extraction artifact | feeds | Lean predicate |
|---|---|---|
| `delta.json::objects_multi_mapped` | injectivity-checker | `IsInjectiveOnObjects Δ` (DomainSpec.lean) |
| `delta.json::morphisms_unwitnessed` | faithfulness-checker | `Functor.Faithful Δ` |
| `delta.json::objects_orphan_l2` | m2-representability-checker | M2 conjecture (open in DomainSpec.lean) |
| schema verdict | schema-fractal-prover | `SchemaFractal F adj` (FractalOP.lean) |
| runtime / test fixture round-trip | instance-fractal-prover | `InstanceFractal F` (FractalOP.lean) |
| any of the above failing | counterexample-finder + lean-emitter | sibling of `M6Counter.lean` |

A green run produces a Lean file that instantiates `SchemaFractal Δ adj` and (when fixtures
are available) `InstanceFractal Δ`, and lake-builds clean. A red run produces a Lean file
mirroring `M6Counter.lean` that proves `¬ SchemaFractal` or `¬ InstanceFractal` for the
extracted Δ — the verdict is then a checked refutation, not an opinion.

---

## Non-goals

- L₂ is not a faithful image of TypeScript semantics. The model is coarse on purpose:
  we only need enough structure for the chosen predicates.
- Composition is partial: we record only the composites the framework's rel_type
  vocabulary already implies. We do not free-generate the morphism algebra.
- Identities are implicit; the extractors do not emit them.
