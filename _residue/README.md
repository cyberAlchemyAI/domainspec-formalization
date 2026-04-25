# _residue/

Ideas in flight. Not Nodes yet — possibly never will be.

The Strict Regime applies to `children/`. It does not apply here. This is the explicit escape valve: a place where half-formed thoughts can exist without being shoehorned into the Atomic Node shape, and without being silently lost.

## The maturity funnel

```
_residue/
  capture/             # raw inbox — timestamped dumps, conversations, half-thoughts
  sketches/            # being shaped, has a working title, not yet a candidate Node
  promotion-queue/     # candidate Nodes — has a proposed Node id and proposed edges
  archive/             # didn't make it. kept for traceability.
```

The intended flow:

1. **capture/** — anything goes. Date-prefix everything (`2026-04-25-some-thought.md`). Conversations, observations, fragments. No structure required.
2. **sketches/** — when a captured idea earns a working title and a paragraph of intent, it moves here. Still no Node structure required.
3. **promotion-queue/** — when a sketch has a proposed Node id, kind, and at least one edge, it moves here. Each item should already be in the proposed Node shape; promotion to `children/` is then a `mv`, not a rewrite.
4. **archive/** — for items that were considered and explicitly rejected. Keep them. The mortality rate is itself a metric.

## Why `_residue/` exists

The Strict Regime is honest only if there is somewhere outside it for ideas to live. Without `_residue/`, two failure modes appear:

- **Shoehorning** — authors force immature ideas into the Node shape because there's nowhere else, polluting the fractal with fake structure.
- **Loss** — ideas that don't fit get dropped entirely, losing the messy raw material that becomes the next breakthrough.

`_residue/` is the explicit acknowledgment that the framework does not yet capture everything. The metrics on this directory measure how much of reality the framework still hasn't absorbed.

## Health metrics

Tracked by `_explorer/`:

- **Time-to-promotion**: how long does an idea sit before becoming a Node?
- **Mortality rate**: capture → archive vs capture → Node
- **Capture rate**: items added per week (signals conceptual activity)

A repo where `_residue/` only grows is a repo that's stopped converting thinking into rigor. A repo where `_residue/` is empty is a repo that's stopped thinking.
