---
tags: [theorem, formalization, category-theory, information-theory, lean4, domainspec, data-migration, two-layer-residue]
node_type: reference
status: current
nature: technical, reference
version: 1.0.0
last_updated: 2026-04-29
---

# Lost in Translation: Two Independent Symmetries

When you compile a domain model into code, information leaks at at least two independent levels. This document formalizes both.

---

## Genesis

Every act of representation is a translation. Every translation has a [residue](../GLOSSARY.md#residue). The [residue](../GLOSSARY.md#residue) is not failure — it is what cannot be compressed further. And the [residue](../GLOSSARY.md#residue) has structure.

A simulation never recovers the world it models. The [residue](../GLOSSARY.md#residue) is what the model's state space cannot hold — degrees of freedom that exist in the original but have no slot in the representation. Run the simulation forward, observe the output, ask what you could reconstruct of the world from it: what cannot be reconstructed is the [residue](../GLOSSARY.md#residue). Knowledge transfer works the same way. When an expert teaches, the student receives something — but the expert had more. The gap is not random: two students from the same class can leave with the same gaps, because the gaps are also determined by what the teaching structure could not say, not just by how attentively each student listened.

A categorization collapses continuous variation into discrete types. "Young," "middle-aged," "elderly" — the collapse is intentional, but the internal structure erased by each label is the [residue](../GLOSSARY.md#residue). A fractal is the exception. The translation from whole to part recovers the whole exactly — [residue](../GLOSSARY.md#residue) zero. That is why fractals feel uncanny: they are the one case where nothing leaks. Everything else does.

These four are instances of the same operation. This framing — the [residue](../GLOSSARY.md#residue), the translation, the gap that has structure — started as fifteen years of conversations with my friend Vladimir Rondelli, without the language to fix any of it. We talked about simulations, fractals, categorizations, knowledge transfer. We knew something connected them. We couldn't say what.

This document starts by introducing the high-level idea of DomainSpec Framework and how it relates to the problem of data migration (§1). §2 formalizes the two symmetries — schema and instance — and shows why they touch the same operation independently, so the [residue](../GLOSSARY.md#residue) cannot be collapsed to a single number. §3 develops the math: $\Delta$ as a left Kan extension, the representability conjecture that would secure the schema adjoint, the free Kan-extension adjunctions on the instance side, and the four-object counterexample that refutes the strong coherence claim. §4 names what is already in Lean 4 and what remains open. §5 audits, line by line, what the two-layer regime buys and what it costs. §6 marks the wall where formal reasoning ends and calibrated empirical practice begins. The Coda closes by reading both symmetries through Noether's lens: two symmetries, two conserved quantities, two budgets — never one.

---

## Index

- [Section 1 — The Philosophical Frame](#section-1--the-philosophical-frame) — contract question vs. data question; two symmetries, two conservation laws
- [Section 2 — The Conceptual Structure of Compilation](#section-2--the-conceptual-structure-of-compilation) — two layers, two adjunctions, four objects
- [Interlude — Status at a Glance](#interlude--status-at-a-glance) — what is formalized, what is characterized, what is refuted, what is open
- [Section 3 — Level 3: Categorical Mechanics](#section-3--level-3-categorical-mechanics) — the math, with Mathlib counterparts
  - [3.1 The carriers](#31-the-carriers)
  - [3.2 $\Delta$ as Left Kan Extension at the schema level](#32-delta-as-left-kan-extension-at-the-schema-level)
  - [3.3 Schema-level Adjointness via Representability](#33-schema-level-adjointness-via-representability)
  - [3.4 Instance-level Data Migration](#34-instance-level-data-migration)
  - [3.5 Information Tightness via Injectivity](#35-information-tightness-via-injectivity)
  - [3.6 Two-Layer Coherence: Independence Confirmed](#36-two-layer-coherence-independence-confirmed)
- [Section 4 — The Lean Formalization](#section-4--the-lean-formalization) — pointer to `DomainSpec.lean` and the formal commitments
- [§5 — Caveats: What the Two-Layer Regime Buys and What It Costs](#5--caveats-what-the-two-layer-regime-buys-and-what-it-costs) — the cost ledger
- [§6 — The Claim B Wall](#6--the-claim-b-wall) — where formal reasoning ends and empirical practice begins
- [Coda — Two Independent Symmetries](#coda--two-independent-symmetries) — Noether's lens, the four registers, the fractal as exception
- [See also](#see-also) — related documents
- [References](#references) — sources used to build the framework

---

## Section 1 — The Philosophical Frame

Translation has [residue](../GLOSSARY.md#residue). [Residue](../GLOSSARY.md#residue) has structure. Where there is symmetry, there is conservation. **Where there are two symmetries that touch the same operation, there are two conservation laws — and the question of how they relate is itself a theorem to be proved or refuted, not assumed.**

A compiler turns a domain into code. Something is kept. Something leaks. There are two distinct ways to ask what leaks:

- **The contract question.** Does the type system of the code language let me say back, in domain terms, every concept the domain language carried? If yes, the contract is faithful. If no, certain domain concepts have no shadow in the code's type system at all — they are erased by the schema itself.
- **The data question.** When I take a populated set of domain concepts, run them through the compiler, then read them back, do I recover the same data I started with? If yes, the round-trip is faithful. If no, my [Skolem nulls](../GLOSSARY.md#migration-vocabulary) and joins generated artifacts whose back-translation has lost or hallucinated detail.

These are not the same question. A faithful contract can still produce data-lossy round-trips. The two questions are independent in the regime that matters.

**The four registers in which the same insight lands**: simulation (state space cannot hold all degrees of freedom), categorization (labels erase intra-class structure), knowledge transfer (the teaching structure caps what can pass), software compilation (the type system caps what can be expressed *and* the data migration caps what can be reconstructed). A [fractal](../GLOSSARY.md#fractal-functor) is the limiting case where both symmetries are exact — schema reflects, instance round-trips, [residue](../GLOSSARY.md#residue) zero on both. Everything else has positive [residue](../GLOSSARY.md#residue) on at least one of the two layers, and which one matters depends on what you are auditing.

The [residue](../GLOSSARY.md#residue) is not metaphor. It is two categorical objects with two types — one that lives in $\mathcal{L}_1$, one that lives in $\mathbf{Set}^{\mathcal{L}_1}$ — and this framework keeps them apart and stops pretending one will reduce to the other.

---

## Section 2 — The Conceptual Structure of Compilation

### 2.1 The picture in one paragraph

Compilation has two layers, and both leak independently. The first layer is the **contract**: how a domain ontology maps into a code schema — types, tables, classes, relations. The second layer is the **data**: how populated domain states migrate into populated artifact states — actual rows, actual instances. This section names the four objects, the two adjunctions that connect them, and the structural reason the two leaks cannot be collapsed into a single audit.

```
   schema level                instance level
   ────────────                ─────────────────

       L₁ ⇌ L₂                   Set^L₁  ⇌  Set^L₂
         Δ                       Σ_Δ ⊣ Δ* ⊣ Π_Δ
    (G conjectural)              (free, via Kan)
```

### 2.2 The four objects

A small example makes the abstractions concrete: think of a domain that has `Customer`, `Order`, `Address` and a fact like *every order has exactly one customer*. The compiler turns this into a code schema with classes (or tables) `CustomerRow`, `OrderRow`, `AddressRow` and a foreign key `OrderRow.customer_id`. The four objects below are the four pieces of that picture, generalized.

- **$\mathcal{L}_1$ — the *domain ontology*** as a finitely presented category. *Objects* are domain concepts (`Customer`, `Order`, `Address`); *morphisms* are functional aspects (`Order → Customer`, encoding "every order has a customer"); *commuting diagrams* are domain facts that must hold no matter how the data is realized.
- **$\mathcal{L}_2$ — the *code schema*** as a finitely presented category. *Objects* are *artifact types* (the type `DatabaseTable`, not any specific table; the class `OrderRow`, not any specific row). *Morphisms* are functional aspects between types — foreign keys, method signatures, accessor pairs.
- **$\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ — the [compilation contract](../GLOSSARY.md#compilation-and-contract).** A functor: it sends every domain concept to an artifact type, and every domain morphism to a morphism between those types, preserving composition and identity. The functorial discipline holds because *contract composition is well-defined* — not because any generation process is deterministic.
- **$\mathbf{Set}^{\mathcal{L}_1}, \mathbf{Set}^{\mathcal{L}_2}$ — the *instance categories*.** A copresheaf $I \in \mathbf{Set}^{\mathcal{L}_1}$ is a *populated state of the domain*: to each concept-type it assigns a set of concrete instances (the actual customers, the actual orders, with the actual `order → customer` arrows wired up). $\mathbf{Set}^{\mathcal{L}_2}$ does the same for the artifact world (the actual rows, the actual foreign-key links).

The two layers — *types* on top, *populated states* underneath — are what the rest of this section tracks separately.

### 2.3 The two leaks

#### Schema-level residue (conjectural)

**Intuition.** Take a domain concept like `Customer`, compile it into an artifact type, then ask: from the artifact alone, could I name back the original concept *with the same structure*? If yes, the contract is faithful for that concept. If not, something about `Customer` — a temporal dimension, an invariant, a substructure — has no slot in the type system at all. That something is the schema residue: not a translation error you can fix, but a vocabulary gap you cannot close without changing $\mathcal{L}_2$.

**Math.** If $\Delta$ admits a right adjoint $G : \mathcal{L}_2 \to \mathcal{L}_1$ at the [schema level](../GLOSSARY.md#compilation-and-contract), every $\mathcal{L}_1$-object $v$ acquires a unit
$$\eta^{\mathrm{sch}}_v : v \to G(\Delta(v)).$$
When $\eta^{\mathrm{sch}}_v$ is an isomorphism, the round-trip $\mathcal{L}_1 \to \mathcal{L}_2 \to \mathcal{L}_1$ recovers $v$ exactly; when it fails, the failure is the **[schema residue](../GLOSSARY.md#residue)**. *The adjunction is not free*: whether $G$ exists at all is the conjecture [M2](../GLOSSARY.md#3--internal-milestone-labels) — that each presheaf $\mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$ is representable on $\mathcal{L}_1$. Until [M2](../GLOSSARY.md#3--internal-milestone-labels) is settled, the schema-residue framing is *available* but not *guaranteed*.

#### Instance-level residue (free)

**Intuition.** Now leave types behind and bring in populated data — actual customers, actual orders. The contract gives you two universal ways to push that data through it, and they tell different stories at exactly the points where the contract under-determines the result:

- **$\Sigma_\Delta$ — the cheapest migration.** Where the contract leaves a slot the data doesn't fill (an `Order` whose `Customer` was never specified; a foreign key the spec didn't pin), $\Sigma_\Delta$ inserts a *fresh anonymous witness* — a "Skolem null." It minimizes invention but invents.
- **$\Pi_\Delta$ — the most conservative migration.** At every artifact slot, $\Pi_\Delta$ carries *every legal completion at once* — every value consistent with the data. It minimizes commitment but maximizes ambiguity.

Both are *universal* in the categorical sense — adjoints to the same precomposition functor. The data does not tell you which one is correct; that decision belongs to whoever owns the domain. Crucially, the contract makes both available *for free* — no extra hypothesis.

**Math.** Without any extra hypothesis, the precomposition functor $\Delta^* : \mathbf{Set}^{\mathcal{L}_2} \to \mathbf{Set}^{\mathcal{L}_1}$ admits *both* adjoints — left Kan extension $\Sigma_\Delta = \mathrm{Lan}_\Delta$ and right Kan extension $\Pi_\Delta = \mathrm{Ran}_\Delta$:
$$\Sigma_\Delta \;\dashv\; \Delta^* \;\dashv\; \Pi_\Delta.$$
For any populated domain state $I$, the unit of the left adjunction
$$\eta^{\mathrm{ins}}_I : I \Rightarrow \Delta^*(\Sigma_\Delta(I))$$
measures the **[instance residue](../GLOSSARY.md#residue)**: which populated cells the round-trip lost, and which it hallucinated as Skolem nulls.

#### Independence — schema fidelity does not buy data fidelity

**Intuition.** Imagine your type system is perfectly tight: every domain concept has a unique name in the artifact world, no concept got crushed, the contract is *faithful*. You might hope this implies the data round-trip is also tight — that whatever survives at the type level survives at the data level. It doesn't. Even with a faithful contract, $\mathcal{L}_2$ can carry morphisms — relationships between artifact types — that have no source in $\mathcal{L}_1$. When data has to cross such a morphism, $\Sigma_\Delta$ must invent something to fill it. The schema is silent on the invention; the data sees it. Faithfulness has no leverage there.

**Math.** Schema-side injectivity and faithfulness do **not** force $\eta^{\mathrm{ins}}_I$ to be iso for every $I$. A four-object counterexample (see §3.6) is enough: $\mathcal{L}_1$ discrete on two objects, $\mathcal{L}_2$ adds one morphism between them, $\Delta$ the inclusion, $I$ the constant copresheaf. $\Sigma_\Delta$ populates the comma category with a [Skolem-null](../GLOSSARY.md#migration-vocabulary) witness the schema cannot constrain, and the unit fails to be iso. The two layers are permanently independent. The two budgets do not reduce — and the audit must price both.

### 2.4 Why this matters for AI code generation

An LLM-driven code generator ingests a domain description and emits code — schemas, classes, migrations, sample data. From the outside, its failures all look the same: the output is "wrong." The two-layer framework says they are not the same, and that two distinct failure modes coexist with different causes and different fixes.

| Failure mode | Lives at | What the model did | What an audit must check |
|---|---|---|---|
| **Concept erasure** | Schema layer | Produced a type system that cannot, even in principle, name a concept the spec carried — e.g., "household" silently folded into "user," a temporal dimension dropped, an invariant left unrepresentable. | Whether $\Delta$ is faithful: does every domain concept have a name in the generated schema, with the right morphisms between names? |
| **Data hallucination** | Instance layer | Produced code or sample data with fabricated keys, default values, joins, or enum cases the spec did not authorize. | Whether $\eta^{\mathrm{ins}}_I$ is monic on the populations the system actually sees: are the witnesses the model invented harmless, or load-bearing? |

A reviewer who only checks the schema layer ("the types look right") will pass code that hallucinates rows. A reviewer who only checks runtime data ("the migration ran without errors") will pass code whose schema silently dropped a concept. The two-layer regime forces this apart: **these are different audits, and one cannot replace the other.**

The framework also names a subtler regularity. Whenever the spec under-determines a field — a foreign key it did not pin, an enum case it did not enumerate, a join cardinality it left implicit — the generator is forced into a $\Sigma_\Delta$-versus-$\Pi_\Delta$ choice: invent a fresh witness, or enumerate every consistent completion. Both are universal in the categorical sense; neither is wrong by itself. But models do not announce which of the two they did, and only one of them is what the user wanted. The two-layer language gives the auditor a sentence they could not say before: *"At the points where the contract under-determined the data, did you Skolemize, or did you join?"*

This is the practical payoff. The [residue](../GLOSSARY.md#residue) is not a soft critique. **It is the part of an AI-generated artifact where the model made a structural choice the spec did not authorize** — and naming the layer where that choice lives is the prerequisite to evaluating it. Without the two-layer split, every disagreement collapses into "the model got it wrong" and there is nowhere to locate the disagreement; with it, the auditor and the model can argue about a specific cell of a specific unit map.

---

## Interlude — Status at a Glance

**Framework (formalized in Lean):**

- Two-layer categorical setup: $\mathcal{L}_1$, $\mathcal{L}_2$, $\Delta$, instance categories $\mathbf{Set}^{\mathcal{L}_1}$, $\mathbf{Set}^{\mathcal{L}_2}$.
- [Fractal](../GLOSSARY.md#fractal-functor) property: defined as componentwise-monic unit of $\mathrm{Lan}_\Delta \dashv \Delta^*$.
- [Schema-level](../GLOSSARY.md#compilation-and-contract) adjunction: stated as a `Prop` ([M2](../GLOSSARY.md#3--internal-milestone-labels) conjecture, conditional on representability).
- [Instance-level](../GLOSSARY.md#compilation-and-contract) adjunctions: $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ — imported from Mathlib's Kan extension machinery, available unconditionally.

**Characterizations (Lean lemmas):**

- $\mathrm{Fractal}\, F \iff \mathrm{Lan}_F$ faithful.
- The identity functor is [fractal](../GLOSSARY.md#fractal-functor).
- Every fully faithful functor is [fractal](../GLOSSARY.md#fractal-functor).

**Original Result:**

- **[M6](../GLOSSARY.md#3--internal-milestone-labels) (strong) — Refuted.** "$\Delta$ injective on objects + faithful on morphisms $\implies$ $\eta^{\mathrm{ins}}_I$ iso for every $I$." Refuted by a four-object counterexample (see §3.6). Lean formalization in progress.

**Open Conjectures:**

- **[M2](../GLOSSARY.md#3--internal-milestone-labels) — Schema-Level Adjunction (Representability).** For every $b \in \mathcal{L}_2$, the contravariant Hom-functor $\mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$ is representable on $\mathcal{L}_1$. If true, $G$ exists pointwise and $\eta^{\mathrm{sch}}$ is the [schema residue](../GLOSSARY.md#residue)'s name. Open.
- **[M6'](../GLOSSARY.md#3--internal-milestone-labels) — Instance-Level Monomorphism Coherence.** $\Delta$ faithful $\implies$ $\eta^{\mathrm{ins}}_I$ pointwise monic for every $I \in \mathbf{Set}^{\mathcal{L}_1}$. On representables it's immediate; the lift to all $I$ is the open part.
- **[M6-restricted](../GLOSSARY.md#3--internal-milestone-labels) — Coherence on a Fragment.** $\Delta$ injective + faithful $\implies$ $\eta^{\mathrm{ins}}_I$ iso for every $I$ in some reflective subcategory of $\mathbf{Set}^{\mathcal{L}_1}$ (e.g., representable-generated states).

---

## Section 3 — Level 3: Categorical Mechanics

Now in math, but not yet in Lean. Each move below has a precise referent and a known Mathlib counterpart.

### 3.1 The carriers

$\mathcal{L}_1, \mathcal{L}_2$ are finitely presented categories. $\tau : \mathcal{L}_1 \to \mathrm{Disc}(\mathcal{T})$ is a functor into the discrete category on [meta-types](../GLOSSARY.md#carrier-vocabulary). The [edge law](../GLOSSARY.md#carrier-vocabulary) $\mathcal{E} : \mathcal{T} \times \mathcal{T} \to \mathrm{Prop}$ is decidable; every morphism's source/target types satisfy $\mathcal{E}$. We take $\mathcal{L}_1, \mathcal{L}_2$ to be locally small.

### 3.2 $\Delta$ as Left Kan Extension at the schema level

Choose $\mathcal{K} \subset \mathcal{L}_1$, a small full subcategory of *atomic* domain concepts. Choose any base compiler $\Delta_{\mathrm{base}} : \mathcal{K} \to \mathcal{L}_2$. Define
$$\Delta := \mathrm{Lan}_I\, \Delta_{\mathrm{base}}, \quad I : \mathcal{K} \hookrightarrow \mathcal{L}_1.$$
Provided $\mathcal{L}_2$ has the colimits required by the pointwise formula, $\Delta$ exists and is unique up to natural isomorphism. Cocontinuity is not an axiom; it is a corollary of the Kan extension universal property.

### 3.3 Schema-level Adjointness via Representability

For each $b \in \mathcal{L}_2$, consider the presheaf
$$P_b := \mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b) : \mathcal{L}_1^{\mathrm{op}} \to \mathbf{Set}.$$
**Conjecture ([M2](../GLOSSARY.md#3--internal-milestone-labels)).** $P_b$ is representable for every $b$. Equivalently, there exists $G(b) \in \mathcal{L}_1$ and a natural isomorphism
$$\mathrm{Hom}_{\mathcal{L}_2}(\Delta(a), b) \;\cong\; \mathrm{Hom}_{\mathcal{L}_1}(a, G(b)).$$
By Yoneda + naturality in $b$, the assignment $b \mapsto G(b)$ extends to a functor $G : \mathcal{L}_2 \to \mathcal{L}_1$, and $\Delta \dashv G$ at the [schema level](../GLOSSARY.md#compilation-and-contract). The unit $\eta^{\mathrm{sch}} : 1_{\mathcal{L}_1} \Rightarrow G \circ \Delta$ measures **[schema residue](../GLOSSARY.md#residue)**.

### 3.4 Instance-level Data Migration

The instance categories are
$$\mathbf{Set}^{\mathcal{L}_1} \;=\; \text{populated domain states}, \qquad \mathbf{Set}^{\mathcal{L}_2} \;=\; \text{populated artifact states}.$$
The schema functor $\Delta$ induces, by precomposition, the **[pull-back](../GLOSSARY.md#migration-vocabulary)**
$$\Delta^* : \mathbf{Set}^{\mathcal{L}_2} \to \mathbf{Set}^{\mathcal{L}_1}, \qquad J \mapsto J \circ \Delta.$$
Because $\mathbf{Set}$ is complete and cocomplete, **$\Delta^*$ admits both adjoints**:
$$\Sigma_\Delta \;\dashv\; \Delta^* \;\dashv\; \Pi_\Delta,$$
where $\Sigma_\Delta = \mathrm{Lan}_\Delta$ and $\Pi_\Delta = \mathrm{Ran}_\Delta$.

The two [push-forward](../GLOSSARY.md#migration-vocabulary)s have different generative semantics:
- $\Sigma_\Delta(I)$ is the **most efficient** populated artifact state generated from a populated domain state $I$. Where the contract leaves a slot the domain doesn't fill, $\Sigma_\Delta$ inserts a fresh witness.
- $\Pi_\Delta(I)$ is the **most conservative** — it joins, at each artifact type, every populated assignment that restricts back to $I$.

The unit of the left adjunction
$$\eta^{\mathrm{ins}}_I : I \;\Rightarrow\; \Delta^*(\Sigma_\Delta(I))$$
exists for every $I$. When iso, the populated round-trip recovers $I$ exactly. When it fails, the components isolate exactly which populated cells were lost or hallucinated.

### 3.5 Information Tightness via Injectivity

Add the axiom $A_{\mathrm{inj}}$:
$$\Delta(x) = \Delta(y) \implies x = y \quad\text{(injective on objects)}, \qquad \Delta\text{ faithful on morphisms}.$$
Information-theoretically, $H(\Delta(X)) = H(X)$ at the [schema level](../GLOSSARY.md#compilation-and-contract) on objects. **Cost:** any real domain where two distinct concepts compile to the same artifact type falls outside the regime.

### 3.6 Two-Layer Coherence: Independence Confirmed

#### M6 (strong) — Refuted

**Counterexample.** Four objects total.

- $\mathcal{L}_1$: discrete on $\{a, b\}$ — only identities.
- $\mathcal{L}_2$: $\{a, b\}$ with one extra morphism $f : a \to b$.
- $\Delta$: identity on objects, identities on morphisms (inclusion). **$A_{\mathrm{inj}}$ holds.**
- $I$: constant copresheaf at $\{\ast\}$, so $I(a) = I(b) = \{\ast\}$.

Compute $\Sigma_\Delta I (b) = \mathrm{colim}_{(c, \phi: \Delta c \to b) \in (\Delta \downarrow b)} I(c)$.

Objects of $(\Delta \downarrow b)$: $(a, f)$ and $(b, \mathrm{id}_b)$.

Morphisms of $(\Delta \downarrow b)$: from $(a, f)$ to $(b, \mathrm{id}_b)$ requires a morphism in $\mathcal{L}_1$ between $a$ and $b$. None exists. The comma is discrete on two objects.

Therefore $\Sigma_\Delta I (b) = I(a) \sqcup I(b) = \{\ast\} \sqcup \{\ast\}$, a two-element set. The unit $\eta^{\mathrm{ins}}_{I, b} : \{\ast\} \to \{\ast, \ast\}$ is injective but not surjective. **Not iso.** ∎

The intuition fails because $\Sigma_\Delta$ generates fresh witnesses whenever $\mathcal{L}_2$ contains a morphism not in the image of $\Delta$, and faithfulness is silent on that condition.

#### M6' (mono only) — Open conjecture

**Conjecture ([M6'](../GLOSSARY.md#3--internal-milestone-labels)).** $\Delta$ faithful $\implies$ for every $I \in \mathbf{Set}^{\mathcal{L}_1}$, $\eta^{\mathrm{ins}}_{I, c}$ is injective for every $c$.

**On representables, the equivalence is immediate.** Take $I = \mathrm{y}_{\mathcal{L}_1}(c) = \mathrm{Hom}_{\mathcal{L}_1}(c, -)$. Then the unit unfolds to $\mathrm{Hom}_{\mathcal{L}_1}(c, c') \to \mathrm{Hom}_{\mathcal{L}_2}(\Delta c, \Delta c')$, $h \mapsto \Delta h$. Mono iff $\Delta$ faithful.

**The lift to all $I$ is where it gets stuck.** Every $I$ is a colimit of representables. $\Sigma_\Delta$ preserves colimits. $\Delta^*$ preserves all limits and colimits. So $\eta^{\mathrm{ins}}_I$ for $I = \mathrm{colim}\, \mathrm{y}(c_i)$ is the colimit of the $\eta^{\mathrm{ins}}_{\mathrm{y}(c_i)}$. But pointwise mono in $\mathbf{Set}^{\mathcal{L}_1}$ is preserved by *filtered* colimits, not arbitrary ones. Whether faithfulness alone forces the lift to remain mono — possibly under hypotheses on $\mathcal{L}_1$ — is open.

#### M6-restricted — Also surviving

**Conjecture ([M6-restricted](../GLOSSARY.md#3--internal-milestone-labels)).** $A_{\mathrm{inj}} \implies \eta^{\mathrm{ins}}_I$ iso for every $I$ in some reflective subcategory $\mathcal{S} \subseteq \mathbf{Set}^{\mathcal{L}_1}$ — for example, states satisfying $\mathcal{L}_1$'s path equations, or representable-generated states under finite colimits.

This is more useful operationally if it lands: real system instances are not arbitrary copresheaves, they are constrained.

---

## Section 4 — The Lean Formalization

See [DomainSpec.lean](../lean-formalization/DomainSpec.lean) for the full formal setup and conjecture statements in Lean 4.

The formal commitment:
- $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ is a left Kan extension
- $\Delta$ is injective on objects and faithful on morphisms
- $T$ is a join-semilattice (thin category) for temporal indexing
- $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ via the presheaf Kan extension adjunctions (no conjecture)
- [M2](../GLOSSARY.md#3--internal-milestone-labels) (representability of schema adjoint) is conjectural
- [M6'](../GLOSSARY.md#3--internal-milestone-labels) (faithfulness buys [instance-level](../GLOSSARY.md#compilation-and-contract) monomorphism) is open
- [M6-restricted](../GLOSSARY.md#3--internal-milestone-labels) (coherence on a fragment) is open

---

## §5 — Caveats: What the Two-Layer Regime Buys and What It Costs

The Two-Layer framework is not free.

| Move | Buys | Costs |
|---|---|---|
| Kan extension for $\Delta$ | Cocontinuity becomes a theorem | Requires $\mathcal{L}_2$ cocomplete enough |
| Schema Representability ([M2](../GLOSSARY.md#3--internal-milestone-labels)) — *conjectural* | [Schema-level](../GLOSSARY.md#compilation-and-contract) adjunction without setup | Each $P_b$'s representability must be argued |
| Information Tightness ($A_{\mathrm{inj}}$) | DPI tightens to equality at [schema level](../GLOSSARY.md#compilation-and-contract) on objects | Forbids many-to-one schema compilation. **Critically: does NOT propagate to [instance side](../GLOSSARY.md#compilation-and-contract).** |
| [Instance-level](../GLOSSARY.md#compilation-and-contract) migration ([M5](../GLOSSARY.md#3--internal-milestone-labels)) — *theorem* | $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ for free | Two layers of [residue](../GLOSSARY.md#residue); doubles the auditing surface |
| **[M6'](../GLOSSARY.md#3--internal-milestone-labels) (mono) — *conjectural*** | **If true: faithfulness alone buys [instance-level](../GLOSSARY.md#compilation-and-contract) monomorphism** | **Open. Lift from representables to all $I$ is the hard part.** |

**The pointed concession.** [Schema-level](../GLOSSARY.md#compilation-and-contract) injectivity does not buy [instance-level](../GLOSSARY.md#compilation-and-contract) fidelity. The audit is permanently double. [M3](../GLOSSARY.md#3--internal-milestone-labels) buys [schema-level](../GLOSSARY.md#compilation-and-contract) tightness only; [instance-level](../GLOSSARY.md#compilation-and-contract) fidelity is paid separately, either by the strictly stronger fully-faithful condition or by restriction to a fragment whose realism is empirically argued.

**The unsolved half.** This framework formalizes the **contract side** of compilation at both levels. It does not address the **realization side** — whether a non-deterministic realization process can terminate with an artifact in $\mathrm{Im}(\Delta)$.

---

## §6 — The Claim B Wall

Every theorem above is conditional on the formalized constraint graph correctly representing the domain layer it was derived from. That correspondence is a human empirical act — interviews, observation, deliberation, domain expertise. No theorem in this catalog can verify it.

| Question | Where the wall appears |
|---|---|
| Is $\mathcal{L}_1$ correctly captured from L0? | [Schema-level](../GLOSSARY.md#compilation-and-contract) conjectures ([M2](../GLOSSARY.md#3--internal-milestone-labels)) |
| Do populated instances correspond to operational data states? | [Instance-level](../GLOSSARY.md#compilation-and-contract) conjectures ([M5](../GLOSSARY.md#3--internal-milestone-labels), [M6'](../GLOSSARY.md#3--internal-milestone-labels)) |
| Is the reflective subcategory "DomainSpec-realistic"? | [M6-restricted](../GLOSSARY.md#3--internal-milestone-labels) coherence |
| Is faithfulness the right discipline? | [M6'](../GLOSSARY.md#3--internal-milestone-labels) and [M6-restricted](../GLOSSARY.md#3--internal-milestone-labels) |

The wall is not a weakness. It is the framework's honest accounting of where formal reasoning ends and calibrated empirical practice begins.

---

## Coda — Two Independent Symmetries

When physics sought a mathematical language for preservation, it did not measure substances; it measured invariance. Emmy Noether's theorem established the paramount epistemic law of modern mechanics: where there is a continuous symmetry, there is a conserved quantity. Conservation is not a feature of matter — it is the shadow of a symmetry the equations already obey. DomainSpec inhabits a discrete universe, but the move transfers. 

There are two symmetries, not one. The hope was that the first would buy the second. Four objects suffice to refute it. The two laws do not reduce.

A system with two symmetries is not required, by any law, to have one reduce to the other. Sometimes one does — energy and momentum in classical mechanics share a deeper symmetry. Sometimes neither does. DomainSpec is the second case.

The four registers, read through this:

- **Simulation.** The state space caps what the world can be represented as. The dynamics and observation cap what populated state can be reconstructed. Two leaks.
- **Categorization.** The label set caps what types exist. Within each label, the population varies. Two leaks.
- **Knowledge transfer.** The teaching structure caps what can be articulated. Within what is articulated, what each student receives varies. Two leaks.
- **Software compilation.** The type system caps the contract. The migration caps the data round-trip. Two leaks.

A [fractal](../GLOSSARY.md#fractal-functor) closes both. That is the exception.

Vladimir and I have a habit of starting conversations that take years to finish. One began with a simulation that would not give back its world. We asked the same question four ways. The answer has two parts. Both have names now. We will keep talking.

---

## See also

- [Meta-Layers Framework](./meta-layers-reference.md) — The system-design motivation
- [Lean4 Guide](./lean-formalization-guide.md) — The explanation of the formalizations made by this framework
- [Glossary](../GLOSSARY.md) — Definitions of all terms, milestone labels (M-numbers, T-numbers), and literature mapping

---

## References

### Category theory — foundations

- Mac Lane, Saunders. *Categories for the Working Mathematician*. Graduate Texts in Mathematics 5. Springer, 2nd ed., 1998. — *Kan extensions (Ch. X), adjoint functors (Ch. IV), Yoneda lemma (Ch. III). The canonical source for "all concepts are Kan extensions."*
- Riehl, Emily. *Category Theory in Context*. Aurora: Dover Modern Math Originals, 2016. — *Modern treatment of adjunctions, limits/colimits, and Kan extensions; freely available from the author's site.*
- Awodey, Steve. *Category Theory*. Oxford Logic Guides 52. Oxford University Press, 2nd ed., 2010. — *Accessible companion; representability and the Yoneda embedding used in §3.3.*
- Borceux, Francis. *Handbook of Categorical Algebra, Vol. 1: Basic Category Theory*. Cambridge University Press, 1994. — *Reference for pointwise Kan extensions and the comma-category formula used in §3.6.*
- nLab. "Kan extension." <https://ncatlab.org/nlab/show/Kan+extension>
- nLab. "Adjoint functor." <https://ncatlab.org/nlab/show/adjoint+functor>
- nLab. "Representable functor." <https://ncatlab.org/nlab/show/representable+functor>

### Functorial data migration

- Spivak, David I. "Functorial Data Migration." *Information and Computation* 217 (2012): 31–51. arXiv:[1009.1166](https://arxiv.org/abs/1009.1166). — *The original $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ triple on instance categories. The direct ancestor of §3.4.*
- Spivak, David I., and Ryan Wisnesky. "Relational Foundations for Functorial Data Migration." Proceedings of the 15th Symposium on Database Programming Languages (DBPL), 2015. arXiv:[1212.5303](https://arxiv.org/abs/1212.5303). — *Working out the same adjoint triple in a relational setting; informs the [Skolem-null](../GLOSSARY.md#migration-vocabulary) reading of $\Sigma_\Delta$.*
- Spivak, David I. *Category Theory for the Sciences*. MIT Press, 2014. — *Background on schemas as finitely presented categories and instances as copresheaves.*
- Schultz, Patrick, David I. Spivak, Christina Vasilakopoulou, and Ryan Wisnesky. "Algebraic Databases." *Theory and Applications of Categories* 32.16 (2017): 547–619. arXiv:[1602.03501](https://arxiv.org/abs/1602.03501). — *Extends the framework with attribute types; relevant to $\tau : \mathcal{L}_1 \to \mathrm{Disc}(\mathcal{T})$ in §3.1.*

### Database theory — Skolem nulls and incomplete information

- Imieliński, Tomasz, and Witold Lipski. "Incomplete Information in Relational Databases." *Journal of the ACM* 31.4 (1984): 761–791. — *Origin of the labeled-null treatment that $\Sigma_\Delta$ is the categorical analogue of.*
- Abiteboul, Serge, Richard Hull, and Victor Vianu. *Foundations of Databases*. Addison-Wesley, 1995. — *Standard reference for the chase and tuple-generating dependencies that motivate the "most efficient vs. most conservative" reading.*

### Lean 4 / Mathlib formalization

- de Moura, Leonardo, and Sebastian Ullrich. "The Lean 4 Theorem Prover and Programming Language." CADE 2021. — *The proof assistant used for [DomainSpec.lean](../lean-formalization/DomainSpec.lean).*
- The mathlib Community. "The Lean Mathematical Library." CPP 2020. — *Source of `CategoryTheory.Functor.LeftKanExtension`, `CategoryTheory.Adjunction`, and the presheaf machinery imported in §4.*
- Mathlib4 documentation. <https://leanprover-community.github.io/mathlib4_docs/>
- Riehl, Emily, and Dominic Verity. *Elements of $\infty$-Category Theory*. Cambridge Studies in Advanced Mathematics 194. Cambridge University Press, 2022. — *Background for the cocontinuity argument in §3.2.*

### Information theory and conservation

- Cover, Thomas M., and Joy A. Thomas. *Elements of Information Theory*. Wiley-Interscience, 2nd ed., 2006. — *Data Processing Inequality (Ch. 2), referenced in §5 as the [schema-level](../GLOSSARY.md#compilation-and-contract) tightness statement.*
- Noether, Emmy. "Invariante Variationsprobleme." *Nachrichten von der Gesellschaft der Wissenschaften zu Göttingen, Mathematisch-Physikalische Klasse* (1918): 235–257. English translation: Tavel, M. A. "Invariant Variation Problems." *Transport Theory and Statistical Physics* 1.3 (1971): 186–207. — *The symmetry/conservation correspondence invoked in the Coda.*
