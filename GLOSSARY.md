---
tags: [glossary, reference, category-theory, domainspec, terminology]
node_type: reference
status: current
nature: technical, reference
version: 1.0.1
last_updated: 2026-04-29
---

# Glossary

A reference for terms used throughout DomainSpec. Three sections: **standard category-theory primitives** (used as-is, no surprise), **DomainSpec-specific terms** (with honesty notes where the name is custom or borrowed), and **internal milestone labels** (the M-numbers and T-numbers, what each points to, and its current status).

If you read a DomainSpec document and a term sounds like jargon you don't recognize, look here. If it's a standard term, this page tells you it's standard. If it's custom, this page tells you that too — and what a working mathematician would recognize it as.

---

## 1 — Categorical primitives

Standard category-theory terms, used in DomainSpec exactly as in Mac Lane / nLab / Mathlib.

- **$\mathcal{L}_1$, $\mathcal{L}_2$** — small categories. In DomainSpec: $\mathcal{L}_1$ is the domain ontology (objects = domain concepts; morphisms = functional aspects); $\mathcal{L}_2$ is the artifact-type schema (objects = artifact types; morphisms = type-level aspects).

- **Functor $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$** — the compiler. Preserves composition and identity. No special properties unless asserted.

- **Faithful** — injective on each hom-set: for every pair $X, Y \in \mathcal{L}_1$, the function $\mathrm{Hom}_{\mathcal{L}_1}(X, Y) \to \mathrm{Hom}_{\mathcal{L}_2}(\Delta X, \Delta Y)$ is injective. Distinct domain morphisms with the same source and target map to distinct artifact morphisms.

- **Full** — surjective on hom-sets. Every artifact morphism between $\Delta(X)$ and $\Delta(Y)$ is the image of some domain morphism.

- **Fully faithful** — both. Equivalent to: $\Delta$ is an equivalence onto its essential image.

- **Injective on objects** — the function $\Delta : \mathrm{Ob}(\mathcal{L}_1) \to \mathrm{Ob}(\mathcal{L}_2)$ is injective. Distinct domain concepts map to distinct artifact types. Independent of fullness.

- **Presheaf / copresheaf** — a functor into $\mathbf{Set}$ (or $\mathbf{Type}$). A copresheaf $I \in \mathbf{Set}^{\mathcal{L}_1}$ is "populated domain data": each domain concept gets a set of concrete instances.

- **Left Kan extension $\mathrm{Lan}_F$** — left adjoint to precomposition $F^*$. Computed pointwise as a colimit over the comma category $(F \downarrow d)$. In DomainSpec: $\Sigma_\Delta$, the most efficient migration.

- **Right Kan extension $\mathrm{Ran}_F$** — right adjoint to precomposition. Computed pointwise as a limit over the structured arrow category $(d \downarrow F)$. In DomainSpec: $\Pi_\Delta$, the most conservative migration.

- **Adjunction unit $\eta : \mathrm{id} \Rightarrow \Delta^* \, \Sigma_\Delta$** — for an adjunction $\Sigma_\Delta \dashv \Delta^*$, the natural transformation marking the round-trip: populate, push forward, pull back. Whether $\eta$ is iso measures whether the round-trip recovers the input. (Generic form: for $L \dashv R$, $\eta : \mathrm{id} \Rightarrow R L$.)

- **Representable functor** — a functor isomorphic to $\mathrm{Hom}(c, -)$ for some object $c$. M2 is a representability conjecture.

- **Monomorphism (mono) / isomorphism (iso)** — standard. In $\mathbf{Set}$: injective / bijective on the underlying function.

- **Comma category $(F \downarrow G)$** — given $F : A \to C$ and $G : B \to C$, the category whose objects are triples $(a, b, F(a) \to G(b))$ and whose morphisms are commuting squares. The general construction.

- **Costructured arrow category $(F \downarrow d)$** — the special case where $G$ is the constant functor at $d \in D$, so objects are pairs $(c, F(c) \to d)$. (Dually, $(d \downarrow F)$ is the *structured arrow* category, used for $\mathrm{Ran}_F$.) The colimit of the projection $(F \downarrow d) \to C$ composed with the diagram functor is what computes $\mathrm{Lan}_F$ pointwise.

- **Cocontinuous** — preserves colimits. Left adjoints are cocontinuous; in particular, $\mathrm{Lan}_F$ (as the left adjoint to $F^*$) is.

---

## 2 — DomainSpec-specific terms

Terms specific to this project. Where the name is custom or borrowed, a note translates it to standard usage.

### Compilation and contract

- **Compiler / compilation contract** — the functor $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$. Not a generation process — a structural commitment about how domain morphisms map to artifact morphisms. Composition-preserving by construction.

- **Schema level** — the level of $\mathcal{L}_1$ and $\mathcal{L}_2$ themselves: types, type-level morphisms, the contract $\Delta$.

- **Instance level** — the level of presheaves $\mathbf{Set}^{\mathcal{L}_1}$ and $\mathbf{Set}^{\mathcal{L}_2}$: populated data, migrations, the round-trip unit.

### Residue

- **Schema residue** — *conditional on a restricted form of M2.* If a right adjoint $\Delta \dashv G$ exists at the schema level, schema residue is the failure of the unit $\eta^{\mathrm{sch}}_v : v \to G(\Delta(v))$ to be iso. Measures: domain concepts that have no faithful shadow in the artifact type system. The unrestricted M2 conjecture (existence of $G$ for arbitrary $\Delta$) is **refuted** in `M2Counter.lean`; the open question is which restriction on $\Delta$ recovers representability. Until that restricted form is settled, this is a *prospective* definition — the concept is only well-defined once $G$ is exhibited.

- **Instance residue** — failure of $\eta^{\mathrm{ins}}_I : I \Rightarrow \Delta^*(\Sigma_\Delta(I))$ to be iso. Measures: domain data lost (or hallucinated) when populated, compiled, and read back.

> **Note on "residue."** Borrowed from information-theoretic intuition (what a translation cannot carry through). Not the residue of complex analysis (residue of a meromorphic function) and not the residue of group theory (coset). If you've seen the word in those contexts, set them aside — DomainSpec uses it in the sense "what the translation could not preserve."

### Coreflective functor

- **Coreflective functor** (unit side) — a functor $F : C \to D$ for which the **unit** of the Kan-extension adjunction $\mathrm{Lan}_F \dashv F^*$ is invertible; equivalently, the left adjoint $\mathrm{Lan}_F$ is fully faithful. The graded versions live in `CoreflectiveHierarchy.lean`: `LanFaithful` (unit componentwise *monic* — the weakest level, $\mathrm{Lan}_F$ faithful), `InstanceCoreflective` (unit componentwise *iso*), `SchemaCoreflective`, and `IsCoreflective` (both layers). By the Yoneda bridge (`YonedaBridge.lean`, `Functor.fullyFaithfulEquivLanFullyFaithful`), `F` is fully faithful iff `Lan_F` is — so `InstanceCoreflective F` is equivalent to **`F` itself being fully faithful**. The counit-side dual is the **reflective functor** ($F^*$ fully faithful), graded in `ReflectiveHierarchy.lean`.

> **Note on the name.** This was originally called a "fractal" functor — a metaphor (*the part determines the whole*, the way a fractal's part carries the structure of the whole), not a mathematical term. It has been renamed to what it actually denotes. A translation recovered without loss by its Kan extension is exactly a **coreflective** (unit side) or **reflective** (counit side) situation; this matches Mathlib's convention, where `CategoryTheory.Reflective` is a fully faithful *right* adjoint (the counit-iso side). The `Is`-prefix in `IsCoreflective` / `IsReflective` avoids a clash with that existing class. See [`lean-formalization/NAMING.md`](lean-formalization/NAMING.md) for the full translation table. The "fractal" word survives only as branding for the [visualization](visualization/fractals.html).

### Migration vocabulary

- **Skolem null** — a fresh witness introduced by $\Sigma_\Delta = \mathrm{Lan}_\Delta$ when filling fields the contract $\Delta$ does not determine. Borrowed from Skolemization (the introduction of fresh function symbols to eliminate existential quantifiers) and from the database-theory tradition (Spivak). Not the empty set; an unconstrained witness.

- **Push-forward / pull-back / conservative migration** — the three operations of the M5 triple. Push-forward (left adjoint) is most efficient (Skolem-null witnesses); pull-back is precomposition; conservative migration (right adjoint) joins all valid completions.

### Two-layer framing

- **Two-layer coherence** — the question of whether schema-level discipline ($\Delta$ injective + faithful, or fully faithful) forces instance-level fidelity ($\eta^{\mathrm{ins}}_I$ iso for all $I$). Refuted in strong form (M6; see `M6Counter.lean`). The weak monic form (M6′) is refuted for universal $I$ and proven on the ind-fragment; the M6-restricted variant is proven (`M6Restricted.lean`).

> **Note on `TwoLayerCoherence` vs `TwoLayerCoherence_strong` in `DomainSpec.lean`.** The naming in the Lean file is misleading. `TwoLayerCoherence` (no suffix) is the *refuted* M6 strong (inj-on-obj + faithful $\Rightarrow$ iso). `TwoLayerCoherence_strong` has a stronger antecedent (fully faithful $\Rightarrow$ iso) and is provable from `instanceCoreflective_of_fullyFaithful`. The `_strong` suffix refers to the antecedent being stronger, not the conclusion. A future rename would help.

### Carrier vocabulary

- **Meta-type** — one of `entity`, `operation`, `constraint`, `relationship`. The four canonical kinds an object of $\mathcal{L}_1$ can have, recorded by the typing functor $\tau : \mathcal{L}_1 \to \mathrm{Disc}(\mathcal{T})$.

- **Edge law $\mathcal{E}$** — a decidable relation on meta-types governing which meta-type pairs admit morphisms. Axiomatized in DomainSpec; the specific predicate is project-defined.

- **DomainSpec** — framework name for the domain formalization (L1 in the seven-layer model). See [docs/meta-layers-reference.md](docs/meta-layers-reference.md) for the layer model and [docs/lean-formalization-guide.md](docs/lean-formalization-guide.md) for the map from concepts in this glossary to Lean code.

---

## 3 — Internal milestone labels

The M-numbers and T-numbers are project-internal labels for specific claims in the framework. Each entry below names the claim, gives its **status**, and points to where it lives.

| Label | Claim | Status | Location |
|---|---|---|---|
| **M1** | Cocontinuity of $\Delta$ at the schema level | Framework assumption (free from Mathlib once $\Delta$ is declared a left Kan extension) | `DomainSpec.lean` § "M1 — Cocontinuity is a theorem at the schema level" (comment block only) |
| **M2 (unrestricted)** | Schema-level right adjoint exists for arbitrary $\Delta$; equivalently, $\mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$ is representable for every $b$ | **Refuted** (formalized) | `M2Counter.lean` `M2_unrestricted_false` (proven, no `sorry`) |
| **M2 (restricted)** | Same statement under a restriction on $\Delta$ (fully faithful / dense / pointwise codense — to be identified) | **Conjectural (open)** | `DomainSpec.lean` `SchemaAdjunctionConjecture` (currently states the unrestricted form) |
| **M3** | $\Delta$ is injective on objects and faithful | Framework assumption | `DomainSpec.lean` `IsInjectiveOnObjects`, `Functor.Faithful` typeclass arguments |
| **M4** | Temporal indexing: a join-semilattice $T$ of times, with $\mathcal{L}_1, \mathcal{L}_2 : T \to \mathbf{Cat}$ | Framework assumption | `DomainSpec.lean` `variable {T : Type*} [SemilatticeSup T] [Category T]` |
| **M5** | Instance-level adjunction triple $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ | Classical theorem (Mac Lane); **`sorry` in our Lean file** | `DomainSpec.lean` `Δ_sigma`, `Δ_pi`, `InstanceLeftAdjunction`, `InstanceRightAdjunction` (all `sorry`) |
| **M6 (strong)** | Inj-on-obj + faithful $\Rightarrow$ $\eta^{\mathrm{ins}}_I$ iso for every $I$ | **Refuted** (formalized) | `M6Counter.lean` `m6_strong_refuted` (proven, no `sorry`) |
| **M6 (weak / M6')** | Faithful $\Rightarrow$ $\eta^{\mathrm{ins}}_I$ pointwise *monic* for every $I$ | **Refuted in general; proven on $\mathrm{Ind}(\mathcal{L}_1)$** | The universal-$I$ monic form is refuted by a bicyclic witness; the ind-fragment form (faithful $\Delta \Rightarrow$ unit mono on ind-presheaves) is proven unconditional. Both mechanized here: `Bicyclic.lean` (`lanUnit_app_not_mono_bicyclic`) and `M6PrimeOnInd.lean` (`unit_mono_on_Ind`), sorry-free. |
| **M6-restricted** | Inj + faithful $\Rightarrow$ iso on a reflective subcategory of $\mathbf{Set}^{\mathcal{L}_1}$ | **Proven** | `M6Restricted.lean` `m6_restricted` (no `sorry`): under `InstanceReflective F`, `IsIso (η_X) ↔ X ∈ F*`-essential-image. |
| **T0'** | Compilation Confluence (per time slice). Bundles C1, C2, C3 below | Partial — C1 proved, C2/C3 stubs | `DomainSpec.lean` `T0'_C1` (proved); C2, C3 commented |
| **T0'_C1** | Determinism: $g = g' \Rightarrow \Delta(g) = \Delta(g')$ | Proved (trivial — `congrArg`) | `DomainSpec.lean` `theorem T0'_C1` |
| **T0'_C2** | Image validity: every morphism's image satisfies the edge law | Open (commented sketch) | `DomainSpec.lean` comment block; needs typing functor on $\mathcal{L}_2$ |
| **T0'_C3** | Per-step entropy bound from A4 | Open (commented sketch) | `DomainSpec.lean` comment block; needs measure theory and concrete `N_plus` |
| **A1** | Meta-types: each $\mathcal{L}_1$-object is tagged by a typing functor $\tau$ into $\mathrm{Disc}(\mathcal{T})$, with $\mathcal{T} = \{\text{entity, operation, constraint, relationship}\}$ | Assumption | `DomainSpec.lean` `axiom EdgeLaw`, `variable (τ ...)` |
| **A_time** (= M4) | Time is a join-semilattice viewed as a thin category; $\mathcal{L}_1, \mathcal{L}_2 : T \to \mathbf{Cat}$ | Assumption | `DomainSpec.lean` `variable {T : Type*} [SemilatticeSup T] [Category T]` |
| **A_Kan** (= M1) | A dense subcategory $K$ and base compiler $\Delta_{\text{base}}$ at each time, with $\Delta$ the left Kan extension | Assumption | `DomainSpec.lean` `variable (I ...) (Δ_base ...) [(Δ t).IsLeftKanExtension ...]` |
| **A_inj** (= M3) | $\Delta$ is injective on objects and faithful at every time | Assumption | `DomainSpec.lean` `[∀ t, IsInjectiveOnObjects (Δ t)] [∀ t, Functor.Faithful (Δ t)]` |
| **A4** | Per-step neighbor measure (entropy bound input for T0'_C3) | Assumption | `DomainSpec.lean` referenced in T0'_C3 comment block; concrete `N_plus` not yet defined |

> **Note on the gap between A1 and A4.** The numbering reflects the file's history, not a sequence: A_time, A_Kan, A_inj are named axioms that align with M4, M1, M3 respectively, while A1 and A4 are numerals tied to specific T0' obligations. There is no A2 or A3. A future rename would smooth this out.

### Definition and three results for `LanFaithful` in `CoreflectiveHierarchy.lean` (proved, no sorries)

| Name | Claim | Status |
|---|---|---|
| `LanFaithful` | Definition: unit of $\mathrm{Lan}_F \dashv F^*$ componentwise monic | Definition |
| `lanFaithful_iff_lan_faithful` | $F$ Lan-faithful $\iff$ $\mathrm{Lan}_F$ faithful | Proved |
| `lanFaithful_id` | $\mathrm{id}_C$ is Lan-faithful | Proved |
| `lanFaithful_of_fullyFaithful` | $F$ fully faithful $\Rightarrow$ $F$ Lan-faithful | Proved |

---

## Appendix — Mapping to related literature

DomainSpec uses standard categorical machinery, recombined for an applied question. The closest neighbors:

- **Spivak, *Functorial Data Migration*** (2012, *Information and Computation*). The instance-level triple $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ is exactly Spivak's three migration functors. Notation matches. DomainSpec's contribution is not the triple — it's the framing (residue, two layers, the M6 question).

- **Mac Lane, *Categories for the Working Mathematician* (Ch. X — Kan Extensions).** The classical theorems on existence and pointwise computation of $\mathrm{Lan}_F$, $\mathrm{Ran}_F$. Underlies M5 entirely.

- **Lawvere, *Adjointness in Foundations* (1969).** Adjoints as approximation. The framing of $\eta$ as "what the round-trip cannot recover" is Lawverian in spirit.

- **nLab — *Kan extension*, *Adjoint functor theorem*, *Density***. For the precise statements and naming of the standard results.

- **Mathlib `CategoryTheory.Functor.KanExtension`.** The Lean implementation of pointwise Kan extensions used (or stubbed) in `DomainSpec.lean` and in the proof of `m6_strong_refuted`.

The property we formalize **does** have established names: $\mathrm{Lan}_F$ faithful (`LanFaithful`), $\mathrm{Lan}_F$ fully faithful / unit-iso (the **coreflective** side, `InstanceCoreflective`), and $F^*$ fully faithful (the **reflective** side, `InstanceReflective`). Earlier drafts called these "fractal" / "cofractal" and claimed no established name existed; that was an artifact of the metaphor, now corrected (see `NAMING.md`). The conditions are small, useful, and standard; the results about them are precise but not deep. The genuinely new mathematical content of DomainSpec — to the extent there is any — is likely concentrated in `m6_strong_refuted` and in the framing of the two-layer audit, not in the categorical machinery.
