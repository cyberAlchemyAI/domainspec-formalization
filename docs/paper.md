---
tags: [paper, theorem, formalization, category-theory, lean4, domainspec, data-migration, two-layer-residue]
node_type: paper
status: current
nature: technical, paper
version: 1.0.0
last_updated: 2026-04-29
---

# Lost in Translation: Two Independent Symmetries

Victor Boscaro

---

## Abstract

Schema compilation is acted on by two distinct symmetries, and each yields its own conservation law: a residue at the level of types and a residue at the level of populated data. Whether the two reduce to one is itself a theorem to be proved or refuted, not assumed. We formalize this phenomenon for a functor $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ between finitely presented categories, where $\mathcal{L}_1$ is a domain ontology and $\mathcal{L}_2$ is a target schema. At the instance level the migration triple $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ (left/right Kan extensions flanking precomposition) exists unconditionally; the unit $\eta^{\mathrm{ins}}_I : I \Rightarrow \Delta^*(\Sigma_\Delta I)$ measures the instance residue. At the schema level, a right adjoint $G : \mathcal{L}_2 \to \mathcal{L}_1$ would yield a schema residue via the unit $\eta^{\mathrm{sch}}$; its existence is the open M2 conjecture (representability of $\mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$). The two layers are independent: M6 Strong — "$\Delta$ injective on objects and faithful implies $\eta^{\mathrm{ins}}_I$ an isomorphism" — is refuted by a four-object counterexample, formalized in Lean 4. We introduce a two-dimensional coreflective hierarchy: on the instance axis $\mathrm{LanFaithful} \subseteq \mathrm{InstanceCoreflective}$, with $\mathrm{SchemaCoreflective}$ an orthogonal schema-axis condition, and $\mathrm{Coreflective} = \mathrm{SchemaCoreflective} \land \mathrm{InstanceCoreflective}$ characterizing the degree to which both residues vanish. Open problems include M2 and M6' (faithfulness implies pointwise-monic unit).

---

## 1. Introduction

Translation has residue, and the residue has structure. Where two distinct symmetries act on the same operation, there are two conservation laws, and the question of how they relate is itself a theorem to be proved or refuted, not assumed. This paper isolates two such symmetries on schema compilation, names the conserved quantity each one yields, and shows — by constructing a four-object counterexample formalized in Lean 4 — that the two laws do not collapse into one.

The motivating observation is not specific to compilers. Simulation, categorization, knowledge transfer, and software compilation are four registers of a single structure: in each, a representation caps both what the target language can express and what its populated states can reconstruct of the source. The present paper develops the case where the source and target are finitely presented categories.

**The two-layer setup.** Let $\mathcal{L}_1$ and $\mathcal{L}_2$ be finitely presented categories and $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ a functor — the *compilation contract* — preserving composition and identity. The *instance categories* $\mathbf{Set}^{\mathcal{L}_1}$ and $\mathbf{Set}^{\mathcal{L}_2}$ are the copresheaf categories: a copresheaf $I \in \mathbf{Set}^{\mathcal{L}_1}$ assigns to each domain concept a set of populated instances. Consider, for concreteness, $\mathcal{L}_1$ encoding a domain schema with an `Order` concept carrying a many-to-many relationship to `Product`, and $\mathcal{L}_2$ a relational schema representing this via a join table. The functor $\Delta$ sends `Order` and `Product` to their respective tables and the relationship to the join table's foreign-key span. Two distinct questions arise: (1) does the type system of $\mathcal{L}_2$ admit a functor back to $\mathcal{L}_1$ that reconstructs every domain concept up to isomorphism — the *schema question*; and (2) when a populated domain state is pushed forward through $\Delta$ and pulled back, is the original data recovered — the *instance question*. These questions have different mathematical homes, different sufficiency conditions, and, as we prove, no implication in either direction.

We refer to the formal framework developed here — the two-layer categorical setup, its adjunctions, and the coreflective hierarchy organizing residue-zero conditions — as **DomainSpec**.[^1]

[^1]: A longer, less formal exposition of the project's motivation and four-register framing is given in the companion document *Lost in Translation: Two Independent Symmetries* (`docs/domainspec-two-layer-framework.md`).

**Contributions.** This paper establishes:

- **Two-layer adjunction structure.** The precomposition functor $\Delta^* : \mathbf{Set}^{\mathcal{L}_2} \to \mathbf{Set}^{\mathcal{L}_1}$ admits both a left Kan extension $\Sigma_\Delta = \mathrm{Lan}_\Delta$ and a right Kan extension $\Pi_\Delta = \mathrm{Ran}_\Delta$, giving the triple $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ unconditionally. The unit $\eta^{\mathrm{ins}}_I : I \Rightarrow \Delta^*(\Sigma_\Delta I)$ is the *instance residue* — it exists for every $I$ without any hypothesis on $\Delta$.

- **Schema-level residue (conditional, M2-restricted).** A schema residue $\eta^{\mathrm{sch}} : \mathrm{id}_{\mathcal{L}_1} \Rightarrow G \circ \Delta$ requires a right adjoint $G : \mathcal{L}_2 \to \mathcal{L}_1$, which exists iff $\mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$ is representable for every $b \in \mathcal{L}_2$. The unrestricted form of this claim is **refuted**: a four-object counterexample (`L1 = Discrete (Fin 2)`, `L2 = {a, b, f}`, $\Delta$ the inclusion) breaks representability at $b$, formalized in [`M2Counter.lean`](../lean-formalization/M2Counter.lean) as [`M2_unrestricted_false`](../lean-formalization/M2Counter.lean#L54). The open question is which restriction on $\Delta$ recovers representability — call this conjecture M2-restricted.

- **Refutation of M6 Strong (Lean 4, no `sorry`).** The claim "$\Delta$ injective on objects and faithful on morphisms implies $\eta^{\mathrm{ins}}_I$ an isomorphism for every $I$" is false. A four-object counterexample suffices: $\mathcal{L}_1$ discrete on $\{a, b\}$, $\mathcal{L}_2$ adding a single morphism $f : a \to b$, $\Delta$ the inclusion, and $I$ the constant copresheaf at a singleton. The comma category $(\Delta \downarrow b)$ is discrete on two objects, so $\Sigma_\Delta I(b) = \{\ast\} \sqcup \{\ast\}$; the unit component $\eta^{\mathrm{ins}}_{I,b} : \{\ast\} \to \{\ast, \ast\}$ is injective but not surjective. The counterexample is formalized in `M6Counter.lean`.

- **Coreflective hierarchy (four levels, `CoreflectiveHierarchy.lean`).** We define and organize four graduated properties of a functor $F : C \to D$:
  - $\mathrm{LanFaithful}(F)$: the unit of $\mathrm{Lan}_F \dashv F^*$ is componentwise monic; equivalently, $\mathrm{Lan}_F$ is faithful.
  - $\mathrm{InstanceCoreflective}(F)$: the unit is componentwise an isomorphism — no Skolem-null witnesses are introduced.
  - $\mathrm{SchemaCoreflective}(F, \mathit{adj})$: for an explicit adjunction $F \dashv G$, the unit $\mathit{adj}.\mathit{unit}$ is a natural isomorphism.
  - $\mathrm{Coreflective}(F, \mathit{adj})$: both $\mathrm{SchemaCoreflective}$ and $\mathrm{InstanceCoreflective}$ hold — residue zero on both layers.

  The adjunction argument in $\mathrm{SchemaCoreflective}$ and $\mathrm{Coreflective}$ is explicit rather than inferred by typeclass resolution, preventing silent assumption of M2. Proved characterizations include: $\mathrm{LanFaithful}(F) \iff \mathrm{Lan}_F$ faithful; the identity functor is coreflective; every fully faithful $F$ (equipped with a right adjoint) is coreflective.

- **Open problems identified.** M2-restricted (schema-level representability under a yet-to-be-identified restriction on $\Delta$ — the unrestricted form is refuted in `M2Counter.lean`) and M6' (faithfulness implies $\eta^{\mathrm{ins}}_I$ pointwise monic for all $I$, not just representables) remain open. A weaker M6-restricted variant — coherence on a reflective subcategory of $\mathbf{Set}^{\mathcal{L}_1}$, e.g., states generated by finite colimits of representables — is also open and may be the operationally relevant case.

**Relation to prior work.** The instance-level triple $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ is Spivak's functorial data migration [1]. The contribution of this paper is not the triple but the two-layer audit: separating schema residue from instance residue, showing the layers do not cohere under the natural faithfulness hypothesis, and organizing the degree of coherence into the coreflective hierarchy.

**Roadmap.** Section 2 situates this work relative to prior literature. Section 3 fixes the categorical setup. Section 4 develops the two-layer framework and both adjunctions. Section 5 defines the coreflective hierarchy and proves the characterization theorems. Section 6 presents the four-object refutation of M6 Strong, with reference to the Lean 4 formalization. Section 7 states M6' and M6-restricted as open problems.

---

## 2. Related Work

**Functorial data migration.** The direct ancestor of the $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ triple is Spivak's functorial data migration [1, 2]. Spivak showed that any functor $\Delta$ between schema categories induces, via left and right Kan extension, a push-pull-push triple of migration functors between the corresponding instance categories, and that this triple accounts for a wide class of database operations — joins, projections, and Skolem-null introduction — in a uniform categorical language. Schultz, Spivak, Vasilakopoulou, and Wisnesky [10] later extended this framework to *algebraic databases*, integrating attribute typing into the categorical setup, which is relevant to any refinement of $\mathcal{L}_1$ that distinguishes attribute carriers from concept-types. The present paper inherits this triple entirely. Our contribution relative to Spivak is the *two-layer audit*: we separate the instance residue $\eta^{\mathrm{ins}}_I$ from the schema residue $\eta^{\mathrm{sch}}$, prove that the two layers are independent (refuting M6 Strong), and introduce the coreflective hierarchy as a graduated classification of how completely both residues vanish. None of these are addressed in [1, 2, 10].

**Skolem nulls and incomplete information.** The appearance of fresh witnesses in $\Sigma_\Delta I$ — the elements introduced when the comma category $(\Delta \downarrow b)$ contains objects not in the image of $\Delta$ — is the categorical analogue of Skolem nulls in the sense of Imieliński and Lipski [3]. That paper established the foundational treatment of labeled nulls and incomplete information in relational databases, showing that the "certain answers" semantics corresponds to a universal quantification over all possible completions of a partial database. The colimit formula $(\Sigma_\Delta I)(b) = \mathrm{colim}_{(\Delta \downarrow b)} I$ makes this quantification explicit: a Skolem witness at $b$ is precisely a connected component of $(\Delta \downarrow b)$ that contributes no constraint from $\mathcal{L}_1$. The M6 Strong refutation (Section 6) shows that such witnesses can appear even when $\Delta$ is injective and faithful.

**Kan extensions and the machinery of category theory.** The main technical tools — left and right Kan extensions, adjoint triples, the coend formula — are developed in Mac Lane [4, Ch. X] and Riehl [5]. Riehl's treatment is particularly useful for the pointwise formula and its coend representation. The coreflective hierarchy of Section 5 makes systematic use of the unit of an adjunction as a measure of invertibility, a perspective emphasized throughout [5]. Awodey [6] provides additional background on functor categories and copresheaves.

**Lean 4 and Mathlib.** All theorems in this paper that are marked as formalized are proved in Lean 4 [7] using Mathlib [8]. In particular, Mathlib's `CategoryTheory.Functor.KanExtension` provides the core infrastructure for left and right Kan extensions along arbitrary functors, including the pointwise formula and the adjunction isomorphism. The adjunction type `Adjunction` in Mathlib packages the unit and counit with the triangle identity proofs, which is used throughout the formalization.

---

## 3. Preliminaries

We briefly recall the categorical notions used throughout this paper. Standard references are Mac Lane [4] and Riehl [5]; readers already fluent in adjunctions and Yoneda may skip to Section 4.

**Categories and functors.** A *category* $\mathcal{C}$ consists of a collection of objects and, for each pair of objects $X, Y$, a hom-set $\mathrm{Hom}_{\mathcal{C}}(X, Y)$ of morphisms, together with associative, unital composition. A *functor* $F : \mathcal{C} \to \mathcal{D}$ assigns to each object and morphism of $\mathcal{C}$ an object and morphism of $\mathcal{D}$, preserving composition and identities. A natural transformation $\alpha : F \Rightarrow G$ between parallel functors assigns to each object $X \in \mathcal{C}$ a morphism $\alpha_X : F(X) \to G(X)$ in $\mathcal{D}$, commuting with all morphisms in $\mathcal{C}$. We say $F$ is *faithful* if the induced maps $\mathrm{Hom}_{\mathcal{C}}(X,Y) \to \mathrm{Hom}_{\mathcal{D}}(F X, F Y)$ are injective for all $X, Y$; *full* if they are surjective; and *fully faithful* if they are bijective. An equivalence of categories is a functor that is full, faithful, and essentially surjective.

**Copresheaves.** Given a small category $\mathcal{C}$, the *copresheaf category* $\mathbf{Set}^{\mathcal{C}}$ is the functor category $[\mathcal{C}, \mathbf{Set}]$: its objects are functors $\mathcal{C} \to \mathbf{Set}$ and its morphisms are natural transformations. Following Spivak [1], we interpret objects of $\mathbf{Set}^{\mathcal{C}}$ as *instance states* of the schema $\mathcal{C}$: each functor $I : \mathcal{C} \to \mathbf{Set}$ assigns to every schema object $c$ a set of concrete records $I(c)$, and to every schema morphism $f : c \to c'$ a function $I(f) : I(c) \to I(c')$ expressing how records in one table participate in records of another. The copresheaf category $\mathbf{Set}^{\mathcal{C}}$ is both complete and cocomplete, because $\mathbf{Set}$ is [4, Ch. V].

**Kan extensions.** Let $F : \mathcal{C} \to \mathcal{D}$ and $H : \mathcal{C} \to \mathcal{E}$ be functors. The *left Kan extension* $\mathrm{Lan}_F H : \mathcal{D} \to \mathcal{E}$, when it exists, is the universal functor equipped with a natural transformation $\eta : H \Rightarrow (\mathrm{Lan}_F H) \circ F$; it is characterized up to natural isomorphism by the adjunction $\mathrm{Hom}(\mathrm{Lan}_F H, K) \cong \mathrm{Hom}(H, K \circ F)$ for any $K : \mathcal{D} \to \mathcal{E}$. Dually, the *right Kan extension* $\mathrm{Ran}_F H$ is the universal functor with a transformation $(\mathrm{Ran}_F H) \circ F \Rightarrow H$. When $\mathcal{E}$ is cocomplete (resp. complete), pointwise left (resp. right) Kan extensions along any $F$ always exist, computed by the coend formula $(\mathrm{Lan}_F H)(d) = \int^{c \in \mathcal{C}} \mathrm{Hom}_{\mathcal{D}}(Fc, d) \cdot H(c)$ [4, Ch. X]. This coend formula is the basis of the data-migration interpretation given in Spivak [1].

**Adjunctions.** An *adjunction* $L \dashv R$ between functors $L : \mathcal{C} \to \mathcal{D}$ and $R : \mathcal{D} \to \mathcal{C}$ is a natural bijection $\mathrm{Hom}_{\mathcal{D}}(LX, Y) \cong \mathrm{Hom}_{\mathcal{C}}(X, RY)$, equivalently specified by a unit $\eta : \mathrm{id}_{\mathcal{C}} \Rightarrow R \circ L$ and counit $\varepsilon : L \circ R \Rightarrow \mathrm{id}_{\mathcal{D}}$ satisfying the triangle identities [4, Ch. IV]. The unit $\eta$ measures how well $R$ inverts $L$: the adjunction is a reflective localization precisely when every component $\eta_X$ is an isomorphism. The Lean formalization throughout this paper uses Mathlib's `Adjunction` type, which packages the unit and counit with the triangle identity proofs.

---

## 4. The Two-Layer Framework

We now define the DomainSpec two-layer framework precisely.

**Definition 4.1 (Schema categories).** Let $\mathcal{L}_1$ and $\mathcal{L}_2$ be small categories, finitely presented in the intended applications. We call $\mathcal{L}_1$ the *domain ontology* and $\mathcal{L}_2$ the *artifact schema*. Objects of $\mathcal{L}_1$ are domain concept-types; morphisms are functional aspects; commuting diagrams encode domain facts. Objects of $\mathcal{L}_2$ are artifact types; morphisms are functional aspects between artifact types.

**Definition 4.2 (Compilation functor).** The *compilation functor* is a functor
$$\Delta : \mathcal{L}_1 \longrightarrow \mathcal{L}_2.$$
It preserves composition and identities by functoriality — not by any assumption of determinism in the generation process. We call $\Delta$ the *compilation contract*.

**Definition 4.3 (Instance categories).** The *instance categories* are the copresheaf categories
$$\mathbf{Set}^{\mathcal{L}_1} = [\mathcal{L}_1, \mathbf{Set}], \qquad \mathbf{Set}^{\mathcal{L}_2} = [\mathcal{L}_2, \mathbf{Set}].$$
An object $I \in \mathbf{Set}^{\mathcal{L}_1}$ is a *populated domain state*: to each concept-type $c \in \mathcal{L}_1$ it assigns a set of concrete records $I(c)$, and to each functional aspect $f : c \to c'$ a function $I(f) : I(c) \to I(c')$. Likewise, objects of $\mathbf{Set}^{\mathcal{L}_2}$ are populated artifact states.

**Definition 4.4 (Pullback functor).** The compilation functor $\Delta$ induces by precomposition the *pullback* (or *restriction-of-scalars*) functor
$$\Delta^* : \mathbf{Set}^{\mathcal{L}_2} \longrightarrow \mathbf{Set}^{\mathcal{L}_1}, \qquad J \mapsto J \circ \Delta.$$
In Lean, $\Delta^*$ is realized as `(whiskeringLeft _ _ _).obj Δ` — Mathlib's left-whiskering functor, which sends a functor $J$ to the precomposition $J \circ \Delta$.

**Theorem 4.5 (Adjoint triple, unconditional).** The pullback functor $\Delta^*$ admits both a left adjoint $\Sigma_\Delta$ and a right adjoint $\Pi_\Delta$, forming an adjoint triple
$$\Sigma_\Delta \;\dashv\; \Delta^* \;\dashv\; \Pi_\Delta,$$
where $\Sigma_\Delta = \mathrm{Lan}_\Delta$ and $\Pi_\Delta = \mathrm{Ran}_\Delta$ are the left and right Kan extensions along $\Delta$.

*Proof.* Because $\mathbf{Set}$ is both complete and cocomplete, pointwise Kan extensions along any functor $\Delta$ exist in all copresheaf categories. The universal properties of $\mathrm{Lan}_\Delta$ and $\mathrm{Ran}_\Delta$ supply the adjunctions $\Sigma_\Delta \dashv \Delta^*$ and $\Delta^* \dashv \Pi_\Delta$ respectively. No hypothesis on $\Delta$ beyond being a functor is required. $\square$

The left adjoint $\Sigma_\Delta(I)$ is the most efficient populated artifact state generated from $I$: where the contract leaves a slot the domain does not fill, $\Sigma_\Delta$ inserts a fresh Skolem-null witness, computed pointwise by the comma-category colimit $(\Sigma_\Delta I)(b) = \mathrm{colim}_{(c,\, \Delta c \to b)} I(c)$. The right adjoint $\Pi_\Delta(I)$ is the most conservative migration: $(\Pi_\Delta I)(b) = \lim_{(b \to \Delta c)} I(c)$. Both are universal generation modes made available by $\Delta$ for free [1].

**Definition 4.6 (Instance residue unit).** For each populated domain state $I \in \mathbf{Set}^{\mathcal{L}_1}$, the unit of the adjunction $\Sigma_\Delta \dashv \Delta^*$ yields a natural transformation
$$\eta^{\mathrm{ins}}_I : I \;\Longrightarrow\; \Delta^*(\Sigma_\Delta I).$$
We call $\eta^{\mathrm{ins}}_I$ the *instance residue unit* of $I$. Its components $(\eta^{\mathrm{ins}}_I)_c : I(c) \to (\Delta^* \Sigma_\Delta I)(c)$ measure, at each domain concept-type $c$, how faithfully the round-trip $I \mapsto \Sigma_\Delta I \mapsto \Delta^*(\Sigma_\Delta I)$ recovers the original populated state. When every component is an isomorphism, the populated round-trip is exact and the instance residue is zero.

**Definition 4.7 (Schema residue, conditional on M2).** At the schema level, the situation is more delicate. For each $b \in \mathcal{L}_2$, define the presheaf
$$P_b := \mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b) : \mathcal{L}_1^{\mathrm{op}} \longrightarrow \mathbf{Set}, \qquad a \mapsto \mathrm{Hom}_{\mathcal{L}_2}(\Delta a, b).$$

**Conjecture 4.8 (M2-restricted — Schema-level adjunction via representability, under a restriction on $\Delta$).** *The unrestricted form of this conjecture — "for arbitrary $\Delta$ and every $b \in \mathcal{L}_2$, the presheaf $P_b = \mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$ is representable" — is **refuted** in `M2Counter.lean` (theorem `M2_unrestricted_false`) by the four-object setup of §6: $\mathcal{L}_1 = \mathrm{Discrete}(\mathrm{Fin}\,2)$, $\mathcal{L}_2 = \{a, b, f\}$, $\Delta$ the inclusion, $b$ the codomain of $f$.* The restricted conjecture asks: identify a class of functors $\Delta$ (e.g. fully faithful, dense, pointwise codense) for which, for every $b \in \mathcal{L}_2$, the presheaf $P_b = \mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$ is representable. That is, there exists an object $G(b) \in \mathcal{L}_1$ and a natural isomorphism
$$\mathrm{Hom}_{\mathcal{L}_2}(\Delta(a), b) \;\cong\; \mathrm{Hom}_{\mathcal{L}_1}(a, G(b))$$
for all $a \in \mathcal{L}_1$, naturally in both $a$ and $b$.

If Conjecture 4.8 holds, then by the Yoneda lemma the assignment $b \mapsto G(b)$ extends uniquely to a functor $G : \mathcal{L}_2 \to \mathcal{L}_1$, and the representability bijection constitutes a schema-level adjunction $\Delta \dashv G$. The unit of this adjunction is the *schema residue unit*
$$\eta^{\mathrm{sch}} : \mathrm{id}_{\mathcal{L}_1} \;\Longrightarrow\; G \circ \Delta,$$
whose component $\eta^{\mathrm{sch}}_v : v \to G(\Delta(v))$ measures whether the schema round-trip $\mathcal{L}_1 \xrightarrow{\Delta} \mathcal{L}_2 \xrightarrow{G} \mathcal{L}_1$ recovers the domain object $v$ up to isomorphism. Conjecture 4.8 is currently open in its restricted form (the unrestricted form being refuted in `M2Counter.lean`); the existence of $G$ and $\eta^{\mathrm{sch}}$ is conditional on it throughout this paper.

**The independence of the two layers.** Schema-level injectivity and faithfulness of $\Delta$ do not force $\eta^{\mathrm{ins}}_I$ to be an isomorphism for every $I$. The following minimal counterexample, constructed with four objects, demonstrates this. Take $\mathcal{L}_1$ discrete on $\{a, b\}$ (only identities), $\mathcal{L}_2 = \{a, b, f : a \to b\}$, and $\Delta$ the inclusion (injective on objects, faithful on morphisms). Let $I$ be the constant copresheaf $I(a) = I(b) = \{\ast\}$. The comma category $(\Delta \downarrow b)$ has two objects, $(a, f)$ and $(b, \mathrm{id}_b)$, and no non-identity morphism between them (because no morphism $a \to b$ exists in $\mathcal{L}_1$). Therefore $\Sigma_\Delta I(b) = I(a) \sqcup I(b) = \{\ast, \ast\}$, a two-element set, while $I(b) = \{\ast\}$. The component $(\eta^{\mathrm{ins}}_I)_b : \{\ast\} \to \{\ast, \ast\}$ is injective but not surjective — not an isomorphism. Thus the two residues are permanently independent; the audit is irreducibly double. The full proof and Lean formalization appear in Section 6.

---

## 5. The Coreflective Hierarchy

The DomainSpec framework admits a graduated classification of compilation functors according to how completely they preserve information on each of the two layers. We define four levels, from weakest to strongest, formalized in [`CoreflectiveHierarchy.lean`](../lean-formalization/CoreflectiveHierarchy.lean).

The hierarchy is two-dimensional. On the instance axis, $\mathrm{LanFaithful} \subseteq \mathrm{InstanceCoreflective}$. On an orthogonal schema axis sits $\mathrm{SchemaCoreflective}$, an independent (and conjectural) condition. The top of the hierarchy is the conjunction $\mathrm{Coreflective} = \mathrm{SchemaCoreflective} \land \mathrm{InstanceCoreflective}$, which requires both axes to be tight simultaneously.

### Level 1 — LanFaithful

**Definition 5.1 (LanFaithful).** A functor $F : C \to D$, admitting pointwise left Kan extensions along $F$ in $\mathbf{Set}^C$, is *Lan-faithful* if the unit $\eta : \mathrm{id}_{\mathbf{Set}^C} \Rightarrow F^* \circ \mathrm{Lan}_F$ of the adjunction $\mathrm{Lan}_F \dashv F^*$ is componentwise monic. That is,
$$\forall\, X : C \to \mathbf{Set},\; \forall\, c \in C, \quad (\eta_X)_c : X(c) \hookrightarrow (F^*(\mathrm{Lan}_F X))(c) \text{ is monic in } \mathbf{Set}.$$

In Lean, the property is stated as: for every copresheaf $X$ and every object $c$, the unit of the canonical $\mathrm{Lan}_F \dashv F^*$ adjunction is monic at $c$.
```lean
def LanFaithful (F : C ⥤ D)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  ∀ (X : C ⥤ Type v) (c : C),
    Mono (((F.lanAdjunction (Type v)).unit.app X).app c)
```
This is the weakest level of the hierarchy: it guarantees no information is lost in the round-trip $X \mapsto F^*(\mathrm{Lan}_F X)$, without yet requiring that nothing extra is introduced.

**Theorem 5.2 (LanFaithful iff $\mathrm{Lan}_F$ faithful).** $F$ is Lan-faithful if and only if the functor $\mathrm{Lan}_F : \mathbf{Set}^C \to \mathbf{Set}^D$ is faithful.

*Proof.* Forward direction: if every $(\eta_X)_c$ is monic, then $\eta_X$ is monic in $\mathbf{Set}^C$ by `NatTrans.mono_of_mono_app`; Mathlib's `Adjunction.faithful_L_of_mono_unit_app` gives that $\mathrm{Lan}_F$ is faithful. Converse: a faithful left adjoint implies the unit is monic (Mathlib typeclass instance), and componentwise mono descends from the functor category to each application. $\square$

### Level 2 — InstanceCoreflective

**Definition 5.3 (InstanceCoreflective).** A functor $F : C \to D$ is an *instance coreflective* if the unit of the adjunction $\mathrm{Lan}_F \dashv F^*$ is componentwise an isomorphism:
$$\forall\, X : C \to \mathbf{Set},\; \forall\, c \in C, \quad (\eta_X)_c \text{ is an isomorphism in } \mathbf{Set}.$$

**Theorem 5.4 (InstanceCoreflective implies LanFaithful).** Every instance coreflective functor is Lan-faithful.

*Proof.* An isomorphism is in particular a monomorphism. $\square$

**Theorem 5.5 (Identity and fully faithful functors are InstanceCoreflective).** (i) The identity functor $\mathrm{id}_C$ is an instance coreflective. (ii) Every fully faithful functor $F : C \to D$ is an instance coreflective.

*Proof.* For a fully faithful functor, the unit of $\mathrm{Lan}_F \dashv F^*$ is a natural isomorphism — the standard result that left Kan extension along a fully faithful functor restricts back to the original [4, Ch. X, §3]. In Mathlib: `[Full F] [Faithful F]` implies `IsIso (adj.unit.app X)` for each $X$; the componentwise version is `NatIso.isIso_app_of_isIso`. $\square$

**Theorem 5.5′ (Instance-coreflectivity is fully-faithfulness).** $\mathrm{InstanceCoreflective}(F)$ holds **iff** $F$ is fully faithful. The forward direction passes through the left Kan extension: $\mathrm{InstanceCoreflective}(F) \iff \mathrm{Lan}_F$ is fully faithful (`fullyFaithful_lan_of_instanceCoreflective`), and $\mathrm{Lan}_F$ fully faithful $\iff F$ fully faithful is the **Yoneda bridge** `Functor.fullyFaithfulEquivLanFullyFaithful` (`YonedaBridge.lean`, sorry-free). Thus the recognizable property "the translation $F$ is fully faithful" and the formalization's `InstanceCoreflective` are interchangeable at the instance layer; the schema layer additionally requires the right adjoint $G$ to exist (the open M2 conjecture).

### Level 3 — SchemaCoreflective

**Definition 5.6 (SchemaCoreflective).** Given a functor $F : C \to D$, a functor $G : D \to C$, and an explicit adjunction $\mathrm{adj} : F \dashv G$, we say $(F, G, \mathrm{adj})$ is a *schema coreflective* if the unit
$$\mathrm{adj.unit} : \mathrm{id}_C \Longrightarrow G \circ F$$
is a natural isomorphism, i.e., $\mathrm{IsIso}(\mathrm{adj.unit})$.

In Lean, the property is stated as: given an explicit adjunction $F \dashv G$, the unit of that adjunction is a natural isomorphism.
```lean
def SchemaCoreflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G) : Prop :=
  IsIso adj.unit
```
The adjunction $\mathrm{adj}$ is an *explicit argument*, not resolved by typeclass inference: one must supply a proof that the schema-level right adjoint $G$ exists, rather than have it inferred. This prevents Lean's typeclass mechanism from silently discharging Conjecture 4.8 (M2), which would smuggle a covert `sorry` into any proof invoking it.

**Theorem 5.7.** (i) Every equivalence of categories $e : C \simeq D$ yields a schema coreflective $(e.\mathrm{functor}, e.\mathrm{inverse}, e.\mathrm{toAdjunction})$. (ii) Every fully faithful functor $F : C \to D$ equipped with an explicit adjunction $\mathrm{adj} : F \dashv G$ is a schema coreflective.

*Proof.* (i) For an equivalence, the unit is an isomorphism by construction. (ii) `[Full F] [Faithful F]` implies `IsIso adj.unit` via Mathlib's `Adjunction.unit_isIso_of_L_fully_faithful`. $\square$

### Level 4 — IsCoreflective

**Definition 5.8 (Coreflective).** A functor $F : C \to D$, together with a functor $G : D \to C$, an explicit adjunction $\mathrm{adj} : F \dashv G$, and the pointwise Kan extension hypothesis, is a *coreflective* if
$$\mathrm{Coreflective}(F, \mathrm{adj}) \;\iff\; \mathrm{SchemaCoreflective}(F, \mathrm{adj}) \;\land\; \mathrm{InstanceCoreflective}(F).$$

In Lean, the property is the conjunction of the two preceding levels: schema-level and instance-level units are both natural isomorphisms.
```lean
def IsCoreflective {G : D ⥤ C} (F : C ⥤ D) (adj : F ⊣ G)
    [∀ X : C ⥤ Type v, F.HasPointwiseLeftKanExtension X] : Prop :=
  SchemaCoreflective F adj ∧ InstanceCoreflective F
```
A coreflective functor has *residue zero* on both layers: the schema round-trip $C \xrightarrow{F} D \xrightarrow{G} C$ is an isomorphism at the level of objects, and the instance round-trip $I \mapsto \mathrm{Lan}_F I \mapsto F^*(\mathrm{Lan}_F I)$ is an isomorphism at every record component.

**Theorem 5.9 (Canonical coreflective functors).** (i) $\mathrm{id}_C$ is a coreflective, witnessed by $\mathrm{Adjunction.id}$. (ii) Every equivalence of categories is a coreflective. (iii) Every fully faithful functor with an explicit right adjoint is a coreflective.

*Proof.* Each case reduces to the constituent results at both levels. For (ii), the equivalence functor is fully faithful, giving InstanceCoreflective; and the equivalence gives SchemaCoreflective by Theorem 5.7(i). $\square$

**Remark 5.10.** The four-level hierarchy is designed so that the two instance-level properties (Definitions 5.1 and 5.3) require no hypothesis beyond pointwise Kan extensions existing, while the schema-level and full coreflective properties (Definitions 5.6 and 5.8) require an explicit adjunction. This reflects the epistemic situation: the adjoint triple $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ exists unconditionally (Theorem 4.5), but the schema-level adjunction $\Delta \dashv G$ is the content of the open Conjecture 4.8 (M2).

---

## 6. Independence of the Two Layers: Refutation of M6 Strong

This section proves that schema-level injectivity on objects and faithfulness of $\Delta$ are insufficient to force the instance-level unit $\eta^{\mathrm{ins}}_I$ to be an isomorphism.

**Theorem 6.1 (M6 Strong is false).** *There exist small categories $\mathcal{L}_1$, $\mathcal{L}_2$, a functor $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ that is injective on objects and faithful, and a copresheaf $I \in \mathbf{Set}^{\mathcal{L}_1}$, such that the unit component*
$$\eta^{\mathrm{ins}}_{I, b} : I(b) \;\longrightarrow\; (\Delta^*(\Sigma_\Delta I))(b) = (\Sigma_\Delta I)(\Delta(b))$$
*is not an isomorphism.*

**Proof.** We exhibit a concrete counterexample on four objects (two in each category).

**The categories.** Let $\mathcal{L}_1 = \mathrm{Disc}(\{a, b\})$ be the discrete category on two objects: $\mathrm{Ob}(\mathcal{L}_1) = \{a, b\}$, and the only morphisms are the identities $\mathrm{id}_a$ and $\mathrm{id}_b$. Let $\mathcal{L}_2$ be the category with $\mathrm{Ob}(\mathcal{L}_2) = \{a, b\}$ and morphisms generated by one additional non-identity morphism $f : a \to b$, so $\mathrm{Hom}_{\mathcal{L}_2}(a, a) = \{\mathrm{id}_a\}$, $\mathrm{Hom}_{\mathcal{L}_2}(a, b) = \{f\}$, $\mathrm{Hom}_{\mathcal{L}_2}(b, b) = \{\mathrm{id}_b\}$, and $\mathrm{Hom}_{\mathcal{L}_2}(b, a) = \emptyset$.

**The functor.** Let $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ be the inclusion: $\Delta(a) = a$, $\Delta(b) = b$, $\Delta(\mathrm{id}_a) = \mathrm{id}_a$, $\Delta(\mathrm{id}_b) = \mathrm{id}_b$. $\Delta$ is injective on objects since $\Delta(a) = a \neq b = \Delta(b)$. $\Delta$ is faithful since for any $x, y \in \mathcal{L}_1$, the hom-set $\mathrm{Hom}_{\mathcal{L}_1}(x, y)$ has at most one element, so the map to $\mathrm{Hom}_{\mathcal{L}_2}(\Delta x, \Delta y)$ is vacuously injective.

**The copresheaf.** Let $I : \mathcal{L}_1 \to \mathbf{Set}$ be the constant functor at a one-element set: $I(a) = I(b) = \{*\}$.

**Computing $\Sigma_\Delta I(b)$.** The left Kan extension $\Sigma_\Delta = \mathrm{Lan}_\Delta$ is computed pointwise:
$$\Sigma_\Delta I(b) \;=\; \mathrm{colim}_{\,(c,\, \phi : \Delta(c) \to b)\,\in\, (\Delta \downarrow b)}\; I(c).$$

The objects of $(\Delta \downarrow b)$ are pairs $(c \in \mathcal{L}_1, \phi : \Delta(c) \to b)$:
- $c = a$, $\phi = f \in \mathrm{Hom}_{\mathcal{L}_2}(a, b)$: the object $(a, f)$;
- $c = b$, $\phi = \mathrm{id}_b$: the object $(b, \mathrm{id}_b)$.

A morphism from $(c, \phi)$ to $(c', \phi')$ in $(\Delta \downarrow b)$ is a morphism $g : c \to c'$ in $\mathcal{L}_1$ with $\phi' \circ \Delta(g) = \phi$. Since $\mathcal{L}_1$ is discrete, $g : c \to c'$ forces $c = c'$. No morphism exists between $(a, f)$ and $(b, \mathrm{id}_b)$. The comma category $(\Delta \downarrow b)$ is discrete on $\{(a, f), (b, \mathrm{id}_b)\}$.

The colimit of a discrete two-object diagram is a coproduct:
$$\Sigma_\Delta I(b) \;=\; I(a) \sqcup I(b) \;=\; \{*\} \sqcup \{*\},$$
a two-element set.

**The unit.** The unit component at $b \in \mathcal{L}_1$ is the canonical coprojection
$$\eta^{\mathrm{ins}}_{I,b} : I(b) = \{*\} \;\longrightarrow\; \{*\} \sqcup \{*\} = \Sigma_\Delta I(b),$$
which is injective but not surjective — not an isomorphism. $\square$

**Remark 6.2 (Skolem witness interpretation).** The failure has a transparent cause: the morphism $f : a \to b$ in $\mathcal{L}_2$ lies entirely outside the image of $\Delta$ on morphisms, yet it contributes a genuine object $(a, f)$ to the comma category. The left Kan extension is obligated — by the universal property of the colimit — to introduce a fresh copy of $I(a) = \{*\}$ as a Skolem witness for this unconstrained arrow. The hypotheses of M6 Strong — injectivity on objects and faithfulness — are each purely about what $\Delta$ sends objects and morphisms *to*; they say nothing about morphisms in $\mathcal{L}_2$ that are not in the image of $\Delta$.

**Lean formalization.** The refutation is discharged in [`M6Counter.lean`](../lean-formalization/M6Counter.lean) in full — no gaps, no `sorry`. The proof supplies two distinguishing values to the two summands of $\Sigma_\Delta I(b)$ and uses that distinction to detect that the unit at $b$ cannot be surjective. The top-level declaration is:
```lean
theorem m6_strong_refuted : ¬ M6Strong
```
The mechanism: the diagram whose colimit *is* $\Sigma_\Delta I(b)$ — namely `CostructuredArrow.proj Δ L2Obj.b ⋙ I`, the comma category $(\Delta \downarrow b)$ projected back into $\mathcal{L}_1$ and composed with $I$ — receives a cocone into `Bool` that sends the leg at $(a, f)$ to `true` and the leg at $(b, \mathrm{id}_b)$ to `false`. Assuming `M6Strong` forces the unit at $b$ to be a bijection from `Unit` to $\Sigma_\Delta I(b)$, so surjectivity collapses the two distinct cocone images into one — a contradiction.

---

## 7. Open Problems

> **Status note (post-publication).** Of the three questions below, only **M2** remains open. **M6-restricted (7.3) is now proven** — `M6Restricted.lean` (`m6_restricted`, no `sorry`): under `InstanceReflective F`, the unit `η_X` is iso iff `X` is in the essential image of `F*`, identifying the reflective fragment as that essential image. **M6′ (7.2) has been resolved**: the universal-$I$ monic form is *refuted* by a bicyclic witness, while the ind-fragment form (faithful $\Delta \Rightarrow$ unit monic on $\mathrm{Ind}(\mathcal{L}_1)$) is *proven unconditional*; both are mechanized in the broader DomainSpec project (`Bicyclic.lean`, `M6PrimeOnInd.lean`), not included in this public subset. The conjecture statements below are retained as originally posed.

The refutation of M6 Strong leaves three related questions unresolved.

**Conjecture 7.1 (M2 — Schema-Level Adjunction).** *Let $\mathcal{L}_1$, $\mathcal{L}_2$ be small categories and $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ a functor. For every object $b \in \mathcal{L}_2$, define*
$$P_b \;:=\; \mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b) : \mathcal{L}_1^{\mathrm{op}} \to \mathbf{Set}.$$
*We conjecture that $P_b$ is representable for every $b \in \mathcal{L}_2$: there exists $G(b) \in \mathcal{L}_1$ and a natural isomorphism $\mathrm{Hom}_{\mathcal{L}_2}(\Delta(c), b) \cong \mathrm{Hom}_{\mathcal{L}_1}(c, G(b))$, natural in $c$.*

By the Yoneda lemma, such an assignment $b \mapsto G(b)$ extends uniquely to a functor $G : \mathcal{L}_2 \to \mathcal{L}_1$, and the natural isomorphism constitutes an adjunction $\Delta \dashv G$. Representability is independent of $\Delta$ being full, faithful, or injective on objects: the existence of a representing object turns on whether $\mathcal{L}_1$ contains the limits required to absorb the comma category $(\Delta \downarrow b)$ into a single object — a property of $\mathcal{L}_1$ (and of how $\Delta$ reaches into it), not of how $\Delta$ acts on individual hom-sets. By the adjoint functor theorem, $G$ exists iff each $P_b$ admits a small solution set in $\mathcal{L}_1$; faithfulness of $\Delta$ contributes nothing to this closure condition, and a fully faithful $\Delta$ into a small $\mathcal{L}_2$ whose ambient $\mathcal{L}_1$ lacks the relevant limits fails M2.

**Conjecture 7.2 (M6' — Instance-Level Monomorphism).** *Let $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ be faithful. We conjecture that for every $I \in \mathbf{Set}^{\mathcal{L}_1}$ and every $c \in \mathcal{L}_1$, the unit component $\eta^{\mathrm{ins}}_{I,c}$ is a monomorphism in $\mathbf{Set}$.*

On representables, the equivalence is immediate: for $I = \mathrm{Hom}_{\mathcal{L}_1}(c', -)$, the unit at $c$ unfolds to $\Delta_{c',c} : \mathrm{Hom}_{\mathcal{L}_1}(c', c) \to \mathrm{Hom}_{\mathcal{L}_2}(\Delta c', \Delta c)$, $h \mapsto \Delta h$, which is injective iff $\Delta$ is faithful — essentially the definition.

The real difficulty lies in the lift from representables to arbitrary $I$. Every $I \in \mathbf{Set}^{\mathcal{L}_1}$ is a colimit of representables, $\Sigma_\Delta = \mathrm{Lan}_\Delta$ preserves colimits as a left adjoint, and $\Delta^*$ preserves both limits and colimits, so $\eta^{\mathrm{ins}}_I$ is the colimit of the representable units $\eta^{\mathrm{ins}}_{\mathrm{y}(c_i)}$ in $\mathbf{Set}^{\mathcal{L}_1}$. Pointwise monomorphisms in $\mathbf{Set}$ are preserved by *filtered* colimits, but not by arbitrary ones: a coproduct of two monos can fail to be mono if the components share targets, and pushouts can collapse distinct preimages. Whether faithfulness of $\Delta$ alone — possibly under structural hypotheses on $\mathcal{L}_1$ that constrain which colimit shapes appear in the representable presentation of $I$ — suffices to keep the lifted unit pointwise monic is the open content of M6'.

**Conjecture 7.3 (M6-restricted — Coherence on a Reflective Fragment).** *Let $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ be injective on objects and faithful. We conjecture that there exists a nontrivial reflective subcategory $\mathcal{S} \hookrightarrow \mathbf{Set}^{\mathcal{L}_1}$ such that for every $I \in \mathcal{S}$ and every $c \in \mathcal{L}_1$, $\eta^{\mathrm{ins}}_{I,c}$ is an isomorphism.*

Plausible candidates for $\mathcal{S}$: the full subcategory generated by representables under finite colimits; or copresheaves satisfying all path equations of $\mathcal{L}_1$. The counterexample in Theorem 6.1 does not obstruct this conjecture: the counterexample uses $\mathcal{L}_1$ discrete, which imposes no path equations whatsoever, leaving nothing for a restriction to $\mathcal{L}_1$'s equations to enforce.

---

## 8. Conclusion

Two layers, two conservation laws, two budgets — never one. The adjoint triple $\Sigma_\Delta \dashv \Delta^* \dashv \Pi_\Delta$ exists unconditionally for any functor $\Delta : \mathcal{L}_1 \to \mathcal{L}_2$ between small categories, giving the instance residue unit $\eta^{\mathrm{ins}}_I$ for free. The claim M6 Strong — that injectivity on objects and faithfulness of $\Delta$ together force $\eta^{\mathrm{ins}}_I$ to be an isomorphism — is false, refuted by a four-object counterexample formalized in Lean 4 with no `sorry`. The coreflective hierarchy is two-dimensional rather than a single chain: an instance-axis progression $\mathrm{LanFaithful} \subseteq \mathrm{InstanceCoreflective}$, an orthogonal schema-axis condition $\mathrm{SchemaCoreflective}$, and the conjunction $\mathrm{Coreflective} = \mathrm{SchemaCoreflective} \land \mathrm{InstanceCoreflective}$ at the top. It provides a graduated classification of how completely the instance and schema residues vanish, with characterization theorems proved at each level. The explicit-adjunction design of $\mathrm{SchemaCoreflective}$ and $\mathrm{Coreflective}$ enforces that the open conjecture M2 is never silently assumed.

Three problems remain open. M2 asks whether $\mathrm{Hom}_{\mathcal{L}_2}(\Delta(-), b)$ is representable for every $b \in \mathcal{L}_2$ — the condition under which the schema-level right adjoint $G$ and the unit $\eta^{\mathrm{sch}}$ exist. M6' asks whether faithfulness of $\Delta$ alone implies that $\eta^{\mathrm{ins}}_I$ is pointwise monic for all $I$, beyond the representable case where the result is immediate. M6-restricted asks for a nontrivial reflective subcategory $\mathcal{S} \hookrightarrow \mathbf{Set}^{\mathcal{L}_1}$ on which injectivity and faithfulness do force $\eta^{\mathrm{ins}}_I$ to be an isomorphism, with copresheaves generated by finite colimits of representables as the natural candidate. Each of these problems has a concrete formulation ready for either a proof or a further counterexample.

The broader significance of this work is the irreducibility of the two residue layers. No condition on $\Delta$ that concerns only how it maps objects and morphisms can simultaneously control both what $\mathcal{L}_2$ does not see of the $\mathcal{L}_1$ type structure (the schema residue) and what the round-trip $I \mapsto \Sigma_\Delta I \mapsto \Delta^*(\Sigma_\Delta I)$ fails to recover of the populated data (the instance residue). The audit of a compilation contract is permanently double.

---

## Coda — Two Symmetries, Two Conservations

Noether's theorem [9] established the governing principle of modern mechanics: every continuous symmetry of an action functional corresponds to a conserved quantity, and conservation is the shadow of an invariance the equations already obey. The setting here is discrete and categorical rather than variational, so the analogy is structural rather than literal — there is no Lagrangian, no Lie group, no integration by parts. What transfers is the form of the correspondence: where there is symmetry, there is conservation; where two symmetries act on the same object, there are two conservations to account for separately.

DomainSpec inhabits a discrete universe, and the move transfers. The compilation functor $\Delta$ admits two symmetries — one at the schema level, where representability (M2) would yield a right adjoint $G$ and the conserved quantity $\eta^{\mathrm{sch}}$; one at the instance level, where the Kan-extension triple yields $\eta^{\mathrm{ins}}_I$ unconditionally. Two conservations, two residues, two budgets. The natural hope was that one would buy the other: that injectivity and faithfulness, sufficient for the schema-level symmetry to be tight, would propagate to the instance level. M6 Strong is precisely that hope, made formal as a conjecture.

**M6 Strong fails.** Four objects suffice to refute it (Theorem 6.1, formalized in `M6Counter.lean` with no `sorry`). The two laws do not collapse, and no purely schema-level discipline on $\Delta$ can recover the instance-level conservation.

The four registers are read through the same lens. In **simulation**, the state space caps the world the model can hold; the dynamics cap the populated trajectory the observer can reconstruct. In **categorization**, the label set caps the types in play; the intra-class variation caps what each instance contributes. In **knowledge transfer**, the teaching structure caps what can be articulated; what each student receives caps what is conserved across the channel. In **software compilation**, the type system caps the contract; the data migration caps the round-trip. In each register, two leaks, two budgets, never one.

A coreflective is the limiting case where both residues vanish — schema round-trip exact, instance round-trip exact, $\eta^{\mathrm{sch}}$ and $\eta^{\mathrm{ins}}$ both natural isomorphisms (Definition 5.8). Everything else has positive residue on at least one of the two layers, and which one matters depends on what is being audited. The open conjectures M2, M6', and M6-restricted mark the live frontier of the framework: the points at which formal reasoning hands off to either further proof or calibrated empirical practice.

The instinct to ask whether the two laws reduce is older than the formalization. We give it a name and an answer.

---

## See also

- [DomainSpec Two-Layer Framework](./domainspec-two-layer-framework.md) — The philosophical and system framing: the four-register motivation (simulation, categorization, knowledge transfer, compilation) and the long-form exposition of the two-layer residue.
- [Lean Formalization Guide](./lean-formalization-guide.md) — The Lean-side companion: file-by-file walkthrough of the formalization, status of each result, and the proof-obligation map.
- [Glossary](../GLOSSARY.md) — Definitions of all terms, milestone labels (M-numbers, T-numbers), and literature mapping.
- [CoreflectiveHierarchy.lean](../lean-formalization/CoreflectiveHierarchy.lean) — The proven kernel: definition of coreflective functor, the faithfulness characterization, identity and fully faithful cases.
- [CoreflectiveHierarchy.lean](../lean-formalization/CoreflectiveHierarchy.lean) — The four-level hierarchy: $\mathrm{LanFaithful}$, $\mathrm{InstanceCoreflective}$, $\mathrm{SchemaCoreflective}$, $\mathrm{Coreflective}$ as defined in §5.
- [S3Coreflective.lean](../lean-formalization/S3Coreflective.lean) — Defines `S2UnitCoreflective` (unit of $\mathrm{Lan}_F \dashv F^*$ is iso) and `S3UnitCoreflective` (unit of $F^* \dashv \mathrm{Ran}_F$ is iso) — the two canonical unit-iso conditions corresponding to the two symmetries of this paper.
- [S2VsS3Counter.lean](../lean-formalization/S2VsS3Counter.lean) — Proves `s2_and_s3_decoupled`: a single functor satisfies S2 but fails S3, formalizing the two-layer independence claim of §6 at the level of the canonical adjunctions.
- [M6Counter.lean](../lean-formalization/M6Counter.lean) — The four-object counterexample formalizing the refutation of M6 Strong (§6).
- [M2Counter.lean](../lean-formalization/M2Counter.lean) — Reuses the four-object setup to refute the unrestricted form of Conjecture 4.8 (M2): theorem `M2_unrestricted_false` (§4).
- [DomainSpec.lean](../lean-formalization/DomainSpec.lean) — The full two-layer residue framework, including the open conjectures M2, M6', and M6-restricted (§7).

---

## References

[1] Spivak, D.I. "Functorial Data Migration." *Information and Computation* 217 (2012): 31–51.

[2] Spivak, D.I., and Wisnesky, R. "Relational Foundations for Functorial Data Migration." *DBPL* 2015.

[3] Imieliński, T., and Lipski, W. "Incomplete Information in Relational Databases." *JACM* 31.4 (1984): 761–791.

[4] Mac Lane, S. *Categories for the Working Mathematician*. GTM 5, Springer, 2nd ed., 1998.

[5] Riehl, E. *Category Theory in Context*. Dover, 2016.

[6] Awodey, S. *Category Theory*. Oxford Logic Guides 52, OUP, 2nd ed., 2010.

[7] de Moura, L., and Ullrich, S. "The Lean 4 Theorem Prover and Programming Language." *CADE* 2021.

[8] The Mathlib Community. "The Lean Mathematical Library." *CPP* 2020.

[9] Noether, E. "Invariante Variationsprobleme." *Nachrichten GWG* (1918): 235–257.

[10] Schultz, P., Spivak, D.I., Vasilakopoulou, C., and Wisnesky, R. "Algebraic Databases." *Theory and Applications of Categories* 32.16 (2017): 547–619. arXiv:1602.03501.
