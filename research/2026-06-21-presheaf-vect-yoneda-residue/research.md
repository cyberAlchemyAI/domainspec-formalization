# Research dispatch 2026-06-21 — presheaf-in-Vect / Yoneda / residue formalization

Lane A. Three explorer returns, collected verbatim. Synthesis lives in `findings.md`.

---

## Explorer Return 1 — Spivak (precedent-in-repo)

Status classification: (a) presheaf-in-Vect = build-from-owned, cited to domainspec-lean-formalization/research/A2-noether/waves/phase-3-redteam/r2-t0-noether.md:132 ("framework proves the envelope but does not equip L1,L2 with Markov-target enrichment"); diagnosis: latent enrichment is a PLANNED sequel, not deployed. (b) Yoneda-incompleteness as hallucination = already-deployed, cited M2Counter.lean:54 (M2_unrestricted_false, no sorry) + paper.md:40 (Def 4.8). (c) schema⊥instance orthogonality = already-deployed, cited M6Counter.lean:125 (m6_strong_refuted) + S2VsS3Counter.lean:158 (s2_and_s3_decoupled). (d) geometric-orthogonality second sense = precedent-clean (not owned by Set chassis), cited domainspec-lean-formalization/docs/reflection-tower-framework.md:314-331.

Placement table: M2 refuted -> M2Counter.lean:54 / paper.md §4.8 (proven); M6 Strong refuted -> M6Counter.lean:125 / paper.md §6.1 (proven); schema-instance independence -> S2VsS3Counter.lean:158 / paper.md Coda (proven); coreflective hierarchy 4 levels -> CoreflectiveHierarchy.lean:1-255 / paper.md §5 (proven); instance residue free -> DomainSpec.lean:105-147 / paper.md §4.5 (proven via Kan); schema residue conditional -> DomainSpec.lean:323-390 / paper.md §4.7 (conjectural, M2-dependent); latent Markov enrichment -> NOT in Lean, reflection-tower-framework.md:314 (open sequel).

presheaf-in-Vect: NEITHER extension nor restatement in-repo — it is BLOCKED. Set-valued presheaves (C ⥤ Type v) are formalized & unconditional (the Σ⊣Δ*⊣Π triple is free via Kan). Vect-valued would be a genuine generalization needing monoidal Kan reproof; currently the framework proves only the envelope (T0'_C3) not the enrichment. Collapse-test evidence: domainspec-lean-formalization/lean-formalization/TannakianDiagnosis.lean:58-65 (fiber functor into Discrete has trivial endo-nat-transformations → discrete-target precludes enrichment semantics; enrichment must live on presheaf VALUES, making it a genuine orthogonal axis).

KEYSTONE: Set-valued formalization owns the two-layer residue structure via the free adjoint triple, both layers independently refuted (M6 Strong) and independently checkable (coreflective hierarchy); presheaf-in-Vect is latent — present in T0'_C3's envelope but not yet formalized as data or theorem. COLLAPSE: a non-sorry Lean proof that Vect^L1 admits the same adjoint triple without Set-valued arguments would make it owned.

---

## Explorer Return 2 — Bénabou (enriched-CT)

(1) Presheaf codomain Set→V: OWNER = Kelly (1982) "Basic Concepts of Enriched Category Theory" Ch.4-5 (V-presheaves [C^op,V], density, enriched Yoneda, Kan extensions). Secondary: Loregian Coend Calculus (2021); Adámek–Rosický. Codebase cites Kelly Ch.5 at GLOSSARY.md:102 and paper-v2.md (density). Label: already-deployed / build-from-owned. The codomain shift is architecturally ROUTINE, not frontier.

(2) "Second sense of orthogonal": two categorical homes — (2a) factorization-system orthogonality (Freyd–Kelly 1972, LNM 76): formal perpendicularity via unique diagonal fill; (2b) enriched orthogonality (Kelly §5.5): hom-object [F,G] terminal in V. Your framework uses "orthogonal" in 2 senses: axis-orthogonality (schema⊥instance) = lattice/poset-theoretic, NOT categorical; perpendicular-embeddings-as-semantic-independence = rhymes with factorization-system orthogonality but is metaphorical, not owned by a single theorem. Label: precedent-clean (formal notion owned by factorization systems; the semantic-independence reading is metaphor).

(3) Enriched Yoneda still incomplete: YES — y_V: C → [C^op,V] is enriched-fully-faithful but NOT essentially surjective; non-representable V-presheaves always exist (Kelly §5.1, absolute density as the intermediate condition). M2-style non-representability transfers DIRECTLY: the four-object counterexample (L1=Discrete(Fin 2), L2={a,b,f}, Δ inclusion) still yields a non-representable presheaf with V=Vect. Incompleteness persists at every base V. Label: already-deployed (Kelly) for Set; M2-restricted remains open for both Set and Vect.

KEYSTONE: codomain replacement Set→V is routine within Kelly; the conceptual load is the M2-restricted restriction question (which restrictions on Δ recover representability), and the M2-strong refutation holds at EVERY base V, not just Set. COLLAPSE: a published M2-restricted theorem (a restriction class R with ∀Δ∈R representability) demotes "open" to "answered".

---

## Explorer Return 3 — Baez (categorical-ML)

(1) "non-representable presheaf = hallucination locus": build-from-owned + partially metaphorical. Framework OWNS hallucination=untracked residue (BACKLOG.md H-8 "hallucination as untracked residue — typing, not minimization"); two-layer audit maps concept-erasure→faithfulness of Δ, data-hallucination→monoicity of Lan-unit η_I: I⇒Δ*Σ_Δ(I); noise-signal-schema-manifesto.md §3.6 "hallucination is partially schema-relative". The exact presheaf/representability framing is NOT yet owned but structurally present. Verdict: precedent-clean for the exact framing, build-from-owned for the residue identification.

(2) functor-into-Vect tied to faithfulness/representability detecting fabrication: precedent-clean (NONE found). categorical-deep-learning (Cruttwell/Gavranović/Shiebler) flagged "not searched" in L2-synthesis.md; DisCoCat only a vocabulary marker; profunctor/optics view of embeddings absent. Genuine literature gap.

(3) checkable "real vs fabricated" via representability: build-from-owned (conditional). Owned & checkable: M6-restricted (F11.lean schema_instance_decoupling_threshold — full faithfulness ⇒ η_X iso on essential image); Bicyclic.lean lanUnit_app_not_mono_bicyclic (faithful but η_X not monic — faithfulness insufficient); persistence lemma ReflectionTower.lean (no finite schema kills all residue). Test pathway (not yet formalized): IsRepresentable((Δ.op ⋙ yoneda.obj I)) — representable ⇒ instances ground to one c:L1; non-representable ⇒ concept hallucination.

KEYSTONE: the formal locus of hallucinated structure = instances surviving Δ and Σ_Δ whose witness cannot be traced to any single L1 object, i.e. non-representable in L1's hom-structure. COLLAPSE: exhibit a populated I where Σ_Δ(I) hallucinates an element that IS representable by a single c:L1 — would falsify; current evidence (M6Counter, Bicyclic) suggests none exists but no proof yet.
