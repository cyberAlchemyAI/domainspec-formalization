# Findings — presheaf-in-Vect / Yoneda-incompleteness / residue formalization (lane A)

Dispatch 2026-06-21. Synthesizer: Loregian, Fosco (n=1). Sources: the three explorer
returns in `research.md` (cited as R1 Spivak, R2 Bénabou, R3 Baez) plus path:line
verifications noted below. Rule applied: **claim ≤ proof** — a verdict never exceeds
what its cited witness establishes. OWNED ⇒ GO (build-from-owned); only **no witness**
or **tautological collapse** is a KILL.

Sibling-repo citations (`domainspec-lean-formalization/…`) are **agent-reported**.
Where I could locally confirm existence/shape they are tagged **verified ✓**; the exact
line numbers inside those files remain trust-but-verify (see Residue).

---

## Verdict matrix

| candidate | owner / precedent | witnessed? | sound? | verdict | use-mode |
|---|---|---|---|---|---|
| **(a) presheaf-in-Vect** | **Owned externally by Kelly 1982** (*Basic Concepts of Enriched Cat. Th.* Ch.4-5, cited `GLOSSARY.md:102`, R2); Set version **proven** in-repo (`DomainSpec.lean:105-147`, paper §4.5, R1) | Set: YES (proven, no sorry). Vect: **NO in-repo Lean witness** (Popper non-vacuity gate); envelope `T0'_C3` only; `reflection-tower-framework.md:314` flags open sequel (R1) | Set: yes. Vect: owned in literature, **un-discharged in Lean** — needs monoidal Kan reproof (R1) | **GO** | **build-from-owned** — owned ⇒ GO (Kelly owns the V-valued path; Set chassis proven). Residue = **deployment gap**, not conceptual gap (see below) |
| **(b) Yoneda-incompleteness-as-hallucination** | M2 non-representability owned, `M2Counter.lean:54` (`M2_unrestricted_false`, no sorry) + paper §4.8 (R1); enriched form owned by Kelly §5.1, transfers to V=Vect (R2) | YES — proven counterexample at V=Set; R2 shows the 4-object counterexample stays non-representable at every base V | yes (non-rep persists at every V) | **GO (sharpened)** | **already-deployed** (incompleteness theorem), **sharpened by Quine**: non-representable presheaf is a *categorical existential* strictly sharper than the instance-residue footprint (non-rep ⇒ residue-failure, one-way); cementing test `IsRepresentable(Δ.op ⋙ yoneda.obj I)` = BACKLOG H-8 |
| **(c) schema–instance independence (lattice-theoretic decoupling)** | `M6Counter.lean:125` (`m6_strong_refuted`) + `S2VsS3Counter.lean:158` (`s2_and_s3_decoupled`) + paper Coda (R1) | YES — both layers independently refuted, independently checkable via coreflective hierarchy (R1) | yes — independence is **poset/lattice decoupling**, NOT categorical factorization-system orthogonality (R2 Bénabou + Quine) | **GO (renamed)** | **already-deployed** |
| **(d) geometric-orthogonality second sense** | **Owned externally**: factorization-system orthogonality (Freyd–Kelly 1972, LNM 76) / enriched orthogonality (Kelly §5.5) (R2); not owned by Set chassis, `reflection-tower-framework.md:314-331` (R1) | formal notion witnessed in literature (Freyd–Kelly); **perpendicular-embeddings-as-semantic-independence reading in-framework is metaphor**, no single theorem (R2) | formal sense: sound (external). framework's perpendicular-embedding reading: metaphorical, unproved | **GO — demote-to-metaphor** | **build-from-owned** for the formal factorization-system notion (Freyd–Kelly/Kelly §5.5); the framework's perpendicular-embeddings reading stays **metaphor**, not a theorem. **Not a KILL** |

No row is a KILL. **OWNED IS NOT A KILL** — every candidate has either a deployed
proof, an owned external precedent, or an owned residue structure to build from.
On (a), Popper's non-vacuity gate returned a "no-witness KILL" against
Lakatos/Quine's GO; the conflict resolves to **GO/build-from-owned** because the
V-valued triple is owned externally by Kelly 1982 and the Set version is proven
in-repo — Popper's finding is recorded as the *residue* (a deployment gap), not as
a verdict (Residue §1). (d)'s framework reading is **demoted to metaphor**, not
killed — the formal notion it gestures at is owned (Freyd–Kelly).

---

## Where it sits in the formalization

Per R1's placement table (Set-valued, all `domainspec-lean-formalization/lean-formalization/…` + `paper.md`):

- **(b) M2 refuted** → `M2Counter.lean:54` / paper §4.8 — *proven*.
- **(c) M6 Strong refuted** → `M6Counter.lean:125` / paper §6.1 — *proven*.
- **(c) schema–instance independence** → `S2VsS3Counter.lean:158` / paper Coda — *proven*.
- **coreflective hierarchy (4 levels)** → `CoreflectiveHierarchy.lean:1-255` / paper §5 — *proven* (independent-checkability witness for (c)).
- **instance residue free** → `DomainSpec.lean:105-147` / paper §4.5 — *proven via Kan* (the Set chassis under (a)).
- **schema residue conditional** → `DomainSpec.lean:323-390` / paper §4.7 — *conjectural, M2-dependent*.
- **(a) latent Markov/Vect enrichment** → **NOT in Lean**; `reflection-tower-framework.md:314` — open sequel. New home for (a) would be a `…VEnriched` module re-proving the Σ⊣Δ*⊣Π triple over a monoidal V (cf. sibling `AsymmetricTowerVEnriched.lean`, agent-reported ✓-exists; see Residue).
- **(b)/(c) hallucination-as-residue typing** → `BACKLOG.md` H-8 (R3), verified ✓ at `BACKLOG.md:361,367,383`; the **cementing step** for (b) is to formalize the representability test `IsRepresentable((Δ.op ⋙ yoneda.obj I))` (**BACKLOG H-8**) — currently **not yet formalized** (R3) — destined for the same instance-residue module as §4.5.
- **(d) formal orthogonality** → external (Freyd–Kelly / Kelly §5.5); in-framework usage is descriptive prose, no module owns it.

---

## Residue (unresolved)

1. **(a) Vect step is blocked, not done — deployment gap, not conceptual gap.**
   Popper's non-vacuity gate (residue, recorded precisely): *"no in-repo Lean witness —
   Σ_Δ ⊣ Δ* ⊣ Π_Δ in [L1, Vect] is un-discharged; blocked deployment gap, not a
   conceptual gap."* This is the residue, NOT a KILL: the triple is owned externally by
   Kelly 1982 and the Set version is proven (`DomainSpec.lean:105-147`), so per OWNED ⇒ GO
   the verdict is build-from-owned (see post-matrix note resolving Popper KILL vs
   Lakatos/Quine GO). R1 and R2 disagree only on difficulty: R2 calls the Set→V codomain
   shift "architecturally routine" (within Kelly); R1 calls it "BLOCKED … needs monoidal
   Kan reproof." Reconciliation: *routine in the literature, un-discharged in Lean.*
   Collapse condition (R1): a non-sorry Lean proof that `Vect^L1` admits the same adjoint
   triple without Set-valued arguments flips (a) to already-deployed.

2. **M2-restricted is open at every base V** (R2). Open question: a restriction class
   R on Δ with ∀Δ∈R representability. A published such theorem demotes (b)'s "open part"
   to answered (R2 collapse condition).

3. **Literature gap (R3 item 2):** functor-into-Vect tied to faithfulness/representability
   for fabrication-detection has **no precedent found**. `categorical-deep-learning`
   (Cruttwell/Gavranović/Shiebler) was flagged "not searched" in `L2-synthesis.md` — a
   genuine unsearched branch, not a confirmed absence. Sweep before any "novel" claim.

4. **Two senses of "orthogonal" remain lexically conflated** (R2 Bénabou + Quine):
   poset/lattice independence (c, now renamed **schema–instance independence
   (lattice-theoretic decoupling)** throughout) vs. categorical factorization-system /
   enriched orthogonality (d). NOTE: "orthogonal" in (c) means **poset/lattice
   independence, NOT categorical factorization-system orthogonality**. The framework
   should disambiguate in prose; a definitions-governance item, not a math gap.

5. **SIBLING-REPO CROSS-CHECK (agent-reported, needs trust-but-verify).**
   `domainspec-lean-formalization` holds material that overlaps lane A and MUST be
   reconciled before (a)/(b)/(c) are treated as settled:
   - `lean-formalization/F11.lean` — `schema_instance_decoupling_threshold` (R3; verified ✓ file+theorem exist, `F11.lean:64,317`). Bears on (c).
   - `lean-formalization/Bicyclic.lean` — `lanUnit_app_not_mono_bicyclic` (R3; verified ✓, `Bicyclic.lean:62,446`): faithful but η_X not monic ⇒ faithfulness insufficient for grounding. Bears on (b) hallucination locus.
   - `lean-formalization/TannakianDiagnosis.lean` — discrete-target ⇒ trivial endo-nat-transformations (R1; verified ✓, `TannakianDiagnosis.lean:55-66` core theorem present). R1's collapse-evidence that enrichment must live on presheaf VALUES (bears on (a)).
   - `lean-formalization/AsymmetricTowerVEnriched.lean` — V-enriched asymmetric tower (verified ✓ file exists). Direct prior art for (a); **must be read before re-proving the Vect triple** — (a) may be closer to already-deployed than R1's Set-only view suggests.
   - `BACKLOG.md` H-8 — hallucination-as-untracked-residue typing (R3; verified ✓, `BACKLOG.md:361`). Bears on (b)/(c).
   File existence and theorem-name presence are locally confirmed; exact line numbers
   and proof completeness (no-sorry status) inside the sibling repo are **not** re-verified
   here and remain trust-but-verify.

---

## One-line answer to the dispatch goal

**No KILLs.** (a) presheaf-in-Vect is **GO/build-from-owned** — owned externally by Kelly 1982, Set version proven, with a **deployment-gap residue** (no in-repo Lean witness for Σ_Δ⊣Δ*⊣Π_Δ in [L1,Vect]; Popper's "no-witness" recorded as residue, not verdict, resolving against Lakatos/Quine GO). (b) Yoneda-incompleteness is **GO, sharpened** by Quine (non-representable presheaf = categorical existential strictly sharper than instance residue; cement via `IsRepresentable(Δ.op ⋙ yoneda.obj I)`, BACKLOG H-8). (c) is **GO, renamed** to schema–instance independence (lattice-theoretic decoupling; already-deployed at `M6Counter.lean:125`, `S2VsS3Counter.lean:158`). (d) is **GO — formal notion build-from-owned (Freyd–Kelly/Kelly §5.5), perpendicular-embeddings reading demoted to metaphor**. A mandatory trust-but-verify cross-check against sibling `domainspec-lean-formalization` modules (esp. `AsymmetricTowerVEnriched.lean`) precedes any from-scratch rebuild of (a).
