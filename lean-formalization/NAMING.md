# Naming — Project Terms ↔ Standard Mathematical Terms

This file is the single source of truth for the mapping between the
project's coreflective / reflective vocabulary and standard
category-theory / Mathlib terminology.

**The names now align with the standard terms.** Earlier versions of this
project called these conditions "fractal" / "cofractal" — a metaphor, not a
mathematical term. They have been renamed to the conditions they actually
denote: a translation that is recovered *without loss* by its Kan extension
is exactly a **(co)reflective** situation. The project's contribution is the
*taxonomy* — which adjunction, which side (unit/counit), which layer
(schema/instance) a fully-faithfulness condition lives on — and its
application to compilation residue, not the individual definitions. Every
project name in this file is provably equivalent to a classical Mathlib
concept; the equivalence lemmas live in the corresponding `.lean` file.

## Coreflective vs. reflective — which side is which

Both conditions are about the canonical adjunction `Lan_F ⊣ F*` between the
presheaf categories `(C ⥤ Type v)` and `(D ⥤ Type v)` being loss-free, in
the two dual senses:

- **Coreflective** (unit side): the **unit** is iso ⇔ the **left** adjoint
  `Lan_F` is fully faithful. Captured by `InstanceCoreflective`,
  `SchemaCoreflective`, `IsCoreflective`.
- **Reflective** (counit side): the **counit** is iso ⇔ the **right** adjoint
  `F*` (precomposition) is fully faithful. Captured by `InstanceReflective`,
  `SchemaReflective`, `IsReflective`.

This matches Mathlib's own convention: `CategoryTheory.Reflective` is a fully
faithful **right** adjoint (the counit-iso side). The `Is`-prefix
(`IsCoreflective`, `IsReflective`) is used precisely to avoid a name clash
with that existing class while keeping the standard reading.

## Unit side — coreflective (`Lan_F ⊣ F*`, unit iso)

| Project name | Standard / Mathlib name | Equivalence lemma | File |
|---|---|---|---|
| `LanFaithful F` | `F.lan : Psh(C) → Psh(D)` is faithful | `lanFaithful_iff_lan_faithful` | `CoreflectiveHierarchy.lean` |
| `InstanceCoreflective F` | `F.lan.FullyFaithful` (componentwise unit iso on `Psh(C) → Psh(D)`) | `fullyFaithful_lan_of_instanceCoreflective` (forward); `instanceCoreflective_of_fullyFaithful` (backward, from `F.FullyFaithful`) | `CoreflectiveHierarchy.lean` |
| `SchemaCoreflective F adj` | `IsIso adj.unit` (definitionally); when `F` is FF this also gives `F.FullyFaithful` via `adj` | `schemaCoreflective_of_fullyFaithful` | `CoreflectiveHierarchy.lean` |
| `IsCoreflective F adj` | `SchemaCoreflective ∧ InstanceCoreflective` | — | `CoreflectiveHierarchy.lean` |
| `S2UnitCoreflective F` | `F.lan.FullyFaithful` (whole-nat-trans form of `InstanceCoreflective`) | `fullyFaithful_lan_of_s2UnitCoreflective` | `S3Coreflective.lean` |

**Mathlib references for the underlying equivalences:**
- Forward (FF ⇒ unit iso): `Adjunction.unit_isIso_of_L_fully_faithful`
- Backward (unit iso ⇒ FF): `Adjunction.fullyFaithfulLOfIsIsoUnit`
- L faithful ⇔ unit componentwise mono:
  `Adjunction.faithful_L_of_mono_unit_app`,
  `Adjunction.unit_mono_of_L_faithful`

**Technical note.** The clean Mathlib equivalence is between unit-iso and
*the left adjoint* being fully faithful. For `F.lanAdjunction _`, the left
adjoint is `F.lan`, not `F`. So `InstanceCoreflective F ⇔ F.lan.FullyFaithful`
directly. The further equivalence `F.FullyFaithful ⇔ F.lan.FullyFaithful` —
which lets one phrase the condition on `F` itself — is proved in
`YonedaBridge.lean` as `Functor.fullyFaithfulEquivLanFullyFaithful`
(sorry-free, Mathlib-only). Chaining the two gives
`InstanceCoreflective F ⇔ F.FullyFaithful`.

## Counit side — reflective (`Lan_F ⊣ F*`, counit iso)

| Project name | Standard / Mathlib name | Equivalence lemma | File |
|---|---|---|---|
| `InstanceReflective F` | `((whiskeringLeft _ _ _).obj F).FullyFaithful` (the precomposition functor `F*` is fully faithful) | `fullyFaithful_pullback_of_instanceReflective` (forward); `instanceReflective_of_pullback_fullyFaithful` (backward) | `ReflectiveHierarchy.lean` |
| `SchemaReflective F adj` | `IsIso adj.counit` (definitionally); equivalently the right adjoint `G` is fully faithful | `schemaReflective_of_R_fullyFaithful` | `ReflectiveHierarchy.lean` |
| `IsReflective F adj` | `SchemaReflective ∧ InstanceReflective` | — | `ReflectiveHierarchy.lean` |

**Mathlib references:**
- Forward (R FF ⇒ counit iso): `Adjunction.counit_isIso_of_R_fully_faithful`
- Backward (counit iso ⇒ R FF): `Adjunction.fullyFaithfulROfIsIsoCounit`

**Note on "dense."** When `F` is *full*, `((whiskeringLeft _ _ _).obj F).FullyFaithful`
is equivalent to `F.IsDense` in Mathlib's sense (see
`Mathlib.CategoryTheory.Functor.KanExtension.Dense`). The unconditional
project-level name is "F* fully faithful," which is what
`InstanceReflective` captures.

## Ran side (`F* ⊣ Ran_F` adjunction)

| Project name | Standard / Mathlib name | Equivalence lemma | File |
|---|---|---|---|
| `S3UnitCoreflective F` | `IsIso (F.ranAdjunction _).unit` — no clean classical name | — | `S3Coreflective.lean` |

`S3UnitCoreflective` does not reduce to a textbook fully-faithfulness
condition on `F` itself in Mathlib's current API. The
`S2VsS3Counter.lean` witness shows it can fail while `S2UnitCoreflective`
holds; the converse is also possible. We therefore keep the name
without a one-line classical translation.

## Symbols and labels (application vs. generic math)

| Context | Use |
|---|---|
| Generic functor in `CoreflectiveHierarchy.lean`, `ReflectiveHierarchy.lean`, `S3Coreflective.lean`, counterexamples | `F : C ⥤ D` |
| The compilation functor in `DomainSpec.lean` and prose | `Δ : L₁ ⥤ L₂` (Spivak-style — collides with diagonal but is the application's standard notation) |

## Conjecture / milestone codes

`M2`, `M4`, `M5`, `M6` are internal milestone labels used in the
project's documentation. Their mathematical content:

| Code | Mathematical statement |
|---|---|
| **M2** (unrestricted) | "For every `F : C ⥤ D` and every `b : D`, `Hom_D(F-, b)` is representable" — equivalently, "`F` has a pointwise right adjoint." Refuted by `M2Counter.lean`. |
| **M2-restricted** | Open: which hypothesis on `F` makes `F` have a right adjoint in the data-migration setting? (Adjoint Functor Theorem territory.) |
| **M4** | The schema-level adjunction whose unit can fail by representability collapse (see `DomainSpec.lean`, `schemaResidueZero_forces_FF`). |
| **M5** | The instance-level triple `Σ_F ⊣ F* ⊣ Π_F` = `Functor.lanAdjunction` + `Functor.ranAdjunction`. |
| **M6** (strong) | "`F` injective on objects + faithful ⇒ unit of `Lan_F ⊣ F*` componentwise iso (i.e., `F` fully faithful at instance layer)." Refuted by `M6Counter.lean`. |
| **M6′** | "`F` faithful ⇒ `Lan_F` faithful" (unit componentwise mono for every `X`). **Refuted** for universal `X` (bicyclic witness); **proven** on the ind-fragment `Ind(L₁)` under `[F.Faithful]`. Mechanized in the broader DomainSpec project (`Bicyclic.lean`, `M6PrimeOnInd.lean`), not in this public subset. |
| **M6-restricted** | Under `[InstanceReflective F]` (i.e. `F*` fully faithful), `IsIso (η_X) ↔ X ∈ F*`-essential-image. **Proven** (no `sorry`) in `M6Restricted.lean` (`m6_restricted`), via Mathlib's `Adjunction.isIso_unit_app_iff_mem_essImage`. |

## Brand vs. math

The "fractal" motif survives only as **branding** for the visualization
(`visualization/fractals.html`) and the intuitive "whole-recoverable-from-part,
residue-zero" framing in the README. Inside the math files, the paper, and any
formal writeup, the conditions are named for what they are — coreflective /
reflective — and cited with their equivalence lemma.
