# _explorer/

The visualization. **Not** a microscope — the canonical reading interface.

GitHub's file browser is designed for trees. This repository is a fractal. The file browser is the substrate; this directory is the lens.

## Status

Placeholder. The explorer is part of v0.1 and is not yet implemented. Until it ships, the file browser and the validator output are the only ways to read the structure.

## Planned

- Parse all `README.md` frontmatter at build time → `graph.json`
- Static site (no server) — runs from any GitHub Pages host or local file
- Node graph: filter by `kind`, `status`, edge type
- Click a Node → render its README and its incoming/outgoing edges
- Health dashboard: residue ratio, proof debt, edge type distribution, refutation count
- Provenance: every Node shows `created`, `updated`, authors

## Architecture intent

- Inspired by, but separate from, the prior ontology-visualization explorer (different repo).
- Pure static — no runtime dependency beyond a browser.
- The build script lives here: `_explorer/build.py` (TBD).
