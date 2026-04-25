#!/usr/bin/env python3
"""Validator for the One Rule and the ontology.

Run from anywhere:
    python _meta/validate.py

Exits with non-zero status if the repository is not in conformance.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

try:
    import yaml
except ImportError:
    print("ERROR: PyYAML required. Install with: pip install pyyaml", file=sys.stderr)
    sys.exit(2)


REPO_ROOT = Path(__file__).resolve().parent.parent
ONTOLOGY_PATH = REPO_ROOT / "_meta" / "ontology.md"

ROOT_ALLOWED_FILES = {
    "README.md",
    "LICENSE",
    "LICENSE-PROSE",
    "CITATION.cff",
    ".gitignore",
}


def parse_frontmatter(md_path: Path):
    text = md_path.read_text(encoding="utf-8")
    m = re.match(r"^---\n(.*?)\n---", text, re.DOTALL)
    if not m:
        return None
    return yaml.safe_load(m.group(1))


def load_ontology():
    fm = parse_frontmatter(ONTOLOGY_PATH)
    if fm is None:
        raise SystemExit(f"Ontology {ONTOLOGY_PATH} missing frontmatter.")
    for required in ("ontology_version", "node_kinds", "statuses", "edge_types"):
        if required not in fm:
            raise SystemExit(f"Ontology missing field: {required}")
    return fm


def is_node_dir(path: Path) -> bool:
    if path == REPO_ROOT:
        return True
    return not path.name.startswith("_") and not path.name.startswith(".")


def walk_nodes(root: Path):
    """Yield every Node directory, starting at root."""
    yield root
    stack = [root]
    while stack:
        current = stack.pop()
        children_dir = current / "children"
        if children_dir.is_dir():
            for child in sorted(children_dir.iterdir()):
                if child.is_dir() and is_node_dir(child):
                    yield child
                    stack.append(child)


def validate():
    errors: list[str] = []
    ontology = load_ontology()
    valid_kinds = set(ontology["node_kinds"].keys())
    valid_statuses = set(ontology["statuses"].keys())
    valid_edge_types = set(ontology["edge_types"].keys())

    nodes = list(walk_nodes(REPO_ROOT))
    node_ids: dict[str, Path] = {}
    node_kinds: dict[str, str] = {}
    node_statuses: dict[str, str] = {}
    frontmatters: dict[Path, dict] = {}

    for node in nodes:
        rel = node.relative_to(REPO_ROOT) if node != REPO_ROOT else Path(".")
        readme = node / "README.md"
        children = node / "children"

        if not readme.is_file():
            errors.append(f"{rel}: missing README.md")
            continue
        if node != REPO_ROOT and not children.is_dir():
            errors.append(f"{rel}: missing children/ directory")

        try:
            fm = parse_frontmatter(readme)
        except yaml.YAMLError as e:
            errors.append(f"{rel}/README.md: invalid YAML frontmatter: {e}")
            continue
        if fm is None:
            errors.append(f"{rel}/README.md: missing YAML frontmatter")
            continue
        frontmatters[node] = fm

        for required in ("id", "title", "kind", "status", "authors", "created", "updated"):
            if required not in fm:
                errors.append(f"{rel}/README.md: frontmatter missing '{required}'")

        kind = fm.get("kind")
        if kind and kind not in valid_kinds:
            errors.append(f"{rel}/README.md: kind '{kind}' not in ontology")
        status = fm.get("status")
        if status and status not in valid_statuses:
            errors.append(f"{rel}/README.md: status '{status}' not in ontology")

        node_id = fm.get("id")
        if node_id:
            if node_id in node_ids:
                errors.append(
                    f"{rel}/README.md: duplicate id '{node_id}' "
                    f"(also in {node_ids[node_id]})"
                )
            else:
                node_ids[node_id] = rel
                node_kinds[node_id] = kind
                node_statuses[node_id] = status

        for entry in node.iterdir():
            if not entry.is_dir():
                continue
            name = entry.name
            if name == "children" or name.startswith("_") or name.startswith("."):
                continue
            if node == REPO_ROOT:
                continue
            errors.append(
                f"{rel}: forbidden subdirectory '{name}' "
                f"(only 'children/' or '_*' allowed inside a Node)"
            )

    for node, fm in frontmatters.items():
        rel = node.relative_to(REPO_ROOT) if node != REPO_ROOT else Path(".")
        edges = fm.get("edges") or []
        source_kind = fm.get("kind")
        for i, edge in enumerate(edges):
            if not isinstance(edge, dict):
                errors.append(f"{rel}/README.md: edge #{i} not a mapping")
                continue
            etype = edge.get("type")
            target = edge.get("target")
            if etype not in valid_edge_types:
                errors.append(
                    f"{rel}/README.md: edge #{i} type '{etype}' not in ontology"
                )
                continue
            if target not in node_ids:
                errors.append(
                    f"{rel}/README.md: edge #{i} target '{target}' "
                    f"is not an existing Node id"
                )
                continue
            rules = ontology["edge_types"][etype]
            allowed_sources = rules.get("sources", [])
            allowed_targets = rules.get("targets", [])
            if "*" not in allowed_sources and source_kind not in allowed_sources:
                errors.append(
                    f"{rel}/README.md: edge #{i} type '{etype}' "
                    f"not allowed from kind '{source_kind}'"
                )
            target_kind = node_kinds.get(target)
            if "*" not in allowed_targets and target_kind not in allowed_targets:
                errors.append(
                    f"{rel}/README.md: edge #{i} type '{etype}' "
                    f"not allowed to kind '{target_kind}' (target {target})"
                )
            if etype == "supersedes":
                if node_statuses.get(target) != "deprecated":
                    errors.append(
                        f"{rel}/README.md: edge #{i} supersedes target '{target}' "
                        f"but target status is not 'deprecated'"
                    )

    for entry in REPO_ROOT.iterdir():
        if entry.is_file() and entry.name not in ROOT_ALLOWED_FILES:
            errors.append(
                f"root: unexpected file '{entry.name}' "
                f"(only README.md, LICENSE, CITATION.cff, .gitignore allowed)"
            )

    if errors:
        print(f"VALIDATION FAILED: {len(errors)} error(s)\n", file=sys.stderr)
        for err in errors:
            print(f"  - {err}", file=sys.stderr)
        sys.exit(1)
    print(f"OK: {len(nodes)} Node(s), ontology v{ontology['ontology_version']}")


if __name__ == "__main__":
    validate()
