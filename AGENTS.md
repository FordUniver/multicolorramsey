# Multicolor Ramsey Project

Lean 4 formalization of "Upper bounds for multicolour Ramsey numbers" ([arXiv:2410.17197](https://arxiv.org/abs/2410.17197)).

## Structure
- **blueprint/paper/**: Original paper (PDF and LaTeX source)
- **blueprint/**: Mathematical blueprint for formalization
- **MulticolorRamsey/**: Lean 4 source code
  - `Basic.lean`: Foundational definitions
  - `Integrals.lean`: Integral calculations
  - `GeometricLemma.lean`: Geometric lemma proofs
  - `KeyLemma.lean`: Key lemma formalization
- **ToMathlib/**: Lemmas destined for contribution to Mathlib
  - Each contribution in its own subdirectory (e.g., `ToMathlib/IndicatorOneMul/`)
  - Each subdirectory contains:
    - `Basic.lean`: The Lean code for the contribution
    - `metadata.yaml`: Metadata tracking PR status and details
  - `ToMathlib.lean`: Root file (required by lakefile.toml)
- **home_page/**: Jekyll website for project homepage
  - `_plugins/mathlib_tracker.rb`: Automatically aggregates `ToMathlib/*/metadata.yaml` into `_data/mathlib_contributions.yaml`
  - `index.md`: Homepage with tabular display of Mathlib contributions
- **tools/texclean/**: LaTeX normalisation CLI
  - `cli.py`, `core.py`
  - `tests/cases/*/` holds per-case fixtures (`input.tex`, `expected.tex`, optional `arguments.json`)

## Links
- [Blueprint Homepage](https://forduniver.github.io/multicolorramsey)
- [Paper](https://arxiv.org/abs/2410.17197)

## Build
- **Lean code**: `lake build`
- **Blueprint PDF**: `leanblueprint pdf`
- **Blueprint web**: `leanblueprint web`
- We are doing one line per sentence in latex

## ToMathlib Contributions

Each potential Mathlib contribution lives in `ToMathlib/ContributionName/` with:
- `Basic.lean`: The Lean code
- `metadata.yaml`: Tracking info (status, PR number, target file, etc.)

Run `python3 scripts/generate_mathlib_data.py` to aggregate all `metadata.yaml` files into `home_page/_data/mathlib_contributions.yaml` for display on the homepage. This is run automatically in CI.

Status values: `tentative`, `branch_created`, `ready_to_submit`, `submitted`, `merged`, `cleaned`

## Blueprint Organization Principles

### CRITICAL: Statement and Proof Organization
1. **No lemma within a proof** - All supporting lemmas must come BEFORE the main statement
2. **Requirements come BEFORE the statement** - All dependencies must be established first
3. **DO NOT SEPARATE statements from proofs** - Statements and their proofs belong together in the same section

### Dependency Ordering
- All mathematical objects must be ordered by logical dependency
- If lemma A uses lemma B, then lemma B must come before lemma A
- Supporting material (integration theory, auxiliary lemmas) comes before the main results that use them
- **Dependencies need not be immediately adjacent** - topically connected small lemmas can be collected in preliminaries/appendices as long as they appear before their usage
- The key principle is avoiding "vorgreifen" (forward references) - never reference something that hasn't been established yet
- we always use \(x\) instead of $x$ in LaTeX files for easier debug.
- **IMPORTANT**: Do not modify files in `blueprint/paper/` - these are original paper files that should remain unchanged
