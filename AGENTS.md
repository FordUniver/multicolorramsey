# Multicolor Ramsey Project

Lean 4 formalization of "Upper bounds for multicolour Ramsey numbers" ([arXiv:2410.17197](https://arxiv.org/abs/2410.17197)).

## Structure
- **source/**: Original paper (PDF and LaTeX source)
- **blueprint/**: Mathematical blueprint for formalization
- **MulticolorRamsey/**: Lean 4 source code
  - `Basic.lean`: Foundational definitions
  - `Integrals.lean`: Integral calculations
  - `GeometricLemma.lean`: Geometric lemma proofs
  - `KeyLemma.lean`: Key lemma formalization

## Links
- [Blueprint Homepage](https://forduniver.github.io/multicolorramsey)
- [Paper](https://arxiv.org/abs/2410.17197)

## Build
- **Lean code**: `lake build`
- **Blueprint PDF**: `leanblueprint pdf`
- **Blueprint web**: `leanblueprint web`
