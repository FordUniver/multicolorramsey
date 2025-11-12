#!/usr/bin/env python3
"""
Generate home_page/_data/mathlib_contributions.yaml from ToMathlib/*/metadata.yaml
"""

import yaml
from pathlib import Path


def main():
    repo_root = Path(__file__).parent.parent
    tomathlib_dir = repo_root / "ToMathlib"
    output_file = repo_root / "home_page" / "_data" / "mathlib_contributions.yaml"

    if not tomathlib_dir.exists():
        print(f"Error: {tomathlib_dir} does not exist")
        return 1

    contributions = []

    # Collect all metadata.yaml files
    for metadata_file in sorted(tomathlib_dir.glob("*/metadata.yaml")):
        with open(metadata_file, 'r', encoding='utf-8') as f:
            contribution = yaml.safe_load(f)
            contributions.append(contribution)

    # Sort by status and date
    status_order = {
        'cleaned': 0,
        'merged': 1,
        'submitted': 2,
        'ready_to_submit': 3,
        'branch_created': 4,
        'tentative': 5
    }

    def sort_key(c):
        status = c.get('status', 'tentative')
        date = c.get('merged_date', c.get('created_date', ''))
        return (status_order.get(status, 99), date)

    contributions.sort(key=sort_key)

    # Create output structure
    output_data = {
        'contributions': contributions
    }

    # Write output file
    output_file.parent.mkdir(parents=True, exist_ok=True)
    with open(output_file, 'w', encoding='utf-8') as f:
        yaml.dump(output_data, f, allow_unicode=True, sort_keys=False)

    print(f"Generated {output_file} with {len(contributions)} contributions")
    return 0


if __name__ == "__main__":
    exit(main())
