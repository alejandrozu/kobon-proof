"""Merge disjoint exact-certificate worker outputs without trusting their claims.

The merged artifact must subsequently pass verify_affine_grid_obstruction.py.
Input digests preserve the provenance of the independently generated ranges.
"""
from pathlib import Path
from fractions import Fraction
import argparse
import hashlib
import json


def merge(parts, output, expected):
    data = None
    records = []
    inputs = []
    for part in parts:
        raw = part.read_bytes()
        value = json.loads(raw)
        if data is None:
            data = {key: value[key] for key in
                    ('source', 'field_polynomial', 'root_interval', 'epsilon_scope')}
        else:
            for key in ('field_polynomial', 'root_interval'):
                assert data[key] == value[key], key
        records.extend(value['records'])
        inputs.append({'path': str(part), 'sha256': hashlib.sha256(raw).hexdigest(),
                       'records': len(value['records'])})
    records.sort(key=lambda row: row['case_index'])
    assert [row['case_index'] for row in records] == list(range(10000, 10000 + expected))
    radius = min(Fraction(row['epsilon_upper']) for row in records if 'weights' in row)
    data.update(records=records, merged_inputs=inputs,
                success=sum(row['status'] == 'exact_symbolic_positive_dependency' for row in records),
                epsilon_upper=str(radius), epsilon_upper_float=float(radius),
                verification_status='Unverified producer output; run the independent affine checker')
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(data, separators=(',', ':')) + '\n')
    print(json.dumps({'records': len(records), 'success': data['success'],
                      'bytes': output.stat().st_size, 'output': str(output)}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('parts', nargs='+', type=Path)
    parser.add_argument('--out', required=True, type=Path)
    parser.add_argument('--expected', type=int, default=3763)
    args = parser.parse_args()
    merge(args.parts, args.out, args.expected)
