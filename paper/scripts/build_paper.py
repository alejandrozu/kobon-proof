"""Compile the self-contained LaTeX manuscript with Tectonic."""
from pathlib import Path
import argparse
import re
import shutil
import subprocess

PAPER = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', default='tectonic', help='Tectonic executable')
    args = parser.parse_args()
    build = PAPER / 'build'
    build.mkdir(exist_ok=True)
    result = subprocess.run(
        [args.engine, '--keep-logs', '--keep-intermediates', '--outdir', str(build), 'main.tex'],
        cwd=PAPER, text=True, encoding='utf-8', errors='replace', capture_output=True)
    (build / 'compile-console.log').write_text(result.stdout + result.stderr, encoding='utf-8')
    if result.returncode:
        raise SystemExit('Compilation failed; see paper/build/compile-console.log')
    log = (build / 'main.log').read_text(encoding='utf-8', errors='replace')
    forbidden = [r'Overfull \\[hv]box', r'There were undefined',
                 r'Reference .* undefined', r'Citation .* undefined',
                 r'Label .* multiply defined', r'^! ']
    for pattern in forbidden:
        if re.search(pattern, log, re.MULTILINE):
            raise SystemExit(f'Unresolved manuscript warning: {pattern}; see paper/build/main.log')
    output = PAPER / 'Kobon_triangle_constructions.pdf'
    shutil.copy2(build / 'main.pdf', output)
    print(f'PASS: compiled {output.name} with resolved references and no overflowing boxes.')


if __name__ == '__main__':
    main()
