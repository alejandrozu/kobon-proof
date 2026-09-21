"""Restore the frozen experiment path layout in a new local work directory.

This copies files only; it does not run an experiment or install packages.
"""
from pathlib import Path
import argparse,shutil
ROOT=Path(__file__).resolve().parents[1]
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--dest',default='work/experiment-resume');args=parser.parse_args()
    dest=Path(args.dest).resolve()
    if dest.exists():raise SystemExit('Choose a new destination; existing files are not overwritten.')
    shutil.copytree(ROOT/'experiments/2026-09-20',dest/'work/kobon')
    for p in (ROOT/'research').glob('kobon-*'):
        shutil.copytree(p,dest/'outputs'/p.name,ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
    print(f'Copied historical layout to {dest}. Read experiments/README.md before running searches.')
