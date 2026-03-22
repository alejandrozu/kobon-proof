"""
Kobon Triangle Problem - Simplified Counter and Configuration Generator

This program:
1. Counts Kobon triangles in line arrangements
2. Generates near-pencil configurations
3. Verifies known small configurations
4. Demonstrates the extension principle

OEIS A006066 values:
- n=25: 191 triangles (Bartholdi) - OPTIMAL
- n=27: 225 triangles (Savchuk) - OPTIMAL  
- n=29: 261 triangles (Bartholdi) - OPTIMAL
"""

from fractions import Fraction
from itertools import combinations
from typing import List, Tuple, Optional
import math


class Line:
    """Represents a non-vertical line as y = mx + b"""
    def __init__(self, slope, intercept):
        self.slope = Fraction(slope).limit_denominator(100000)
        self.intercept = Fraction(intercept).limit_denominator(100000)
    
    def eval_at(self, x):
        return self.slope * x + self.intercept
    
    def intersection(self, other: 'Line') -> Optional[Tuple[Fraction, Fraction]]:
        if self.slope == other.slope:
            return None
        x = (other.intercept - self.intercept) / (self.slope - other.slope)
        y = self.eval_at(x)
        return (x, y)
    
    def signed_distance(self, point: Tuple[Fraction, Fraction]) -> Fraction:
        return point[1] - self.eval_at(point[0])
    
    def __repr__(self):
        return f"Line(m={float(self.slope):.6f}, b={float(self.intercept):.6f})"


def is_kobon_triangle(lines: List[Line], i: int, j: int, k: int) -> bool:
    """Check if lines i, j, k form a Kobon triangle."""
    n = len(lines)
    li, lj, lk = lines[i], lines[j], lines[k]
    
    v_ij = li.intersection(lj)
    v_jk = lj.intersection(lk)
    v_ik = li.intersection(lk)
    
    if v_ij is None or v_jk is None or v_ik is None:
        return False
    
    for m in range(n):
        if m == i or m == j or m == k:
            continue
        
        lm = lines[m]
        d_ij = lm.signed_distance(v_ij)
        d_jk = lm.signed_distance(v_jk)
        d_ik = lm.signed_distance(v_ik)
        
        if d_ij == 0 or d_jk == 0 or d_ik == 0:
            return False
        
        signs = [d_ij > 0, d_jk > 0, d_ik > 0]
        if not (all(signs) or not any(signs)):
            return False
    
    return True


def count_kobon_triangles(lines: List[Line]) -> int:
    """Count the number of Kobon triangles."""
    n = len(lines)
    count = 0
    for i, j, k in combinations(range(n), 3):
        if is_kobon_triangle(lines, i, j, k):
            count += 1
    return count


def check_general_position(lines: List[Line]) -> Tuple[bool, str]:
    """Check if lines are in general position."""
    n = len(lines)
    
    for i in range(n):
        for j in range(i + 1, n):
            if lines[i].slope == lines[j].slope:
                return False, f"Lines {i} and {j} are parallel"
    
    for i, j, k in combinations(range(n), 3):
        v_ij = lines[i].intersection(lines[j])
        v_ik = lines[i].intersection(lines[k])
        if v_ij is not None and v_ik is not None and v_ij == v_ik:
            return False, f"Lines {i}, {j}, {k} are concurrent"
    
    return True, "OK"


def near_pencil(n: int, slope_spread: float = 0.001) -> List[Line]:
    """Generate near-pencil arrangement."""
    lines = []
    for i in range(n):
        slope = slope_spread * (i - n/2)
        intercept = (i * 3 + 1) % (n + 1) - n/2
        lines.append(Line(slope, intercept))
    return lines


def print_lines(lines: List[Line], name: str):
    """Print line equations."""
    print(f"\n{name}:")
    print("-" * 50)
    for i, line in enumerate(lines):
        m = float(line.slope)
        b = float(line.intercept)
        if abs(b) < 0.0001:
            print(f"  L{i+1}: y = {m:.8f}x")
        elif b >= 0:
            print(f"  L{i+1}: y = {m:.8f}x + {b:.8f}")
        else:
            print(f"  L{i+1}: y = {m:.8f}x - {abs(b):.8f}")


def main():
    print("=" * 70)
    print("KOBON TRIANGLE PROBLEM - Configuration Counter")
    print("=" * 70)
    
    # Test known configurations
    print("\n" + "=" * 70)
    print("VERIFICATION: Known Small Configurations")
    print("=" * 70)
    
    # n=3
    print("\n--- n=3 Configuration (expected: 1 triangle) ---")
    lines_3 = [Line(0, 0), Line(1, 0), Line(-1, 2)]
    print_lines(lines_3, "Lines")
    count = count_kobon_triangles(lines_3)
    print(f"\nTriangle count: {count} (expected: 1) - {'PASS' if count == 1 else 'FAIL'}")
    
    # n=5
    print("\n--- n=5 Configuration (expected: 5 triangles) ---")
    lines_5 = [
        Line(Fraction(1, 1000), 0),
        Line(Fraction(2, 1000), -3),
        Line(Fraction(3, 1000), 1),
        Line(Fraction(4, 1000), -5),
        Line(Fraction(5, 1000), 4),
    ]
    print_lines(lines_5, "Lines")
    count = count_kobon_triangles(lines_5)
    print(f"\nTriangle count: {count} (expected: 5) - {'PASS' if count == 5 else 'FAIL'}")
    
    # n=7
    print("\n--- n=7 Configuration (expected: 11 triangles) ---")
    lines_7 = [
        Line(-3, -9),
        Line(Fraction(-29, 10), Fraction(4, 3)),
        Line(Fraction(-11, 5), 4),
        Line(-1, 1),
        Line(Fraction(-1, 10), -2),
        Line(Fraction(11, 5), 5),
        Line(Fraction(23, 10), -3),
    ]
    print_lines(lines_7, "Lines")
    count = count_kobon_triangles(lines_7)
    print(f"\nTriangle count: {count} (expected: 11) - {'PASS' if count == 11 else 'FAIL'}")
    
    # OEIS values
    print("\n" + "=" * 70)
    print("OEIS A006066 VALUES")
    print("=" * 70)
    print("\nKnown optimal configurations:")
    print("-" * 60)
    print(f"{'n':<5} {'Triangles':<12} {'Upper Bound':<15} {'Discoverer'}")
    print("-" * 60)
    print(f"{'25':<5} {'191':<12} {'191':<15} {'Bartholdi'}")
    print(f"{'27':<5} {'225':<12} {'225':<15} {'Savchuk'}")
    print(f"{'29':<5} {'261':<12} {'261':<15} {'Bartholdi'}")
    print("-" * 60)
    print("\nExtension principle lower bounds:")
    print(f"{'26':<5} {'>= 203':<12} {'205':<15} {'(from n=25 + 12)'}")
    print(f"{'28':<5} {'>= 238':<12} {'239':<15} {'(from n=27 + 13)'}")
    print(f"{'30':<5} {'>= 275':<12} {'276':<15} {'(from n=29 + 14)'}")
    
    # Generate configurations
    print("\n" + "=" * 70)
    print("GENERATED CONFIGURATIONS (Near-Pencil Method)")
    print("=" * 70)
    
    # n=25
    print("\n--- n=25 Near-Pencil Configuration ---")
    lines_25 = near_pencil(25, slope_spread=0.01)
    gp_ok, _ = check_general_position(lines_25)
    count_25 = count_kobon_triangles(lines_25)
    print(f"General position: {gp_ok}")
    print(f"Triangle count: {count_25}")
    print(f"OEIS optimal: 191")
    print(f"Upper bound: {25 * 23 // 3}")
    print_lines(lines_25, "Line Equations")
    
    # n=27
    print("\n--- n=27 Near-Pencil Configuration ---")
    lines_27 = near_pencil(27, slope_spread=0.01)
    gp_ok, _ = check_general_position(lines_27)
    count_27 = count_kobon_triangles(lines_27)
    print(f"General position: {gp_ok}")
    print(f"Triangle count: {count_27}")
    print(f"OEIS optimal: 225")
    print(f"Upper bound: {27 * 25 // 3}")
    print_lines(lines_27, "Line Equations")
    
    # n=29
    print("\n--- n=29 Near-Pencil Configuration ---")
    lines_29 = near_pencil(29, slope_spread=0.01)
    gp_ok, _ = check_general_position(lines_29)
    count_29 = count_kobon_triangles(lines_29)
    print(f"General position: {gp_ok}")
    print(f"Triangle count: {count_29}")
    print(f"OEIS optimal: 261")
    print(f"Upper bound: {29 * 27 // 3}")
    print_lines(lines_29, "Line Equations")
    
    # Extension principle
    print("\n" + "=" * 70)
    print("EXTENSION PRINCIPLE")
    print("=" * 70)
    print("\nTheoretical result from the Lean proof:")
    print("If K(2m+1) >= T, then K(2m+2) >= T + m")
    print("\nThis means:")
    print("  - K(26) >= K(25) + 12 = 191 + 12 = 203")
    print("  - K(28) >= K(27) + 13 = 225 + 13 = 238")
    print("  - K(30) >= K(29) + 14 = 261 + 14 = 275")
    print("\nThe extension requires adding a carefully positioned line that:")
    print("  1. Has a slope between existing slopes")
    print("  2. Intersects all existing lines")
    print("  3. Creates new triangles without destroying existing ones")
    
    # Summary
    print("\n" + "=" * 70)
    print("SUMMARY")
    print("=" * 70)
    print("""
The Kobon triangle problem remains an active area of research. The optimal
configurations for n=25, 27, 29 were found using advanced computational methods:

1. SAT-solving (Savchuk 2025): Uses table encoding and SAT solvers
2. Projective geometry (Bartholdi et al.): Uses geometric insights

The near-pencil method we implemented is a well-known construction that
achieves good results for many values, but not optimal for all.

The extension principle provides theoretical lower bounds, demonstrating
that from any odd configuration, we can construct an even one with at
least T + (n-1)/2 triangles where T is the odd triangle count.

For explicit optimal configurations, see:
- OEIS A006066: https://oeis.org/A006066
- Savchuk paper: https://arxiv.org/abs/2507.07951
- Bartholdi paper: https://arxiv.org/abs/0706.0723
""")


if __name__ == "__main__":
    main()
