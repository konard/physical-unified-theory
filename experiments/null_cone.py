#!/usr/bin/env python3
"""Bounded, dependency-free checks of selected equations of arXiv:2611.34924v1."""

import cmath
from fractions import Fraction
import math
import unittest


def radial_sum(s, cutoff):
    """Equation (4.33), with one polarization and angular harmonic."""
    phases = (cmath.exp(-2j * k / s) / k**2 for k in range(1, cutoff + 1))
    terms = list(phases)
    return complex(math.fsum(z.real for z in terms), math.fsum(z.imag for z in terms)) / (2 * s**2)


def radial_imaginary_cubic_coefficient(t, cutoff):
    """Imaginary part divided by t³, where t = 1/s."""
    return -math.fsum(math.sin(2 * k * t) / (2 * k**2 * t) for k in range(1, cutoff + 1))


def finite_weight_replica_purity(weight, dimension):
    """Compute the two replica functionals on a finite constant diagonal."""
    diagonal = (weight,) * dimension
    independent = sum(diagonal) ** 2
    cyclic = sum(value**2 for value in diagonal)
    return sum(diagonal), cyclic / independent


class NullConeChecks(unittest.TestCase):
    def test_radial_tail_at_fixed_area(self):
        for s in (0.5, 2.0, 100.0):
            for n in (16, 128, 1024):
                with self.subTest(s=s, n=n):
                    tail = abs(radial_sum(s, 2 * n) - radial_sum(s, n))
                    self.assertLessEqual(tail, 1 / (2 * s**2 * n))

    def test_cubic_coefficient_grows_with_cutoff(self):
        # |sin x - x| <= |x|³/6 bounds the error of each sampled quotient.
        t = 1e-7
        previous = 0.0
        for n in (16, 128, 1024, 8192):
            with self.subTest(n=n):
                harmonic = math.fsum(1 / k for k in range(1, n + 1))
                observed = -radial_imaginary_cubic_coefficient(t, n)
                error_bound = (2 / 3) * t**2 * (n * (n + 1) / 2)
                self.assertAlmostEqual(observed, -radial_sum(1 / t, n).imag / t**3, places=11)
                self.assertLessEqual(abs(observed - harmonic), error_bound + 2e-14)
                self.assertGreater(observed, previous)
                previous = observed

    def test_scalar_replica_countermodel(self):
        weight = Fraction(2, 3)
        for n in (1, 16, 128, 1024):
            with self.subTest(n=n):
                trace, purity = finite_weight_replica_purity(weight, n)
                self.assertEqual(trace, n * weight)
                self.assertEqual(purity, Fraction(1, n))
                self.assertLessEqual(trace, 1 / purity)

    def test_clock_form_countermodel(self):
        L = 3
        previous = Fraction(1)
        for n in (1, 16, 128, 1024):
            with self.subTest(n=n):
                resolvent = Fraction(L, L + n)
                self.assertLess(resolvent, previous)
                self.assertLess(resolvent, Fraction(L, n))
                self.assertLessEqual(n * resolvent**2, Fraction(L, 4))
                previous = resolvent

    def test_schwarzschild_log_coefficient(self):
        q = Fraction(257, 302)
        self.assertEqual(q / (2 * (1 - q)) - Fraction(1, 2), Fraction(106, 45))


if __name__ == "__main__":
    unittest.main()
