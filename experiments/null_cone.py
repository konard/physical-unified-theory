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


def gaussian_clock_log_overlap_bound(s, rate, L, floor, cutoff):
    """Log of a resolvent upper bound for the commuting radial clock model."""
    log_laplace_transform = -0.5 * math.fsum(
        math.log1p(rate * k / s) for k in range(1, cutoff + 1)
    )
    return math.log(L / floor) + log_laplace_transform


class NullConeChecks(unittest.TestCase):
    def test_jt_clock_momentum_boundary_term(self):
        # Rational points on the unit circles for the global AdS coordinates.
        sin_time, cos_time = Fraction(5, 13), Fraction(12, 13)
        for sin_space, cos_space in ((0, 1), (Fraction(3, 5), Fraction(4, 5)),
                                     (Fraction(-8, 17), Fraction(15, 17))):
            with self.subTest(sin_space=sin_space, cos_space=cos_space):
                sec_space = Fraction(1) / cos_space
                tan_space = sin_space / Fraction(cos_space)
                dilaton_mode = sin_time * sec_space
                # Set c = L_AdS = 1. Collect the four independent one-form terms.
                y_zero, y_one = -sin_time * tan_space, -cos_time
                variation = (
                    y_zero * sec_space * tan_space + dilaton_mode * sec_space**2,
                    y_one * sec_space * tan_space,
                    y_zero * sec_space + dilaton_mode * tan_space,
                    y_one * sec_space,
                )
                exact_derivative = (
                    sin_time * sec_space,
                    -cos_time * sec_space * tan_space,
                    0,
                    -cos_time * sec_space,
                )
                self.assertEqual(variation, exact_derivative)

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

    def test_sewn_preparation_retains_window_weight_only_for_summable_weights(self):
        window_size = 4
        for cut_size in (16, 128, 1024):
            with self.subTest(cut_size=cut_size):
                constant_weights = (Fraction(2, 3),) * cut_size
                summable_weights = [Fraction(1, k * (k + 1)) for k in range(1, cut_size + 1)]
                constant_probability = sum(constant_weights[:window_size]) / sum(constant_weights)
                summable_probability = sum(summable_weights[:window_size]) / sum(summable_weights)
                self.assertEqual(constant_probability, Fraction(window_size, cut_size))
                self.assertEqual(summable_probability, Fraction(4 * (cut_size + 1), 5 * cut_size))
                self.assertGreaterEqual(summable_probability, Fraction(4, 5))

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

    def test_radial_gaussian_clock_has_vanishing_overlap_bound(self):
        s = 2.0
        rate = 0.5
        L = 3.0
        floor = 0.75
        first_mode_bound = math.log(L / floor) - 0.5 * math.log1p(rate / s)
        self.assertAlmostEqual(
            gaussian_clock_log_overlap_bound(s, rate, L, floor, 1),
            first_mode_bound,
        )
        previous = first_mode_bound
        for n in (16, 128, 1024):
            with self.subTest(n=n):
                bound = gaussian_clock_log_overlap_bound(s, rate, L, floor, n)
                last_mode_bound = math.log(L / floor) - 0.5 * math.log1p(rate * n / s)
                self.assertLess(bound, previous)
                self.assertLessEqual(bound, last_mode_bound)
                previous = bound
        self.assertLess(previous, math.log(1e-12))

    def test_schwarzschild_log_coefficient(self):
        q = Fraction(257, 302)
        self.assertEqual(q / (2 * (1 - q)) - Fraction(1, 2), Fraction(106, 45))


if __name__ == "__main__":
    unittest.main()
