"""Run every certificate once and check its printed values against README.md.

Each script runs under nice, with a 600 s alarm, from certificates/. x1_real_arrays.py needs numpy and is skipped
when numpy is missing; every other script is stdlib-only. The C checks need a C compiler (cc).
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(os.path.dirname(HERE), 'certificates')
PY = sys.executable


def run(*args, timeout=600):
    p = subprocess.run(['nice', '-n', '15', *args], cwd=CERT, capture_output=True, text=True, timeout=timeout)
    if p.returncode != 0:
        raise AssertionError(f"{args} exited {p.returncode}:\n{p.stdout[-2000:]}\n{p.stderr[-2000:]}")
    return p.stdout


def have_numpy():
    return subprocess.run([PY, '-c', 'import numpy'], capture_output=True).returncode == 0


class Theorems(unittest.TestCase):
    def test_three_rows(self):
        out = run(PY, '-I', 'x1_theorems.py', '--conjecture')
        self.assertIn('PASS', out)
        self.assertEqual(out.count('cell walk == closed form'), 3)
        self.assertNotIn(': False', out)
        for hmin, best, omt in ((79, 92, '1.8309163030e-15'), (43, 51, '4.2212827752e-13'),
                                (20, 23, '4.3712752456e-11')):
            self.assertIn(f'Delta > 0 exactly for h >= {hmin}', out)
            self.assertIn(f'best h = {best}', out)
            self.assertIn(f"1 - theta' = {omt}", out)
        for x in ('1.051e+15', '4.559e+12', '4.402e+10'):           # crossovers at c0 = 84
            self.assertIn(x, out)
        self.assertIn('[conjecture only]', out)
        self.assertIn('3.9762e-9', out)

    def test_theorem1_count(self):
        out = run(PY, '-I', 'x1_exponent_count.py')
        self.assertEqual(out.count('match=True'), 5)
        self.assertIn('best h = 92', out)
        self.assertIn("1 - theta' = 1.830916e-15", out)


class PrePass(unittest.TestCase):
    def test_fourier_side(self):
        out = run(PY, '-I', 'x1_prepass_check.py')
        self.assertIn('total norm-1 lines checked: 42', out)
        self.assertIn('PASS', out)
        self.assertEqual(out.count('  OK'), 6)

    @unittest.skipUnless(have_numpy(), 'numpy missing')
    def test_real_arrays(self):
        ok = run(PY, 'x1_real_arrays.py', 'B', '2', '4')
        self.assertIn('match=YES', ok)
        self.assertIn('aux 0 fail / 102, X_d 0 fail / 18, Y_d 0 fail / 18', ok)
        base = run(PY, 'x1_real_arrays.py', 'B', '2', '0')
        self.assertIn('aux 0 fail / 102, X_d 0 fail / 18, Y_d 0 fail / 18', base)
        steps = lambda o: int(re.search(r'directional steps=(\d+)', o).group(1))
        self.assertEqual(steps(base) - steps(ok), 18)                    # one step saved per bank entry
        bad = run(PY, 'x1_real_arrays.py', 'B', '2', '5')               # one-sided control must fail
        self.assertIn('Y_d 18 fail / 18', bad)


class E1(unittest.TestCase):
    def test_invocation(self):
        out = run(PY, '-I', 'x1_e1_check.py')
        self.assertIn('PASS', out)
        self.assertIn('failures=1214  refuted as expected', out)
        self.assertIn('failures=468  refuted as expected', out)


class Word(unittest.TestCase):
    def test_independent(self):
        out = run(PY, '-I', 'x1_word_check.py')
        self.assertEqual(out.count(': OK'), 5)

    def test_search_verifier(self):
        out = run(PY, '-I', 'm6_word_verify.py')
        self.assertIn('PASS', out)
        self.assertNotIn('FAIL', out)


@unittest.skipUnless(shutil.which('cc'), 'no C compiler')
class Network(unittest.TestCase):
    def test_rep_h6_h7(self):
        with tempfile.TemporaryDirectory() as d:
            for h in (6, 7):
                exe = os.path.join(d, f'rep{h}')
                subprocess.run(['cc', '-O2', f'-DH={h}', '-o', exe, 'x1_e2e_rep.c'], cwd=CERT, check=True)
                out = run(exe)
                self.assertIn('match=YES', out)
                self.assertNotIn('match=NO', out)
                self.assertIn('bank swap failures 0 /', out)
                self.assertRegex(out, r'FAIL totals: nondeg 0 nest 0 residual 0 degenerate-residual 0 '
                                      r'edge-phase 0 wire-phase 0')


@unittest.skipUnless(shutil.which('cc'), 'no C compiler')
class E1Full(unittest.TestCase):
    def test_e1_rep_h8_h9(self):
        with tempfile.TemporaryDirectory() as d:
            for h, delta in ((8, '-171008'), (9, '-5785344')):
                exe = os.path.join(d, f'e1rep{h}')
                subprocess.run(['cc', '-O2', f'-DH={h}', '-o', exe, 'x1_e1_rep.c'], cwd=CERT, check=True)
                out = run(exe)
                self.assertIn('match=YES', out)
                self.assertNotIn('match=NO', out)
                self.assertIn('bank swap failures 0 /', out)
                self.assertIn(f'(2 v^2 (v - 3ch) = {delta})', out)
                self.assertRegex(out, r'FAIL totals: nondeg 0 nest 0 residual 0 degenerate-residual 0 '
                                      r'edge-phase 0 wire-phase 0')


if __name__ == '__main__':
    unittest.main()
