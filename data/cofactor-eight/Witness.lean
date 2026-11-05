import HodgeComputer.Verify

set_option maxHeartbeats 2000000

set_option maxRecDepth 1000

set_option linter.unusedTactic false

set_option linter.unusedSimpArgs false

set_option linter.unnecessarySeqFocus false

set_option linter.unreachableTactic false

noncomputable section

namespace HodgeComputer.Instances.CofactorEight

open MvPolynomial HodgeTestbed

def F : Poly := (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 0)^6 +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 0)^5 * (MvPolynomial.X 1) +
    (MvPolynomial.C (9 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 1)^2 +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (-2 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (13 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1)^3 +
    (MvPolynomial.C (6 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (-4 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1) * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (18 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^4 +
    (MvPolynomial.C (16 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (-18 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 2)^4 +
    (MvPolynomial.C (-4 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (12 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^5 +
    (MvPolynomial.C (13 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (-16 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^4 +
    (MvPolynomial.C (-4 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (9 : ℂ)) * (MvPolynomial.X 1)^6 +
    (MvPolynomial.C (14 : ℂ)) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (-20 : ℂ)) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (7 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^4 +
    (MvPolynomial.C (-18 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (12 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^4 +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 2)^6 +
    (MvPolynomial.C (-2 : ℂ)) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 3)^6 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 4)^6 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 4)^4 * (MvPolynomial.X 5)^2 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 5)^6

def A : Poly := (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 0)^5 * (MvPolynomial.X 4) +
    (MvPolynomial.C (5 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 1) * (MvPolynomial.X 4) +
    (MvPolynomial.C (10 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (4 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-5 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (10 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^3 * (MvPolynomial.X 4) +
    (MvPolynomial.C (6 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-15 / 2 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1) * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (7 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 4) +
    (MvPolynomial.C (8 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-17 / 2 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-5 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4) +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 1)^5 * (MvPolynomial.X 4) +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-3 : ℂ)) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-5 / 2 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4)

def D : Poly := (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1) * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (-3 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 3)^4 +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (-3 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1) * (MvPolynomial.X 3)^4 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (-3 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^4 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (-3 : ℂ)) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^4 +
    (MvPolynomial.C (9 / 4 : ℂ)) * (MvPolynomial.X 3)^6 +
    (MvPolynomial.C (1 / 4 : ℂ)) * (MvPolynomial.X 4)^6 +
    (MvPolynomial.C (1 / 4 : ℂ)) * (MvPolynomial.X 4)^4 * (MvPolynomial.X 5)^2 +
    (MvPolynomial.C (1 / 4 : ℂ)) * (MvPolynomial.X 5)^6

def Q : Poly := 0

def N0 : Poly := (MvPolynomial.C (1 / 2 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1) * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-7 / 4 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4) +
    (MvPolynomial.C (3 / 2 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-7 / 4 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (3 / 2 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-5 / 2 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 / 2 : ℂ)) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) +
    (MvPolynomial.C (-7 / 4 : ℂ)) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4) +
    (MvPolynomial.C (3 / 2 : ℂ)) * (MvPolynomial.X 3)^6 * (MvPolynomial.X 4)

def N1 : Poly := 0

def N2 : Poly := 0

def N3 : Poly := (MvPolynomial.C (1 / 4 : ℂ)) * (MvPolynomial.X 0)^5 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (5 / 8 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 1) * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (5 / 4 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 / 2 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (-7 / 8 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 3)^3 * (MvPolynomial.X 4) +
    (MvPolynomial.C (5 / 4 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^3 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (3 / 4 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (-21 / 16 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1) * (MvPolynomial.X 3)^3 * (MvPolynomial.X 4) +
    (MvPolynomial.C (7 / 8 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (-27 / 16 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^3 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 / 4 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (-7 / 8 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^3 * (MvPolynomial.X 4) +
    (MvPolynomial.C (3 / 4 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 3)^5 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 / 4 : ℂ)) * (MvPolynomial.X 1)^5 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (3 / 8 : ℂ)) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (-5 / 8 : ℂ)) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 3)^3 * (MvPolynomial.X 4) +
    (MvPolynomial.C (1 / 8 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 3) * (MvPolynomial.X 4) +
    (MvPolynomial.C (-7 / 16 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^3 * (MvPolynomial.X 4) +
    (MvPolynomial.C (3 / 8 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 3)^5 * (MvPolynomial.X 4)

def N4 : Poly := (MvPolynomial.C (1 / 12 : ℂ)) * (MvPolynomial.X 0)^5 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (5 / 24 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 1) * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (5 / 12 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 6 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (-5 / 24 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (5 / 12 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^3 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 4 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (-5 / 16 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1) * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (7 / 24 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 3 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (-17 / 48 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 12 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (-5 / 24 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 12 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 12 : ℂ)) * (MvPolynomial.X 1)^5 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 8 : ℂ)) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (-1 / 8 : ℂ)) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 24 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (-5 / 48 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 / 24 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4)^2

def N5 : Poly := (MvPolynomial.C (1 / 12 : ℂ)) * (MvPolynomial.X 0)^5 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (5 / 24 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 1) * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (5 / 12 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 6 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (-5 / 24 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (5 / 12 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^3 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 4 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (-5 / 16 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1) * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (7 / 24 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 3 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (-17 / 48 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 12 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (-5 / 24 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 12 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 12 : ℂ)) * (MvPolynomial.X 1)^5 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 8 : ℂ)) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 2)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (-1 / 8 : ℂ)) * (MvPolynomial.X 1)^3 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 24 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^4 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (-5 / 48 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 2)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4) * (MvPolynomial.X 5) +
    (MvPolynomial.C (1 / 24 : ℂ)) * (MvPolynomial.X 1) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4) * (MvPolynomial.X 5)

def N : Fin 6 → Poly := fun i => if i.val = 0 then N0 else if i.val = 1 then N1 else if i.val = 2 then N2 else if i.val = 3 then N3 else if i.val = 4 then N4 else N5

private theorem derivative_0_0 : pderiv (0 : Fin 6) (X 0 : Poly) = 1 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_0_1 : pderiv (0 : Fin 6) (X 1 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_0_2 : pderiv (0 : Fin 6) (X 2 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_0_3 : pderiv (0 : Fin 6) (X 3 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_0_4 : pderiv (0 : Fin 6) (X 4 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_0_5 : pderiv (0 : Fin 6) (X 5 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_1_0 : pderiv (1 : Fin 6) (X 0 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_1_1 : pderiv (1 : Fin 6) (X 1 : Poly) = 1 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_1_2 : pderiv (1 : Fin 6) (X 2 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_1_3 : pderiv (1 : Fin 6) (X 3 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_1_4 : pderiv (1 : Fin 6) (X 4 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_1_5 : pderiv (1 : Fin 6) (X 5 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_2_0 : pderiv (2 : Fin 6) (X 0 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_2_1 : pderiv (2 : Fin 6) (X 1 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_2_2 : pderiv (2 : Fin 6) (X 2 : Poly) = 1 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_2_3 : pderiv (2 : Fin 6) (X 3 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_2_4 : pderiv (2 : Fin 6) (X 4 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_2_5 : pderiv (2 : Fin 6) (X 5 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_3_0 : pderiv (3 : Fin 6) (X 0 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_3_1 : pderiv (3 : Fin 6) (X 1 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_3_2 : pderiv (3 : Fin 6) (X 2 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_3_3 : pderiv (3 : Fin 6) (X 3 : Poly) = 1 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_3_4 : pderiv (3 : Fin 6) (X 4 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_3_5 : pderiv (3 : Fin 6) (X 5 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_4_0 : pderiv (4 : Fin 6) (X 0 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_4_1 : pderiv (4 : Fin 6) (X 1 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_4_2 : pderiv (4 : Fin 6) (X 2 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_4_3 : pderiv (4 : Fin 6) (X 3 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_4_4 : pderiv (4 : Fin 6) (X 4 : Poly) = 1 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_4_5 : pderiv (4 : Fin 6) (X 5 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_5_0 : pderiv (5 : Fin 6) (X 0 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_5_1 : pderiv (5 : Fin 6) (X 1 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_5_2 : pderiv (5 : Fin 6) (X 2 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_5_3 : pderiv (5 : Fin 6) (X 3 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_5_4 : pderiv (5 : Fin 6) (X 4 : Poly) = 0 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

private theorem derivative_5_5 : pderiv (5 : Fin 6) (X 5 : Poly) = 1 := by norm_num [pderiv_X, Pi.single_apply, Fin.ext_iff]

theorem e1 : (1 : Poly) * directional F N = A*D := by

  simp only [directional, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]

  change (1:Poly) * (pderiv (0 : Fin 6) F * N0 + (pderiv (1 : Fin 6) F * N1 + (pderiv (2 : Fin 6) F * N2 + (pderiv (3 : Fin 6) F * N3 + (pderiv (4 : Fin 6) F * N4 + (pderiv (5 : Fin 6) F * N5)))))) = A*D

  simp only [F,A,D,N0,N1,N2,N3,N4,N5,map_zero,map_add,pderiv_C,pderiv_mul,pderiv_pow,derivative_0_0, derivative_0_1, derivative_0_2, derivative_0_3, derivative_0_4, derivative_0_5, derivative_1_0, derivative_1_1, derivative_1_2, derivative_1_3, derivative_1_4, derivative_1_5, derivative_2_0, derivative_2_1, derivative_2_2, derivative_2_3, derivative_2_4, derivative_2_5, derivative_3_0, derivative_3_1, derivative_3_2, derivative_3_3, derivative_3_4, derivative_3_5, derivative_4_0, derivative_4_1, derivative_4_2, derivative_4_3, derivative_4_4, derivative_4_5, derivative_5_0, derivative_5_1, derivative_5_2, derivative_5_3, derivative_5_4, derivative_5_5]

  apply MvPolynomial.funext; intro x

  norm_num <;> ring

theorem e2 : divergenceNumerator D N = F^1*Q := by

  simp only [divergenceNumerator, divergence, directional, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]

  change D * (pderiv (0 : Fin 6) N0 + (pderiv (1 : Fin 6) N1 + (pderiv (2 : Fin 6) N2 + (pderiv (3 : Fin 6) N3 + (pderiv (4 : Fin 6) N4 + (pderiv (5 : Fin 6) N5)))))) - (pderiv (0 : Fin 6) D * N0 + (pderiv (1 : Fin 6) D * N1 + (pderiv (2 : Fin 6) D * N2 + (pderiv (3 : Fin 6) D * N3 + (pderiv (4 : Fin 6) D * N4 + (pderiv (5 : Fin 6) D * N5)))))) = F^1*Q

  simp only [F,D,Q,N0,N1,N2,N3,N4,N5,map_zero,map_add,pderiv_C,pderiv_mul,pderiv_pow,derivative_0_0, derivative_0_1, derivative_0_2, derivative_0_3, derivative_0_4, derivative_0_5, derivative_1_0, derivative_1_1, derivative_1_2, derivative_1_3, derivative_1_4, derivative_1_5, derivative_2_0, derivative_2_1, derivative_2_2, derivative_2_3, derivative_2_4, derivative_2_5, derivative_3_0, derivative_3_1, derivative_3_2, derivative_3_3, derivative_3_4, derivative_3_5, derivative_4_0, derivative_4_1, derivative_4_2, derivative_4_3, derivative_4_4, derivative_4_5, derivative_5_0, derivative_5_1, derivative_5_2, derivative_5_3, derivative_5_4, derivative_5_5]

  apply MvPolynomial.funext; intro x

  norm_num <;> ring

theorem denominator_homogeneous : D.IsHomogeneous 6 := by

  simpa only [D] using (((((((((((((((((((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).add ((((isHomogeneous_C (σ := Fin 6) (2 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (3 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (2 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2))).add (((isHomogeneous_C (σ := Fin 6) (-3 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4))).add ((((isHomogeneous_C (σ := Fin 6) (2 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2))).add (((((isHomogeneous_C (σ := Fin 6) (2 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (-3 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4))).add (((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (2 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2))).add (((isHomogeneous_C (σ := Fin 6) (-3 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4))).add (((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2))).add (((isHomogeneous_C (σ := Fin 6) (-3 : ℂ)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4))).add ((isHomogeneous_C (σ := Fin 6) (9 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 6))).add ((isHomogeneous_C (σ := Fin 6) (1 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 6))).add (((isHomogeneous_C (σ := Fin 6) (1 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (5 : Fin 6)).pow 2))).add ((isHomogeneous_C (σ := Fin 6) (1 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (5 : Fin 6)).pow 6)))

theorem N0_homogeneous : N0.IsHomogeneous 7 := by

  simpa only [N0] using (((((((((((((((((isHomogeneous_C (σ := Fin 6) (1 / 2 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).add (((((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (2 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (-7 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 2 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-7 / 4 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 2 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (-5 / 2 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 2 : ℂ)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (-7 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((isHomogeneous_C (σ := Fin 6) (3 / 2 : ℂ)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 6)).mul (isHomogeneous_X ℂ (4 : Fin 6))))

theorem N1_homogeneous : N1.IsHomogeneous 7 := by

  simpa only [N1] using isHomogeneous_zero (Fin 6) ℂ _

theorem N2_homogeneous : N2.IsHomogeneous 7 := by

  simpa only [N2] using isHomogeneous_zero (Fin 6) ℂ _

theorem N3_homogeneous : N3.IsHomogeneous 7 := by

  simpa only [N3] using (((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) (1 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 8 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 2 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (-7 / 8 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (3 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-21 / 16 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (7 / 8 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-27 / 16 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 4 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-7 / 8 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (3 / 4 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 8 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (-5 / 8 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 8 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (3 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-7 / 16 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (4 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (3 / 8 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (4 : Fin 6))))

theorem N4_homogeneous : N4.IsHomogeneous 7 := by

  simpa only [N4] using ((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) (1 / 12 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2)).add ((((isHomogeneous_C (σ := Fin 6) (5 / 24 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (5 / 12 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 6 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (-5 / 24 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (5 / 12 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 16 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (7 / 24 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 3 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add (((((isHomogeneous_C (σ := Fin 6) (-17 / 48 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 12 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 24 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 12 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add (((isHomogeneous_C (σ := Fin 6) (1 / 12 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 8 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (-1 / 8 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 24 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 48 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 24 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (4 : Fin 6)).pow 2)))

theorem N5_homogeneous : N5.IsHomogeneous 7 := by

  simpa only [N5] using (((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) (1 / 12 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 24 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 12 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 6 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 24 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 12 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (1 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (-5 / 16 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (7 / 24 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (1 / 3 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (-17 / 48 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 12 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (-5 / 24 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 12 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (1 / 12 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 8 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-1 / 8 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 24 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add ((((((isHomogeneous_C (σ := Fin 6) (-5 / 48 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 24 : ℂ)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (3 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (4 : Fin 6))).mul (isHomogeneous_X ℂ (5 : Fin 6))))

theorem numerator_homogeneous : ∀ i, (N i).IsHomogeneous 7 := by

  intro i; fin_cases i

  · exact N0_homogeneous

  · exact N1_homogeneous

  · exact N2_homogeneous

  · exact N3_homogeneous

  · exact N4_homogeneous

  · exact N5_homogeneous

def toUni : Poly →+* Polynomial Coeff := MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun i => if i.val = 0 then (Polynomial.X) else if i.val = 1 then (Polynomial.C (MvPolynomial.X 0)) else if i.val = 2 then (Polynomial.C (MvPolynomial.X 1)) else if i.val = 3 then (Polynomial.C (MvPolynomial.X 2)) else if i.val = 4 then (Polynomial.C (MvPolynomial.X 3)) else (Polynomial.C (MvPolynomial.X 4)))

def fromUni : Polynomial Coeff →+* Poly := Polynomial.eval₂RingHom (MvPolynomial.eval₂Hom MvPolynomial.C (fun i => if i.val = 0 then (MvPolynomial.X 1) else if i.val = 1 then (MvPolynomial.X 2) else if i.val = 2 then (MvPolynomial.X 3) else if i.val = 3 then (MvPolynomial.X 4) else (MvPolynomial.X 5))) (MvPolynomial.X 0)

@[simp] theorem toUni_X0 : toUni (MvPolynomial.X 0) = (Polynomial.X) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X1 : toUni (MvPolynomial.X 1) = (Polynomial.C (MvPolynomial.X 0)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X2 : toUni (MvPolynomial.X 2) = (Polynomial.C (MvPolynomial.X 1)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X3 : toUni (MvPolynomial.X 3) = (Polynomial.C (MvPolynomial.X 2)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X4 : toUni (MvPolynomial.X 4) = (Polynomial.C (MvPolynomial.X 3)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X5 : toUni (MvPolynomial.X 5) = (Polynomial.C (MvPolynomial.X 4)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_C (c : ℂ) : toUni (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by simp [toUni]

@[simp] theorem fromUni_w0 : fromUni (Polynomial.C (MvPolynomial.X 0)) = (MvPolynomial.X 1) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w1 : fromUni (Polynomial.C (MvPolynomial.X 1)) = (MvPolynomial.X 2) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w2 : fromUni (Polynomial.C (MvPolynomial.X 2)) = (MvPolynomial.X 3) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w3 : fromUni (Polynomial.C (MvPolynomial.X 3)) = (MvPolynomial.X 4) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w4 : fromUni (Polynomial.C (MvPolynomial.X 4)) = (MvPolynomial.X 5) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_t : fromUni Polynomial.X = MvPolynomial.X 0 := by simp [fromUni]

theorem retract : fromUni.comp toUni = RingHom.id Poly := by

  apply MvPolynomial.ringHom_ext

  · intro c; simp [toUni,fromUni]

  · intro i; fin_cases i <;> simp only [RingHom.comp_apply,RingHom.id_apply]

    · change fromUni (toUni (X 0)) = X 0; simp only [toUni_X0,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 1)) = X 1; simp only [toUni_X1,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 2)) = X 2; simp only [toUni_X2,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 3)) = X 3; simp only [toUni_X3,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 4)) = X 4; simp only [toUni_X4,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 5)) = X 5; simp only [toUni_X5,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

def fUni : Polynomial Coeff := Polynomial.C ((MvPolynomial.C (1 : ℂ))) * Polynomial.X^6 +
    Polynomial.C ((MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 0)) * Polynomial.X^5 +
    Polynomial.C ((MvPolynomial.C (9 : ℂ)) * (MvPolynomial.X 0)^2 +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 1)^2 +
    (MvPolynomial.C (-2 : ℂ)) * (MvPolynomial.X 2)^2) * Polynomial.X^4 +
    Polynomial.C ((MvPolynomial.C (13 : ℂ)) * (MvPolynomial.X 0)^3 +
    (MvPolynomial.C (6 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 +
    (MvPolynomial.C (-4 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 2)^2) * Polynomial.X^3 +
    Polynomial.C ((MvPolynomial.C (18 : ℂ)) * (MvPolynomial.X 0)^4 +
    (MvPolynomial.C (16 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^2 +
    (MvPolynomial.C (-18 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 1)^4 +
    (MvPolynomial.C (-4 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2) * Polynomial.X^2 +
    Polynomial.C ((MvPolynomial.C (12 : ℂ)) * (MvPolynomial.X 0)^5 +
    (MvPolynomial.C (13 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 1)^2 +
    (MvPolynomial.C (-16 : ℂ)) * (MvPolynomial.X 0)^3 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (3 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^4 +
    (MvPolynomial.C (-4 : ℂ)) * (MvPolynomial.X 0) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2) * Polynomial.X^1 +
    Polynomial.C ((MvPolynomial.C (9 : ℂ)) * (MvPolynomial.X 0)^6 +
    (MvPolynomial.C (14 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 1)^2 +
    (MvPolynomial.C (-20 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (7 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^4 +
    (MvPolynomial.C (-18 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 1)^2 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (12 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 2)^4 +
    (MvPolynomial.C (2 : ℂ)) * (MvPolynomial.X 1)^6 +
    (MvPolynomial.C (-2 : ℂ)) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 2)^6 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 3)^6 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (1 : ℂ)) * (MvPolynomial.X 4)^6) * Polynomial.X^0

theorem toUni_F : toUni F = fUni := by

  simp only [F, fUni, map_add, map_mul, map_pow, toUni_C, toUni_X0,toUni_X1,toUni_X2,toUni_X3,toUni_X4,toUni_X5]; polynomial

theorem fUni_degree : fUni.natDegree = 6 := by

  unfold fUni; compute_degree!

theorem fUni_lc : fUni.leadingCoeff = MvPolynomial.C (1 : ℂ) := by

  rw [Polynomial.leadingCoeff, fUni_degree]

  simp only [fUni, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]

  norm_num

def point : Fin 5 → ℂ := fun i => if i.val = 0 then (1 : ℂ) else if i.val = 1 then (1 : ℂ) else if i.val = 2 then (1 : ℂ) else if i.val = 3 then (1 : ℂ) else (1 : ℂ)

def specialize : Coeff →+* ℂ := MvPolynomial.eval point

def fFiber : Polynomial ℂ := (Polynomial.C (1 : ℂ)) * Polynomial.X^6 +
    (Polynomial.C (3 : ℂ)) * Polynomial.X^5 +
    (Polynomial.C (10 : ℂ)) * Polynomial.X^4 +
    (Polynomial.C (15 : ℂ)) * Polynomial.X^3 +
    (Polynomial.C (15 : ℂ)) * Polynomial.X^2 +
    (Polynomial.C (8 : ℂ)) * Polynomial.X +
    (Polynomial.C (8 : ℂ))

def dFiber : Polynomial ℂ := (Polynomial.C (1 : ℂ)) * Polynomial.X^4 +
    (Polynomial.C (2 : ℂ)) * Polynomial.X^3 +
    (Polynomial.C (2 : ℂ)) * Polynomial.X^2 +
    (Polynomial.C (1 : ℂ)) * Polynomial.X +
    (Polynomial.C (1 : ℂ))

def bezoutF : Polynomial ℂ := (Polynomial.C (-1 / 3 : ℂ)) * Polynomial.X^2 +
    (Polynomial.C (-1 / 3 : ℂ)) * Polynomial.X +
    (Polynomial.C (1 / 3 : ℂ))

def bezoutD : Polynomial ℂ := (Polynomial.C (1 / 3 : ℂ)) * Polynomial.X^4 +
    (Polynomial.C (2 / 3 : ℂ)) * Polynomial.X^3 +
    (Polynomial.C (2 : ℂ)) * Polynomial.X^2 +
    (Polynomial.C (5 / 3 : ℂ)) * Polynomial.X +
    (Polynomial.C (-5 / 3 : ℂ))

theorem fiber_F : (toUni F).map specialize = fFiber := by

  rw [toUni_F]

  norm_num [fUni,specialize,point,fFiber] <;> polynomial

theorem fiber_D : (toUni D).map specialize = dFiber := by

  simp only [D,map_add,map_mul,map_pow,toUni_C,toUni_X0,toUni_X1,toUni_X2,toUni_X3,toUni_X4,toUni_X5]

  norm_num [specialize,point,dFiber] <;> polynomial

theorem fiber_coprime : IsCoprime fFiber dFiber := by

  refine ⟨bezoutF, bezoutD, ?_⟩

  unfold bezoutF bezoutD fFiber dFiber

  polynomial

theorem denominator_legal : IsRelPrime F D := by

  apply relPrime_of_retract toUni fromUni retract

  apply relPrime_of_specialization specialize

  · rw [toUni_F, fUni_lc]

    exact (isUnit_iff_ne_zero.mpr (by norm_num : (1 : ℂ) ≠ 0)).map MvPolynomial.C

  · rw [fiber_F, fiber_D]

    exact fiber_coprime.isRelPrime

theorem denominator_ne_zero : D ≠ 0 := by

  intro h

  have he := congrArg (MvPolynomial.eval (![1,1,1,1,1,1] : Fin 6 → ℂ)) h

  norm_num [D, show (![1,1,1,1,1,1] : Fin 6 → ℂ) 0 = 1 from rfl, show (![1,1,1,1,1,1] : Fin 6 → ℂ) 1 = 1 from rfl, show (![1,1,1,1,1,1] : Fin 6 → ℂ) 2 = 1 from rfl, show (![1,1,1,1,1,1] : Fin 6 → ℂ) 3 = 1 from rfl, show (![1,1,1,1,1,1] : Fin 6 → ℂ) 4 = 1 from rfl, show (![1,1,1,1,1,1] : Fin 6 → ℂ) 5 = 1 from rfl] at he

theorem certificate : Verify F A 1 6 D N Q where

  denominator_ne_zero := denominator_ne_zero

  denominator_homogeneous := denominator_homogeneous

  numerator_homogeneous := numerator_homogeneous

  denominator_legal := denominator_legal

  identity := normalized_identity (by simpa using e1) e2

theorem solved : HasCertificate F A 1 := ⟨6, D, N, Q, certificate⟩

end HodgeComputer.Instances.CofactorEight

#print axioms HodgeComputer.Instances.CofactorEight.solved
