import HodgeComputer.Verify

set_option maxHeartbeats 2000000

set_option maxRecDepth 1000

set_option linter.unusedTactic false

set_option linter.unusedSimpArgs false

set_option linter.unnecessarySeqFocus false

set_option linter.unreachableTactic false

noncomputable section

namespace HodgeComputer.Instances.KleinRational

open MvPolynomial HodgeTestbed

def F : Poly := (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^5 * (MvPolynomial.X (1 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (0 : Fin 6)) * (MvPolynomial.X (2 : Fin 6))^5 +
    (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (1 : Fin 6))^5 * (MvPolynomial.X (2 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (3 : Fin 6))^5 * (MvPolynomial.X (4 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (3 : Fin 6)) * (MvPolynomial.X (5 : Fin 6))^5 +
    (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (4 : Fin 6))^5 * (MvPolynomial.X (5 : Fin 6))

def A : Poly := (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^3 * (MvPolynomial.X (1 : Fin 6))^2 * (MvPolynomial.X (3 : Fin 6))

def D : Poly := (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^18 * (MvPolynomial.X (1 : Fin 6))^12 +
    (MvPolynomial.C (σ := Fin 6) (6 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^17 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^3 +
    (MvPolynomial.C (σ := Fin 6) (33 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^16 * (MvPolynomial.X (1 : Fin 6))^8 * (MvPolynomial.X (2 : Fin 6))^6 +
    (MvPolynomial.C (σ := Fin 6) (-3 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^15 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6))^2 +
    (MvPolynomial.C (σ := Fin 6) (20 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^15 * (MvPolynomial.X (1 : Fin 6))^6 * (MvPolynomial.X (2 : Fin 6))^9 +
    (MvPolynomial.C (σ := Fin 6) (30 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^14 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6))^5 +
    (MvPolynomial.C (σ := Fin 6) (15 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^14 * (MvPolynomial.X (1 : Fin 6))^4 * (MvPolynomial.X (2 : Fin 6))^12 +
    (MvPolynomial.C (σ := Fin 6) (60 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^13 * (MvPolynomial.X (1 : Fin 6))^9 * (MvPolynomial.X (2 : Fin 6))^8 +
    (MvPolynomial.C (σ := Fin 6) (-3 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^13 * (MvPolynomial.X (1 : Fin 6))^2 * (MvPolynomial.X (2 : Fin 6))^15 +
    (MvPolynomial.C (σ := Fin 6) (15 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (2 : Fin 6))^4 +
    (MvPolynomial.C (σ := Fin 6) (51 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (1 : Fin 6))^7 * (MvPolynomial.X (2 : Fin 6))^11 +
    (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^18 +
    (MvPolynomial.C (σ := Fin 6) (51 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^7 +
    (MvPolynomial.C (σ := Fin 6) (30 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6))^5 * (MvPolynomial.X (2 : Fin 6))^14 +
    (MvPolynomial.C (σ := Fin 6) (90 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^10 +
    (MvPolynomial.C (σ := Fin 6) (6 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^3 * (MvPolynomial.X (2 : Fin 6))^17 +
    (MvPolynomial.C (σ := Fin 6) (20 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^9 * (MvPolynomial.X (1 : Fin 6))^15 * (MvPolynomial.X (2 : Fin 6))^6 +
    (MvPolynomial.C (σ := Fin 6) (60 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^9 * (MvPolynomial.X (1 : Fin 6))^8 * (MvPolynomial.X (2 : Fin 6))^13 +
    (MvPolynomial.C (σ := Fin 6) (60 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^8 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6))^9 +
    (MvPolynomial.C (σ := Fin 6) (33 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^8 * (MvPolynomial.X (1 : Fin 6))^6 * (MvPolynomial.X (2 : Fin 6))^16 +
    (MvPolynomial.C (σ := Fin 6) (51 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^7 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6))^12 +
    (MvPolynomial.C (σ := Fin 6) (33 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^6 * (MvPolynomial.X (1 : Fin 6))^16 * (MvPolynomial.X (2 : Fin 6))^8 +
    (MvPolynomial.C (σ := Fin 6) (20 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^6 * (MvPolynomial.X (1 : Fin 6))^9 * (MvPolynomial.X (2 : Fin 6))^15 +
    (MvPolynomial.C (σ := Fin 6) (30 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^5 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (2 : Fin 6))^11 +
    (MvPolynomial.C (σ := Fin 6) (15 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^4 * (MvPolynomial.X (1 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^14 +
    (MvPolynomial.C (σ := Fin 6) (6 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^3 * (MvPolynomial.X (1 : Fin 6))^17 * (MvPolynomial.X (2 : Fin 6))^10 +
    (MvPolynomial.C (σ := Fin 6) (-3 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^2 * (MvPolynomial.X (1 : Fin 6))^15 * (MvPolynomial.X (2 : Fin 6))^13 +
    (MvPolynomial.C (σ := Fin 6) (1 : ℂ)) * (MvPolynomial.X (1 : Fin 6))^18 * (MvPolynomial.X (2 : Fin 6))^12

def Q : Poly := 0

def N0 : Poly := (MvPolynomial.C (σ := Fin 6) (1 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^19 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6)) * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-1 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^18 * (MvPolynomial.X (1 : Fin 6))^8 * (MvPolynomial.X (2 : Fin 6))^4 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (3 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^17 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-3 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^17 * (MvPolynomial.X (1 : Fin 6))^6 * (MvPolynomial.X (2 : Fin 6))^7 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (25 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^16 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6))^3 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-1 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^16 * (MvPolynomial.X (1 : Fin 6))^4 * (MvPolynomial.X (2 : Fin 6))^10 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (23 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^15 * (MvPolynomial.X (1 : Fin 6))^9 * (MvPolynomial.X (2 : Fin 6))^6 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-1 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^15 * (MvPolynomial.X (1 : Fin 6))^2 * (MvPolynomial.X (2 : Fin 6))^13 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-3 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^14 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (2 : Fin 6))^2 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (73 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^14 * (MvPolynomial.X (1 : Fin 6))^7 * (MvPolynomial.X (2 : Fin 6))^9 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (51 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^13 * (MvPolynomial.X (1 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^5 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (29 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^13 * (MvPolynomial.X (1 : Fin 6))^5 * (MvPolynomial.X (2 : Fin 6))^12 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (191 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^8 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-25 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (1 : Fin 6))^3 * (MvPolynomial.X (2 : Fin 6))^15 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (15 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6))^15 * (MvPolynomial.X (2 : Fin 6))^4 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (9 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6))^8 * (MvPolynomial.X (2 : Fin 6))^11 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-5 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6)) * (MvPolynomial.X (2 : Fin 6))^18 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (115 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6))^7 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (39 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^6 * (MvPolynomial.X (2 : Fin 6))^14 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (197 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^9 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6))^10 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-25 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^9 * (MvPolynomial.X (1 : Fin 6))^4 * (MvPolynomial.X (2 : Fin 6))^17 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (3 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^8 * (MvPolynomial.X (1 : Fin 6))^16 * (MvPolynomial.X (2 : Fin 6))^6 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (75 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^8 * (MvPolynomial.X (1 : Fin 6))^9 * (MvPolynomial.X (2 : Fin 6))^13 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (37 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^7 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (2 : Fin 6))^9 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (15 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^7 * (MvPolynomial.X (1 : Fin 6))^7 * (MvPolynomial.X (2 : Fin 6))^16 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (1 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^6 * (MvPolynomial.X (1 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^12 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (15 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^5 * (MvPolynomial.X (1 : Fin 6))^17 * (MvPolynomial.X (2 : Fin 6))^8 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-5 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^5 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^15 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-9 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^4 * (MvPolynomial.X (1 : Fin 6))^15 * (MvPolynomial.X (2 : Fin 6))^11 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-5 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^3 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6))^14 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (3 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^2 * (MvPolynomial.X (1 : Fin 6))^18 * (MvPolynomial.X (2 : Fin 6))^10 * (MvPolynomial.X (3 : Fin 6))

def N1 : Poly := (MvPolynomial.C (σ := Fin 6) (-5 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^18 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6)) * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (5 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^17 * (MvPolynomial.X (1 : Fin 6))^9 * (MvPolynomial.X (2 : Fin 6))^4 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-1 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^16 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (15 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^16 * (MvPolynomial.X (1 : Fin 6))^7 * (MvPolynomial.X (2 : Fin 6))^7 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (43 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^15 * (MvPolynomial.X (1 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^3 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (5 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^15 * (MvPolynomial.X (1 : Fin 6))^5 * (MvPolynomial.X (2 : Fin 6))^10 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (19 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^14 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^6 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (5 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^14 * (MvPolynomial.X (1 : Fin 6))^3 * (MvPolynomial.X (2 : Fin 6))^13 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^13 * (MvPolynomial.X (1 : Fin 6))^15 * (MvPolynomial.X (2 : Fin 6))^2 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (97 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^13 * (MvPolynomial.X (1 : Fin 6))^8 * (MvPolynomial.X (2 : Fin 6))^9 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (39 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6))^5 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (23 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (1 : Fin 6))^6 * (MvPolynomial.X (2 : Fin 6))^12 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (207 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6))^8 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (13 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6))^4 * (MvPolynomial.X (2 : Fin 6))^15 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-5 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^16 * (MvPolynomial.X (2 : Fin 6))^4 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (13 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^9 * (MvPolynomial.X (2 : Fin 6))^11 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-3 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^2 * (MvPolynomial.X (2 : Fin 6))^18 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (139 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^9 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (2 : Fin 6))^7 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (15 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^9 * (MvPolynomial.X (1 : Fin 6))^7 * (MvPolynomial.X (2 : Fin 6))^14 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (149 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^8 * (MvPolynomial.X (1 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^10 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-15 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^8 * (MvPolynomial.X (1 : Fin 6))^5 * (MvPolynomial.X (2 : Fin 6))^17 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-1 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^7 * (MvPolynomial.X (1 : Fin 6))^17 * (MvPolynomial.X (2 : Fin 6))^6 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (59 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^7 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^13 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (25 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^6 * (MvPolynomial.X (1 : Fin 6))^15 * (MvPolynomial.X (2 : Fin 6))^9 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (9 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^6 * (MvPolynomial.X (1 : Fin 6))^8 * (MvPolynomial.X (2 : Fin 6))^16 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-19 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^5 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6))^12 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-5 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^4 * (MvPolynomial.X (1 : Fin 6))^18 * (MvPolynomial.X (2 : Fin 6))^8 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-3 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^4 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6))^15 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (3 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^3 * (MvPolynomial.X (1 : Fin 6))^16 * (MvPolynomial.X (2 : Fin 6))^11 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-3 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^2 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (2 : Fin 6))^14 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-1 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6)) * (MvPolynomial.X (1 : Fin 6))^19 * (MvPolynomial.X (2 : Fin 6))^10 * (MvPolynomial.X (3 : Fin 6))

def N2 : Poly := (MvPolynomial.C (σ := Fin 6) (-3 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^18 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^2 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (3 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^17 * (MvPolynomial.X (1 : Fin 6))^8 * (MvPolynomial.X (2 : Fin 6))^5 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (5 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^16 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6)) * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (9 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^16 * (MvPolynomial.X (1 : Fin 6))^6 * (MvPolynomial.X (2 : Fin 6))^8 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (65 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^15 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6))^4 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (3 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^15 * (MvPolynomial.X (1 : Fin 6))^4 * (MvPolynomial.X (2 : Fin 6))^11 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (23 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^14 * (MvPolynomial.X (1 : Fin 6))^9 * (MvPolynomial.X (2 : Fin 6))^7 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (3 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^14 * (MvPolynomial.X (1 : Fin 6))^2 * (MvPolynomial.X (2 : Fin 6))^14 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-5 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^13 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (2 : Fin 6))^3 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (89 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^13 * (MvPolynomial.X (1 : Fin 6))^7 * (MvPolynomial.X (2 : Fin 6))^10 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (71 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (1 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^6 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (25 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^12 * (MvPolynomial.X (1 : Fin 6))^5 * (MvPolynomial.X (2 : Fin 6))^13 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (155 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^9 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (5 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^11 * (MvPolynomial.X (1 : Fin 6))^3 * (MvPolynomial.X (2 : Fin 6))^16 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (25 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^15 * (MvPolynomial.X (2 : Fin 6))^5 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (13 / 4 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6))^8 * (MvPolynomial.X (2 : Fin 6))^12 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (1 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^10 * (MvPolynomial.X (1 : Fin 6)) * (MvPolynomial.X (2 : Fin 6))^19 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (159 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^9 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6))^8 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-5 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^9 * (MvPolynomial.X (1 : Fin 6))^6 * (MvPolynomial.X (2 : Fin 6))^15 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (81 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^8 * (MvPolynomial.X (1 : Fin 6))^11 * (MvPolynomial.X (2 : Fin 6))^11 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (5 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^8 * (MvPolynomial.X (1 : Fin 6))^4 * (MvPolynomial.X (2 : Fin 6))^18 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (5 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^7 * (MvPolynomial.X (1 : Fin 6))^16 * (MvPolynomial.X (2 : Fin 6))^7 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-1 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^7 * (MvPolynomial.X (1 : Fin 6))^9 * (MvPolynomial.X (2 : Fin 6))^14 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (29 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^6 * (MvPolynomial.X (1 : Fin 6))^14 * (MvPolynomial.X (2 : Fin 6))^10 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-3 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^6 * (MvPolynomial.X (1 : Fin 6))^7 * (MvPolynomial.X (2 : Fin 6))^17 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (-17 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^5 * (MvPolynomial.X (1 : Fin 6))^12 * (MvPolynomial.X (2 : Fin 6))^13 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (25 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^4 * (MvPolynomial.X (1 : Fin 6))^17 * (MvPolynomial.X (2 : Fin 6))^9 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (1 / 7 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^4 * (MvPolynomial.X (1 : Fin 6))^10 * (MvPolynomial.X (2 : Fin 6))^16 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (13 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^3 * (MvPolynomial.X (1 : Fin 6))^15 * (MvPolynomial.X (2 : Fin 6))^12 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (1 / 14 : ℂ)) * (MvPolynomial.X (0 : Fin 6))^2 * (MvPolynomial.X (1 : Fin 6))^13 * (MvPolynomial.X (2 : Fin 6))^15 * (MvPolynomial.X (3 : Fin 6)) +
    (MvPolynomial.C (σ := Fin 6) (5 / 28 : ℂ)) * (MvPolynomial.X (0 : Fin 6)) * (MvPolynomial.X (1 : Fin 6))^18 * (MvPolynomial.X (2 : Fin 6))^11 * (MvPolynomial.X (3 : Fin 6))

def N3 : Poly := 0

def N4 : Poly := 0

def N5 : Poly := 0

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

theorem denominator_homogeneous : D.IsHomogeneous 30 := by

  simpa only [D] using ((((((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 18)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).add ((((isHomogeneous_C (σ := Fin 6) (6 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 3))).add ((((isHomogeneous_C (σ := Fin 6) (33 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 6))).add ((((isHomogeneous_C (σ := Fin 6) (-3 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2))).add ((((isHomogeneous_C (σ := Fin 6) (20 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 9))).add ((((isHomogeneous_C (σ := Fin 6) (30 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 5))).add ((((isHomogeneous_C (σ := Fin 6) (15 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12))).add ((((isHomogeneous_C (σ := Fin 6) (60 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 8))).add ((((isHomogeneous_C (σ := Fin 6) (-3 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 15))).add ((((isHomogeneous_C (σ := Fin 6) (15 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4))).add ((((isHomogeneous_C (σ := Fin 6) (51 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11))).add (((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 18))).add ((((isHomogeneous_C (σ := Fin 6) (51 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 7))).add ((((isHomogeneous_C (σ := Fin 6) (30 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 14))).add ((((isHomogeneous_C (σ := Fin 6) (90 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10))).add ((((isHomogeneous_C (σ := Fin 6) (6 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 17))).add ((((isHomogeneous_C (σ := Fin 6) (20 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 6))).add ((((isHomogeneous_C (σ := Fin 6) (60 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 13))).add ((((isHomogeneous_C (σ := Fin 6) (60 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 9))).add ((((isHomogeneous_C (σ := Fin 6) (33 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 16))).add ((((isHomogeneous_C (σ := Fin 6) (51 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12))).add ((((isHomogeneous_C (σ := Fin 6) (33 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 8))).add ((((isHomogeneous_C (σ := Fin 6) (20 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 15))).add ((((isHomogeneous_C (σ := Fin 6) (30 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11))).add ((((isHomogeneous_C (σ := Fin 6) (15 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 14))).add ((((isHomogeneous_C (σ := Fin 6) (6 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10))).add ((((isHomogeneous_C (σ := Fin 6) (-3 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 13))).add (((isHomogeneous_C (σ := Fin 6) (1 : ℂ)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 18)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12)))

theorem N0_homogeneous : N0.IsHomogeneous 31 := by

  simpa only [N0] using (((((((((((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) (1 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 19)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).add (((((isHomogeneous_C (σ := Fin 6) (-1 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 18)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (3 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-3 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 7)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (25 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-1 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (23 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 6)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-1 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 13)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-3 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (73 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 9)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (51 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (29 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (191 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 8)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-25 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 15)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (15 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (9 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 18)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (115 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 7)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (39 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 14)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (197 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-25 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 17)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 6)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (75 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 13)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (37 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 9)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (15 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 16)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (15 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 8)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 15)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-9 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 14)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 18)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (3 : Fin 6))))

theorem N1_homogeneous : N1.IsHomogeneous 31 := by

  simpa only [N1] using (((((((((((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) (-5 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 18)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add ((((isHomogeneous_C (σ := Fin 6) (-1 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (15 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 7)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (43 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (19 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 6)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 13)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (97 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 9)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (39 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (23 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (207 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 8)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (13 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 15)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (13 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-3 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 18)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (139 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 7)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (15 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 14)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (149 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-15 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 17)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-1 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 6)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (59 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 13)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (25 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 9)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (9 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 16)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-19 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 18)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 8)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-3 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 15)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-3 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 14)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-1 / 28 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 19)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (3 : Fin 6))))

theorem N2_homogeneous : N2.IsHomogeneous 31 := by

  simpa only [N2] using (((((((((((((((((((((((((((((((((((isHomogeneous_C (σ := Fin 6) (-3 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 18)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 2)).mul (isHomogeneous_X ℂ (3 : Fin 6))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul (isHomogeneous_X ℂ (2 : Fin 6))).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (9 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 8)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (65 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 4)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (23 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 7)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (3 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 14)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 3)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (89 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (71 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 6)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (25 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 13)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (155 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 9)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 16)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (25 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 5)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (13 / 4 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (1 : Fin 6))).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 19)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (159 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 8)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-5 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 15)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (81 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 11)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 8)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 18)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 16)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 7)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-1 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 9)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 14)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (29 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 14)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 10)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-3 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 6)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 7)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 17)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (-17 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 5)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 12)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 13)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (25 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 17)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 9)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 7 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 4)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 10)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 16)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (13 / 28 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 3)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 15)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 12)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (1 / 14 : ℂ)).mul ((isHomogeneous_X ℂ (0 : Fin 6)).pow 2)).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 13)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 15)).mul (isHomogeneous_X ℂ (3 : Fin 6)))).add (((((isHomogeneous_C (σ := Fin 6) (5 / 28 : ℂ)).mul (isHomogeneous_X ℂ (0 : Fin 6))).mul ((isHomogeneous_X ℂ (1 : Fin 6)).pow 18)).mul ((isHomogeneous_X ℂ (2 : Fin 6)).pow 11)).mul (isHomogeneous_X ℂ (3 : Fin 6))))

theorem N3_homogeneous : N3.IsHomogeneous 31 := by

  simpa only [N3] using isHomogeneous_zero (Fin 6) ℂ _

theorem N4_homogeneous : N4.IsHomogeneous 31 := by

  simpa only [N4] using isHomogeneous_zero (Fin 6) ℂ _

theorem N5_homogeneous : N5.IsHomogeneous 31 := by

  simpa only [N5] using isHomogeneous_zero (Fin 6) ℂ _

theorem numerator_homogeneous : ∀ i, (N i).IsHomogeneous 31 := by

  intro i; fin_cases i

  · exact N0_homogeneous

  · exact N1_homogeneous

  · exact N2_homogeneous

  · exact N3_homogeneous

  · exact N4_homogeneous

  · exact N5_homogeneous

def toUni : Poly →+* Polynomial Coeff := MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun i => if i.val = 0 then (Polynomial.C (MvPolynomial.X 0)) else if i.val = 1 then (Polynomial.C (MvPolynomial.X 1)) else if i.val = 2 then (Polynomial.C (MvPolynomial.X 2)) else if i.val = 3 then (Polynomial.X) else if i.val = 4 then (Polynomial.C (MvPolynomial.X 3) + Polynomial.X) else (Polynomial.C (MvPolynomial.X 4)))

def fromUni : Polynomial Coeff →+* Poly := Polynomial.eval₂RingHom (MvPolynomial.eval₂Hom MvPolynomial.C (fun i => if i.val = 0 then (MvPolynomial.X 0) else if i.val = 1 then (MvPolynomial.X 1) else if i.val = 2 then (MvPolynomial.X 2) else if i.val = 3 then (MvPolynomial.X 4 - MvPolynomial.X 3) else (MvPolynomial.X 5))) (MvPolynomial.X 3)

@[simp] theorem toUni_X0 : toUni (MvPolynomial.X 0) = (Polynomial.C (MvPolynomial.X 0)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X1 : toUni (MvPolynomial.X 1) = (Polynomial.C (MvPolynomial.X 1)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X2 : toUni (MvPolynomial.X 2) = (Polynomial.C (MvPolynomial.X 2)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X3 : toUni (MvPolynomial.X 3) = (Polynomial.X) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X4 : toUni (MvPolynomial.X 4) = (Polynomial.C (MvPolynomial.X 3) + Polynomial.X) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X5 : toUni (MvPolynomial.X 5) = (Polynomial.C (MvPolynomial.X 4)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_C (c : ℂ) : toUni (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by simp [toUni]

@[simp] theorem fromUni_w0 : fromUni (Polynomial.C (MvPolynomial.X 0)) = (MvPolynomial.X 0) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w1 : fromUni (Polynomial.C (MvPolynomial.X 1)) = (MvPolynomial.X 1) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w2 : fromUni (Polynomial.C (MvPolynomial.X 2)) = (MvPolynomial.X 2) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w3 : fromUni (Polynomial.C (MvPolynomial.X 3)) = (MvPolynomial.X 4 - MvPolynomial.X 3) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w4 : fromUni (Polynomial.C (MvPolynomial.X 4)) = (MvPolynomial.X 5) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_t : fromUni Polynomial.X = MvPolynomial.X 3 := by simp [fromUni]

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

def fUni : Polynomial Coeff := Polynomial.C ((MvPolynomial.C (σ := Fin 5) (1 : ℂ))) * Polynomial.X^6 +
    Polynomial.C ((MvPolynomial.C (σ := Fin 5) (1 : ℂ)) * (MvPolynomial.X (3 : Fin 5)) +
    (MvPolynomial.C (σ := Fin 5) (1 : ℂ)) * (MvPolynomial.X (4 : Fin 5))) * Polynomial.X^5 +
    Polynomial.C ((MvPolynomial.C (σ := Fin 5) (5 : ℂ)) * (MvPolynomial.X (3 : Fin 5)) * (MvPolynomial.X (4 : Fin 5))) * Polynomial.X^4 +
    Polynomial.C ((MvPolynomial.C (σ := Fin 5) (10 : ℂ)) * (MvPolynomial.X (3 : Fin 5))^2 * (MvPolynomial.X (4 : Fin 5))) * Polynomial.X^3 +
    Polynomial.C ((MvPolynomial.C (σ := Fin 5) (10 : ℂ)) * (MvPolynomial.X (3 : Fin 5))^3 * (MvPolynomial.X (4 : Fin 5))) * Polynomial.X^2 +
    Polynomial.C ((MvPolynomial.C (σ := Fin 5) (5 : ℂ)) * (MvPolynomial.X (3 : Fin 5))^4 * (MvPolynomial.X (4 : Fin 5)) +
    (MvPolynomial.C (σ := Fin 5) (1 : ℂ)) * (MvPolynomial.X (4 : Fin 5))^5) * Polynomial.X^1 +
    Polynomial.C ((MvPolynomial.C (σ := Fin 5) (1 : ℂ)) * (MvPolynomial.X (0 : Fin 5))^5 * (MvPolynomial.X (1 : Fin 5)) +
    (MvPolynomial.C (σ := Fin 5) (1 : ℂ)) * (MvPolynomial.X (0 : Fin 5)) * (MvPolynomial.X (2 : Fin 5))^5 +
    (MvPolynomial.C (σ := Fin 5) (1 : ℂ)) * (MvPolynomial.X (1 : Fin 5))^5 * (MvPolynomial.X (2 : Fin 5)) +
    (MvPolynomial.C (σ := Fin 5) (1 : ℂ)) * (MvPolynomial.X (3 : Fin 5))^5 * (MvPolynomial.X (4 : Fin 5))) * Polynomial.X^0

theorem toUni_F : toUni F = fUni := by

  simp only [F, fUni, map_add, map_mul, map_pow, toUni_C, toUni_X0,toUni_X1,toUni_X2,toUni_X3,toUni_X4,toUni_X5]; norm_num [map_ofNat] <;> polynomial

theorem fUni_degree : fUni.natDegree = 6 := by

  unfold fUni; compute_degree!

theorem fUni_lc : fUni.leadingCoeff = MvPolynomial.C (1 : ℂ) := by

  rw [Polynomial.leadingCoeff, fUni_degree]

  simp only [fUni, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]

  norm_num

def point : Fin 5 → ℂ := fun i => if i.val = 0 then (1 : ℂ) else if i.val = 1 then (1 : ℂ) else if i.val = 2 then (1 : ℂ) else if i.val = 3 then (1 : ℂ) else (1 : ℂ)

def specialize : Coeff →+* ℂ := MvPolynomial.eval point

def fFiber : Polynomial ℂ := (Polynomial.C (1 : ℂ)) * Polynomial.X^6 +
    (Polynomial.C (2 : ℂ)) * Polynomial.X^5 +
    (Polynomial.C (5 : ℂ)) * Polynomial.X^4 +
    (Polynomial.C (10 : ℂ)) * Polynomial.X^3 +
    (Polynomial.C (10 : ℂ)) * Polynomial.X^2 +
    (Polynomial.C (6 : ℂ)) * Polynomial.X +
    (Polynomial.C (4 : ℂ))

def dFiber : Polynomial ℂ := (Polynomial.C (729 : ℂ))

def bezoutF : Polynomial ℂ := 0

def bezoutD : Polynomial ℂ := (Polynomial.C (1 / 729 : ℂ))

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

theorem certificate : Verify F A 1 30 D N Q where

  denominator_ne_zero := denominator_ne_zero

  denominator_homogeneous := denominator_homogeneous

  numerator_homogeneous := numerator_homogeneous

  denominator_legal := denominator_legal

  identity := normalized_identity (by simpa using e1) e2

theorem solved : HasCertificate F A 1 := ⟨30, D, N, Q, certificate⟩

end HodgeComputer.Instances.KleinRational

#print axioms HodgeComputer.Instances.KleinRational.solved
