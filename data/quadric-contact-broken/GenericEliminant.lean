import Proposal.GenericLineChart
import Proposal.Subresultant

namespace GenericLineChart
variable {K : Type*} [CommRing K]

def eliminantCoeff0 (p q s k u v : K) : K := -u*v^10
def eliminantCoeff1 (p q s k u v : K) : K := k^2*p*v^9
def eliminantCoeff2 (p q s k u v : K) : K := -k^2*u*v^8*s
def eliminantCoeff3 (p q s k u v : K) : K := 2*k^6*v^7 + k^4*q^2*v^7 + 6*k^2*q*u*v^8 + 9*u^2*v^9
def eliminantCoeff4 (p q s k u v : K) : K := -2*k^4*p*q*v^7 + 2*k^4*u*v^6*s^2 - 8*k^2*p*u*v^8
def eliminantCoeff5 (p q s k u v : K) : K := -4*k^8*v^5*s - 2*k^6*p*v^5*s^2 + 2*k^6*q^2*v^5*s + 4*k^4*p^2*v^7 + 8*k^4*q*u*v^6*s + 8*k^2*u^2*v^7*s
def eliminantCoeff6 (p q s k u v : K) : K := 12*k^8*q*v^5 + 2*k^6*p*q*v^5*s - 2*k^6*q^3*v^5 + 40*k^6*u*v^6 + 2*k^6*u*v^4*s^3 - 16*k^4*q^2*u*v^6 - 42*k^2*q*u^2*v^7 - 36*u^3*v^8
def eliminantCoeff7 (p q s k u v : K) : K := 2*k^10*v^3*s^2 - 10*k^8*p*v^5 + k^8*q^2*v^3*s^2 + 3*k^6*p*q^2*v^5 + 18*k^4*p*q*u*v^6 - 6*k^4*u^2*v^5*s^2 + 28*k^2*p*u^2*v^7
def eliminantCoeff8 (p q s k u v : K) : K := -4*k^10*q*v^3*s + 2*k^8*p*q*v^3*s^2 - 2*k^8*q^3*v^3*s - 10*k^8*u*v^4*s - k^8*u*v^2*s^4 - 6*k^6*p^2*q*v^5 + 8*k^6*p*u*v^4*s^2 - 17*k^6*q^2*u*v^4*s - 18*k^4*p^2*u*v^6 - 42*k^4*q*u^2*v^5*s - 28*k^2*u^3*v^6*s
def eliminantCoeff9 (p q s k u v : K) : K := 4*k^12*v^3 + 8*k^10*p*v^3*s + k^10*p*v*s^4 + 4*k^10*q^2*v^3 - 4*k^8*p^2*v^3*s^2 + k^8*q^4*v^3 + 12*k^8*q*u*v^4 + 6*k^6*p^3*v^5 + 2*k^6*p*q*u*v^4*s + 14*k^6*q^3*u*v^4 - 12*k^6*u^2*v^5 + 66*k^4*q^2*u^2*v^5 + 126*k^2*q*u^3*v^6 + 84*u^4*v^7
def eliminantCoeff10 (p q s k u v : K) : K := -4*k^10*p*q*v^3 - 2*k^10*p*q*v*s^3 - 12*k^10*u*v^2*s^2 - k^10*u*s^5 + 4*k^8*p^2*q*v^3*s - 2*k^8*p*q^3*v^3 + 8*k^8*p*u*v^4 - 2*k^8*q^2*u*v^2*s^2 + 2*k^6*p^2*u*v^4*s - 20*k^6*p*q^2*u*v^4 - 6*k^6*q*u^2*v^3*s^2 - 60*k^4*p*q*u^2*v^5 - 56*k^2*p*u^3*v^6
def eliminantCoeff11 (p q s k u v : K) : K := 2*k^12*p*v*s^2 - 10*k^10*p^2*v^3 + k^10*p*q^2*v*s^2 + 12*k^10*q*u*v^2*s + 2*k^10*q*u*s^4 + 3*k^8*p^2*q^2*v^3 - 2*k^8*p*q*u*v^2*s^2 + 6*k^8*q^3*u*v^2*s + 44*k^8*u^2*v^3*s + 5*k^8*u^2*v*s^4 + 18*k^6*p^2*q*u*v^4 - 12*k^6*p*u^2*v^3*s^2 + 42*k^6*q^2*u^2*v^3*s + 30*k^4*p^2*u^2*v^5 + 90*k^4*q*u^3*v^4*s + 56*k^2*u^4*v^5*s
def eliminantCoeff12 (p q s k u v : K) : K := -12*k^12*u*v^2 - 2*k^12*u*s^3 + 2*k^10*p^2*q*v*s^2 + 12*k^10*p*u*v^2*s - 12*k^10*q^2*u*v^2 - k^10*q^2*u*s^3 - 6*k^8*p^3*q*v^3 + 6*k^8*p^2*u*v^2*s^2 - 6*k^8*p*q^2*u*v^2*s - 3*k^8*q^4*u*v^2 - 96*k^8*q*u^2*v^3 - 6*k^8*q*u^2*v*s^3 - 16*k^6*p^3*u*v^4 - 16*k^6*p*q*u^2*v^3*s - 32*k^6*q^3*u^2*v^3 - 178*k^6*u^3*v^4 - 12*k^6*u^3*v^2*s^3 - 125*k^4*q^2*u^3*v^4 - 210*k^2*q*u^4*v^5 - 126*u^5*v^6
def eliminantCoeff13 (p q s k u v : K) : K := -4*k^12*p^2*v*s - 2*k^10*p^3*v*s^2 - 2*k^10*p^2*q^2*v*s + 12*k^10*p*q*u*v^2 - 2*k^10*p*q*u*s^3 + 4*k^8*p^4*v^3 - 4*k^8*p^2*q*u*v^2*s + 6*k^8*p*q^3*u*v^2 + 32*k^8*p*u^2*v^3 + 4*k^8*q^2*u^2*v*s^2 - 8*k^6*p^2*u^2*v^3*s + 44*k^6*p*q^2*u^2*v^3 + 18*k^6*q*u^3*v^2*s^2 + 100*k^4*p*q*u^3*v^4 + 20*k^4*u^4*v^3*s^2 + 70*k^2*p*u^4*v^5
def eliminantCoeff14 (p q s k u v : K) : K := 4*k^12*p*u*s^2 + 2*k^10*p^3*q*v*s + 2*k^10*p^2*u*s^3 + 2*k^10*p*q^2*u*s^2 - 12*k^10*q*u^2*v*s - 4*k^8*p^2*q^2*u*v^2 + 4*k^8*p*q*u^2*v*s^2 - 6*k^8*q^3*u^2*v*s - 32*k^8*u^3*v^2*s - 4*k^8*u^3*s^4 - 18*k^6*p^2*q*u^2*v^3 + 8*k^6*p*u^3*v^2*s^2 - 44*k^6*q^2*u^3*v^2*s - 20*k^4*p^2*u^3*v^4 - 100*k^4*q*u^4*v^3*s - 70*k^2*u^5*v^4*s
def eliminantCoeff15 (p q s k u v : K) : K := 2*k^12*p^3*v + 12*k^12*u^2*v + k^10*p^3*q^2*v - 2*k^10*p^2*q*u*s^2 - 12*k^10*p*u^2*v*s + 12*k^10*q^2*u^2*v + 6*k^8*p^3*q*u*v^2 - 6*k^8*p^2*u^2*v*s^2 + 6*k^8*p*q^2*u^2*v*s + 3*k^8*q^4*u^2*v + 96*k^8*q*u^3*v^2 + 6*k^8*q*u^3*s^3 + 12*k^6*p^3*u^2*v^3 + 16*k^6*p*q*u^3*v^2*s + 32*k^6*q^3*u^3*v^2 + 178*k^6*u^4*v^3 + 16*k^6*u^4*v*s^3 + 125*k^4*q^2*u^4*v^3 + 210*k^2*q*u^5*v^4 + 126*u^6*v^5
def eliminantCoeff16 (p q s k u v : K) : K := -2*k^12*p^2*u*s - 2*k^10*p^4*q*v - k^10*p^2*q^2*u*s - 12*k^10*p*q*u^2*v + 10*k^10*u^3*s^2 - 5*k^8*p^4*u*v^2 + 2*k^8*p^2*q*u^2*v*s - 6*k^8*p*q^3*u^2*v - 44*k^8*p*u^3*v^2 - 3*k^8*q^2*u^3*s^2 + 12*k^6*p^2*u^3*v^2*s - 42*k^6*p*q^2*u^3*v^2 - 18*k^6*q*u^4*v*s^2 - 90*k^4*p*q*u^4*v^3 - 30*k^4*u^5*v^2*s^2 - 56*k^2*p*u^5*v^4
def eliminantCoeff17 (p q s k u v : K) : K := k^10*p^5*v + 2*k^10*p^3*q*u*s + 12*k^10*p^2*u^2*v + 4*k^10*q*u^3*s + 2*k^8*p^2*q^2*u^2*v - 4*k^8*p*q*u^3*s^2 + 2*k^8*q^3*u^3*s - 8*k^8*u^4*v*s + 6*k^6*p^2*q*u^3*v^2 - 2*k^6*p*u^4*v*s^2 + 20*k^6*q^2*u^4*v*s + 60*k^4*q*u^5*v^2*s + 56*k^2*u^6*v^3*s
def eliminantCoeff18 (p q s k u v : K) : K := -4*k^12*u^3 - k^10*p^4*u*s - 8*k^10*p*u^3*s - 4*k^10*q^2*u^3 + 4*k^8*p^2*u^3*s^2 - k^8*q^4*u^3 - 12*k^8*q*u^4*v - 2*k^6*p*q*u^4*v*s - 14*k^6*q^3*u^4*v + 12*k^6*u^5*v^2 - 6*k^6*u^5*s^3 - 66*k^4*q^2*u^5*v^2 - 126*k^2*q*u^6*v^3 - 84*u^7*v^4
def eliminantCoeff19 (p q s k u v : K) : K := 4*k^10*p*q*u^3 + k^8*p^4*u^2*v - 2*k^8*p^2*q*u^3*s + 2*k^8*p*q^3*u^3 + 10*k^8*p*u^4*v - 8*k^6*p^2*u^4*v*s + 17*k^6*p*q^2*u^4*v + 6*k^6*q*u^5*s^2 + 42*k^4*p*q*u^5*v^2 + 18*k^4*u^6*v*s^2 + 28*k^2*p*u^6*v^3
def eliminantCoeff20 (p q s k u v : K) : K := -2*k^10*p^2*u^3 - k^8*p^2*q^2*u^3 + 10*k^8*u^5*s - 3*k^6*q^2*u^5*s + 6*k^4*p^2*u^5*v^2 - 18*k^4*q*u^6*v*s - 28*k^2*u^7*v^2*s
def eliminantCoeff21 (p q s k u v : K) : K := -12*k^8*q*u^5 - 2*k^6*p^3*u^4*v - 2*k^6*p*q*u^5*s + 2*k^6*q^3*u^5 - 40*k^6*u^6*v + 16*k^4*q^2*u^6*v + 42*k^2*q*u^7*v^2 + 36*u^8*v^3
def eliminantCoeff22 (p q s k u v : K) : K := 4*k^8*p*u^5 + 2*k^6*p^2*u^5*s - 2*k^6*p*q^2*u^5 - 8*k^4*p*q*u^6*v - 4*k^4*u^7*s^2 - 8*k^2*p*u^7*v^2
def eliminantCoeff23 (p q s k u v : K) : K := -2*k^4*p^2*u^6*v + 2*k^4*q*u^7*s + 8*k^2*u^8*v*s
def eliminantCoeff24 (p q s k u v : K) : K := -2*k^6*u^7 - k^4*q^2*u^7 - 6*k^2*q*u^8*v - 9*u^9*v^2
def eliminantCoeff25 (p q s k u v : K) : K := k^2*p*u^8*v
def eliminantCoeff26 (p q s k u v : K) : K := -k^2*u^9*s
def eliminantCoeff27 (p q s k u v : K) : K := u^10*v
def eliminant (r p q s k u v : K) : K := eliminantCoeff0 p q s k u v + r*(eliminantCoeff1 p q s k u v + r*(eliminantCoeff2 p q s k u v + r*(eliminantCoeff3 p q s k u v + r*(eliminantCoeff4 p q s k u v + r*(eliminantCoeff5 p q s k u v + r*(eliminantCoeff6 p q s k u v + r*(eliminantCoeff7 p q s k u v + r*(eliminantCoeff8 p q s k u v + r*(eliminantCoeff9 p q s k u v + r*(eliminantCoeff10 p q s k u v + r*(eliminantCoeff11 p q s k u v + r*(eliminantCoeff12 p q s k u v + r*(eliminantCoeff13 p q s k u v + r*(eliminantCoeff14 p q s k u v + r*(eliminantCoeff15 p q s k u v + r*(eliminantCoeff16 p q s k u v + r*(eliminantCoeff17 p q s k u v + r*(eliminantCoeff18 p q s k u v + r*(eliminantCoeff19 p q s k u v + r*(eliminantCoeff20 p q s k u v + r*(eliminantCoeff21 p q s k u v + r*(eliminantCoeff22 p q s k u v + r*(eliminantCoeff23 p q s k u v + r*(eliminantCoeff24 p q s k u v + r*(eliminantCoeff25 p q s k u v + r*(eliminantCoeff26 p q s k u v + r*(eliminantCoeff27 p q s k u v)))))))))))))))))))))))))))

def resStage1Part0 (A B F H k r p u : K) : K := A^4*H^3 + 4*A^3*B^2*H^3 - 2*A^3*B*F*H^2 - 16*A^3*B*H^3*r^3*u + 6*A^3*F*H^2*r^3*u - 4*A^3*H^3*k^2*p*r^4
def resStage1Part1 (A B F H k r p u : K) : K := 8*A^3*H^3*r^6*u^2 + 4*A^2*B^4*H^3 - 4*A^2*B^3*F*H^2 + A^2*B^2*F^2*H - 4*A^2*B^2*F*H^2*r^3*u + 8*A^2*B^2*H^3*k^2*p*r^4
def resStage1Part2 (A B F H k r p u : K) : K := 4*A^2*B*F^2*H*r^3*u - 4*A^2*B*F*H^2*k^2*p*r^4 - A^2*F^3*r^3*u + A^2*F^2*H*k^2*p*r^4 - 4*A^2*F*H^2*k^2*p*r^7*u + 4*A^2*H^3*k^6*r^6
def resStage1Part3 (A B F H k r p u : K) : K := 4*A^2*H^3*k^4*p^2*r^8 - 8*A*B^2*H^3*k^6*r^6 - 4*A*B*F*H^2*k^6*r^6 + 12*A*F*H^2*k^6*r^9*u - 8*A*H^3*k^8*p*r^10 + 2*B^2*F^2*H*k^6*r^6
def resStage1Part4 (A B F H k r p u : K) : K := -2*F^3*k^6*r^9*u + 2*F^2*H*k^8*p*r^10 + 4*H^3*k^12*r^12
def resStage1 (A B F H k r p u : K) : K := resStage1Part0 A B F H k r p u + resStage1Part1 A B F H k r p u + resStage1Part2 A B F H k r p u + resStage1Part3 A B F H k r p u + resStage1Part4 A B F H k r p u

def resStage3Part0 (A H k r p u q : K) : K := -A^5*u + 4*A^4*H^2*u + A^4*H*k^2*p*r + 3*A^4*H*r^3*u^2 + 6*A^4*k^2*p*r^4*u - 3*A^4*k^2*q*r^3*u
def resStage3Part1 (A H k r p u q : K) : K := -4*A^3*H^4*u - 4*A^3*H^3*k^2*p*r - 4*A^3*H^3*r^3*u^2 - 20*A^3*H^2*k^2*p*r^4*u + 8*A^3*H^2*k^2*q*r^3*u - 4*A^3*H*k^4*p^2*r^5
def resStage3Part2 (A H k r p u q : K) : K := 2*A^3*H*k^4*p*q*r^4 - 12*A^3*H*k^2*p*r^7*u^2 + 6*A^3*H*k^2*q*r^6*u^2 - 2*A^3*k^6*r^6*u - 12*A^3*k^4*p^2*r^8*u + 12*A^3*k^4*p*q*r^7*u
def resStage3Part3 (A H k r p u q : K) : K := -3*A^3*k^4*q^2*r^6*u + 4*A^2*H^5*k^2*p*r + 16*A^2*H^4*k^2*p*r^4*u + 2*A^2*H^3*k^6*r^3 + 8*A^2*H^3*k^4*p^2*r^5 - 4*A^2*H^3*k^4*p*q*r^4
def resStage3Part4 (A H k r p u q : K) : K := A^2*H^3*k^4*q^2*r^3 + 12*A^2*H^3*k^2*p*r^7*u^2 + 24*A^2*H^2*k^4*p^2*r^8*u - 20*A^2*H^2*k^4*p*q*r^7*u + 4*A^2*H^2*k^4*q^2*r^6*u + 2*A^2*H*k^8*p*r^7
def resStage3Part5 (A H k r p u q : K) : K := 4*A^2*H*k^6*p^3*r^9 - 4*A^2*H*k^6*p^2*q*r^8 + A^2*H*k^6*p*q^2*r^7 - 18*A^2*H*k^6*r^9*u^2 + 12*A^2*H*k^4*p^2*r^11*u^2 - 12*A^2*H*k^4*p*q*r^10*u^2
def resStage3Part6 (A H k r p u q : K) : K := 3*A^2*H*k^4*q^2*r^9*u^2 + 12*A^2*k^8*p*r^10*u - 6*A^2*k^8*q*r^9*u + 8*A^2*k^6*p^3*r^12*u - 12*A^2*k^6*p^2*q*r^11*u + 6*A^2*k^6*p*q^2*r^10*u
def resStage3Part7 (A H k r p u q : K) : K := -A^2*k^6*q^3*r^9*u - 8*A*H^5*k^6*r^3 - 24*A*H^4*k^6*r^6*u + 24*A*H^2*k^8*p*r^10*u - 8*A*H*k^10*p^2*r^11 + 4*A*H*k^10*p*q*r^10
def resStage3Part8 (A H k r p u q : K) : K := 72*A*H*k^8*p*r^13*u^2 - 36*A*H*k^8*q*r^12*u^2 - 24*A*k^10*p^2*r^14*u + 24*A*k^10*p*q*r^13*u - 6*A*k^10*q^2*r^12*u + 8*H^7*k^6*r^3
def resStage3Part9 (A H k r p u q : K) : K := 80*H^6*k^6*r^6*u - 8*H^5*k^8*p*r^7 + 8*H^5*k^8*q*r^6 + 288*H^5*k^6*r^9*u^2 - 48*H^4*k^8*p*r^10*u + 48*H^4*k^8*q*r^9*u
def resStage3Part10 (A H k r p u q : K) : K := 432*H^4*k^6*r^12*u^3 + 4*H^3*k^12*r^9 - 8*H^3*k^10*p^2*r^11 + 2*H^3*k^10*q^2*r^9 - 72*H^3*k^8*p*r^13*u^2 + 72*H^3*k^8*q*r^12*u^2
def resStage3Part11 (A H k r p u q : K) : K := 216*H^3*k^6*r^15*u^4 - 48*H^2*k^10*p^2*r^14*u + 24*H^2*k^10*p*q*r^13*u + 8*H*k^12*p^3*r^15 - 8*H*k^12*p^2*q*r^14 + 2*H*k^12*p*q^2*r^13
def resStage3Part12 (A H k r p u q : K) : K := -72*H*k^10*p^2*r^17*u^2 + 72*H*k^10*p*q*r^16*u^2 - 18*H*k^10*q^2*r^15*u^2 + 16*k^12*p^3*r^18*u - 24*k^12*p^2*q*r^17*u + 12*k^12*p*q^2*r^16*u
def resStage3Part13 (A H k r p u q : K) : K := -2*k^12*q^3*r^15*u
def resStage3 (A H k r p u q : K) : K := resStage3Part0 A H k r p u q + resStage3Part1 A H k r p u q + resStage3Part2 A H k r p u q + resStage3Part3 A H k r p u q + resStage3Part4 A H k r p u q + resStage3Part5 A H k r p u q + resStage3Part6 A H k r p u q + resStage3Part7 A H k r p u q + resStage3Part8 A H k r p u q + resStage3Part9 A H k r p u q + resStage3Part10 A H k r p u q + resStage3Part11 A H k r p u q + resStage3Part12 A H k r p u q + resStage3Part13 A H k r p u q

def resStage4Part0 (H k r p u q s : K) : K := -H^10*u + H^9*k^2*p*r - H^9*r^3*u^2 + H^8*k^2*p*r^4*u + 6*H^8*k^2*q*r^3*u - H^8*k^2*r^2*s*u
def resStage4Part1 (H k r p u q s : K) : K := 2*H^7*k^6*r^3 + 4*H^7*k^4*p^2*r^5 - 2*H^7*k^4*p*q*r^4 + H^7*k^4*q^2*r^3 + 6*H^7*k^2*q*r^6*u^2 + 54*H^6*k^6*r^6*u
def resStage4Part2 (H k r p u q s : K) : K := 10*H^6*k^4*p^2*r^8*u + 4*H^6*k^4*p*q*r^7*u - 9*H^6*k^4*q^2*r^6*u + 8*H^6*k^4*q*r^5*s*u + 2*H^6*k^4*r^4*s^2*u - 10*H^5*k^8*p*r^7
def resStage4Part3 (H k r p u q s : K) : K := 12*H^5*k^8*q*r^6 - 4*H^5*k^8*r^5*s + 6*H^5*k^6*p^3*r^9 - 6*H^5*k^6*p^2*q*r^8 + 3*H^5*k^6*p*q^2*r^7 + 2*H^5*k^6*p*q*r^6*s
def resStage4Part4 (H k r p u q s : K) : K := -2*H^5*k^6*p*r^5*s^2 - 2*H^5*k^6*q^3*r^6 + 2*H^5*k^6*q^2*r^5*s + 270*H^5*k^6*r^9*u^2 + 6*H^5*k^4*p^2*r^11*u^2 + 6*H^5*k^4*p*q*r^10*u^2
def resStage4Part5 (H k r p u q s : K) : K := -9*H^5*k^4*q^2*r^9*u^2 + 6*H^5*k^4*q*r^8*s*u^2 + 6*H^5*k^4*r^7*s^2*u^2 - 42*H^4*k^8*p*r^10*u + 72*H^4*k^8*q*r^9*u - 30*H^4*k^8*r^8*s*u
def resStage4Part6 (H k r p u q s : K) : K := 14*H^4*k^6*p^3*r^12*u - 12*H^4*k^6*p^2*q*r^11*u + 2*H^4*k^6*p^2*r^10*s*u - 5*H^4*k^6*p*q^2*r^10*u + 12*H^4*k^6*p*q*r^9*s*u - 2*H^4*k^6*p*r^8*s^2*u
def resStage4Part7 (H k r p u q s : K) : K := 4*H^4*k^6*q^3*r^9*u - 7*H^4*k^6*q^2*r^8*s*u + 432*H^4*k^6*r^12*u^3 + 2*H^4*k^6*r^6*s^3*u + 4*H^3*k^12*r^9 - 10*H^3*k^10*p^2*r^11
def resStage4Part8 (H k r p u q s : K) : K := -4*H^3*k^10*p*q*r^10 + 8*H^3*k^10*p*r^9*s + 4*H^3*k^10*q^2*r^9 - 4*H^3*k^10*q*r^8*s + 2*H^3*k^10*r^7*s^2 + 4*H^3*k^8*p^4*r^13
def resStage4Part9 (H k r p u q s : K) : K := -6*H^3*k^8*p^3*q*r^12 + 3*H^3*k^8*p^2*q^2*r^11 + 4*H^3*k^8*p^2*q*r^10*s - 4*H^3*k^8*p^2*r^9*s^2 - 2*H^3*k^8*p*q^3*r^10 + 2*H^3*k^8*p*q*r^8*s^2
def resStage4Part10 (H k r p u q s : K) : K := -36*H^3*k^8*p*r^13*u^2 + H^3*k^8*q^4*r^9 - 2*H^3*k^8*q^3*r^8*s + H^3*k^8*q^2*r^7*s^2 + 72*H^3*k^8*q*r^12*u^2 - 36*H^3*k^8*r^11*s*u^2
def resStage4Part11 (H k r p u q s : K) : K := 8*H^3*k^6*p^3*r^15*u^2 - 6*H^3*k^6*p^2*q*r^14*u^2 - 6*H^3*k^6*p*q^2*r^13*u^2 + 12*H^3*k^6*p*q*r^12*s*u^2 + 4*H^3*k^6*q^3*r^12*u^2 - 6*H^3*k^6*q^2*r^11*s*u^2
def resStage4Part12 (H k r p u q s : K) : K := -6*H^3*k^6*q*r^10*s^2*u^2 + 216*H^3*k^6*r^15*u^4 + 8*H^3*k^6*r^9*s^3*u^2 - 30*H^2*k^10*p^2*r^14*u + 36*H^2*k^10*p*r^12*s*u - 6*H^2*k^10*r^10*s^2*u
def resStage4Part13 (H k r p u q s : K) : K := 7*H^2*k^8*p^4*r^16*u - 12*H^2*k^8*p^3*q*r^15*u + 5*H^2*k^8*p^2*q^2*r^14*u + 8*H^2*k^8*p^2*q*r^13*s*u - 6*H^2*k^8*p^2*r^12*s^2*u - 6*H^2*k^8*p*q^2*r^12*s*u
def resStage4Part14 (H k r p u q s : K) : K := 4*H^2*k^8*p*q*r^11*s^2*u + H^2*k^8*q^2*r^10*s^2*u - H^2*k^8*r^8*s^4*u + 2*H*k^12*p^3*r^15 - 4*H*k^12*p^2*r^13*s + 2*H*k^12*p*r^11*s^2
def resStage4Part15 (H k r p u q s : K) : K := H*k^10*p^5*r^17 - 2*H*k^10*p^4*q*r^16 + H*k^10*p^3*q^2*r^15 + 2*H*k^10*p^3*q*r^14*s - 2*H*k^10*p^3*r^13*s^2 - 2*H*k^10*p^2*q^2*r^13*s
def resStage4Part16 (H k r p u q s : K) : K := 2*H*k^10*p^2*q*r^12*s^2 - 18*H*k^10*p^2*r^17*u^2 + H*k^10*p*q^2*r^11*s^2 - 2*H*k^10*p*q*r^10*s^3 + 36*H*k^10*p*r^15*s*u^2 + H*k^10*p*r^9*s^4
def resStage4Part17 (H k r p u q s : K) : K := -18*H*k^10*r^13*s^2*u^2 + 3*H*k^8*p^4*r^19*u^2 - 6*H*k^8*p^3*q*r^18*u^2 + 3*H*k^8*p^2*q^2*r^17*u^2 + 6*H*k^8*p^2*q*r^16*s*u^2 - 6*H*k^8*p^2*r^15*s^2*u^2
def resStage4Part18 (H k r p u q s : K) : K := -6*H*k^8*p*q^2*r^15*s*u^2 + 6*H*k^8*p*q*r^14*s^2*u^2 + 3*H*k^8*q^2*r^13*s^2*u^2 - 6*H*k^8*q*r^12*s^3*u^2 + 3*H*k^8*r^11*s^4*u^2 + 2*k^12*p^3*r^18*u
def resStage4Part19 (H k r p u q s : K) : K := -6*k^12*p^2*r^16*s*u + 6*k^12*p*r^14*s^2*u - 2*k^12*r^12*s^3*u + k^10*p^5*r^20*u - 2*k^10*p^4*q*r^19*u - k^10*p^4*r^18*s*u
def resStage4Part20 (H k r p u q s : K) : K := k^10*p^3*q^2*r^18*u + 4*k^10*p^3*q*r^17*s*u - 2*k^10*p^3*r^16*s^2*u - 3*k^10*p^2*q^2*r^16*s*u + 2*k^10*p^2*r^14*s^3*u + 3*k^10*p*q^2*r^14*s^2*u
def resStage4Part21 (H k r p u q s : K) : K := -4*k^10*p*q*r^13*s^3*u + k^10*p*r^12*s^4*u - k^10*q^2*r^12*s^3*u + 2*k^10*q*r^11*s^4*u - k^10*r^10*s^5*u
def resStage4 (H k r p u q s : K) : K := resStage4Part0 H k r p u q s + resStage4Part1 H k r p u q s + resStage4Part2 H k r p u q s + resStage4Part3 H k r p u q s + resStage4Part4 H k r p u q s + resStage4Part5 H k r p u q s + resStage4Part6 H k r p u q s + resStage4Part7 H k r p u q s + resStage4Part8 H k r p u q s + resStage4Part9 H k r p u q s + resStage4Part10 H k r p u q s + resStage4Part11 H k r p u q s + resStage4Part12 H k r p u q s + resStage4Part13 H k r p u q s + resStage4Part14 H k r p u q s + resStage4Part15 H k r p u q s + resStage4Part16 H k r p u q s + resStage4Part17 H k r p u q s + resStage4Part18 H k r p u q s + resStage4Part19 H k r p u q s + resStage4Part20 H k r p u q s + resStage4Part21 H k r p u q s

theorem resultant_stage1 (A B F H k r p u : K) :
    QuadricContact.Subresultant.resultant (2*H*A) (k^2*r*F) (k^4*r^2*H)
      (A^2+2*k^6*r^6) (2*k^2*r*A*B) (k^4*r^2*(B^2+p*k^2*r^4)) (u*k^6*r^6)
    = k^12*r^6*resStage1 A B F H k r p u := by
  unfold QuadricContact.Subresultant.resultant resStage1 resStage1Part0 resStage1Part1 resStage1Part2 resStage1Part3 resStage1Part4
  ring

 theorem resultant_stage2 (A H k r p u q : K) :
    resStage1 A (H+3*u*r^3) (A+2*H*(H+3*u*r^3)+k^2*r^3*(q-2*p*r)) H k r p u
    = r^3*resStage3 A H k r p u q := by
  unfold resStage1 resStage1Part0 resStage1Part1 resStage1Part2 resStage1Part3 resStage1Part4 resStage3 resStage3Part0 resStage3Part1 resStage3Part2 resStage3Part3 resStage3Part4 resStage3Part5 resStage3Part6 resStage3Part7 resStage3Part8 resStage3Part9 resStage3Part10 resStage3Part11 resStage3Part12 resStage3Part13
  ring

 theorem resultant_stage3 (H k r p u q s : K) :
    resStage3 (H^2+k^2*r^2*(p*r^2-q*r+s)) H k r p u q
    = resStage4 H k r p u q s := by
  unfold resStage3 resStage3Part0 resStage3Part1 resStage3Part2 resStage3Part3 resStage3Part4 resStage3Part5 resStage3Part6 resStage3Part7 resStage3Part8 resStage3Part9 resStage3Part10 resStage3Part11 resStage3Part12 resStage3Part13 resStage4 resStage4Part0 resStage4Part1 resStage4Part2 resStage4Part3 resStage4Part4 resStage4Part5 resStage4Part6 resStage4Part7 resStage4Part8 resStage4Part9 resStage4Part10 resStage4Part11 resStage4Part12 resStage4Part13 resStage4Part14 resStage4Part15 resStage4Part16 resStage4Part17 resStage4Part18 resStage4Part19 resStage4Part20 resStage4Part21
  ring

 theorem resultant_stage4 (k r p u q s v : K) :
    resStage4 (v-u*r^3) k r p u q s = eliminant r p q s k u v := by
  unfold resStage4 resStage4Part0 resStage4Part1 resStage4Part2 resStage4Part3 resStage4Part4 resStage4Part5 resStage4Part6 resStage4Part7 resStage4Part8 resStage4Part9 resStage4Part10 resStage4Part11 resStage4Part12 resStage4Part13 resStage4Part14 resStage4Part15 resStage4Part16 resStage4Part17 resStage4Part18 resStage4Part19 resStage4Part20 resStage4Part21 eliminant eliminantCoeff0 eliminantCoeff1 eliminantCoeff2 eliminantCoeff3 eliminantCoeff4 eliminantCoeff5 eliminantCoeff6 eliminantCoeff7 eliminantCoeff8 eliminantCoeff9 eliminantCoeff10 eliminantCoeff11 eliminantCoeff12 eliminantCoeff13 eliminantCoeff14 eliminantCoeff15 eliminantCoeff16 eliminantCoeff17 eliminantCoeff18 eliminantCoeff19 eliminantCoeff20 eliminantCoeff21 eliminantCoeff22 eliminantCoeff23 eliminantCoeff24 eliminantCoeff25 eliminantCoeff26 eliminantCoeff27
  ring

theorem eliminant_identity (r p q s k u v : K) :
    QuadricContact.Subresultant.resultant
      (qa r p q s k u v) (qb r p s k u v) (qc r k u v)
      (cd r p q s k u v) (ce r p q s k u v)
      (cf r p k u v) (cg r k u)
    = k^12*r^9*eliminant r p q s k u v := by
  let H := hNum r u v
  let A := aa r p q s k u v
  let B := bb r u v
  let F := 2*H*B+H^2+k^2*r^2*(s-p*r^2)
  have hB : B=H+3*u*r^3 := by dsimp [B,H,bb,hNum]; ring
  have hF : F=A+2*H*B+k^2*r^3*(q-2*p*r) := by
    dsimp [F,A,H,aa,hNum]
    ring
  change QuadricContact.Subresultant.resultant (2*H*A) (k^2*r*F) (k^4*r^2*H)
      (A^2+2*k^6*r^6) (2*k^2*r*A*B) (k^4*r^2*(B^2+p*k^2*r^4)) (u*k^6*r^6)
    = k^12*r^9*eliminant r p q s k u v
  rw [resultant_stage1, hF, hB, resultant_stage2]
  have hA : A=H^2+k^2*r^2*(p*r^2-q*r+s) := rfl
  rw [hA, resultant_stage3]
  change k^12*r^6*(r^3*resStage4 (v-u*r^3) k r p u q s) = _
  rw [resultant_stage4]
  ring

end GenericLineChart
#print axioms GenericLineChart.eliminant_identity

