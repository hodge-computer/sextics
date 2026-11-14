import Proposal.GeometricFormalInputs01Part01

/-! Continuation of GeometricFormalInputs01.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: higgs/FermatHiggs.lean -/
section
/-!
Exact scalar-commutant theorem for all 35 Fermat Higgs forms.
The proof uses a spanning forest of the entry-equality constraints. Every
edge below is checked as a literal instance of the supplied matrix equation.
The theorem applies over any semiring; no modular rank inference is used.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CycleQ2FermatHiggs
open scoped BigOperators

def entryConstraints {K : Type*} [Zero K] (P : Matrix (Fin 33) (Fin 33) K) : Prop :=
  ∀ m : Fin 35, ∀ i j : Fin 33,
    (match complement m j with | none => 0 | some k => P k i) =
    (match complement m i with | none => 0 | some k => P k j)

theorem scalar_of_entryConstraints {K : Type*} [Zero K]
    (P : Matrix (Fin 33) (Fin 33) K) (h : entryConstraints P) :
    ∃ c : K, ∀ i j, P i j = if i = j then c else 0 := by
  have h0 : P 0 0 = P 0 0 := rfl
  have h1023 : P 31 0 = 0 := (h 0 0 10)
  have h957 : P 29 0 = 0 := (h 0 0 18)
  have h825 : P 25 0 = 0 := (h 0 0 25)
  have h594 : P 18 0 = 0 := (h 0 0 29)
  have h330 : P 10 0 = 0 := (h 0 0 31)
  have h1024 : P 31 1 = 0 := (h 0 1 10)
  have h958 : P 29 1 = 0 := (h 0 1 18)
  have h826 : P 25 1 = 0 := (h 0 1 25)
  have h595 : P 18 1 = 0 := (h 0 1 29)
  have h331 : P 10 1 = 0 := (h 0 1 31)
  have h1025 : P 31 2 = 0 := (h 0 2 10)
  have h959 : P 29 2 = 0 := (h 0 2 18)
  have h827 : P 25 2 = 0 := (h 0 2 25)
  have h596 : P 18 2 = 0 := (h 0 2 29)
  have h332 : P 10 2 = 0 := (h 0 2 31)
  have h1026 : P 31 3 = 0 := (h 0 3 10)
  have h960 : P 29 3 = 0 := (h 0 3 18)
  have h828 : P 25 3 = 0 := (h 0 3 25)
  have h597 : P 18 3 = 0 := (h 0 3 29)
  have h333 : P 10 3 = 0 := (h 0 3 31)
  have h1027 : P 31 4 = 0 := (h 0 4 10)
  have h961 : P 29 4 = 0 := (h 0 4 18)
  have h829 : P 25 4 = 0 := (h 0 4 25)
  have h598 : P 18 4 = 0 := (h 0 4 29)
  have h334 : P 10 4 = 0 := (h 0 4 31)
  have h1028 : P 31 5 = 0 := (h 0 5 10)
  have h962 : P 29 5 = 0 := (h 0 5 18)
  have h830 : P 25 5 = 0 := (h 0 5 25)
  have h599 : P 18 5 = 0 := (h 0 5 29)
  have h335 : P 10 5 = 0 := (h 0 5 31)
  have h1029 : P 31 6 = 0 := (h 0 6 10)
  have h963 : P 29 6 = 0 := (h 0 6 18)
  have h831 : P 25 6 = 0 := (h 0 6 25)
  have h600 : P 18 6 = 0 := (h 0 6 29)
  have h336 : P 10 6 = 0 := (h 0 6 31)
  have h1030 : P 31 7 = 0 := (h 0 7 10)
  have h964 : P 29 7 = 0 := (h 0 7 18)
  have h832 : P 25 7 = 0 := (h 0 7 25)
  have h601 : P 18 7 = 0 := (h 0 7 29)
  have h337 : P 10 7 = 0 := (h 0 7 31)
  have h1031 : P 31 8 = 0 := (h 0 8 10)
  have h965 : P 29 8 = 0 := (h 0 8 18)
  have h833 : P 25 8 = 0 := (h 0 8 25)
  have h602 : P 18 8 = 0 := (h 0 8 29)
  have h338 : P 10 8 = 0 := (h 0 8 31)
  have h1032 : P 31 9 = 0 := (h 0 9 10)
  have h966 : P 29 9 = 0 := (h 0 9 18)
  have h834 : P 25 9 = 0 := (h 0 9 25)
  have h603 : P 18 9 = 0 := (h 0 9 29)
  have h339 : P 10 9 = 0 := (h 0 9 31)
  have h1034 : P 31 11 = 0 := (h 0 10 11).symm
  have h1035 : P 31 12 = 0 := (h 0 10 12).symm
  have h1036 : P 31 13 = 0 := (h 0 10 13).symm
  have h1037 : P 31 14 = 0 := (h 0 10 14).symm
  have h1038 : P 31 15 = 0 := (h 0 10 15).symm
  have h1039 : P 31 16 = 0 := (h 0 10 16).symm
  have h1040 : P 31 17 = 0 := (h 0 10 17).symm
  have h1042 : P 31 19 = 0 := (h 0 10 19).symm
  have h1043 : P 31 20 = 0 := (h 0 10 20).symm
  have h1044 : P 31 21 = 0 := (h 0 10 21).symm
  have h1045 : P 31 22 = 0 := (h 0 10 22).symm
  have h1046 : P 31 23 = 0 := (h 0 10 23).symm
  have h1047 : P 31 24 = 0 := (h 0 10 24).symm
  have h1049 : P 31 26 = 0 := (h 0 10 26).symm
  have h1050 : P 31 27 = 0 := (h 0 10 27).symm
  have h1051 : P 31 28 = 0 := (h 0 10 28).symm
  have h1053 : P 31 30 = 0 := (h 0 10 30).symm
  have h1055 : P 31 32 = 0 := (h 0 10 32).symm
  have h968 : P 29 11 = 0 := (h 0 11 18)
  have h836 : P 25 11 = 0 := (h 0 11 25)
  have h605 : P 18 11 = 0 := (h 0 11 29)
  have h341 : P 10 11 = 0 := (h 0 11 31)
  have h969 : P 29 12 = 0 := (h 0 12 18)
  have h837 : P 25 12 = 0 := (h 0 12 25)
  have h606 : P 18 12 = 0 := (h 0 12 29)
  have h342 : P 10 12 = 0 := (h 0 12 31)
  have h970 : P 29 13 = 0 := (h 0 13 18)
  have h838 : P 25 13 = 0 := (h 0 13 25)
  have h607 : P 18 13 = 0 := (h 0 13 29)
  have h343 : P 10 13 = 0 := (h 0 13 31)
  have h971 : P 29 14 = 0 := (h 0 14 18)
  have h839 : P 25 14 = 0 := (h 0 14 25)
  have h608 : P 18 14 = 0 := (h 0 14 29)
  have h344 : P 10 14 = 0 := (h 0 14 31)
  have h972 : P 29 15 = 0 := (h 0 15 18)
  have h840 : P 25 15 = 0 := (h 0 15 25)
  have h609 : P 18 15 = 0 := (h 0 15 29)
  have h345 : P 10 15 = 0 := (h 0 15 31)
  have h973 : P 29 16 = 0 := (h 0 16 18)
  have h841 : P 25 16 = 0 := (h 0 16 25)
  have h610 : P 18 16 = 0 := (h 0 16 29)
  have h346 : P 10 16 = 0 := (h 0 16 31)
  have h974 : P 29 17 = 0 := (h 0 17 18)
  have h842 : P 25 17 = 0 := (h 0 17 25)
  have h611 : P 18 17 = 0 := (h 0 17 29)
  have h347 : P 10 17 = 0 := (h 0 17 31)
  have h976 : P 29 19 = 0 := (h 0 18 19).symm
  have h977 : P 29 20 = 0 := (h 0 18 20).symm
  have h978 : P 29 21 = 0 := (h 0 18 21).symm
  have h979 : P 29 22 = 0 := (h 0 18 22).symm
  have h980 : P 29 23 = 0 := (h 0 18 23).symm
  have h981 : P 29 24 = 0 := (h 0 18 24).symm
  have h983 : P 29 26 = 0 := (h 0 18 26).symm
  have h984 : P 29 27 = 0 := (h 0 18 27).symm
  have h985 : P 29 28 = 0 := (h 0 18 28).symm
  have h987 : P 29 30 = 0 := (h 0 18 30).symm
  have h989 : P 29 32 = 0 := (h 0 18 32).symm
  have h844 : P 25 19 = 0 := (h 0 19 25)
  have h613 : P 18 19 = 0 := (h 0 19 29)
  have h349 : P 10 19 = 0 := (h 0 19 31)
  have h845 : P 25 20 = 0 := (h 0 20 25)
  have h614 : P 18 20 = 0 := (h 0 20 29)
  have h350 : P 10 20 = 0 := (h 0 20 31)
  have h846 : P 25 21 = 0 := (h 0 21 25)
  have h615 : P 18 21 = 0 := (h 0 21 29)
  have h351 : P 10 21 = 0 := (h 0 21 31)
  have h847 : P 25 22 = 0 := (h 0 22 25)
  have h616 : P 18 22 = 0 := (h 0 22 29)
  have h352 : P 10 22 = 0 := (h 0 22 31)
  have h848 : P 25 23 = 0 := (h 0 23 25)
  have h617 : P 18 23 = 0 := (h 0 23 29)
  have h353 : P 10 23 = 0 := (h 0 23 31)
  have h849 : P 25 24 = 0 := (h 0 24 25)
  have h618 : P 18 24 = 0 := (h 0 24 29)
  have h354 : P 10 24 = 0 := (h 0 24 31)
  have h851 : P 25 26 = 0 := (h 0 25 26).symm
  have h852 : P 25 27 = 0 := (h 0 25 27).symm
  have h853 : P 25 28 = 0 := (h 0 25 28).symm
  have h855 : P 25 30 = 0 := (h 0 25 30).symm
  have h857 : P 25 32 = 0 := (h 0 25 32).symm
  have h620 : P 18 26 = 0 := (h 0 26 29)
  have h356 : P 10 26 = 0 := (h 0 26 31)
  have h621 : P 18 27 = 0 := (h 0 27 29)
  have h357 : P 10 27 = 0 := (h 0 27 31)
  have h622 : P 18 28 = 0 := (h 0 28 29)
  have h358 : P 10 28 = 0 := (h 0 28 31)
  have h624 : P 18 30 = 0 := (h 0 29 30).symm
  have h626 : P 18 32 = 0 := (h 0 29 32).symm
  have h360 : P 10 30 = 0 := (h 0 30 31)
  have h362 : P 10 32 = 0 := (h 0 31 32).symm
  have h1056 : P 32 0 = 0 := (h 1 0 9)
  have h990 : P 30 0 = 0 := (h 1 0 17)
  have h924 : P 28 0 = 0 := (h 1 0 19)
  have h858 : P 26 0 = 0 := (h 1 0 24)
  have h792 : P 24 0 = 0 := (h 1 0 26)
  have h627 : P 19 0 = 0 := (h 1 0 28)
  have h561 : P 17 0 = 0 := (h 1 0 30)
  have h297 : P 9 0 = 0 := (h 1 0 32)
  have h1057 : P 32 1 = 0 := (h 1 1 9)
  have h991 : P 30 1 = 0 := (h 1 1 17)
  have h925 : P 28 1 = 0 := (h 1 1 19)
  have h859 : P 26 1 = 0 := (h 1 1 24)
  have h793 : P 24 1 = 0 := (h 1 1 26)
  have h628 : P 19 1 = 0 := (h 1 1 28)
  have h562 : P 17 1 = 0 := (h 1 1 30)
  have h298 : P 9 1 = 0 := (h 1 1 32)
  have h1058 : P 32 2 = 0 := (h 1 2 9)
  have h992 : P 30 2 = 0 := (h 1 2 17)
  have h926 : P 28 2 = 0 := (h 1 2 19)
  have h860 : P 26 2 = 0 := (h 1 2 24)
  have h794 : P 24 2 = 0 := (h 1 2 26)
  have h629 : P 19 2 = 0 := (h 1 2 28)
  have h563 : P 17 2 = 0 := (h 1 2 30)
  have h299 : P 9 2 = 0 := (h 1 2 32)
  have h1059 : P 32 3 = 0 := (h 1 3 9)
  have h993 : P 30 3 = 0 := (h 1 3 17)
  have h927 : P 28 3 = 0 := (h 1 3 19)
  have h861 : P 26 3 = 0 := (h 1 3 24)
  have h795 : P 24 3 = 0 := (h 1 3 26)
  have h630 : P 19 3 = 0 := (h 1 3 28)
  have h564 : P 17 3 = 0 := (h 1 3 30)
  have h300 : P 9 3 = 0 := (h 1 3 32)
  have h1060 : P 32 4 = 0 := (h 1 4 9)
  have h994 : P 30 4 = 0 := (h 1 4 17)
  have h928 : P 28 4 = 0 := (h 1 4 19)
  have h862 : P 26 4 = 0 := (h 1 4 24)
  have h796 : P 24 4 = 0 := (h 1 4 26)
  have h631 : P 19 4 = 0 := (h 1 4 28)
  have h565 : P 17 4 = 0 := (h 1 4 30)
  have h301 : P 9 4 = 0 := (h 1 4 32)
  have h1061 : P 32 5 = 0 := (h 1 5 9)
  have h995 : P 30 5 = 0 := (h 1 5 17)
  have h929 : P 28 5 = 0 := (h 1 5 19)
  have h863 : P 26 5 = 0 := (h 1 5 24)
  have h797 : P 24 5 = 0 := (h 1 5 26)
  have h632 : P 19 5 = 0 := (h 1 5 28)
  have h566 : P 17 5 = 0 := (h 1 5 30)
  have h302 : P 9 5 = 0 := (h 1 5 32)
  have h1062 : P 32 6 = 0 := (h 1 6 9)
  have h996 : P 30 6 = 0 := (h 1 6 17)
  have h930 : P 28 6 = 0 := (h 1 6 19)
  have h864 : P 26 6 = 0 := (h 1 6 24)
  have h798 : P 24 6 = 0 := (h 1 6 26)
  have h633 : P 19 6 = 0 := (h 1 6 28)
  have h567 : P 17 6 = 0 := (h 1 6 30)
  have h303 : P 9 6 = 0 := (h 1 6 32)
  have h1063 : P 32 7 = 0 := (h 1 7 9)
  have h997 : P 30 7 = 0 := (h 1 7 17)
  have h931 : P 28 7 = 0 := (h 1 7 19)
  have h865 : P 26 7 = 0 := (h 1 7 24)
  have h799 : P 24 7 = 0 := (h 1 7 26)
  have h634 : P 19 7 = 0 := (h 1 7 28)
  have h568 : P 17 7 = 0 := (h 1 7 30)
  have h304 : P 9 7 = 0 := (h 1 7 32)
  have h1064 : P 32 8 = 0 := (h 1 8 9)
  have h998 : P 30 8 = 0 := (h 1 8 17)
  have h932 : P 28 8 = 0 := (h 1 8 19)
  have h866 : P 26 8 = 0 := (h 1 8 24)
  have h800 : P 24 8 = 0 := (h 1 8 26)
  have h635 : P 19 8 = 0 := (h 1 8 28)
  have h569 : P 17 8 = 0 := (h 1 8 30)
  have h305 : P 9 8 = 0 := (h 1 8 32)
  have h1066 : P 32 10 = 0 := (h 1 9 10).symm
  have h1067 : P 32 11 = 0 := (h 1 9 11).symm
  have h1068 : P 32 12 = 0 := (h 1 9 12).symm
  have h1069 : P 32 13 = 0 := (h 1 9 13).symm
  have h1070 : P 32 14 = 0 := (h 1 9 14).symm
  have h1071 : P 32 15 = 0 := (h 1 9 15).symm
  have h1072 : P 32 16 = 0 := (h 1 9 16).symm
  have h1074 : P 32 18 = 0 := (h 1 9 18).symm
  have h1076 : P 32 20 = 0 := (h 1 9 20).symm
  have h1077 : P 32 21 = 0 := (h 1 9 21).symm
  have h1078 : P 32 22 = 0 := (h 1 9 22).symm
  have h1079 : P 32 23 = 0 := (h 1 9 23).symm
  have h1081 : P 32 25 = 0 := (h 1 9 25).symm
  have h1083 : P 32 27 = 0 := (h 1 9 27).symm
  have h1085 : P 32 29 = 0 := (h 1 9 29).symm
  have h1087 : P 32 31 = 0 := (h 1 9 31).symm
  have h1000 : P 30 10 = 0 := (h 1 10 17)
  have h934 : P 28 10 = 0 := (h 1 10 19)
  have h868 : P 26 10 = 0 := (h 1 10 24)
  have h802 : P 24 10 = 0 := (h 1 10 26)
  have h637 : P 19 10 = 0 := (h 1 10 28)
  have h571 : P 17 10 = 0 := (h 1 10 30)
  have h307 : P 9 10 = 0 := (h 1 10 32)
  have h1001 : P 30 11 = 0 := (h 1 11 17)
  have h935 : P 28 11 = 0 := (h 1 11 19)
  have h869 : P 26 11 = 0 := (h 1 11 24)
  have h803 : P 24 11 = 0 := (h 1 11 26)
  have h638 : P 19 11 = 0 := (h 1 11 28)
  have h572 : P 17 11 = 0 := (h 1 11 30)
  have h308 : P 9 11 = 0 := (h 1 11 32)
  have h1002 : P 30 12 = 0 := (h 1 12 17)
  have h936 : P 28 12 = 0 := (h 1 12 19)
  have h870 : P 26 12 = 0 := (h 1 12 24)
  have h804 : P 24 12 = 0 := (h 1 12 26)
  have h639 : P 19 12 = 0 := (h 1 12 28)
  have h573 : P 17 12 = 0 := (h 1 12 30)
  have h309 : P 9 12 = 0 := (h 1 12 32)
  have h1003 : P 30 13 = 0 := (h 1 13 17)
  have h937 : P 28 13 = 0 := (h 1 13 19)
  have h871 : P 26 13 = 0 := (h 1 13 24)
  have h805 : P 24 13 = 0 := (h 1 13 26)
  have h640 : P 19 13 = 0 := (h 1 13 28)
  have h574 : P 17 13 = 0 := (h 1 13 30)
  have h310 : P 9 13 = 0 := (h 1 13 32)
  have h1004 : P 30 14 = 0 := (h 1 14 17)
  have h938 : P 28 14 = 0 := (h 1 14 19)
  have h872 : P 26 14 = 0 := (h 1 14 24)
  have h806 : P 24 14 = 0 := (h 1 14 26)
  have h641 : P 19 14 = 0 := (h 1 14 28)
  have h575 : P 17 14 = 0 := (h 1 14 30)
  have h311 : P 9 14 = 0 := (h 1 14 32)
  have h1005 : P 30 15 = 0 := (h 1 15 17)
  have h939 : P 28 15 = 0 := (h 1 15 19)
  have h873 : P 26 15 = 0 := (h 1 15 24)
  have h807 : P 24 15 = 0 := (h 1 15 26)
  have h642 : P 19 15 = 0 := (h 1 15 28)
  have h576 : P 17 15 = 0 := (h 1 15 30)
  have h312 : P 9 15 = 0 := (h 1 15 32)
  have h1006 : P 30 16 = 0 := (h 1 16 17)
  have h940 : P 28 16 = 0 := (h 1 16 19)
  have h874 : P 26 16 = 0 := (h 1 16 24)
  have h808 : P 24 16 = 0 := (h 1 16 26)
  have h643 : P 19 16 = 0 := (h 1 16 28)
  have h577 : P 17 16 = 0 := (h 1 16 30)
  have h313 : P 9 16 = 0 := (h 1 16 32)
  have h1008 : P 30 18 = 0 := (h 1 17 18).symm
  have h1010 : P 30 20 = 0 := (h 1 17 20).symm
  have h1011 : P 30 21 = 0 := (h 1 17 21).symm
  have h1012 : P 30 22 = 0 := (h 1 17 22).symm
  have h1013 : P 30 23 = 0 := (h 1 17 23).symm
  have h1015 : P 30 25 = 0 := (h 1 17 25).symm
  have h1017 : P 30 27 = 0 := (h 1 17 27).symm
  have h1019 : P 30 29 = 0 := (h 1 17 29).symm
  have h1021 : P 30 31 = 0 := (h 1 17 31).symm
  have h942 : P 28 18 = 0 := (h 1 18 19)
  have h876 : P 26 18 = 0 := (h 1 18 24)
  have h810 : P 24 18 = 0 := (h 1 18 26)
  have h645 : P 19 18 = 0 := (h 1 18 28)
  have h579 : P 17 18 = 0 := (h 1 18 30)
  have h315 : P 9 18 = 0 := (h 1 18 32)
  have h944 : P 28 20 = 0 := (h 1 19 20).symm
  have h945 : P 28 21 = 0 := (h 1 19 21).symm
  have h946 : P 28 22 = 0 := (h 1 19 22).symm
  have h947 : P 28 23 = 0 := (h 1 19 23).symm
  have h949 : P 28 25 = 0 := (h 1 19 25).symm
  have h951 : P 28 27 = 0 := (h 1 19 27).symm
  have h953 : P 28 29 = 0 := (h 1 19 29).symm
  have h955 : P 28 31 = 0 := (h 1 19 31).symm
  have h878 : P 26 20 = 0 := (h 1 20 24)
  have h812 : P 24 20 = 0 := (h 1 20 26)
  have h647 : P 19 20 = 0 := (h 1 20 28)
  have h581 : P 17 20 = 0 := (h 1 20 30)
  have h317 : P 9 20 = 0 := (h 1 20 32)
  have h879 : P 26 21 = 0 := (h 1 21 24)
  have h813 : P 24 21 = 0 := (h 1 21 26)
  have h648 : P 19 21 = 0 := (h 1 21 28)
  have h582 : P 17 21 = 0 := (h 1 21 30)
  have h318 : P 9 21 = 0 := (h 1 21 32)
  have h880 : P 26 22 = 0 := (h 1 22 24)
  have h814 : P 24 22 = 0 := (h 1 22 26)
  have h649 : P 19 22 = 0 := (h 1 22 28)
  have h583 : P 17 22 = 0 := (h 1 22 30)
  have h319 : P 9 22 = 0 := (h 1 22 32)
  have h881 : P 26 23 = 0 := (h 1 23 24)
  have h815 : P 24 23 = 0 := (h 1 23 26)
  have h650 : P 19 23 = 0 := (h 1 23 28)
  have h584 : P 17 23 = 0 := (h 1 23 30)
  have h320 : P 9 23 = 0 := (h 1 23 32)
  have h883 : P 26 25 = 0 := (h 1 24 25).symm
  have h885 : P 26 27 = 0 := (h 1 24 27).symm
  have h887 : P 26 29 = 0 := (h 1 24 29).symm
  have h889 : P 26 31 = 0 := (h 1 24 31).symm
  have h817 : P 24 25 = 0 := (h 1 25 26)
  have h652 : P 19 25 = 0 := (h 1 25 28)
  have h586 : P 17 25 = 0 := (h 1 25 30)
  have h322 : P 9 25 = 0 := (h 1 25 32)
  have h819 : P 24 27 = 0 := (h 1 26 27).symm
  have h821 : P 24 29 = 0 := (h 1 26 29).symm
  have h823 : P 24 31 = 0 := (h 1 26 31).symm
  have h654 : P 19 27 = 0 := (h 1 27 28)
  have h588 : P 17 27 = 0 := (h 1 27 30)
  have h324 : P 9 27 = 0 := (h 1 27 32)
  have h656 : P 19 29 = 0 := (h 1 28 29).symm
  have h658 : P 19 31 = 0 := (h 1 28 31).symm
  have h590 : P 17 29 = 0 := (h 1 29 30)
  have h326 : P 9 29 = 0 := (h 1 29 32)
  have h592 : P 17 31 = 0 := (h 1 30 31).symm
  have h328 : P 9 31 = 0 := (h 1 31 32)
  have h891 : P 27 0 = 0 := (h 2 0 19)
  have h759 : P 23 0 = 0 := (h 2 0 26)
  have h528 : P 16 0 = 0 := (h 2 0 30)
  have h264 : P 8 0 = 0 := (h 2 0 32)
  have h892 : P 27 1 = 0 := (h 2 1 19)
  have h760 : P 23 1 = 0 := (h 2 1 26)
  have h529 : P 16 1 = 0 := (h 2 1 30)
  have h265 : P 8 1 = 0 := (h 2 1 32)
  have h893 : P 27 2 = 0 := (h 2 2 19)
  have h761 : P 23 2 = 0 := (h 2 2 26)
  have h530 : P 16 2 = 0 := (h 2 2 30)
  have h266 : P 8 2 = 0 := (h 2 2 32)
  have h894 : P 27 3 = 0 := (h 2 3 19)
  have h762 : P 23 3 = 0 := (h 2 3 26)
  have h531 : P 16 3 = 0 := (h 2 3 30)
  have h267 : P 8 3 = 0 := (h 2 3 32)
  have h895 : P 27 4 = 0 := (h 2 4 19)
  have h763 : P 23 4 = 0 := (h 2 4 26)
  have h532 : P 16 4 = 0 := (h 2 4 30)
  have h268 : P 8 4 = 0 := (h 2 4 32)
  have h896 : P 27 5 = 0 := (h 2 5 19)
  have h764 : P 23 5 = 0 := (h 2 5 26)
  have h533 : P 16 5 = 0 := (h 2 5 30)
  have h269 : P 8 5 = 0 := (h 2 5 32)
  have h897 : P 27 6 = 0 := (h 2 6 19)
  have h765 : P 23 6 = 0 := (h 2 6 26)
  have h534 : P 16 6 = 0 := (h 2 6 30)
  have h270 : P 8 6 = 0 := (h 2 6 32)
  have h898 : P 27 7 = 0 := (h 2 7 19)
  have h766 : P 23 7 = 0 := (h 2 7 26)
  have h535 : P 16 7 = 0 := (h 2 7 30)
  have h271 : P 8 7 = 0 := (h 2 7 32)
  have h1065 : P 32 9 = 0 := (h 2 8 9).symm
  have h1073 : P 32 17 = 0 := (h 2 8 17).symm
  have h1080 : P 32 24 = 0 := (h 2 8 24).symm
  have h1084 : P 32 28 = 0 := (h 2 8 28).symm
  have h999 : P 30 9 = 0 := (h 2 9 16)
  have h900 : P 27 9 = 0 := (h 2 9 19)
  have h867 : P 26 9 = 0 := (h 2 9 23)
  have h768 : P 23 9 = 0 := (h 2 9 26)
  have h636 : P 19 9 = 0 := (h 2 9 27)
  have h537 : P 16 9 = 0 := (h 2 9 30)
  have h273 : P 8 9 = 0 := (h 2 9 32)
  have h901 : P 27 10 = 0 := (h 2 10 19)
  have h769 : P 23 10 = 0 := (h 2 10 26)
  have h538 : P 16 10 = 0 := (h 2 10 30)
  have h274 : P 8 10 = 0 := (h 2 10 32)
  have h902 : P 27 11 = 0 := (h 2 11 19)
  have h770 : P 23 11 = 0 := (h 2 11 26)
  have h539 : P 16 11 = 0 := (h 2 11 30)
  have h275 : P 8 11 = 0 := (h 2 11 32)
  have h903 : P 27 12 = 0 := (h 2 12 19)
  have h771 : P 23 12 = 0 := (h 2 12 26)
  have h540 : P 16 12 = 0 := (h 2 12 30)
  have h276 : P 8 12 = 0 := (h 2 12 32)
  have h904 : P 27 13 = 0 := (h 2 13 19)
  have h772 : P 23 13 = 0 := (h 2 13 26)
  have h541 : P 16 13 = 0 := (h 2 13 30)
  have h277 : P 8 13 = 0 := (h 2 13 32)
  have h905 : P 27 14 = 0 := (h 2 14 19)
  have h773 : P 23 14 = 0 := (h 2 14 26)
  have h542 : P 16 14 = 0 := (h 2 14 30)
  have h278 : P 8 14 = 0 := (h 2 14 32)
  have h906 : P 27 15 = 0 := (h 2 15 19)
  have h774 : P 23 15 = 0 := (h 2 15 26)
  have h543 : P 16 15 = 0 := (h 2 15 30)
  have h279 : P 8 15 = 0 := (h 2 15 32)
  have h1007 : P 30 17 = 0 := (h 2 16 17).symm
  have h1014 : P 30 24 = 0 := (h 2 16 24).symm
  have h1018 : P 30 28 = 0 := (h 2 16 28).symm
  have h908 : P 27 17 = 0 := (h 2 17 19)
  have h875 : P 26 17 = 0 := (h 2 17 23)
  have h776 : P 23 17 = 0 := (h 2 17 26)
  have h644 : P 19 17 = 0 := (h 2 17 27)
  have h545 : P 16 17 = 0 := (h 2 17 30)
  have h281 : P 8 17 = 0 := (h 2 17 32)
  have h909 : P 27 18 = 0 := (h 2 18 19)
  have h777 : P 23 18 = 0 := (h 2 18 26)
  have h546 : P 16 18 = 0 := (h 2 18 30)
  have h282 : P 8 18 = 0 := (h 2 18 32)
  have h911 : P 27 20 = 0 := (h 2 19 20).symm
  have h912 : P 27 21 = 0 := (h 2 19 21).symm
  have h913 : P 27 22 = 0 := (h 2 19 22).symm
  have h915 : P 27 24 = 0 := (h 2 19 24).symm
  have h916 : P 27 25 = 0 := (h 2 19 25).symm
  have h919 : P 27 28 = 0 := (h 2 19 28).symm
  have h920 : P 27 29 = 0 := (h 2 19 29).symm
  have h922 : P 27 31 = 0 := (h 2 19 31).symm
  have h779 : P 23 20 = 0 := (h 2 20 26)
  have h548 : P 16 20 = 0 := (h 2 20 30)
  have h284 : P 8 20 = 0 := (h 2 20 32)
  have h780 : P 23 21 = 0 := (h 2 21 26)
  have h549 : P 16 21 = 0 := (h 2 21 30)
  have h285 : P 8 21 = 0 := (h 2 21 32)
  have h781 : P 23 22 = 0 := (h 2 22 26)
  have h550 : P 16 22 = 0 := (h 2 22 30)
  have h286 : P 8 22 = 0 := (h 2 22 32)
  have h882 : P 26 24 = 0 := (h 2 23 24).symm
  have h886 : P 26 28 = 0 := (h 2 23 28).symm
  have h783 : P 23 24 = 0 := (h 2 24 26)
  have h651 : P 19 24 = 0 := (h 2 24 27)
  have h552 : P 16 24 = 0 := (h 2 24 30)
  have h288 : P 8 24 = 0 := (h 2 24 32)
  have h784 : P 23 25 = 0 := (h 2 25 26)
  have h553 : P 16 25 = 0 := (h 2 25 30)
  have h289 : P 8 25 = 0 := (h 2 25 32)
  have h787 : P 23 28 = 0 := (h 2 26 28).symm
  have h788 : P 23 29 = 0 := (h 2 26 29).symm
  have h790 : P 23 31 = 0 := (h 2 26 31).symm
  have h655 : P 19 28 = 0 := (h 2 27 28).symm
  have h556 : P 16 28 = 0 := (h 2 28 30)
  have h292 : P 8 28 = 0 := (h 2 28 32)
  have h557 : P 16 29 = 0 := (h 2 29 30)
  have h293 : P 8 29 = 0 := (h 2 29 32)
  have h559 : P 16 31 = 0 := (h 2 30 31).symm
  have h295 : P 8 31 = 0 := (h 2 31 32)
  have h726 : P 22 0 = 0 := (h 3 0 26)
  have h495 : P 15 0 = 0 := (h 3 0 30)
  have h231 : P 7 0 = 0 := (h 3 0 32)
  have h727 : P 22 1 = 0 := (h 3 1 26)
  have h496 : P 15 1 = 0 := (h 3 1 30)
  have h232 : P 7 1 = 0 := (h 3 1 32)
  have h728 : P 22 2 = 0 := (h 3 2 26)
  have h497 : P 15 2 = 0 := (h 3 2 30)
  have h233 : P 7 2 = 0 := (h 3 2 32)
  have h729 : P 22 3 = 0 := (h 3 3 26)
  have h498 : P 15 3 = 0 := (h 3 3 30)
  have h234 : P 7 3 = 0 := (h 3 3 32)
  have h730 : P 22 4 = 0 := (h 3 4 26)
  have h499 : P 15 4 = 0 := (h 3 4 30)
  have h235 : P 7 4 = 0 := (h 3 4 32)
  have h731 : P 22 5 = 0 := (h 3 5 26)
  have h500 : P 15 5 = 0 := (h 3 5 30)
  have h236 : P 7 5 = 0 := (h 3 5 32)
  have h732 : P 22 6 = 0 := (h 3 6 26)
  have h501 : P 15 6 = 0 := (h 3 6 30)
  have h237 : P 7 6 = 0 := (h 3 6 32)
  have h1075 : P 32 19 = 0 := (h 3 7 19).symm
  have h734 : P 22 8 = 0 := (h 3 8 26)
  have h503 : P 15 8 = 0 := (h 3 8 30)
  have h239 : P 7 8 = 0 := (h 3 8 32)
  have h1033 : P 31 10 = 0 := (h 3 9 10).symm
  have h967 : P 29 10 = 0 := (h 3 10 17)
  have h835 : P 25 10 = 0 := (h 3 10 24)
  have h736 : P 22 10 = 0 := (h 3 10 26)
  have h604 : P 18 10 = 0 := (h 3 10 28)
  have h505 : P 15 10 = 0 := (h 3 10 30)
  have h241 : P 7 10 = 0 := (h 3 10 32)
  have h737 : P 22 11 = 0 := (h 3 11 26)
  have h506 : P 15 11 = 0 := (h 3 11 30)
  have h242 : P 7 11 = 0 := (h 3 11 32)
  have h738 : P 22 12 = 0 := (h 3 12 26)
  have h507 : P 15 12 = 0 := (h 3 12 30)
  have h243 : P 7 12 = 0 := (h 3 12 32)
  have h739 : P 22 13 = 0 := (h 3 13 26)
  have h508 : P 15 13 = 0 := (h 3 13 30)
  have h244 : P 7 13 = 0 := (h 3 13 32)
  have h740 : P 22 14 = 0 := (h 3 14 26)
  have h509 : P 15 14 = 0 := (h 3 14 30)
  have h245 : P 7 14 = 0 := (h 3 14 32)
  have h1009 : P 30 19 = 0 := (h 3 15 19).symm
  have h742 : P 22 16 = 0 := (h 3 16 26)
  have h511 : P 15 16 = 0 := (h 3 16 30)
  have h247 : P 7 16 = 0 := (h 3 16 32)
  have h943 : P 28 19 = 0 := (h 3 18 19).symm
  have h877 : P 26 19 = 0 := (h 3 19 22)
  have h811 : P 24 19 = 0 := (h 3 19 25)
  have h745 : P 22 19 = 0 := (h 3 19 26)
  have h580 : P 17 19 = 0 := (h 3 19 29)
  have h514 : P 15 19 = 0 := (h 3 19 30)
  have h316 : P 9 19 = 0 := (h 3 19 31)
  have h250 : P 7 19 = 0 := (h 3 19 32)
  have h746 : P 22 20 = 0 := (h 3 20 26)
  have h515 : P 15 20 = 0 := (h 3 20 30)
  have h251 : P 7 20 = 0 := (h 3 20 32)
  have h747 : P 22 21 = 0 := (h 3 21 26)
  have h516 : P 15 21 = 0 := (h 3 21 30)
  have h252 : P 7 21 = 0 := (h 3 21 32)
  have h749 : P 22 23 = 0 := (h 3 23 26)
  have h518 : P 15 23 = 0 := (h 3 23 30)
  have h254 : P 7 23 = 0 := (h 3 23 32)
  have h753 : P 22 27 = 0 := (h 3 26 27).symm
  have h522 : P 15 27 = 0 := (h 3 27 30)
  have h258 : P 7 27 = 0 := (h 3 27 32)
  have h910 : P 27 19 = 0 := (h 4 18 19).symm
  have h917 : P 27 26 = 0 := (h 4 18 26).symm
  have h921 : P 27 30 = 0 := (h 4 18 30).symm
  have h923 : P 27 32 = 0 := (h 4 18 32).symm
  have h778 : P 23 19 = 0 := (h 4 19 25)
  have h547 : P 16 19 = 0 := (h 4 19 29)
  have h283 : P 8 19 = 0 := (h 4 19 31)
  have h785 : P 23 26 = 0 := (h 4 25 26).symm
  have h789 : P 23 30 = 0 := (h 4 25 30).symm
  have h791 : P 23 32 = 0 := (h 4 25 32).symm
  have h554 : P 16 26 = 0 := (h 4 26 29)
  have h290 : P 8 26 = 0 := (h 4 26 31)
  have h558 : P 16 30 = 0 := (h 4 29 30).symm
  have h560 : P 16 32 = 0 := (h 4 29 32).symm
  have h294 : P 8 30 = 0 := (h 4 30 31)
  have h296 : P 8 32 = 0 := (h 4 31 32).symm
  have h660 : P 20 0 = 0 := (h 5 0 26)
  have h429 : P 13 0 = 0 := (h 5 0 30)
  have h165 : P 5 0 = 0 := (h 5 0 32)
  have h661 : P 20 1 = 0 := (h 5 1 26)
  have h430 : P 13 1 = 0 := (h 5 1 30)
  have h166 : P 5 1 = 0 := (h 5 1 32)
  have h662 : P 20 2 = 0 := (h 5 2 26)
  have h431 : P 13 2 = 0 := (h 5 2 30)
  have h167 : P 5 2 = 0 := (h 5 2 32)
  have h663 : P 20 3 = 0 := (h 5 3 26)
  have h432 : P 13 3 = 0 := (h 5 3 30)
  have h168 : P 5 3 = 0 := (h 5 3 32)
  have h664 : P 20 4 = 0 := (h 5 4 26)
  have h433 : P 13 4 = 0 := (h 5 4 30)
  have h169 : P 5 4 = 0 := (h 5 4 32)
  have h666 : P 20 6 = 0 := (h 5 6 26)
  have h435 : P 13 6 = 0 := (h 5 6 30)
  have h171 : P 5 6 = 0 := (h 5 6 32)
  have h667 : P 20 7 = 0 := (h 5 7 26)
  have h436 : P 13 7 = 0 := (h 5 7 30)
  have h172 : P 5 7 = 0 := (h 5 7 32)
  have h668 : P 20 8 = 0 := (h 5 8 26)
  have h437 : P 13 8 = 0 := (h 5 8 30)
  have h173 : P 5 8 = 0 := (h 5 8 32)
  have h669 : P 20 9 = 0 := (h 5 9 26)
  have h438 : P 13 9 = 0 := (h 5 9 30)
  have h174 : P 5 9 = 0 := (h 5 9 32)
  have h670 : P 20 10 = 0 := (h 5 10 26)
  have h439 : P 13 10 = 0 := (h 5 10 30)
  have h175 : P 5 10 = 0 := (h 5 10 32)
  have h671 : P 20 11 = 0 := (h 5 11 26)
  have h440 : P 13 11 = 0 := (h 5 11 30)
  have h176 : P 5 11 = 0 := (h 5 11 32)
  have h672 : P 20 12 = 0 := (h 5 12 26)
  have h441 : P 13 12 = 0 := (h 5 12 30)
  have h177 : P 5 12 = 0 := (h 5 12 32)
  have h674 : P 20 14 = 0 := (h 5 14 26)
  have h443 : P 13 14 = 0 := (h 5 14 30)
  have h179 : P 5 14 = 0 := (h 5 14 32)
  have h675 : P 20 15 = 0 := (h 5 15 26)
  have h444 : P 13 15 = 0 := (h 5 15 30)
  have h180 : P 5 15 = 0 := (h 5 15 32)
  have h676 : P 20 16 = 0 := (h 5 16 26)
  have h445 : P 13 16 = 0 := (h 5 16 30)
  have h181 : P 5 16 = 0 := (h 5 16 32)
  have h677 : P 20 17 = 0 := (h 5 17 26)
  have h446 : P 13 17 = 0 := (h 5 17 30)
  have h182 : P 5 17 = 0 := (h 5 17 32)
  have h678 : P 20 18 = 0 := (h 5 18 26)
  have h447 : P 13 18 = 0 := (h 5 18 30)
  have h183 : P 5 18 = 0 := (h 5 18 32)
  have h679 : P 20 19 = 0 := (h 5 19 26)
  have h448 : P 13 19 = 0 := (h 5 19 30)
  have h184 : P 5 19 = 0 := (h 5 19 32)
  have h681 : P 20 21 = 0 := (h 5 21 26)
  have h450 : P 13 21 = 0 := (h 5 21 30)
  have h186 : P 5 21 = 0 := (h 5 21 32)
  have h682 : P 20 22 = 0 := (h 5 22 26)
  have h451 : P 13 22 = 0 := (h 5 22 30)
  have h187 : P 5 22 = 0 := (h 5 22 32)
  have h683 : P 20 23 = 0 := (h 5 23 26)
  have h452 : P 13 23 = 0 := (h 5 23 30)
  have h188 : P 5 23 = 0 := (h 5 23 32)
  have h684 : P 20 24 = 0 := (h 5 24 26)
  have h453 : P 13 24 = 0 := (h 5 24 30)
  have h189 : P 5 24 = 0 := (h 5 24 32)
  have h685 : P 20 25 = 0 := (h 5 25 26)
  have h454 : P 13 25 = 0 := (h 5 25 30)
  have h190 : P 5 25 = 0 := (h 5 25 32)
  have h687 : P 20 27 = 0 := (h 5 26 27).symm
  have h688 : P 20 28 = 0 := (h 5 26 28).symm
  have h689 : P 20 29 = 0 := (h 5 26 29).symm
  have h691 : P 20 31 = 0 := (h 5 26 31).symm
  have h456 : P 13 27 = 0 := (h 5 27 30)
  have h192 : P 5 27 = 0 := (h 5 27 32)
  have h457 : P 13 28 = 0 := (h 5 28 30)
  have h193 : P 5 28 = 0 := (h 5 28 32)
  have h458 : P 13 29 = 0 := (h 5 29 30)
  have h194 : P 5 29 = 0 := (h 5 29 32)
  have h460 : P 13 31 = 0 := (h 5 30 31).symm
  have h196 : P 5 31 = 0 := (h 5 31 32)
  have h693 : P 21 0 = 0 := (h 6 0 25)
  have h462 : P 14 0 = 0 := (h 6 0 29)
  have h396 : P 12 0 = 0 := (h 6 0 30)
  have h198 : P 6 0 = 0 := (h 6 0 31)
  have h132 : P 4 0 = 0 := (h 6 0 32)
  have h694 : P 21 1 = 0 := (h 6 1 25)
  have h463 : P 14 1 = 0 := (h 6 1 29)
  have h397 : P 12 1 = 0 := (h 6 1 30)
  have h199 : P 6 1 = 0 := (h 6 1 31)
  have h133 : P 4 1 = 0 := (h 6 1 32)
  have h695 : P 21 2 = 0 := (h 6 2 25)
  have h464 : P 14 2 = 0 := (h 6 2 29)
  have h398 : P 12 2 = 0 := (h 6 2 30)
  have h200 : P 6 2 = 0 := (h 6 2 31)
  have h134 : P 4 2 = 0 := (h 6 2 32)
  have h696 : P 21 3 = 0 := (h 6 3 25)
  have h465 : P 14 3 = 0 := (h 6 3 29)
  have h399 : P 12 3 = 0 := (h 6 3 30)
  have h201 : P 6 3 = 0 := (h 6 3 31)
  have h135 : P 4 3 = 0 := (h 6 3 32)
  have h1082 : P 32 26 = 0 := (h 6 4 26).symm
  have h698 : P 21 5 = 0 := (h 6 5 25)
  have h467 : P 14 5 = 0 := (h 6 5 29)
  have h401 : P 12 5 = 0 := (h 6 5 30)
  have h203 : P 6 5 = 0 := (h 6 5 31)
  have h137 : P 4 5 = 0 := (h 6 5 32)
  have h1041 : P 31 18 = 0 := (h 6 6 18).symm
  have h700 : P 21 7 = 0 := (h 6 7 25)
  have h469 : P 14 7 = 0 := (h 6 7 29)
  have h403 : P 12 7 = 0 := (h 6 7 30)
  have h205 : P 6 7 = 0 := (h 6 7 31)
  have h139 : P 4 7 = 0 := (h 6 7 32)
  have h701 : P 21 8 = 0 := (h 6 8 25)
  have h470 : P 14 8 = 0 := (h 6 8 29)
  have h404 : P 12 8 = 0 := (h 6 8 30)
  have h206 : P 6 8 = 0 := (h 6 8 31)
  have h140 : P 4 8 = 0 := (h 6 8 32)
  have h933 : P 28 9 = 0 := (h 6 9 17)
  have h801 : P 24 9 = 0 := (h 6 9 24)
  have h702 : P 21 9 = 0 := (h 6 9 25)
  have h570 : P 17 9 = 0 := (h 6 9 28)
  have h471 : P 14 9 = 0 := (h 6 9 29)
  have h405 : P 12 9 = 0 := (h 6 9 30)
  have h207 : P 6 9 = 0 := (h 6 9 31)
  have h141 : P 4 9 = 0 := (h 6 9 32)
  have h703 : P 21 10 = 0 := (h 6 10 25)
  have h472 : P 14 10 = 0 := (h 6 10 29)
  have h406 : P 12 10 = 0 := (h 6 10 30)
  have h208 : P 6 10 = 0 := (h 6 10 31)
  have h142 : P 4 10 = 0 := (h 6 10 32)
  have h704 : P 21 11 = 0 := (h 6 11 25)
  have h473 : P 14 11 = 0 := (h 6 11 29)
  have h407 : P 12 11 = 0 := (h 6 11 30)
  have h209 : P 6 11 = 0 := (h 6 11 31)
  have h143 : P 4 11 = 0 := (h 6 11 32)
  have h1016 : P 30 26 = 0 := (h 6 12 26).symm
  have h706 : P 21 13 = 0 := (h 6 13 25)
  have h475 : P 14 13 = 0 := (h 6 13 29)
  have h409 : P 12 13 = 0 := (h 6 13 30)
  have h211 : P 6 13 = 0 := (h 6 13 31)
  have h145 : P 4 13 = 0 := (h 6 13 32)
  have h975 : P 29 18 = 0 := (h 6 14 18).symm
  have h708 : P 21 15 = 0 := (h 6 15 25)
  have h477 : P 14 15 = 0 := (h 6 15 29)
  have h411 : P 12 15 = 0 := (h 6 15 30)
  have h213 : P 6 15 = 0 := (h 6 15 31)
  have h147 : P 4 15 = 0 := (h 6 15 32)
  have h709 : P 21 16 = 0 := (h 6 16 25)
  have h478 : P 14 16 = 0 := (h 6 16 29)
  have h412 : P 12 16 = 0 := (h 6 16 30)
  have h214 : P 6 16 = 0 := (h 6 16 31)
  have h148 : P 4 16 = 0 := (h 6 16 32)
  have h950 : P 28 26 = 0 := (h 6 17 26).symm
  have h843 : P 25 18 = 0 := (h 6 18 21)
  have h711 : P 21 18 = 0 := (h 6 18 25)
  have h480 : P 14 18 = 0 := (h 6 18 29)
  have h414 : P 12 18 = 0 := (h 6 18 30)
  have h216 : P 6 18 = 0 := (h 6 18 31)
  have h150 : P 4 18 = 0 := (h 6 18 32)
  have h712 : P 21 19 = 0 := (h 6 19 25)
  have h481 : P 14 19 = 0 := (h 6 19 29)
  have h415 : P 12 19 = 0 := (h 6 19 30)
  have h217 : P 6 19 = 0 := (h 6 19 31)
  have h151 : P 4 19 = 0 := (h 6 19 32)
  have h713 : P 21 20 = 0 := (h 6 20 25)
  have h482 : P 14 20 = 0 := (h 6 20 29)
  have h416 : P 12 20 = 0 := (h 6 20 30)
  have h218 : P 6 20 = 0 := (h 6 20 31)
  have h152 : P 4 20 = 0 := (h 6 20 32)
  have h715 : P 21 22 = 0 := (h 6 22 25)
  have h484 : P 14 22 = 0 := (h 6 22 29)
  have h418 : P 12 22 = 0 := (h 6 22 30)
  have h220 : P 6 22 = 0 := (h 6 22 31)
  have h154 : P 4 22 = 0 := (h 6 22 32)
  have h716 : P 21 23 = 0 := (h 6 23 25)
  have h485 : P 14 23 = 0 := (h 6 23 29)
  have h419 : P 12 23 = 0 := (h 6 23 30)
  have h221 : P 6 23 = 0 := (h 6 23 31)
  have h155 : P 4 23 = 0 := (h 6 23 32)
  have h818 : P 24 26 = 0 := (h 6 24 26).symm
  have h719 : P 21 26 = 0 := (h 6 25 26).symm
  have h720 : P 21 27 = 0 := (h 6 25 27).symm
  have h587 : P 17 26 = 0 := (h 6 26 28)
  have h488 : P 14 26 = 0 := (h 6 26 29)
  have h422 : P 12 26 = 0 := (h 6 26 30)
  have h224 : P 6 26 = 0 := (h 6 26 31)
  have h158 : P 4 26 = 0 := (h 6 26 32)
  have h489 : P 14 27 = 0 := (h 6 27 29)
  have h423 : P 12 27 = 0 := (h 6 27 30)
  have h225 : P 6 27 = 0 := (h 6 27 31)
  have h159 : P 4 27 = 0 := (h 6 27 32)
  have h363 : P 11 0 = 0 := (h 7 0 30)
  have h99 : P 3 0 = 0 := (h 7 0 32)
  have h364 : P 11 1 = 0 := (h 7 1 30)
  have h100 : P 3 1 = 0 := (h 7 1 32)
  have h365 : P 11 2 = 0 := (h 7 2 30)
  have h101 : P 3 2 = 0 := (h 7 2 32)
  have h367 : P 11 4 = 0 := (h 7 4 30)
  have h103 : P 3 4 = 0 := (h 7 4 32)
  have h369 : P 11 6 = 0 := (h 7 6 30)
  have h105 : P 3 6 = 0 := (h 7 6 32)
  have h370 : P 11 7 = 0 := (h 7 7 30)
  have h106 : P 3 7 = 0 := (h 7 7 32)
  have h899 : P 27 8 = 0 := (h 7 8 17)
  have h767 : P 23 8 = 0 := (h 7 8 24)
  have h536 : P 16 8 = 0 := (h 7 8 28)
  have h371 : P 11 8 = 0 := (h 7 8 30)
  have h107 : P 3 8 = 0 := (h 7 8 32)
  have h372 : P 11 9 = 0 := (h 7 9 30)
  have h108 : P 3 9 = 0 := (h 7 9 32)
  have h373 : P 11 10 = 0 := (h 7 10 30)
  have h109 : P 3 10 = 0 := (h 7 10 32)
  have h375 : P 11 12 = 0 := (h 7 12 30)
  have h111 : P 3 12 = 0 := (h 7 12 32)
  have h377 : P 11 14 = 0 := (h 7 14 30)
  have h113 : P 3 14 = 0 := (h 7 14 32)
  have h378 : P 11 15 = 0 := (h 7 15 30)
  have h114 : P 3 15 = 0 := (h 7 15 32)
  have h381 : P 11 18 = 0 := (h 7 18 30)
  have h117 : P 3 18 = 0 := (h 7 18 32)
  have h382 : P 11 19 = 0 := (h 7 19 30)
  have h118 : P 3 19 = 0 := (h 7 19 32)
  have h384 : P 11 21 = 0 := (h 7 21 30)
  have h120 : P 3 21 = 0 := (h 7 21 32)
  have h385 : P 11 22 = 0 := (h 7 22 30)
  have h121 : P 3 22 = 0 := (h 7 22 32)
  have h686 : P 20 26 = 0 := (h 7 25 26).symm
  have h455 : P 13 26 = 0 := (h 7 26 29)
  have h389 : P 11 26 = 0 := (h 7 26 30)
  have h191 : P 5 26 = 0 := (h 7 26 31)
  have h125 : P 3 26 = 0 := (h 7 26 32)
  have h66 : P 2 0 = 0 := (h 8 0 32)
  have h67 : P 2 1 = 0 := (h 8 1 32)
  have h1086 : P 32 30 = 0 := (h 8 2 30).symm
  have h69 : P 2 3 = 0 := (h 8 3 32)
  have h1048 : P 31 25 = 0 := (h 8 4 25).symm
  have h71 : P 2 5 = 0 := (h 8 5 32)
  have h402 : P 12 6 = 0 := (h 8 6 29)
  have h138 : P 4 6 = 0 := (h 8 6 31)
  have h72 : P 2 6 = 0 := (h 8 6 32)
  have h733 : P 22 7 = 0 := (h 8 7 24)
  have h502 : P 15 7 = 0 := (h 8 7 28)
  have h73 : P 2 7 = 0 := (h 8 7 32)
  have h74 : P 2 8 = 0 := (h 8 8 32)
  have h735 : P 22 9 = 0 := (h 8 9 24)
  have h504 : P 15 9 = 0 := (h 8 9 28)
  have h75 : P 2 9 = 0 := (h 8 9 32)
  have h76 : P 2 10 = 0 := (h 8 10 32)
  have h77 : P 2 11 = 0 := (h 8 11 32)
  have h982 : P 29 25 = 0 := (h 8 12 25).symm
  have h79 : P 2 13 = 0 := (h 8 13 32)
  have h410 : P 12 14 = 0 := (h 8 14 29)
  have h146 : P 4 14 = 0 := (h 8 14 31)
  have h80 : P 2 14 = 0 := (h 8 14 32)
  have h941 : P 28 17 = 0 := (h 8 15 17).symm
  have h954 : P 28 30 = 0 := (h 8 15 30).symm
  have h82 : P 2 16 = 0 := (h 8 16 32)
  have h809 : P 24 17 = 0 := (h 8 17 22)
  have h743 : P 22 17 = 0 := (h 8 17 24)
  have h512 : P 15 17 = 0 := (h 8 17 28)
  have h413 : P 12 17 = 0 := (h 8 17 29)
  have h149 : P 4 17 = 0 := (h 8 17 31)
  have h83 : P 2 17 = 0 := (h 8 17 32)
  have h744 : P 22 18 = 0 := (h 8 18 24)
  have h513 : P 15 18 = 0 := (h 8 18 28)
  have h84 : P 2 18 = 0 := (h 8 18 32)
  have h85 : P 2 19 = 0 := (h 8 19 32)
  have h86 : P 2 20 = 0 := (h 8 20 32)
  have h417 : P 12 21 = 0 := (h 8 21 29)
  have h153 : P 4 21 = 0 := (h 8 21 31)
  have h87 : P 2 21 = 0 := (h 8 21 32)
  have h822 : P 24 30 = 0 := (h 8 22 30).symm
  have h89 : P 2 23 = 0 := (h 8 23 32)
  have h751 : P 22 25 = 0 := (h 8 24 25).symm
  have h752 : P 22 26 = 0 := (h 8 24 26).symm
  have h756 : P 22 30 = 0 := (h 8 24 30).symm
  have h520 : P 15 25 = 0 := (h 8 25 28)
  have h421 : P 12 25 = 0 := (h 8 25 29)
  have h157 : P 4 25 = 0 := (h 8 25 31)
  have h91 : P 2 25 = 0 := (h 8 25 32)
  have h521 : P 15 26 = 0 := (h 8 26 28)
  have h92 : P 2 26 = 0 := (h 8 26 32)
  have h93 : P 2 27 = 0 := (h 8 27 32)
  have h525 : P 15 30 = 0 := (h 8 28 30).symm
  have h426 : P 12 30 = 0 := (h 8 29 30).symm
  have h162 : P 4 30 = 0 := (h 8 30 31)
  have h96 : P 2 30 = 0 := (h 8 30 32)
  have h33 : P 1 0 = 0 := (h 9 0 32)
  have h35 : P 1 2 = 0 := (h 9 2 32)
  have h37 : P 1 4 = 0 := (h 9 4 32)
  have h368 : P 11 5 = 0 := (h 9 5 29)
  have h104 : P 3 5 = 0 := (h 9 5 31)
  have h38 : P 1 5 = 0 := (h 9 5 32)
  have h39 : P 1 6 = 0 := (h 9 6 32)
  have h40 : P 1 7 = 0 := (h 9 7 32)
  have h41 : P 1 8 = 0 := (h 9 8 32)
  have h42 : P 1 9 = 0 := (h 9 9 32)
  have h43 : P 1 10 = 0 := (h 9 10 32)
  have h45 : P 1 12 = 0 := (h 9 12 32)
  have h376 : P 11 13 = 0 := (h 9 13 29)
  have h112 : P 3 13 = 0 := (h 9 13 31)
  have h46 : P 1 13 = 0 := (h 9 13 32)
  have h47 : P 1 14 = 0 := (h 9 14 32)
  have h907 : P 27 16 = 0 := (h 9 15 16).symm
  have h775 : P 23 16 = 0 := (h 9 16 22)
  have h379 : P 11 16 = 0 := (h 9 16 29)
  have h115 : P 3 16 = 0 := (h 9 16 31)
  have h49 : P 1 16 = 0 := (h 9 16 32)
  have h380 : P 11 17 = 0 := (h 9 17 29)
  have h116 : P 3 17 = 0 := (h 9 17 31)
  have h50 : P 1 17 = 0 := (h 9 17 32)
  have h51 : P 1 18 = 0 := (h 9 18 32)
  have h52 : P 1 19 = 0 := (h 9 19 32)
  have h383 : P 11 20 = 0 := (h 9 20 29)
  have h119 : P 3 20 = 0 := (h 9 20 31)
  have h53 : P 1 20 = 0 := (h 9 20 32)
  have h54 : P 1 21 = 0 := (h 9 21 32)
  have h750 : P 22 24 = 0 := (h 9 23 24).symm
  have h754 : P 22 28 = 0 := (h 9 23 28).symm
  have h519 : P 15 24 = 0 := (h 9 24 27)
  have h387 : P 11 24 = 0 := (h 9 24 29)
  have h123 : P 3 24 = 0 := (h 9 24 31)
  have h57 : P 1 24 = 0 := (h 9 24 32)
  have h388 : P 11 25 = 0 := (h 9 25 29)
  have h124 : P 3 25 = 0 := (h 9 25 31)
  have h58 : P 1 25 = 0 := (h 9 25 32)
  have h59 : P 1 26 = 0 := (h 9 26 32)
  have h523 : P 15 28 = 0 := (h 9 27 28).symm
  have h391 : P 11 28 = 0 := (h 9 28 29)
  have h127 : P 3 28 = 0 := (h 9 28 31)
  have h61 : P 1 28 = 0 := (h 9 28 32)
  have h393 : P 11 30 = 0 := (h 9 29 30).symm
  have h129 : P 3 30 = 0 := (h 9 30 31)
  have h63 : P 1 30 = 0 := (h 9 30 32)
  have h1 : P 0 1 = 0 := (h 10 1 32)
  have h2 : P 0 2 = 0 := (h 10 2 32)
  have h3 : P 0 3 = 0 := (h 10 3 32)
  have h697 : P 21 4 = 0 := (h 10 4 23)
  have h466 : P 14 4 = 0 := (h 10 4 27)
  have h4 : P 0 4 = 0 := (h 10 4 32)
  have h665 : P 20 5 = 0 := (h 10 5 24)
  have h434 : P 13 5 = 0 := (h 10 5 28)
  have h5 : P 0 5 = 0 := (h 10 5 32)
  have h699 : P 21 6 = 0 := (h 10 6 23)
  have h468 : P 14 6 = 0 := (h 10 6 27)
  have h6 : P 0 6 = 0 := (h 10 6 32)
  have h7 : P 0 7 = 0 := (h 10 7 32)
  have h8 : P 0 8 = 0 := (h 10 8 32)
  have h9 : P 0 9 = 0 := (h 10 9 32)
  have h10 : P 0 10 = 0 := (h 10 10 32)
  have h11 : P 0 11 = 0 := (h 10 11 32)
  have h705 : P 21 12 = 0 := (h 10 12 23)
  have h474 : P 14 12 = 0 := (h 10 12 27)
  have h12 : P 0 12 = 0 := (h 10 12 32)
  have h15 : P 0 15 = 0 := (h 10 15 32)
  have h16 : P 0 16 = 0 := (h 10 16 32)
  have h710 : P 21 17 = 0 := (h 10 17 23)
  have h479 : P 14 17 = 0 := (h 10 17 27)
  have h17 : P 0 17 = 0 := (h 10 17 32)
  have h18 : P 0 18 = 0 := (h 10 18 32)
  have h19 : P 0 19 = 0 := (h 10 19 32)
  have h22 : P 0 22 = 0 := (h 10 22 32)
  have h718 : P 21 25 = 0 := (h 10 23 25).symm
  have h722 : P 21 29 = 0 := (h 10 23 29).symm
  have h723 : P 21 30 = 0 := (h 10 23 30).symm
  have h724 : P 21 31 = 0 := (h 10 23 31).symm
  have h690 : P 20 30 = 0 := (h 10 24 30).symm
  have h487 : P 14 25 = 0 := (h 10 25 27)
  have h25 : P 0 25 = 0 := (h 10 25 32)
  have h26 : P 0 26 = 0 := (h 10 26 32)
  have h491 : P 14 29 = 0 := (h 10 27 29).symm
  have h492 : P 14 30 = 0 := (h 10 27 30).symm
  have h493 : P 14 31 = 0 := (h 10 27 31).symm
  have h459 : P 13 30 = 0 := (h 10 28 30).symm
  have h29 : P 0 29 = 0 := (h 10 29 32)
  have h30 : P 0 30 = 0 := (h 10 30 32)
  have h31 : P 0 31 = 0 := (h 10 31 32)
  have h1052 : P 31 29 = 0 := (h 11 0 29).symm
  have h366 : P 11 3 = 0 := (h 11 3 28)
  have h400 : P 12 4 = 0 := (h 11 4 27)
  have h948 : P 28 24 = 0 := (h 11 11 24).symm
  have h956 : P 28 32 = 0 := (h 11 11 32).symm
  have h914 : P 27 23 = 0 := (h 11 12 23).symm
  have h673 : P 20 13 = 0 := (h 11 13 22)
  have h13 : P 0 13 = 0 := (h 11 13 31)
  have h14 : P 0 14 = 0 := (h 11 14 31)
  have h741 : P 22 15 = 0 := (h 11 15 20)
  have h755 : P 22 29 = 0 := (h 11 20 29).symm
  have h758 : P 22 32 = 0 := (h 11 20 32).symm
  have h21 : P 0 21 = 0 := (h 11 21 31)
  have h692 : P 20 32 = 0 := (h 11 22 32).symm
  have h386 : P 11 23 = 0 := (h 11 23 28)
  have h23 : P 0 23 = 0 := (h 11 23 31)
  have h420 : P 12 24 = 0 := (h 11 24 27)
  have h24 : P 0 24 = 0 := (h 11 24 31)
  have h425 : P 12 29 = 0 := (h 11 27 29).symm
  have h428 : P 12 32 = 0 := (h 11 27 32).symm
  have h392 : P 11 29 = 0 := (h 11 28 29).symm
  have h395 : P 11 32 = 0 := (h 11 28 32).symm
  have h32 : P 0 32 = 0 := (h 11 31 32).symm
  have h1022 : P 30 32 = 0 := (h 12 7 32).symm
  have h988 : P 29 31 = 0 := (h 12 9 31).symm
  have h890 : P 26 32 = 0 := (h 12 15 32).symm
  have h856 : P 25 31 = 0 := (h 12 17 31).symm
  have h824 : P 24 32 = 0 := (h 12 18 32).symm
  have h757 : P 22 31 = 0 := (h 12 19 31).symm
  have h659 : P 19 32 = 0 := (h 12 22 32).symm
  have h625 : P 18 31 = 0 := (h 12 24 31).symm
  have h593 : P 17 32 = 0 := (h 12 25 32).symm
  have h526 : P 15 31 = 0 := (h 12 26 31).symm
  have h527 : P 15 32 = 0 := (h 12 26 32).symm
  have h361 : P 10 31 = 0 := (h 12 28 31).symm
  have h329 : P 9 32 = 0 := (h 12 29 32).symm
  have h262 : P 7 31 = 0 := (h 12 30 31).symm
  have h263 : P 7 32 = 0 := (h 12 30 32).symm
  have h461 : P 13 32 = 0 := (h 14 26 32).symm
  have h197 : P 5 32 = 0 := (h 14 30 32).symm
  have h725 : P 21 32 = 0 := (h 15 18 32).symm
  have h494 : P 14 32 = 0 := (h 15 25 32).symm
  have h427 : P 12 31 = 0 := (h 15 26 31).symm
  have h229 : P 6 31 = 0 := (h 15 29 31).symm
  have h230 : P 6 32 = 0 := (h 15 29 32).symm
  have h163 : P 4 31 = 0 := (h 15 30 31).symm
  have h164 : P 4 32 = 0 := (h 15 30 32).symm
  have h394 : P 11 31 = 0 := (h 16 26 31).symm
  have h130 : P 3 31 = 0 := (h 16 30 31).symm
  have h131 : P 3 32 = 0 := (h 16 30 32).symm
  have h240 : P 7 9 = 0 := (h 17 9 28)
  have h249 : P 7 18 = 0 := (h 17 18 28)
  have h257 : P 7 26 = 0 := (h 17 26 28)
  have h97 : P 2 31 = 0 := (h 17 30 31).symm
  have h98 : P 2 32 = 0 := (h 17 30 32).symm
  have h248 : P 7 17 = 0 := (h 18 17 27)
  have h255 : P 7 24 = 0 := (h 18 24 27)
  have h259 : P 7 28 = 0 := (h 18 27 28).symm
  have h64 : P 1 31 = 0 := (h 18 30 31).symm
  have h65 : P 1 32 = 0 := (h 18 30 32).symm
  have h202 : P 6 4 = 0 := (h 19 4 27)
  have h210 : P 6 12 = 0 := (h 19 12 27)
  have h223 : P 6 25 = 0 := (h 19 25 27)
  have h227 : P 6 29 = 0 := (h 19 27 29).symm
  have h888 : P 26 30 = 0 := (h 21 4 30).symm
  have h854 : P 25 29 = 0 := (h 21 6 29).symm
  have h820 : P 24 28 = 0 := (h 21 9 28).symm
  have h721 : P 21 28 = 0 := (h 21 10 28).symm
  have h657 : P 19 30 = 0 := (h 21 12 30).symm
  have h623 : P 18 29 = 0 := (h 21 14 29).symm
  have h589 : P 17 28 = 0 := (h 21 17 28).symm
  have h591 : P 17 30 = 0 := (h 21 17 30).symm
  have h490 : P 14 28 = 0 := (h 21 18 28).symm
  have h424 : P 12 28 = 0 := (h 21 19 28).symm
  have h359 : P 10 29 = 0 := (h 21 21 29).symm
  have h325 : P 9 28 = 0 := (h 21 24 28).symm
  have h327 : P 9 30 = 0 := (h 21 24 30).symm
  have h226 : P 6 28 = 0 := (h 21 25 28).symm
  have h228 : P 6 30 = 0 := (h 21 25 30).symm
  have h160 : P 4 28 = 0 := (h 21 26 28).symm
  have h161 : P 4 29 = 0 := (h 21 26 29).symm
  have h786 : P 23 27 = 0 := (h 22 9 27).symm
  have h555 : P 16 27 = 0 := (h 22 17 27).symm
  have h390 : P 11 27 = 0 := (h 22 19 27).symm
  have h291 : P 8 27 = 0 := (h 22 24 27).symm
  have h195 : P 5 30 = 0 := (h 22 25 30).symm
  have h126 : P 3 27 = 0 := (h 22 26 27).symm
  have h128 : P 3 29 = 0 := (h 22 26 29).symm
  have h524 : P 15 29 = 0 := (h 23 17 29).symm
  have h260 : P 7 29 = 0 := (h 23 24 29).symm
  have h261 : P 7 30 = 0 := (h 23 24 30).symm
  have h94 : P 2 28 = 0 := (h 23 26 28).symm
  have h95 : P 2 29 = 0 := (h 23 26 29).symm
  have h60 : P 1 27 = 0 := (h 24 26 27).symm
  have h62 : P 1 29 = 0 := (h 24 26 29).symm
  have h27 : P 0 27 = 0 := (h 25 26 27).symm
  have h28 : P 0 28 = 0 := (h 25 26 28).symm
  have h707 : P 21 14 = 0 := (h 27 1 14).symm
  have h717 : P 21 24 = 0 := (h 27 1 24).symm
  have h36 : P 1 3 = 0 := (h 27 3 21)
  have h70 : P 2 4 = 0 := (h 27 4 20)
  have h81 : P 2 15 = 0 := (h 27 15 20)
  have h48 : P 1 15 = 0 := (h 27 15 21)
  have h90 : P 2 24 = 0 := (h 27 20 24).symm
  have h56 : P 1 23 = 0 := (h 27 21 23).symm
  have h653 : P 19 26 = 0 := (h 28 2 26).symm
  have h619 : P 18 25 = 0 := (h 28 4 25).symm
  have h585 : P 17 24 = 0 := (h 28 7 24).symm
  have h517 : P 15 22 = 0 := (h 28 9 22).symm
  have h355 : P 10 25 = 0 := (h 28 12 25).symm
  have h321 : P 9 24 = 0 := (h 28 15 24).symm
  have h323 : P 9 26 = 0 := (h 28 15 26).symm
  have h253 : P 7 22 = 0 := (h 28 17 22).symm
  have h256 : P 7 25 = 0 := (h 28 17 25).symm
  have h156 : P 4 24 = 0 := (h 28 18 24).symm
  have h88 : P 2 22 = 0 := (h 28 19 22).symm
  have h551 : P 16 23 = 0 := (h 29 7 23).symm
  have h287 : P 8 23 = 0 := (h 29 15 23).symm
  have h122 : P 3 23 = 0 := (h 29 18 23).symm
  have h55 : P 1 22 = 0 := (h 29 19 22).symm
  have h483 : P 14 21 = 0 := (h 30 8 21).symm
  have h486 : P 14 24 = 0 := (h 30 8 24).symm
  have h449 : P 13 20 = 0 := (h 30 9 20).symm
  have h219 : P 6 21 = 0 := (h 30 16 21).symm
  have h222 : P 6 24 = 0 := (h 30 16 24).symm
  have h185 : P 5 20 = 0 := (h 30 17 20).symm
  have h20 : P 0 20 = 0 := (h 30 19 20).symm
  have h348 : P 10 18 = 0 := (h 33 0 18).symm
  have h314 : P 9 17 = 0 := (h 33 3 17).symm
  have h280 : P 8 16 = 0 := (h 33 4 16).symm
  have h246 : P 7 15 = 0 := (h 33 5 15).symm
  have h178 : P 5 13 = 0 := (h 33 7 13).symm
  have h144 : P 4 12 = 0 := (h 33 8 12).symm
  have h110 : P 3 11 = 0 := (h 33 9 11).symm
  have h212 : P 6 14 = 0 := (h 34 1 14).symm
  have h215 : P 6 17 = 0 := (h 34 1 17).symm
  have h78 : P 2 12 = 0 := (h 34 5 12).symm
  have h44 : P 1 11 = 0 := (h 34 6 11).symm
  have h1088 : P 32 32 = P 0 0 := (h 10 0 32).symm.trans h0
  have h1054 : P 31 31 = P 0 0 := (h 11 0 31).symm.trans h0
  have h1020 : P 30 30 = P 0 0 := (h 19 0 30).symm.trans h0
  have h986 : P 29 29 = P 0 0 := (h 20 0 29).symm.trans h0
  have h884 : P 26 26 = P 0 0 := (h 25 0 26).symm.trans h0
  have h850 : P 25 25 = P 0 0 := (h 26 0 25).symm.trans h0
  have h748 : P 22 22 = P 0 0 := (h 27 0 22).symm.trans h0
  have h646 : P 19 19 = P 0 0 := (h 30 0 19).symm.trans h0
  have h612 : P 18 18 = P 0 0 := (h 31 0 18).symm.trans h0
  have h510 : P 15 15 = P 0 0 := (h 32 0 15).symm.trans h0
  have h340 : P 10 10 = P 0 0 := (h 33 0 10).symm.trans h0
  have h238 : P 7 7 = P 0 0 := (h 34 0 7).symm.trans h0
  have h306 : P 9 9 = P 0 0 := (h 1 9 32).trans h1088
  have h272 : P 8 8 = P 0 0 := (h 2 8 32).trans h1088
  have h170 : P 5 5 = P 0 0 := (h 5 5 32).trans h1088
  have h136 : P 4 4 = P 0 0 := (h 6 4 32).trans h1088
  have h102 : P 3 3 = P 0 0 := (h 7 3 32).trans h1088
  have h68 : P 2 2 = P 0 0 := (h 8 2 32).trans h1088
  have h34 : P 1 1 = P 0 0 := (h 9 1 32).trans h1088
  have h204 : P 6 6 = P 0 0 := (h 6 6 31).trans h1054
  have h578 : P 17 17 = P 0 0 := (h 1 17 30).trans h1020
  have h544 : P 16 16 = P 0 0 := (h 2 16 30).trans h1020
  have h442 : P 13 13 = P 0 0 := (h 5 13 30).trans h1020
  have h408 : P 12 12 = P 0 0 := (h 6 12 30).trans h1020
  have h374 : P 11 11 = P 0 0 := (h 7 11 30).trans h1020
  have h476 : P 14 14 = P 0 0 := (h 6 14 29).trans h986
  have h816 : P 24 24 = P 0 0 := (h 1 24 26).trans h884
  have h782 : P 23 23 = P 0 0 := (h 2 23 26).trans h884
  have h680 : P 20 20 = P 0 0 := (h 5 20 26).trans h884
  have h714 : P 21 21 = P 0 0 := (h 6 21 25).trans h850
  have h952 : P 28 28 = P 0 0 := (h 1 19 28).symm.trans h646
  have h918 : P 27 27 = P 0 0 := (h 2 19 27).symm.trans h646
  refine ⟨P 0 0, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13
  · exact h14
  · exact h15
  · exact h16
  · exact h17
  · exact h18
  · exact h19
  · exact h20
  · exact h21
  · exact h22
  · exact h23
  · exact h24
  · exact h25
  · exact h26
  · exact h27
  · exact h28
  · exact h29
  · exact h30
  · exact h31
  · exact h32
  · exact h33
  · exact h34
  · exact h35
  · exact h36
  · exact h37
  · exact h38
  · exact h39
  · exact h40
  · exact h41
  · exact h42
  · exact h43
  · exact h44
  · exact h45
  · exact h46
  · exact h47
  · exact h48
  · exact h49
  · exact h50
  · exact h51
  · exact h52
  · exact h53
  · exact h54
  · exact h55
  · exact h56
  · exact h57
  · exact h58
  · exact h59
  · exact h60
  · exact h61
  · exact h62
  · exact h63
  · exact h64
  · exact h65
  · exact h66
  · exact h67
  · exact h68
  · exact h69
  · exact h70
  · exact h71
  · exact h72
  · exact h73
  · exact h74
  · exact h75
  · exact h76
  · exact h77
  · exact h78
  · exact h79
  · exact h80
  · exact h81
  · exact h82
  · exact h83
  · exact h84
  · exact h85
  · exact h86
  · exact h87
  · exact h88
  · exact h89
  · exact h90
  · exact h91
  · exact h92
  · exact h93
  · exact h94
  · exact h95
  · exact h96
  · exact h97
  · exact h98
  · exact h99
  · exact h100
  · exact h101
  · exact h102
  · exact h103
  · exact h104
  · exact h105
  · exact h106
  · exact h107
  · exact h108
  · exact h109
  · exact h110
  · exact h111
  · exact h112
  · exact h113
  · exact h114
  · exact h115
  · exact h116
  · exact h117
  · exact h118
  · exact h119
  · exact h120
  · exact h121
  · exact h122
  · exact h123
  · exact h124
  · exact h125
  · exact h126
  · exact h127
  · exact h128
  · exact h129
  · exact h130
  · exact h131
  · exact h132
  · exact h133
  · exact h134
  · exact h135
  · exact h136
  · exact h137
  · exact h138
  · exact h139
  · exact h140
  · exact h141
  · exact h142
  · exact h143
  · exact h144
  · exact h145
  · exact h146
  · exact h147
  · exact h148
  · exact h149
  · exact h150
  · exact h151
  · exact h152
  · exact h153
  · exact h154
  · exact h155
  · exact h156
  · exact h157
  · exact h158
  · exact h159
  · exact h160
  · exact h161
  · exact h162
  · exact h163
  · exact h164
  · exact h165
  · exact h166
  · exact h167
  · exact h168
  · exact h169
  · exact h170
  · exact h171
  · exact h172
  · exact h173
  · exact h174
  · exact h175
  · exact h176
  · exact h177
  · exact h178
  · exact h179
  · exact h180
  · exact h181
  · exact h182
  · exact h183
  · exact h184
  · exact h185
  · exact h186
  · exact h187
  · exact h188
  · exact h189
  · exact h190
  · exact h191
  · exact h192
  · exact h193
  · exact h194
  · exact h195
  · exact h196
  · exact h197
  · exact h198
  · exact h199
  · exact h200
  · exact h201
  · exact h202
  · exact h203
  · exact h204
  · exact h205
  · exact h206
  · exact h207
  · exact h208
  · exact h209
  · exact h210
  · exact h211
  · exact h212
  · exact h213
  · exact h214
  · exact h215
  · exact h216
  · exact h217
  · exact h218
  · exact h219
  · exact h220
  · exact h221
  · exact h222
  · exact h223
  · exact h224
  · exact h225
  · exact h226
  · exact h227
  · exact h228
  · exact h229
  · exact h230
  · exact h231
  · exact h232
  · exact h233
  · exact h234
  · exact h235
  · exact h236
  · exact h237
  · exact h238
  · exact h239
  · exact h240
  · exact h241
  · exact h242
  · exact h243
  · exact h244
  · exact h245
  · exact h246
  · exact h247
  · exact h248
  · exact h249
  · exact h250
  · exact h251
  · exact h252
  · exact h253
  · exact h254
  · exact h255
  · exact h256
  · exact h257
  · exact h258
  · exact h259
  · exact h260
  · exact h261
  · exact h262
  · exact h263
  · exact h264
  · exact h265
  · exact h266
  · exact h267
  · exact h268
  · exact h269
  · exact h270
  · exact h271
  · exact h272
  · exact h273
  · exact h274
  · exact h275
  · exact h276
  · exact h277
  · exact h278
  · exact h279
  · exact h280
  · exact h281
  · exact h282
  · exact h283
  · exact h284
  · exact h285
  · exact h286
  · exact h287
  · exact h288
  · exact h289
  · exact h290
  · exact h291
  · exact h292
  · exact h293
  · exact h294
  · exact h295
  · exact h296
  · exact h297
  · exact h298
  · exact h299
  · exact h300
  · exact h301
  · exact h302
  · exact h303
  · exact h304
  · exact h305
  · exact h306
  · exact h307
  · exact h308
  · exact h309
  · exact h310
  · exact h311
  · exact h312
  · exact h313
  · exact h314
  · exact h315
  · exact h316
  · exact h317
  · exact h318
  · exact h319
  · exact h320
  · exact h321
  · exact h322
  · exact h323
  · exact h324
  · exact h325
  · exact h326
  · exact h327
  · exact h328
  · exact h329
  · exact h330
  · exact h331
  · exact h332
  · exact h333
  · exact h334
  · exact h335
  · exact h336
  · exact h337
  · exact h338
  · exact h339
  · exact h340
  · exact h341
  · exact h342
  · exact h343
  · exact h344
  · exact h345
  · exact h346
  · exact h347
  · exact h348
  · exact h349
  · exact h350
  · exact h351
  · exact h352
  · exact h353
  · exact h354
  · exact h355
  · exact h356
  · exact h357
  · exact h358
  · exact h359
  · exact h360
  · exact h361
  · exact h362
  · exact h363
  · exact h364
  · exact h365
  · exact h366
  · exact h367
  · exact h368
  · exact h369
  · exact h370
  · exact h371
  · exact h372
  · exact h373
  · exact h374
  · exact h375
  · exact h376
  · exact h377
  · exact h378
  · exact h379
  · exact h380
  · exact h381
  · exact h382
  · exact h383
  · exact h384
  · exact h385
  · exact h386
  · exact h387
  · exact h388
  · exact h389
  · exact h390
  · exact h391
  · exact h392
  · exact h393
  · exact h394
  · exact h395
  · exact h396
  · exact h397
  · exact h398
  · exact h399
  · exact h400
  · exact h401
  · exact h402
  · exact h403
  · exact h404
  · exact h405
  · exact h406
  · exact h407
  · exact h408
  · exact h409
  · exact h410
  · exact h411
  · exact h412
  · exact h413
  · exact h414
  · exact h415
  · exact h416
  · exact h417
  · exact h418
  · exact h419
  · exact h420
  · exact h421
  · exact h422
  · exact h423
  · exact h424
  · exact h425
  · exact h426
  · exact h427
  · exact h428
  · exact h429
  · exact h430
  · exact h431
  · exact h432
  · exact h433
  · exact h434
  · exact h435
  · exact h436
  · exact h437
  · exact h438
  · exact h439
  · exact h440
  · exact h441
  · exact h442
  · exact h443
  · exact h444
  · exact h445
  · exact h446
  · exact h447
  · exact h448
  · exact h449
  · exact h450
  · exact h451
  · exact h452
  · exact h453
  · exact h454
  · exact h455
  · exact h456
  · exact h457
  · exact h458
  · exact h459
  · exact h460
  · exact h461
  · exact h462
  · exact h463
  · exact h464
  · exact h465
  · exact h466
  · exact h467
  · exact h468
  · exact h469
  · exact h470
  · exact h471
  · exact h472
  · exact h473
  · exact h474
  · exact h475
  · exact h476
  · exact h477
  · exact h478
  · exact h479
  · exact h480
  · exact h481
  · exact h482
  · exact h483
  · exact h484
  · exact h485
  · exact h486
  · exact h487
  · exact h488
  · exact h489
  · exact h490
  · exact h491
  · exact h492
  · exact h493
  · exact h494
  · exact h495
  · exact h496
  · exact h497
  · exact h498
  · exact h499
  · exact h500
  · exact h501
  · exact h502
  · exact h503
  · exact h504
  · exact h505
  · exact h506
  · exact h507
  · exact h508
  · exact h509
  · exact h510
  · exact h511
  · exact h512
  · exact h513
  · exact h514
  · exact h515
  · exact h516
  · exact h517
  · exact h518
  · exact h519
  · exact h520
  · exact h521
  · exact h522
  · exact h523
  · exact h524
  · exact h525
  · exact h526
  · exact h527
  · exact h528
  · exact h529
  · exact h530
  · exact h531
  · exact h532
  · exact h533
  · exact h534
  · exact h535
  · exact h536
  · exact h537
  · exact h538
  · exact h539
  · exact h540
  · exact h541
  · exact h542
  · exact h543
  · exact h544
  · exact h545
  · exact h546
  · exact h547
  · exact h548
  · exact h549
  · exact h550
  · exact h551
  · exact h552
  · exact h553
  · exact h554
  · exact h555
  · exact h556
  · exact h557
  · exact h558
  · exact h559
  · exact h560
  · exact h561
  · exact h562
  · exact h563
  · exact h564
  · exact h565
  · exact h566
  · exact h567
  · exact h568
  · exact h569
  · exact h570
  · exact h571
  · exact h572
  · exact h573
  · exact h574
  · exact h575
  · exact h576
  · exact h577
  · exact h578
  · exact h579
  · exact h580
  · exact h581
  · exact h582
  · exact h583
  · exact h584
  · exact h585
  · exact h586
  · exact h587
  · exact h588
  · exact h589
  · exact h590
  · exact h591
  · exact h592
  · exact h593
  · exact h594
  · exact h595
  · exact h596
  · exact h597
  · exact h598
  · exact h599
  · exact h600
  · exact h601
  · exact h602
  · exact h603
  · exact h604
  · exact h605
  · exact h606
  · exact h607
  · exact h608
  · exact h609
  · exact h610
  · exact h611
  · exact h612
  · exact h613
  · exact h614
  · exact h615
  · exact h616
  · exact h617
  · exact h618
  · exact h619
  · exact h620
  · exact h621
  · exact h622
  · exact h623
  · exact h624
  · exact h625
  · exact h626
  · exact h627
  · exact h628
  · exact h629
  · exact h630
  · exact h631
  · exact h632
  · exact h633
  · exact h634
  · exact h635
  · exact h636
  · exact h637
  · exact h638
  · exact h639
  · exact h640
  · exact h641
  · exact h642
  · exact h643
  · exact h644
  · exact h645
  · exact h646
  · exact h647
  · exact h648
  · exact h649
  · exact h650
  · exact h651
  · exact h652
  · exact h653
  · exact h654
  · exact h655
  · exact h656
  · exact h657
  · exact h658
  · exact h659
  · exact h660
  · exact h661
  · exact h662
  · exact h663
  · exact h664
  · exact h665
  · exact h666
  · exact h667
  · exact h668
  · exact h669
  · exact h670
  · exact h671
  · exact h672
  · exact h673
  · exact h674
  · exact h675
  · exact h676
  · exact h677
  · exact h678
  · exact h679
  · exact h680
  · exact h681
  · exact h682
  · exact h683
  · exact h684
  · exact h685
  · exact h686
  · exact h687
  · exact h688
  · exact h689
  · exact h690
  · exact h691
  · exact h692
  · exact h693
  · exact h694
  · exact h695
  · exact h696
  · exact h697
  · exact h698
  · exact h699
  · exact h700
  · exact h701
  · exact h702
  · exact h703
  · exact h704
  · exact h705
  · exact h706
  · exact h707
  · exact h708
  · exact h709
  · exact h710
  · exact h711
  · exact h712
  · exact h713
  · exact h714
  · exact h715
  · exact h716
  · exact h717
  · exact h718
  · exact h719
  · exact h720
  · exact h721
  · exact h722
  · exact h723
  · exact h724
  · exact h725
  · exact h726
  · exact h727
  · exact h728
  · exact h729
  · exact h730
  · exact h731
  · exact h732
  · exact h733
  · exact h734
  · exact h735
  · exact h736
  · exact h737
  · exact h738
  · exact h739
  · exact h740
  · exact h741
  · exact h742
  · exact h743
  · exact h744
  · exact h745
  · exact h746
  · exact h747
  · exact h748
  · exact h749
  · exact h750
  · exact h751
  · exact h752
  · exact h753
  · exact h754
  · exact h755
  · exact h756
  · exact h757
  · exact h758
  · exact h759
  · exact h760
  · exact h761
  · exact h762
  · exact h763
  · exact h764
  · exact h765
  · exact h766
  · exact h767
  · exact h768
  · exact h769
  · exact h770
  · exact h771
  · exact h772
  · exact h773
  · exact h774
  · exact h775
  · exact h776
  · exact h777
  · exact h778
  · exact h779
  · exact h780
  · exact h781
  · exact h782
  · exact h783
  · exact h784
  · exact h785
  · exact h786
  · exact h787
  · exact h788
  · exact h789
  · exact h790
  · exact h791
  · exact h792
  · exact h793
  · exact h794
  · exact h795
  · exact h796
  · exact h797
  · exact h798
  · exact h799
  · exact h800
  · exact h801
  · exact h802
  · exact h803
  · exact h804
  · exact h805
  · exact h806
  · exact h807
  · exact h808
  · exact h809
  · exact h810
  · exact h811
  · exact h812
  · exact h813
  · exact h814
  · exact h815
  · exact h816
  · exact h817
  · exact h818
  · exact h819
  · exact h820
  · exact h821
  · exact h822
  · exact h823
  · exact h824
  · exact h825
  · exact h826
  · exact h827
  · exact h828
  · exact h829
  · exact h830
  · exact h831
  · exact h832
  · exact h833
  · exact h834
  · exact h835
  · exact h836
  · exact h837
  · exact h838
  · exact h839
  · exact h840
  · exact h841
  · exact h842
  · exact h843
  · exact h844
  · exact h845
  · exact h846
  · exact h847
  · exact h848
  · exact h849
  · exact h850
  · exact h851
  · exact h852
  · exact h853
  · exact h854
  · exact h855
  · exact h856
  · exact h857
  · exact h858
  · exact h859
  · exact h860
  · exact h861
  · exact h862
  · exact h863
  · exact h864
  · exact h865
  · exact h866
  · exact h867
  · exact h868
  · exact h869
  · exact h870
  · exact h871
  · exact h872
  · exact h873
  · exact h874
  · exact h875
  · exact h876
  · exact h877
  · exact h878
  · exact h879
  · exact h880
  · exact h881
  · exact h882
  · exact h883
  · exact h884
  · exact h885
  · exact h886
  · exact h887
  · exact h888
  · exact h889
  · exact h890
  · exact h891
  · exact h892
  · exact h893
  · exact h894
  · exact h895
  · exact h896
  · exact h897
  · exact h898
  · exact h899
  · exact h900
  · exact h901
  · exact h902
  · exact h903
  · exact h904
  · exact h905
  · exact h906
  · exact h907
  · exact h908
  · exact h909
  · exact h910
  · exact h911
  · exact h912
  · exact h913
  · exact h914
  · exact h915
  · exact h916
  · exact h917
  · exact h918
  · exact h919
  · exact h920
  · exact h921
  · exact h922
  · exact h923
  · exact h924
  · exact h925
  · exact h926
  · exact h927
  · exact h928
  · exact h929
  · exact h930
  · exact h931
  · exact h932
  · exact h933
  · exact h934
  · exact h935
  · exact h936
  · exact h937
  · exact h938
  · exact h939
  · exact h940
  · exact h941
  · exact h942
  · exact h943
  · exact h944
  · exact h945
  · exact h946
  · exact h947
  · exact h948
  · exact h949
  · exact h950
  · exact h951
  · exact h952
  · exact h953
  · exact h954
  · exact h955
  · exact h956
  · exact h957
  · exact h958
  · exact h959
  · exact h960
  · exact h961
  · exact h962
  · exact h963
  · exact h964
  · exact h965
  · exact h966
  · exact h967
  · exact h968
  · exact h969
  · exact h970
  · exact h971
  · exact h972
  · exact h973
  · exact h974
  · exact h975
  · exact h976
  · exact h977
  · exact h978
  · exact h979
  · exact h980
  · exact h981
  · exact h982
  · exact h983
  · exact h984
  · exact h985
  · exact h986
  · exact h987
  · exact h988
  · exact h989
  · exact h990
  · exact h991
  · exact h992
  · exact h993
  · exact h994
  · exact h995
  · exact h996
  · exact h997
  · exact h998
  · exact h999
  · exact h1000
  · exact h1001
  · exact h1002
  · exact h1003
  · exact h1004
  · exact h1005
  · exact h1006
  · exact h1007
  · exact h1008
  · exact h1009
  · exact h1010
  · exact h1011
  · exact h1012
  · exact h1013
  · exact h1014
  · exact h1015
  · exact h1016
  · exact h1017
  · exact h1018
  · exact h1019
  · exact h1020
  · exact h1021
  · exact h1022
  · exact h1023
  · exact h1024
  · exact h1025
  · exact h1026
  · exact h1027
  · exact h1028
  · exact h1029
  · exact h1030
  · exact h1031
  · exact h1032
  · exact h1033
  · exact h1034
  · exact h1035
  · exact h1036
  · exact h1037
  · exact h1038
  · exact h1039
  · exact h1040
  · exact h1041
  · exact h1042
  · exact h1043
  · exact h1044
  · exact h1045
  · exact h1046
  · exact h1047
  · exact h1048
  · exact h1049
  · exact h1050
  · exact h1051
  · exact h1052
  · exact h1053
  · exact h1054
  · exact h1055
  · exact h1056
  · exact h1057
  · exact h1058
  · exact h1059
  · exact h1060
  · exact h1061
  · exact h1062
  · exact h1063
  · exact h1064
  · exact h1065
  · exact h1066
  · exact h1067
  · exact h1068
  · exact h1069
  · exact h1070
  · exact h1071
  · exact h1072
  · exact h1073
  · exact h1074
  · exact h1075
  · exact h1076
  · exact h1077
  · exact h1078
  · exact h1079
  · exact h1080
  · exact h1081
  · exact h1082
  · exact h1083
  · exact h1084
  · exact h1085
  · exact h1086
  · exact h1087
  · exact h1088


theorem transpose_mul_higgs_apply {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K) (m : Fin 35) (i j : Fin 33) :
    (P.transpose * higgsMatrix K m) i j =
      (match complement m j with | none => 0 | some k => P k i) := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, higgsMatrix]
  simp_rw [complement_symm m _ j]
  cases hc : complement m j with
  | none => simp [hc]
  | some k => simp [hc, eq_comm]

theorem higgs_mul_apply {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K) (m : Fin 35) (i j : Fin 33) :
    (higgsMatrix K m * P) i j =
      (match complement m i with | none => 0 | some k => P k j) := by
  simp only [Matrix.mul_apply, higgsMatrix]
  cases hc : complement m i with
  | none => simp [hc]
  | some k => simp [hc, eq_comm]

theorem scalar_of_higgs_equations {K : Type*} [Semiring K]
    (P : Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m : Fin 35, P.transpose * higgsMatrix K m = higgsMatrix K m * P) :
    ∃ c : K, ∀ i j, P i j = if i = j then c else 0 := by
  apply scalar_of_entryConstraints P
  intro m i j
  have he := congrArg (fun M : Matrix (Fin 33) (Fin 33) K => M i j) (h m)
  simpa only [transpose_mul_higgs_apply, higgs_mul_apply] using he

/-- The compatible idempotents are exactly zero and the identity. Turning
a geometric subvariation into such a matrix remains a separate theorem. -/
theorem compatible_projector_trivial {K : Type*} [Field K]
    (P : Matrix (Fin 33) (Fin 33) K)
    (h : ∀ m : Fin 35, P.transpose * higgsMatrix K m = higgsMatrix K m * P)
    (hP : P * P = P) : P = 0 ∨ P = 1 := by
  obtain ⟨c, hc⟩ := scalar_of_higgs_equations P h
  have hm : (P * P) 0 0 = c * c := by
    simp [Matrix.mul_apply, hc, eq_comm]
  have he : c * c = c := by
    have ht := congrArg (fun M : Matrix (Fin 33) (Fin 33) K => M 0 0) hP
    simpa only [hm, hc 0 0, ite_true] using ht
  have hz : c * (c - 1) = 0 := by
    rw [mul_sub, mul_one, he, sub_self]
  rcases mul_eq_zero.mp hz with hzero | hone
  · left
    ext i j
    simpa only [hzero, ite_self, Matrix.zero_apply] using hc i j
  · right
    have hc1 : c = 1 := sub_eq_zero.mp hone
    ext i j
    simpa only [hc1, Matrix.one_apply] using hc i j

end CycleQ2FermatHiggs

#print axioms CycleQ2FermatHiggs.scalar_of_higgs_equations
#print axioms CycleQ2FermatHiggs.compatible_projector_trivial
end


