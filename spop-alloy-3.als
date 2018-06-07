//=========================================================
// Zad. 3
// 1) Sprawdz asercje BelowToo
// 2) Uzupelnij predykat Geometry i sprawdz asercje
//    BelowToo' (wybierajac w menu "Execute->...")
//    dla zakresow 2 i 3
// 3) Uzupelnij predykat NoSharing i sprawdz asercje
//    BelowToo'' dla zakresow 6 i 10
// 4) Wygeneruj instancje modelu spelniajaca predykat
//    Nosharing. Co jest "nie tak" w tej instancji?
//=========================================================

sig Platform {}
sig Man {ceiling, floor: Platform}

// Czlowiek m mieszka nad czlowiekiem n, jesli podloga m
// jest sufitem dla n
pred Above[m, n: Man] {m.floor = n.ceiling}

// Czyjs sufit jest czyjas podloga
fact PaulSimon {all m: Man | some n: Man | Above[n, m]}

// Czyjas podloga jest czyims sufitem? 
assert BelowToo { all m: Man | some n: Man | Above[m, n] }

check BelowToo for 2

pred Geometry {
  // Podloga danej osoby nie moze byc jednoczesnie
  // jej sufitem
  // (tu wpisz ograniczenie)
  all m:Man | m.ceiling != m.floor
}

assert BelowToo' {
  Geometry => (all m: Man | some n: Man | Above[m, n])
}

check BelowToo' for 2
check BelowToo' for 3

pred NoSharing {
  // Dwie osoby nie moga miec wspolnej podlogi lub
  // wspolnego sufitu
  // (tu wpisz ograniczenie)
  all disj m,n:Man | m.floor != n.floor and m.ceiling != n.ceiling
}

assert BelowToo'' {
  NoSharing => (all m: Man | some n: Man | Above[m, n])
}

check BelowToo'' for 6
check BelowToo'' for 10

run {Geometry && NoSharing}

// problem jest taki, ze fakt PaulSimon wymusza, zeby wszyscy zawsze mieli kogos pod soba
// czyli prowadzi to do tego, ze w pewnym miejscu mamy petle w pietrach,
// bo ten najnizej tez musi miec kogos pod soba
