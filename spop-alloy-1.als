//=========================================================
// Zad. 1
// Przejrzyj kilka instancji ponizszego modelu, a nastepnie
// stopniowo rozszerzaj go i analizuj dopisujac kolejne
// ograniczenia. Analizujac model przegladaj zawsze kilka
// jego instancji (menu "Instance -> Show Next Solution"
// lub "Next" na pasku narzedzi).
//=========================================================

sig Gang { members: set Inmate }

sig Inmate { room: Cell }

sig Cell { }

pred show {
  // W miescie sa dwa gangi
  // (tu wpisz ograniczenie)
  #Gang = 2
  // Kazdy gang ma czlonkow w wiezieniu 
  // (tu wpisz ograniczenie)
 all g:Gang | some i:Inmate | i in g.members
  // Kazdy osadzony jest czlonkiem ktoregos z gangow
  // (tu wpisz ograniczenie)
all i:Inmate | one g:Gang | i in g.members 
  // Nie ma pustych cel
  // (tu wpisz ograniczenie)
all c:Cell | some i:Inmate | i.room = c
  // W kazdej celi moze siedziec nie wiecej niz dwoch
  // osadzonych
  // (tu wpisz ograniczenie)
all c:Cell | #{i:Inmate | i.room = c} <= 2
  // Czlonkowie tego samego gangu nie siedza w tej
  // samej celi
  // (tu wpisz ograniczenie)
all disj i,j:Inmate | i.room != j.room
}

run show
