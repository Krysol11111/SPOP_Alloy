//=========================================================
// Zad. 2
// 1) Sprawdz, ze ponizszy model nie posiada instancji
// 2) Rozszerz model tak, by fryzjer mogl byc kobieta
//    (wprowadz zbiory Person i Woman)
// 3) Przejrzyj wszystkie mozliwe instancje stworzonego
//    modelu (menu "Instance -> Show Next Solution" lub
//    "Next" na pasku narzedzi)
// 4) Dodaj ograniczenie, ze jesli ktos nie jest fryzjerem,
//    to goli co najwyzej tylko siebie
//=========================================================

abstract sig Person {shaves: set Man}

sig Man,Woman extends Person {}

one sig Barber in Person { }

fact {
  // Fryzjer goli tych i tylko tych mezczyzn, ktorzy
  // sie sami nie gola
  Barber.shaves = { m: Man | m not in m.shaves }
  // jesli sa tylko mezczyzni to zbior jest pusty
  // jest tak, poniewaz jesli fryzjer ma byc mezczyzna to musi, albo golic siebie, albo nie golic siebie
  // jesli ma siebie golic, to z racji tego, że jest fryzjerem nie moze siebie golic -> sprzecznosc
  // jesli ma nie golic siebie to fryzjer musi go golic - czyli on sam - znowu sprzecznosc
  // nie ma innych opcji => fryzjer nie moze byc mezczyzna
  // jak dodamy kobiety to kazdy fryzjer bedzie kobieta

  //Jesli ktos nie jest fryzjerem, to goli co najwyzej tylko siebie
  all p:Person | p in Barber or #p.shaves = 0 or (#p.shaves = 1 and p in p.shaves)
}

run {}
