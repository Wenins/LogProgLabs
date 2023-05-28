implement main
    open core, stdio

domains
    vault = rubles; dollars.

class facts - polyclinicDb
    карта_пациента : (integer PID, string FullNameP, string Address, string Number, integer Age, string Job).
    врач : (integer DID, string FullNameD, string Profile).
    приём : (integer DID, integer PID, string DateP, string Diagnosis, string Treatment, boolean SickDay).
    расписание_приемов : (integer DID, integer Start, integer End).
    лекарство : (string Medicine).
    метод_лечения : (string Method).
    выходные : (string Day).
    будние : (string Day).
    стоимость_приёма : (integer DID, integer PriceP, vault VP).
    стоимость_лекарства : (string Medicine, integer PriceM, vault VM).
    количество_таблеток : (string Medicine, integer Amount).
    время_терапии : (string Method, integer Days).
    стоимость_терапии : (string Method, integer PriceT, vault VT).
    таблетки_в_день : (string Medicine, integer TPD).
    длительность_таблеток : (string Medicine, integer TPD).

class facts
    s : (real Sum) single.
    стоимость : (string Med, integer Price, vault VT) nondeterm.

clauses
    s(0).

class predicates
    %расписание_поликлиники : (string Day) nondeterm.
    история_болезней : (string PatientName) nondeterm.
    назначенное_лечение : (string PatientName) nondeterm.
    назначенные_препараты : (string PatientName) nondeterm.
    общий_счёт : (string PatientName) nondeterm.
    цена : (string C) nondeterm.

clauses
    цена(X) :-
        лекарство(X),
        стоимость_лекарства(X, Cost, _),
        assert(стоимость(X, Cost, rubles)),
        fail.
    цена(X) :-
        метод_лечения(X),
        стоимость_терапии(X, Cost, _),
        assert(стоимость(X, Cost, rubles)),
        fail.
    цена(X) :-
        приём(_, _, _, _, X, _).

    история_болезней(X) :-
        карта_пациента(ID, X, _, _, _, _),
        приём(_, ID, _, Dis, _, _),
        writef("Болезни %:\n", X),
        writef("\t%\n", Dis),
        fail.
    история_болезней(X) :-
        карта_пациента(_, X, _, _, _, _),
        write("Конец списка\n").

    назначенное_лечение(X) :-
        карта_пациента(ID, X, _, _, _, _),
        приём(_, ID, _, _, Heal, _),
        writef("Лечение, назначенное %:\n", X),
        метод_лечения(Heal),
        writef("\t%\n", Heal),
        fail.
    назначенное_лечение(X) :-
        карта_пациента(_, X, _, _, _, _),
        write("Конец списка\n").

    назначенные_препараты(X) :-
        карта_пациента(ID, X, _, _, _, _),
        приём(_, ID, _, _, Heal, _),
        writef("Препараты, назначенные %:\n", X),
        лекарство(Heal),
        writef("\t%\n", Heal),
        fail.
    назначенные_препараты(X) :-
        карта_пациента(_, X, _, _, _, _),
        write("Конец списка\n").

    общий_счёт(X) :-
        карта_пациента(ID, X, _, _, _, _),
        assert(s(0)),
        приём(DID, ID, _, _, Heal, _),
        стоимость_приёма(DID, Price, _),
        s(Sum),
        цена(Heal),
        стоимость(Heal, Cost, _),
        assert(s(Sum + Price + Cost)),
        fail.
    общий_счёт(X) :-
        карта_пациента(_, X, _, _, _, _),
        s(Sum),
        writef("Общий счет % равен %", X, Sum),
        nl.

clauses
    run() :-
        file::consult("../polydb.txt", polyclinicDb),
        fail.

    run() :-
        общий_счёт('Кьеркегеров Тимофей Евгеньевич'),
        fail.

    run() :-
        назначенное_лечение('Кьеркегеров Тимофей Евгеньевич'),
        fail.

    run() :-
        назначенные_препараты('Кьеркегеров Тимофей Евгеньевич'),
        fail.
    run() :-
        история_болезней('Кьеркегеров Тимофей Евгеньевич'),
        fail.

    run().

end implement main

goal
    console::runUtf8(main::run).
