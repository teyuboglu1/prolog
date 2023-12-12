implement main
    open core, stdio, file

domains
    id_sotrudnika = integer.
    name = string.
    gender = string.
    age = integer.
    data_priema = string.
    id_otdela = integer.
    id_dolzhnosti = integer.
    nazvaniye_otdela = string.
    dolzhnost = string.
    data_nachala = string.
    stazh = integer.

class facts - officeDb
    sotrudnik : (id_sotrudnika, name, gender, age, data_priema, id_otdela, id_dolzhnosti, stazh) nondeterm.
    otdel : (id_otdela, nazvaniye_otdela) nondeterm.
    dolzhnost : (id_dolzhnosti, dolzhnost, id_otdela) nondeterm.
    zanimaet : (id_sotrudnika, id_dolzhnosti, data_nachala) nondeterm.
    total_age : (integer) determ.
    counter_of_sotrudnikov : (integer) determ.

class predicates
    gender_sotrudnika : (name Name, gender Gender) nondeterm anyflow.
clauses
    gender_sotrudnika(X, Y) :-
        sotrudnik(_, X, Y, _, _, _, _, _).

class predicates
    otdel_sotrudnika : (name Name, nazvaniye_otdela Otdel) nondeterm anyflow.
clauses
    otdel_sotrudnika(X, Y) :-
        sotrudnik(_, X, _, _, _, Z, _, _),
        otdel(Z, Y).

class predicates
    dolzhnost_sotrudnika : (name Name, dolzhnost Dolzhnost) nondeterm anyflow.
clauses
    dolzhnost_sotrudnika(X, Y) :-
        sotrudnik(_, X, _, _, _, _, Z, _),
        dolzhnost(Z, Y, _).

class predicates
    data_nachala_raboti : (name Name, data_nachala DataNachala) nondeterm anyflow.
clauses
    data_nachala_raboti(X, Y) :-
        sotrudnik(Z, X, _, _, _, _, _, _),
        zanimaet(Z, _, Y).

class predicates
    dolzhnosti_otdela : (nazvaniye_otdela Otdel, dolzhnost Dolzhnost) nondeterm anyflow.
clauses
    dolzhnosti_otdela(X, Y) :-
        otdel(Z, X),
        dolzhnost(_, Y, Z).

class predicates
    age_sotrudnika : (name Name, age Age) nondeterm anyflow.
clauses
    age_sotrudnika(X, Y) :-
        sotrudnik(_, X, _, Y, _, _, _, _).

class predicates
    starshiy_sotrudnik : (name Name, age Age) nondeterm anyflow.
clauses
    starshiy_sotrudnik(X, Y) :-
        sotrudnik(_, X, _, Z, _, _, _, _),
        not((sotrudnik(_, _, _, Y, _, _, _, _) and Y > Z)).

class predicates
    mladshiy_sotrudnik : (name Name, age Age) nondeterm anyflow.
clauses
    mladshiy_sotrudnik(X, Y) :-
        sotrudnik(_, X, _, Z, _, _, _, _),
        not((sotrudnik(_, _, _, Y, _, _, _, _) and Y < Z)).

class predicates
    summa_mladshego_i_starshego : (integer Res) nondeterm anyflow.
clauses
    summa_mladshego_i_starshego(Res) :-
        mladshiy_sotrudnik(_, Y),
        starshiy_sotrudnik(_, B),
        Res = B + Y.

class predicates
    counter_of_sotrudnikov : (integer [out]) nondeterm.
clauses
    counter_of_sotrudnikov(Res) :-
        assert(count_of_patients(0)),
        sotrudnik(_, _, _, _, _, _, _, _),
        retract(count_of_sotrudnikov(Count)),
        Res = Count + 1,
        asserta(count_of_sotrudnikov(Res)),
        fail.

    counter_of_sotrudnikov(Res) :-
        retract(count_of_sotrudnikov(Res)).

class predicates
    avg_age : (real [out]) nondeterm.
clauses
    avg_age(Res) :-
        assert(total_age(0)),
        sotrudnik(_, _, _, X, _, _, _, _),
        retract(total_age(Total)),
        Sum = Total + X,
        asserta(total_age(Sum)),
        fail.
    avg_age(Res) :-
        retract(total_age(Sum)),
        counter_of_sotrudnikov(Count),
        Res = Sum / Count.

class predicates
    sales_department_employees_with_age_and_experience : (name Name, age Age, stazh Stazh) nondeterm anyflow.
clauses
    sales_department_employees_with_age_and_experience(X, Y, K) :-
        sotrudnik(_, X, _, Y, _, _, _, K),
        Y > 25,
        K > 10.

clauses
    run() :-
        consult("../officeDB.txt", officeDb),
        fail.
    run() :-
        nl,
        write("Gender sotrudnika\n"),
        gender_sotrudnika(X, Y),
        write(X, ":", Y),
        nl,
        fail.
    run() :-
        nl,
        write("Dolzhnost sotrudnika\n"),
        dolzhnost_sotrudnika(X, Y),
        write(X, ":", Y),
        nl,
        fail.
    run() :-
        nl,
        write("Vozrast sotrudnika\n"),
        age_sotrudnika(X, Y),
        write(X, ":", Y),
        nl,
        fail.
    run() :-
        nl,
        write("Avg vozrast sotrudnikov:\n"),
        avg_age(Res),
        write(Res),
        nl,
        fail.
    run() :-
        nl,
        write("Summa vozrastov sotrudnika\n"),
        summa_mladshego_i_starshego(X, Y),
        write(X, ":", Y),
        nl,
        fail.
    run() :-
        nl,
        write("Stazh Age\n"),
        sales_department_employees_with_age_and_experience(X, Y, K),
        write(X, ":", Y, ":", K),
        nl,
        fail.

    run().

end implement main

goal
    console::runUtf8(main::run).
