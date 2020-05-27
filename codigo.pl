:- module(_,_, [assertions]).
:- use_module(library(classic/classic_predicates)).
:- use_package(dynamic).


:- doc(title, "Segunda pr@'{a}ctica - CPU Anular").
:- doc(subtitle, "Programaci@'{o}n Declarativa: L@'{o}gica y Restricciones").
:- doc(author, "Jaime Bautista Salinero; 150103").
:- doc(date, "@today").
:- doc(module, "Este m@'{o}dulo representa una CPU anular donde cada registro puede contener un @'{u}nico s@'{i}mbolo.

La CPU tiene la capacidad de ejecutar dos tipos de instrucciones:
@begin{enumerate}
@item move(i): Copia el contenido del registro r@var{i} en el registro r@var{i+1} para 1 <= i < n, y de r@var{n} a r@var{1} para i=n.
@item swap(i,j): Intercambia el contenido de los registros r@var{i} y r@var{j} para i < j.
@end{enumerate}

@section{Aclaraciones sobre predicados}

@subsection{ejecutar_instruccion}
Para este predicado se ha emplado un predicado auxiliar, elaborando un camino diferente seg@'{u}n el tipo de la instrucci@'{o}n, move o swap.
As@'{i} mismo, se han elaborado los caminos correspondientes para que, en el caso en el que se sepan los estados inicial y finales, el predicado sea capaz de deducir la instrucci@'{o}n correspondiente que lo llevar@'{a} al estado final.

Cada tipo de instrucci@'{o}n solo tendr@'{a} su propio camino independiente al otro tipo. 

@subsection{generador_de_codigo}
Una de las maneras existentes para que este predicado pueda devolver el camino m@'{a}s corto que lo lleve a la soluci@'{o}n es relizar la b@'{u}squeda en anchura en vez de en profundidad, siedo est@'{a} @'{u}ltimo la opci@'{o}n por defecto para el sistema Ciao prolog.

A pesar de tener la posibilidad de emplear la librer@'{i}a bf de Ciao, se ha implementado una serie de predicados que realizan la b@'{u}squeda en anchura. La memoria necesaria para almacenar los estados visitados, as@'{i} como el camino que los ha llevado hasta ah@'{i}, se ha implementado mediante una estructura din@'{a}mica, insertando los estados correspondientes a medida que se visiten y eliminado los caminos anteriores. La estructura es la siguiente: @p
@noindent
@tt{[[EstadoActual,[Ruta,EstadoInicial]]}. @p
@noindent
Ejemplo: @tt{[[regs(1,1),[move(1),regs(1,2)]],[regs(2,2),[move(2),regs(1,2)]],...]}.

@section{Estructura de la documentaci@'{o}n}

Los predicados explicados en la secci@'{o}n 'Documentation on exports' est@'{a}n ordenados de la siguiente manera para facilitar su estructura:
@begin{enumerate}
@item Predicados pedidos en el ejercicio y a continuaci@'{o}n sus predicados auxiliares.
@item Predicados sobre listas.
@end{enumerate}

@section{Consultas}
Las consultas de comprobaci@'{o}n se han automatizado en el c@'{o}digo con predicados test.

@section{Generaci@'{o}n de la documentaci@'{o}n}

Esta documentaci@'{o}n ha sido generada automaticamente con la herramienta
@href{http://ciao-lang.org/ciao/build/doc/lpdoc.html/}{@bf{lpdoc}}. Para generarla,
desde una l@'{i}nea de comandos ubicada en el directorio donde se encuentra el fichero de c@'{o}digo,
se ha ejecutado:
@begin{verbatim}
~$ lpdoc -t pdf codigo.pl
@end{verbatim}

").

% AUTOR: Jaime Bautista Salinero - 53940280-J, 150103
alumno_prode('Bautista', 'Salinero', 'Jaime', 'X150103').

%% ---------------------------------------%%
% --- Predicates for buldings exercise --- %
%% ---------------------------------------%%

%%% Predicates

:- pred eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos) # "Sustituye los comodines * por variables. Ser@'{a} cierto si @var{RegistrosSinComodines} es una estructura de tipo reg/n que resulta de sustituir los comodines que aparecen en el argumento @var{Registros}/n por variables. @var{ListaSimbolos} es una lista que contiene todos los s@'{i}mbolos utilizados en el t@'{e}rmino @var{Registros}/n en el mismo orden en los que estos aparecen en los registros, permiti@'{e}ndose que haya s@'{i}mbolos repetidos. @includedef{eliminar_comodines/3}".
:- test eliminar_comodines(A,B,C) : (A=regs(1,1,+,5,*)) => (B=regs(1,1,+,5,_),C=[1,1,+,5]) + not_fails # "eliminar comodines con un comodín al final y elementos repetidos".
:- test eliminar_comodines(A,B,C) : (A=regs(1,1,+,5,6)) => (B=regs(1,1,+,5,6),C=[1,1,+,5,6]) + not_fails # "eliminar comodines sin comodines y elementos repetidos".
:- test eliminar_comodines(A,B,C) : (A=regs(*,*,*,*,*)) => (B=regs(_,_,_,_,_),C=[]) + not_fails # "eliminar comodines con todos los elementos comodines".
eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos) :-
    functor(Registros,regs,N),
    functor(RegistrosSinComodines,regs,N),
    remove_wildcard(N,Registros,RegistrosSinComodines),
    create_symbol_list(0,N,Registros,ListaSimbolos).

:- pred ejecutar_instruccion(EstadoActual, Instruccion, EstadoSiguiente) # "Materializa la transici@'{o}n entre los estados actual y siguiente mediante la ejecuci@'{o}n de una instrucci@'{o}n. @includedef{ejecutar_instruccion/3}".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=move(7)) => (C=regs(1,2,3,4,5,6)) + fails # "ejecutar instruccion move en un índice no existente".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=move(3)) => (C=regs(1,2,3,3,5,6)) + not_fails # "ejecutar instruccion move en un índice situado a la mitad".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=move(1)) => (C=regs(1,1,3,4,5,6)) + not_fails # "ejecutar instruccion move en un índice situado al principio".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=move(6)) => (C=regs(6,2,3,4,5,6)) + not_fails # "ejecutar instruccion move en un índice siteado al final".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=swap(3,4)) => (C=regs(1,2,4,3,5,6)) + not_fails # "ejecutar instruccion swap con índices situado en la mitad".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=swap(1,6)) => (C=regs(6,2,3,4,5,1)) + not_fails # "ejecutar instruccion swap con índices situados en los extremos".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=swap(6,1)) => (C=regs(1,2,3,4,5,6)) + fails # "ejecutar instruccion swap con índice J mayor que I".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=swap(1,7)) => (C=regs(1,2,3,4,5,6)) + fails # "ejecutar instruccion swap con índice J no existente".
ejecutar_instruccion(EstadoActual, Instruccion, EstadoSiguiente) :-
    execute_instruction(EstadoActual,Instruccion,EstadoSiguiente).

:- pred generador_de_codigo(EstadoInicial, EstadoFinal, ListaDeInstrucciones) # "Ser@'{a} cierto si @var{ListaDeInstrucciones} unifica con una lista de instrucciones de la CPU que aplicadas secuencialmente desde un estado inicial de los registros representado por @var{EstadoInicial} permite transitar hacia el estado final de los registros representado por @var{EstadoFinal}. @includedef{generador_de_codigo/3}".
:- test generador_de_codigo(A,B,C) : (A=regs(a,b,c,d), B=regs(a,d,a,b)) => (C=[move(2),move(1),swap(2,4),swap(3,4)]) + not_fails # "ejecutar instruccion swap con índice J no existente".
:- test generador_de_codigo(A,B,C) : (A=regs(a,b,c), B=regs(a,a,*)) => (C=[move(1)]) + not_fails # "ejecutar instruccion swap con índice J no existente".
generador_de_codigo(EstadoInicial, EstadoFinal, ListaDeInstrucciones) :-
    eliminar_comodines(EstadoInicial,InicialSinComodines,_),
    eliminar_comodines(EstadoFinal,FinalSinComodines,_),
    code_generator(InicialSinComodines,FinalSinComodines,ListaDeInstrucciones).

%% ---------------------------------------%%
% --         Axuliary predicates        -- %
%% ---------------------------------------%%

%%% For eliminar_comodines
:- pred remove_wildcard(I,R,Rs) # "@var{Rs} ser@'{a} una estructura de datos del mismo tama@~{n}o que @var{R} sustituyendo los comodines(*) de @var{R} por la variable an@'{o}nima. @var{I} ser@'{a} el acumulador, siendo necesario pasarle como primer valor el tama@~{n}o total de la estructura de datos. @includedef{remove_wildcard/3}".
remove_wildcard(0,_,_) :- !.
remove_wildcard(I,R,Rs) :-
    %I > 0, % El corte del anterior lo sustituye
    arg(I,R,X1),
    substitute_wildcard(X1,X2),
    arg(I,Rs,X2),
    I1 is I - 1,
    remove_wildcard(I1,R,Rs).

:- pred substitute_wildcard(X,Y) # "Para el caso en que @var{X} sea un comod@'{i}, @var{Y} ser@'{a} la variable an@'{o}nima. En otro caso @var{Y} ser@'{a} igual que @var{X}. @includedef{substitute_wildcard/2}".
substitute_wildcard(*,_).
substitute_wildcard(X,X) :-
    X \== '*'.

:- pred create_symbol_list(I,Max,R,S) # "Este predicado generar@'{a} una lista, en @var{S} compuesta por los s@'{i}mbolos de la estructura de datos en @var{R}omitiendo el comod@'{i} (*). En @var{Max} se le debe de pasar la longitud de la estructura @var{R} e @var{I} ser@'{a} la variable usada como acumulador. @includedef{create_symbol_list/4}".
create_symbol_list(I,Max,_,S) :- 
    I =:= Max,
    list(S), !.
create_symbol_list(I,Max,R,[S|Ss]) :-
    I1 is I+1,
    arg(I1,R,S),
    S \== '*',
    create_symbol_list(I1,Max,R,Ss).
create_symbol_list(I,Max,R,S) :-
    I1 is I+1,
    arg(I1,R,X),
    X == '*',
    create_symbol_list(I1,Max,R,S).

%%% For ejecutar_instruccion
:- pred execute_instruction(Ea,I,Es) # "Predidado auxiliar para ejecutar instrucci@'{o}n, mediante el cual, al ejecutar la instrucci@'{o}n @var{I} sobre la estructura de registros @var{Ea} se debe obtener @var{Ea}. @includedef{execute_instruction/3}".
% Basic movements
execute_instruction(Ea,move(I),Es) :- % I < N
    nonvar(I),
    functor(Ea,regs,N),
    I =:= N,
    functor(Es,regs,N),
    arg(I,Ea,X1),
    arg(1,Es,X1),
    subcopy_term(N,Ea,Es).
execute_instruction(Ea,move(I),Es) :- % I = N
    nonvar(I),
    I1 is I+1,
    I >= 1,
    functor(Ea,regs,N),
    functor(Es,regs,N),
    I < N,
    arg(I,Ea,X1),
    arg(I1,Es,X1),
    subcopy_term(N,Ea,Es).

execute_instruction(Ea,swap(I,J),Es) :-
    nonvar(I),
    I >= 1,
    functor(Ea,regs,N),
    functor(Es,regs,N),
    I =< N,
    I < J,
    arg(I,Ea,Xi),
    arg(J,Ea,Xj),
    arg(I,Es,Xj),
    arg(J,Es,Xi),
    subcopy_term(N,Ea,Es).

% Backtracking for move
execute_instruction(Ea,move(I),Es) :-
    var(I),
    functor(Ea,regs,N),
    execute_instruction1(Ea,move(0),I,N,Es).
% Backtracking for swap
execute_instruction(Ea,swap(I,J),Es) :-
    var(I),
    var(J),
    functor(Ea,regs,N),
    execute_instruction1(Ea,swap(0,1),I,J,N,Es).

:- pred execute_instruction1(Ea,In,I,N,Es) # " Predicado encargado de realizar el backtracking correspondiente para averiguar la instrucci@'{o}n @var{In} de move, que llevará el registro @var{Ea} a @var{Es}. @var{N} ser@'{a} la longitud m@'{a}xima de los registros mientras que @var{I} ser@'{a} el acumulador que permite la construcci@'{o} de todos los movimientos posibles. @includedef{execute_instruction1/5}".
execute_instruction1(Ea,move(I),I,_,Es) :- % solution
    execute_instruction(Ea,move(I),Es).
execute_instruction1(Ea,move(I1),I,N,Es) :-
    nonvar(I1),
    I1 =< N,
    I2 is I1+1,
    execute_instruction1(Ea,move(I2),I,N,Es).
    
:- pred execute_instruction1(Ea,In,I,J,N,Es) # " Predicado encargado de realizar el backtracking correspondiente para averiguar la instrucci@'{o}n @var{In} de swap, que llevará el registro @var{Ea} a @var{Es}. @var{N} ser@'{a} la longitud m@'{a}xima de los registros mientras que @var{I} y @var{J} ser@'{a}n los acumuladores que permiten la construcci@'{o} de todos los cambios posibles. En un camino se incrementar@'{a} @var{J} y en otro camino @var{I} y @var{J} a la vez. @includedef{execute_instruction1/6}".
execute_instruction1(Ea,swap(I,J),I,J,_,Es) :- % solution
    I \== J,
    execute_instruction(Ea,swap(I,J),Es).
execute_instruction1(Ea,swap(I1,J1),I,J,N,Es) :-
    nonvar(I1),
    nonvar(J1),
    I1 < J1,
    J1 =< N,
    J2 is J1+1,
    execute_instruction1(Ea,swap(I1,J2),I,J,N,Es).
execute_instruction1(Ea,swap(I1,J1),I,J,N,Es) :-
    nonvar(I1),
    nonvar(J1),
    I1 < J1,
    J1 =< N,
    I2 is I1+1,
    J2 is J1+1,
    execute_instruction1(Ea,swap(I2,J2),I,J,N,Es).

% Aqui hay que pasarle functor del mismo tamano
:- pred subcopy_term(I,Ea,Es) # "Copia los elementos de la estructura @var{Ea} a la misma posici@'{o}n en la estructura @var{Es} siempre y cuando el elemento correspondiente en @var{Es} no est@'{e} previamente inicializado. @var{I} ser@'{a} el acumuludar para recorrer las estructuras y que como valor inicial se le debe de pasar la longitud de las mismas. @includedef{subcopy_term/3}". 
subcopy_term(0,_,_).
subcopy_term(I,Ea,Es) :-
    arg(I,Es,X1),
    var(X1),
    arg(I,Ea,X1),
    I1 is I-1,
    subcopy_term(I1,Ea,Es).
subcopy_term(I,Ea,Es) :-
    arg(I,Es,X1),
    nonvar(X1),
    I1 is I-1,
    subcopy_term(I1,Ea,Es).

%%% For generador_de_codigo
:- pred code_generator(Ei,Ef,Path) # "Inicializa la estructura din@'{a}mica empleada para la memoria del camino y los estados de la b@'{u}queda por anchura. As@'{i} mismo, ejecuta la b@'{u}squeda por anchura pasandole como punto de partida la estructura inicial @var{Ei} y como meta la estructura final @var{Ef}. @includedef{code_generator/3}".
code_generator(Ei,Ef,Path) :-
    retractall( seen( _ ) ),
    bfs( Ef, [[Ei,[Ei]]], [_|Path] ). 

% dynamic structure for already seen states
:- dynamic seen/1.

:- pred add_to_seen(E) # "Dada una lista de estados @var{N} los a@~{n}ade a la estructura din@'{a}mica de estados ya vistos. @includedef{add_to_seen/1}". 
add_to_seen([]).
add_to_seen([[N|_]|Rest]) :-
        assertz(seen(N)),
        add_to_seen(Rest).

:- pred remove_seen(E,L) # "Dada una lista @var{E} elimina los estados que ya han sido vistos de la estructura din@'{a}mica y devuelve una lista nueva con los que no se han visto a@'{u}n en @var{L}. @includedef{remove_seen/2}".
remove_seen( [], [] ).
remove_seen( [[N|_]|Rest], Result ) :-
        seen( N ), !,
        remove_seen( Rest, Result ).
remove_seen( [State|Rest], [State|Result] ) :-
        !, remove_seen( Rest, Result ).

:- pred next_states(X,Y) # "Mediante un estado actual y su ruta asociada en @var{X} y con estructura [Estado,Ruta], se devuelve un estado siguiente con la nueva ruta asociada en @var{Y} con estructura [NuevoEstado,[NuevoMoviento,Ruta]]. @includedef{next_states/2}".
next_states([N,Path], [NewN,[Function|Path]]) :-
    ejecutar_instruccion(N,Function,NewN).

:- pred next_states_list(State,Result) # "Devuelve todos los elementos del siguiente nivel en el @'{a}rbol partiendo del estado actual @var{State}. @var{Result} tendr@'{a} la misma estructura que los elementos almacenados en la estructura din@'{a}mica seen/1. @includedef{next_states_list/2}".
next_states_list(State, Result) :-
    findall(X,next_states(State,X),Result).


:- pred bfs(Goal,Queue,Path) # "Ejecuta el algoritmo de b@'{u}squeda en anchura para una meta @var{Goal} y una cola en @var{Queue}. Devuelve el resultado final de la meta y la ruta en @var{Path}. @includedef{bfs/3}".
bfs(Goal,[[Goal|[Path]]|_],FinalPath) :-
        !, reverse(Path,FinalPath).
bfs(Goal,[State|Rest],Result) :-
    next_states_list(State,Successors),
    remove_seen(Successors,NewStates),
    add_to_seen(NewStates),
    append(Rest,NewStates,Queue),
    bfs(Goal,Queue,Result).

%% ---------------------------------------%%
% -- Predicates for List representation -- %
%% ---------------------------------------%%

:- prop list(X) # "@var{X} es una lista. @includedef{list/1}".
list([]).
list([_|Xs]) :-
     list(Xs).

