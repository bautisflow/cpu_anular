:- module(_,_, [assertions]).
:- use_module(library(iso_misc)).

:- export(main/0).
main.

:- doc(title, "Segunda pr@'{a}ctica - CPU Anular").
:- doc(subtitle, "Programaci@'{o}n Declarativa: L@'{o}gica y Restricciones").
:- doc(author, "Jaime Bautista Salinero; 150103").
:- doc(date, "@today").
:- doc(module, "Este m@'{o}dulo representa una CPU anular donde cada registro puede contener un único símbolo..

@section{Aclaraci@'{o}nes}

@section{Estructura de la documentaci@'{o}n}

Los predicados explicados en la secci@'{o}n 'Documentation on exports' est@'{a}n ordenados de la siguiente manera para facilitar su estructura:
@begin{enumerate}
@item Predicados pedidos en el ejercicio y a continuaci@'{o}n sus predicados auxiliares.
@item Predicados sobre listas.
@end{enumerate}

@section{Consultas de comprobaci@'{o}n}

A continuaci@'{o}n, se muestras las peticiones realizadas al programa para validar los resultados y a su derecha el resultado esperado:

@subsection{basic_building}
@noindent
@tt{basic_building([0,0]). -> no} @p

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

%%% Types
%:- prop move(i) # "Copia el contenido del registro r@var{i} en el registro r@var{i+1} para 1 <= i < n, y de r@var{n} a r@var{1} para i=n. @includedef{move/1}"
%move(i).

%:- prop swap(i,j) # "Intercambia el contenido de los registros r@var{i} y r@var{j} para i < j. @includedef{swap/2}"
%swap(i,j).


%%% Predicates

:- pred eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos) # "Sustituye los comodines * por variables. Ser@'{a} cierto si @var{RegistrosSinComodines} es una estructura de tipo reg/n que resulta de sustituir los comodines que aparecen en el argumento @var{Registros}/n por variables. @var{ListaSimbolos} es una lista que contiene todos los s@'{i}mbolos utilizados en el t@'{e}rmino @var{Registros}/n en el mismo orden en los que estos aparecen en los registros, permiti@'{e}ndose que haya s@'{i}mbolos repetidos. @includedef{eliminar_comodines/3}".
eliminar_comodines(Registros, RegistrosSinComodines, ListaSimbolos) :-
    functor(Registros,regs,N),
    functor(RegistrosSinComodines,regs,N),
    remove_wildcard(N,Registros,RegistrosSinComodines),
    create_symbol_list(0,N,Registros,ListaSimbolos).

remove_wildcard(0,_,_) :- !.
remove_wildcard(I,R,Rs) :-
    %I > 0, % El corte del anterior lo sustituye
    arg(I,R,X1),
    substitute_wildcard(X1,X2),
    arg(I,Rs,X2),
    I1 is I - 1,
    remove_wildcard(I1,R,Rs).

substitute_wildcard(*,_).
substitute_wildcard(X,X) :-
    X \== '*'.

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

%subterm(Term,Term).
%subterm(Sub,Term) :-
%    compound(Term),
%    functor(Term,F,N),
%    subterm(N,Sub,Term).
%subterm(N,Sub,Term) :-
%    N > 1,
%    N1 is N-1,
%    subterm(N1,Sub,Term).
%subterm(N,Sub,Term) :-
%    arg(N,Term,Arg),
%    subterm(Sub,Arg).
%
%substitute(Old,New,Old,New).
%substitite(Old,New,Term,Term) :-
%    constant(Term),
%    Term \== Old.
%substitute(Old,New,Term,Term1) :-
%    compound(Term),
%    functor(Term,F,N),
%    functor(Term1,F,N),
%    substitute(N,Old,New,Term,Term1).
%substitute(N,Old,New,Term,Term1) :-
%    N > 0,
%    arg(N,Term,Arg),
%    substitute(Old,New,Arg,Arg1),
%    arg(N,Term1,Arg1),
%    N1 is N-1,
%    substitute(N1,Old,New,Term,Term1).
%substitute(0,Old,New,Term,Term1).
 

:- pred ejecutar_instruccion(EstadoActual, Instruccion, EstadoSiguiente) # "Materializa la transici@'{o}n entre los estados actual y siguiente mediante la ejecuci@'{o}n de una instrucci@'{o}n. @includedef{ejecutar_instruccion/3}".
:- test ejecutar_instruccion(A,B,C) : (A=regs(1,2,3,4,5,6), B=move(3)) => (C=regs(1,2,3,3,4,5,6)) + fails # "Prueba".
ejecutar_instruccion(EstadoActual, Instruccion, EstadoSiguiente) :-
    execute_instruction(EstadoActual,Instruccion,EstadoSiguiente).

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
    I >= 1,
    functor(Ea,regs,N),
    functor(Es,regs,N),
    I < N,
    arg(I,Ea,X1),
    I1 is I+1,
    arg(I1,Es,X1),
    subcopy_term(N,Ea,Es).

execute_instruction(Ea,swap(I,J),Es) :-
    nonvar(I),
    I >= 1,
    functor(Ea,regs,N),
    functor(Es,regs,N),
    I =< N,
    arg(I,Ea,Xi),
    arg(J,Ea,Xj),
    arg(I,Es,Xj),
    arg(J,Es,Xi),
    subcopy_term(N,Ea,Es).

execute_instruction(Ea,move(I),Es) :-
    var(I),
    functor(Ea,regs,N),
    execute_instruction(Ea,move(1),N,Es).
execute_instruction(Ea,move(I),_,Es) :- % Backtraking
    nonvar(I),
    execute_instruction(Ea,move(I),Es).
execute_instruction(Ea,move(I),Max,Es) :- % Backtraking
    I =< Max,
    I1 is I+1,
    execute_instruction(Ea,move(I),Es),
    execute_instruction(Ea,move(I1),Max,Es).

% Aqui hay que pasarle functor del mismo tamaño
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

    

:- pred generador_de_codigo(EstadoInicial, EstadoFinal, ListaDeInstrucciones) # "Ser@'{a} cierto si @var{ListaDeInstrucciones} unifica con una lista de instrucciones de la CPU que aplicadas secuencialmente desde un estado inicial de los registros representado por @var{EstadoInicial} permite transitar hacia el estado final de los registros representado por @var{EstadoFinal}. @includedef{generador_de_codigo/3}".
generador_de_codigo(EstadoInicial, EstadoFinal, ListaDeInstrucciones) :-
    code_generator(EstadoInicial,EstadoFinal,ListaDeInstrucciones).

code_generator(Ei,Ef,[L|Ll]) :-
    ejecutar_instruccion(Ei,L,Ef).
    


%%%% Auxiliary predicates

%% ---------------------------------------%%
% -- Predicates for List representation -- %
%% ---------------------------------------%%

:- prop list(X) # "@var{X} es una lista. @includedef{list/1}".
list([]).
list([_|Xs]) :-
     list(Xs).

:- pred list_append(Xs,Ys,Zs) # "@var{Zs} ser@'{a} el resultado de introducir la lista @var{Ys} al final de la lista @var{Xs}. @includedef{list_append/3}".
list_append([],Ys,Ys).
list_append([X|Xs],Ys,[X|Zs]) :-
	list_append(Xs,Ys,Zs).


:- pred list_reverse(Xs,Ys) # "@var{Ys} ser@'{a} la lista @var{Xs} del rev@'{e}s, es decir, intercambiando cada elemento 'n' de @var{Xs} por longitud(@var{Xs}) -'n' - 1. @includedef{list_reverse/2}".
list_reverse(Xs,Ys) :-
    list_reverse(Xs,[],Ys).
:- pred list_reverse(Xs,Acc,Ys) # "@var{Ys} ser@'{a} la lista @var{Xs} del rev@'{e}s. Se genera mediante el uso de un acumulador de elementos. @includedef{list_reverse/3}".
list_reverse([],Ys,Ys).
list_reverse([X|Xs],Acc,Ys) :-
	list_reverse(Xs,[X|Acc],Ys).

:- pred list_flatten(Xs,Ys) # "Aplana la lista @var{Xs}, devolviendo el resultado en @var{Ys}. El aplanado consiste en generar una lista de elementos, en este caso naturales, a partir de una lista cuyos elementos son listas. @includedef{list_flatten/2}".
list_flatten([],[]).
list_flatten(X,[X]).
list_flatten([X|Xs],Y) :-
    list_flatten(X,Ys1),
    list_flatten(Xs,Ys2),
    list_append(Ys1,Ys2,Y).
